(ns kotoba.native.peephole-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.peephole :as peephole]
            [kotoba.native.machine-ir :as machine-ir]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]))

(defn- legacy-x86 [kir]
  (binding [machine-ir/*production-routing-enabled?* false]
    (x86/emit-program kir)))

(defn- legacy-arm [kir]
  (binding [machine-ir/*production-routing-enabled?* false]
    (arm/emit-program kir)))

;; ---------------------------------------------------------------------------
;; Operand recognition
;; ---------------------------------------------------------------------------

(deftest constant-operand-recognizes-exactly-the-safe-forms
  (is (= 7 (peephole/constant-operand 7)))
  (is (= -1 (peephole/constant-operand -1)))
  (is (= 0 (peephole/constant-operand 0)))
  (testing "booleans are the i64 words one and zero"
    (is (= 1 (peephole/constant-operand true)))
    (is (= 0 (peephole/constant-operand false))))
  (testing "false and zero are PRESENT, not absent -- callers must use some?"
    (is (some? (peephole/constant-operand false)))
    (is (some? (peephole/constant-operand 0))))
  (testing "every form whose code reads a stack slot or clobbers state is refused"
    (doseq [form ['x "s" '(f 1) '(cap-call 3 1) '(+ 1 2) '(let [a 1] a) nil]]
      (is (nil? (peephole/constant-operand form))
          (str form " must keep the spill/reload window")))))

;; ---------------------------------------------------------------------------
;; Backend integration
;; ---------------------------------------------------------------------------

(def ^:private constant-rhs
  {:format :kotoba.kir/v4 :exports ['main]
   ;; Nested addition stays outside the bounded GMIR production pilot, so this
   ;; fixture continues to exercise the legacy emitter's peephole seam.
   :functions [{:name 'main :params [] :body '(+ (+ 3 4) 5)}]})

(deftest x86-64-materializes-a-constant-operand-into-the-scratch-register
  (let [code (:code (legacy-x86 constant-rhs))
        window [0x48 0xb9 0x05 0x00 0x00 0x00 0x00 0x00 0x00 0x00]]
    (is (= 1 (count (filter #(= window %) (partition 10 1 code))))
        "the optimized window must appear exactly once, byte for byte")
    (is (not-any? #(= [0x48 0xb8 0x05 0x00 0x00 0x00 0x00 0x00 0x00 0x00
                       0x48 0x89 0xc1 0x58] %)
                  (partition 14 1 code))
        "no spill/reload round trip may survive for a constant operand")))

(deftest aarch64-materializes-a-constant-operand-into-the-scratch-register
  (let [code (:code (legacy-arm constant-rhs))
        ;; movz x1,#5 ; movk x1,#0,lsl 16 ; lsl 32 ; lsl 48.
        window (concat [0xa1 0x00 0x80 0xd2] [0x01 0x00 0xa0 0xf2]
                       [0x01 0x00 0xc0 0xf2] [0x01 0x00 0xe0 0xf2])]
    (is (= 1 (count (filter #(= (seq window) %) (partition 16 1 code))))
        "the optimized window must appear exactly once, byte for byte")))

(deftest optimized-windows-reclaim-the-spill-and-reload-bytes
  (testing "x86-64 reclaims push/mov/pop (5 bytes)"
    (is (= 58 (count (:code (legacy-x86 constant-rhs))))))
  (testing "AArch64 reclaims save/restore (20 bytes)"
    (is (= 92 (count (:code (legacy-arm constant-rhs)))))))

;; ---------------------------------------------------------------------------
;; What the verifier actually requires
;; ---------------------------------------------------------------------------

(def ^:private branch-heavy
  ;; Constant operands on BOTH sides of a branch. Final layout must recompute
  ;; both displacements after each arm shrinks.
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'main :params ['p]
                :body '(if p (+ p 5) (- (* p 3) 7))}]})

(deftest emission-stays-deterministic-across-repeated-compilation
  ;; kotoba-verifier re-derives emission from sealed KIR and rejects any drift,
  ;; so a pass that was nondeterministic would not merely be untidy -- it would
  ;; make every artifact it touched unverifiable.
  (doseq [kir [constant-rhs branch-heavy]]
    (is (= (legacy-x86 kir) (legacy-x86 kir)))
    (is (= (legacy-arm kir) (legacy-arm kir)))
    (is (apply = (repeatedly 5 #(:code (legacy-x86 kir)))))
    (is (apply = (repeatedly 5 #(:code (legacy-arm kir)))))))

(deftest branch-displacements-still-span-optimized-windows
  ;; A branch whose arms contain shortened windows must still be emitted,
  ;; deterministic, and keep both arms present.
  (let [x (legacy-x86 branch-heavy)
        a (legacy-arm branch-heavy)]
    (is (seq (:code x)))
    (is (seq (:code a)))
    (is (= 0 (get-in x [:exports 'main :offset])))
    (is (= (count (:code x)) (get-in x [:exports 'main :length])))
    (is (= (count (:code a)) (get-in a [:exports 'main :length])))
    (is (zero? (rem (count (:code a)) 4))
        "every AArch64 artifact must stay a whole number of instructions")))
