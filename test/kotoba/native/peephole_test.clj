(ns kotoba.native.peephole-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.peephole :as peephole]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]))

;; ---------------------------------------------------------------------------
;; The invariant itself
;; ---------------------------------------------------------------------------

(deftest pad-to-preserves-the-window-length-exactly
  (testing "every admitted padding length reaches the target exactly"
    (doseq [target (range 0 40)
            used (range 0 (inc target))]
      (let [replacement (vec (repeat used 0xcc))
            padded (peephole/pad-to replacement target peephole/nop-x86-64)]
        (is (= target (count padded))
            (str "x86-64 window of " target " bytes holding " used))
        (is (= replacement (subvec padded 0 used))
            "the replacement must be left byte-identical, padding only appends"))))
  (testing "AArch64 padding is four-byte aligned by construction"
    (doseq [target (range 0 40 4)
            used (range 0 (inc target) 4)]
      (is (= target (count (peephole/pad-to (vec (repeat used 0xcc)) target
                                            peephole/nop-aarch64)))))))

(deftest pad-to-refuses-to-grow-a-window
  ;; Growing is the one failure mode that would corrupt every already-baked
  ;; branch displacement spanning the window, so it must throw rather than
  ;; produce an artifact that fails later in the verifier or at run time.
  (is (thrown? clojure.lang.ExceptionInfo
               (peephole/pad-to [1 2 3 4] 3 peephole/nop-x86-64)))
  (is (thrown? clojure.lang.ExceptionInfo
               (peephole/pad-to (vec (repeat 8 0)) 4 peephole/nop-aarch64))))

(deftest aarch64-padding-rejects-unaligned-lengths
  (doseq [n [1 2 3 5 6 7]]
    (is (thrown? clojure.lang.ExceptionInfo (peephole/nop-aarch64 n))
        (str n " is not a whole number of AArch64 instructions"))))

;; ---------------------------------------------------------------------------
;; No-op encodings
;; ---------------------------------------------------------------------------

(deftest x86-64-no-ops-are-the-recommended-encodings
  ;; Intel SDM Vol. 2B Table 4-12. Asserted literally so a future edit cannot
  ;; quietly substitute an invented filler the verifier would still accept.
  (is (= [0x90] (peephole/nop-x86-64 1)))
  (is (= [0x66 0x90] (peephole/nop-x86-64 2)))
  (is (= [0x0f 0x1f 0x00] (peephole/nop-x86-64 3)))
  (is (= [0x0f 0x1f 0x44 0x00 0x00] (peephole/nop-x86-64 5)))
  (is (= [0x66 0x0f 0x1f 0x84 0x00 0x00 0x00 0x00 0x00] (peephole/nop-x86-64 9)))
  (testing "lengths above nine are a deterministic greedy sequence"
    (is (= (into (peephole/nop-x86-64 9) (peephole/nop-x86-64 4))
           (peephole/nop-x86-64 13)))
    (is (= 40 (count (peephole/nop-x86-64 40))))))

(deftest aarch64-no-op-is-the-architectural-encoding
  (is (= [0x1f 0x20 0x03 0xd5] (peephole/nop-aarch64 4)))
  (is (= (concat (peephole/nop-aarch64 4) (peephole/nop-aarch64 4))
         (peephole/nop-aarch64 8)))
  (is (= [] (peephole/nop-aarch64 0))))

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
   :functions [{:name 'main :params [] :body '(+ 3 5)}]})

(deftest x86-64-materializes-a-constant-operand-into-the-scratch-register
  (let [code (:code (x86/emit-program constant-rhs))
        ;; mov rcx,5 followed by the five-byte canonical no-op that replaces
        ;; the push/mov/pop the unoptimized window would have emitted.
        window [0x48 0xb9 0x05 0x00 0x00 0x00 0x00 0x00 0x00 0x00
                0x0f 0x1f 0x44 0x00 0x00]]
    (is (= 1 (count (filter #(= window %) (partition 15 1 code))))
        "the optimized window must appear exactly once, byte for byte")
    (is (not-any? #(= [0x48 0xb8 0x05 0x00 0x00 0x00 0x00 0x00 0x00 0x00
                       0x48 0x89 0xc1 0x58] %)
                  (partition 14 1 code))
        "no spill/reload round trip may survive for a constant operand")))

(deftest aarch64-materializes-a-constant-operand-into-the-scratch-register
  (let [code (:code (arm/emit-program constant-rhs))
        ;; movz x1,#5 ; movk x1,#0,lsl 16 ; lsl 32 ; lsl 48 ; then five nops.
        window (concat [0xa1 0x00 0x80 0xd2] [0x01 0x00 0xa0 0xf2]
                       [0x01 0x00 0xc0 0xf2] [0x01 0x00 0xe0 0xf2]
                       (peephole/nop-aarch64 20))]
    (is (= 1 (count (filter #(= (seq window) %) (partition 36 1 code))))
        "the optimized window must appear exactly once, byte for byte")))

;; The numbers below are the whole point of the exercise: they are what the
;; UNOPTIMIZED emitter produced for this program too. If a later change makes
;; the peephole reclaim its padding instead of preserving it, these fail --
;; which is the intended alarm, because reclaiming bytes silently invalidates
;; every branch displacement both backends bake as plain bytes at emit time.
(deftest the-optimized-window-occupies-the-length-it-replaced
  (testing "x86-64: fuel(13) + pad-push(1) + mov rax,3(10) + window(15) + add(3) + epilogue(8)"
    (is (= 50 (count (:code (x86/emit-program constant-rhs))))))
  (testing "AArch64: fuel(20) + stp/mov-fp(8) + movz/movk x0(16) + window(36) + add(4) + ldp/ret(8)"
    (is (= 92 (count (:code (arm/emit-program constant-rhs)))))))

;; ---------------------------------------------------------------------------
;; What the verifier actually requires
;; ---------------------------------------------------------------------------

(def ^:private branch-heavy
  ;; Constant operands on BOTH sides of a branch, so the `if` displacements --
  ;; which both backends bake as plain bytes from `code-size` before any pass
  ;; could run -- span optimized windows in the then AND else arms.
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'main :params ['p]
                :body '(if p (+ p 5) (- (* p 3) 7))}]})

(deftest emission-stays-deterministic-across-repeated-compilation
  ;; kotoba-verifier re-derives emission from sealed KIR and rejects any drift,
  ;; so a pass that was nondeterministic would not merely be untidy -- it would
  ;; make every artifact it touched unverifiable.
  (doseq [kir [constant-rhs branch-heavy]]
    (is (= (x86/emit-program kir) (x86/emit-program kir)))
    (is (= (arm/emit-program kir) (arm/emit-program kir)))
    (is (apply = (repeatedly 5 #(:code (x86/emit-program kir)))))
    (is (apply = (repeatedly 5 #(:code (arm/emit-program kir)))))))

(deftest branch-displacements-still-span-optimized-windows
  ;; A branch whose arms contain optimized windows must still be emitted, be
  ;; deterministic, and keep both arms present. Executing it is the native
  ;; executor's job (tender-native, a different repository); what is checkable
  ;; here is that the windows inside the arms did not change the code the
  ;; displacements were computed over -- which the length assertions above pin
  ;; down and which this exercises through a real branching program.
  (let [x (x86/emit-program branch-heavy)
        a (arm/emit-program branch-heavy)]
    (is (seq (:code x)))
    (is (seq (:code a)))
    (is (= 0 (get-in x [:exports 'main :offset])))
    (is (= (count (:code x)) (get-in x [:exports 'main :length])))
    (is (= (count (:code a)) (get-in a [:exports 'main :length])))
    (is (zero? (rem (count (:code a)) 4))
        "every AArch64 artifact must stay a whole number of instructions")))
