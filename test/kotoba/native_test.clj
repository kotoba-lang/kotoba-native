(ns kotoba.native-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]
            [kotoba.native.elf64]))

;; Load gate: the split must not break namespace resolution. Each extracted
;; namespace must load standalone from this repo's own dependency closure.
(deftest every-extracted-namespace-loads
  (is (some? (find-ns 'kotoba.native.x86-64)) "kotoba.native.x86-64 must load")
  (is (some? (find-ns 'kotoba.native.aarch64)) "kotoba.native.aarch64 must load")
  (is (some? (find-ns 'kotoba.native.elf64)) "kotoba.native.elf64 must load"))

(deftest native-backends-deterministically-own-code-and-export-layout
  (let [kir {:format :kotoba.kir/v4 :exports ['main]
             :functions [{:name 'main :params [] :body 42}]}
        x (x86/emit-program kir)
        a (arm/emit-program kir)]
    (is (= x (x86/emit-program kir)))
    (is (= a (arm/emit-program kir)))
    (is (seq (:code x)))
    (is (seq (:code a)))
    (is (= 0 (get-in x [:exports 'main :offset])))
    (is (= 0 (get-in a [:exports 'main :offset])))))

;; ── f64 scalar ops (ADR-2608030300 stage 1) ──────────────────────────────
;;
;; Encodings are asserted against what `clang -target arm64-apple-macos`
;; assembles, not against the manual as I read it. Hand-derived opcode fields
;; are the single easiest thing to get quietly wrong in a backend that emits
;; raw words, and a wrong one produces a program that runs and computes
;; nonsense.

(defn- words
  "The emitted bytes as 32-bit little-endian words."
  [bytes]
  (mapv (fn [chunk]
          (reduce (fn [acc [i b]] (bit-or acc (bit-shift-left (bit-and b 0xff) (* 8 i))))
                  0 (map-indexed vector chunk)))
        (partition 4 bytes)))

(defn- emit [form]
  (words (#'kotoba.native.aarch64/emit-expr form {} 0)))

(deftest f64-from-and-to-bits-are-identities-on-this-backend
  (testing "the value is already its bit pattern in x0, so no instruction is needed"
    (is (= (emit 4614253070214989087)
           (emit (list 'f64-from-bits 4614253070214989087))
           (emit (list 'f64-to-bits (list 'f64-from-bits 4614253070214989087)))))))

(deftest f64-binary-ops-move-through-the-fp-bank
  (let [code (emit (list 'f64-add
                         (list 'f64-from-bits 4611686018427387904)
                         (list 'f64-from-bits 4613937818241073152)))
        tail (take-last 4 code)]
    (testing "fmov d0,x0 · fmov d1,x1 · fadd d0,d0,d1 · fmov x0,d0"
      (is (= [0x9e670000 0x9e670021 0x1e612800 0x9e660000] (vec tail)))))
  (testing "every binary opcode, as clang assembles it"
    (doseq [[op word] {'f64-sub 0x1e613800 'f64-mul 0x1e610800 'f64-div 0x1e611800
                       'f64-max 0x1e614800 'f64-min 0x1e615800}]
      (let [code (emit (list op (list 'f64-from-bits 1) (list 'f64-from-bits 2)))]
        (is (= word (nth (vec code) (- (count code) 2))) (str op))))))

(deftest f64-unary-ops-need-no-second-register
  (doseq [[op word] {'f64-abs 0x1e60c000 'f64-neg 0x1e614000 'f64-sqrt 0x1e61c000}]
    (let [code (vec (emit (list op (list 'f64-from-bits 4611686018427387904))))]
      (is (= [0x9e670000 word 0x9e660000] (vec (take-last 3 code))) (str op)))))

(deftest f64-arithmetic-nests
  (testing "(a*b)+c reuses the ordinary binary save/restore, so nesting is free"
    (let [code (emit (list 'f64-add
                           (list 'f64-mul (list 'f64-from-bits 1) (list 'f64-from-bits 2))
                           (list 'f64-from-bits 3)))]
      (is (some #{0x1e610800} code) "the inner multiply is present")
      (is (some #{0x1e612800} code) "the outer add is present")
      (is (= 0x9e660000 (last code)) "the result lands back in x0"))))

;; ── the same ops on x86-64 ───────────────────────────────────────────────

(defn- emit86 [form]
  (vec (#'kotoba.native.x86-64/emit-expr form {} {:temp-depth 0 :tail? false})))

(deftest x86-f64-matches-the-assembler
  (testing "from-bits and to-bits emit nothing here either"
    (is (= (emit86 4611686018427387904)
           (emit86 (list 'f64-from-bits 4611686018427387904)))))
  (testing "addsd through the SSE bank, lhs in rax and rhs in rcx"
    (let [code (emit86 (list 'f64-add (list 'f64-from-bits 1) (list 'f64-from-bits 2)))]
      (is (= [0x66 0x48 0x0f 0x6e 0xc0 0x66 0x48 0x0f 0x6e 0xc9
              0xf2 0x0f 0x58 0xc1 0x66 0x48 0x0f 0x7e 0xc0]
             (vec (take-last 19 code))))))
  (testing "neg and abs are sign-bit operations, not SSE with a constant pool"
    (is (= [0x48 0x0f 0xba 0xf8 0x3f]
           (vec (take-last 5 (emit86 (list 'f64-neg (list 'f64-from-bits 1)))))))
    (is (= [0x48 0x0f 0xba 0xf0 0x3f]
           (vec (take-last 5 (emit86 (list 'f64-abs (list 'f64-from-bits 1))))))))
  (testing "sqrt does need the SSE bank"
    (is (= [0xf2 0x0f 0x51 0xc0 0x66 0x48 0x0f 0x7e 0xc0]
           (vec (take-last 9 (emit86 (list 'f64-sqrt (list 'f64-from-bits 1)))))))))

(deftest both-backends-cover-the-same-f64-ops
  (testing "a parity gap that closes on one architecture only is still a gap"
    (let [a (set (keys @#'kotoba.native.aarch64/f64-binary-ops))
          x (set (keys @#'kotoba.native.x86-64/f64-binary-ops))]
      (is (= a x))
      (is (= '#{f64-add f64-sub f64-mul f64-div f64-min f64-max} a)))
    (let [a (set (keys @#'kotoba.native.aarch64/f64-unary-ops))
          x (set (keys @#'kotoba.native.x86-64/f64-unary-ops))]
      (is (= a x))
      (is (= '#{f64-abs f64-neg f64-sqrt} a)))))
