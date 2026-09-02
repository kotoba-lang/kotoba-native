(ns kotoba.native-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]
            [kotoba.native.machine-ir :as machine]
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

(deftest production-backends-route-scalar-direct-calls-through-machine-ir
  (let [kir {:format :kotoba.kir/v4 :exports ['main]
             :functions
             [{:name 'inc-one :params ['x] :result :i64 :body '(+ x 1)}
              {:name 'main :params ['x] :result :i64
               :body '(let [live 40] (+ live (inc-one x)))}]}
        x (x86/emit-program kir)
        a (arm/emit-program kir)]
    (is (machine/pilot-module? kir))
    (is (= x (x86/emit-program kir)))
    (is (= a (arm/emit-program kir)))
    (doseq [[target artifact] [[:x86-64 x] [:aarch64 a]]]
      (is (= #{'main} (set (keys (:exports artifact)))) target)
      (is (pos? (get-in artifact [:exports 'main :offset])) target)
      (is (pos? (get-in artifact [:exports 'main :length])) target)
      (is (= 1 (get-in artifact [:exports 'main :arity])) target)
      (is (seq (:code artifact)) target))))

(defn- contains-bytes? [bytes needle]
  (boolean (some #(= (vec needle) %)
                 (partition (count needle) 1 bytes))))

(deftest production-runtime-handle-calls-route-through-machine-ir
  (let [kir {:format :kotoba.kir/v4 :exports ['main]
             :functions [{:name 'main :params ['v] :result :i64
                          :body '(+ (vector-count v) (vector-count v))}]}
        x86-code (:code (x86/emit-program kir))
        arm-code (:code (arm/emit-program kir))]
    (is (machine/pilot-expression? '[v]
                                   '(+ (vector-count v) (vector-count v))))
    (is (= 2 (count (filter #(= [0x41 0xff 0x91 0xa8 0x00 0x00 0x00] %)
                            (partition 7 1 x86-code))))
        "both x86 runtime calls use [r9+168]")
    (is (contains-bytes? x86-code [0x4c 0x89 0x8c 0x24])
        "the production x86 path uses the MIR-owned context spill")
    (is (= 2 (count (filter #(= [0xf0 0x54 0x40 0xf9] %)
                            (partition 4 1 arm-code))))
        "both AArch64 runtime calls load [x7,#168]")
    (is (contains-bytes? arm-code [0xe7 0x03 0x00 0xf9])
        "the production AArch64 path preserves x7")))

(deftest f64-production-slice-routes-through-machine-ir
  (let [binary-forms
        {'f64-add '(f64-add (f64-from-bits 4607182418800017408)
                            (f64-from-bits 4611686018427387904))
         'f64-sub '(f64-sub 1 2) 'f64-mul '(f64-mul 1 2)
         'f64-div '(f64-div 1 2) 'f64-min '(f64-min 1 2)
         'f64-max '(f64-max 1 2) 'f64-eq '(f64-eq 1 2)
         'f64-lt '(f64-lt 1 2) 'f64-le '(f64-le 1 2)
         'f64-gt '(f64-gt 1 2) 'f64-ge '(f64-ge 1 2)
         'f64-unordered '(f64-unordered 1 2)}
        unary-forms {'f64-from-bits '(f64-from-bits 1)
                     'f64-to-bits '(f64-to-bits 1)
                     'f64-abs '(f64-abs 1) 'f64-neg '(f64-neg 1)
                     'f64-sqrt '(f64-sqrt 1)}]
    (doseq [[op form] (concat binary-forms unary-forms)]
      (is (machine/pilot-expression? [] form) (str op))
      (is (seq (machine/compile-expression :x86-64 [] form)) (str op " x86"))
      (is (seq (machine/compile-expression :aarch64 [] form)) (str op " arm")))
    (let [gmir (machine/lower-kir-expression []
                 '(f64-sqrt (f64-add (f64-from-bits 1)
                                     (f64-from-bits 2))))
          ops (mapv :gmir/op (:gmir/instructions gmir))
          x86-code (machine/compile-expression :x86-64 []
                     '(f64-add (f64-from-bits 1) (f64-from-bits 2)))
          arm-code (machine/compile-expression :aarch64 []
                     '(f64-add (f64-from-bits 1) (f64-from-bits 2)))]
      (is (some #{:gmir/f64-add} ops))
      (is (some #{:gmir/f64-sqrt} ops))
      (is (contains-bytes? x86-code [0xf2 0x0f 0x58 0xc1]))
      (is (contains-bytes? arm-code [0x00 0x28 0x61 0x1e])))))

(deftest f32-production-slice-routes-through-machine-ir
  (let [binary-forms
        {'f32-add '(f32-add (f32-from-bits 1065353216)
                            (f32-from-bits 1073741824))
         'f32-sub '(f32-sub 1 2) 'f32-mul '(f32-mul 1 2)
         'f32-div '(f32-div 1 2) 'f32-min '(f32-min 1 2)
         'f32-max '(f32-max 1 2) 'f32-eq '(f32-eq 1 2)
         'f32-lt '(f32-lt 1 2) 'f32-le '(f32-le 1 2)
         'f32-gt '(f32-gt 1 2) 'f32-ge '(f32-ge 1 2)
         'f32-unordered '(f32-unordered 1 2)}
        unary-forms {'f32-from-bits '(f32-from-bits 1)
                     'f32-to-bits '(f32-to-bits 1)
                     'f32-abs '(f32-abs 1) 'f32-neg '(f32-neg 1)
                     'f32-sqrt '(f32-sqrt 1)}]
    (doseq [[op form] (concat binary-forms unary-forms)]
      (is (machine/pilot-expression? [] form) (str op))
      (is (seq (machine/compile-expression :x86-64 [] form)) (str op " x86"))
      (is (seq (machine/compile-expression :aarch64 [] form)) (str op " arm")))
    (let [gmir (machine/lower-kir-expression []
                 '(f32-sqrt (f32-add (f32-from-bits 1065353216)
                                     (f32-from-bits 1073741824))))
          ops (mapv :gmir/op (:gmir/instructions gmir))
          x86-code (machine/compile-expression :x86-64 []
                     '(f32-add (f32-from-bits 1065353216)
                               (f32-from-bits 1073741824)))
          arm-code (machine/compile-expression :aarch64 []
                     '(f32-add (f32-from-bits 1065353216)
                               (f32-from-bits 1073741824)))]
      (is (some #{:gmir/f32-add} ops))
      (is (some #{:gmir/f32-sqrt} ops))
      (is (contains-bytes? x86-code [0xf3 0x0f 0x58 0xc1]))
      (is (contains-bytes? arm-code [0x00 0x28 0x20 0x1e])))))

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
