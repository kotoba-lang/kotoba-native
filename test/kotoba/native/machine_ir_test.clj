(ns kotoba.native.machine-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.native.machine-ir :as machine]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))

(def spill-program
  (let [registers (mapv gmir/vreg (range 6))]
    {:gmir/version 1
     :gmir/instructions
     (vec (concat
           (map-indexed (fn [index register]
                          {:gmir/op :gmir/constant :gmir/dst register
                           :gmir/value index})
                        registers)
           [{:gmir/op :gmir/add :gmir/dst (gmir/vreg 6)
             :gmir/left (first registers) :gmir/right (last registers)}
            {:gmir/op :gmir/return :gmir/value (gmir/vreg 6)}]))}))

(def program
  {:gmir/version 1
   :gmir/instructions
   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
    {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
    {:gmir/op :gmir/branch-zero :gmir/test v2 :gmir/target :test.label/zero}
    {:gmir/op :gmir/return :gmir/value v2}
    {:gmir/op :gmir/label :gmir/id :test.label/zero}
    {:gmir/op :gmir/return :gmir/value v1}]})

(deftest closed-gmir-reaches-allocated-mc-for-both-targets
  (doseq [target [:x86-64 :aarch64]]
    (let [mc (machine/compile-gmir target program)]
      (is (= target (:mc/target mc)))
      (is (= :mc/branch-zero
             (get-in mc [:mc/instructions 3 :mc/op])))
      (is (= :mir/label (get-in mc [:mc/instructions 5 :mir/op])))
      (is (not-any? #(and (keyword? %)
                          (= "kotoba.gmir.vreg" (namespace %)))
                    (tree-seq coll? seq mc))))))

(deftest allocation-is-deterministic-and-fails-closed
  (is (= (machine/compile-gmir :x86-64 program)
         (machine/compile-gmir :x86-64 program)))
  (testing "use before definition"
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/compile-gmir
                  :x86-64
                  {:gmir/version 1
                   :gmir/instructions
                   [{:gmir/op :gmir/return :gmir/value v0}]}))))
  (testing "unknown operations do not fall through"
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/compile-gmir
                  :aarch64
                  {:gmir/version 1
                   :gmir/instructions [{:gmir/op :gmir/magic}]})))))

(deftest shared-mc-contract-gates-the-target-encoder
  (let [mc (machine/compile-gmir :x86-64 program)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/encode-mc
                  (assoc-in mc [:mc/instructions 0 :mc/encoding]
                            :aarch64/argument))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/encode-mc
                  (assoc-in mc [:mc/instructions 0 :ambient/policy] true))))))

(deftest exhausted-register-profile-encodes-bounded-spills-for-both-isas
  (let [x86-mc (machine/compile-gmir :x86-64 spill-program)
        arm-mc (machine/compile-gmir :aarch64 spill-program)
        x86 (machine/encode-mc x86-mc)
        arm (machine/encode-mc arm-mc)]
    (is (= 7 (:mc/frame-slots x86-mc)))
    (is (= 7 (:mc/frame-slots arm-mc)))
    (is (= [0x48 0x81 0xec 0x40 0x00 0x00 0x00]
           (subvec x86 0 7)))
    (is (= [0x48 0x89 0x84 0x24 0x00 0x00 0x00 0x00]
           (subvec x86 17 25)))
    (is (= [0x48 0x81 0xc4 0x40 0x00 0x00 0x00 0xc3]
           (subvec x86 (- (count x86) 8))))
    (is (= [0xff 0x03 0x01 0xd1] (subvec arm 0 4)))
    (is (= [0xe0 0x03 0x00 0xf9] (subvec arm 20 24)))
    (is (= [0xff 0x03 0x01 0x91 0xc0 0x03 0x5f 0xd6]
           (subvec arm (- (count arm) 8))))))

(deftest kir-expression-slice-encodes-final-bytes-for-both-isas
  (is (= [0x48 0x89 0xf8             ; mov rax,rdi
          0x48 0x89 0xf1             ; mov rcx,rsi
          0x48 0x89 0xc2             ; mov rdx,rax
          0x48 0x01 0xca             ; add rdx,rcx
          0x48 0x89 0xd0 0xc3]       ; mov rax,rdx; ret
         (machine/compile-expression :x86-64 ['a 'b] '(+ a b))))
  (is (= [0x02 0x00 0x01 0x8b       ; add x2,x0,x1
          0xe0 0x03 0x02 0xaa       ; mov x0,x2
          0xc0 0x03 0x5f 0xd6]      ; ret
         (machine/compile-expression :aarch64 ['a 'b] '(+ a b)))))

(deftest recursive-i64-arithmetic-reaches-final-bytes-for-both-isas
  (doseq [form ['(- a) '(- a b) '(* a b) '(quot a b)
                '(bit-and a b) '(bit-or a b) '(bit-xor a b)
                '(+ (* a b) (- a b)) '(+ a b 3 4)
                '(bit-xor a b 3 4)]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x02 0x00 0x01 0xcb 0xe0 0x03 0x02 0xaa 0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 ['a 'b] '(- a b))))
  (is (machine/pilot-expression? ['a 'b]
                                 '(+ (* a 6) (bit-xor (- a b) 3)))))

(deftest parameters-are-materialized-before-expression-temporaries
  ;; AArch64 passes arguments in the same x0-x4 register set used by this
  ;; bounded allocator. If a constant is emitted first, it can overwrite an
  ;; ABI argument before the later `:gmir/argument` instruction reads it.
  (doseq [form ['(- a) '(+ 1 a) '(* 2 (+ 3 a)) '(* a 48271N)]]
    (let [instructions (:gmir/instructions
                        (machine/lower-kir-expression ['a] form))]
      (is (= :gmir/argument (:gmir/op (first instructions))) form)
      (is (= 0 (:gmir/index (first instructions))) form)
      (is (seq (machine/compile-expression :aarch64 ['a] form)) form))))

(deftest x86-signed-division-preserves-all-implicit-registers
  (let [bytes (machine/compile-expression
               :x86-64 [] '(+ (* 3 4) (quot 10 2)))
        division-window [0x50             ; push rax
                         0x52             ; push rdx (live product)
                         0x51             ; push rcx
                         0x48 0x8b 0x8c 0x24 0x10 0x00 0x00 0x00 ; divisor
                         0x4c 0x89 0xc0   ; mov rax,r8 (dividend)
                         0x48 0x99         ; cqo
                         0x48 0xf7 0xf9   ; idiv rcx
                         0x48 0x89 0xc1   ; quotient -> allocated rcx
                         0x48 0x81 0xc4 0x08 0x00 0x00 0x00 ; discard old rcx
                         0x5a             ; restore live rdx
                         0x58]]           ; restore rax
    (is (= 1 (count (filter #(= division-window %)
                            (partition (count division-window) 1 bytes)))))))

(deftest aarch64-signed-division-explicitly-traps-kir-error-cases
  (let [bytes (machine/compile-expression :aarch64 ['a 'b] '(quot a b))
        words (mapv vec (partition 4 bytes))]
    (is (= 1 (count (filter #(= [0x00 0x00 0x20 0xd4] %) words)))
        "BRK is shared by the zero and MIN/-1 guards")
    (is (some #(= [0x02 0x0c 0xc1 0x9a] %) words)
        "the guarded operation remains sdiv x2,x0,x1 after allocation")))

(deftest scalar-comparisons-and-predicates-reach-final-bytes-for-both-isas
  (doseq [form ['(= a b) '(< a b) '(> a b) '(<= a b) '(>= a b)
                '(< a b 9) '(= a b 9)
                '(not a) '(zero? a) '(pos? a) '(neg? a)]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x48 0x89 0xf8 0x48 0x89 0xf1
          0x48 0x39 0xc8 0x0f 0x9c 0xc2 0x48 0x0f 0xb6 0xd2
          0x48 0x89 0xd0 0xc3]
         (machine/compile-expression :x86-64 ['a 'b] '(< a b))))
  (is (= [0x1f 0x00 0x01 0xeb 0xe2 0xa7 0x9f 0x9a
          0xe0 0x03 0x02 0xaa 0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 ['a 'b] '(< a b)))))

(deftest booleans-let-nested-tail-if-and-five-arguments-are-admitted
  (doseq [form [true false
                '(let [x (+ a b) y (* x c)] (if (< y d) y e))
                '(if (< a b) (if c 11 12) (if d 21 22))]]
    (is (machine/pilot-expression? ['a 'b 'c 'd 'e] form) form)
    (is (seq (machine/compile-expression :x86-64 ['a 'b 'c 'd 'e] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b 'c 'd 'e] form)) form)))

(deftest ordered-do-reaches-production-ir-without-dropping-traps
  (let [form '(do (+ a 1) (quot a b) (* a b))
        instructions (:gmir/instructions
                      (machine/lower-kir-expression ['a 'b] form))
        operations (mapv :gmir/op instructions)
        x86 (machine/compile-expression :x86-64 ['a 'b] form)
        arm (machine/compile-expression :aarch64 ['a 'b] form)]
    (is (machine/pilot-expression? ['a 'b] form))
    (is (< (.indexOf operations :gmir/add)
           (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/multiply))
        "all do forms retain source evaluation order")
    (is (= :gmir/return (last operations)))
    (is (= 1 (count (filter #(= [0x48 0xf7 0xf9] %)
                            (partition 3 1 x86))))
        "an unused x86 quotient still executes and can trap")
    (is (= 1 (count (filter #(= [0x00 0x00 0x20 0xd4] %)
                            (partition 4 arm))))
        "an unused AArch64 quotient retains the shared BRK guards"))
  (is (machine/pilot-expression? [] '(do 1)))
  (is (not (machine/pilot-expression? [] '(do)))
      "empty do has nil semantics and is outside the scalar i64 contract"))

(deftest ordered-do-can-delegate-its-final-expression-to-tail-control
  (let [form '(do (+ a 1) (quot a b) (if (< a b) 11 22))
        instructions (:gmir/instructions
                      (machine/lower-kir-expression ['a 'b] form))
        operations (mapv :gmir/op instructions)]
    (is (machine/pilot-expression? ['a 'b] form))
    (is (< (.indexOf operations :gmir/add)
           (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/less-than)
           (.indexOf operations :gmir/branch-zero))
        "prefix effects and traps execute before the tail condition")
    (is (= 2 (count (filter #(= :gmir/return %) operations)))
        "both tail arms return without a synthetic merge")
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (machine/compile-expression target ['a 'b] form)) target)))
  (is (machine/pilot-expression? ['a]
                                 '(do (do (+ a 1))
                                      (if a (do 11) (do 22)))))
  (is (not (machine/pilot-expression? ['a]
                                      '(do (if a 1 2) 3)))
      "a non-final if remains outside value lowering and cannot be reordered"))

(deftest final-layout-resolves-branches-after-selected-instruction-sizes
  (let [x86 (machine/compile-expression :x86-64 ['p] '(if p 11 22))
        arm (machine/compile-expression :aarch64 ['p] '(if p 11 22))]
    (is (= [0x0f 0x84 0x0e 0x00 0x00 0x00] (subvec x86 6 12))
        "x86 jz skips the selected then arm using next-PC rel32")
    (is (= [0xe0 0x00 0x00 0xb4] (subvec arm 0 4))
        "AArch64 cbz x0 reaches the final else label at +28 bytes")
    (is (= 40 (count x86)))
    (is (= 52 (count arm)))))

(deftest kir-to-gmir-boundary-rejects-unsupported-shapes
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/compile-expression :aarch64 ['a] '(+ a (if a 1 2))))))

(deftest full-signed-i64-immediates-have-fixed-wire-bytes
  (is (= [0x48 0xb8 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0xc3]
         (machine/compile-expression :x86-64 [] Long/MAX_VALUE)))
  (is (= [0xe0 0xff 0x9f 0xd2 0xe0 0xff 0xbf 0xf2
          0xe0 0xff 0xdf 0xf2 0xe0 0xff 0xef 0xf2
          0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 [] Long/MAX_VALUE)))
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/compile-expression :x86-64 [] (inc (bigint Long/MAX_VALUE))))))
