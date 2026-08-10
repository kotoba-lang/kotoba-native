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
  (doseq [form ['(- a b) '(* a b) '(quot a b)
                '(bit-and a b) '(bit-or a b) '(bit-xor a b)
                '(+ (* a b) (- a b))]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x02 0x00 0x01 0xcb 0xe0 0x03 0x02 0xaa 0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 ['a 'b] '(- a b))))
  (is (machine/pilot-expression? ['a 'b]
                                 '(+ (* a 6) (bit-xor (- a b) 3)))))

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
               (machine/compile-expression :x86-64 ['a] '(< a 2))))
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
