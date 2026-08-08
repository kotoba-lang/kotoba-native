(ns kotoba.native.machine-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.native.machine-ir :as machine]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))

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
               (machine/compile-expression :x86-64 ['a] '(* a 2))))
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
