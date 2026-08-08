(ns kotoba.native.machine-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.machine-ir :as machine]))

(def v0 (machine/vreg 0))
(def v1 (machine/vreg 1))
(def v2 (machine/vreg 2))

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
      (is (= :mir/relative-branch
             (get-in mc [:mc/instructions 3 :mir/op])))
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
