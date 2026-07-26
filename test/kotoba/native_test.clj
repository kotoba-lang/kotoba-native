(ns kotoba.native-test
  (:require [clojure.test :refer [deftest is]]
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
