(ns kotoba.native-test
  (:require [clojure.test :refer [deftest is]]
            [kotoba.native.x86-64]
            [kotoba.native.aarch64]
            [kotoba.native.elf64]))

;; Load gate: the split must not break namespace resolution. Each extracted
;; namespace must load standalone from this repo's own dependency closure.
(deftest every-extracted-namespace-loads
  (is (some? (find-ns 'kotoba.native.x86-64)) "kotoba.native.x86-64 must load")
  (is (some? (find-ns 'kotoba.native.aarch64)) "kotoba.native.aarch64 must load")
  (is (some? (find-ns 'kotoba.native.elf64)) "kotoba.native.elf64 must load"))
