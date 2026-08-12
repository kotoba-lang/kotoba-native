(ns kotoba.native.elf64-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.artifact.core :as artifact]
            [kotoba.native.elf64 :as elf64]))

(defn- sealed-kernel [target fuel]
  (artifact/seal
   {:target target
    :target-profile {:runtime :none :ambient-syscalls false}
    :program {:entry 'main}
    :exports {'main {:offset 0 :arity 0}}
    :limits {:fuel fuel}
    :fuel-abi {:initial fuel}
    :code [0xc3]}))

(defn- le64 [bytes offset]
  (reduce (fn [value index]
            (+ value (bit-shift-left (long (nth bytes (+ offset index)))
                                     (* index 8))))
          0 (range 8)))

(deftest kernel-image-context-uses-the-sealed-fuel-bound
  (doseq [[target package]
          [[:x86_64-aiueos-kernel-v1 elf64/package-kernel]
           [:aarch64-aiueos-kernel-v1 elf64/package-kernel-aarch64]]]
    (let [fuel 4096
          image (:bytes (package (sealed-kernel target fuel)))]
      (is (= fuel (le64 image (+ (if (= target :x86_64-aiueos-kernel-v1)
                                    0xb000
                                    0x8000)
                                 8)))
          (str target)))))

(deftest kernel-image-rejects-disagreeing-fuel-identities
  (let [value (assoc (sealed-kernel :x86_64-aiueos-kernel-v1 4096)
                     :fuel-abi {:initial 512})]
    (testing "resealing does not make contradictory context authority valid"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"one valid sealed fuel bound"
                            (elf64/package-kernel
                             (artifact/seal (dissoc value :sha256))))))))
