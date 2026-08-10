(ns kotoba.native.aggregate-abi-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.native.aggregate-abi :as abi]
            [kotoba.native.machine-ir :as machine]))

(def scalar-pair
  [:record :test/pair [[:left :i64] [:ready :bool]]])

(deftest published-edn-is-the-portable-contract
  (let [published (-> "aggregate-abi.edn" io/resource slurp edn/read-string)]
    (is (= abi/contract published))
    (is (= published (abi/validate-contract! published)))
    (doseq [invalid [(update published :targets dissoc :aarch64)
                     (assoc-in published [:legacy/record :ambient/policy] true)
                     (assoc-in published [:targets :x86-64 :ambient/policy] true)
                     (update published :extracted dissoc :variant-boundary)]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (abi/validate-contract! invalid))))))

(deftest established-record-boundary-is-one-owned-handle
  (let [plan (abi/record-boundary-plan scalar-pair)]
    (is (= :pair-chain-handle (:boundary/parameters plan)))
    (is (= :pair-chain-handle (:boundary/results plan)))
    (is (= 1 (:boundary/word-count plan)))
    (is (= :host-context (:boundary/ownership plan)))
    (is (= 4096 (:boundary/arena-cell-limit plan)))
    (is (= :held (:boundary/extracted-admission plan))))
  (doseq [type [[:record :test/empty []]
                [:record :test/nested [[:value [:record :test/inner [[:x :i64]]]]]]
                [:record :test/duplicate [[:x :i64] [:x :bool]]]
                [:variant :test/v [[:x :i64]]]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (abi/record-boundary-plan type)) type)))

(deftest every-allocator-register-is-call-clobbered
  (doseq [target [:x86-64 :aarch64]]
    (let [{:keys [allocator-registers return-register call-clobbers]}
          (abi/call-profile target)]
      (is (= :all-allocator-registers call-clobbers) target)
      (is (contains? (set allocator-registers) return-register) target)))
  (is (thrown? clojure.lang.ExceptionInfo (abi/call-profile :riscv64))))

(deftest scalar-call-admission-requires-all-versioned-guarantees
  (testing "missing preservation facts are named"
    (try
      (abi/admit-extracted-call! :x86-64 #{:per-function-frame})
      (is false "call must fail without every guarantee")
      (catch clojure.lang.ExceptionInfo error
        (is (= :missing-call-guarantees (:problem (ex-data error))))
        (is (= #{:spill-live-values-across-call
                 :parallel-argument-assignment
                 :single-word-return-register}
               (get-in (ex-data error) [:value :missing]))))))
  (testing "the complete scalar call proof returns the target profile"
    (is (= :all-allocator-registers
           (:call-clobbers
            (abi/admit-extracted-call!
             :aarch64
             #{:per-function-frame
               :spill-live-values-across-call
               :parallel-argument-assignment
               :single-word-return-register})))))
  (testing "standalone expressions still report the module boundary"
    (try
      (machine/lower-kir-expression ['x] '(callee x))
      (is false "call-shaped KIR must not enter GMIR")
      (catch clojure.lang.ExceptionInfo error
        (is (= :aggregate-abi (:phase (ex-data error))))
        (is (= :call-abi-not-admitted (:problem (ex-data error)))))))
  (is (not (machine/pilot-expression? ['x] '(callee x)))))
