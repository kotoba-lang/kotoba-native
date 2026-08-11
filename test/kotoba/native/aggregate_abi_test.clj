(ns kotoba.native.aggregate-abi-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.native.aggregate-abi :as abi]
            [kotoba.native.machine-ir :as machine]))

(def scalar-pair
  [:record :test/pair [[:left :i64] [:ready :bool]]])

(def word-record
  [:record :test/word [[:maybe [:option :i64]] [:text :string]]])

(def nested-record
  [:record :test/nested [[:value [:record :test/inner [[:x :i64]]]]]])

(def scalar-variant
  [:variant :test/outcome [[:count :i64] [:ready :bool]]])

(def aggregate-variant
  [:variant :test/aggregate-outcome
   [[:pair scalar-pair] [:nested nested-record] [:count :i64]]])

(deftest published-edn-is-the-portable-contract
  (let [published (-> "aggregate-abi.edn" io/resource slurp edn/read-string)]
    (is (= abi/contract published))
    (is (= published (abi/validate-contract! published)))
    (doseq [invalid [(update published :targets dissoc :aarch64)
                     (assoc-in published [:portable/record :ambient/policy] true)
                     (assoc-in published [:portable/variant :boundary/case-limit] 33)
                     (assoc-in published [:targets :x86-64 :ambient/policy] true)
                     (update published :extracted dissoc :variant-boundary)]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (abi/validate-contract! invalid))))))

(deftest scalar-record-boundary-is-one-owned-admitted-handle
  (let [plan (abi/record-boundary-plan scalar-pair)]
    (is (= :pair-chain-handle (:boundary/parameters plan)))
    (is (= :pair-chain-handle (:boundary/results plan)))
    (is (= 1 (:boundary/word-count plan)))
    (is (= :host-context (:boundary/ownership plan)))
    (is (= 4096 (:boundary/arena-cell-limit plan)))
    (is (= :admitted (:boundary/extracted-admission plan))))
  (is (= :admitted
         (:boundary/extracted-admission
          (abi/record-boundary-plan word-record))))
  (let [plan (abi/record-boundary-plan nested-record)]
    (is (= :recursive-word-handles (:boundary/field-representation plan)))
    (is (= 32 (:boundary/max-nesting-depth plan))))
  (doseq [type [[:record :test/empty []]
                [:record :test/duplicate [[:x :i64] [:x :bool]]]
                [:variant :test/v [[:x :i64]]]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (abi/record-boundary-plan type)) type)))

(deftest recursive-record-boundary-is-depth-bounded
  (let [nested (fn [depth]
                 (reduce (fn [field-type index]
                           [:record (keyword "test" (str "level-" index))
                            [[:value field-type]]])
                         :i64
                         (range depth)))]
    (is (= :admitted
           (:boundary/extracted-admission
            (abi/record-boundary-plan (nested 32)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (abi/record-boundary-plan (nested 33))))))

(deftest scalar-variant-boundary-is-one-owned-checked-handle
  (let [plan (abi/variant-boundary-plan scalar-variant)]
    (is (= :pair-tag-payload-handle (:boundary/parameters plan)))
    (is (= :pair-tag-payload-handle (:boundary/results plan)))
    (is (= :zero-based-declaration-ordinal (:boundary/tag plan)))
    (is (= [:count :ready] (:boundary/cases plan)))
    (is (= [:i64 :bool] (:boundary/payload-schemas plan)))
    (is (= #{:i64 :bool :record} (:boundary/payload-types plan)))
    (is (= #{0 1} (:boundary/bool-words plan)))
    (is (= :admitted (:boundary/extracted-admission plan))))
  (let [plan (abi/variant-boundary-plan aggregate-variant)]
    (is (abi/aggregate-payload-variant-type? aggregate-variant))
    (is (= [scalar-pair nested-record :i64]
           (:boundary/payload-schemas plan)))
    (is (= :recursive-word-handles
           (:boundary/payload-representation plan)))
    (is (= 32 (:boundary/max-payload-nesting-depth plan))))
  (doseq [type [[:variant :unqualified [[:x :i64]]]
                [:variant :test/empty []]
                [:variant :test/duplicate [[:x :i64] [:x :bool]]]
                [:variant :test/text [[:x :string]]]
                [:record :test/not-variant [[:x :i64]]]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (abi/variant-boundary-plan type)) type)))

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

(deftest callable-and-linkage-admission-is-closed-and-bounded
  (let [{:keys [callable-dispatch linkage]} (:extracted abi/contract)]
    (is (= :closed-ordinal-dispatch (:indirect callable-dispatch)))
    (is (= :bounded-pair-chain (:apply callable-dispatch)))
    (is (= 4 (:max-apply-arguments callable-dispatch)))
    (is (false? (:arbitrary-address callable-dispatch)))
    (is (= :closed-module-graph (:mode linkage)))
    (is (false? (:ambient-symbols linkage)))
    (is (false? (:unresolved-symbols linkage))))
  (let [evidence {:mode :closed-module-graph
                  :module-graph-digest (apply str (repeat 64 "a"))
                  :unresolved-symbols #{}
                  :ambient-symbols false}]
    (is (= evidence (abi/admit-closed-linkage! evidence)))
    (doseq [invalid [(assoc evidence :unresolved-symbols #{'missing})
                     (assoc evidence :ambient-symbols true)
                     (assoc evidence :module-graph-digest "not-a-digest")
                     (dissoc evidence :unresolved-symbols)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"unsealed-external-linkage"
                            (abi/admit-closed-linkage! invalid))))))
