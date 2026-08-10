(ns kotoba.native.aggregate-abi
  "Portable contract for aggregates that reach a native function boundary.

  The established emitters already pass records as one-word pair-chain
  handles. The extracted GMIR path has no call operation yet. Keeping those
  facts in one closed value prevents a local SROA bundle from being mistaken
  for an external ABI and gives future call lowering an executable gate."
  (:require [clojure.set :as set]))

(def contract
  {:abi/id :kotoba.native/aggregate-boundary
   :abi/version 2
   :abi/word-bits 64
   :legacy/record
   {:boundary/parameters :pair-chain-handle
    :boundary/results :pair-chain-handle
    :boundary/word-count 1
    :boundary/layout :declaration-order
    :boundary/terminator 0
    :boundary/allocation :context-pair-arena
    :boundary/ownership :host-context
    :boundary/arena-cell-limit 4096}
   :extracted
   {:local-record :scalar-replacement
    :local-variant :scalar-replacement
    :record-boundary :held
    :variant-boundary :held
    :call-admission :scalar-admitted
    :call-requires #{:per-function-frame
                     :spill-live-values-across-call
                     :parallel-argument-assignment
                     :single-word-return-register}}
   :targets
   {:x86-64
    {:argument-registers [:x86-64/rdi :x86-64/rsi :x86-64/rdx
                          :x86-64/rcx :x86-64/r8]
     :return-register :x86-64/rax
     :allocator-registers [:x86-64/rax :x86-64/rcx :x86-64/rdx :x86-64/r8]
     :call-clobbers :all-allocator-registers}
    :aarch64
    {:argument-registers [:aarch64/x0 :aarch64/x1 :aarch64/x2
                          :aarch64/x3 :aarch64/x4]
     :return-register :aarch64/x0
     :allocator-registers [:aarch64/x0 :aarch64/x1
                           :aarch64/x2 :aarch64/x3]
     :call-clobbers :all-allocator-registers}}})

(defn- reject! [problem value]
  (throw (ex-info (str "aggregate ABI rejected: " (name problem))
                  {:phase :aggregate-abi :problem problem :value value})))

(defn scalar-record-type?
  "True for the first aggregate family eligible for a future extracted
  boundary: a named, non-empty record with unique scalar fields."
  [type]
  (and (vector? type) (= 3 (count type)) (= :record (first type))
       (keyword? (second type)) (vector? (nth type 2)) (seq (nth type 2))
       (every? #(and (vector? %) (= 2 (count %))
                     (keyword? (first %))
                     (contains? #{:i64 :bool} (second %)))
               (nth type 2))
       (= (count (nth type 2))
          (count (distinct (map first (nth type 2)))))))

(defn validate-contract!
  "Validate the published contract and return it unchanged."
  [value]
  (when-not (= #{:abi/id :abi/version :abi/word-bits :legacy/record
                 :extracted :targets}
               (set (keys value)))
    (reject! :non-canonical-contract value))
  (when-not (and (= :kotoba.native/aggregate-boundary (:abi/id value))
                 (= 2 (:abi/version value))
                 (= 64 (:abi/word-bits value)))
    (reject! :unsupported-contract-version value))
  (let [record (:legacy/record value)]
    (when-not (and (= #{:boundary/parameters :boundary/results
                        :boundary/word-count :boundary/layout
                        :boundary/terminator :boundary/allocation
                        :boundary/ownership :boundary/arena-cell-limit}
                      (set (keys record)))
                   (= :pair-chain-handle (:boundary/parameters record))
                   (= :pair-chain-handle (:boundary/results record))
                   (= 1 (:boundary/word-count record))
                   (= :declaration-order (:boundary/layout record))
                   (= 0 (:boundary/terminator record))
                   (= :context-pair-arena (:boundary/allocation record))
                   (= :host-context (:boundary/ownership record))
                   (= 4096 (:boundary/arena-cell-limit record)))
      (reject! :invalid-legacy-record-boundary record)))
  (let [extracted (:extracted value)
        required (:call-requires extracted)]
    (when-not (= #{:local-record :local-variant :record-boundary
                   :variant-boundary :call-admission :call-requires}
                 (set (keys extracted)))
      (reject! :invalid-extracted-boundary extracted))
    (when-not (and (= :scalar-replacement (:local-record extracted))
                   (= :scalar-replacement (:local-variant extracted))
                   (= :held (:record-boundary extracted))
                   (= :held (:variant-boundary extracted))
                   (= :scalar-admitted (:call-admission extracted)))
      (reject! :invalid-extracted-admission extracted))
    (when-not (= #{:per-function-frame
                   :spill-live-values-across-call
                   :parallel-argument-assignment
                   :single-word-return-register}
                 required)
      (reject! :invalid-call-prerequisites required)))
  (when-not (= #{:x86-64 :aarch64} (set (keys (:targets value))))
    (reject! :invalid-target-set (:targets value)))
  (doseq [[target {:keys [argument-registers return-register
                          allocator-registers call-clobbers]}]
          (:targets value)]
    (when-not (and (contains? #{:x86-64 :aarch64} target)
                   (= #{:argument-registers :return-register
                        :allocator-registers :call-clobbers}
                      (set (keys (get (:targets value) target))))
                   (vector? argument-registers) (= 5 (count argument-registers))
                   (= (count argument-registers)
                      (count (distinct argument-registers)))
                   (keyword? return-register)
                   (vector? allocator-registers) (seq allocator-registers)
                   (contains? (set allocator-registers) return-register)
                   (= :all-allocator-registers call-clobbers))
      (reject! :invalid-target-call-profile
               {target (get (:targets value) target)})))
  value)

(defn record-boundary-plan
  "Return the established one-word record boundary for an eligible scalar
  record. This describes the legacy path; it does not admit extracted calls."
  [type]
  (when-not (scalar-record-type? type)
    (reject! :unsupported-record-type type))
  (assoc (:legacy/record contract)
         :boundary/type type
         :boundary/extracted-admission :held))

(defn call-profile [target]
  (or (get-in contract [:targets target])
      (reject! :unsupported-target target)))

(defn admit-extracted-call!
  "Fail closed until a call implementation supplies every frame/clobber
  guarantee and the versioned contract deliberately flips admission."
  [target guarantees]
  (let [profile (call-profile target)
        required (get-in contract [:extracted :call-requires])
        supplied (set guarantees)
        missing (set/difference required supplied)]
    (when (seq missing)
      (reject! :missing-call-guarantees
               {:target target :missing missing :profile profile}))
    (when-not (= :scalar-admitted
                 (get-in contract [:extracted :call-admission]))
      (reject! :call-abi-not-admitted
               {:target target :required required :profile profile}))
    profile))

(defn reject-unextracted-call!
  "The standalone expression producer invokes this for call-shaped values.
  Calls are admitted only inside a validated GMIR v3 function module."
  [form]
  (reject! :call-abi-not-admitted
           {:form form
            :required (get-in contract [:extracted :call-requires])}))

(validate-contract! contract)
