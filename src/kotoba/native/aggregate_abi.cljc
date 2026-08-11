(ns kotoba.native.aggregate-abi
  "Portable contract for aggregates that reach a native function boundary.

  Word-field records, including recursively nested records, and scalar variants
  cross extracted calls as one-word context-owned pair handles. Local flat
  non-escaping aggregates remain replaced."
  (:require [clojure.set :as set]))

(def contract
  {:abi/id :kotoba.native/aggregate-boundary
   :abi/version 6
   :abi/word-bits 64
   :portable/record
   {:boundary/parameters :pair-chain-handle
    :boundary/results :pair-chain-handle
    :boundary/word-count 1
    :boundary/layout :declaration-order
    :boundary/field-representation :recursive-word-handles
    :boundary/max-nesting-depth 32
    :boundary/terminator 0
    :boundary/allocation :context-pair-arena
    :boundary/ownership :host-context
    :boundary/arena-cell-limit 4096}
   :portable/variant
   {:boundary/parameters :pair-tag-payload-handle
    :boundary/results :pair-tag-payload-handle
    :boundary/word-count 1
    :boundary/tag :zero-based-declaration-ordinal
    :boundary/payload-types #{:i64 :bool}
    :boundary/bool-words #{0 1}
    :boundary/case-limit 32
    :boundary/allocation :context-pair-arena
    :boundary/ownership :host-context
    :boundary/arena-cell-limit 4096}
   :extracted
   {:local-record :scalar-replacement
    :local-variant :scalar-replacement
    :record-boundary :word-pair-chain-admitted
    :variant-boundary :scalar-pair-handle-admitted
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

(def ^:private max-record-nesting-depth 32)

(defn scalar-record-type?
  "True for a named, non-empty record whose unique fields each occupy one
  native word. A nested record occupies one word through its pair-chain handle;
  nesting is bounded so adversarial schemas fail closed during admission."
  [type]
  (letfn [(record-type? [candidate depth]
            (and (< depth max-record-nesting-depth)
                 (vector? candidate) (= 3 (count candidate))
                 (= :record (first candidate))
                 (keyword? (second candidate))
                 (vector? (nth candidate 2)) (seq (nth candidate 2))
                 (every? #(and (vector? %) (= 2 (count %))
                               (keyword? (first %))
                               (word-field-type? (second %) (inc depth)))
                         (nth candidate 2))
                 (= (count (nth candidate 2))
                    (count (distinct (map first (nth candidate 2)))))))
          (word-field-type? [field-type depth]
            (or (contains? #{:i64 :bool :f32 :f64 :string :keyword
                             :vector :vector-f64 :string-index}
                           field-type)
                (and (vector? field-type)
                     (contains? #{:option :result :list :set :map :ref}
                                (first field-type)))
                (record-type? field-type depth)))]
    (record-type? type 0)))

(defn nested-record-type?
  "True when TYPE is admitted and contains at least one inline record field."
  [type]
  (and (scalar-record-type? type)
       (boolean
        (some (fn [[_ field-type]]
                (and (vector? field-type)
                     (= :record (first field-type))))
              (nth type 2)))))

(defn validate-contract!
  "Validate the published contract and return it unchanged."
  [value]
  (when-not (= #{:abi/id :abi/version :abi/word-bits :portable/record
                 :portable/variant
                 :extracted :targets}
               (set (keys value)))
    (reject! :non-canonical-contract value))
  (when-not (and (= :kotoba.native/aggregate-boundary (:abi/id value))
                 (= 6 (:abi/version value))
                 (= 64 (:abi/word-bits value)))
    (reject! :unsupported-contract-version value))
  (let [record (:portable/record value)]
    (when-not (and (= #{:boundary/parameters :boundary/results
                        :boundary/word-count :boundary/layout
                        :boundary/field-representation :boundary/max-nesting-depth
                        :boundary/terminator :boundary/allocation
                        :boundary/ownership :boundary/arena-cell-limit}
                      (set (keys record)))
                   (= :pair-chain-handle (:boundary/parameters record))
                   (= :pair-chain-handle (:boundary/results record))
                   (= 1 (:boundary/word-count record))
                   (= :declaration-order (:boundary/layout record))
                   (= :recursive-word-handles (:boundary/field-representation record))
                   (= 32 (:boundary/max-nesting-depth record))
                   (= 0 (:boundary/terminator record))
                   (= :context-pair-arena (:boundary/allocation record))
                   (= :host-context (:boundary/ownership record))
                   (= 4096 (:boundary/arena-cell-limit record)))
      (reject! :invalid-portable-record-boundary record)))
  (let [variant (:portable/variant value)]
    (when-not (and (= #{:boundary/parameters :boundary/results
                        :boundary/word-count :boundary/tag :boundary/payload-types
                        :boundary/bool-words :boundary/case-limit
                        :boundary/allocation :boundary/ownership
                        :boundary/arena-cell-limit}
                      (set (keys variant)))
                   (= :pair-tag-payload-handle (:boundary/parameters variant))
                   (= :pair-tag-payload-handle (:boundary/results variant))
                   (= 1 (:boundary/word-count variant))
                   (= :zero-based-declaration-ordinal (:boundary/tag variant))
                   (= #{:i64 :bool} (:boundary/payload-types variant))
                   (= #{0 1} (:boundary/bool-words variant))
                   (= 32 (:boundary/case-limit variant))
                   (= :context-pair-arena (:boundary/allocation variant))
                   (= :host-context (:boundary/ownership variant))
                   (= 4096 (:boundary/arena-cell-limit variant)))
      (reject! :invalid-portable-variant-boundary variant)))
  (let [extracted (:extracted value)
        required (:call-requires extracted)]
    (when-not (= #{:local-record :local-variant :record-boundary
                   :variant-boundary :call-admission :call-requires}
                 (set (keys extracted)))
      (reject! :invalid-extracted-boundary extracted))
    (when-not (and (= :scalar-replacement (:local-record extracted))
                   (= :scalar-replacement (:local-variant extracted))
                   (= :word-pair-chain-admitted (:record-boundary extracted))
                   (= :scalar-pair-handle-admitted (:variant-boundary extracted))
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
  "Return the admitted one-word scalar record boundary plan."
  [type]
  (when-not (scalar-record-type? type)
    (reject! :unsupported-record-type type))
  (assoc (:portable/record contract)
         :boundary/type type
         :boundary/extracted-admission :admitted))

(defn scalar-variant-type?
  "True for the admitted sealed scalar variant boundary family."
  [type]
  (and (vector? type) (= 3 (count type)) (= :variant (first type))
       (keyword? (second type)) (some? (namespace (second type)))
       (vector? (nth type 2)) (<= 1 (count (nth type 2)) 32)
       (every? #(and (vector? %) (= 2 (count %))
                     (keyword? (first %))
                     (contains? #{:i64 :bool} (second %)))
               (nth type 2))
       (= (count (nth type 2))
          (count (distinct (map first (nth type 2)))))))

(defn variant-boundary-plan
  "Return the admitted one-word scalar variant boundary plan."
  [type]
  (when-not (scalar-variant-type? type)
    (reject! :unsupported-variant-type type))
  (assoc (:portable/variant contract)
         :boundary/type type
         :boundary/cases (mapv first (nth type 2))
         :boundary/extracted-admission :admitted))

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
