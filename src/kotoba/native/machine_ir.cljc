(ns kotoba.native.machine-ir
  "Closed production contract for GMIR -> target MIR -> allocated MC data.

  The existing production emitters are migrated incrementally. This namespace
  makes the missing layers explicit without pretending arbitrary KIR is already
  covered: the admitted integer/control subset is closed and every unknown op,
  use-before-definition, register exhaustion, or malformed label fails closed."
  (:require [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]
            [kotoba.codegen.mc :as mc]
            [kotoba.codegen.layout :as layout]
            [kotoba.native.aggregate-abi :as aggregate-abi]
            #?(:cljs [kotoba.kir.cljs-i64 :as i64])))

(defn- reject! [phase problem instruction]
  (throw (ex-info (str "machine IR rejected: " (name problem))
                  {:phase phase :problem problem :instruction instruction})))

(defn- lower-mc-instructions [isa instructions]
  (mapv (fn [{:mir/keys [op id test] :as instruction}]
          (case op
            :mir/label (layout/label id)
            :mir/branch-zero
            {:mc/op :mc/branch-zero :mc/test test
             :mc/target (:mir/target instruction)}
            :mir/jump
            {:mc/op :mc/jump :mc/target (:mir/target instruction)}
            (into {:mc/op :mc/instruction
                   :mc/encoding (keyword (name isa) (name op))}
                  (remove (fn [[k _]] (= k :mir/op)) instruction))))
        instructions))

(defn lower-mc
  "Lower allocated MIR to explicit MC instruction/layout data.

  Instruction bytes remain owned by the target encoders. Branches become the
  same layout tokens used by production backends, so PC-relative values cannot
  be baked before final sizes are known."
  [{:mir/keys [version target registers frame-slots instructions entry functions]
    :as program}]
  (mir/validate! program)
  (when-not (= :physical registers)
    (reject! :mc :registers-not-allocated program))
  (mc/validate!
   (if (= 3 version)
     {:mc/version 3
      :mc/target target
      :mc/entry entry
      :mc/functions
      (mapv (fn [{:mir/keys [name arity frame-slots frame-policy instructions]}]
              {:mc/name name :mc/arity arity :mc/frame-slots frame-slots
               :mc/frame-policy frame-policy
               :mc/instructions (lower-mc-instructions target instructions)})
            functions)}
     {:mc/version 2
      :mc/target target
      :mc/frame-slots (or frame-slots 0)
      :mc/instructions (lower-mc-instructions target instructions)})))

(defn compile-gmir [target program]
  (->> program (mir/select-target target) mir/allocate-registers lower-mc))

;; ── closed KIR expression -> GMIR pilot ─────────────────────────────────────

(def ^:private kir-binary-ops
  {'+ :gmir/add '- :gmir/subtract '* :gmir/multiply
   'quot :gmir/quotient 'bit-and :gmir/bit-and
   'bit-or :gmir/bit-or 'bit-xor :gmir/bit-xor
   'i64-shift-left :gmir/shift-left
   'i64-shift-right :gmir/shift-right-signed
   'u64-shift-right :gmir/shift-right-unsigned
   '= :gmir/equal '< :gmir/less-than '> :gmir/greater-than
   '<= :gmir/less-or-equal '>= :gmir/greater-or-equal})

(def ^:private kir-predicate-ops
  {'not :gmir/equal 'zero? :gmir/equal
   'pos? :gmir/greater-than 'neg? :gmir/less-than})

(def ^:private kir-fold-ops '#{+ - * bit-and bit-or bit-xor})
(def ^:private kir-comparison-ops '#{= < > <= >=})
(def ^:private kir-word-unary-ops '#{bool-not bit-not i32-wrap u32-wrap})
(def ^:private kir-i32-binary-ops
  '#{i32-wrapping-add i32-wrapping-mul i32-xor
     i32-shift-left i32-shift-right u32-shift-right})
(def ^:private kir-f64-binary-ops
  {'f64-add :gmir/f64-add 'f64-sub :gmir/f64-subtract
   'f64-mul :gmir/f64-multiply 'f64-div :gmir/f64-divide
   'f64-min :gmir/f64-min 'f64-max :gmir/f64-max
   'f64-eq :gmir/f64-equal 'f64-lt :gmir/f64-less-than
   'f64-le :gmir/f64-less-or-equal 'f64-gt :gmir/f64-greater-than
   'f64-ge :gmir/f64-greater-or-equal
   'f64-unordered :gmir/f64-unordered})
(def ^:private kir-f64-unary-ops
  '#{f64-from-bits f64-to-bits f64-abs f64-neg f64-sqrt})
(def ^:private kir-kernel-memory-ops
  {'kernel-load-u8 [:gmir/kernel-load-u8 512]
   'kernel-load-u8-4k [:gmir/kernel-load-u8 4096]
   'kernel-load-u8-16k [:gmir/kernel-load-u8 16384]
   'kernel-store-u8 [:gmir/kernel-store-u8 512]
   'kernel-store-u8-4k [:gmir/kernel-store-u8 4096]
   'kernel-load-u32 [:gmir/kernel-load-u32 512]
   'kernel-store-u32 [:gmir/kernel-store-u32 512]})

(def ^:private kir-runtime-ops
  {'pair :pair
   'pair-first :pair-first
   'pair-second :pair-second
   'kgraph-assert! :kgraph-assert!
   'kgraph-get :kgraph-get
   'kgraph-count :kgraph-count
   'kgraph-entity-at :kgraph-entity-at
   'string-byte-length :string-byte-length
   'string=? :string=?
   'string-concat :string-concat
   'string-substring :string-substring
   'string-code-point-at :string-code-point-at
   'vector-new-empty :vector-new-empty
   'vector-conj :vector-conj
   'vector-count :vector-count
   'vector-at :vector-at
   'vector-assoc :vector-assoc
   'vector-drop :vector-drop
   'vector-f64-new :vector-new-empty
   'vector-f64-conj :vector-conj
   'vector-f64-count :vector-count
   'vector-f64-at :vector-at
   'vector-f64-assoc :vector-assoc
   'vector-f64-drop :vector-drop})

(def ^:private typed-capability-kinds
  {[:i64 :i64] :i64
   [:string :string] :string
   [:option-i64 :option-i64] :option-i64
   [:result-i64 :result-i64] :result-i64})

(defn- valid-capability-id? [value]
  (and (integer? value) (<= 0 value 255)))

(defn- scalar-literal? [form]
  (or (boolean? form) (gmir/i64-value? form)))

(defn- scalar-literal [form]
  (if (boolean? form) (if form 1 0) form))

(defn- scalar-record-fields [type]
  (when (and (vector? type) (= 3 (count type)) (= :record (first type))
             (keyword? (second type)) (vector? (nth type 2))
             (seq (nth type 2))
             (every? #(and (vector? %) (= 2 (count %))
                           (keyword? (first %))
                           (contains? #{:i64 :bool} (second %)))
                     (nth type 2))
             (= (count (nth type 2))
                (count (distinct (map first (nth type 2))))))
    (nth type 2)))

(defn- record-value? [value]
  (= :record (:aggregate/kind value)))

(defn- record-value [type values]
  {:aggregate/kind :record :aggregate/type type :aggregate/values (vec values)})

(defn- scalar-variant-cases [type]
  (when (and (vector? type) (= 3 (count type)) (= :variant (first type))
             (keyword? (second type)) (vector? (nth type 2))
             (seq (nth type 2))
             (every? #(and (vector? %) (= 2 (count %))
                           (keyword? (first %))
                           (contains? #{:i64 :bool} (second %)))
                     (nth type 2))
             (= (count (nth type 2))
                (count (distinct (map first (nth type 2))))))
    (nth type 2)))

(defn- variant-value? [value]
  (= :variant (:aggregate/kind value)))

(defn- variant-value [type tag payload]
  {:aggregate/kind :variant :aggregate/type type
   :variant/tag tag :variant/payload payload})

(defn- scalar-register! [value form]
  (if (gmir/vreg? value)
    value
    (reject! :kir-to-gmir :scalar-value-required {:form form :value value})))

(def ^:dynamic *production-routing-enabled?*
  "Migration seam used by legacy-emitter regression tests. Production leaves
  this enabled; disabling it never changes the IR contracts themselves."
  true)

(defn lower-kir-expression
  "Lower a closed pure tail-expression subset to GMIR.

  Admitted forms are integer/boolean literals, parameters, lexical `let`,
  ordered non-empty `do`, recursive scalar arithmetic/comparisons/predicates,
  tail-position `if`, fixed scalar-field records, and non-escaping scalar
  variants eliminated by SROA.
  Unsupported shapes fail closed rather than escaping to the legacy emitter."
  ([params body]
   (lower-kir-expression params body {}))
  ([params body signatures]
   (when-not (and (vector? params) (every? symbol? params)
                  (= (count params) (count (distinct params)))
                  (map? signatures)
                  (every? gmir/function-id? (keys signatures))
                  (every? #(and (integer? %) (<= 0 % 5)) (vals signatures)))
     (reject! :kir-to-gmir :invalid-parameters
              {:params params :signatures signatures}))
   (let [next-reg (atom -1)
        next-label (atom -1)
        fresh-reg #(gmir/vreg (swap! next-reg inc))
        fresh-label (fn [stem]
                      (keyword "kotoba.gmir.label"
                               (str stem "-" (swap! next-label inc))))
        parameter-registers (mapv (fn [_] (fresh-reg)) params)
        parameter-code (mapv (fn [index register]
                               {:gmir/op :gmir/argument :gmir/dst register
                                :gmir/index index})
                             (range) parameter-registers)
        parameter-env (into {} (map (fn [parameter register]
                                      [parameter [:local register]])
                                    params parameter-registers))]
    (letfn [(constant-value [literal]
              (let [dst (fresh-reg)]
                [[{:gmir/op :gmir/constant :gmir/dst dst :gmir/value literal}]
                 dst]))

            (binary-value [op [left-code left-value] [right-code right-value] form]
              (let [left (scalar-register! left-value form)
                    right (scalar-register! right-value form)
                    dst (fresh-reg)]
                [(vec (concat left-code right-code
                              [{:gmir/op op :gmir/dst dst
                                :gmir/left left :gmir/right right}]))
                 dst]))

            (signed-i32-value [[code source] form]
              (let [[count-code count-register] (constant-value 32)
                    shifted (fresh-reg)
                    dst (fresh-reg)]
                [(vec (concat code count-code
                              [{:gmir/op :gmir/shift-left :gmir/dst shifted
                                :gmir/left (scalar-register! source form)
                                :gmir/right count-register}
                               {:gmir/op :gmir/shift-right-signed :gmir/dst dst
                                :gmir/left shifted :gmir/right count-register}]))
                 dst]))

            (unsigned-i32-value [[code source] form]
              (let [[mask-code mask-register] (constant-value 4294967295)
                    dst (fresh-reg)]
                [(vec (concat code mask-code
                              [{:gmir/op :gmir/bit-and :gmir/dst dst
                                :gmir/left (scalar-register! source form)
                                :gmir/right mask-register}]))
                 dst]))

            (merge-values [then-value else-value then-exit else-exit form]
              (cond
                (and (gmir/vreg? then-value) (gmir/vreg? else-value))
                (let [dst (fresh-reg)]
                  [[{:gmir/op :gmir/phi :gmir/dst dst
                     :gmir/incomings
                     [{:gmir/predecessor then-exit :gmir/value then-value}
                      {:gmir/predecessor else-exit :gmir/value else-value}]}]
                   dst])

                (and (record-value? then-value) (record-value? else-value)
                     (= (:aggregate/type then-value)
                        (:aggregate/type else-value)))
                (let [then-values (:aggregate/values then-value)
                      else-values (:aggregate/values else-value)
                      destinations (mapv (fn [_] (fresh-reg)) then-values)]
                  (when-not (= (count then-values) (count else-values))
                    (reject! :kir-to-gmir :record-value-width-mismatch {:form form}))
                  [(mapv (fn [dst then-register else-register]
                           {:gmir/op :gmir/phi :gmir/dst dst
                            :gmir/incomings
                            [{:gmir/predecessor then-exit :gmir/value then-register}
                             {:gmir/predecessor else-exit :gmir/value else-register}]})
                         destinations then-values else-values)
                   (record-value (:aggregate/type then-value) destinations)])

                (and (variant-value? then-value) (variant-value? else-value)
                     (= (:aggregate/type then-value)
                        (:aggregate/type else-value)))
                (let [tag-dst (fresh-reg)
                      payload-dst (fresh-reg)]
                  [[{:gmir/op :gmir/phi :gmir/dst tag-dst
                     :gmir/incomings
                     [{:gmir/predecessor then-exit
                       :gmir/value (:variant/tag then-value)}
                      {:gmir/predecessor else-exit
                       :gmir/value (:variant/tag else-value)}]}
                    {:gmir/op :gmir/phi :gmir/dst payload-dst
                     :gmir/incomings
                     [{:gmir/predecessor then-exit
                       :gmir/value (:variant/payload then-value)}
                      {:gmir/predecessor else-exit
                       :gmir/value (:variant/payload else-value)}]}]
                   (variant-value (:aggregate/type then-value)
                                  tag-dst payload-dst)])

                :else
                (reject! :kir-to-gmir :branch-value-shape-mismatch
                         {:form form :then then-value :else else-value})))

            (value [form env]
              (cond
                (scalar-literal? form)
                (let [dst (fresh-reg)]
                  [[{:gmir/op :gmir/constant :gmir/dst dst
                     :gmir/value (scalar-literal form)}] dst])

                (symbol? form)
                (if-some [[kind payload] (get env form)]
                  (if (= :local kind)
                    [[] payload]
                    (let [dst (fresh-reg)]
                      [[{:gmir/op :gmir/argument :gmir/dst dst
                         :gmir/index payload}] dst]))
                  (reject! :kir-to-gmir :unknown-parameter {:form form}))

                (and (seq? form) (contains? kir-fold-ops (first form))
                     (or (> (count form) 3)
                         (and (= '- (first form)) (= 2 (count form)))))
                (let [op (first form)
                      operands (if (and (= '- op) (= 2 (count form)))
                                 (list 0 (second form))
                                 (rest form))
                      [[initial-code initial-value] & lowered]
                      (mapv #(value % env) operands)]
                  (reduce (fn [[code left] [right-code right]]
                            (let [right (scalar-register! right form)
                                  dst (fresh-reg)]
                              [(vec (concat code right-code
                                            [{:gmir/op (get kir-binary-ops op)
                                              :gmir/dst dst :gmir/left left
                                              :gmir/right right}]))
                               dst]))
                          [initial-code (scalar-register! initial-value form)]
                          lowered))

                (and (seq? form) (contains? kir-comparison-ops (first form))
                     (> (count form) 3))
                (let [op (get kir-binary-ops (first form))
                      lowered (mapv #(value % env) (rest form))
                      code (vec (mapcat first lowered))
                      registers (mapv #(scalar-register! (second %) form) lowered)
                      comparisons
                      (mapv (fn [[left right]]
                              (let [dst (fresh-reg)]
                                [{:gmir/op op :gmir/dst dst
                                  :gmir/left left :gmir/right right}
                                 dst]))
                            (partition 2 1 registers))
                      code (into code (map first comparisons))]
                  (reduce (fn [[code left] [_ right]]
                            (let [dst (fresh-reg)]
                              [(conj code {:gmir/op :gmir/bit-and :gmir/dst dst
                                           :gmir/left left :gmir/right right})
                               dst]))
                          [code (second (first comparisons))]
                          (rest comparisons)))

                (and (seq? form) (contains? kir-binary-ops (first form))
                     (= 3 (count form)))
                (let [[left-code left-value] (value (second form) env)
                      [right-code right-value] (value (nth form 2) env)
                      left (scalar-register! left-value form)
                      right (scalar-register! right-value form)
                      dst (fresh-reg)]
                  [(vec (concat left-code right-code
                                [{:gmir/op (get kir-binary-ops (first form))
                                  :gmir/dst dst
                                  :gmir/left left :gmir/right right}]))
                   dst])

                (and (seq? form) (contains? kir-predicate-ops (first form))
                     (= 2 (count form)))
                (let [[operand-code operand-value] (value (second form) env)
                      operand (scalar-register! operand-value form)
                      zero (fresh-reg)
                      dst (fresh-reg)]
                  [(vec (concat operand-code
                                [{:gmir/op :gmir/constant :gmir/dst zero
                                  :gmir/value 0}
                                 {:gmir/op (get kir-predicate-ops (first form))
                                  :gmir/dst dst :gmir/left operand
                                  :gmir/right zero}]))
                   dst])

                (and (seq? form) (contains? kir-word-unary-ops (first form))
                     (= 2 (count form)))
                (let [lowered (value (second form) env)]
                  (case (first form)
                    bool-not (binary-value :gmir/equal lowered
                                           (constant-value 0) form)
                    bit-not (binary-value :gmir/bit-xor lowered
                                          (constant-value -1) form)
                    i32-wrap (signed-i32-value lowered form)
                    u32-wrap (unsigned-i32-value lowered form)))

                (and (seq? form) (contains? kir-i32-binary-ops (first form))
                     (= 3 (count form)))
                (let [op (first form)
                      left (value (second form) env)
                      right (value (nth form 2) env)]
                  (case op
                    i32-wrapping-add
                    (signed-i32-value
                     (binary-value :gmir/add left right form) form)
                    i32-wrapping-mul
                    (signed-i32-value
                     (binary-value :gmir/multiply left right form) form)
                    i32-xor
                    (signed-i32-value
                     (binary-value :gmir/bit-xor left right form) form)
                    i32-shift-left
                    (signed-i32-value
                     (binary-value :gmir/shift-left left right form) form)
                    i32-shift-right
                    (binary-value :gmir/shift-right-signed
                                  (signed-i32-value left form) right form)
                    u32-shift-right
                    (binary-value :gmir/shift-right-unsigned
                                  (unsigned-i32-value left form) right form)))

                (and (seq? form) (contains? kir-f64-binary-ops (first form))
                     (= 3 (count form)))
                (binary-value (get kir-f64-binary-ops (first form))
                              (value (second form) env)
                              (value (nth form 2) env) form)

                (and (seq? form) (contains? kir-f64-unary-ops (first form))
                     (= 2 (count form)))
                (let [lowered (value (second form) env)]
                  (case (first form)
                    (f64-from-bits f64-to-bits) lowered
                    f64-abs (binary-value :gmir/bit-and lowered
                                          (constant-value #?(:clj Long/MAX_VALUE
                                                             :cljs i64/max-i64)) form)
                    f64-neg (binary-value :gmir/bit-xor lowered
                                          (constant-value #?(:clj Long/MIN_VALUE
                                                             :cljs i64/min-i64)) form)
                    f64-sqrt
                    (let [[code input] lowered, dst (fresh-reg)]
                      [(conj code {:gmir/op :gmir/f64-sqrt :gmir/dst dst
                                   :gmir/input (scalar-register! input form)})
                       dst])))

                (and (seq? form) (contains? kir-kernel-memory-ops (first form))
                     (contains? #{4 5} (count form)))
                (let [[op maximum] (get kir-kernel-memory-ops (first form))
                      lowered (mapv #(value % env) (rest form))
                      code (vec (mapcat first lowered))
                      operands (mapv #(scalar-register! (second %) form) lowered)
                      dst (fresh-reg)
                      [base length index stored] operands]
                  (when-not (= (if (contains? #{:gmir/kernel-store-u8
                                                :gmir/kernel-store-u32} op)
                                 4 3)
                               (count operands))
                    (reject! :kir-to-gmir :kernel-memory-arity {:form form}))
                  [(conj code
                         (cond-> {:gmir/op op :gmir/dst dst :gmir/base base
                                  :gmir/length length :gmir/index index
                                  :gmir/maximum maximum}
                           stored (assoc :gmir/stored stored)))
                   dst])

                (and (seq? form) (= 'kernel-subregion (first form))
                     (= 5 (count form)))
                (let [lowered (mapv #(value % env) (rest form))
                      [base length offset size]
                      (mapv #(scalar-register! (second %) form) lowered)
                      dst (fresh-reg)]
                  [(conj (vec (mapcat first lowered))
                         {:gmir/op :gmir/kernel-subregion :gmir/dst dst
                          :gmir/base base :gmir/length length
                          :gmir/offset offset :gmir/size size})
                   dst])

                (and (seq? form) (contains? kir-runtime-ops (first form)))
                (let [runtime (get kir-runtime-ops (first form))
                      arguments (vec (rest form))
                      expected (get gmir/runtime-operation-arities runtime)
                      lowered (mapv #(value % env) arguments)
                      registers (mapv #(scalar-register! (second %) form) lowered)
                      dst (fresh-reg)]
                  (when-not (= expected (count arguments))
                    (reject! :kir-to-gmir :runtime-call-arity
                             {:form form :runtime runtime :expected expected}))
                  [(conj (vec (mapcat first lowered))
                         {:gmir/op :gmir/runtime-call :gmir/dst dst
                          :gmir/runtime runtime :gmir/arguments registers})
                   dst])

                (and (seq? form) (= 'cap-call (first form)) (= 3 (count form)))
                (let [capability (second form)
                      [code input] (value (nth form 2) env)
                      dst (fresh-reg)]
                  (when-not (valid-capability-id? capability)
                    (reject! :kir-to-gmir :invalid-capability-id {:form form}))
                  [(conj code {:gmir/op :gmir/capability-call :gmir/dst dst
                               :gmir/capability capability :gmir/kind :i64
                               :gmir/arguments [(scalar-register! input form)]})
                   dst])

                (and (seq? form) (= 'typed-cap-call (first form))
                     (= 5 (count form)))
                (let [[_ capability request-type result-type request] form
                      kind (get typed-capability-kinds [request-type result-type])
                      [code input] (value request env)
                      dst (fresh-reg)]
                  (when-not (and (valid-capability-id? capability) kind)
                    (reject! :kir-to-gmir :invalid-typed-capability-call
                             {:form form :request-type request-type
                              :result-type result-type}))
                  [(conj code {:gmir/op :gmir/capability-call :gmir/dst dst
                               :gmir/capability capability :gmir/kind kind
                               :gmir/arguments [(scalar-register! input form)]})
                   dst])

                (and (seq? form) (= 'record-new (first form)) (<= 2 (count form)))
                (let [type (second form)
                      fields (or (scalar-record-fields type)
                                 (reject! :kir-to-gmir :unsupported-record-type
                                          {:form form :type type}))
                      field-forms (vec (drop 2 form))]
                  (when-not (= (count fields) (count field-forms))
                    (reject! :kir-to-gmir :record-field-count-mismatch {:form form}))
                  (let [lowered (mapv #(value % env) field-forms)]
                    [(vec (mapcat first lowered))
                     (record-value type
                                   (mapv #(scalar-register! (second %) form)
                                         lowered))]))

                (and (seq? form) (= 'record-get (first form)) (= 4 (count form)))
                (let [type (second form)
                      fields (or (scalar-record-fields type)
                                 (reject! :kir-to-gmir :unsupported-record-type
                                          {:form form :type type}))
                      [record-code aggregate] (value (nth form 2) env)
                      field (nth form 3)
                      field-index (first (keep-indexed
                                          (fn [index [name _]]
                                            (when (= name field) index))
                                          fields))]
                  (when-not (and (record-value? aggregate)
                                 (= type (:aggregate/type aggregate)))
                    (reject! :kir-to-gmir :record-type-mismatch
                             {:form form :expected type :actual aggregate}))
                  (when-not (some? field-index)
                    (reject! :kir-to-gmir :unknown-record-field
                             {:form form :field field}))
                  [record-code (nth (:aggregate/values aggregate) field-index)])

                (and (seq? form) (= 'variant-new (first form)) (= 4 (count form)))
                (let [type (second form)
                      cases (or (scalar-variant-cases type)
                                (reject! :kir-to-gmir :unsupported-variant-type
                                         {:form form :type type}))
                      tag (nth form 2)
                      ordinal (first (keep-indexed
                                      (fn [index [name _]]
                                        (when (= name tag) index))
                                      cases))]
                  (when-not (some? ordinal)
                    (reject! :kir-to-gmir :unknown-variant-case
                             {:form form :case tag}))
                  (let [tag-register (fresh-reg)
                        [payload-code payload-value] (value (nth form 3) env)
                        payload (scalar-register! payload-value form)]
                    [(into [{:gmir/op :gmir/constant :gmir/dst tag-register
                             :gmir/value ordinal}]
                           payload-code)
                     (variant-value type tag-register payload)]))

                (and (seq? form) (= 'variant-match (first form)) (= 4 (count form)))
                (let [type (second form)
                      cases (or (scalar-variant-cases type)
                                (reject! :kir-to-gmir :unsupported-variant-type
                                         {:form form :type type}))
                      branches (nth form 3)]
                  (when-not (and (vector? branches)
                                 (= (count cases) (count branches))
                                 (every? #(and (vector? %) (= 3 (count %))
                                               (keyword? (first %))
                                               (symbol? (second %)))
                                         branches)
                                 (= (mapv first cases) (mapv first branches)))
                    (reject! :kir-to-gmir :invalid-variant-branches
                             {:form form :cases cases :branches branches}))
                  (let [[variant-code aggregate] (value (nth form 2) env)]
                    (when-not (and (variant-value? aggregate)
                                   (= type (:aggregate/type aggregate)))
                      (reject! :kir-to-gmir :variant-type-mismatch
                               {:form form :expected type :actual aggregate}))
                    (let [tag-symbol (gensym "$variant-tag-")
                          payload-symbol (gensym "$variant-payload-")
                          match-env (assoc env
                                           tag-symbol [:local (:variant/tag aggregate)]
                                           payload-symbol [:local (:variant/payload aggregate)])
                          dispatch
                          (reduce (fn [fallback [ordinal [_ binder body]]]
                                    (list 'if (list '= tag-symbol ordinal)
                                          (list 'let [binder payload-symbol] body)
                                          fallback))
                                  (let [[_ binder body] (peek branches)]
                                    (list 'let [binder payload-symbol] body))
                                  (reverse (map-indexed vector (pop branches))))
                          [dispatch-code result] (value dispatch match-env)]
                      [(into variant-code dispatch-code) result])))

                (and (seq? form) (= 'if (first form)) (= 4 (count form)))
                (let [[test-code test-value] (value (second form) env)
                      test (scalar-register! test-value form)
                      then-label (fresh-label "value-if-then")
                      then-exit (fresh-label "value-if-then-exit")
                      else-label (fresh-label "value-if-else")
                      else-exit (fresh-label "value-if-else-exit")
                      join-label (fresh-label "value-if-join")
                      [then-code then-value] (value (nth form 2) env)
                      [else-code else-value] (value (nth form 3) env)
                      [phis merged] (merge-values then-value else-value
                                                  then-exit else-exit form)]
                  [(vec (concat test-code
                                [{:gmir/op :gmir/branch-zero
                                  :gmir/test test :gmir/target else-label}
                                 {:gmir/op :gmir/label :gmir/id then-label}]
                                then-code
                                [{:gmir/op :gmir/label :gmir/id then-exit}
                                 {:gmir/op :gmir/jump :gmir/target join-label}
                                 {:gmir/op :gmir/label :gmir/id else-label}]
                                else-code
                                [{:gmir/op :gmir/label :gmir/id else-exit}
                                 {:gmir/op :gmir/jump :gmir/target join-label}
                                 {:gmir/op :gmir/label :gmir/id join-label}]
                                phis))
                   merged])

                (and (seq? form) (= 'let (first form)) (= 3 (count form))
                     (vector? (second form)) (even? (count (second form))))
                (let [[code bound-env]
                      (reduce (fn [[code current-env] [binding expression]]
                                (when-not (symbol? binding)
                                  (reject! :kir-to-gmir :invalid-binding {:form form}))
                                (let [[expression-code register]
                                      (value expression current-env)]
                                  [(into code expression-code)
                                   (assoc current-env binding [:local register])]))
                              [[] env]
                              (partition 2 (second form)))
                      [body-code result] (value (nth form 2) bound-env)]
                  [(into code body-code) result])

                (and (seq? form) (= 'do (first form)) (next form))
                (let [lowered (mapv #(value % env) (rest form))]
                  [(vec (mapcat first lowered))
                   (second (peek lowered))])

                (and (seq? form) (contains? signatures (first form)))
                (let [callee (first form)
                      arguments (vec (rest form))
                      expected (get signatures callee)]
                  (when-not (= expected (count arguments))
                    (reject! :kir-to-gmir :call-arity-mismatch
                             {:form form :callee callee :expected expected}))
                  (let [lowered (mapv #(value % env) arguments)
                        registers (mapv #(scalar-register! (second %) form) lowered)
                        dst (fresh-reg)]
                    [(into (vec (mapcat first lowered))
                           [{:gmir/op :gmir/call :gmir/dst dst
                             :gmir/callee callee :gmir/arguments registers}])
                     dst]))

                (and (seq? form) (symbol? (first form)))
                (aggregate-abi/reject-unextracted-call! form)

                :else (reject! :kir-to-gmir :unsupported-value {:form form})))

            (tail [form env]
              (cond
                (and (seq? form) (= 'do (first form)) (next form))
                (let [expressions (vec (rest form))
                      prefix (pop expressions)
                      prefix-code (mapcat (fn [expression]
                                            (first (value expression env)))
                                          prefix)]
                  (into (vec prefix-code) (tail (peek expressions) env)))

                (and (seq? form) (= 'if (first form)) (= 4 (count form)))
                (let [[test-code test-value] (value (second form) env)
                      test (scalar-register! test-value form)
                      else-label (fresh-label "if-else")]
                  (vec (concat test-code
                               [{:gmir/op :gmir/branch-zero
                                 :gmir/test test :gmir/target else-label}]
                               (tail (nth form 2) env)
                               [{:gmir/op :gmir/label :gmir/id else-label}]
                               (tail (nth form 3) env))))

                (and (seq? form) (= 'let (first form)) (= 3 (count form))
                     (vector? (second form)) (even? (count (second form))))
                (let [[code bound-env]
                      (reduce (fn [[code current-env] [binding expression]]
                                (when-not (symbol? binding)
                                  (reject! :kir-to-gmir :invalid-binding {:form form}))
                                (let [[expression-code register]
                                      (value expression current-env)]
                                  [(into code expression-code)
                                   (assoc current-env binding [:local register])]))
                              [[] env]
                              (partition 2 (second form)))]
                  (into code (tail (nth form 2) bound-env)))

                :else
                (let [[code result-value] (value form env)
                      result (scalar-register! result-value form)]
                  (conj code {:gmir/op :gmir/return :gmir/value result}))))]
      (let [instructions (into parameter-code (tail body parameter-env))]
        {:gmir/version (cond
                         (some #(= :gmir/call (:gmir/op %)) instructions) 3
                         (some #(= :gmir/phi (:gmir/op %)) instructions) 2
                         :else 1)
         :gmir/instructions instructions})))))

(defn pilot-expression?
  "True only for the deliberately bounded production migration slice.

  Scalar arithmetic, comparisons, predicates, lexical `let`, ordered `do`,
  recursive `if`, fixed scalar-field record SROA, and non-escaping scalar
  variant SROA use the extracted IR path; allocation spills when necessary."
  [params body]
  (let [parameters (set params)]
    (letfn [(shape [form env]
              (cond
                (scalar-literal? form) :scalar
                (symbol? form) (get env form)

                (and (seq? form) (contains? kir-fold-ops (first form))
                     (or (> (count form) 3)
                         (and (= '- (first form)) (= 2 (count form))))
                     (every? #(= :scalar (shape % env)) (rest form)))
                :scalar

                (and (seq? form) (contains? kir-comparison-ops (first form))
                     (> (count form) 3)
                     (every? #(= :scalar (shape % env)) (rest form)))
                :scalar

                (and (seq? form) (contains? kir-binary-ops (first form))
                     (= 3 (count form))
                     (= :scalar (shape (second form) env))
                     (= :scalar (shape (nth form 2) env)))
                :scalar

                (and (seq? form) (contains? kir-predicate-ops (first form))
                     (= 2 (count form))
                     (= :scalar (shape (second form) env)))
                :scalar

                (and (seq? form) (contains? kir-word-unary-ops (first form))
                     (= 2 (count form))
                     (= :scalar (shape (second form) env)))
                :scalar

                (and (seq? form) (contains? kir-i32-binary-ops (first form))
                     (= 3 (count form))
                     (= :scalar (shape (second form) env))
                     (= :scalar (shape (nth form 2) env)))
                :scalar

                (and (seq? form) (contains? kir-f64-binary-ops (first form))
                     (= 3 (count form))
                     (= :scalar (shape (second form) env))
                     (= :scalar (shape (nth form 2) env)))
                :scalar

                (and (seq? form) (contains? kir-f64-unary-ops (first form))
                     (= 2 (count form))
                     (= :scalar (shape (second form) env)))
                :scalar

                (and (seq? form) (contains? kir-kernel-memory-ops (first form))
                     (contains? #{4 5} (count form))
                     (every? #(= :scalar (shape % env)) (rest form)))
                :scalar

                (and (seq? form) (= 'kernel-subregion (first form))
                     (= 5 (count form))
                     (every? #(= :scalar (shape % env)) (rest form)))
                :scalar

                (and (seq? form) (contains? kir-runtime-ops (first form))
                     (= (get gmir/runtime-operation-arities
                             (get kir-runtime-ops (first form)))
                        (count (rest form)))
                     (every? #(= :scalar (shape % env)) (rest form)))
                :scalar

                (and (seq? form) (= 'cap-call (first form)) (= 3 (count form))
                     (valid-capability-id? (second form))
                     (= :scalar (shape (nth form 2) env)))
                :scalar

                (and (seq? form) (= 'typed-cap-call (first form))
                     (= 5 (count form))
                     (valid-capability-id? (second form))
                     (contains? typed-capability-kinds
                                [(nth form 2) (nth form 3)])
                     (= :scalar (shape (nth form 4) env)))
                :scalar

                (and (seq? form) (= 'record-new (first form)) (<= 2 (count form)))
                (let [type (second form), fields (scalar-record-fields type)]
                  (when (and fields (= (count fields) (- (count form) 2))
                             (every? #(= :scalar (shape % env)) (drop 2 form)))
                    type))

                (and (seq? form) (= 'record-get (first form)) (= 4 (count form)))
                (let [type (second form), fields (scalar-record-fields type)]
                  (when (and fields (= type (shape (nth form 2) env))
                             (some #(= (nth form 3) (first %)) fields))
                    :scalar))

                (and (seq? form) (= 'variant-new (first form)) (= 4 (count form)))
                (let [type (second form), cases (scalar-variant-cases type)
                      tag (nth form 2)]
                  (when (and cases
                             (some #(= tag (first %)) cases)
                             (= :scalar (shape (nth form 3) env)))
                    type))

                (and (seq? form) (= 'variant-match (first form)) (= 4 (count form)))
                (let [type (second form), cases (scalar-variant-cases type)
                      branches (nth form 3)]
                  (when (and cases (= type (shape (nth form 2) env))
                             (vector? branches)
                             (= (count cases) (count branches))
                             (every? #(and (vector? %) (= 3 (count %))
                                           (keyword? (first %))
                                           (symbol? (second %)))
                                     branches)
                             (= (mapv first cases) (mapv first branches)))
                    (let [branch-shapes
                          (mapv (fn [[_ binder branch]]
                                  (shape branch (assoc env binder :scalar)))
                                branches)]
                      (when (and (every? some? branch-shapes)
                                 (apply = branch-shapes))
                        (first branch-shapes)))))

                (and (seq? form) (= 'if (first form)) (= 4 (count form))
                     (= :scalar (shape (second form) env)))
                (let [then-shape (shape (nth form 2) env)
                      else-shape (shape (nth form 3) env)]
                  (when (= then-shape else-shape) then-shape))

                (and (seq? form) (= 'let (first form)) (= 3 (count form))
                     (vector? (second form)) (even? (count (second form))))
                (loop [bindings (partition 2 (second form)), env env]
                  (if-let [[binding expression] (first bindings)]
                    (let [expression-shape (shape expression env)]
                      (when (and (symbol? binding) expression-shape)
                        (recur (next bindings) (assoc env binding expression-shape))))
                    (shape (nth form 2) env)))

                (and (seq? form) (= 'do (first form)) (next form))
                (let [shapes (mapv #(shape % env) (rest form))]
                  (when (every? some? shapes) (peek shapes)))

                :else nil))]
    (and *production-routing-enabled?*
         (vector? params) (<= (count params) 5)
         (= (count params) (count parameters))
         (every? symbol? params)
         (= :scalar (shape body (zipmap params (repeat :scalar))))))))

(defn lower-kir-module
  "Lower the first closed multi-function KIR slice to GMIR v3. The module has
  exactly one exported scalar entry; every function is scalar-only and direct
  calls resolve against the module signature table."
  [kir]
  (let [functions (:functions kir)
        exports (:exports kir)]
    (when-not (and (vector? functions) (seq functions)
                   (vector? exports) (= 1 (count exports))
                   (every? #(and (map? %)
                                 (gmir/function-id? (:name %))
                                 (vector? (:params %))
                                 (contains? #{nil :i64 :bool} (:result %)))
                           functions))
      (reject! :kir-to-gmir :unsupported-function-module kir))
    (let [signatures (into {} (map (juxt :name #(count (:params %))) functions))
          names (mapv :name functions)
          entry (first exports)]
      (when-not (and (= (count names) (count (distinct names)))
                     (contains? signatures entry))
        (reject! :kir-to-gmir :invalid-function-module
                 {:entry entry :functions names}))
      (gmir/validate!
       {:gmir/version 3
        :gmir/entry entry
        :gmir/functions
        (mapv (fn [{:keys [name params body]}]
                (let [lowered (lower-kir-expression params body signatures)]
                  {:gmir/name name
                   :gmir/arity (count params)
                   :gmir/instructions (:gmir/instructions lowered)}))
              functions)}))))

(defn pilot-module?
  "True when a checked KIR module can use the extracted scalar-call pipeline.
  At least one call is required so call-free programs retain their existing
  per-expression migration route."
  [kir]
  (and *production-routing-enabled?*
       (try
         (let [module (lower-kir-module kir)]
           (boolean
            (some #(some (fn [instruction]
                           (= :gmir/call (:gmir/op instruction)))
                         (:gmir/instructions %))
                  (:gmir/functions module))))
         (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) _ false))))

;; ── MC -> bytes ──────────────────────────────────────────────────────────────

(def ^:private x86-register-code
  {:x86-64/rax 0 :x86-64/rcx 1 :x86-64/rdx 2 :x86-64/r8 8
   :x86-64/r9 9 :x86-64/r10 10 :x86-64/r11 11
   :x86-64/rdi 7 :x86-64/rsi 6})
(def ^:private x86-arguments [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8])
(def ^:private aarch64-register-code
  {:aarch64/x0 0 :aarch64/x1 1 :aarch64/x2 2 :aarch64/x3 3
   :aarch64/x4 4 :aarch64/x7 7 :aarch64/x16 16 :aarch64/x17 17})

(defn- byte-value [n] (bit-and (unchecked-int n) 0xff))

(defn- le64 [n]
  #?(:clj (mapv #(byte-value (unsigned-bit-shift-right (long n) (* 8 %))) (range 8))
     :cljs (let [u (js/BigInt.asUintN 64 (i64/->bigint n))
                 base (js/BigInt 256)]
             (loop [i 0, remaining u, out []]
               (if (= i 8) out
                   (recur (inc i) (/ remaining base)
                          (conj out (js/Number (bit-and remaining (js/BigInt 255))))))))))

(defn- u32le [word]
  (mapv #(byte-value (unsigned-bit-shift-right word (* 8 %))) (range 4)))

(defn- align16 [n]
  (* 16 (quot (+ n 15) 16)))

(declare a64-register)

(defn- x86-stack-memory [opcode register slot]
  (let [code (get x86-register-code register)
        offset (* 8 slot)]
    (when-not (some? code)
      (reject! :mc-encode :unsupported-register {:register register}))
    (vec (concat [(bit-or 0x48 (if (>= code 8) 4 0))
                  opcode
                  (bit-or 0x84 (bit-shift-left (bit-and code 7) 3))
                  0x24]
                 (u32le offset)))))

(defn- x86-adjust-stack [opcode frame-bytes]
  (if (zero? frame-bytes)
    []
    (vec (concat [0x48 0x81 opcode] (u32le frame-bytes)))))

(defn- a64-adjust-stack [opcode frame-bytes]
  (loop [remaining frame-bytes, out []]
    (if (zero? remaining)
      out
      (let [chunk (min remaining 4080)]
        (recur (- remaining chunk)
               (into out (u32le (bit-or opcode
                                        (bit-shift-left chunk 10)))))))))

(defn- a64-stack-memory [opcode register slot]
  (u32le (bit-or opcode
                 (bit-shift-left slot 10)
                 (bit-shift-left 31 5)
                 (a64-register register))))

(defn- x86-rr [opcode dst src]
  (let [d (get x86-register-code dst)
        s (get x86-register-code src)]
    (when-not (and (some? d) (some? s))
      (reject! :mc-encode :unsupported-register {:dst dst :src src}))
    [(bit-or 0x48 (if (>= s 8) 4 0) (if (>= d 8) 1 0))
     opcode
     (bit-or 0xc0 (bit-shift-left (bit-and s 7) 3) (bit-and d 7))]))

(defn- x86-rr-two-byte [opcode dst src]
  (let [d (get x86-register-code dst)
        s (get x86-register-code src)]
    (when-not (and (some? d) (some? s))
      (reject! :mc-encode :unsupported-register {:dst dst :src src}))
    [(bit-or 0x48 (if (>= d 8) 4 0) (if (>= s 8) 1 0))
     0x0f opcode
     (bit-or 0xc0 (bit-shift-left (bit-and d 7) 3) (bit-and s 7))]))

(defn- x86-push [register]
  (let [code (get x86-register-code register)]
    (when-not (some? code)
      (reject! :mc-encode :unsupported-register {:register register}))
    (if (>= code 8) [0x41 (+ 0x50 (bit-and code 7))]
        [(+ 0x50 code)])))

(defn- x86-pop [register]
  (let [code (get x86-register-code register)]
    (when-not (some? code)
      (reject! :mc-encode :unsupported-register {:register register}))
    (if (>= code 8) [0x41 (+ 0x58 (bit-and code 7))]
        [(+ 0x58 code)])))

(defn- x86-quotient [dst left right]
  ;; `cqo`/`idiv` implicitly use RDX:RAX and need a non-RAX/RDX divisor. MIR
  ;; exposes only `dst` as written, so every other allocated value in RAX,
  ;; RDX, or RCX must survive. Save all three before loading operands; operands
  ;; already in an implicit register are read from those stable stack slots.
  (let [saved-slot {:x86-64/rcx 0 :x86-64/rdx 1 :x86-64/rax 2}
        load-operand (fn [dst src]
                       (if-some [slot (get saved-slot src)]
                         (x86-stack-memory 0x8b dst slot)
                         (if (= dst src) [] (x86-rr 0x89 dst src))))
        restore (case dst
                  :x86-64/rax
                  (concat (x86-pop :x86-64/rcx)
                          (x86-pop :x86-64/rdx)
                          (x86-adjust-stack 0xc4 8))
                  :x86-64/rcx
                  (concat (x86-rr 0x89 :x86-64/rcx :x86-64/rax)
                          (x86-adjust-stack 0xc4 8)
                          (x86-pop :x86-64/rdx)
                          (x86-pop :x86-64/rax))
                  :x86-64/rdx
                  (concat (x86-rr 0x89 :x86-64/rdx :x86-64/rax)
                          (x86-pop :x86-64/rcx)
                          (x86-adjust-stack 0xc4 8)
                          (x86-pop :x86-64/rax))
                  :x86-64/r8
                  (concat (x86-rr 0x89 :x86-64/r8 :x86-64/rax)
                          (x86-pop :x86-64/rcx)
                          (x86-pop :x86-64/rdx)
                          (x86-pop :x86-64/rax)))]
    (vec (concat (x86-push :x86-64/rax)
                 (x86-push :x86-64/rdx)
                 (x86-push :x86-64/rcx)
                 (load-operand :x86-64/rcx right)
                 (load-operand :x86-64/rax left)
                 [0x48 0x99 0x48 0xf7 0xf9]
                 restore))))

(defn- x86-shift [subop dst left right]
  ;; Variable-count shifts require CL. r11 is outside MIR's allocator profile,
  ;; and saving rcx makes the selected instruction preserve every non-dst
  ;; register exactly as its MIR dataflow promises.
  (vec (concat (x86-push :x86-64/rcx)
               (when-not (= :x86-64/r11 left)
                 (x86-rr 0x89 :x86-64/r11 left))
               (when-not (= :x86-64/rcx right)
                 (x86-rr 0x89 :x86-64/rcx right))
               [0x49 0xd3 (bit-or 0xc0 (bit-shift-left subop 3) 3)]
               (x86-pop :x86-64/rcx)
               (when-not (= dst :x86-64/r11)
                 (x86-rr 0x89 dst :x86-64/r11)))))

(defn- x86-gpr-to-xmm [xmm src]
  (let [s (get x86-register-code src)]
    (when-not (and (integer? xmm) (<= 0 xmm 15) (some? s))
      (reject! :mc-encode :unsupported-f64-register {:xmm xmm :src src}))
    [0x66 (bit-or 0x48 (if (>= xmm 8) 4 0) (if (>= s 8) 1 0))
     0x0f 0x6e
     (bit-or 0xc0 (bit-shift-left (bit-and xmm 7) 3) (bit-and s 7))]))

(defn- x86-xmm-to-gpr [dst xmm]
  (let [d (get x86-register-code dst)]
    (when-not (and (some? d) (integer? xmm) (<= 0 xmm 15))
      (reject! :mc-encode :unsupported-f64-register {:dst dst :xmm xmm}))
    [0x66 (bit-or 0x48 (if (>= xmm 8) 4 0) (if (>= d 8) 1 0))
     0x0f 0x7e
     (bit-or 0xc0 (bit-shift-left (bit-and xmm 7) 3) (bit-and d 7))]))

(defn- x86-setcc [condition dst]
  (let [d (get x86-register-code dst)]
    (when-not (some? d)
      (reject! :mc-encode :unsupported-register {:dst dst}))
    (vec (concat (when (>= d 4) [(bit-or 0x40 (if (>= d 8) 1 0))])
                 [0x0f condition (bit-or 0xc0 (bit-and d 7))]))))

(defn- x86-movzx-byte [dst]
  (let [d (get x86-register-code dst)]
    (when-not (some? d)
      (reject! :mc-encode :unsupported-register {:dst dst}))
    [(bit-or 0x48 (if (>= d 8) 5 0)) 0x0f 0xb6
     (bit-or 0xc0 (bit-shift-left (bit-and d 7) 3) (bit-and d 7))]))

(def ^:private x86-f64-binary-opcode
  {:x86-64/f64-add 0x58 :x86-64/f64-subtract 0x5c
   :x86-64/f64-multiply 0x59 :x86-64/f64-divide 0x5e
   :x86-64/f64-min 0x5d :x86-64/f64-max 0x5f})

(defn- x86-f64-binary [encoding dst left right]
  (vec (concat (x86-gpr-to-xmm 0 left)
               (x86-gpr-to-xmm 1 right)
               [0xf2 0x0f (get x86-f64-binary-opcode encoding) 0xc1]
               (x86-xmm-to-gpr dst 0))))

(defn- x86-f64-compare [encoding dst left right]
  (let [swapped? (contains? #{:x86-64/f64-less-than
                              :x86-64/f64-less-or-equal} encoding)
        condition (case encoding
                    :x86-64/f64-equal 0x94
                    :x86-64/f64-less-than 0x97
                    :x86-64/f64-less-or-equal 0x93
                    :x86-64/f64-greater-than 0x97
                    :x86-64/f64-greater-or-equal 0x93
                    :x86-64/f64-unordered 0x9a)]
    (vec (concat (x86-gpr-to-xmm 0 left)
                 (x86-gpr-to-xmm 1 right)
                 (if swapped? [0x66 0x0f 0x2e 0xc8]
                     [0x66 0x0f 0x2e 0xc1])
                 (x86-setcc condition dst)
                 (when (= :x86-64/f64-equal encoding)
                   (concat (x86-setcc 0x9b :x86-64/r11)
                           [(bit-or 0x40 4 (if (= :x86-64/r8 dst) 1 0))
                            0x20
                            (bit-or 0xc0 (bit-shift-left 3 3)
                                    (bit-and (get x86-register-code dst) 7))]))
                 (x86-movzx-byte dst)))))

(defn- x86-mov-imm [dst value]
  (let [d (get x86-register-code dst)]
    (when-not (some? d) (reject! :mc-encode :unsupported-register {:dst dst}))
    (into [(bit-or 0x48 (if (>= d 8) 1 0)) (+ 0xb8 (bit-and d 7))] (le64 value))))

(defn- x86-compare [condition dst left right]
  (let [d (get x86-register-code dst)]
    (when-not (some? d)
      (reject! :mc-encode :unsupported-register {:dst dst}))
    (vec (concat (x86-rr 0x39 left right)
                 (when (>= d 8) [0x41])
                 [0x0f condition (bit-or 0xc0 (bit-and d 7))
                  (bit-or 0x48 (if (>= d 8) 5 0)) 0x0f 0xb6
                  (bit-or 0xc0
                          (bit-shift-left (bit-and d 7) 3)
                          (bit-and d 7))]))))

(defn- a64-register [register]
  (or (get aarch64-register-code register)
      (reject! :mc-encode :unsupported-register {:register register})))

(defn- a64-mov [dst src]
  (u32le (bit-or 0xaa0003e0 (bit-shift-left (a64-register src) 16)
                   (a64-register dst))))

(defn- a64-constant [dst value]
  (let [rd (a64-register dst)
        chunks #?(:clj (mapv #(bit-and (unsigned-bit-shift-right (long value) %) 0xffff)
                              [0 16 32 48])
                  :cljs (let [u (js/BigInt.asUintN 64 (i64/->bigint value))
                              base (js/BigInt 65536)
                              mask (js/BigInt 65535)]
                          (loop [i 0, remaining u, out []]
                            (if (= i 4) out
                                (recur (inc i) (/ remaining base)
                                       (conj out (js/Number (bit-and remaining mask))))))))]
    (vec (mapcat (fn [chunk opcode]
                   (u32le (bit-or opcode (bit-shift-left chunk 5) rd)))
                 chunks
                 [0xd2800000 0xf2a00000 0xf2c00000 0xf2e00000]))))

(defn- a64-compare [cset dst left right]
  (vec (concat
        (u32le (bit-or 0xeb00001f
                       (bit-shift-left (a64-register right) 16)
                       (bit-shift-left (a64-register left) 5)))
        (u32le (bit-or cset (a64-register dst))))))

(defn- a64-f64-binary [base dst left right]
  (vec (concat
        (u32le (bit-or 0x9e670000
                       (bit-shift-left (a64-register left) 5)))
        (u32le (bit-or 0x9e670001
                       (bit-shift-left (a64-register right) 5)))
        (u32le base)
        (u32le (bit-or 0x9e660000 (a64-register dst))))))

(defn- a64-f64-compare [cset dst left right]
  (vec (concat
        (u32le (bit-or 0x9e670000
                       (bit-shift-left (a64-register left) 5)))
        (u32le (bit-or 0x9e670001
                       (bit-shift-left (a64-register right) 5)))
        (u32le 0x1e612000)
        (u32le (bit-or cset (a64-register dst))))))

(defn- x86-cmp-imm32 [register value]
  (let [code (get x86-register-code register)]
    (when-not (some? code)
      (reject! :mc-encode :unsupported-register {:register register}))
    (vec (concat [(bit-or 0x48 (if (>= code 8) 1 0)) 0x81
                  (bit-or 0xf8 (bit-and code 7))]
                 (u32le value)))))

(defn- x86-memory-access [kind register]
  (let [code (get x86-register-code register)]
    (when-not (some? code)
      (reject! :mc-encode :unsupported-register {:register register}))
    (let [rex (bit-or 0x40 (if (>= code 8) 4 0) 1)
          modrm (bit-or (bit-shift-left (bit-and code 7) 3) 3)]
      (case kind
        :load-u8 [rex 0x0f 0xb6 modrm]
        :load-u32 [(bit-or rex 0x40) 0x8b modrm]
        :store-u8 [rex 0x88 modrm]
        :store-u32 [rex 0x89 modrm]))))

(defn- memory-label [instruction-index suffix]
  (keyword "kotoba.native.kernel-memory"
           (str suffix "-" instruction-index)))

(defn- x86-kernel-memory
  [instruction-index width store? {:mir/keys [dst base length index stored maximum]}]
  (let [trap (memory-label instruction-index "trap")
        done (memory-label instruction-index "done")
        result (if store? stored dst)]
    (vec (concat
          (x86-cmp-imm32 length maximum)
          [(layout/relative-branch :x86-64/ja-rel32 trap)]
          (x86-rr 0x85 base base)
          [(layout/relative-branch :x86-64/jz-rel32 trap)]
          (x86-rr 0x39 index length)
          [(layout/relative-branch :x86-64/jae-rel32 trap)]
          (when (= 32 width)
            (concat (x86-rr 0x89 :x86-64/r10 length)
                    (x86-rr 0x29 :x86-64/r10 index)
                    (x86-cmp-imm32 :x86-64/r10 4)
                    [(layout/relative-branch :x86-64/jl-rel32 trap)]))
          (x86-rr 0x89 :x86-64/r11 base)
          (x86-rr 0x01 :x86-64/r11 index)
          (x86-memory-access (keyword (str (if store? "store" "load")
                                           "-u" width)) result)
          [(layout/relative-branch :x86-64/jmp-rel32 done)
           (layout/label trap)]
          [0x0f 0x0b]
          [(layout/label done)]))))

(defn- x86-kernel-subregion
  [instruction-index {:mir/keys [dst base length offset size]}]
  (let [trap (memory-label instruction-index "subregion-trap")
        done (memory-label instruction-index "subregion-done")]
    (vec (concat
          (x86-rr 0x85 base base)
          [(layout/relative-branch :x86-64/jz-rel32 trap)]
          (x86-rr 0x39 offset length)
          [(layout/relative-branch :x86-64/ja-rel32 trap)]
          (x86-rr 0x89 :x86-64/r10 length)
          (x86-rr 0x29 :x86-64/r10 offset)
          (x86-rr 0x39 size :x86-64/r10)
          [(layout/relative-branch :x86-64/ja-rel32 trap)]
          (when-not (= dst base) (x86-rr 0x89 dst base))
          (x86-rr 0x01 dst offset)
          [(layout/relative-branch :x86-64/jmp-rel32 done)
           (layout/label trap)]
          [0x0f 0x0b]
          [(layout/label done)]))))

(defn- a64-kernel-memory
  [instruction-index width store? {:mir/keys [dst base length index stored maximum]}]
  (let [trap (memory-label instruction-index "trap")
        done (memory-label instruction-index "done")
        result (if store? stored dst)
        address :aarch64/x16]
    (vec (concat
          (a64-constant :aarch64/x16 maximum)
          (u32le (bit-or 0xeb00001f (bit-shift-left 16 16)
                         (bit-shift-left (a64-register length) 5)))
          [(layout/relative-branch :aarch64/b-hi-imm19 trap)
           (layout/relative-branch :aarch64/cbz-imm19 trap
                                   [(a64-register base)])]
          (u32le (bit-or 0xeb00001f
                         (bit-shift-left (a64-register length) 16)
                         (bit-shift-left (a64-register index) 5)))
          [(layout/relative-branch :aarch64/b-hs-imm19 trap)]
          (when (= 32 width)
            (concat
             (u32le (bit-or 0xcb000000
                            (bit-shift-left (a64-register index) 16)
                            (bit-shift-left (a64-register length) 5) 16))
             (u32le (bit-or 0xf100001f (bit-shift-left 4 10)
                            (bit-shift-left 16 5)))
             [(layout/relative-branch :aarch64/b-lt-imm19 trap)]))
          (u32le (bit-or 0x8b000000
                         (bit-shift-left (a64-register index) 16)
                         (bit-shift-left (a64-register base) 5) 16))
          (u32le (case [store? width]
                   [false 8] (bit-or 0x39400000 (bit-shift-left 16 5)
                                     (a64-register result))
                   [false 32] (bit-or 0xb9400000 (bit-shift-left 16 5)
                                      (a64-register result))
                   [true 8] (bit-or 0x39000000 (bit-shift-left 16 5)
                                    (a64-register result))
                   [true 32] (bit-or 0xb9000000 (bit-shift-left 16 5)
                                     (a64-register result))))
          [(layout/relative-branch :aarch64/b-imm26 done)
           (layout/label trap)]
          (u32le 0xd4200000)
          [(layout/label done)]))))

(defn- a64-kernel-subregion
  [instruction-index {:mir/keys [dst base length offset size]}]
  (let [trap (memory-label instruction-index "subregion-trap")
        done (memory-label instruction-index "subregion-done")]
    (vec (concat
          [(layout/relative-branch :aarch64/cbz-imm19 trap
                                   [(a64-register base)])]
          (u32le (bit-or 0xeb00001f
                         (bit-shift-left (a64-register length) 16)
                         (bit-shift-left (a64-register offset) 5)))
          [(layout/relative-branch :aarch64/b-hi-imm19 trap)]
          (u32le (bit-or 0xcb000000
                         (bit-shift-left (a64-register offset) 16)
                         (bit-shift-left (a64-register length) 5) 16))
          (u32le (bit-or 0xeb00001f (bit-shift-left 16 16)
                         (bit-shift-left (a64-register size) 5)))
          [(layout/relative-branch :aarch64/b-hi-imm19 trap)]
          (u32le (bit-or 0x8b000000
                         (bit-shift-left (a64-register offset) 16)
                         (bit-shift-left (a64-register base) 5)
                         (a64-register dst)))
          [(layout/relative-branch :aarch64/b-imm26 done)
           (layout/label trap)]
          (u32le 0xd4200000)
          [(layout/label done)]))))

(defn- a64-quotient [dst left right]
  ;; AArch64 SDIV returns zero on division by zero and wraps MIN/-1; KIR traps
  ;; on both. x16 is an ABI scratch register outside MIR's allocated profile.
  ;; The fixed local branches are word-relative and stay inside this selected
  ;; instruction, so final label layout cannot invalidate them.
  (vec (concat
        ;; cbz right, trap (+15 instructions)
        (u32le (bit-or 0xb4000000 (bit-shift-left 15 5)
                       (a64-register right)))
        (a64-constant :aarch64/x16 #?(:clj Long/MIN_VALUE :cljs i64/min-i64))
        ;; cmp left,x16; b.ne divide (+7 instructions)
        (u32le (bit-or 0xeb00001f (bit-shift-left 16 16)
                       (bit-shift-left (a64-register left) 5)))
        (u32le (bit-or 0x54000001 (bit-shift-left 7 5)))
        (a64-constant :aarch64/x16 -1)
        ;; cmp right,x16; b.eq trap (+3 instructions)
        (u32le (bit-or 0xeb00001f (bit-shift-left 16 16)
                       (bit-shift-left (a64-register right) 5)))
        (u32le (bit-or 0x54000000 (bit-shift-left 3 5)))
        ;; divide; b done (+2 instructions); trap
        (u32le (bit-or 0x9ac00c00
                       (bit-shift-left (a64-register right) 16)
                       (bit-shift-left (a64-register left) 5)
                       (a64-register dst)))
        (u32le (bit-or 0x14000000 2))
        (u32le 0xd4200000))))

(defn- x86-runtime-call
  [frame-bytes {:mir/keys [context-offset] :as instruction}]
  (when (or (< frame-bytes 8) (not (zero? (mod context-offset 8))))
    (reject! :mc-encode :invalid-runtime-call-frame instruction))
  (let [context-slot (quot (- frame-bytes 8) 8)
        indirect-call (if (<= context-offset 127)
                        [0x41 0xff 0x51 context-offset]
                        (vec (concat [0x41 0xff 0x91]
                                     (u32le context-offset))))]
    (vec (concat
          (x86-stack-memory 0x89 :x86-64/r9 context-slot)
          (x86-rr 0x89 :x86-64/rdi :x86-64/r9)
          indirect-call
          (x86-stack-memory 0x8b :x86-64/r9 context-slot)))))

(defn- a64-runtime-call
  [{:mir/keys [context-offset] :as instruction}]
  (when (or (neg? context-offset) (not (zero? (mod context-offset 8)))
            (> (quot context-offset 8) 4095))
    (reject! :mc-encode :invalid-runtime-context-offset instruction))
  (vec (concat
        (a64-adjust-stack 0xd10003ff 16)
        (a64-stack-memory 0xf9000000 :aarch64/x7 0)
        (a64-mov :aarch64/x0 :aarch64/x7)
        (u32le (bit-or 0xf9400000
                       (bit-shift-left (quot context-offset 8) 10)
                       (bit-shift-left 7 5) 16))
        (u32le 0xd63f0200)
        (a64-stack-memory 0xf9400000 :aarch64/x7 0)
        (a64-adjust-stack 0x910003ff 16))))

(defn- x86-capability-call
  [frame-bytes {:mir/keys [capability kind context-offset] :as instruction}]
  (when (< frame-bytes 8)
    (reject! :mc-encode :invalid-capability-call-frame instruction))
  (let [context-slot (quot (- frame-bytes 8) 8)
        byte-offset (+ 16 (quot capability 8))
        mask (bit-shift-left 1 (mod capability 8))
        kind-code (get gmir/capability-kinds kind)
        typed? (pos? kind-code)
        indirect-call (if (<= context-offset 127)
                        [0x41 0xff 0x51 context-offset]
                        (vec (concat [0x41 0xff 0x91]
                                     (u32le context-offset))))]
    (vec (concat
          [0x41 0xf6 0x41 byte-offset mask 0x75 0x02 0x0f 0x0b]
          (x86-stack-memory 0x89 :x86-64/r9 context-slot)
          [0xbe] (u32le capability)
          (when typed?
            (concat [0xba] (u32le kind-code)
                    [0xb9] (u32le kind-code)))
          (x86-rr 0x89 :x86-64/rdi :x86-64/r9)
          indirect-call
          (x86-stack-memory 0x8b :x86-64/r9 context-slot)))))

(defn- a64-capability-call
  [{:mir/keys [capability kind context-offset] :as instruction}]
  (let [word-offset (+ 16 (* 8 (quot capability 64)))
        bit-index (mod capability 64)
        kind-code (get gmir/capability-kinds kind)
        typed? (pos? kind-code)]
    (when-not (and (some? kind-code) (<= 0 capability 255))
      (reject! :mc-encode :invalid-capability-call instruction))
    (vec (concat
          (u32le (bit-or 0xf9400000
                         (bit-shift-left (quot word-offset 8) 10)
                         (bit-shift-left 7 5) 16))
          (u32le (bit-or 0x37000000
                         (bit-shift-left (bit-and bit-index 0x20) 26)
                         (bit-shift-left (bit-and bit-index 0x1f) 19)
                         (bit-shift-left 2 5) 16))
          (u32le 0xd4200000)
          (a64-adjust-stack 0xd10003ff 16)
          (a64-stack-memory 0xf9000000 :aarch64/x7 0)
          (a64-constant :aarch64/x1 capability)
          (when typed?
            (concat (a64-constant :aarch64/x2 kind-code)
                    (a64-constant :aarch64/x3 kind-code)))
          (a64-mov :aarch64/x0 :aarch64/x7)
          (u32le (bit-or 0xf9400000
                         (bit-shift-left (quot context-offset 8) 10)
                         (bit-shift-left 7 5) 16))
          (u32le 0xd63f0200)
          (a64-stack-memory 0xf9400000 :aarch64/x7 0)
          (a64-adjust-stack 0x910003ff 16)))))

(defn- encode-selected
  [isa frame-bytes return-suffix instruction-index
   {:mc/keys [encoding] :as instruction}]
  (case encoding
    :x86-64/argument
    (let [dst (:mir/dst instruction)
          src (get x86-arguments (:mir/index instruction))]
      (when-not src (reject! :mc-encode :argument-index-unsupported instruction))
      (if (= dst src) [] (x86-rr 0x89 dst src)))
    :x86-64/constant (x86-mov-imm (:mir/dst instruction) (:mir/value instruction))
    :x86-64/add
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr 0x01 dst right))))
    :x86-64/subtract
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr 0x29 dst right))))
    :x86-64/multiply
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr-two-byte 0xaf dst right))))
    :x86-64/quotient
    (x86-quotient (:mir/dst instruction) (:mir/left instruction)
                  (:mir/right instruction))
    :x86-64/bit-and
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr 0x21 dst right))))
    :x86-64/bit-or
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr 0x09 dst right))))
    :x86-64/bit-xor
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                   (x86-rr 0x31 dst right))))
    :x86-64/shift-left
    (x86-shift 4 (:mir/dst instruction) (:mir/left instruction)
               (:mir/right instruction))
    :x86-64/shift-right-signed
    (x86-shift 7 (:mir/dst instruction) (:mir/left instruction)
               (:mir/right instruction))
    :x86-64/shift-right-unsigned
    (x86-shift 5 (:mir/dst instruction) (:mir/left instruction)
               (:mir/right instruction))
    (:x86-64/f64-add :x86-64/f64-subtract :x86-64/f64-multiply
     :x86-64/f64-divide :x86-64/f64-min :x86-64/f64-max)
    (x86-f64-binary encoding (:mir/dst instruction) (:mir/left instruction)
                    (:mir/right instruction))
    :x86-64/f64-sqrt
    (vec (concat (x86-gpr-to-xmm 0 (:mir/input instruction))
                 [0xf2 0x0f 0x51 0xc0]
                 (x86-xmm-to-gpr (:mir/dst instruction) 0)))
    (:x86-64/f64-equal :x86-64/f64-less-than
     :x86-64/f64-less-or-equal :x86-64/f64-greater-than
     :x86-64/f64-greater-or-equal :x86-64/f64-unordered)
    (x86-f64-compare encoding (:mir/dst instruction) (:mir/left instruction)
                     (:mir/right instruction))
    :x86-64/kernel-load-u8 (x86-kernel-memory instruction-index 8 false instruction)
    :x86-64/kernel-store-u8 (x86-kernel-memory instruction-index 8 true instruction)
    :x86-64/kernel-load-u32 (x86-kernel-memory instruction-index 32 false instruction)
    :x86-64/kernel-store-u32 (x86-kernel-memory instruction-index 32 true instruction)
    :x86-64/kernel-subregion (x86-kernel-subregion instruction-index instruction)
    (:x86-64/equal :x86-64/less-than :x86-64/greater-than
     :x86-64/less-or-equal :x86-64/greater-or-equal)
    (x86-compare (case encoding
                   :x86-64/equal 0x94
                   :x86-64/less-than 0x9c
                   :x86-64/greater-than 0x9f
                   :x86-64/less-or-equal 0x9e
                   :x86-64/greater-or-equal 0x9d)
                 (:mir/dst instruction) (:mir/left instruction)
                 (:mir/right instruction))
    :x86-64/spill-load
    (x86-stack-memory 0x8b (:mir/dst instruction) (:mir/slot instruction))
    :x86-64/spill-store
    (x86-stack-memory 0x89 (:mir/src instruction) (:mir/slot instruction))
    :x86-64/move
    (if (= (:mir/dst instruction) (:mir/src instruction))
      []
      (x86-rr 0x89 (:mir/dst instruction) (:mir/src instruction)))
    :x86-64/runtime-call (x86-runtime-call frame-bytes instruction)
    :x86-64/capability-call (x86-capability-call frame-bytes instruction)
    :x86-64/return
    (vec (concat (when-not (= :x86-64/rax (:mir/value instruction))
                   (x86-rr 0x89 :x86-64/rax (:mir/value instruction)))
                 return-suffix))

    :aarch64/argument
    (let [dst (:mir/dst instruction)
          index (:mir/index instruction)
          src (keyword "aarch64" (str "x" index))]
      (when-not (<= 0 index 4) (reject! :mc-encode :argument-index-unsupported instruction))
      (if (= dst src) [] (a64-mov dst src)))
    :aarch64/constant (a64-constant (:mir/dst instruction) (:mir/value instruction))
    :aarch64/add
    (u32le (bit-or 0x8b000000
                   (bit-shift-left (a64-register (:mir/right instruction)) 16)
                   (bit-shift-left (a64-register (:mir/left instruction)) 5)
                   (a64-register (:mir/dst instruction))))
    (:aarch64/subtract :aarch64/multiply
     :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor
     :aarch64/shift-left :aarch64/shift-right-signed
     :aarch64/shift-right-unsigned)
    (let [base (case encoding
                 :aarch64/subtract 0xcb000000
                 :aarch64/multiply 0x9b007c00
                 :aarch64/bit-and 0x8a000000
                 :aarch64/bit-or 0xaa000000
                 :aarch64/bit-xor 0xca000000
                 :aarch64/shift-left 0x9ac02000
                 :aarch64/shift-right-signed 0x9ac02800
                 :aarch64/shift-right-unsigned 0x9ac02400)]
      (u32le (bit-or base
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
    :aarch64/quotient
    (a64-quotient (:mir/dst instruction) (:mir/left instruction)
                  (:mir/right instruction))
    (:aarch64/f64-add :aarch64/f64-subtract :aarch64/f64-multiply
     :aarch64/f64-divide :aarch64/f64-min :aarch64/f64-max)
    (a64-f64-binary (case encoding
                      :aarch64/f64-add 0x1e612800
                      :aarch64/f64-subtract 0x1e613800
                      :aarch64/f64-multiply 0x1e610800
                      :aarch64/f64-divide 0x1e611800
                      :aarch64/f64-min 0x1e615800
                      :aarch64/f64-max 0x1e614800)
                    (:mir/dst instruction) (:mir/left instruction)
                    (:mir/right instruction))
    :aarch64/f64-sqrt
    (vec (concat
          (u32le (bit-or 0x9e670000
                         (bit-shift-left (a64-register (:mir/input instruction)) 5)))
          (u32le 0x1e61c000)
          (u32le (bit-or 0x9e660000 (a64-register (:mir/dst instruction))))))
    (:aarch64/f64-equal :aarch64/f64-less-than
     :aarch64/f64-less-or-equal :aarch64/f64-greater-than
     :aarch64/f64-greater-or-equal :aarch64/f64-unordered)
    (a64-f64-compare (case encoding
                       :aarch64/f64-equal 0x9a9f17e0
                       :aarch64/f64-less-than 0x9a9f57e0
                       :aarch64/f64-less-or-equal 0x9a9f87e0
                       :aarch64/f64-greater-than 0x9a9fd7e0
                       :aarch64/f64-greater-or-equal 0x9a9fb7e0
                       :aarch64/f64-unordered 0x9a9f77e0)
                     (:mir/dst instruction) (:mir/left instruction)
                     (:mir/right instruction))
    :aarch64/kernel-load-u8 (a64-kernel-memory instruction-index 8 false instruction)
    :aarch64/kernel-store-u8 (a64-kernel-memory instruction-index 8 true instruction)
    :aarch64/kernel-load-u32 (a64-kernel-memory instruction-index 32 false instruction)
    :aarch64/kernel-store-u32 (a64-kernel-memory instruction-index 32 true instruction)
    :aarch64/kernel-subregion (a64-kernel-subregion instruction-index instruction)
    (:aarch64/equal :aarch64/less-than :aarch64/greater-than
     :aarch64/less-or-equal :aarch64/greater-or-equal)
    (a64-compare (case encoding
                   :aarch64/equal 0x9a9f17e0
                   :aarch64/less-than 0x9a9fa7e0
                   :aarch64/greater-than 0x9a9fd7e0
                   :aarch64/less-or-equal 0x9a9fc7e0
                   :aarch64/greater-or-equal 0x9a9fb7e0)
                 (:mir/dst instruction) (:mir/left instruction)
                 (:mir/right instruction))
    :aarch64/spill-load
    (a64-stack-memory 0xf9400000 (:mir/dst instruction) (:mir/slot instruction))
    :aarch64/spill-store
    (a64-stack-memory 0xf9000000 (:mir/src instruction) (:mir/slot instruction))
    :aarch64/move
    (if (= (:mir/dst instruction) (:mir/src instruction))
      []
      (a64-mov (:mir/dst instruction) (:mir/src instruction)))
    :aarch64/runtime-call (a64-runtime-call instruction)
    :aarch64/capability-call (a64-capability-call instruction)
    :aarch64/return
    (vec (concat (when-not (= :aarch64/x0 (:mir/value instruction))
                   (a64-mov :aarch64/x0 (:mir/value instruction)))
                 return-suffix))
    (reject! :mc-encode :unknown-encoding (assoc instruction :isa isa))))

(defn- relative32 [opcode displacement]
  (into [opcode] (mapv byte-value
                       [displacement
                        (unsigned-bit-shift-right displacement 8)
                        (unsigned-bit-shift-right displacement 16)
                        (unsigned-bit-shift-right displacement 24)])))

(defn- encode-layout-branch [{:mir/keys [encoding operands]} displacement]
  (case encoding
    :x86-64/jz-rel32 (into [0x0f 0x84] (subvec (relative32 0 displacement) 1))
    :x86-64/jl-rel32 (into [0x0f 0x8c] (subvec (relative32 0 displacement) 1))
    :x86-64/ja-rel32 (into [0x0f 0x87] (subvec (relative32 0 displacement) 1))
    :x86-64/jae-rel32 (into [0x0f 0x83] (subvec (relative32 0 displacement) 1))
    :x86-64/jmp-rel32 (relative32 0xe9 displacement)
    :x86-64/call-rel32 (relative32 0xe8 displacement)
    :x86-64/jne-rel8 [0x75 (byte-value displacement)]
    :aarch64/cbz-imm19
    (u32le (bit-or 0xb4000000
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)
                   (first operands)))
    :aarch64/b-hi-imm19
    (u32le (bit-or 0x54000008
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))
    :aarch64/b-hs-imm19
    (u32le (bit-or 0x54000002
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))
    :aarch64/b-lt-imm19
    (u32le (bit-or 0x5400000b
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))
    :aarch64/b-imm26
    (u32le (bit-or 0x14000000 (bit-and (quot displacement 4) 0x03ffffff)))
    :aarch64/bl-imm26
    (u32le (bit-or 0x94000000 (bit-and (quot displacement 4) 0x03ffffff)))
    :aarch64/cbnz-x16-imm19
    (u32le (bit-or 0xb5000010
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))))

(defn- size-of-token [token]
  (or (layout/token-size token)
      (when (and (integer? token) (<= 0 token 255)) 1)))

(defn- resolve-layout [tokens]
  (let [labels (layout/label-offsets tokens size-of-token)]
    (layout/resolve-tokens tokens size-of-token labels encode-layout-branch
                           (fn [token _] [token]))))

(defn- instruction-tokens
  [isa frame-bytes return-suffix callee-labels instructions]
  (vec
   (mapcat
    (fn [instruction-index {:mc/keys [op test] :as instruction}]
      (if (layout/label-token? instruction)
        [instruction]
        (case op
          :mc/instruction
          (if (= "call" (name (:mc/encoding instruction)))
            (let [callee (:mir/callee instruction)
                  label (get callee-labels callee)]
              (when-not label
                (reject! :mc-encode :unknown-call-target instruction))
              [(layout/relative-branch
                (if (= :x86-64 isa)
                  :x86-64/call-rel32 :aarch64/bl-imm26)
                label)])
            (encode-selected isa frame-bytes return-suffix instruction-index instruction))
          :mc/branch-zero
          (if (= :x86-64 isa)
            (concat (x86-rr 0x85 test test)
                    [(layout/relative-branch :x86-64/jz-rel32
                                             (:mc/target instruction))])
            [(layout/relative-branch :aarch64/cbz-imm19
                                     (:mc/target instruction)
                                     [(a64-register test)])])
          :mc/jump
          [(layout/relative-branch
            (if (= :x86-64 isa) :x86-64/jmp-rel32 :aarch64/b-imm26)
            (:mc/target instruction))]
          (reject! :mc-encode :unknown-operation instruction))))
    (range) instructions)))

(defn- qualify-function-locals [function-index tokens]
  (let [labels (->> tokens (filter layout/label-token?) (map :mir/id) set)
        renamed (into {} (map (fn [id]
                                [id (keyword (str "kotoba.native.local." function-index)
                                             (str (namespace id) "." (name id)))])
                              labels))]
    (mapv (fn [token]
            (cond
              (layout/label-token? token) (assoc token :mir/id (get renamed (:mir/id token)))
              (and (layout/relative-branch-token? token)
                   (contains? renamed (:mir/target token)))
              (assoc token :mir/target (get renamed (:mir/target token)))
              :else token))
          tokens)))

(defn- call-frame-policy? [frame-policy]
  (contains? #{:all-vregs :call-live} frame-policy))

(defn- function-frame [target frame-slots frame-policy]
  (let [storage-bytes (align16 (* 8 frame-slots))]
    (case target
      :x86-64
      (let [frame-bytes (+ storage-bytes (if (call-frame-policy? frame-policy) 8 0))]
        {:frame-bytes frame-bytes
         :prologue (x86-adjust-stack 0xec frame-bytes)
         :return-suffix (vec (concat (x86-adjust-stack 0xc4 frame-bytes) [0xc3]))})

      :aarch64
      (if (call-frame-policy? frame-policy)
        {:frame-bytes storage-bytes
         :prologue (vec (concat (u32le 0xa9bf7bfd) (u32le 0x910003fd)
                                (a64-adjust-stack 0xd10003ff storage-bytes)))
         :return-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                     (u32le 0xa8c17bfd) (u32le 0xd65f03c0)))}
        {:frame-bytes storage-bytes
         :prologue (a64-adjust-stack 0xd10003ff storage-bytes)
         :return-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                     (u32le 0xd65f03c0)))}))))

(defn encode-mc-module
  "Encode an allocated MC v3 module. PREFIXES is an optional function-name to
  target-token map used by production fuel instrumentation; it participates in
  the same final layout as frames, branches, and calls."
  ([program] (encode-mc-module program {}))
  ([{:mc/keys [target entry functions] :as program} prefixes]
   (mc/validate! program)
   (when-not (= 3 (:mc/version program))
     (reject! :mc-encode :module-version-required program))
   (let [callee-labels (into {}
                             (map-indexed
                              (fn [index {:mc/keys [name]}]
                                [name (keyword "kotoba.native.function" (str index))])
                              functions))
         tokens
         (vec
          (mapcat
           (fn [index {:mc/keys [name frame-slots frame-policy instructions]}]
             (let [{:keys [frame-bytes prologue return-suffix]}
                   (function-frame target frame-slots frame-policy)
                   local (vec (concat (get prefixes name []) prologue
                                      (instruction-tokens target frame-bytes return-suffix
                                                          callee-labels instructions)))]
               (into [(layout/label (get callee-labels name))]
                     (qualify-function-locals index local))))
           (range) functions))
         labels (layout/label-offsets tokens size-of-token)
         code (layout/resolve-tokens tokens size-of-token labels encode-layout-branch
                                     (fn [token _] [token]))
         function-offsets (mapv #(get labels (get callee-labels (:mc/name %))) functions)
         entry-index (first (keep-indexed (fn [index function]
                                           (when (= entry (:mc/name function)) index))
                                         functions))
         entry-offset (nth function-offsets entry-index)
         entry-end (if (< (inc entry-index) (count function-offsets))
                     (nth function-offsets (inc entry-index))
                     (count code))
         entry-arity (:mc/arity (nth functions entry-index))]
     {:code code
      :exports {entry {:offset entry-offset
                       :length (- entry-end entry-offset)
                       :arity entry-arity}}})))

(defn encode-mc
  "Encode a closed allocated MC v2 program into final machine bytes."
  [{:mc/keys [target frame-slots instructions] :as program}]
  (mc/validate! program)
  (when-not (= 2 (:mc/version program))
    (reject! :mc-encode :flat-program-version-required program))
  (let [host-call? (some #(contains? #{"runtime-call" "capability-call"}
                                     (some-> (:mc/encoding %) name))
                         instructions)
        {:keys [frame-bytes prologue return-suffix]}
        (function-frame target frame-slots
                        (if host-call? :call-live :allocator))]
    (resolve-layout
     (vec (concat prologue
                  (instruction-tokens target frame-bytes return-suffix {}
                                      instructions))))))

(defn compile-kir-module
  "End-to-end scalar direct-call slice: checked KIR module through GMIR v3,
  MIR v3 allocation, MC v3 and final function/call layout."
  ([target kir] (compile-kir-module target kir {}))
  ([target kir prefixes]
   (aggregate-abi/admit-extracted-call!
    target #{:per-function-frame :spill-live-values-across-call
             :parallel-argument-assignment :single-word-return-register})
   (->> (lower-kir-module kir)
        (compile-gmir target)
        (#(encode-mc-module % prefixes)))))

(defn compile-expression
  "End-to-end closed slice: KIR expression -> GMIR -> MIR -> RA -> MC -> bytes."
  [target params body]
  (->> (lower-kir-expression params body)
       (compile-gmir target)
       encode-mc))
