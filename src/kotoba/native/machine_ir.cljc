(ns kotoba.native.machine-ir
  "Closed production contract for GMIR -> target MIR -> allocated MC data.

  Production native emission crosses this namespace exclusively. Admitted KIR
  lowers through closed GMIR/MIR/MC data; unknown operations, unsupported value
  shapes, use-before-definition, register exhaustion, and malformed labels fail
  closed before either ISA encoder."
  (:require [clojure.walk :as walk]
            [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]
            [kotoba.codegen.mc :as mc]
            [kotoba.codegen.layout :as layout]
            [kotoba.native.aggregate-abi :as aggregate-abi]
            [kotoba.native.string-index :as string-index]
            [kotoba.native.string-search :as string-search]
            #?(:cljs [kotoba.kir.cljs-i64 :as i64])))

(defn- reject! [phase problem instruction]
  (throw (ex-info (str "machine IR rejected: " (name problem))
                  {:phase phase :problem problem :instruction instruction})))

(defn- a64-op [instruction]
  (or (:mc/encoding instruction) (:mir/op instruction)))

(defn- a64-fused-multiply [multiply consumer]
  (let [product (:mir/dst multiply)
        consumer-op (a64-op consumer)
        addend (cond
                 (and (contains? #{:mir/add :aarch64/add} consumer-op)
                      (= product (:mir/left consumer))) (:mir/right consumer)
                 (and (contains? #{:mir/add :aarch64/add} consumer-op)
                      (= product (:mir/right consumer))) (:mir/left consumer)
                 (and (contains? #{:mir/subtract :aarch64/subtract} consumer-op)
                      (= product (:mir/right consumer))) (:mir/left consumer))]
    (when (and addend (not= product addend))
      (let [subtract? (contains? #{:mir/subtract :aarch64/subtract} consumer-op)
            fused {:mir/dst (:mir/dst consumer)
                   :mir/left (:mir/left multiply)
                   :mir/right (:mir/right multiply)
                   :mir/addend addend}]
        (if (:mc/encoding multiply)
          (assoc fused :mc/op :mc/instruction
                 :mc/encoding (if subtract?
                                :aarch64/multiply-subtract
                                :aarch64/multiply-add))
          (assoc fused :mir/op (if subtract?
                                 :mir/multiply-subtract
                                 :mir/multiply-add)))))))

(declare a64-source-registers-mir)

(defn- a64-product-use-count
  "Uses of `product` after `after`, stopping when a later dst kills it.

  Physical registers are reused. Counting to the end of the function
  treats a later live-range as a use of this product and would refuse
  a unique-use MADD (the `(+ (* n 7) 1)` then `(- v (* n 3))` shape)."
  [instructions after product]
  (loop [remaining (seq (subvec (vec instructions) after))
         uses 0]
    (if-not remaining
      uses
      (let [instruction (first remaining)
            used? (boolean (some #{product} (a64-source-registers-mir instruction)))
            killed? (= product (:mir/dst instruction))]
        (cond
          (and used? killed?) (inc uses)
          killed? uses
          used? (recur (next remaining) (inc uses))
          :else (recur (next remaining) uses))))))

(defn- a64-fuse-multiplies [instructions]
  (loop [index 0, out []]
    (if (>= index (count instructions))
      (vec out)
      (let [multiply (get instructions index)]
        (if (contains? #{:mir/multiply :aarch64/multiply} (a64-op multiply))
          (let [after (inc index)
                consumer-index
                (loop [candidate after]
                  (if (contains? #{:mir/constant :aarch64/constant}
                                 (a64-op (get instructions candidate)))
                    (recur (inc candidate))
                    candidate))
                between (subvec instructions after consumer-index)
                protected (set [(:mir/dst multiply) (:mir/left multiply)
                                (:mir/right multiply)])
                unclobbered? (not-any? #(contains? protected (:mir/dst %)) between)
                product (:mir/dst multiply)
                unique-use? (= 1 (a64-product-use-count instructions after product))
                fused (when (and unclobbered? unique-use?)
                        (a64-fused-multiply multiply
                                            (get instructions consumer-index)))]
            (if fused
              (recur (inc consumer-index) (into out (concat between [fused])))
              (recur (inc index) (conj out multiply))))
          (recur (inc index) (conj out multiply)))))))

(def ^:private a64-direct-result-ops
  ;; These instructions read every source before writing dst and accept any
  ;; allocated GPR as that destination. Keep the set closed: calls, checked
  ;; memory, and private-scratch encoders need their own aliasing proof.
  #{:mir/constant :mir/add :mir/subtract :mir/multiply
    :mir/multiply-add :mir/multiply-subtract :mir/quotient-constant
    :mir/bit-and :mir/bit-or :mir/bit-xor
    :mir/shift-left :mir/shift-right-signed :mir/shift-right-unsigned
    :mir/equal :mir/less-than :mir/greater-than
    :mir/less-or-equal :mir/greater-or-equal})

(defn- a64-source-registers-mir [instruction]
  (mapcat (fn [key]
            (let [value (get instruction key)]
              (cond (vector? value) value
                    (keyword? value) [value]
                    :else [])))
          [:mc/test :mir/test :mir/value :mir/src :mir/input :mir/left :mir/right
           :mir/addend :mir/base :mir/length :mir/index :mir/stored
           :mir/offset :mir/size :mir/arguments]))

(defn- a64-used-before-definition?
  [instructions register]
  (loop [remaining instructions]
    (when-let [instruction (first remaining)]
      (cond
        (some #{register} (a64-source-registers-mir instruction)) true
        (= register (:mir/dst instruction)) false
        :else (recur (next remaining))))))

(defn- a64-coalesce-direct-results [instructions]
  ;; Phi elimination leaves a producer, an optional edge label, a move into
  ;; the phi register, and an unconditional jump. AArch64's three-operand
  ;; forms can write the phi register directly. The target-block liveness
  ;; check is essential: the physical source register may name another live
  ;; allocation after the join even though the edge move is adjacent.
  (let [instructions (vec instructions)
        labels (into {} (keep-indexed (fn [index instruction]
                                        (when (= :mir/label (:mir/op instruction))
                                          [(:mir/id instruction) index]))
                                      instructions))]
    (loop [index 0, out []]
      (if (>= index (count instructions))
        (vec out)
        (let [producer (get instructions index)
              after-labels (loop [candidate (inc index)]
                             (if (= :mir/label
                                    (:mir/op (get instructions candidate)))
                               (recur (inc candidate))
                               candidate))
              move (get instructions after-labels)
              jump (get instructions (inc after-labels))
              source (:mir/dst producer)
              target-index (get labels (:mir/target jump))
              edge? (and (contains? a64-direct-result-ops (:mir/op producer))
                         (= :mir/move (:mir/op move))
                         (= source (:mir/src move))
                         (= :mir/jump (:mir/op jump))
                         target-index
                         (not (a64-used-before-definition?
                               (subvec instructions (inc target-index)) source)))
              return (get instructions (inc index))
              return? (and (contains? a64-direct-result-ops (:mir/op producer))
                           (= :mir/return (:mir/op return))
                           (= source (:mir/value return)))]
          (cond
            edge?
            (recur (inc after-labels)
                   (into out
                         (concat [(assoc producer :mir/dst (:mir/dst move))]
                                 (subvec instructions (inc index) after-labels))))

            return?
            (recur (+ index 2)
                   (conj out (assoc producer :mir/dst :aarch64/x0)
                         (assoc return :mir/value :aarch64/x0)))

            :else
            (recur (inc index) (conj out producer))))))))

(defn- lower-mc-instructions [isa instructions]
  (let [instructions (if (= :aarch64 isa)
                       (-> instructions
                           a64-fuse-multiplies
                           a64-coalesce-direct-results)
                       instructions)]
    (mapv (fn [{:mir/keys [op id test] :as instruction}]
            (case op
              :mir/label (layout/label id)
              :mir/reentry
              {:mc/op :mc/reentry :mc/parameters (:mir/parameters instruction)}
              :mir/recur
              {:mc/op :mc/recur :mc/arguments (:mir/arguments instruction)}
              :mir/branch-zero
              {:mc/op :mc/branch-zero :mc/test test
               :mc/target (:mir/target instruction)}
              :mir/branch-nonzero
              {:mc/op :mc/branch-nonzero :mc/test test
               :mc/target (:mir/target instruction)}
              :mir/jump
              {:mc/op :mc/jump :mc/target (:mir/target instruction)}
              (into {:mc/op :mc/instruction
                     :mc/encoding (keyword (name isa) (name op))}
                    (remove (fn [[k _]] (= k :mir/op)) instruction))))
          instructions)))

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
   'kernel-store-u32 [:gmir/kernel-store-u32 512]
   ;; 4096 because the lock word this names lives at offset 0 of a page, and
   ;; its callers declare lengths of both 512 and 4096. A 512 ceiling would
   ;; trap the 4096 ones on the length check before reaching the shared word.
   'kernel-try-lock-u32 [:gmir/kernel-try-lock-u32 4096]
   'kernel-unlock-u32 [:gmir/kernel-unlock-u32 4096]})

(def ^:private kir-x86-privileged-ops
  {'kernel-boot-info :boot-info
   'kernel-read-cr0 :read-cr0
   'kernel-write-cr0 :write-cr0
   'kernel-read-cr2 :read-cr2
   'kernel-read-cr3 :read-cr3
   'kernel-write-cr3 :write-cr3
   'kernel-invlpg :invlpg
   'kernel-read-cs :read-cs
   'kernel-page-fault-handler-address :page-fault-handler-address
   'kernel-page-fault-recovery-handler-address :page-fault-recovery-handler-address
   'kernel-configure-page-fault-recovery :configure-page-fault-recovery
   'kernel-double-fault-handler-address :double-fault-handler-address
   'kernel-configure-double-fault-ist :configure-double-fault-ist
   'kernel-load-gdt-tss :load-gdt-tss
   'kernel-load-idt :load-idt
   'kernel-probe-guard-write :probe-guard-write
   'kernel-probe-text-write :probe-text-write
   'kernel-probe-nx-execute :probe-nx-execute
   'kernel-probe-recoverable-guard-write :probe-recoverable-guard-write
   'kernel-probe-double-fault :probe-double-fault
   'kernel-cli :cli
   'kernel-sti :sti
   'kernel-hlt :hlt
   'kernel-pause :pause
   'kernel-out-u8 :out-u8
   'kernel-out-u32 :out-u32
   'kernel-in-u8 :in-u8
   'kernel-in-u32 :in-u32
   'kernel-read-msr :read-msr
   'kernel-write-msr :write-msr
   'kernel-cpuid-eax :cpuid-eax
   'kernel-cpuid-ebx :cpuid-ebx
   'kernel-cpuid-ecx :cpuid-ecx
   'kernel-cpuid-edx :cpuid-edx})

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

(def ^:private native-clock-request-type
  [:variant :kotoba.clock/request [[:wall :bool] [:monotonic :bool]]])

(def ^:private native-clock-wall-type
  [:record :kotoba.clock/wall
   [[:unix-millis :i64] [:observation-sequence :i64]]])

(def ^:private native-clock-monotonic-type
  [:record :kotoba.clock/monotonic
   [[:nanos :i64] [:observation-sequence :i64]]])

(def ^:private native-clock-error-type
  [:record :kotoba.clock/error [[:code :keyword] [:message :string]]])

(def ^:private native-clock-result-type
  [:variant :kotoba.clock/result
   [[:wall native-clock-wall-type]
    [:monotonic native-clock-monotonic-type]
    [:error native-clock-error-type]]])

(def ^:private native-dataspace-assert-type
  [:record :kotoba.dataspace/assert
   [[:assertion :document] [:facet :i64]]])

(def ^:private native-dataspace-retract-type
  [:record :kotoba.dataspace/retract
   [[:assertion :document] [:facet :i64]]])

(def ^:private native-dataspace-observe-type
  [:record :kotoba.dataspace/observe
   [[:pattern :document] [:facet :i64]]])

(def ^:private native-dataspace-request-type
  [:variant :kotoba.dataspace/request
   [[:assert native-dataspace-assert-type]
    [:retract native-dataspace-retract-type]
    [:observe native-dataspace-observe-type]
    [:facet-enter :bool]
    [:facet-leave :i64]]])

(def ^:private native-dataspace-asserted-type
  [:record :kotoba.dataspace/asserted
   [[:count :i64] [:notices :document]]])

(def ^:private native-dataspace-retracted-type
  [:record :kotoba.dataspace/retracted [[:count :i64]]])

(def ^:private native-dataspace-matches-type
  [:record :kotoba.dataspace/matches
   [[:bindings :document] [:notices :document]]])

(def ^:private native-dataspace-facet-type
  [:record :kotoba.dataspace/facet [[:id :i64]]])

(def ^:private native-dataspace-error-type
  [:record :kotoba.dataspace/error
   [[:code :keyword] [:message :string]]])

(def ^:private native-dataspace-result-type
  [:variant :kotoba.dataspace/result
   [[:asserted native-dataspace-asserted-type]
    [:retracted native-dataspace-retracted-type]
    [:matches native-dataspace-matches-type]
    [:facet native-dataspace-facet-type]
    [:error native-dataspace-error-type]]])

(def ^:private native-ui-parent-type [:option :keyword])
(def ^:private native-ui-node-type
  [:record :kotoba.ui/node
   [[:id :keyword] [:parent native-ui-parent-type]
    [:kind :keyword] [:text :string]]])
(def ^:private native-ui-node-set-type [:set native-ui-node-type])
(def ^:private native-ui-commit-request-type
  [:record :kotoba.ui/commit-request
   [[:base-revision :i64] [:nodes native-ui-node-set-type]]])
(def ^:private native-ui-commit-result-type
  [:record :kotoba.ui/commit-result [[:revision :i64] [:node-count :i64]]])
(def ^:private native-ui-event-request-type
  [:record :kotoba.ui/event-request [[:after-revision :i64]]])
(def ^:private native-ui-event-type
  [:record :kotoba.ui/event
   [[:revision :i64] [:target :keyword] [:kind :keyword] [:value :string]]])
(def ^:private native-ui-event-result-type [:option native-ui-event-type])

(def ^:private typed-capability-kinds
  {[:i64 :i64] :i64
   [:string :string] :string
   [:option-i64 :option-i64] :option-i64
   [:result-i64 :result-i64] :result-i64
   [native-clock-request-type native-clock-result-type] :clock-v1
   [native-dataspace-request-type native-dataspace-result-type] :dataspace-v1
   [native-ui-commit-request-type native-ui-commit-result-type] :ui-commit-v1
   [native-ui-event-request-type native-ui-event-result-type] :ui-event-v1})

(defn- capability-id
  "Return the closed host representation of an admitted capability id.

  NBB reads KIR i64 literals as JavaScript BigInt values. GMIR and the machine
  encoders intentionally represent the bounded 0..255 capability namespace as
  ordinary host integers, so normalize only after proving the value fits."
  [value]
  (let [value #?(:clj value
                 :cljs (if (i64/bigint-value? value) (js/Number value) value))]
    (when (and (integer? value) (<= 0 value 255)) value)))

(defn- valid-capability-id? [value]
  (some? (capability-id value)))

(defn word-result-type?
  "True for result descriptors represented by one native word. Escaping
  records and variants retain their explicit aggregate ABI boundary."
  [type]
  (or (contains? #{nil :i64 :bool :f32 :f64 :string :keyword :document
                   :option-i64 :result-i64
                   :vector :vector-f64 :string-index} type)
      (and (vector? type)
           (contains? #{:option :result :list :set :map :ref}
                      (first type)))))

(defn- scalar-literal? [form]
  (or (boolean? form) (gmir/i64-value? form)))

(defn- scalar-literal [form]
  (if (boolean? form) (if form 1 0) form))

(defn- utf8-bytes [content]
  (mapv #(bit-and (int %) 0xff)
        #?(:clj (.getBytes ^String content "UTF-8")
           :cljs (js/Array.from (.encode (js/TextEncoder.) content)))))

(defn- scalar-record-fields [type]
  (when (aggregate-abi/scalar-record-type? type)
    (nth type 2)))

(defn- record-value? [value]
  (= :record (:aggregate/kind value)))

(defn- record-value [type values]
  {:aggregate/kind :record :aggregate/type type :aggregate/values (vec values)})

(defn- scalar-variant-cases [type]
  (when (aggregate-abi/scalar-variant-type? type)
    (nth type 2)))

(defn- provider-record-fields [type]
  (when (contains? #{native-clock-wall-type native-clock-monotonic-type
                     native-clock-error-type
                     native-dataspace-assert-type native-dataspace-retract-type
                     native-dataspace-observe-type native-dataspace-asserted-type
                     native-dataspace-retracted-type native-dataspace-matches-type
                     native-dataspace-facet-type native-dataspace-error-type
                     native-ui-node-type native-ui-commit-request-type
                     native-ui-commit-result-type native-ui-event-request-type
                     native-ui-event-type}
                   type)
    (nth type 2)))

(defn- provider-variant-cases [type]
  (when (contains? #{native-clock-request-type native-clock-result-type
                     native-dataspace-request-type native-dataspace-result-type}
                   type)
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

(defn- normalize-surface-operations
  "Expand composite surface forms into the closed runtime/control subset.
  Generated lets preserve exact-once evaluation of reused operands."
  [body]
  (walk/postwalk
   (fn [form]
     (if-not (seq? form)
       form
       (let [op (first form), args (rest form)]
         (cond
           (and (= op 'option-some) (= 1 (count args)))
           (list 'pair 1 (first args))
           (and (= op 'option-none) (empty? args)) (list 'pair 0 0)
           (and (= op 'option-some?) (= 1 (count args)))
           (list 'pair-first (first args))
           (and (= op 'option-value) (= 2 (count args)))
           (let [[value fallback] args, tagged (gensym "option__")]
             (list 'let [tagged value]
                   (list 'if (list 'pair-first tagged)
                         (list 'pair-second tagged) fallback)))
           (and (= op 'option-some-of) (= 2 (count args)))
           (list 'pair 1 (second args))
           (and (= op 'option-none-of) (= 1 (count args))) (list 'pair 0 0)
           (and (= op 'option-some?-of) (= 2 (count args)))
           (list 'pair-first (second args))
           (and (= op 'option-value-of) (= 3 (count args)))
           (let [[_ value fallback] args, tagged (gensym "option__")]
             (list 'let [tagged value]
                   (list 'if (list 'pair-first tagged)
                         (list 'pair-second tagged) fallback)))
           (and (= op 'option-match) (= 5 (count args))
                (symbol? (nth args 3)))
           (let [[_ value none-body binder some-body] args
                 tagged (gensym "option__")]
             (list 'let [tagged value]
                   (list 'if (list 'pair-first tagged)
                         (list 'let [binder (list 'pair-second tagged)] some-body)
                         none-body)))
           (and (= op 'result-ok) (= 1 (count args)))
           (list 'pair 1 (first args))
           (and (= op 'result-err) (= 1 (count args)))
           (list 'pair 0 (first args))
           (and (= op 'result-ok?) (= 1 (count args)))
           (list 'pair-first (first args))
           (and (contains? '#{result-value result-error} op)
                (= 2 (count args)))
           (let [[value fallback] args, tagged (gensym "result__")
                 ok? (list 'pair-first tagged)
                 payload (list 'pair-second tagged)]
             (list 'let [tagged value]
                   (if (= op 'result-value)
                     (list 'if ok? payload fallback)
                     (list 'if ok? fallback payload))))
           (and (contains? '#{result-ok-of result-err-of} op)
                (= 2 (count args)))
           (list 'pair (if (= op 'result-ok-of) 1 0) (second args))
           (and (= op 'result-ok?-of) (= 2 (count args)))
           (list 'pair-first (second args))
           (and (contains? '#{result-value-of result-error-of} op)
                (= 3 (count args)))
           (let [[_ value fallback] args, tagged (gensym "result__")
                 ok? (list 'pair-first tagged)
                 payload (list 'pair-second tagged)]
             (list 'let [tagged value]
                   (if (= op 'result-value-of)
                     (list 'if ok? payload fallback)
                     (list 'if ok? fallback payload))))
           (and (= op 'result-match-of) (= 6 (count args))
                (symbol? (nth args 2)) (symbol? (nth args 4)))
           (let [[_ value ok-binder ok-body err-binder err-body] args
                 tagged (gensym "result__"), payload (list 'pair-second tagged)]
             (list 'let [tagged value]
                   (list 'if (list 'pair-first tagged)
                         (list 'let [ok-binder payload] ok-body)
                         (list 'let [err-binder payload] err-body))))
           (contains? '#{vector-new vector-f64-new} op)
           (reduce (fn [items item] (list 'vector-conj items item))
                   (list 'vector-new-empty) args)
           (= op 'typed-set-new)
           (reduce (fn [items item] (list 'vector-conj items item))
                   (list 'vector-new-empty) (rest args))
           (and (= op 'typed-set-conj) (= 3 (count args)))
           (list 'vector-conj (second args) (nth args 2))
           (and (= op 'typed-set-count) (= 2 (count args)))
           (list 'vector-count (second args))
           (and (= op 'typed-set-nth) (= 3 (count args)))
           (list 'vector-at (second args) (nth args 2))
           (and (contains? '#{vector-get vector-f64-get} op)
                (= 3 (count args)))
           (let [[items-form index-form fallback] args
                 items (gensym "vector__"), index (gensym "index__")]
             (list 'let [items items-form index index-form]
                   (list 'if (list 'if (list '< index 0) 0
                                   (list '< index (list 'vector-count items)))
                         (list 'vector-at items index)
                         fallback)))
           (and (= op 'keyword-name) (= 1 (count args)))
           (let [subject (gensym "keyword__")]
             (list 'let [subject (first args)]
                   (list 'string-substring subject 1
                         (list 'string-byte-length subject))))
           (and (= op 'keyword-from-string) (= 1 (count args)))
           (list 'string-concat ":" (first args))
           (and (= op 'string-contains?) (= 2 (count args)))
           (normalize-surface-operations (string-search/lower-contains args))
           (and (= op 'string-replace-all) (= 3 (count args)))
           (normalize-surface-operations (string-search/lower-replace-all args))
           (and (contains? '#{string-index-new string-index-count
                              string-index-contains string-index-get
                              string-index-assoc} op)
                (= (count args)
                   (get '{string-index-new 0 string-index-count 1
                          string-index-contains 2 string-index-get 2
                          string-index-assoc 3} op)))
           (normalize-surface-operations (string-index/lower op args))
           ;; Native `:document` is a string-shaped pair handle over UTF-8
           ;; EDN bytes. These casts are identity at the ABI; the host
           ;; inject reads and interns the same pair.
           (and (contains? '#{document-edn-read document-edn-print} op)
                (= 1 (count args)))
           (first args)
           :else form))))
   body))

(defn- normalize-scalar-variant-boundary
  "Lower the admitted scalar variant boundary to the existing one-word pair
  handle. This is used only for a module that declares a variant parameter or
  result; call-free local variants retain the allocation-free SROA path."
  [body]
  (walk/postwalk
   (fn [form]
     (if-not (seq? form)
       form
       (let [op (first form), args (rest form)]
         (cond
           (and (= op 'variant-new) (= 3 (count args)))
           (let [[type tag payload] args
                 cases (scalar-variant-cases type)
                 ordinal (first (keep-indexed (fn [index [candidate _]]
                                                (when (= candidate tag) index))
                                              cases))]
             (when (or (nil? cases) (nil? ordinal))
               (reject! :variant-boundary :invalid-constructor
                        {:type type :tag tag}))
             (list 'pair ordinal payload))

           (and (= op 'variant-match) (= 3 (count args)))
           (let [[type value branches] args
                 cases (scalar-variant-cases type)
                 declared (mapv first cases)
                 supplied (when (vector? branches) (mapv first branches))]
             (when-not (and cases (= declared supplied)
                            (every? #(and (vector? %) (= 3 (count %))
                                          (symbol? (second %)))
                                    branches))
               (reject! :variant-boundary :invalid-dispatch
                        {:type type :branches branches}))
             (let [tagged (gensym "variant__")
                   ordinal (list 'pair-first tagged)
                   payload (list 'pair-second tagged)
                   dispatch
                   (reduce (fn [fallback [index [_ binder branch]]]
                             (list 'if (list '= ordinal index)
                                   (list 'let [binder payload] branch)
                                   fallback))
                           (list 'quot 1 0)
                           (reverse (map-indexed vector branches)))]
               (list 'let [tagged value] dispatch)))

           :else form))))
   body))

(defn- normalize-scalar-record-boundary
  "Lower admitted record parameters/results and nested records to the
  declaration-order pair-chain handle. Post-order rewriting makes every inner
  record a one-word handle before its enclosing constructor is lowered."
  [body]
  (walk/postwalk
   (fn [form]
     (if-not (seq? form)
       form
       (let [op (first form), args (rest form)]
         (cond
           (and (= op 'record-new) (<= 2 (count args)))
           (let [[type & values] args, fields (scalar-record-fields type)]
             (when-not (and fields (= (count fields) (count values)))
               (reject! :record-boundary :invalid-constructor
                        {:type type :values values}))
             (reduce (fn [tail value] (list 'pair value tail))
                     0 (reverse values)))

           (and (= op 'record-get) (= 3 (count args)))
           (let [[type value field] args
                 fields (scalar-record-fields type)
                 index (first (keep-indexed (fn [i [candidate _]]
                                              (when (= candidate field) i))
                                            fields))]
             (when (or (nil? fields) (nil? index))
               (reject! :record-boundary :invalid-projection
                        {:type type :field field}))
             (list 'pair-first
                   (nth (iterate (fn [handle] (list 'pair-second handle)) value)
                        index)))

           :else form))))
   body))

(defn- normalize-provider-boundary
  "Lower the sealed clock provider's nested variant/record values to pair
  handles. This path is selected only by an exact typed-cap-call contract; it
  does not widen public entry aggregates or local SROA."
  [body]
  (walk/postwalk
   (fn [form]
     (if-not (seq? form)
       form
       (let [op (first form), args (rest form)]
         (cond
           (and (= op 'record-new) (<= 2 (count args))
                (provider-record-fields (first args)))
           (let [[type & values] args, fields (provider-record-fields type)]
             (when-not (and fields (= (count fields) (count values)))
               (reject! :provider-boundary :invalid-record-constructor
                        {:type type :values values}))
             (reduce (fn [tail value] (list 'pair value tail))
                     0 (reverse values)))

           (and (= op 'record-get) (= 3 (count args))
                (provider-record-fields (first args)))
           (let [[type value field] args
                 fields (provider-record-fields type)
                 index (first (keep-indexed (fn [i [candidate _]]
                                              (when (= candidate field) i))
                                            fields))]
             (when (or (nil? fields) (nil? index))
               (reject! :provider-boundary :invalid-record-projection
                        {:type type :field field}))
             (list 'pair-first
                   (nth (iterate (fn [handle] (list 'pair-second handle)) value)
                        index)))

           (and (= op 'variant-new) (= 3 (count args))
                (provider-variant-cases (first args)))
           (let [[type tag payload] args
                 cases (provider-variant-cases type)
                 ordinal (first (keep-indexed (fn [index [candidate _]]
                                                (when (= candidate tag) index))
                                              cases))]
             (when (or (nil? cases) (nil? ordinal))
               (reject! :provider-boundary :invalid-variant-constructor
                        {:type type :tag tag}))
             (list 'pair ordinal payload))

           (and (= op 'variant-match) (= 3 (count args))
                (provider-variant-cases (first args)))
           (let [[type value branches] args
                 cases (provider-variant-cases type)
                 declared (mapv first cases)
                 supplied (when (vector? branches) (mapv first branches))]
             (when-not (and cases (= declared supplied)
                            (every? #(and (vector? %) (= 3 (count %))
                                          (symbol? (second %)))
                                    branches))
               (reject! :provider-boundary :invalid-variant-dispatch
                        {:type type :branches branches}))
             (let [tagged (gensym "provider_variant__")
                   ordinal (list 'pair-first tagged)
                   payload (list 'pair-second tagged)
                   dispatch
                   (reduce (fn [fallback [index [_ binder branch]]]
                             (list 'if (list '= ordinal index)
                                   (list 'let [binder payload] branch)
                                   fallback))
                           (list 'quot 1 0)
                           (reverse (map-indexed vector branches)))]
               (list 'let [tagged value] dispatch)))

           :else form))))
   body))

(defn- scalar-boundary-type? [type]
  (or (word-result-type? type)
      (aggregate-abi/scalar-record-type? type)
      (aggregate-abi/scalar-variant-type? type)))

(defn- function-boundary-types [{:keys [params param-types result]}]
  (let [types (or param-types (vec (repeat (count params) :i64)))]
    (when (= (count params) (count types))
      (conj (vec types) result))))

(defn- variant-boundary-module? [functions]
  (boolean
   (or
    (some (fn [function]
            (some aggregate-abi/scalar-variant-type?
                  (function-boundary-types function)))
          functions)
    ;; Aggregate payload variants cannot use the two-register local SROA
    ;; representation: their payload record already occupies one word through
    ;; a pair-chain handle. Select the boxed normalization even when the
    ;; variant itself does not cross a function boundary.
    (some aggregate-abi/aggregate-payload-variant-type?
          (tree-seq coll? seq functions)))))

(defn- module-record-types [functions]
  (reduce
   (fn [types type]
     (let [name (second type)]
       (if-let [existing (get types name)]
         (do (when-not (= existing type)
               (reject! :record-boundary :conflicting-schema
                        {:name name :left existing :right type}))
             types)
         (assoc types name type))))
   {}
   (filter aggregate-abi/scalar-record-type?
           (tree-seq coll? seq functions))))

(defn- record-boundary-module?
  ([functions] (record-boundary-module? functions (module-record-types functions)))
  ([functions record-types]
   (boolean
    (or
     (some (fn [function]
             (some (fn [type]
                     (or (aggregate-abi/scalar-record-type? type)
                         (and (vector? type) (= :ref (first type))
                              (contains? record-types (second type)))))
                   (function-boundary-types function)))
           functions)
     ;; Flat local records retain allocation-free SROA. Nested records need
     ;; each inner value boxed to one word before it occupies an outer field,
     ;; so a module containing an inline nested schema uses pair-chain lowering.
     (some aggregate-abi/nested-record-type?
           (tree-seq coll? seq functions))
     ;; A flat record used as an aggregate variant payload is also boxed before
     ;; the enclosing tag/payload pair is constructed.
     (some aggregate-abi/aggregate-payload-variant-type?
           (tree-seq coll? seq functions))))))

(defn- provider-boundary-module? [functions]
  (boolean
   (some (fn [form]
           (and (seq? form) (= 'typed-cap-call (first form))
                (= 5 (count form))
                (let [kind (get typed-capability-kinds
                                [(nth form 2) (nth form 3)])]
                  (or (and (= :clock-v1 kind) (= 7 (second form)))
                      (and (= :dataspace-v1 kind) (= 24 (second form)))
                      (and (= :ui-commit-v1 kind) (= 9 (second form)))
                      (and (= :ui-event-v1 kind) (= 10 (second form)))))))
         (tree-seq coll? seq functions))))

(defn- tail-constructed-record-types
  "Record type descriptors a body can actually RETURN.

  Only a tail `record-new` reaches the result boundary and gets boxed into the
  pair chain a caller walks. A record constructed anywhere else is a local: a
  binding's value flattens into slots (ADR 0002) and an operand is consumed in
  place, so neither is boundary evidence. Walking the whole body instead
  rejected every function that builds one record while returning another --
  measured 2026-08-11 on kotoba-lang/murakumo, six of its thirty-three
  `*_core.kotoba` modules, all on that shape alone."
  [body]
  (if-not (seq? body)
    #{}
    (let [op (first body)]
      (cond
        (= op 'record-new) (let [type (second body)]
                             (if (aggregate-abi/scalar-record-type? type) #{type} #{}))
        (= op 'let) (tail-constructed-record-types (nth body 2 nil))
        (= op 'do) (tail-constructed-record-types (last body))
        (= op 'if) (into (tail-constructed-record-types (nth body 2 nil))
                         (tail-constructed-record-types (nth body 3 nil)))
        :else #{}))))

(defn- validate-record-reference-results! [functions]
  (doseq [{:keys [name result body]} functions
          :when (and (vector? result) (= :ref (first result)))
          type (tail-constructed-record-types body)]
    (when-not (= (second result) (second type))
      (reject! :record-boundary :result-schema-mismatch
               {:function name :result result :constructed type}))))

(defn- i64-mul [a b]
  #?(:clj (unchecked-multiply (long a) (long b))
     :cljs (i64/wrap-i64 (* (i64/->bigint a) (i64/->bigint b)))))

(defn- i64-add [a b]
  #?(:clj (unchecked-add (long a) (long b))
     :cljs (i64/wrap-i64 (+ (i64/->bigint a) (i64/->bigint b)))))

(def ^:private gmir-source-keys
  [:gmir/test :gmir/value :gmir/src :gmir/input :gmir/left :gmir/right
   :gmir/addend :gmir/base :gmir/length :gmir/index :gmir/stored
   :gmir/offset :gmir/size :gmir/arguments])

(def ^:private gmir-block-boundary
  #{:gmir/label :gmir/branch-zero :gmir/jump})

(def ^:private gmir-dce-ops
  ;; Only drop the arithmetic this pass introduces. Quotient and other
  ;; trapping ops stay even when their dst is unread (ordered `do`).
  #{:gmir/constant :gmir/add})

(defn- gmir-source-registers [instruction]
  (concat
   (mapcat (fn [key]
             (let [value (get instruction key)]
               (cond (vector? value) (filter gmir/vreg? value)
                     (gmir/vreg? value) [value]
                     :else [])))
           gmir-source-keys)
   (keep (fn [incoming]
           (when (gmir/vreg? (:gmir/value incoming))
             (:gmir/value incoming)))
         (:gmir/incomings instruction))))

(defn- gmir-defs [instructions]
  (into {} (keep (fn [instruction]
                   (when-let [dst (:gmir/dst instruction)]
                     [dst instruction]))
                 instructions)))

(defn- const-i64 [defs v]
  (let [instruction (get defs v)]
    (when (and instruction
               (= :gmir/constant (:gmir/op instruction))
               (gmir/i64-value? (:gmir/value instruction)))
      (:gmir/value instruction))))

(defn- add-const-base [defs v]
  (let [instruction (get defs v)]
    (when (and instruction (= :gmir/add (:gmir/op instruction)))
      (let [left (:gmir/left instruction)
            right (:gmir/right instruction)
            left-k (const-i64 defs left)
            right-k (const-i64 defs right)]
        (cond (and (some? right-k) (nil? left-k)) [left right-k]
              (and (some? left-k) (nil? right-k)) [right left-k]
              :else nil)))))

(defn- remap-gmir-sources [instruction aliases]
  (let [rename (fn [v] (get aliases v v))
        rename-maybe (fn [v]
                       (cond (vector? v) (mapv rename v)
                             (gmir/vreg? v) (rename v)
                             :else v))]
    (cond-> (reduce (fn [out key]
                      (if (contains? out key)
                        (update out key rename-maybe)
                        out))
                    instruction
                    gmir-source-keys)
      (:gmir/incomings instruction)
      (update :gmir/incomings
              (fn [incomings]
                (mapv (fn [incoming]
                        (if (gmir/vreg? (:gmir/value incoming))
                          (update incoming :gmir/value rename)
                          incoming))
                      incomings))))))

(defn- distribute-const-offset-multiplies [instructions next-reg]
  (let [defs (gmir-defs instructions)]
    (vec
     (mapcat
      (fn [instruction]
        (if-not (= :gmir/multiply (:gmir/op instruction))
          [instruction]
          (let [left (:gmir/left instruction)
                right (:gmir/right instruction)
                left-k (const-i64 defs left)
                right-k (const-i64 defs right)
                offset (cond (and (some? right-k) (nil? left-k))
                             (when-let [base (add-const-base defs left)]
                               {:base (first base) :k (second base)
                                :c right-k :c-reg right})
                             (and (some? left-k) (nil? right-k))
                             (when-let [base (add-const-base defs right)]
                               {:base (first base) :k (second base)
                                :c left-k :c-reg left}))]
            (if-not offset
              [instruction]
              (let [product (next-reg)
                    folded (next-reg)
                    kC (i64-mul (:k offset) (:c offset))]
                [{:gmir/op :gmir/multiply :gmir/dst product
                  :gmir/left (:base offset) :gmir/right (:c-reg offset)}
                 {:gmir/op :gmir/constant :gmir/dst folded :gmir/value kC}
                 {:gmir/op :gmir/add :gmir/dst (:gmir/dst instruction)
                  :gmir/left product :gmir/right folded}])))))
      instructions))))

(defn- fold-add-of-add-const [instructions next-reg]
  (let [defs (gmir-defs instructions)]
    (vec
     (mapcat
      (fn [instruction]
        (if-not (= :gmir/add (:gmir/op instruction))
          [instruction]
          (let [left (:gmir/left instruction)
                right (:gmir/right instruction)
                left-k (const-i64 defs left)
                right-k (const-i64 defs right)
                inner (cond (some? right-k) (add-const-base defs left)
                            (some? left-k) (add-const-base defs right)
                            :else nil)
                outer-k (or right-k left-k)]
            (if-not (and inner (some? outer-k))
              [instruction]
              (let [folded (next-reg)
                    sum (i64-add (second inner) outer-k)]
                [{:gmir/op :gmir/constant :gmir/dst folded :gmir/value sum}
                 {:gmir/op :gmir/add :gmir/dst (:gmir/dst instruction)
                  :gmir/left (first inner) :gmir/right folded}])))))
      instructions))))

(defn- const-key
  "An i64 constant in a form that can sit inside a map KEY on both hosts.

  ClojureScript represents an i64 as a JS BigInt, and `hash` on a BigInt throws
  `Cannot create property 'closure_uid_…' on bigint` -- `goog.getUid` cannot
  attach a property to a primitive. The throw is invisible until the map grows:
  eight or fewer entries is a PersistentArrayMap, which compares with `=` and
  never hashes, so a small function passes and a larger one does not.

  Measured 2026-08-18 against amu@29e8386 with this repository pinned at
  d4b050ae: a four-round i64 kernel compiled under nbb, a five-round one -- nine
  distinct constant multiplies, one past the array-map boundary -- answered
  `internal compiler error`, and the same source compiled through the JVM front.
  `bench/runtime-comparison/kernel.kotoba`, the benchmark this repository's own
  codegen work is measured on, is eight rounds, so `amu compile --target
  x86_64` of it could not run at all on the JDK-free front.

  Stringifying is enough: only intra-run uniqueness matters, and the decimal
  form of an integer is injective on both hosts."
  [value]
  (str value))

(defn- gvn-const-multiplies [instructions]
  (loop [remaining instructions
         mul-by {}
         aliases {}
         out []]
    (if-not (seq remaining)
      (->> out
           (mapv #(remap-gmir-sources % aliases)))
      (let [instruction (first remaining)]
        (cond
          (contains? gmir-block-boundary (:gmir/op instruction))
          (recur (next remaining) {} aliases (conj out instruction))

          (not= :gmir/multiply (:gmir/op instruction))
          (recur (next remaining) mul-by aliases (conj out instruction))

          :else
          (let [defs (gmir-defs (concat out remaining))
                left (:gmir/left instruction)
                right (:gmir/right instruction)
                left-k (const-i64 defs left)
                right-k (const-i64 defs right)
                ;; The constant is stringified because this vector becomes a
                ;; map key; see `const-key`.
                key (cond (some? right-k) [left (const-key right-k)]
                          (some? left-k) [right (const-key left-k)])]
            (if-not key
              (recur (next remaining) mul-by aliases (conj out instruction))
              (if-let [canonical (get mul-by key)]
                (recur (next remaining) mul-by
                       (assoc aliases (:gmir/dst instruction) canonical)
                       out)
                (recur (next remaining)
                       (assoc mul-by key (:gmir/dst instruction))
                       aliases
                       (conj out instruction))))))))))

(defn- dce-gmir [instructions]
  (loop [current (vec instructions)]
    (let [used (set (mapcat gmir-source-registers current))
          kept (filterv (fn [instruction]
                          (or (not (contains? gmir-dce-ops (:gmir/op instruction)))
                              (contains? used (:gmir/dst instruction))))
                        current)]
      (if (= kept current) kept (recur kept)))))

(defn- rewrite-offset-multiplies
  "LLVM's first-round trick on `(n+k)*C+1`: distribute a constant offset
  through the multiply, fold the now-constant addend, and reuse `n*C`.

  Valid wrapping i64: (n+k)*C+1 = n*C+(k*C+1). The add that produced n+k
  is left in place if it still has other readers."
  [instructions]
  (let [max-index (reduce max -1 (keep (fn [instruction]
                                         (when-let [dst (:gmir/dst instruction)]
                                           (when (gmir/vreg? dst)
                                             #?(:clj (Long/parseLong (name dst))
                                                :cljs (js/parseInt (name dst) 10)))))
                                       instructions))
        next-reg (let [counter (atom max-index)]
                   #(gmir/vreg (swap! counter inc)))]
    (-> instructions
        (distribute-const-offset-multiplies next-reg)
        (fold-add-of-add-const next-reg)
        gvn-const-multiplies
        dce-gmir)))

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
   (let [body (normalize-surface-operations body)
        next-reg (atom -1)
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

            (string-literal-value [content]
              (let [address (fresh-reg), length (fresh-reg), dst (fresh-reg)]
                [[{:gmir/op :gmir/data-address :gmir/dst address
                   :gmir/content content}
                  {:gmir/op :gmir/constant :gmir/dst length
                   :gmir/value (count (utf8-bytes content))}
                  {:gmir/op :gmir/runtime-call :gmir/dst dst :gmir/runtime :pair
                   :gmir/arguments [address length]}]
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

                (string? form) (string-literal-value form)
                (keyword? form) (string-literal-value (str form))

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

                (and (seq? form)
                     (contains? kir-x86-privileged-ops (first form)))
                (let [action (get kir-x86-privileged-ops (first form))
                      arguments (vec (rest form))
                      expected (get gmir/x86-privileged-action-arities action)
                      lowered (mapv #(value % env) arguments)
                      registers (mapv #(scalar-register! (second %) form) lowered)
                      dst (fresh-reg)]
                  (when-not (= expected (count arguments))
                    (reject! :kir-to-gmir :x86-privileged-arity
                             {:form form :action action :expected expected}))
                  [(conj (vec (mapcat first lowered))
                         {:gmir/op :gmir/x86-privileged :gmir/dst dst
                          :gmir/action action :gmir/arguments registers})
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
                (let [capability (capability-id (second form))
                      [code input] (value (nth form 2) env)
                      dst (fresh-reg)]
                  (when-not capability
                    (reject! :kir-to-gmir :invalid-capability-id {:form form}))
                  [(conj code {:gmir/op :gmir/capability-call :gmir/dst dst
                               :gmir/capability capability :gmir/kind :i64
                               :gmir/arguments [(scalar-register! input form)]})
                   dst])

                (and (seq? form) (= 'typed-cap-call (first form))
                     (= 5 (count form)))
                (let [[_ raw-capability request-type result-type request] form
                      capability (capability-id raw-capability)
                      kind (get typed-capability-kinds [request-type result-type])
                      [code input] (value request env)
                      dst (fresh-reg)]
                  (when-not (and capability kind)
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

                (and (seq? form) (contains? signatures (first form)))
                (let [callee (first form)
                      arguments (vec (rest form))
                      expected (get signatures callee)]
                  (when-not (= expected (count arguments))
                    (reject! :kir-to-gmir :call-arity-mismatch
                             {:form form :callee callee :expected expected}))
                  (let [lowered (mapv #(value % env) arguments)
                        registers (mapv #(scalar-register! (second %) form) lowered)]
                    (into (vec (mapcat first lowered))
                          [{:gmir/op :gmir/tail-call :gmir/callee callee
                            :gmir/arguments registers}])))

                :else
                (let [[code result-value] (value form env)
                      result (scalar-register! result-value form)]
                  (conj code {:gmir/op :gmir/return :gmir/value result}))))]
      (let [instructions (rewrite-offset-multiplies
                          (into parameter-code (tail body parameter-env)))]
        {:gmir/version (cond
                         (some #(contains? #{:gmir/call :gmir/tail-call}
                                            (:gmir/op %)) instructions) 3
                         (some #(= :gmir/phi (:gmir/op %)) instructions) 2
                         :else 1)
         :gmir/instructions instructions})))))

(defn pilot-expression?
  "True only for the deliberately bounded production migration slice.

  Scalar arithmetic, comparisons, predicates, lexical `let`, ordered `do`,
  recursive `if`, fixed scalar-field record SROA, and non-escaping scalar
  variant SROA use the extracted IR path; allocation spills when necessary."
  [params body]
  (let [body (normalize-surface-operations body)
        parameters (set params)]
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

                (and (seq? form)
                     (contains? kir-x86-privileged-ops (first form))
                     (= (get gmir/x86-privileged-action-arities
                             (get kir-x86-privileged-ops (first form)))
                        (count (rest form)))
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
    (and (vector? params) (<= (count params) 5)
         (= (count params) (count parameters))
         (every? symbol? params)
         (= :scalar (shape body (zipmap params (repeat :scalar))))))))

(defn lower-kir-module
  "Lower a closed multi-function KIR module to GMIR v3. The first export owns
  the GMIR entry identity; all requested exports are retained by final native
  layout. Every function is scalar-boundary-only and direct calls resolve
  against the module signature table."
  [kir]
  (let [functions (:functions kir)
        exports (:exports kir)
        record-types (module-record-types functions)]
    (validate-record-reference-results! functions)
    (when-not (and (vector? functions) (seq functions)
                   (vector? exports) (seq exports)
                   (= (count exports) (count (distinct exports)))
                   (every? gmir/function-id? exports)
                   (every? #(and (map? %)
                                 (gmir/function-id? (:name %))
                                 (vector? (:params %))
                                 (let [types (function-boundary-types %)]
                                   (and types (every? scalar-boundary-type? types))))
                           functions))
      (reject! :kir-to-gmir :unsupported-function-module kir))
    (let [signatures (into {} (map (juxt :name #(count (:params %))) functions))
          names (mapv :name functions)
          entry (first exports)
          variant-boundary? (variant-boundary-module? functions)
          record-boundary? (record-boundary-module? functions record-types)
          provider-boundary? (provider-boundary-module? functions)]
      (when-not (and (= (count names) (count (distinct names)))
                     (every? #(contains? signatures %) exports))
        (reject! :kir-to-gmir :invalid-function-module
                 {:entry entry :exports exports :functions names}))
      (gmir/validate!
       {:gmir/version 3
        :gmir/entry entry
        :gmir/functions
        (mapv (fn [{:keys [name params body]}]
                (let [body (cond-> body
                             provider-boundary? normalize-provider-boundary
                             record-boundary? normalize-scalar-record-boundary
                             variant-boundary? normalize-scalar-variant-boundary)
                      lowered (lower-kir-expression params body signatures)]
                  {:gmir/name name
                   :gmir/arity (count params)
                   :gmir/instructions (:gmir/instructions lowered)}))
              functions)}))))

(defn pilot-module?
  "True when a checked KIR module can use the extracted scalar-call pipeline.
  At least one call is required so call-free programs retain their existing
  per-expression migration route."
  [kir]
  (try
         (let [module (lower-kir-module kir)]
           (or (record-boundary-module? (:functions kir))
               (variant-boundary-module? (:functions kir))
               (provider-boundary-module? (:functions kir))
               (boolean
                (some #(some (fn [instruction]
                               (= :gmir/data-address (:gmir/op instruction)))
                             (:gmir/instructions %))
                      (:gmir/functions module)))
               (boolean
                (some #(some (fn [instruction]
                               (contains? #{:gmir/call :gmir/tail-call}
                                          (:gmir/op instruction)))
                             (:gmir/instructions %))
                      (:gmir/functions module)))))
         (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) _ false)))

;; ── MC -> bytes ──────────────────────────────────────────────────────────────

(def ^:private x86-register-code
  {:x86-64/rax 0 :x86-64/rcx 1 :x86-64/rdx 2 :x86-64/rbx 3 :x86-64/r8 8
   :x86-64/r9 9 :x86-64/r10 10 :x86-64/r11 11
   ;; R12-R15 are callee-saved and enter allocated MIR through the preserved
   ;; tier. Every encoder here selects REX.B/REX.R from `(>= code 8)` and the
   ;; ModRM field from `(bit-and code 7)`, so they need no special case: R12's
   ;; low three bits are RSP's, but a SIB byte follows only when mod is not 11,
   ;; and register-to-register forms are always mod 11.
   :x86-64/r12 12 :x86-64/r13 13 :x86-64/r14 14 :x86-64/r15 15
   :x86-64/rdi 7 :x86-64/rsi 6})
(def ^:private x86-arguments [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8])
(def ^:private aarch64-register-code
  {:aarch64/x0 0 :aarch64/x1 1 :aarch64/x2 2 :aarch64/x3 3
   :aarch64/x4 4 :aarch64/x5 5 :aarch64/x6 6 :aarch64/x7 7
   ;; x8-x12 are caller-saved temporaries and reach allocated MIR through the
   ;; leaf tier, which is offered only to functions that call nothing.
   :aarch64/x8 8 :aarch64/x9 9 :aarch64/x10 10 :aarch64/x11 11
   :aarch64/x12 12
   ;; x13-x15 are leaf-only constant-cache registers. x16-x17 remain the
   ;; local encoder scratch pair and are never admitted to allocated MIR.
   ;; x18 is the reserved platform register and is deliberately absent.
   :aarch64/x13 13 :aarch64/x14 14 :aarch64/x15 15
   :aarch64/x16 16 :aarch64/x17 17
   ;; x19-x26 are callee-saved and enter through the preserved tier.
   :aarch64/x19 19 :aarch64/x20 20 :aarch64/x21 21 :aarch64/x22 22
   :aarch64/x23 23 :aarch64/x24 24 :aarch64/x25 25 :aarch64/x26 26})

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

;; Hacker's Delight signed reciprocal construction. All arithmetic here is
;; wider than i64: the returned multiplier is normalized back to one signed
;; word only after the exact recurrence terminates. Keeping this computation
;; in the encoder means GMIR retains the source operation and the independent
;; verifier can deterministically re-derive the same selected bytes.
(def ^:private wide-zero #?(:clj 0N :cljs (js/BigInt 0)))
(def ^:private wide-one #?(:clj 1N :cljs (js/BigInt 1)))
(def ^:private wide-two63
  #?(:clj 9223372036854775808N :cljs (js/BigInt "9223372036854775808")))
(def ^:private wide-two64
  #?(:clj 18446744073709551616N :cljs (js/BigInt "18446744073709551616")))
(def ^:private wide-max-i64
  #?(:clj 9223372036854775807N :cljs (js/BigInt "9223372036854775807")))
(def ^:private wide-min-i64
  #?(:clj -9223372036854775808N :cljs (js/BigInt "-9223372036854775808")))

(defn- ->wide [value]
  #?(:clj (bigint value) :cljs (i64/->bigint value)))

(defn- wide-quot [left right]
  #?(:clj (quot left right) :cljs (/ left right)))

(defn- wide-mod [left right]
  (- left (* (wide-quot left right) right)))

(defn- wide-neg? [value] (< value wide-zero))

(defn signed-division-magic
  "Return the exact signed reciprocal multiplier and post-shift for DIVISOR.

  Zero and +/-1 deliberately stay on the guarded hardware path. For every
  other i64 divisor the result implements truncation toward zero using one
  signed multiply-high, an optional numerator correction, an arithmetic
  shift, and a final sign correction."
  [divisor]
  (let [divisor (->wide divisor)]
    (when (and (not= divisor wide-zero)
               (not= divisor wide-one)
               (not= divisor (- wide-one)))
      (let [negative-divisor? (wide-neg? divisor)
            absolute-divisor (if negative-divisor? (- divisor) divisor)
            t (+ wide-two63 (if negative-divisor? wide-one wide-zero))
            anc (- t wide-one (wide-mod t absolute-divisor))
            initial-q1 (wide-quot wide-two63 anc)
            initial-q2 (wide-quot wide-two63 absolute-divisor)]
        (loop [power 63
               q1 initial-q1, r1 (- wide-two63 (* initial-q1 anc))
               q2 initial-q2, r2 (- wide-two63 (* initial-q2 absolute-divisor))]
          (let [power (inc power)
                doubled-q1 (* (+ wide-one wide-one) q1)
                doubled-r1 (* (+ wide-one wide-one) r1)
                [q1 r1] (if (>= doubled-r1 anc)
                          [(+ doubled-q1 wide-one) (- doubled-r1 anc)]
                          [doubled-q1 doubled-r1])
                doubled-q2 (* (+ wide-one wide-one) q2)
                doubled-r2 (* (+ wide-one wide-one) r2)
                [q2 r2] (if (>= doubled-r2 absolute-divisor)
                          [(+ doubled-q2 wide-one)
                           (- doubled-r2 absolute-divisor)]
                          [doubled-q2 doubled-r2])
                delta (- absolute-divisor r2)]
            (if (or (< q1 delta) (and (= q1 delta) (= r1 wide-zero)))
              (recur power q1 r1 q2 r2)
              (let [multiplier (+ q2 wide-one)
                    multiplier (if negative-divisor? (- multiplier) multiplier)
                    multiplier (cond
                                 (> multiplier wide-max-i64) (- multiplier wide-two64)
                                 (< multiplier wide-min-i64) (+ multiplier wide-two64)
                                 :else multiplier)]
                {:multiplier multiplier
                 :shift (- power 64)
                 :add-numerator? (and (not negative-divisor?)
                                      (wide-neg? multiplier))
                 :subtract-numerator? (and negative-divisor?
                                            (not (wide-neg? multiplier)))}))))))))

(declare a64-register x86-mov-imm x86-mov-imm-fixed)

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
        ;; The three registers `idiv` writes or reads implicitly each need their
        ;; own unwinding. Every other allocated register -- the whole leaf and
        ;; preserved tiers included -- takes the same shape: move the quotient
        ;; out of RAX, then pop all three back.
        restore (condp = dst
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
                  (concat (x86-rr 0x89 dst :x86-64/rax)
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

(defn- x86-quotient-constant [dst left divisor reciprocal-live? result-in-r11?]
  (if-let [{:keys [multiplier shift add-numerator? subtract-numerator?]}
           (signed-division-magic divisor)]
    ;; RAX and RDX are saved because `imul r10` writes both and MIR declares
    ;; only `dst` as written, so whatever the allocator left in them has to come
    ;; back. Neither of the two reads of the numerator needs to go through those
    ;; saved slots, though:
    ;;
    ;; - the read BEFORE the multiply does not, because `push` does not modify
    ;;   the register it pushes. When `left` is RAX the value is already in
    ;;   place and the instruction is nothing at all; otherwise a register move
    ;;   reaches it, since nothing has been clobbered yet.
    ;; - the read AFTER the multiply does not either, if the numerator is put
    ;;   in R11 first. R11 is outside MIR's allocator profile and is where the
    ;;   result accumulates anyway, so `add r11,rdx` finishes the add-numerator
    ;;   case with no separate move and no reload.
    ;;
    ;; Together that removes two eight-byte stack reads per division and, in
    ;; the add-numerator case, the `mov r11,rdx` as well.
    (let [numerator? (or add-numerator? subtract-numerator?)
          move (fn [target source]
                 (if (= target source) [] (x86-rr 0x89 target source)))]
      (vec
       (concat
        (x86-push :x86-64/rax)
        (x86-push :x86-64/rdx)
        (when numerator? (move :x86-64/r11 left))
        (move :x86-64/rax left)
        (when-not reciprocal-live? (x86-mov-imm :x86-64/r10 multiplier))
        ;; imul r10: signed RDX:RAX = RAX * R10
        [0x49 0xf7 0xea]
        (cond
          ;; r11 already holds the numerator; RDX holds the high half.
          add-numerator? (x86-rr 0x01 :x86-64/r11 :x86-64/rdx)
          ;; high - numerator, computed in RDX because it is already clobbered.
          subtract-numerator? (concat (x86-rr 0x29 :x86-64/rdx :x86-64/r11)
                                      (x86-rr 0x89 :x86-64/r11 :x86-64/rdx))
          :else (x86-rr 0x89 :x86-64/r11 :x86-64/rdx))
        (when (pos? shift) [0x49 0xc1 0xfb shift]) ; sar r11,shift
        ;; RDX rather than R10: it is dead here in every branch above and the
        ;; pop restores it regardless, which leaves R10 free to keep carrying
        ;; the reciprocal into the next division.
        (x86-rr 0x89 :x86-64/rdx :x86-64/r11)
        [0x48 0xc1 0xea 0x3f] ; shr rdx,63
        (x86-rr 0x01 :x86-64/r11 :x86-64/rdx)
        (x86-pop :x86-64/rdx)
        (x86-pop :x86-64/rax)
        (when-not (or result-in-r11? (= dst :x86-64/r11))
          (x86-rr 0x89 dst :x86-64/r11)))))
    ;; Zero and +/-1 retain the established hardware guards. They are uncommon
    ;; in real optimized code and keeping one path prevents special-case trap
    ;; semantics from drifting between the two ISAs.
    (vec (concat (x86-mov-imm :x86-64/r11 divisor)
                 (x86-quotient dst left :x86-64/r11)))))

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

;; `movabs r64,imm64` is ten bytes (eleven for r8-r15) whatever the value is,
;; so a literal 1 costs exactly what 2^63 costs. Two narrower forms cover
;; almost every constant a program contains:
;;
;;   0 <= v <= 0xFFFFFFFF   mov r32,imm32   five bytes, zero-extends to 64
;;   -2^31 <= v < 0         mov r64,imm32   seven bytes, sign-extends
;;
;; `xor r32,r32` would encode zero in two, and is deliberately not used: it
;; writes flags where a `mov` writes none, and these bytes land in a stream
;; whose later instructions were emitted expecting no flag change.
;;
;; Narrowing is sound because every intra-function branch is a
;; `kotoba.codegen.layout` token, so displacements resolve after final token
;; sizes are known.
(defn- x86-immediate-form [value]
  #?(:clj (let [v (long value)]
            (cond (and (<= 0 v) (<= v 0xFFFFFFFF)) :zero-extended
                  (and (<= -2147483648 v) (neg? v)) :sign-extended
                  :else :full))
     :cljs (let [v (i64/->bigint value)]
             (cond (and (>= v (js/BigInt 0)) (<= v (js/BigInt "4294967295"))) :zero-extended
                   (and (>= v (js/BigInt "-2147483648")) (< v (js/BigInt 0))) :sign-extended
                   :else :full))))

(defn- x86-le32 [n]
  #?(:clj (mapv #(bit-and (unsigned-bit-shift-right (long n) (* 8 %)) 0xff) (range 4))
     :cljs (let [u (js/BigInt.asUintN 32 (i64/->bigint n))
                 base (js/BigInt 256)]
             (loop [i 0 rem u out []]
               (if (= i 4)
                 out
                 (recur (inc i) (/ rem base)
                        (conj out (js/Number (bit-and rem (js/BigInt 0xff))))))))))

;; The full-width form, for values that are NOT final when their width is
;; chosen. `resolve-program-layout` reserves a token's width from a first pass
;; and then demands exactly that many bytes back; a data address is not known
;; until the layout resolves, so narrowing it would reserve ten bytes for an
;; offset that later encodes in five and trip the reserved-width check — which
;; is precisely what it is there to catch. Compile-time constants have no such
;; problem: their value is final before anything is sized.
;; x86-64 folds a constant straight into add, sub and multiply, so the separate
;; `mov reg,imm` that fed them disappears along with the register it occupied.
;; Every one of these immediates is a sign-extended imm32, so a value outside
;; the signed 32-bit range keeps the two-instruction form.
;;
;;   add r64,imm32   REX.W 81 /0 id
;;   sub r64,imm32   REX.W 81 /5 id
;;   imul r64,r64,imm32   REX.W 69 /r id   -- three-operand, so dst may differ
;;                                            from the source and no move is
;;                                            needed ahead of it either
(defn- x86-imm32? [value]
  #?(:clj (let [v (long value)] (and (<= -2147483648 v) (<= v 2147483647)))
     :cljs (let [v (i64/->bigint value)]
             (and (>= v (js/BigInt "-2147483648")) (<= v (js/BigInt "2147483647"))))))

(defn- x86-alu-imm [slash dst value]
  (let [d (get x86-register-code dst)]
    (when-not (some? d) (reject! :mc-encode :unsupported-register {:dst dst}))
    (into [(bit-or 0x48 (if (>= d 8) 1 0)) 0x81
           (bit-or 0xc0 (bit-shift-left slash 3) (bit-and d 7))]
          (x86-le32 value))))

;; `lea dst,[src+disp]` computes what `mov dst,src` then `add dst,imm` computes,
;; in one instruction, when the destination differs from the source. It is sound
;; here because it writes no flags and nothing reads the flags the `add` wrote:
;; every flag consumer this backend emits carries its own producer in the same
;; unit — `x86-compare` puts `cmp` immediately before `setcc`, and
;; `:mc/branch-zero` puts `test reg,reg` immediately before `jz`. No flag ever
;; travels between two MIR instructions.
;;
;; Returns nil when the base register would need a SIB byte (RSP and R12 encode
;; rm=100, which means "SIB follows"), leaving the caller on the two-instruction
;; form rather than emitting a different addressing mode than it intended.
(defn- x86-lea-disp32 [dst src displacement]
  (let [d (get x86-register-code dst)
        s (get x86-register-code src)]
    (when (and (some? d) (some? s) (not= 4 (bit-and s 7)))
      (into [(bit-or 0x48 (if (>= d 8) 4 0) (if (>= s 8) 1 0)) 0x8d
             (bit-or 0x80 (bit-shift-left (bit-and d 7) 3) (bit-and s 7))]
            (x86-le32 displacement)))))

(defn- x86-negatable-imm32?
  "A displacement may be negated for `sub`; the one signed 32-bit value whose
   negation does not fit is the minimum."
  [value]
  #?(:clj (> (long value) -2147483648)
     :cljs (> (i64/->bigint value) (js/BigInt "-2147483648"))))

(defn- x86-imul-imm [dst src value]
  (let [d (get x86-register-code dst)
        s (get x86-register-code src)]
    (when-not (and (some? d) (some? s))
      (reject! :mc-encode :unsupported-register {:dst dst :src src}))
    (into [(bit-or 0x48 (if (>= d 8) 4 0) (if (>= s 8) 1 0)) 0x69
           (bit-or 0xc0 (bit-shift-left (bit-and d 7) 3) (bit-and s 7))]
          (x86-le32 value))))

(defn- x86-mov-imm-fixed [dst value]
  (let [d (get x86-register-code dst)]
    (when-not (some? d) (reject! :mc-encode :unsupported-register {:dst dst}))
    (into [(bit-or 0x48 (if (>= d 8) 1 0)) (+ 0xb8 (bit-and d 7))] (le64 value))))

(defn- x86-mov-imm [dst value]
  (let [d (get x86-register-code dst)]
    (when-not (some? d) (reject! :mc-encode :unsupported-register {:dst dst}))
    (case (x86-immediate-form value)
      :zero-extended (into (if (>= d 8) [0x41 (+ 0xb8 (bit-and d 7))] [(+ 0xb8 d)])
                           (x86-le32 value))
      :sign-extended (into [(bit-or 0x48 (if (>= d 8) 1 0)) 0xc7
                            (bit-or 0xc0 (bit-and d 7))]
                           (x86-le32 value))
      :full (into [(bit-or 0x48 (if (>= d 8) 1 0)) (+ 0xb8 (bit-and d 7))]
                  (le64 value)))))

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

(defn- a64-constant-chunks [value]
  #?(:clj (mapv #(bit-and (unsigned-bit-shift-right (long value) %) 0xffff)
                 [0 16 32 48])
     :cljs (let [u (js/BigInt.asUintN 64 (i64/->bigint value))
                 base (js/BigInt 65536)
                 mask (js/BigInt 65535)]
             (loop [i 0, remaining u, out []]
               (if (= i 4) out
                   (recur (inc i) (/ remaining base)
                          (conj out (js/Number (bit-and remaining mask)))))))))

(defn- a64-wide-move [opcode rd chunk lane]
  (u32le (bit-or opcode
                 (bit-shift-left lane 21)
                 (bit-shift-left chunk 5)
                 rd)))

(defn- a64-logical-immediate-fields [chunks]
  ;; AArch64 logical immediates are a rotated, non-empty/non-full run of ones
  ;; in a power-of-two element, replicated to the register width. Work from
  ;; the already exact four u16 chunks so this selector is identical on the
  ;; JVM and in ClojureScript (where bitwise numbers are otherwise only i32).
  (let [bit-at (fn [index]
                 (not (zero? (bit-and (nth chunks (quot index 16))
                                      (bit-shift-left 1 (mod index 16))))))
        bits (mapv bit-at (range 64))]
    (some
     (fn [width]
       (when (every? #(= (nth bits %) (nth bits (mod % width))) (range 64))
         (some
          (fn [ones]
            (some
             (fn [rotation]
               (when (every? (fn [index]
                               (= (nth bits index)
                                  (< (mod (+ (mod index width) rotation) width)
                                     ones)))
                             (range 64))
                 (let [len ({2 1, 4 2, 8 3, 16 4, 32 5, 64 6} width)]
                   {:n (if (= width 64) 1 0)
                    :immr rotation
                    :imms (bit-or (bit-and (- (* 2 width)) 0x3f)
                                  (dec ones))})))
             (range width)))
          (range 1 width))))
     [2 4 8 16 32 64])))

(defn- a64-logical-immediate [rd chunks]
  (when-let [{:keys [n immr imms]} (a64-logical-immediate-fields chunks)]
    ;; ORR Xd,XZR,#imm is the architectural MOV (bitmask immediate) alias.
    (u32le (bit-or 0xb20003e0
                   (bit-shift-left n 22)
                   (bit-shift-left immr 16)
                   (bit-shift-left imms 10)
                   rd))))

(defn- a64-constant-fixed
  "The legacy four-word form. Keep it only where an enclosing sequence has a
  fixed local branch displacement or layout has reserved exactly 16 bytes."
  [dst value]
  (let [rd (a64-register dst)]
    (vec (mapcat (fn [lane chunk]
                   (a64-wide-move (if (zero? lane) 0xd2800000 0xf2800000)
                                  rd chunk lane))
                 (range 4) (a64-constant-chunks value)))))

(defn- a64-constant [dst value]
  (let [rd (a64-register dst)
        chunks (a64-constant-chunks value)
        movz-lanes (keep-indexed #(when-not (zero? %2) %1) chunks)
        movn-lanes (keep-indexed #(when-not (= 0xffff %2) %1) chunks)
        movn? (< (max 1 (count movn-lanes)) (max 1 (count movz-lanes)))
        lanes (if movn? movn-lanes movz-lanes)
        first-lane (or (first lanes) 0)
        fill (if movn? 0xffff 0)
        first-chunk (nth chunks first-lane)
        initial (a64-wide-move (if movn? 0x92800000 0xd2800000)
                               rd (if movn? (bit-and (bit-not first-chunk) 0xffff)
                                      first-chunk)
                               first-lane)
        wide (vec
              (concat
               initial
               (mapcat (fn [lane]
                         (when (and (not= lane first-lane)
                                    (not= fill (nth chunks lane)))
                           (a64-wide-move 0xf2800000 rd (nth chunks lane) lane)))
                       (range 4))))
        logical (a64-logical-immediate rd chunks)]
    ;; Preserve the established wide-move spelling on ties. Apart from making
    ;; output deterministic, MOVZ/MOVN is the simpler dependency-breaking form.
    (if (and logical (< (count logical) (count wide))) logical wide)))

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

(defn- x86-kernel-bounds-check
  "The shared preamble for every checked kernel access: the declared length is
  within this operation's ceiling, the base is not null, the index is inside
  the length, and a 32-bit access has four bytes left after it. Branches to
  `trap` on any violation, and otherwise leaves R11 holding base+index. R10 is
  scratch here and dead afterwards, which is what lets the lock sequence below
  borrow it without saving anything."
  [trap width {:mir/keys [base length index maximum]}]
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
        (x86-rr 0x01 :x86-64/r11 index))))

(defn- x86-set-zero-flag
  "`sete dst8` then zero-extend, the tail `x86-compare` already uses. Written
  once here because the lock sequence needs the same two instructions and the
  REX bookkeeping for a high register is easy to get subtly wrong twice."
  [dst]
  (let [d (get x86-register-code dst)]
    (when-not (some? d)
      (reject! :mc-encode :unsupported-register {:dst dst}))
    (vec (concat (when (>= d 8) [0x41])
                 [0x0f 0x94 (bit-or 0xc0 (bit-and d 7))
                  (bit-or 0x48 (if (>= d 8) 5 0)) 0x0f 0xb6
                  (bit-or 0xc0
                          (bit-shift-left (bit-and d 7) 3)
                          (bit-and d 7))]))))

(defn- x86-kernel-memory
  [instruction-index width store? {:mir/keys [dst stored] :as instruction}]
  (let [trap (memory-label instruction-index "trap")
        done (memory-label instruction-index "done")
        result (if store? stored dst)]
    (vec (concat
          (x86-kernel-bounds-check trap width instruction)
          (x86-memory-access (keyword (str (if store? "store" "load")
                                           "-u" width)) result)
          [(layout/relative-branch :x86-64/jmp-rel32 done)
           (layout/label trap)]
          [0x0f 0x0b]
          [(layout/label done)]))))

(defn- x86-kernel-lock
  "One atomic compare-and-swap of the u32 at base+index, against a comparand
  and a replacement that the OPERATION fixes rather than the guest. `dst`
  receives 1 when this call performed the swap and 0 when it did not.

  `lock cmpxchg` reads its comparand from EAX and writes the observed word
  back there, and RAX is allocatable in this profile, so it is pushed and
  popped around the sequence -- the same thing `x86-quotient` does for its own
  RAX/RDX pair. R10 carries the replacement: it is dead after the bounds
  check, so nothing allocated is disturbed. POP does not touch the flags, so
  RAX is restored before ZF is read, and `dst` may safely alias any of the
  three sources because all of them were consumed by the preamble."
  [instruction-index expected desired {:mir/keys [dst] :as instruction}]
  (let [trap (memory-label instruction-index "lock-trap")
        done (memory-label instruction-index "lock-done")]
    (vec (concat
          (x86-kernel-bounds-check trap 32 instruction)
          (x86-push :x86-64/rax)
          (x86-mov-imm :x86-64/rax expected)
          (x86-mov-imm :x86-64/r10 desired)
          ;; lock cmpxchg [r11], r10d -- REX.R for r10, REX.B for r11, and
          ;; ModRM mod=00 rm=011 is a bare [R11] because 011 is neither the
          ;; SIB escape nor the RIP-relative form.
          [0xf0 0x45 0x0f 0xb1 0x13]
          (x86-pop :x86-64/rax)
          (x86-set-zero-flag dst)
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

(defn- a64-kernel-bounds-check
  "AArch64's half of the shared preamble. Same four checks as the x86 side,
  leaving x16 holding base+index. x16/x17 are the encoder scratch pair and are
  never admitted to allocated MIR, so neither can collide with an operand."
  [trap width {:mir/keys [base length index maximum]}]
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
                       (bit-shift-left (a64-register base) 5) 16)))))

(defn- a64-kernel-lock
  "The AArch64 lock. There is no CAS below ARMv8.1-LSE, so this is the
  exclusive-monitor pair: LDAXR the word, compare it against the comparand the
  OPERATION fixes, and STLXR the replacement back. STLXR may fail without
  contention -- the monitor is cleared by an interrupt or an unrelated store to
  the same granule -- so a failed store retries. That retry is bounded in the
  only sense that matters here: it re-runs only when the word still held the
  comparand, and a caller that loses the race leaves through `fail` rather than
  spinning. Keeping it inside one selection is the reason this is a lock and
  not a general compare-exchange, which would put the same loop in the guest as
  control flow across basic blocks.

  `clrex` on the mismatch path drops the monitor rather than leaving it set
  across the branch. x17 carries the loaded word and then the store status;
  `dst` carries the replacement and then the result."
  [instruction-index expected desired {:mir/keys [dst] :as instruction}]
  (let [trap (memory-label instruction-index "lock-trap")
        retry (memory-label instruction-index "lock-retry")
        fail (memory-label instruction-index "lock-fail")
        done (memory-label instruction-index "lock-done")]
    (vec (concat
          (a64-kernel-bounds-check trap 32 instruction)
          [(layout/label retry)]
          ;; ldaxr w17, [x16]
          (u32le 0x885ffe11)
          ;; cmp x17, #expected  (LDAXR zero-extends, so the 64-bit form is exact)
          (u32le (bit-or 0xf100001f (bit-shift-left expected 10)
                         (bit-shift-left 17 5)))
          [(layout/relative-branch :aarch64/b-ne-imm19 fail)]
          (a64-constant dst desired)
          ;; stlxr w17, w<dst>, [x16] -- 0x8800fc00 is the bare STLXR word,
          ;; plus Rs=17 at bits 20-16 and Rn=16 at bits 9-5. Checked against
          ;; the assembler rather than derived twice: an earlier hand carry
          ;; produced 0x8910fe00, which decodes as nothing at all.
          (u32le (bit-or 0x8811fe00 (a64-register dst)))
          ;; cmp x17, #0 -- a non-zero status is a failed store, not a lost race
          (u32le (bit-or 0xf100001f (bit-shift-left 17 5)))
          [(layout/relative-branch :aarch64/b-ne-imm19 retry)]
          (a64-constant dst 1)
          [(layout/relative-branch :aarch64/b-imm26 done)
           (layout/label fail)]
          ;; clrex
          (u32le 0xd5033f5f)
          (a64-constant dst 0)
          [(layout/relative-branch :aarch64/b-imm26 done)
           (layout/label trap)]
          (u32le 0xd4200000)
          [(layout/label done)]))))

(defn- a64-kernel-memory
  [instruction-index width store? {:mir/keys [dst stored] :as instruction}]
  (let [trap (memory-label instruction-index "trap")
        done (memory-label instruction-index "done")
        result (if store? stored dst)]
    (vec (concat
          (a64-kernel-bounds-check trap width instruction)
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
        (a64-constant-fixed :aarch64/x16 #?(:clj Long/MIN_VALUE :cljs i64/min-i64))
        ;; cmp left,x16; b.ne divide (+7 instructions)
        (u32le (bit-or 0xeb00001f (bit-shift-left 16 16)
                       (bit-shift-left (a64-register left) 5)))
        (u32le (bit-or 0x54000001 (bit-shift-left 7 5)))
        (a64-constant-fixed :aarch64/x16 -1)
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

(defn- a64-quotient-constant [dst left divisor load-multiplier?]
  (if-let [{:keys [multiplier shift add-numerator? subtract-numerator?]}
           (signed-division-magic divisor)]
    (vec
     (concat
      (when load-multiplier? (a64-constant :aarch64/x16 multiplier))
      ;; smulh x17,left,x16
      (u32le (bit-or 0x9b407c00
                     (bit-shift-left 16 16)
                     (bit-shift-left (a64-register left) 5)
                     17))
      (when add-numerator?
        (u32le (bit-or 0x8b000000
                       (bit-shift-left (a64-register left) 16)
                       (bit-shift-left 17 5) 17)))
      (when subtract-numerator?
        (u32le (bit-or 0xcb000000
                       (bit-shift-left (a64-register left) 16)
                       (bit-shift-left 17 5) 17)))
      ;; asr x17,x17,#shift (SBFM), omitted when the reciprocal needs no shift.
      (when (pos? shift)
        (u32le (bit-or 0x9340fc00
                       (bit-shift-left shift 16)
                       (bit-shift-left 17 5) 17)))
      ;; ADD dst,x17,x17,LSR#63 combines extraction of the sign correction and
      ;; truncation toward zero. x16 therefore keeps the cached multiplier.
      (u32le (bit-or 0x8b400000
                     (bit-shift-left 17 16)
                     (bit-shift-left 63 10)
                     (bit-shift-left 17 5)
                     (a64-register dst)))))
    (vec (concat (a64-constant :aarch64/x17 divisor)
                 (a64-quotient dst left :aarch64/x17)))))

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

(def ^:private x86-page-fault-handler-bytes
  ;; cli; CR2/error-code classification; G/W/X debugcon receipt; deterministic
  ;; isa-debug-exit. The CPU error frame is consumed only for evidence and the
  ;; handler never returns, so this does not pretend to be a general ISR ABI.
  [0xfa 0x41 0x0f 0x20 0xd2 0x4c 0x8b 0x1c 0x24
   0x49 0x81 0xfa 0x00 0x00 0x10 0x00 0x74 0x14
   0x49 0x81 0xfa 0x00 0x10 0x10 0x00 0x74 0x20
   0x49 0x81 0xfa 0x00 0x00 0x11 0x00 0x74 0x2c 0xeb 0x3f
   0x4c 0x89 0xd8 0x83 0xe0 0x03 0x83 0xf8 0x02 0x75 0x34
   0xb0 0x47 0x41 0xb8 0x19 0x00 0x00 0x00 0xeb 0x32
   0x4c 0x89 0xd8 0x83 0xe0 0x03 0x83 0xf8 0x03 0x75 0x1f
   0xb0 0x57 0x41 0xb8 0x1a 0x00 0x00 0x00 0xeb 0x1d
   0x4c 0x89 0xd8 0x83 0xe0 0x11 0x83 0xf8 0x11 0x75 0x0a
   0xb0 0x58 0x41 0xb8 0x1b 0x00 0x00 0x00 0xeb 0x08
   0xb0 0x46 0x41 0xb8 0x1f 0x00 0x00 0x00
   0x66 0xba 0xe9 0x00 0xee 0x44 0x89 0xc0
   0x66 0xba 0xf4 0x00 0xef 0xf4 0xeb 0xfd])

(def ^:private x86-page-fault-recovery-handler-bytes
  [0xfa 0x48 0x89 0x04 0x25 0x10 0x01 0x11 0x00
   0x48 0x89 0x14 0x25 0x18 0x01 0x11 0x00
   0x4c 0x89 0x14 0x25 0x20 0x01 0x11 0x00
   0x4c 0x89 0x1c 0x25 0x28 0x01 0x11 0x00
   0x4c 0x89 0x24 0x25 0x30 0x01 0x11 0x00
   0x4c 0x89 0x2c 0x25 0x38 0x01 0x11 0x00
   0x4c 0x89 0x34 0x25 0x40 0x01 0x11 0x00
   0x49 0x89 0xe6 0x41 0x0f 0x20 0xd2 0x4d 0x8b 0x1e
   0x49 0x81 0xfa 0x00 0x00 0x10 0x00 0x0f 0x85 0x92 0x00 0x00 0x00
   0x4c 0x89 0xd8 0x83 0xe0 0x03 0x83 0xf8 0x02 0x0f 0x85 0x83 0x00 0x00 0x00
   0x4c 0x8b 0x24 0x25 0x00 0x01 0x11 0x00
   0x4c 0x8b 0x2c 0x25 0x08 0x01 0x11 0x00
   0x4d 0x85 0xe4 0x74 0x6e 0x4d 0x85 0xed 0x74 0x69
   0x4d 0x89 0x14 0x24 0x4d 0x89 0x5c 0x24 0x08
   0x49 0x8b 0x46 0x08 0x49 0x89 0x44 0x24 0x10
   0x4c 0x89 0xec 0x49 0x89 0x64 0x24 0x18
   0xb0 0x52 0x66 0xba 0xe9 0x00 0xee
   0x49 0x83 0x46 0x08 0x04 0x4c 0x89 0xf4 0x48 0x83 0xc4 0x08
   0x48 0x8b 0x04 0x25 0x10 0x01 0x11 0x00
   0x48 0x8b 0x14 0x25 0x18 0x01 0x11 0x00
   0x4c 0x8b 0x14 0x25 0x20 0x01 0x11 0x00
   0x4c 0x8b 0x1c 0x25 0x28 0x01 0x11 0x00
   0x4c 0x8b 0x24 0x25 0x30 0x01 0x11 0x00
   0x4c 0x8b 0x2c 0x25 0x38 0x01 0x11 0x00
   0x4c 0x8b 0x34 0x25 0x40 0x01 0x11 0x00
   0x48 0xcf
   0xb0 0x46 0x66 0xba 0xe9 0x00 0xee 0xb8 0x1f 0x00 0x00 0x00
   0x66 0xba 0xf4 0x00 0xef 0xf4 0xeb 0xec])

(def ^:private x86-double-fault-handler-bytes
  ;; The CPU must enter on TSS.IST1. A same-CPL IST switch pushes SS, RSP,
  ;; RFLAGS, CS, RIP, then the architectural zero #DF error code: 48 bytes.
  ;; This handler is deliberately non-returning and validates that exact frame
  ;; position before publishing a distinct machine receipt.
  [0xfa 0x49 0x89 0xe2 0x4c 0x8b 0x1c 0x24
   0x4c 0x8b 0x24 0x25 0x80 0x01 0x11 0x00
   0x4c 0x8b 0x2c 0x25 0x88 0x01 0x11 0x00
   0x4c 0x8b 0x34 0x25 0x90 0x01 0x11 0x00
   0x4d 0x85 0xe4 0x74 0x58 0x4d 0x85 0xed 0x74 0x53
   0x4d 0x85 0xf6 0x74 0x4e 0x4d 0x39 0xea 0x72 0x49
   0x4d 0x39 0xf2 0x73 0x44 0x4d 0x8d 0x7e 0xd0
   0x4d 0x39 0xfa 0x75 0x3b 0x4d 0x85 0xdb 0x75 0x36
   0x4d 0x89 0x14 0x24 0x4d 0x89 0x5c 0x24 0x08
   0x48 0x8b 0x44 0x24 0x20 0x49 0x89 0x44 0x24 0x10
   0x48 0x8b 0x44 0x24 0x28 0x49 0x89 0x44 0x24 0x18
   0x4d 0x89 0x74 0x24 0x20
   0xb0 0x44 0x66 0xba 0xe9 0x00 0xee
   0xb8 0x1c 0x00 0x00 0x00 0x66 0xba 0xf4 0x00 0xef
   0xf4 0xeb 0xfd
   0xb0 0x46 0x66 0xba 0xe9 0x00 0xee
   0xb8 0x1f 0x00 0x00 0x00 0x66 0xba 0xf4 0x00 0xef
   0xf4 0xeb 0xfd])

(def ^:private x86-configure-double-fault-ist
  [0x4c 0x89 0xd0 0x4c 0x09 0xd8 0x48 0xa9 0xff 0x0f 0x00 0x00
   0x75 0x55 0x4d 0x85 0xd2 0x74 0x50 0x4d 0x85 0xdb 0x74 0x4b
   0x4d 0x39 0xda 0x74 0x46
   0x4c 0x89 0x14 0x25 0x80 0x01 0x11 0x00
   0x4c 0x89 0x1c 0x25 0x88 0x01 0x11 0x00
   0x49 0x8d 0x83 0xf0 0x0f 0x00 0x00
   0x48 0x89 0x04 0x25 0x90 0x01 0x11 0x00
   0x4c 0x3b 0x14 0x25 0x80 0x01 0x11 0x00 0x75 0x1d
   0x4c 0x3b 0x1c 0x25 0x88 0x01 0x11 0x00 0x75 0x13
   0x48 0x3b 0x04 0x25 0x90 0x01 0x11 0x00 0x75 0x09
   0x49 0xc7 0xc2 0x01 0x00 0x00 0x00 0xeb 0x03 0x4d 0x31 0xd2])

(def ^:private x86-load-gdt-tss-and-readback
  ;; r10 points at a 10-byte pseudo-descriptor. The new GDT is read back
  ;; exactly before the fixed available-TSS selector 0x18 is loaded and STR
  ;; confirms the task register. Invalid preconditions return zero; a hardware
  ;; contradiction after LGDT traps rather than continuing on ambiguous state.
  [0x49 0x83 0xfb 0x0a 0x75 0x4a 0x4d 0x85 0xd2 0x74 0x45
   0x41 0x0f 0x01 0x12 0x48 0x83 0xec 0x10 0x0f 0x01 0x04 0x24
   0x66 0x41 0x8b 0x02 0x66 0x8b 0x0c 0x24 0x66 0x39 0xc8 0x75 0x31
   0x49 0x8b 0x42 0x02 0x48 0x8b 0x4c 0x24 0x02 0x48 0x39 0xc8 0x75 0x23
   0x48 0x83 0xc4 0x10 0x66 0xb8 0x18 0x00 0x0f 0x00 0xd8
   0x66 0x0f 0x00 0xc8 0x66 0x83 0xf8 0x18 0x75 0x12
   0x49 0xc7 0xc2 0x01 0x00 0x00 0x00 0xeb 0x0b
   0x4d 0x31 0xd2 0xeb 0x06 0x48 0x83 0xc4 0x10 0x0f 0x0b])

(def ^:private x86-configure-page-fault-recovery
  [0x4c 0x89 0xd0 0x4c 0x09 0xd8 0x48 0xa9 0xff 0x0f 0x00 0x00
   0x75 0x43 0x4d 0x85 0xd2 0x74 0x3e 0x4d 0x85 0xdb 0x74 0x39
   0x4d 0x39 0xd3 0x74 0x34 0x4c 0x89 0x14 0x25 0x00 0x01 0x11 0x00
   0x49 0x8d 0x83 0xf0 0x0f 0x00 0x00 0x48 0x89 0x04 0x25 0x08 0x01 0x11 0x00
   0x4c 0x3b 0x14 0x25 0x00 0x01 0x11 0x00 0x75 0x13
   0x48 0x3b 0x04 0x25 0x08 0x01 0x11 0x00 0x75 0x09
   0x49 0xc7 0xc2 0x01 0x00 0x00 0x00 0xeb 0x03 0x4d 0x31 0xd2])

(defn- x86-page-fault-handler-address [dst]
  (let [n (count x86-page-fault-handler-bytes)]
    (vec (concat [0xe9] (u32le n)
                 x86-page-fault-handler-bytes
                 ;; Handler starts immediately after the five-byte jump. RIP
                 ;; after this LEA is handler-start + n + 7.
                 [0x4c 0x8d 0x15] (u32le (- (+ n 7)))
                 (when-not (= dst :x86-64/r10)
                   (x86-rr 0x89 dst :x86-64/r10))))))

(defn- x86-page-fault-recovery-handler-address [dst]
  (let [n (count x86-page-fault-recovery-handler-bytes)]
    (vec (concat [0xe9] (u32le n)
                 x86-page-fault-recovery-handler-bytes
                 [0x4c 0x8d 0x15] (u32le (- (+ n 7)))
                 (when-not (= dst :x86-64/r10)
                   (x86-rr 0x89 dst :x86-64/r10))))))

(defn- x86-double-fault-handler-address [dst]
  (let [n (count x86-double-fault-handler-bytes)]
    (vec (concat [0xe9] (u32le n)
                 x86-double-fault-handler-bytes
                 [0x4c 0x8d 0x15] (u32le (- (+ n 7)))
                 (when-not (= dst :x86-64/r10)
                   (x86-rr 0x89 dst :x86-64/r10))))))

(def ^:private x86-load-idt-and-readback
  ;; r10 = pointer to the 10-byte pseudo-descriptor, r11 = declared length.
  ;; LIDT is immediately followed by SIDT and exact limit/base comparison.
  [0x49 0x83 0xfb 0x0a 0x75 0x38 0x4d 0x85 0xd2 0x74 0x33
   0x41 0x0f 0x01 0x1a 0x48 0x83 0xec 0x10 0x0f 0x01 0x0c 0x24
   0x41 0x0f 0xb7 0x02 0x0f 0xb7 0x0c 0x24 0x39 0xc8 0x75 0x1b
   0x49 0x8b 0x42 0x02 0x48 0x8b 0x4c 0x24 0x02 0x48 0x39 0xc8 0x75 0x0d
   0x48 0x83 0xc4 0x10 0x49 0xc7 0xc2 0x01 0x00 0x00 0x00 0xeb 0x02
   0x0f 0x0b])

(defn- x86-privileged
  [{:mir/keys [dst action arguments] :as instruction}]
  (let [copy-to (fn [register value]
                  (if (= register value) [] (x86-rr 0x89 register value)))
        finish (fn [bytes result]
                 (vec (concat bytes (copy-to dst result))))
        [a b] arguments]
    (case action
      :boot-info
      (finish [0x4d 0x8b 0x51 0x50] :x86-64/r10)
      :read-cr0
      (finish [0x41 0x0f 0x20 0xc2] :x86-64/r10)
      :write-cr0
      (finish (concat (copy-to :x86-64/r10 a)
                      [0x41 0x0f 0x22 0xc2])
              :x86-64/r10)
      :read-cr2
      (finish [0x41 0x0f 0x20 0xd2] :x86-64/r10)
      :read-cr3
      (finish [0x41 0x0f 0x20 0xda] :x86-64/r10)
      :write-cr3
      (finish (concat (copy-to :x86-64/r10 a)
                      [0x41 0x0f 0x22 0xda])
              :x86-64/r10)
      :invlpg
      (finish (concat (copy-to :x86-64/r10 a)
                      [0x41 0x0f 0x01 0x3a])
              :x86-64/r10)
      :read-cs
      (finish [0x4d 0x31 0xd2 0x66 0x41 0x8c 0xca] :x86-64/r10)
      :page-fault-handler-address
      (x86-page-fault-handler-address dst)
      :page-fault-recovery-handler-address
      (x86-page-fault-recovery-handler-address dst)
      :configure-page-fault-recovery
      (finish (concat (copy-to :x86-64/r10 a)
                      (copy-to :x86-64/r11 b)
                      x86-configure-page-fault-recovery)
              :x86-64/r10)
      :double-fault-handler-address
      (x86-double-fault-handler-address dst)
      :configure-double-fault-ist
      (finish (concat (copy-to :x86-64/r10 a)
                      (copy-to :x86-64/r11 b)
                      x86-configure-double-fault-ist)
              :x86-64/r10)
      :load-gdt-tss
      (finish (concat (copy-to :x86-64/r10 a)
                      (copy-to :x86-64/r11 b)
                      x86-load-gdt-tss-and-readback)
              :x86-64/r10)
      :load-idt
      (finish (concat (copy-to :x86-64/r10 a)
                      (copy-to :x86-64/r11 b)
                      x86-load-idt-and-readback)
              :x86-64/r10)
      :probe-guard-write
      (finish [0xc6 0x04 0x25 0x00 0x00 0x10 0x00 0x00] :x86-64/r10)
      :probe-text-write
      (finish [0xc6 0x04 0x25 0x00 0x10 0x10 0x00 0x00] :x86-64/r10)
      :probe-nx-execute
      (finish [0x49 0xba 0x00 0x00 0x11 0x00 0x00 0x00 0x00 0x00
               0x41 0xff 0xd2] :x86-64/r10)
      :probe-recoverable-guard-write
      (finish [0x49 0xc7 0xc2 0x00 0x00 0x10 0x00 0x41 0xc6 0x02 0x00
               0x4d 0x31 0xd2]
              :x86-64/r10)
      :probe-double-fault
      (finish [0x41 0xbb 0x00 0x00 0x10 0x00 0x41 0xc6 0x03 0x00
               0x4d 0x31 0xd2]
              :x86-64/r10)
      (:cli :sti :hlt :pause)
      (finish (concat (case action
                        :cli [0xfa] :sti [0xfb] :hlt [0xf4] :pause [0xf3 0x90])
                      (x86-mov-imm :x86-64/r10 0))
              :x86-64/r10)
      (:out-u8 :out-u32)
      (finish
       (concat (copy-to :x86-64/r10 a)
               (copy-to :x86-64/r11 b)
               (x86-push :x86-64/rax) (x86-push :x86-64/rdx)
               (x86-rr 0x89 :x86-64/rdx :x86-64/r10)
               (x86-rr 0x89 :x86-64/rax :x86-64/r11)
               [(if (= action :out-u8) 0xee 0xef)]
               (x86-pop :x86-64/rdx) (x86-pop :x86-64/rax))
       :x86-64/r11)
      (:in-u8 :in-u32)
      (finish
       (concat (copy-to :x86-64/r10 a)
               (x86-push :x86-64/rax) (x86-push :x86-64/rdx)
               (x86-rr 0x89 :x86-64/rdx :x86-64/r10)
               (when (= action :in-u8) [0x31 0xc0])
               [(if (= action :in-u8) 0xec 0xed)]
               (x86-rr 0x89 :x86-64/r11 :x86-64/rax)
               (x86-pop :x86-64/rdx) (x86-pop :x86-64/rax))
       :x86-64/r11)
      :read-msr
      (finish
       (concat (copy-to :x86-64/r10 a)
               (x86-push :x86-64/rax) (x86-push :x86-64/rcx)
               (x86-push :x86-64/rdx)
               (x86-rr 0x89 :x86-64/rcx :x86-64/r10)
               [0x0f 0x32]
               (x86-rr 0x89 :x86-64/r11 :x86-64/rdx)
               [0x49 0xc1 0xe3 0x20]
               (x86-rr 0x09 :x86-64/r11 :x86-64/rax)
               (x86-pop :x86-64/rdx) (x86-pop :x86-64/rcx)
               (x86-pop :x86-64/rax))
       :x86-64/r11)
      :write-msr
      (finish
       (concat (copy-to :x86-64/r10 a)
               (copy-to :x86-64/r11 b)
               (x86-push :x86-64/rax) (x86-push :x86-64/rcx)
               (x86-push :x86-64/rdx)
               (x86-rr 0x89 :x86-64/rcx :x86-64/r10)
               (x86-rr 0x89 :x86-64/rax :x86-64/r11)
               (x86-rr 0x89 :x86-64/rdx :x86-64/r11)
               [0x48 0xc1 0xea 0x20 0x0f 0x30]
               (x86-pop :x86-64/rdx) (x86-pop :x86-64/rcx)
               (x86-pop :x86-64/rax))
       :x86-64/r11)
      (:cpuid-eax :cpuid-ebx :cpuid-ecx :cpuid-edx)
      (finish
       (concat (copy-to :x86-64/r10 a)
               (copy-to :x86-64/r11 b)
               (x86-push :x86-64/rax) (x86-push :x86-64/rbx)
               (x86-push :x86-64/rcx) (x86-push :x86-64/rdx)
               (x86-rr 0x89 :x86-64/rax :x86-64/r10)
               (x86-rr 0x89 :x86-64/rcx :x86-64/r11)
               [0x0f 0xa2]
               (case action
                 :cpuid-eax [0x41 0x89 0xc2]
                 :cpuid-ebx [0x41 0x89 0xda]
                 :cpuid-ecx [0x41 0x89 0xca]
                 :cpuid-edx [0x41 0x89 0xd2])
               (x86-pop :x86-64/rdx) (x86-pop :x86-64/rcx)
               (x86-pop :x86-64/rbx) (x86-pop :x86-64/rax))
       :x86-64/r10)
      (reject! :mc-encode :unknown-x86-privileged-action instruction))))

(defn- encode-selected
  [isa frame-bytes return-suffix instruction-index load-a64-multiplier?
   {:mc/keys [encoding] :as instruction}]
  (case encoding
    :x86-64/argument
    (let [dst (:mir/dst instruction)
          src (get x86-arguments (:mir/index instruction))]
      (when-not src (reject! :mc-encode :argument-index-unsupported instruction))
      (if (= dst src) [] (x86-rr 0x89 dst src)))
    :x86-64/constant (x86-mov-imm (:mir/dst instruction) (:mir/value instruction))
    :x86-64/data-address
    [{:native/data-content (:mir/content instruction)
      :native/data-dst (:mir/dst instruction) :native/data-target :x86-64}]
    :x86-64/add
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (if-let [immediate (:native/x86-immediate instruction)]
        (or (when-not (= dst left) (x86-lea-disp32 dst left immediate))
            (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                         (x86-alu-imm 0 dst immediate))))
        (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                     (x86-rr 0x01 dst right)))))
    :x86-64/subtract
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (if-let [immediate (:native/x86-immediate instruction)]
        (or (when (and (not= dst left) (x86-negatable-imm32? immediate))
              (x86-lea-disp32 dst left (- immediate)))
            (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                         (x86-alu-imm 5 dst immediate))))
        (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                     (x86-rr 0x29 dst right)))))
    :x86-64/multiply
    (let [dst (:mir/dst instruction) left (:mir/left instruction) right (:mir/right instruction)]
      (if-let [immediate (:native/x86-immediate instruction)]
        ;; Three-operand imul reads `left` and writes `dst` in one instruction,
        ;; so unlike add and sub it needs no move even when they differ.
        (x86-imul-imm dst left immediate)
        (vec (concat (when-not (= dst left) (x86-rr 0x89 dst left))
                     (x86-rr-two-byte 0xaf dst right)))))
    :x86-64/quotient
    (x86-quotient (:mir/dst instruction) (:mir/left instruction)
                  (:mir/right instruction))
    :x86-64/quotient-constant
    (x86-quotient-constant (:mir/dst instruction) (:mir/left instruction)
                           (:mir/divisor instruction)
                           (:native/x86-reciprocal-live instruction)
                           (:native/x86-result-in-r11 instruction))
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
    ;; Acquire moves the word 0 -> 1; release moves it 1 -> 0. The comparand
    ;; and the replacement are the operation's, not the guest's.
    :x86-64/kernel-try-lock-u32 (x86-kernel-lock instruction-index 0 1 instruction)
    :x86-64/kernel-unlock-u32 (x86-kernel-lock instruction-index 1 0 instruction)
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
    :x86-64/x86-privileged (x86-privileged instruction)
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
    :aarch64/data-address
    [{:native/data-content (:mir/content instruction)
      :native/data-dst (:mir/dst instruction) :native/data-target :aarch64}]
    :aarch64/add
    (if-let [immediate (:native/a64-immediate instruction)]
      (u32le (bit-or (if (= :subtract (:native/a64-immediate-op instruction))
                       0xd1000000 0x91000000)
                     (bit-shift-left (:native/a64-immediate-shift instruction) 22)
                     (bit-shift-left immediate 10)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction))))
      (u32le (bit-or 0x8b000000
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
    (:aarch64/multiply-add :aarch64/multiply-subtract)
    ;; Two independent features meet on this case. The Mersenne reduction
    ;; changes what a multiply-add/subtract emits when the multiplier is
    ;; 2^shift-1; the corpus immediate folding gave `:aarch64/subtract` a case
    ;; of its own. They compose: the Mersenne test is on the fused encodings,
    ;; the immediate test is on the plain subtract, and neither reads the
    ;; other's instruction key.
    (if-let [shift (:native/a64-mersenne-shift instruction)]
      (let [factor (a64-register (:native/a64-mersenne-factor instruction))
            addend (a64-register (:mir/addend instruction))
            dst (a64-register (:mir/dst instruction))]
        (vec
         (concat
          ;; x17 = factor - (factor << shift) = -factor*(2^shift-1)
          (u32le (bit-or 0xcb000000 (bit-shift-left factor 16)
                         (bit-shift-left shift 10)
                         (bit-shift-left factor 5) 17))
          ;; dst = addend - factor*(2^shift-1)
          (u32le (bit-or 0x8b000000 (bit-shift-left 17 16)
                         (bit-shift-left addend 5) dst)))))
      (u32le (bit-or (if (= :aarch64/multiply-add encoding)
                       0x9b000000 0x9b008000)
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/addend instruction)) 10)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
    :aarch64/subtract
    (if-let [immediate (:native/a64-immediate instruction)]
      (u32le (bit-or (if (= :add (:native/a64-immediate-op instruction))
                       0x91000000 0xd1000000)
                     (bit-shift-left (:native/a64-immediate-shift instruction) 22)
                     (bit-shift-left immediate 10)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction))))
      (u32le (bit-or 0xcb000000
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
    (:aarch64/multiply
     :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor
     :aarch64/shift-left :aarch64/shift-right-signed
     :aarch64/shift-right-unsigned)
    (let [base (case encoding
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
    :aarch64/quotient-constant
    (a64-quotient-constant (:mir/dst instruction) (:mir/left instruction)
                           (:mir/divisor instruction)
                           load-a64-multiplier?)
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
    :aarch64/kernel-try-lock-u32 (a64-kernel-lock instruction-index 0 1 instruction)
    :aarch64/kernel-unlock-u32 (a64-kernel-lock instruction-index 1 0 instruction)
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
    :aarch64/cbnz-imm19
    (u32le (bit-or 0xb5000000
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)
                   (first operands)))
    :aarch64/b-hi-imm19
    (u32le (bit-or 0x54000008
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))
    :aarch64/b-hs-imm19
    (u32le (bit-or 0x54000002
                   (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)))
    ;; B.NE, cond 0001. The legacy `kotoba.native.aarch64` emitter has carried
    ;; this branch for a long time; this table had never needed it, because
    ;; nothing in production MIR branched on inequality until the lock did.
    :aarch64/b-ne-imm19
    (u32le (bit-or 0x54000001
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
      (when (:native/data-content token)
        (case (:native/data-target token) :x86-64 10 :aarch64 16 nil))
      (when (and (integer? token) (<= 0 token 255)) 1)))

(defn- resolve-program-layout [tokens]
  (let [labels (layout/label-offsets tokens size-of-token)
        code-size (reduce + 0 (keep size-of-token tokens))
        contents (distinct (keep :native/data-content tokens))
        data-offsets (loop [remaining (seq contents), offset code-size, out {}]
                       (if-let [content (first remaining)]
                         (recur (next remaining)
                                (+ offset (count (utf8-bytes content)))
                                (assoc out content offset))
                         out))
        code (layout/resolve-tokens
              tokens size-of-token labels encode-layout-branch
              (fn [token _]
                (if-let [content (:native/data-content token)]
                  (let [offset (get data-offsets content)]
                    (case (:native/data-target token)
                      :x86-64 (x86-mov-imm-fixed (:native/data-dst token) offset)
                      :aarch64 (a64-constant-fixed (:native/data-dst token) offset)))
                  [token])))
        data (vec (mapcat utf8-bytes contents))]
    {:code (vec (concat code data)) :code-size code-size :labels labels}))

(defn- resolve-layout [tokens]
  (:code (resolve-program-layout tokens)))

(def ^:private a64-leaf-constant-registers
  [:aarch64/x13 :aarch64/x14 :aarch64/x15])

(def ^:private a64-leaf-cache-safe-encodings
  ;; Keep this closed: checked-memory and host-boundary encoders have their own
  ;; private scratch conventions and must opt in only after proving x13-x15
  ;; preservation.
  #{:aarch64/argument :aarch64/constant :aarch64/data-address
    :aarch64/add :aarch64/subtract :aarch64/multiply
    :aarch64/multiply-add :aarch64/multiply-subtract
    :aarch64/quotient :aarch64/quotient-constant
    :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor
    :aarch64/shift-left :aarch64/shift-right-signed
    :aarch64/shift-right-unsigned
    :aarch64/f64-add :aarch64/f64-subtract :aarch64/f64-multiply
    :aarch64/f64-divide :aarch64/f64-min :aarch64/f64-max
    :aarch64/f64-sqrt :aarch64/f64-equal :aarch64/f64-less-than
    :aarch64/f64-less-or-equal :aarch64/f64-greater-than
    :aarch64/f64-greater-or-equal :aarch64/f64-unordered
    :aarch64/equal :aarch64/less-than :aarch64/greater-than
    :aarch64/less-or-equal :aarch64/greater-or-equal
    :aarch64/spill-load :aarch64/spill-store :aarch64/move :aarch64/return})

(defn- a64-cache-register-sources [instruction aliases]
  (reduce
   (fn [out key]
     (if-not (contains? out key)
       out
       (update out key
               (fn [value]
                 (if (vector? value)
                   (mapv #(get aliases % %) value)
                   (get aliases value value))))))
   instruction
   [:mir/test :mir/value :mir/src :mir/input :mir/left :mir/right :mir/addend
    :mir/base :mir/length :mir/index :mir/stored :mir/offset :mir/size
    :mir/arguments]))

(defn- positive-mersenne-shift [value]
  (let [candidate (+ (->wide value) wide-one)
        two (+ wide-one wide-one)]
    (when (> candidate wide-one)
      (loop [remaining candidate, shift 0]
        (cond
          (= remaining wide-one) (when (<= 1 shift 63) shift)
          (= wide-zero (wide-mod remaining two))
          (recur (wide-quot remaining two) (inc shift))
          :else nil)))))

(defn- a64-strength-reduce-cached-mersenne [instruction cache]
  (if-not (= :aarch64/multiply-subtract (:mc/encoding instruction))
    instruction
    (let [cached-values (into {} (map (fn [[value register]] [register value]) cache))
          factor (cond
                   (contains? cached-values (:mir/left instruction))
                   (:mir/right instruction)
                   (contains? cached-values (:mir/right instruction))
                   (:mir/left instruction))
          constant-register (cond
                              (contains? cached-values (:mir/left instruction))
                              (:mir/left instruction)
                              (contains? cached-values (:mir/right instruction))
                              (:mir/right instruction))
          shift (some-> constant-register cached-values positive-mersenne-shift)]
      (if shift
        (assoc instruction
               :native/a64-mersenne-shift shift
               :native/a64-mersenne-factor factor)
        instruction))))

(def ^:private a64-source-keys
  [:mir/test :mir/value :mir/src :mir/input :mir/left :mir/right :mir/addend
   :mir/base :mir/length :mir/index :mir/stored :mir/offset :mir/size
   :mir/arguments])

(defn- a64-source-registers [instruction]
  (mapcat (fn [key]
            (let [value (get instruction key)]
              (cond (vector? value) value
                    (keyword? value) [value]
                    :else [])))
          a64-source-keys))

(defn- a64-add-sub-immediate [op value]
  (let [value (->wide value)
        negative? (wide-neg? value)
        magnitude (if negative? (- value) value)
        [immediate shift]
        (cond
          (<= magnitude #?(:clj 4095N :cljs (js/BigInt 4095)))
          [magnitude 0]
          (and (= wide-zero
                  (wide-mod magnitude #?(:clj 4096N :cljs (js/BigInt 4096))))
               (<= (wide-quot magnitude #?(:clj 4096N :cljs (js/BigInt 4096)))
                   #?(:clj 4095N :cljs (js/BigInt 4095))))
          [(wide-quot magnitude #?(:clj 4096N :cljs (js/BigInt 4096))) 1]
          :else nil)]
    (when immediate
      {:op (case [op negative?]
             [:aarch64/add false] :add
             [:aarch64/add true] :subtract
             [:aarch64/subtract false] :subtract
             [:aarch64/subtract true] :add)
       :immediate #?(:clj (int immediate) :cljs (js/Number immediate))
       :shift shift})))

(defn- a64-fold-adjacent-add-sub-immediates [instructions]
  (letfn [(uses-before-redefinition [instructions register]
            (loop [remaining instructions, uses 0]
              (if-let [instruction (first remaining)]
                (let [uses (+ uses (count (filter #{register}
                                                  (a64-source-registers instruction))))]
                  (if (= register (:mir/dst instruction))
                    uses
                    (recur (next remaining) uses)))
                uses)))]
    (loop [remaining instructions, out []]
      (if-let [constant (first remaining)]
        (let [consumer (second remaining)
              register (:mir/dst constant)
              op (:mc/encoding consumer)
              constant? (= :aarch64/constant (:mc/encoding constant))
              operand
              (cond
                (and (= op :aarch64/add) (= register (:mir/right consumer)))
                (:mir/left consumer)
                (and (= op :aarch64/add) (= register (:mir/left consumer)))
                (:mir/right consumer)
                (and (= op :aarch64/subtract) (= register (:mir/right consumer)))
                (:mir/left consumer))
              selected (when (and constant? operand
                                  (= 1 (uses-before-redefinition
                                        (next remaining) register)))
                         (a64-add-sub-immediate op (:mir/value constant)))]
          (if selected
            (recur (nnext remaining)
                   (conj out (assoc consumer
                                    :mir/left operand
                                    :native/a64-immediate-op (:op selected)
                                    :native/a64-immediate (:immediate selected)
                                    :native/a64-immediate-shift (:shift selected))))
            (recur (next remaining) (conj out constant))))
        (vec out)))))

;; A Mersenne-reduced multiply-subtract no longer reads its `:mir/left` and
;; `:mir/right`; it reads the factor register the reduction recorded. Reporting
;; the pre-reduction operands here would keep a constant register alive that
;; nothing loads any more, and the cache would refuse a slot it could have used.
(defn- a64-used-source-registers [instructions]
  (set
   (mapcat (fn [instruction]
             (let [keys (cond-> a64-source-keys
                          (:native/a64-mersenne-shift instruction)
                          (->> (remove #{:mir/left :mir/right})))]
               (concat
                (when-let [factor (:native/a64-mersenne-factor instruction)] [factor])
                (mapcat (fn [key]
                       (let [value (get instruction key)]
                         (cond (vector? value) value
                               (keyword? value) [value]
                               :else [])))
                        keys))))
           instructions)))

;; The x86-64 sibling of `a64-fold-adjacent-add-sub-immediates`, extended to
;; multiply because x86-64 has a three-operand `imul r64,r64,imm32` where
;; AArch64 does not. Same shape and same safety condition: a constant may fold
;; into the instruction that follows it only when that instruction is its one
;; and only reader before the register is written again. Anything else — the
;; register read twice, read later, or never — leaves both instructions alone.
;; Once a constant is folded, the instruction that carries it reads its source
;; through a form that accepts any register: three-operand `imul r64,r64,imm32`
;; and `lea r64,[r64+disp32]` both name their source explicitly rather than
;; operating in place. A copy feeding such an instruction is therefore
;; redundant — `mov rcx,r11` then `imul r8,rcx,M` is `imul r8,r11,M`.
;;
;; The safety condition is the one the immediate folding already uses: the
;; copy's destination must be read exactly once before it is written again. If
;; anything else reads it, or reads it later, the copy is doing work and stays.
;;
;; Restricted to instructions that carry an immediate on purpose. Without one,
;; add and subtract lower in place and genuinely need the copy; propagating
;; into them would change which register the result lands in.
;; A constant division leaves its answer in R11 and then moves it to whatever
;; `dst` the allocator chose. That move sits on the dependency chain — the next
;; instruction cannot start until it retires — and it is unnecessary whenever
;; the reader is a form that names its source explicitly, which the folded
;; three-operand shapes all are.
;;
;; So: when the division's destination is read exactly once, by the instruction
;; immediately after it, in a slot that accepts any register, the reader is
;; pointed at R11 and the division is told to skip its move. R11 is outside the
;; allocator's four registers, and the reader writes its own `dst`, so nothing
;; can be holding R11 across the gap.
(defn- x86-quotient-result-in-place [instructions]
  (letfn [(uses-before-redefinition [instructions register]
            (loop [remaining instructions, uses 0]
              (if-let [instruction (first remaining)]
                (let [uses (+ uses (count (filter #{register}
                                                  (a64-source-registers instruction))))]
                  (if (= register (:mir/dst instruction))
                    uses
                    (recur (next remaining) uses)))
                uses)))]
    (loop [remaining instructions, out []]
      (if-let [division (first remaining)]
        (let [reader (second remaining)
              produced (:mir/dst division)
              slot (cond (= produced (:mir/left reader)) :mir/left
                         (= produced (:mir/right reader)) :mir/right)
              in-place?
              (and (= :x86-64/quotient-constant (:mc/encoding division))
                   (not= :x86-64/r11 produced)
                   (contains? #{:x86-64/multiply :x86-64/add :x86-64/subtract}
                              (:mc/encoding reader))
                   (some? (:native/x86-immediate reader))
                   ;; only `left` is a free source slot on the folded forms;
                   ;; `right` is the operand the immediate replaced and is not read
                   (= :mir/left slot)
                   (not= :x86-64/r11 (:mir/dst reader))
                   (= 1 (uses-before-redefinition (next remaining) produced)))]
          (if in-place?
            (recur (nnext remaining)
                   (conj out
                         (assoc division :native/x86-result-in-r11 true)
                         (assoc reader :mir/left :x86-64/r11)))
            (recur (next remaining) (conj out division))))
        (vec out)))))

(def ^:private x86-reciprocal-cache-safe-encodings
  ;; Closed on purpose, the way `a64-leaf-cache-safe-encodings` is closed. R10
  ;; survives from one constant division to the next only across encodings that
  ;; are known not to write it. Measured on this file: the only emitters that
  ;; touch R10 are `x86-quotient-constant` itself, `x86-privileged`, the
  ;; kernel-memory pair and the fault-handler addresses — none of which are
  ;; listed here, and an encoding nobody has checked is not listed either, so a
  ;; sequence containing one simply does not qualify.
  #{:x86-64/argument :x86-64/constant :x86-64/move
    :x86-64/add :x86-64/subtract :x86-64/multiply
    :x86-64/quotient-constant :x86-64/return
    :x86-64/bit-and :x86-64/bit-or :x86-64/bit-xor
    :x86-64/equal :x86-64/less-than :x86-64/less-or-equal
    :x86-64/greater-than :x86-64/greater-or-equal})

;; Every constant division by the same divisor loads the same ten-byte
;; reciprocal into R10. Loading it once is worth seven of those ten-byte loads
;; on a kernel that divides eight times, and costs nothing: R10 is outside the
;; allocator's four registers, and the sign correction that used to borrow it
;; now borrows RDX, which is dead at that point in every branch and is restored
;; by the pop regardless.
;;
;; Only in a straight-line run of qualifying encodings, and only for divisions
;; after the first with that exact divisor. A branch would let control reach the
;; second division without passing the first.
(defn- x86-hoist-repeated-reciprocal [instructions]
  (if-not (every? #(contains? x86-reciprocal-cache-safe-encodings (:mc/encoding %))
                  instructions)
    instructions
    (first
     (reduce (fn [[out loaded] instruction]
               (if (= :x86-64/quotient-constant (:mc/encoding instruction))
                 (let [divisor (:mir/divisor instruction)]
                   (if (contains? loaded divisor)
                     [(conj out (assoc instruction :native/x86-reciprocal-live true))
                      loaded]
                     [(conj out instruction) (conj loaded divisor)]))
                 [(conj out instruction) loaded]))
             [[] #{}]
             instructions))))

(defn- x86-propagate-copies [instructions]
  (letfn [(uses-before-redefinition [instructions register]
            (loop [remaining instructions, uses 0]
              (if-let [instruction (first remaining)]
                (let [uses (+ uses (count (filter #{register}
                                                  (a64-source-registers instruction))))]
                  (if (= register (:mir/dst instruction))
                    uses
                    (recur (next remaining) uses)))
                uses)))]
    (loop [remaining instructions, out []]
      (if-let [copy (first remaining)]
        (let [consumer (second remaining)
              copied (:mir/dst copy)
              propagable? (and (= :x86-64/move (:mc/encoding copy))
                               (some? (:mir/src copy))
                               (contains? #{:x86-64/multiply :x86-64/add :x86-64/subtract}
                                          (:mc/encoding consumer))
                               (some? (:native/x86-immediate consumer))
                               (= copied (:mir/left consumer))
                               (= 1 (uses-before-redefinition (next remaining) copied)))]
          (if propagable?
            (recur (nnext remaining)
                   (conj out (assoc consumer :mir/left (:mir/src copy))))
            (recur (next remaining) (conj out copy))))
        (vec out)))))

(defn- x86-fold-adjacent-immediates [instructions]
  (letfn [(uses-before-redefinition [instructions register]
            (loop [remaining instructions, uses 0]
              (if-let [instruction (first remaining)]
                (let [uses (+ uses (count (filter #{register}
                                                  (a64-source-registers instruction))))]
                  (if (= register (:mir/dst instruction))
                    uses
                    (recur (next remaining) uses)))
                uses)))]
    (loop [remaining instructions, out []]
      (if-let [constant (first remaining)]
        (let [consumer (second remaining)
              register (:mir/dst constant)
              op (:mc/encoding consumer)
              constant? (= :x86-64/constant (:mc/encoding constant))
              ;; `operand` is what survives as the instruction's own source once
              ;; the constant is gone. Subtraction is not commutative, so only a
              ;; constant on the right may fold; add and multiply take either.
              operand
              (cond
                (and (#{:x86-64/add :x86-64/multiply} op) (= register (:mir/right consumer)))
                (:mir/left consumer)
                (and (#{:x86-64/add :x86-64/multiply} op) (= register (:mir/left consumer)))
                (:mir/right consumer)
                (and (= op :x86-64/subtract) (= register (:mir/right consumer)))
                (:mir/left consumer))
              foldable? (and constant?
                             operand
                             (x86-imm32? (:mir/value constant))
                             (= 1 (uses-before-redefinition (next remaining) register)))]
          (if foldable?
            (recur (nnext remaining)
                   (conj out (assoc consumer
                                    :mir/left operand
                                    :native/x86-immediate (:mir/value constant))))
            (recur (next remaining) (conj out constant))))
        (vec out)))))

(defn- a64-cache-leaf-constants [instructions]
  ;; The cache registers are caller-saved. Restrict the transform to one
  ;; branchless leaf so no call or alternate entry can invalidate their value.
  (if-not
   (every? (fn [{:mc/keys [op encoding]}]
             (and (= :mc/instruction op)
                  (contains? a64-leaf-cache-safe-encodings encoding)
                  (not (contains? #{"call" "tail-call"} (name encoding)))))
           instructions)
    instructions
    (let [occurrences
          (reduce (fn [out [index {:mc/keys [encoding] :as instruction}]]
                    (if (= :aarch64/constant encoding)
                      (update out (:mir/value instruction) (fnil conj []) index)
                      out))
                  {} (map-indexed vector instructions))
          selected (->> occurrences
                        (keep (fn [[value indexes]]
                                (when (> (count indexes) 1)
                                  {:value value :first (first indexes)
                                   :saving (* (dec (count indexes))
                                              (count (a64-constant
                                                      :aarch64/x13 value)))})))
                        (sort-by (juxt (comp - :saving) :first))
                        (take (count a64-leaf-constant-registers)))
          cache (into {} (map (fn [{:keys [value]} register]
                                [value register])
                              selected a64-leaf-constant-registers))
          rewritten
          (:out
           (reduce
            (fn [{:keys [aliases loaded out]} {:mc/keys [encoding] :as instruction}]
              (if (and (= :aarch64/constant encoding)
                       (contains? cache (:mir/value instruction)))
                (let [value (:mir/value instruction)
                      register (get cache value)
                      emitted (if (contains? loaded value)
                                out
                                (conj out (assoc instruction :mir/dst register)))]
                  {:aliases (assoc aliases (:mir/dst instruction) register)
                   :loaded (conj loaded value)
                   :out emitted})
                (let [rewritten (-> instruction
                                    (a64-cache-register-sources aliases)
                                    (a64-strength-reduce-cached-mersenne cache))
                      dst (:mir/dst instruction)]
                  {:aliases (if dst (dissoc aliases dst) aliases)
                   :loaded loaded
                   :out (conj out rewritten)})))
            {:aliases {} :loaded #{} :out []}
            instructions))
          used (a64-used-source-registers rewritten)
          cache-registers (set (vals cache))]
      (vec (remove #(and (= :aarch64/constant (:mc/encoding %))
                         (contains? cache-registers (:mir/dst %))
                         (not (contains? used (:mir/dst %))))
                   rewritten)))))

(def ^:private a64-x16-preserving-encodings
  #{:aarch64/argument :aarch64/constant :aarch64/data-address
    :aarch64/add :aarch64/subtract :aarch64/multiply
    :aarch64/multiply-add :aarch64/multiply-subtract
    :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor
    :aarch64/shift-left :aarch64/shift-right-signed
    :aarch64/shift-right-unsigned :aarch64/spill-load
    :aarch64/spill-store :aarch64/move :aarch64/return})

(defn- rename-token-labels
  "Give every label defined inside TOKENS a private namespace and retarget its
  internal branches.  Fuel prefixes contain local success labels; a self-tail
  re-entry needs a second copy of the prefix, and duplicate labels would make
  final layout ambiguous."
  [scope tokens]
  (let [labels (->> tokens (filter layout/label-token?) (map :mir/id) set)
        renamed (into {} (map (fn [id]
                                [id (keyword (str "kotoba.native." scope)
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

(defn- instruction-tokens
  [isa frame-bytes return-suffix tail-suffix callee-labels
   self-tail-prefix self-tail-body instructions]
  (let [instructions (case isa
                       :aarch64 (-> instructions
                                    a64-cache-leaf-constants
                                    ;; Unique-use mul+add becomes MADD. A product
                                    ;; reused by several constant adds (CSE of
                                    ;; `(n+k)*C`) stays MUL; fusing it would drop
                                    ;; the multiply while later adds still read it.
                                    a64-fuse-multiplies
                                    a64-fold-adjacent-add-sub-immediates)
                       :x86-64 (-> instructions
                                 x86-fold-adjacent-immediates
                                 x86-propagate-copies
                                 x86-quotient-result-in-place
                                 x86-hoist-repeated-reciprocal)
                       instructions)]
    (:out
     (reduce
      (fn [{:keys [out cached-a64-multiplier]}
           [instruction-index {:mc/keys [op test encoding] :as instruction}]]
        (let [magic (when (and (= isa :aarch64)
                               (= encoding :aarch64/quotient-constant))
                      (signed-division-magic (:mir/divisor instruction)))
              multiplier (:multiplier magic)
              load-multiplier? (not= multiplier cached-a64-multiplier)
              tokens
      (if (layout/label-token? instruction)
        [instruction]
        (case op
          :mc/reentry
          [(layout/label self-tail-body)]

          :mc/recur
          (concat (rename-token-labels (str "self-tail." instruction-index)
                                       self-tail-prefix)
                  [(layout/relative-branch :aarch64/b-imm26 self-tail-body)])

          :mc/instruction
          (if (contains? #{"call" "tail-call"}
                         (name (:mc/encoding instruction)))
            (let [callee (:mir/callee instruction)
                  label (get callee-labels callee)]
              (when-not label
                (reject! :mc-encode :unknown-call-target instruction))
              (if (= "tail-call" (name (:mc/encoding instruction)))
                (concat tail-suffix
                        [(layout/relative-branch
                          (if (= :x86-64 isa)
                            :x86-64/jmp-rel32 :aarch64/b-imm26)
                          label)])
                [(layout/relative-branch
                  (if (= :x86-64 isa)
                    :x86-64/call-rel32 :aarch64/bl-imm26)
                  label)]))
            (encode-selected isa frame-bytes return-suffix instruction-index
                             load-multiplier? instruction))
          :mc/branch-zero
          (if (= :x86-64 isa)
            (concat (x86-rr 0x85 test test)
                    [(layout/relative-branch :x86-64/jz-rel32
                                             (:mc/target instruction))])
            [(layout/relative-branch :aarch64/cbz-imm19
                                     (:mc/target instruction)
                                     [(a64-register test)])])
          :mc/branch-nonzero
          (if (= :aarch64 isa)
            [(layout/relative-branch :aarch64/cbnz-imm19
                                     (:mc/target instruction)
                                     [(a64-register (:mc/test instruction))])]
            (reject! :mc-encode :unknown-operation instruction))
          :mc/jump
          [(layout/relative-branch
            (if (= :x86-64 isa) :x86-64/jmp-rel32 :aarch64/b-imm26)
            (:mc/target instruction))]
          (reject! :mc-encode :unknown-operation instruction)))
              next-multiplier
              (cond
                multiplier multiplier
                (and (= :mc/instruction op)
                     (contains? a64-x16-preserving-encodings encoding))
                cached-a64-multiplier
                :else nil)]
          {:out (into out tokens)
           :cached-a64-multiplier next-multiplier}))
      {:out [] :cached-a64-multiplier nil}
      (map-indexed vector instructions)))))

(defn- qualify-function-locals
  ([function-index tokens] (qualify-function-locals function-index tokens #{}))
  ([function-index tokens protected]
   (let [labels (->> tokens (filter layout/label-token?) (map :mir/id)
                     (remove protected) set)
         renamed (into {} (map (fn [id]
                                 [id (keyword (str "kotoba.native.local." function-index)
                                              (str (namespace id) "." (name id)))])
                               labels))]
     (mapv (fn [token]
             (cond
               (and (layout/label-token? token)
                    (contains? protected (:mir/id token))) token
               (layout/label-token? token)
               (assoc token :mir/id (get renamed (:mir/id token)))
               (and (layout/relative-branch-token? token)
                    (contains? renamed (:mir/target token)))
               (assoc token :mir/target (get renamed (:mir/target token)))
               :else token))
           tokens))))

(defn- call-frame-policy? [frame-policy]
  (contains? #{:all-vregs :call-live} frame-policy))

;; ── callee-saved registers ───────────────────────────────────────────────────
;;
;; The allocator's preserved tier is callee-saved by both ABIs, so a function
;; that names one of those registers owes its caller the original value back.
;; The frame pays exactly that debt: it saves the registers the body actually
;; names and no others, so a function small enough to stay in the scratch tier
;; carries no save at all.
;;
;; Which registers those are is derived from the instruction stream about to be
;; emitted rather than carried alongside it. A carried list has to be kept equal
;; to the body, and when it drifts it drifts toward omitting a save -- which is
;; a corrupted caller, observed far from here.

(defn- x86-saved-frame
  "Pre-index the stack by eight when an odd number of pushes would otherwise
   leave RSP misaligned. The padding sits above the pushes so that FRAME-BYTES,
   which the context slot is measured from, stays exactly as computed."
  [saved]
  (let [pad (if (odd? (count saved)) 8 0)]
    {:save (vec (concat (x86-adjust-stack 0xec pad)
                        (mapcat x86-push saved)))
     :restore (vec (concat (mapcat x86-pop (reverse saved))
                           (x86-adjust-stack 0xc4 pad)))}))

(defn- a64-stack-pair
  "STP/LDP of two registers across one 16-byte stack step, or STR/LDP of one
   when the count is odd -- SP has to stay 16-byte aligned either way, so an
   odd save spends the same sixteen bytes as a pair."
  [opcode a b]
  (u32le (bit-or opcode
                 (if b (bit-shift-left (get aarch64-register-code b) 10) 0)
                 (bit-shift-left 31 5)
                 (get aarch64-register-code a))))

(defn- a64-saved-frame [saved]
  (let [pairs (partition-all 2 saved)]
    {:save (vec (mapcat (fn [[a b]]
                          (if b
                            (a64-stack-pair 0xa9bf0000 a b)   ; stp a, b, [sp, #-16]!
                            (a64-stack-pair 0xf81f0c00 a nil))) ; str a, [sp, #-16]!
                        pairs))
     :restore (vec (mapcat (fn [[a b]]
                             (if b
                               (a64-stack-pair 0xa8c10000 a b)   ; ldp a, b, [sp], #16
                               (a64-stack-pair 0xf8410400 a nil))) ; ldr a, [sp], #16
                           (reverse pairs)))}))

(defn- function-frame [target frame-slots frame-policy instructions]
  (let [storage-bytes (align16 (* 8 frame-slots))
        saved (mir/saved-registers target instructions)]
    (case target
      :x86-64
      (let [frame-bytes (+ storage-bytes (if (call-frame-policy? frame-policy) 8 0))
            {:keys [save restore]} (x86-saved-frame saved)]
        {:frame-bytes frame-bytes
         :saved-registers saved
         :prologue (vec (concat save (x86-adjust-stack 0xec frame-bytes)))
         :tail-suffix (vec (concat (x86-adjust-stack 0xc4 frame-bytes) restore))
         :return-suffix (vec (concat (x86-adjust-stack 0xc4 frame-bytes)
                                     restore [0xc3]))})

      :aarch64
      (let [{:keys [save restore]} (a64-saved-frame saved)]
        (if (call-frame-policy? frame-policy)
          {:frame-bytes storage-bytes
           :saved-registers saved
           :prologue (vec (concat save (u32le 0xa9bf7bfd) (u32le 0x910003fd)
                                  (a64-adjust-stack 0xd10003ff storage-bytes)))
           :tail-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                     (u32le 0xa8c17bfd) restore))
           :return-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                       (u32le 0xa8c17bfd) restore
                                       (u32le 0xd65f03c0)))}
          {:frame-bytes storage-bytes
           :saved-registers saved
           :prologue (vec (concat save
                                  (a64-adjust-stack 0xd10003ff storage-bytes)))
           :tail-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                     restore))
           :return-suffix (vec (concat (a64-adjust-stack 0x910003ff storage-bytes)
                                       restore (u32le 0xd65f03c0)))})))))

(defn- fresh-self-tail-body-label
  "Choose a deterministic function-local label absent from both admitted MC
  labels and the closed instrumentation prefix. Source MIR can spell any
  qualified keyword, so a fixed encoder-private keyword is not collision-safe."
  [function-index prefix instructions]
  (let [occupied (->> (concat prefix instructions)
                      (filter layout/label-token?)
                      (map :mir/id)
                      set)]
    (loop [attempt 0]
      (let [candidate (keyword "kotoba.native.internal.self-tail"
                               (str function-index "." attempt))]
        (if (contains? occupied candidate)
          (recur (inc attempt))
          candidate)))))

(defn encode-mc-module
  "Encode an allocated MC v3 module. PREFIXES is an optional function-name to
  target-token map used by production fuel instrumentation; it participates in
  the same final layout as frames, branches, and calls."
  ([program] (encode-mc-module program {} [(:mc/entry program)]))
  ([program prefixes] (encode-mc-module program prefixes [(:mc/entry program)]))
  ([{:mc/keys [target entry functions] :as program} prefixes exports]
   (mc/validate! program)
   (when-not (= 3 (:mc/version program))
     (reject! :mc-encode :module-version-required program))
   (let [function-names (set (map :mc/name functions))
         _ (when-not (and (vector? exports) (seq exports)
                          (= (count exports) (count (distinct exports)))
                          (every? function-names exports))
             (reject! :mc-encode :invalid-module-exports {:exports exports}))
         callee-labels (into {}
                             (map-indexed
                              (fn [index {:mc/keys [name]}]
                                [name (keyword "kotoba.native.function" (str index))])
                              functions))
         tokens
         (vec
          (mapcat
           (fn [index {:mc/keys [name frame-slots frame-policy instructions]}]
             (let [{:keys [frame-bytes prologue return-suffix tail-suffix]}
                   (function-frame target frame-slots frame-policy instructions)
                   prefix (get prefixes name [])
                   self-tail-body (fresh-self-tail-body-label index prefix instructions)
                   local (vec (concat prefix prologue
                                      (instruction-tokens target frame-bytes return-suffix tail-suffix
                                                          callee-labels prefix self-tail-body
                                                          instructions)))]
               (into [(layout/label (get callee-labels name))]
                     (qualify-function-locals index local #{self-tail-body}))))
           (range) functions))
         {:keys [labels code code-size]} (resolve-program-layout tokens)
         function-offsets (mapv #(get labels (get callee-labels (:mc/name %))) functions)
         entry-index (first (keep-indexed (fn [index function]
                                           (when (= entry (:mc/name function)) index))
                                         functions))
         entry-offset (nth function-offsets entry-index)
         entry-end (if (< (inc entry-index) (count function-offsets))
                     (nth function-offsets (inc entry-index))
                     code-size)
         entry-arity (:mc/arity (nth functions entry-index))
         indexes (into {} (map-indexed (fn [index function]
                                         [(:mc/name function) index])
                                       functions))]
     {:code code
      :exports
      (into {}
            (map (fn [name]
                   (let [index (get indexes name)
                         offset (nth function-offsets index)
                         end (if (< (inc index) (count function-offsets))
                               (nth function-offsets (inc index))
                               code-size)]
                     [name {:offset offset :length (- end offset)
                            :arity (:mc/arity (nth functions index))}]))
                 exports))})))

(defn encode-mc
  "Encode a closed allocated MC v2 program into final machine bytes."
  [{:mc/keys [target frame-slots instructions] :as program}]
  (mc/validate! program)
  (when-not (= 2 (:mc/version program))
    (reject! :mc-encode :flat-program-version-required program))
  (let [host-call? (some #(contains? #{"runtime-call" "capability-call"}
                                     (some-> (:mc/encoding %) name))
                         instructions)
        {:keys [frame-bytes prologue return-suffix tail-suffix]}
        (function-frame target frame-slots
                        (if host-call? :call-live :allocator)
                        instructions)]
    (resolve-layout
     (vec (concat prologue
                  (instruction-tokens target frame-bytes return-suffix tail-suffix {}
                                      [] nil instructions))))))

(def ^:private guest-reentry-ops
  ;; A function that contains one of these can run unbounded guest or host
  ;; work after entry. Fuel is the bound. Arithmetic, `if`, `let`, and `do`
  ;; are finite without it.
  #{:gmir/call :gmir/tail-call :gmir/runtime-call :gmir/capability-call})

(defn function-reenters-guest?
  "True when lowered instructions can invoke more guest or host work."
  [instructions]
  (boolean (some #(contains? guest-reentry-ops (:gmir/op %)) instructions)))

(defn entry-fuel-prefixes
  "Production fuel map: only functions that can re-enter. TOKENS-FOR is
  called with the function name for each such function and must return a
  token vector. Acyclic leaves are omitted — charging them is what the
  100k C harness was paying on `kernel_wide`."
  [kir tokens-for]
  (let [module (lower-kir-module kir)]
    (into {}
          (keep (fn [{:gmir/keys [name instructions]}]
                  (when (function-reenters-guest? instructions)
                    [name (vec (tokens-for name))]))
                (:gmir/functions module)))))

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
        (#(encode-mc-module % prefixes (:exports kir))))))

(defn compile-expression
  "End-to-end closed slice: KIR expression -> GMIR -> MIR -> RA -> MC -> bytes."
  [target params body]
  (->> (lower-kir-expression params body)
       (compile-gmir target)
       encode-mc))
