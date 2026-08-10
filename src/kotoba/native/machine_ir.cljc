(ns kotoba.native.machine-ir
  "Closed pilot contract for GMIR -> target MIR -> allocated MC data.

  The existing production emitters are migrated incrementally. This namespace
  makes the missing layers explicit without pretending arbitrary KIR is already
  covered: the admitted integer/control subset is closed and every unknown op,
  use-before-definition, register exhaustion, or malformed label fails closed."
  (:require [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]
            [kotoba.codegen.mc :as mc]
            [kotoba.codegen.layout :as layout]
            #?(:cljs [kotoba.kir.cljs-i64 :as i64])))

(defn- reject! [phase problem instruction]
  (throw (ex-info (str "machine IR rejected: " (name problem))
                  {:phase phase :problem problem :instruction instruction})))

(defn lower-mc
  "Lower allocated MIR to explicit MC instruction/layout data.

  Instruction bytes remain owned by the target encoders. Branches become the
  same layout tokens used by production backends, so PC-relative values cannot
  be baked before final sizes are known."
  [{:mir/keys [target registers frame-slots instructions] :as program}]
  (mir/validate! program)
  (when-not (= :physical registers)
    (reject! :mc :registers-not-allocated program))
  (mc/validate!
   {:mc/version 2
    :mc/target target
    :mc/frame-slots (or frame-slots 0)
    :mc/instructions
    (mapv (fn [{:mir/keys [op id target test] :as instruction}]
            (case op
              :mir/label (layout/label id)
              :mir/branch-zero
              {:mc/op :mc/branch-zero :mc/test test :mc/target target}
              :mir/jump
              {:mc/op :mc/jump :mc/target target}
              (into {:mc/op :mc/instruction
                     :mc/encoding (keyword (name (:mir/target program)) (name op))}
                    (remove (fn [[k _]] (= k :mir/op)) instruction))))
          instructions)}))

(defn compile-gmir [target program]
  (->> program (mir/select-target target) mir/allocate-registers lower-mc))

;; ── closed KIR expression -> GMIR pilot ─────────────────────────────────────

(def ^:private kir-binary-ops
  {'+ :gmir/add '- :gmir/subtract '* :gmir/multiply
   'quot :gmir/quotient 'bit-and :gmir/bit-and
   'bit-or :gmir/bit-or 'bit-xor :gmir/bit-xor
   '= :gmir/equal '< :gmir/less-than '> :gmir/greater-than
   '<= :gmir/less-or-equal '>= :gmir/greater-or-equal})

(def ^:private kir-predicate-ops
  {'not :gmir/equal 'zero? :gmir/equal
   'pos? :gmir/greater-than 'neg? :gmir/less-than})

(def ^:private kir-fold-ops '#{+ - * bit-and bit-or bit-xor})
(def ^:private kir-comparison-ops '#{= < > <= >=})

(defn- scalar-literal? [form]
  (or (boolean? form) (gmir/i64-value? form)))

(defn- scalar-literal [form]
  (if (boolean? form) (if form 1 0) form))

(def ^:dynamic *production-routing-enabled?*
  "Migration seam used by legacy-emitter regression tests. Production leaves
  this enabled; disabling it never changes the IR contracts themselves."
  true)

(defn lower-kir-expression
  "Lower a closed pure tail-expression subset to GMIR.

  Admitted forms are integer/boolean literals, parameters, lexical `let`,
  recursive scalar arithmetic/comparisons/predicates, and tail-position `if`.
  Unsupported shapes fail closed rather than escaping to the legacy emitter."
  [params body]
  (when-not (and (vector? params) (every? symbol? params)
                 (= (count params) (count (distinct params))))
    (reject! :kir-to-gmir :invalid-parameters {:params params}))
  (let [next-reg (atom -1)
        next-label (atom -1)
        fresh-reg #(gmir/vreg (swap! next-reg inc))
        fresh-label (fn [stem]
                      (keyword "kotoba.gmir.label"
                               (str stem "-" (swap! next-label inc))))
        parameter-env (into {} (map-indexed (fn [index parameter]
                                              [parameter [:argument index]])
                                            params))]
    (letfn [(value [form env]
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
                      [[initial-code initial] & lowered]
                      (mapv #(value % env) operands)]
                  (reduce (fn [[code left] [right-code right]]
                            (let [dst (fresh-reg)]
                              [(vec (concat code right-code
                                            [{:gmir/op (get kir-binary-ops op)
                                              :gmir/dst dst :gmir/left left
                                              :gmir/right right}]))
                               dst]))
                          [initial-code initial]
                          lowered))

                (and (seq? form) (contains? kir-comparison-ops (first form))
                     (> (count form) 3))
                (let [op (get kir-binary-ops (first form))
                      lowered (mapv #(value % env) (rest form))
                      code (vec (mapcat first lowered))
                      registers (mapv second lowered)
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
                (let [[left-code left] (value (second form) env)
                      [right-code right] (value (nth form 2) env)
                      dst (fresh-reg)]
                  [(vec (concat left-code right-code
                                [{:gmir/op (get kir-binary-ops (first form))
                                  :gmir/dst dst
                                  :gmir/left left :gmir/right right}]))
                   dst])

                (and (seq? form) (contains? kir-predicate-ops (first form))
                     (= 2 (count form)))
                (let [[operand-code operand] (value (second form) env)
                      zero (fresh-reg)
                      dst (fresh-reg)]
                  [(vec (concat operand-code
                                [{:gmir/op :gmir/constant :gmir/dst zero
                                  :gmir/value 0}
                                 {:gmir/op (get kir-predicate-ops (first form))
                                  :gmir/dst dst :gmir/left operand
                                  :gmir/right zero}]))
                   dst])

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

                :else (reject! :kir-to-gmir :unsupported-value {:form form})))

            (tail [form env]
              (cond
                (and (seq? form) (= 'if (first form)) (= 4 (count form)))
                (let [[test-code test] (value (second form) env)
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
                (let [[code result] (value form env)]
                  (conj code {:gmir/op :gmir/return :gmir/value result}))))]
      {:gmir/version 1 :gmir/instructions (tail body parameter-env)})))

(defn pilot-expression?
  "True only for the deliberately bounded production migration slice.

  Scalar arithmetic, comparisons, predicates, lexical `let`, and recursive
  tail `if` use the extracted IR path; allocation spills when necessary."
  [params body]
  (let [parameters (set params)]
    (letfn [(value? [form env]
              (or (scalar-literal? form)
                  (contains? env form)
                  (and (seq? form) (contains? kir-fold-ops (first form))
                       (or (> (count form) 3)
                           (and (= '- (first form)) (= 2 (count form))))
                       (every? #(value? % env) (rest form)))
                  (and (seq? form) (contains? kir-comparison-ops (first form))
                       (> (count form) 3)
                       (every? #(value? % env) (rest form)))
                  (and (seq? form) (contains? kir-binary-ops (first form))
                       (= 3 (count form))
                       (value? (second form) env) (value? (nth form 2) env))
                  (and (seq? form) (contains? kir-predicate-ops (first form))
                       (= 2 (count form)) (value? (second form) env))
                  (and (seq? form) (= 'let (first form)) (= 3 (count form))
                       (vector? (second form)) (even? (count (second form)))
                       (loop [bindings (partition 2 (second form)), env env]
                         (if-let [[binding expression] (first bindings)]
                           (and (symbol? binding) (value? expression env)
                                (recur (next bindings) (conj env binding)))
                           (value? (nth form 2) env))))))
            (tail? [form env]
              (or (value? form env)
                  (and (seq? form) (= 'if (first form)) (= 4 (count form))
                       (value? (second form) env)
                       (tail? (nth form 2) env)
                       (tail? (nth form 3) env))
                  (and (seq? form) (= 'let (first form)) (= 3 (count form))
                       (vector? (second form)) (even? (count (second form)))
                       (loop [bindings (partition 2 (second form)), env env]
                         (if-let [[binding expression] (first bindings)]
                           (and (symbol? binding) (value? expression env)
                                (recur (next bindings) (conj env binding)))
                           (tail? (nth form 2) env))))))]
    (and *production-routing-enabled?*
         (vector? params) (<= (count params) 5)
         (= (count params) (count parameters))
         (every? symbol? params)
         (tail? body parameters)))))

;; ── MC -> bytes ──────────────────────────────────────────────────────────────

(def ^:private x86-register-code
  {:x86-64/rax 0 :x86-64/rcx 1 :x86-64/rdx 2 :x86-64/r8 8
   :x86-64/rdi 7 :x86-64/rsi 6})
(def ^:private x86-arguments [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8])
(def ^:private aarch64-register-code
  {:aarch64/x0 0 :aarch64/x1 1 :aarch64/x2 2 :aarch64/x3 3
   :aarch64/x4 4 :aarch64/x16 16})

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

(defn- x86-quotient [dst left right]
  ;; `cqo`/`idiv` use RDX:RAX implicitly. RDX can still hold an unrelated live
  ;; allocated value, so preserve it independently of the explicit operands.
  ;; Restore before copying RAX to `dst`, which also handles `dst = rdx`.
  (vec (concat (x86-push :x86-64/rdx)
               (x86-push right)
               (when-not (= :x86-64/rax left)
                 (x86-rr 0x89 :x86-64/rax left))
               [0x48 0x99 0x59 0x48 0xf7 0xf9]
               [0x5a]
               (when-not (= dst :x86-64/rax)
                 (x86-rr 0x89 dst :x86-64/rax)))))

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

(defn- encode-selected [isa frame-bytes {:mc/keys [encoding] :as instruction}]
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
    :x86-64/return
    (vec (concat (when-not (= :x86-64/rax (:mir/value instruction))
                   (x86-rr 0x89 :x86-64/rax (:mir/value instruction)))
                 (x86-adjust-stack 0xc4 frame-bytes)
                 [0xc3]))

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
     :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor)
    (let [base (case encoding
                 :aarch64/subtract 0xcb000000
                 :aarch64/multiply 0x9b007c00
                 :aarch64/bit-and 0x8a000000
                 :aarch64/bit-or 0xaa000000
                 :aarch64/bit-xor 0xca000000)]
      (u32le (bit-or base
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
    :aarch64/quotient
    (a64-quotient (:mir/dst instruction) (:mir/left instruction)
                  (:mir/right instruction))
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
    :aarch64/return
    (vec (concat (when-not (= :aarch64/x0 (:mir/value instruction))
                   (a64-mov :aarch64/x0 (:mir/value instruction)))
                 (a64-adjust-stack 0x910003ff frame-bytes)
                 (u32le 0xd65f03c0)))
    (reject! :mc-encode :unknown-encoding (assoc instruction :isa isa))))

(defn encode-mc
  "Encode a closed allocated MC program into final machine bytes."
  [{:mc/keys [version target frame-slots instructions] :as program}]
  (mc/validate! program)
  (let [frame-bytes (align16 (* 8 frame-slots))
        prologue (if (= :x86-64 target)
                   (x86-adjust-stack 0xec frame-bytes)
                   (a64-adjust-stack 0xd10003ff frame-bytes))
        tokens
        (vec (concat prologue (mapcat
              (fn [{:mc/keys [op test target] :as instruction}]
                (if (layout/label-token? instruction)
                  [instruction]
                  (case op
                    :mc/instruction (encode-selected (:mc/target program)
                                                     frame-bytes instruction)
                    :mc/branch-zero
                    (if (= :x86-64 (:mc/target program))
                      (concat (x86-rr 0x85 test test)
                              [(layout/relative-branch :x86-64/jz-rel32 target)])
                      [(layout/relative-branch :aarch64/cbz-imm19 target
                                               [(a64-register test)])])
                    :mc/jump
                    [(layout/relative-branch
                      (if (= :x86-64 (:mc/target program))
                        :x86-64/jmp-rel32 :aarch64/b-imm26)
                      target)]
                    (reject! :mc-encode :unknown-operation instruction))))
              instructions)))
        size-of (fn [token]
                  (or (layout/token-size token)
                      (when (and (integer? token) (<= 0 token 255)) 1)))
        labels (layout/label-offsets tokens size-of)]
    (layout/resolve-tokens
     tokens size-of labels
     (fn [{:mir/keys [encoding operands]} displacement]
       (case encoding
         :x86-64/jz-rel32 (into [0x0f 0x84] (mapv byte-value
                                                  [displacement
                                                   (unsigned-bit-shift-right displacement 8)
                                                   (unsigned-bit-shift-right displacement 16)
                                                   (unsigned-bit-shift-right displacement 24)]))
         :x86-64/jmp-rel32 (into [0xe9] (mapv byte-value
                                              [displacement
                                               (unsigned-bit-shift-right displacement 8)
                                               (unsigned-bit-shift-right displacement 16)
                                               (unsigned-bit-shift-right displacement 24)]))
         :aarch64/cbz-imm19
         (u32le (bit-or 0xb4000000
                        (bit-shift-left (bit-and (quot displacement 4) 0x7ffff) 5)
                        (first operands)))
         :aarch64/b-imm26
         (u32le (bit-or 0x14000000 (bit-and (quot displacement 4) 0x03ffffff)))))
     (fn [token _] [token]))))

(defn compile-expression
  "End-to-end closed slice: KIR expression -> GMIR -> MIR -> RA -> MC -> bytes."
  [target params body]
  (->> (lower-kir-expression params body)
       (compile-gmir target)
       encode-mc))
