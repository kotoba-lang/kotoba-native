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
   'bit-or :gmir/bit-or 'bit-xor :gmir/bit-xor})

(def ^:dynamic *production-routing-enabled?*
  "Migration seam used by legacy-emitter regression tests. Production leaves
  this enabled; disabling it never changes the IR contracts themselves."
  true)

(defn lower-kir-expression
  "Lower a closed pure tail-expression subset to GMIR.

  Admitted forms are integer literals, parameters, recursive i64 arithmetic,
  and tail-position `(if test then else)`.
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
        parameter-index (zipmap params (range))]
    (letfn [(value [form]
              (cond
                (gmir/i64-value? form)
                (let [dst (fresh-reg)]
                  [[{:gmir/op :gmir/constant :gmir/dst dst :gmir/value form}] dst])

                (symbol? form)
                (if-some [index (get parameter-index form)]
                  (let [dst (fresh-reg)]
                    [[{:gmir/op :gmir/argument :gmir/dst dst :gmir/index index}] dst])
                  (reject! :kir-to-gmir :unknown-parameter {:form form}))

                (and (seq? form) (contains? kir-binary-ops (first form))
                     (= 3 (count form)))
                (let [[left-code left] (value (second form))
                      [right-code right] (value (nth form 2))
                      dst (fresh-reg)]
                  [(vec (concat left-code right-code
                                [{:gmir/op (get kir-binary-ops (first form))
                                  :gmir/dst dst
                                  :gmir/left left :gmir/right right}]))
                   dst])

                :else (reject! :kir-to-gmir :unsupported-value {:form form})))

            (tail [form]
              (if (and (seq? form) (= 'if (first form)) (= 4 (count form)))
                (let [[test-code test] (value (second form))
                      else-label (fresh-label "if-else")]
                  (vec (concat test-code
                               [{:gmir/op :gmir/branch-zero
                                 :gmir/test test :gmir/target else-label}]
                               (tail (nth form 2))
                               [{:gmir/op :gmir/label :gmir/id else-label}]
                               (tail (nth form 3)))))
                (let [[code result] (value form)]
                  (conj code {:gmir/op :gmir/return :gmir/value result}))))]
      {:gmir/version 1 :gmir/instructions (tail body)})))

(defn pilot-expression?
  "True only for the deliberately bounded production migration slice.

  Recursive i64 arithmetic and tail `if` use the extracted IR path; allocation
  spills when necessary. Other expression families remain on the established
  emitter until their typed GMIR operations are admitted explicitly."
  [params body]
  (let [parameters (set params)
        atomic? #(or (gmir/i64-value? %) (contains? parameters %))]
    (letfn [(value? [form]
              (or (atomic? form)
                  (and (seq? form) (contains? kir-binary-ops (first form))
                       (= 3 (count form))
                       (value? (second form)) (value? (nth form 2)))))]
    (and *production-routing-enabled?*
         (vector? params) (<= (count params) 4)
         (= (count params) (count parameters))
         (every? symbol? params)
         (or (value? body)
             (and (seq? body) (= 'if (first body)) (= 4 (count body))
                  (value? (second body))
                  (value? (nth body 2))
                  (value? (nth body 3))))))))

;; ── MC -> bytes ──────────────────────────────────────────────────────────────

(def ^:private x86-register-code
  {:x86-64/rax 0 :x86-64/rcx 1 :x86-64/rdx 2 :x86-64/r8 8
   :x86-64/rdi 7 :x86-64/rsi 6})
(def ^:private x86-arguments [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8])
(def ^:private aarch64-register-code
  {:aarch64/x0 0 :aarch64/x1 1 :aarch64/x2 2 :aarch64/x3 3})

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
  (vec (concat (x86-push right)
               (when-not (= :x86-64/rax left)
                 (x86-rr 0x89 :x86-64/rax left))
               [0x48 0x99 0x59 0x48 0xf7 0xf9]
               (when-not (= dst :x86-64/rax)
                 (x86-rr 0x89 dst :x86-64/rax)))))

(defn- x86-mov-imm [dst value]
  (let [d (get x86-register-code dst)]
    (when-not (some? d) (reject! :mc-encode :unsupported-register {:dst dst}))
    (into [(bit-or 0x48 (if (>= d 8) 1 0)) (+ 0xb8 (bit-and d 7))] (le64 value))))

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
      (when-not (<= 0 index 3) (reject! :mc-encode :argument-index-unsupported instruction))
      (if (= dst src) [] (a64-mov dst src)))
    :aarch64/constant (a64-constant (:mir/dst instruction) (:mir/value instruction))
    :aarch64/add
    (u32le (bit-or 0x8b000000
                   (bit-shift-left (a64-register (:mir/right instruction)) 16)
                   (bit-shift-left (a64-register (:mir/left instruction)) 5)
                   (a64-register (:mir/dst instruction))))
    (:aarch64/subtract :aarch64/multiply :aarch64/quotient
     :aarch64/bit-and :aarch64/bit-or :aarch64/bit-xor)
    (let [base (case encoding
                 :aarch64/subtract 0xcb000000
                 :aarch64/multiply 0x9b007c00
                 :aarch64/quotient 0x9ac00c00
                 :aarch64/bit-and 0x8a000000
                 :aarch64/bit-or 0xaa000000
                 :aarch64/bit-xor 0xca000000)]
      (u32le (bit-or base
                     (bit-shift-left (a64-register (:mir/right instruction)) 16)
                     (bit-shift-left (a64-register (:mir/left instruction)) 5)
                     (a64-register (:mir/dst instruction)))))
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
