(ns kotoba.native.layout
  "Deterministic layout for target instruction tokens.

  Backends may mix ordinary encoded bytes with the label and relative-branch
  tokens defined here. Labels have no encoded size. Relative branches reserve
  their architectural width during the first pass and receive their signed
  displacement only after every label position is known.

  This is the first MC/layout boundary in kotoba-native. It deliberately owns
  neither KIR lowering nor register allocation.")

(def ^:private relative-branch-sizes
  {:x86-64/jz-rel32 6
   :x86-64/js-rel32 6
   :x86-64/jl-rel32 6
   :x86-64/jg-rel32 6
   :x86-64/ja-rel32 6
   :x86-64/jae-rel32 6
   :x86-64/jmp-rel32 5
   :x86-64/jmp-rel8 2
   :x86-64/jne-rel8 2
   :aarch64/cbz-x0-imm19 4
   :aarch64/cbz-x1-imm19 4
   :aarch64/cbnz-x1-imm19 4
   :aarch64/cbnz-x16-imm19 4
   :aarch64/b-eq-imm19 4
   :aarch64/b-ne-imm19 4
   :aarch64/b-hi-imm19 4
   :aarch64/b-hs-imm19 4
   :aarch64/b-lt-imm19 4
   :aarch64/b-gt-imm19 4
   :aarch64/tbnz-imm14 4
   :aarch64/b-imm26 4})

(def ^:private relative-branch-ranges
  {:x86-64/jz-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/js-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/jl-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/jg-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/ja-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/jae-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/jmp-rel32 [(- 0x80000000) 0x7fffffff]
   :x86-64/jmp-rel8 [-128 127]
   :x86-64/jne-rel8 [-128 127]
   :aarch64/cbz-x0-imm19 [(- 0x100000) 0xffffc]
   :aarch64/cbz-x1-imm19 [(- 0x100000) 0xffffc]
   :aarch64/cbnz-x1-imm19 [(- 0x100000) 0xffffc]
   :aarch64/cbnz-x16-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-eq-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-ne-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-hi-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-hs-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-lt-imm19 [(- 0x100000) 0xffffc]
   :aarch64/b-gt-imm19 [(- 0x100000) 0xffffc]
   :aarch64/tbnz-imm14 [(- 0x8000) 0x7ffc]
   :aarch64/b-imm26 [(- 0x8000000) 0x7fffffc]})

;; x86 relative displacements start after the instruction. AArch64 immediate
;; branches are relative to the address of the branch instruction itself.
(def ^:private relative-branch-pc-bias
  {:x86-64/jz-rel32 6
   :x86-64/js-rel32 6
   :x86-64/jl-rel32 6
   :x86-64/jg-rel32 6
   :x86-64/ja-rel32 6
   :x86-64/jae-rel32 6
   :x86-64/jmp-rel32 5
   :x86-64/jmp-rel8 2
   :x86-64/jne-rel8 2
   :aarch64/cbz-x0-imm19 0
   :aarch64/cbz-x1-imm19 0
   :aarch64/cbnz-x1-imm19 0
   :aarch64/cbnz-x16-imm19 0
   :aarch64/b-eq-imm19 0
   :aarch64/b-ne-imm19 0
   :aarch64/b-hi-imm19 0
   :aarch64/b-hs-imm19 0
   :aarch64/b-lt-imm19 0
   :aarch64/b-gt-imm19 0
   :aarch64/tbnz-imm14 0
   :aarch64/b-imm26 0})

(def ^:private relative-branch-alignments
  {:x86-64/jz-rel32 1
   :x86-64/js-rel32 1
   :x86-64/jl-rel32 1
   :x86-64/jg-rel32 1
   :x86-64/ja-rel32 1
   :x86-64/jae-rel32 1
   :x86-64/jmp-rel32 1
   :x86-64/jmp-rel8 1
   :x86-64/jne-rel8 1
   :aarch64/cbz-x0-imm19 4
   :aarch64/cbz-x1-imm19 4
   :aarch64/cbnz-x1-imm19 4
   :aarch64/cbnz-x16-imm19 4
   :aarch64/b-eq-imm19 4
   :aarch64/b-ne-imm19 4
   :aarch64/b-hi-imm19 4
   :aarch64/b-hs-imm19 4
   :aarch64/b-lt-imm19 4
   :aarch64/b-gt-imm19 4
   :aarch64/tbnz-imm14 4
   :aarch64/b-imm26 4})

(defn label
  "A zero-width, function-local label token. ID must be a qualified keyword."
  [id]
  {:mir/op :mir/label :mir/id id})

(defn relative-branch
  "A target instruction whose displacement is resolved by `resolve-tokens`."
  ([encoding target]
   {:mir/op :mir/relative-branch
    :mir/encoding encoding
    :mir/target target})
  ([encoding target operands]
   {:mir/op :mir/relative-branch
    :mir/encoding encoding
    :mir/target target
    :mir/operands (vec operands)}))

(defn label-token? [token]
  (and (map? token) (= :mir/label (:mir/op token))))

(defn relative-branch-token? [token]
  (and (map? token) (= :mir/relative-branch (:mir/op token))))

(defn token-size
  "Returns the encoded width of a layout token, or nil for a token owned by
  another layer."
  [token]
  (cond
    (label-token? token) 0
    (relative-branch-token? token) (get relative-branch-sizes (:mir/encoding token))
    :else nil))

(defn- qualified-label-id? [x]
  (and (keyword? x) (some? (namespace x))))

(defn- validate-layout-token! [token]
  (cond
    (label-token? token)
    (do
      (when-not (= #{:mir/op :mir/id} (set (keys token)))
        (throw (ex-info "non-canonical MIR label token" {:phase :layout :token token})))
      (when-not (qualified-label-id? (:mir/id token))
        (throw (ex-info "MIR label id must be a qualified keyword"
                        {:phase :layout :token token}))))

    (relative-branch-token? token)
    (do
      (when-not (contains? #{#{:mir/op :mir/encoding :mir/target}
                             #{:mir/op :mir/encoding :mir/target :mir/operands}}
                           (set (keys token)))
        (throw (ex-info "non-canonical MIR relative branch token"
                        {:phase :layout :token token})))
      (when-not (contains? relative-branch-sizes (:mir/encoding token))
        (throw (ex-info "unsupported MIR relative branch encoding"
                        {:phase :layout :token token})))
      (when-not (qualified-label-id? (:mir/target token))
        (throw (ex-info "MIR branch target must be a qualified keyword"
                        {:phase :layout :token token})))
      (when (and (contains? token :mir/operands)
                 (not (vector? (:mir/operands token))))
        (throw (ex-info "MIR branch operands must be a vector"
                        {:phase :layout :token token})))
      (if (= :aarch64/tbnz-imm14 (:mir/encoding token))
        (let [[reg bit-index :as operands] (:mir/operands token)]
          (when-not (and (= 2 (count operands))
                         (integer? reg) (<= 0 reg 31)
                         (integer? bit-index) (<= 0 bit-index 63))
            (throw (ex-info "AArch64 TBNZ requires [register bit-index] operands"
                            {:phase :layout :token token}))))
        (when (contains? token :mir/operands)
          (throw (ex-info "MIR branch encoding does not accept operands"
                          {:phase :layout :token token})))))

    (and (map? token) (contains? token :mir/op))
    (throw (ex-info "unknown canonical MIR token operation"
                    {:phase :layout :token token}))

    :else nil)
  token)

(defn label-offsets
  "First layout pass. SIZE-OF must return every non-label token's encoded
  width. Duplicate labels and unknown token widths fail closed."
  [tokens size-of]
  (loop [remaining tokens position 0 labels {}]
    (if-let [token (first remaining)]
      (do
        (validate-layout-token! token)
        (if (label-token? token)
          (let [id (:mir/id token)]
            (when (contains? labels id)
              (throw (ex-info "duplicate MIR label" {:phase :layout :label id})))
            (recur (next remaining) position (assoc labels id position)))
          (let [size (size-of token)]
            (when-not (and (integer? size) (not (neg? size)))
              (throw (ex-info "token has no non-negative encoded size"
                              {:phase :layout :token token :size size})))
            (recur (next remaining) (+ position size) labels))))
      labels)))

(defn signed-displacement
  "Returns TARGET-(POSITION+PC-BIAS). x86 uses its instruction width as the
  bias; AArch64 immediate branches use zero because their PC is the address of
  the branch instruction."
  [position pc-bias target]
  (- target (+ position pc-bias)))

(defn resolve-tokens
  "Second layout pass. LABELS normally comes from `label-offsets`. ENCODE-BRANCH
  receives the canonical branch token and its signed displacement. ENCODE-OTHER
  resolves all backend-owned tokens and bytes."
  [tokens size-of labels encode-branch encode-other]
  (loop [remaining tokens position 0 out []]
    (if-let [token (first remaining)]
      (cond
        (label-token? token)
        (recur (next remaining) position out)

        (relative-branch-token? token)
        (let [size (size-of token)
              target-id (:mir/target token)
              target (get labels target-id)]
          (when (nil? target)
            (throw (ex-info "MIR branch references an unknown label"
                            {:phase :layout :target target-id})))
          (let [encoding (:mir/encoding token)
                pc-bias (get relative-branch-pc-bias encoding)
                alignment (get relative-branch-alignments encoding)
                displacement (signed-displacement position pc-bias target)
                [minimum maximum] (get relative-branch-ranges encoding)]
            (when-not (<= minimum displacement maximum)
              (throw (ex-info "MIR relative branch displacement is out of range"
                              {:phase :layout :token token :displacement displacement
                               :minimum minimum :maximum maximum})))
            (when-not (zero? (mod displacement alignment))
              (throw (ex-info "MIR relative branch displacement is unaligned"
                              {:phase :layout :token token :displacement displacement
                               :alignment alignment})))
            (let [encoded (vec (encode-branch token displacement))]
              (when-not (= size (count encoded))
                (throw (ex-info "branch encoder violated its reserved width"
                                {:phase :layout :token token :reserved size
                                 :encoded (count encoded)})))
              (recur (next remaining) (+ position size) (into out encoded)))))

        :else
        (let [size (size-of token)
              encoded (vec (encode-other token position))]
          (when-not (= size (count encoded))
            (throw (ex-info "token encoder violated its reserved width"
                            {:phase :layout :token token :reserved size
                             :encoded (count encoded)})))
          (recur (next remaining) (+ position size) (into out encoded))))
      out)))
