(ns kotoba.native.peephole
  "Deterministic, size-preserving peephole rewriting shared by the native
  backends.

  ## Why size-preserving is not a stylistic choice

  Both native backends bake intra-function branch displacements into plain
  bytes at emission time, before any later pass could run:
  `x86-64/emit-expr`'s `if` case emits `(le32 (code-size then-code))` and
  `aarch64/emit-expr`'s emits `(cbz-x0 (+ 8 (code-size then-code)))`; the
  variant-dispatch chains do the same. Once emitted, those displacement bytes
  are indistinguishable from any other byte in the token vector. A rewriting
  pass that changed a byte COUNT anywhere would therefore silently invalidate
  every already-baked displacement that spans it -- and would do so without a
  single failing size check, because the token vector has no instruction
  boundaries to check against.

  So the invariant this namespace exists to enforce is:

      a rewritten window occupies EXACTLY as many bytes as the window it
      replaces, padded with canonical architectural no-ops.

  `pad-to` enforces it by construction and throws otherwise. Under that
  invariant, every displacement -- baked and deferred alike -- stays correct
  without the backends knowing a pass ran at all. Nothing else in either
  backend needs to change.

  Padding to the original length means this pass does not shrink code. That is
  deliberate for a first increment: what it removes is memory traffic (a spill
  store, a reload, a stack-pointer round trip) and replaces it with a no-op
  that retires without touching memory. Actually shrinking code requires
  turning the baked displacements into deferred tokens first, which is a
  separate, larger change to both backends.

  ## Why recognition is on KIR forms, not on emitted bytes

  A classic peephole matches byte patterns in the instruction stream. That is
  unsound here: the token vector is undelimited byte soup, so a 64-bit
  immediate whose bytes happen to spell a recognized opcode sequence would be
  rewritten as if it were code. `constant-operand` therefore inspects the KIR
  operand FORM -- which is unambiguous by construction -- and the backend
  builds the replacement window itself from encodings it already owns. No
  function here ever scans emitted bytes looking for instructions.

  ## Determinism

  Every function here is a pure function of its arguments with no map/set
  iteration order dependence, so the same KIR always yields the same bytes.
  That is what `kotoba-verifier` requires: it re-derives emission from sealed
  KIR and rejects any drift, so a nondeterministic pass would not merely be
  untidy, it would make every artifact unverifiable."
  #?(:cljs (:require [kotoba.kir.cljs-i64 :as i64])))

;; The i64 VALUE a KIR operand materializes at compile time, or nil when the
;; operand is anything else. Deliberately narrow: only the two forms whose
;; emitted code provably (a) needs no accumulator register, (b) reads no stack
;; slot, and therefore (c) is insensitive to the temp-depth the spill it
;; replaces would have introduced. Every other form -- a symbol (reads a
;; param/let slot at a depth-relative displacement), a call, a cap-call, a
;; nested expression -- fails (c), (b) or both, and must keep the spill.
;;
;; `integer?` alone does not reliably recognize a cljs `bigint`; mirrors the
;; identical dispatch guard both backends' own `emit-expr` already uses.
;; `false` must map to the value 0 and still be reported as present, so this
;; returns nil-or-value and callers test with `some?`, never truthiness.
(defn constant-operand
  [form]
  (cond
    (boolean? form) (if form 1 0)
    #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form))) form
    :else nil))

;; Intel SDM Vol. 2B, Table 4-12 ("Recommended Multi-Byte Sequence of NOP
;; Instruction"). Indexed by length; index 0 is unused. These are the
;; architecturally recommended encodings, so a disassembler and the verifier's
;; own re-emission both see ordinary NOPs rather than an invented filler.
(def ^:private x86-64-nops
  [nil
   [0x90]
   [0x66 0x90]
   [0x0f 0x1f 0x00]
   [0x0f 0x1f 0x40 0x00]
   [0x0f 0x1f 0x44 0x00 0x00]
   [0x66 0x0f 0x1f 0x44 0x00 0x00]
   [0x0f 0x1f 0x80 0x00 0x00 0x00 0x00]
   [0x0f 0x1f 0x84 0x00 0x00 0x00 0x00 0x00]
   [0x66 0x0f 0x1f 0x84 0x00 0x00 0x00 0x00 0x00]])

;; Exactly `n` bytes of x86-64 no-op. Lengths above 9 are emitted as a
;; deterministic greedy sequence of 9-byte no-ops followed by the remainder,
;; so the encoding is a function of `n` alone.
(defn nop-x86-64
  [n]
  (when (neg? n)
    (throw (ex-info "negative x86-64 no-op length" {:phase :x86-64 :length n})))
  (loop [remaining n out []]
    (cond
      (zero? remaining) out
      (<= remaining 9) (into out (nth x86-64-nops remaining))
      :else (recur (- remaining 9) (into out (nth x86-64-nops 9))))))

;; AArch64 `nop` is the single encoding 0xd503201f; every instruction is four
;; bytes, so a padding length that is not a multiple of four could not be
;; instruction-aligned and is rejected rather than silently rounded.
(def ^:private aarch64-nop [0x1f 0x20 0x03 0xd5])

(defn nop-aarch64
  [n]
  (when (or (neg? n) (pos? (rem n 4)))
    (throw (ex-info "AArch64 no-op padding must be a non-negative multiple of four"
                    {:phase :aarch64 :length n})))
  (vec (mapcat (fn [_] aarch64-nop) (range (quot n 4)))))

;; The load-bearing invariant. `replacement` must be no longer than the window
;; it replaces; the difference is filled with canonical no-ops so the total
;; byte count is unchanged and every already-baked branch displacement that
;; spans this window stays correct.
;;
;; Being longer is a programming error, not a condition to accommodate: it
;; would push every subsequent instruction and corrupt those displacements, so
;; it throws here rather than producing an artifact that only fails later, in
;; the verifier or at run time.
(defn pad-to
  [replacement target nop-fn]
  (let [length (count replacement)]
    (when (> length target)
      (throw (ex-info "peephole replacement is longer than the window it replaces"
                      {:phase :peephole :replacement-length length :window-length target})))
    (into (vec replacement) (nop-fn (- target length)))))
