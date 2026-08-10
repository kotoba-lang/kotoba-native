(ns kotoba.native.x86-64
  ;; `kotoba.native.peephole` is required on BOTH runtimes, so the reader
  ;; conditional that used to wrap the whole `:require` (see
  ;; `kotoba.wasm.core`'s ns form for that original reasoning -- the `:clj`
  ;; branch needed no requires at all) now wraps only the cljs-only item.
  (:require [kotoba.codegen.layout :as layout]
            [kotoba.native.machine-ir :as machine-ir]
            [kotoba.native.peephole :as peephole]
            [kotoba.native.string-index :as string-index]
            [kotoba.native.string-search :as string-search]
            #?@(:cljs [[kotoba.kir.cljs-i64 :as i64]])))

;; `le32` only ever encodes small, non-negative, interpreter-internal
;; displacements/offsets/immediate operands in this file (stack disps,
;; jump/call targets, cap ids) -- never an arbitrary `.kotoba` i64 VALUE --
;; so it stays plain JS-number-based on both runtimes, same reasoning
;; `kotoba.wasm.core`'s `uleb` comment gives: `(long n)` was
;; already a no-op cast on :clj for values in this range; dropped for :cljs
;; since cljs has no `long`.
;; Mirrors `kotoba.wasm.core`'s `utf8` -- `.getBytes` is JVM-only,
;; cljs has no `String`/`Charset`; `TextEncoder` is the UTF-8-safe equivalent.
(defn- utf8-bytes [s]
  #?(:clj (.getBytes ^String s "UTF-8")
     :cljs (js/Array.from (.encode (js/TextEncoder.) s))))

(defn- le32 [n]
  (mapv #(bit-and (unsigned-bit-shift-right #?(:clj (long n) :cljs n) (* 8 %)) 0xff) (range 4)))

;; `le64` DOES encode arbitrary `.kotoba` i64 literals (`emit-expr`'s
;; `(integer? form)` case, below) across the FULL signed 64-bit range, so
;; this is the highest-risk port in this file -- same class of bug
;; `kotoba.wasm.core`'s `sleb` comment documents at length: a
;; naive cljs port using `bit-and`/`unsigned-bit-shift-right` on a plain
;; number or bigint directly would either throw ("Cannot mix BigInt and
;; other types") or silently truncate to 32 bits, corrupting the compiled
;; machine code rather than erroring. The `:cljs` branch first reduces N to
;; its UNSIGNED 64-bit bit-pattern via `BigInt.asUintN` (matching what
;; `unsigned-bit-shift-right` on a JVM `long` already does implicitly --
;; treat the two's-complement bits as unsigned for extraction purposes),
;; then extracts 8 bits at a time via repeated division by a small,
;; always-int32-safe bigint constant (256) rather than `i64/ashr`:
;; `i64/ashr`'s own divisor is computed via a PLAIN (non-bigint)
;; `bit-shift-left`, safe only for its existing caller's small, fixed
;; 7-bit-at-a-time `sleb128` shift -- calling it here with shift>=32 hits
;; JS's int32 bitwise-shift wraparound (shift amounts are taken mod 32,
;; so `bit-shift-left 1 32` silently equals `bit-shift-left 1 0` = 1, not
;; 2^32), confirmed live: it produced the low 4 bytes twice instead of the
;; correct high 4 bytes. Repeated division by a fixed 256 avoids computing
;; any large divisor at all.
(defn- le64 [n]
  #?(:clj (mapv #(bit-and (unsigned-bit-shift-right (long n) (* 8 %)) 0xff) (range 8))
     :cljs (let [u (js/BigInt.asUintN 64 (i64/->bigint n))
                 base (js/BigInt 256)]
             (loop [i 0 rem u out []]
               (if (= i 8)
                 out
                 (recur (inc i) (/ rem base) (conj out (js/Number (bit-and rem (js/BigInt 0xff))))))))))

(def ^:private param-pushes [[0x57] [0x56] [0x52] [0x51] [0x41 0x50]])
(def ^:private arg-pops [[0x5f] [0x5e] [0x5a] [0x59] [0x41 0x58]])
(declare fresh-label)

(def ^:private fuel-charge
  ;; Compatibility byte vector for the low-level native executor qualification,
  ;; which predates deferred layout and dereferences this private var directly.
  [0x49 0x83 0x79 0x08 0x00 0x75 0x02 0x0f 0x0b 0x49 0xff 0x49 0x08])

(defn- fuel-charge-tokens [counter]
  ;; context v2: fuel is qword [r9+8].
  (let [present-label (fresh-label counter "fuel-present")]
    (vec (concat [0x49 0x83 0x79 0x08 0x00]
                 [(layout/relative-branch :x86-64/jne-rel8 present-label)]
                 [0x0f 0x0b]
                 [(layout/label present-label)]
                 [0x49 0xff 0x49 0x08]))))

(defn- token-size [token]
  (cond (some? (layout/token-size token)) (layout/token-size token)
        (and (map? token) (or (:call token) (:tail-self token))) 5
        (and (map? token) (:string-literal token)) 10
        :else 1))
(defn- code-size [tokens] (reduce + (map token-size tokens)))

;; ── f64 ──────────────────────────────────────────────────────────────────
;;
;; Same representation choice as the AArch64 backend: an f64 lives in the
;; ordinary integer register and stack slot as its IEEE-754 bit pattern, so
;; `f64-from-bits` and `f64-to-bits` emit nothing and f64 literals reuse the
;; existing constant path (the frontend already lowers them to
;; `(f64-from-bits <i64>)`).
;;
;; `emit-binary` leaves lhs in rax and rhs in rcx, so arithmetic is: move
;; both into the SSE bank, operate, move the result back.
;;
;; `f64-neg` and `f64-abs` do NOT go through SSE. x86 has no scalar fneg or
;; fabs — the usual trick is xorpd/andpd against a mask, which needs a
;; constant pool this backend does not have. Flipping or clearing the sign
;; bit with `btc`/`btr` in the integer register is the same operation, is
;; exactly what AArch64's FNEG/FABS do (both are bit operations that raise no
;; exception, NaN included), and keeps the two backends bit-identical.
;;
;; Every encoding below was checked against `clang -target x86_64-apple-macos`.

(def ^:private movq-rax-xmm0 [0x66 0x48 0x0f 0x6e 0xc0])
(def ^:private movq-rcx-xmm1 [0x66 0x48 0x0f 0x6e 0xc9])
(def ^:private movq-xmm0-rax [0x66 0x48 0x0f 0x7e 0xc0])

(def ^:private f64-binary-ops
  {'f64-add [0xf2 0x0f 0x58 0xc1] 'f64-sub [0xf2 0x0f 0x5c 0xc1]
   'f64-mul [0xf2 0x0f 0x59 0xc1] 'f64-div [0xf2 0x0f 0x5e 0xc1]
   'f64-max [0xf2 0x0f 0x5f 0xc1] 'f64-min [0xf2 0x0f 0x5d 0xc1]})

;; UCOMISD sets ZF=PF=CF=1 when either operand is NaN, so a NaN-safe ordered
;; test must be one that reads CF=0 or ZF=0: `seta` (CF=0 and ZF=0) and `setae`
;; (CF=0) both fail on unordered. `setb`/`setbe` would SUCCEED there, which is
;; why lt/le swap the operands and reuse seta/setae rather than using them.
;; Equality additionally needs PF=0, since unordered also sets ZF.
(def ^:private ucomisd-xmm0-xmm1 [0x66 0x0f 0x2e 0xc1])
(def ^:private ucomisd-xmm1-xmm0 [0x66 0x0f 0x2e 0xc8])
(def ^:private movzx-rax-al [0x48 0x0f 0xb6 0xc0])

(def ^:private f64-compare-ops
  {'f64-gt (vec (concat ucomisd-xmm0-xmm1 [0x0f 0x97 0xc0] movzx-rax-al))
   'f64-ge (vec (concat ucomisd-xmm0-xmm1 [0x0f 0x93 0xc0] movzx-rax-al))
   'f64-lt (vec (concat ucomisd-xmm1-xmm0 [0x0f 0x97 0xc0] movzx-rax-al))
   'f64-le (vec (concat ucomisd-xmm1-xmm0 [0x0f 0x93 0xc0] movzx-rax-al))
   'f64-unordered (vec (concat ucomisd-xmm0-xmm1 [0x0f 0x9a 0xc0] movzx-rax-al))
   ;; sete al; setnp cl; and al, cl
   'f64-eq (vec (concat ucomisd-xmm0-xmm1 [0x0f 0x94 0xc0 0x0f 0x9b 0xc1 0x20 0xc8]
                        movzx-rax-al))})

(def ^:private f64-unary-ops
  {'f64-sqrt (vec (concat movq-rax-xmm0 [0xf2 0x0f 0x51 0xc0] movq-xmm0-rax))
   'f64-neg [0x48 0x0f 0xba 0xf8 0x3f]
   'f64-abs [0x48 0x0f 0xba 0xf0 0x3f]})

(declare emit-expr)
(declare finalize)
(declare record-new-binding)
(declare boxed-record-chain)

(defn- fresh-label [counter purpose]
  (keyword "kotoba.mir.label" (str purpose "-" (swap! counter inc))))

(defn- load-param [param-index param-count pad? temp-depth]
  (let [disp (* 8 (+ (if pad? 1 0) (- param-count 1 param-index) temp-depth))]
    (into [0x48 0x8b 0x84 0x24] (le32 disp))))

;; A `let`-bound value's own 8-byte pushed stack slot, addressed relative to
;; the CURRENT temp-depth (8-byte units pushed since function entry) rather
;; than a fixed offset -- unlike params (fixed disp from the frame's own
;; base, via `load-param`), a let value can be read after further nested
;; pushes (more arithmetic temporaries, nested lets), so its offset from the
;; live rsp must be recomputed from how much *more* has been pushed since it
;; was stored.
(defn- load-let [let-depth temp-depth]
  (into [0x48 0x8b 0x84 0x24] (le32 (* 8 (- temp-depth let-depth 1)))))

;; The spill/reload window that both `emit-binary` and the n-ary arithmetic
;; reduce place between the left operand's code and the operation itself:
;;
;;     push rax           ; spill left -- right's code targets rax too
;;     <right operand>
;;     mov rcx,rax        ; move right's result into the scratch register
;;     pop rax            ; reload left
;;
(def ^:private binary-spill [0x50])
(def ^:private binary-reload [0x48 0x89 0xc1 0x58])

;; When the right operand is a compile-time constant, that whole round trip is
;; unnecessary: there is nothing to protect rax from, because the constant can
;; be materialized straight into the scratch register. `mov rcx,imm64`
;; (REX.W B8+rcx) is the same ten bytes `mov rax,imm64` (REX.W B8+rax) would
;; have taken, so the window shrinks by exactly the spill and reload -- which
;; become canonical no-ops rather than shortening the window, because both
;; backends bake branch displacements as plain bytes before any pass can run.
;; `kotoba.native.peephole`'s namespace docstring explains why that makes size
;; preservation mandatory rather than merely convenient.
;;
;; The window length is DERIVED from the replacement's own length rather than
;; written as a literal 15: `mov rcx,imm64` and `mov rax,imm64` encode in the
;; same width, so the replacement's length is exactly what the constant's code
;; would have occupied on the unoptimized path. Should either encoding ever
;; change, the two move together instead of drifting apart silently.
(defn- emit-rhs-window [right env ctx]
  (let [constant (peephole/constant-operand right)]
    (if (some? constant)
      (into [0x48 0xb9] (le64 constant))
      (vec (concat binary-spill
                   (emit-expr right env (update ctx :temp-depth inc))
                   binary-reload)))))

(defn- emit-binary [left right opcode env ctx]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr left env ctx)
                 (emit-rhs-window right env ctx)
                 opcode))))

;; Every call shape on this backend -- a self tail call, an ordinary call, and
;; a host context call -- begins the same way: evaluate each argument
;; left-to-right and push it, so that a nested call's own temporaries cannot
;; clobber an argument already computed. That walk lives here ONCE, because the
;; three copies it replaced were not identical for long enough to be safe: each
;; was written as
;;
;;     (if-let [arg (first remaining)] …)
;;
;; and `if-let` tests the BOUND VALUE, not the sequence. An argument whose KIR
;; form is the literal `false` is a perfectly ordinary `:bool` value here (see
;; `emit-expr`: it is the i64 word 0), but it made `if-let` take the else
;; branch -- so that argument AND EVERY ARGUMENT AFTER IT was silently not
;; emitted, while the caller still popped the full arity from `argc`. The
;; result was a program that assembled cleanly, was shorter by exactly the
;; missing pushes, and ran off its own stack (SIGSEGV via the tail-self path,
;; SIGILL via the ordinary one). `nil` cannot appear here for the same reason
;; `false` can -- KIR has no nil argument form -- so nothing was ever relying
;; on the truthiness test to terminate the loop early; it terminated on the
;; empty sequence, and `(seq remaining)` says exactly that.
;;
;; The AArch64 backend was never affected: it walks arguments with `mapcat`,
;; which has no truthiness test to get wrong. That is not a representation
;; difference between the two backends -- both carry a `:bool` as an i64 word
;; -- it is a difference in how the loop was written, which is why the fix is
;; here and not in any value encoding.
(defn- emit-pushed-arguments
  "Each argument evaluated in order and pushed, starting at TEMP-DEPTH."
  [args env ctx temp-depth]
  (loop [remaining args depth temp-depth out []]
    (if (seq remaining)
      (recur (next remaining) (inc depth)
             (into out (concat (emit-expr (first remaining) env
                                          (assoc ctx :tail? false :temp-depth depth))
                               [0x50])))
      out)))

(defn- emit-tail-self-call [args env {:keys [param-count pad? temp-depth] :as ctx}]
  ;; All arguments are evaluated before any parameter slot is overwritten.
  ;; r11 then anchors the existing function frame while the temporary values
  ;; are popped in reverse order into their corresponding slots.  Charging
  ;; fuel here preserves ordinary call semantics; the final jump re-enters
  ;; the expression body without growing the native stack.
  (let [argc (count args)
        values (emit-pushed-arguments args env ctx temp-depth)
        anchor [0x4c 0x8d 0x9c 0x24] ; lea r11,[rsp+argc*8]
        stores (mapcat (fn [param-index]
                         (let [disp (* 8 (+ (if pad? 1 0)
                                              (- param-count 1 param-index)))]
                           (concat [0x58 0x49 0x89 0x83] (le32 disp))))
                       (reverse (range argc)))]
    (vec (concat values anchor (le32 (* argc 8)) stores
                 (fuel-charge-tokens (:mir-label-counter ctx))
                 [{:tail-self true}]))))

;; The caller's half of the record-parameter boundary. A record is N slots and
;; the ABI passes one word, so an argument that denotes a record is boxed into
;; the same `pair` chain a record RESULT has crossed on since ADR 0062 -- as a
;; source rewrite into forms this backend already emits, not a new encoding.
;;
;; Two shapes can denote a record here. A literal `record-new` boxes its field
;; expressions directly. A `let`-bound record was FLATTENED into one slot per
;; field, so it is re-boxed from those slots, in declared field order -- reading
;; each child binding by name, which `emit-expr` resolves exactly as it would
;; anywhere else. Anything else (a call's result, a parameter) is already a
;; one-word handle and passes through untouched.
(defn- box-record-argument [arg env]
  (cond
    (record-new-binding arg) (boxed-record-chain (vec (drop 2 arg)))
    (and (symbol? arg) (:record-fields (get env arg)))
    (let [{:keys [record-type record-fields]} (get env arg)]
      (boxed-record-chain (mapv (fn [[field-name _]] (get record-fields field-name))
                                (nth record-type 2))))
    :else arg))

(defn- emit-call [op args env {:keys [temp-depth function-name tail?] :as ctx}]
  (let [args (mapv #(box-record-argument % env) args)
        argc (count args)]
    (when (> argc 5)
      (throw (ex-info "x86-64 fuel ABI supports at most five arguments"
                      {:phase :x86-64 :function op :arity argc})))
    ;; The tail-self-call fast path reuses the CURRENT frame's own param
    ;; slots via a fixed disp from the function's baseline (`emit-tail-self-
    ;; call`'s `stores`, computed from param-count/pad? alone, with no
    ;; per-call depth term) -- correct only when nothing else (a `let`'s
    ;; still-live bindings) is currently pushed between rsp and that
    ;; baseline. `:tail?` already excludes every other non-tail position
    ;; (arithmetic/comparison/heap-call/cap-call operands all set it false);
    ;; the added `(zero? temp-depth)` guard is specifically for a self-call
    ;; in tail position from inside a `let`'s body, which is otherwise still
    ;; `:tail? true` but no longer at the function's own baseline depth.
    (if (and tail? (= op function-name) (zero? temp-depth))
      (emit-tail-self-call args env ctx)
      (let [values (emit-pushed-arguments args env ctx temp-depth)
            pops (mapcat #(nth arg-pops %) (reverse (range argc)))
            ;; SysV requires rsp%16==0 immediately before CALL. The fixed
            ;; function frame is aligned; expression temporaries may flip it.
            align? (odd? temp-depth)]
        (vec (concat values pops (when align? [0x50]) [{:call op}]
                     (when align? [0x48 0x83 0xc4 0x08])))))))

;; `cap-id` arrives as an arbitrary `.kotoba` VALUE straight from the KIR
;; effect (`cap-call`'s first arg), which on cljs is a `bigint` (see
;; `le64`'s own doc comment above) -- but this function only ever does
;; small, always-in-[0,255] bit/offset arithmetic on it (validated
;; elsewhere, e.g. `kotoba.verifier`'s `valid-effect?`), so it's
;; coerced to a plain JS number ONCE up front rather than propagating
;; bigint through `quot`/`mod`/`bit-shift-left`: JS bigint arithmetic
;; ops throw ("Cannot mix BigInt and other types") when combined with a
;; plain-number operand like the literal `8` here, confirmed live.
(defn- emit-cap-call [cap-id value env {:keys [temp-depth] :as ctx}]
  (let [counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        allowed-label (fresh-label counter "cap-allowed")
        cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        byte-offset (+ 16 (quot cap-id 8))
        mask (bit-shift-left 1 (mod cap-id 8))
        ;; Save context across the host ABI call. The fixed guest frame is
        ;; aligned; an even temp depth needs one additional 8-byte pad after
        ;; pushing r9.
        align? (even? temp-depth)]
    (vec (concat
          [0x41 0xf6 0x41 byte-offset mask]
          [(layout/relative-branch :x86-64/jne-rel8 allowed-label)]
          [0x0f 0x0b]
          [(layout/label allowed-label)]
          (emit-expr value env (assoc ctx :tail? false))
          [0x48 0x89 0xc2 0x41 0x51]             ; rdx=value; push r9
          (when align? [0x50])
          [0xbe] (le32 cap-id)                    ; esi=cap-id
          [0x4c 0x89 0xcf 0x41 0xff 0x51 0x30]   ; rdi=r9; call [r9+48]
          (when align? [0x48 0x83 0xc4 0x08])
          [0x41 0x59]))))                         ; pop r9

(defn- emit-typed-cap-call [cap-id kind value env {:keys [temp-depth] :as ctx}]
  (let [counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        allowed-label (fresh-label counter "typed-cap-allowed")
        cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        byte-offset (+ 16 (quot cap-id 8))
        mask (bit-shift-left 1 (mod cap-id 8))
        align? (even? temp-depth)]
    (vec (concat
          [0x41 0xf6 0x41 byte-offset mask]
          [(layout/relative-branch :x86-64/jne-rel8 allowed-label)]
          [0x0f 0x0b]
          [(layout/label allowed-label)]
          (emit-expr value env (assoc ctx :tail? false))
          [0x49 0x89 0xc0 0x41 0x51]             ; r8=request; push r9
          (when align? [0x50])
          [0xbe] (le32 cap-id)                    ; esi=cap-id
          [0xba] (le32 kind)                      ; edx=request kind
          [0xb9] (le32 kind)                      ; ecx=result kind
          [0x4c 0x89 0xcf 0x41 0xff 0x91] (le32 128)
          (when align? [0x48 0x83 0xc4 0x08])
          [0x41 0x59]))))

(def ^:private heap-call-offsets
  {'pair 56 'pair-first 64 'pair-second 72
   'kgraph-assert! 80 'kgraph-get 88 'kgraph-count 96 'kgraph-entity-at 104
   ;; A string value IS a pair(offset,length) handle -- string-byte-length
   ;; is exactly pair-second, no new host function needed.
   'string-byte-length 72
   'string=? 112 'string-concat 120
   ;; General string-substring. The ascii-literal fast path above handles the
   ;; literal case without a host call; every other shape needs one, because
   ;; only the host can read the boundary bytes.
   'string-substring 136
   ;; string-code-point-at: scalar result, so nothing is allocated at all.
   'string-code-point-at 144
   ;; vector-i64 (ADR-2608030300's parity gap). A vector VALUE is a one-word
   ;; handle into the host's vector table, exactly as a pair value is -- so
   ;; every operation is an ordinary context call and this backend needs no
   ;; new value representation, no new register discipline, and no new
   ;; instruction encoding. The host owns bounds, capacity and copying;
   ;; `vector-new-empty` is not a KIR operation but this lowering's own
   ;; construction primitive (see `vector-new` in emit-expr).
   'vector-new-empty 152 'vector-conj 160 'vector-count 168
   'vector-at 176 'vector-assoc 184 'vector-drop 192})

;; `vector-f64-*` is the SAME host table. A native f64 is already an i64 word
;; carrying an IEEE-754 bit pattern (ADR-2608030300: "no new value
;; representation, only i64 words"), so an f64 vector is a vector of those
;; words and needs no second arena, no second set of offsets, and no element
;; tagging. The two KIR op families stay distinct because the reference
;; interpreter validates their elements differently; below this line they are
;; one operation each.
(def ^:private vector-op-aliases
  '{vector-f64-new vector-new vector-f64-conj vector-conj
    vector-f64-count vector-count vector-f64-at vector-at
    vector-f64-assoc vector-assoc vector-f64-drop vector-drop
    vector-f64-get vector-get})

(defn- emit-heap-call [op args env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        offset (get heap-call-offsets op)
        argc (count args)
        ;; Evaluate each arg left-to-right onto the stack (mirrors emit-call's
        ;; push shape), then pop them off in reverse into rsi/rdx/rcx/r8 (skip
        ;; index 0 = rdi, reserved below for the context pointer moved from
        ;; r9) -- net stack effect is zero, so `align?` still reads the
        ;; original (pre-call) temp-depth exactly like the pair-only version.
        values (emit-pushed-arguments args env ctx temp-depth)
        pops (mapcat #(nth arg-pops (inc %)) (reverse (range argc)))
        align? (even? temp-depth)]
    (vec (concat values pops [0x41 0x51] (when align? [0x50])
                 [0x4c 0x89 0xcf]
                 ;; `call qword ptr [r9+disp]`. The disp8 form (ModRM 0x51)
                 ;; takes a SIGNED byte, so an offset above 127 silently
                 ;; becomes negative and calls the wrong slot -- 136 reads as
                 ;; -120. Offsets past 127 therefore take the disp32 form
                 ;; (ModRM 0x91), which is what the typed-cap-call path at
                 ;; offset 128 already uses. Offsets at or below 127 keep the
                 ;; shorter encoding, byte for byte as before.
                 (if (<= offset 127)
                   [0x41 0xff 0x51 offset]
                   (concat [0x41 0xff 0x91] (le32 offset)))
                 (when align? [0x48 0x83 0xc4 0x08]) [0x41 0x59]))))

(defn- emit-kernel-load-u8 [[base length index] maximum env {:keys [temp-depth] :as ctx}]
  ;; Evaluate exactly once, then enforce a non-null base, an unsigned index
  ;; below length, and the operation profile's maximum transfer
  ;; bytes. Every violation reaches UD2 before memory is touched.
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "kernel-load-u8-trap")
        end-label (fresh-label counter "kernel-load-u8-end")]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2))
        [0x59 0x5a                              ; rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x85 0xd2]
        [(layout/relative-branch :x86-64/jz-rel32 trap-label)]
        [0x48 0x39 0xc8]
        [(layout/relative-branch :x86-64/jae-rel32 trap-label)]
        [0x0f 0xb6 0x04 0x02]
        [(layout/relative-branch :x86-64/jmp-rel8 end-label)
         (layout/label trap-label)]
        [0x0f 0x0b]
        [(layout/label end-label)]))))

;; `(kernel-subregion base length offset sublen)` -> base+offset, trapping
;; unless the sub-window fits inside the parent window.
;;
;; The load/store checks above constrain an index within a DECLARED length,
;; and the caller supplies both that base and that length. Narrowing a region
;; by hand -- `(fnv (+ base object-offset) object-length)`, the shape six
;; aiueos objects use -- therefore produced a window nothing had checked. This
;; makes the derivation itself checked, so a correct entry window implies
;; every window derived from it is correct.
;;
;; Overflow-free by construction, and without a scratch register: `offset >
;; length` traps first, so `sub rcx,rdi` (length is dead after that compare)
;; cannot underflow, and `sublen` is compared against that remainder instead
;; of against `offset + sublen`, which a hostile pair could wrap. Every
;; comparison is unsigned (`ja`), so a negative i64 arrives as a huge unsigned
;; value and trips the check rather than passing a signed one.
;;
;; Displacements, from the end of each jump to the UD2 at +36:
;;   +0  test rdx,rdx   +3  jz  (+27)   +9  cmp rdi,rcx  +12 ja (+18)
;;   +18 sub rcx,rdi    +21 cmp rax,rcx +24 ja (+6)      +30 lea rax,[rdx+rdi]
;;   +34 jmp +2         +36 ud2         +38 skip
(defn- emit-kernel-subregion [[base length offset sublen] env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "kernel-subregion-trap")
        end-label (fresh-label counter "kernel-subregion-end")]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr offset env (update ctx :temp-depth + 2)) [0x50]
        (emit-expr sublen env (update ctx :temp-depth + 3))
        [0x5f 0x59 0x5a 0x48 0x85 0xd2]
        [(layout/relative-branch :x86-64/jz-rel32 trap-label)]
        [0x48 0x39 0xcf]
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x29 0xf9 0x48 0x39 0xc8]
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x8d 0x04 0x3a]
        [(layout/relative-branch :x86-64/jmp-rel8 end-label)
         (layout/label trap-label)]
        [0x0f 0x0b]
        [(layout/label end-label)]))))

(defn- emit-kernel-store-u8 [[base length index value] maximum env {:keys [temp-depth] :as ctx}]
  ;; Evaluate once and perform the same null/length/index checks as load-u8.
  ;; AL is stored only after every check succeeds; RAX remains the expression
  ;; result. Invalid writes trap before mutating memory.
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "kernel-store-u8-trap")
        end-label (fresh-label counter "kernel-store-u8-end")]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2)) [0x50]
        (emit-expr value env (update ctx :temp-depth + 3))
        [0x5f 0x59 0x5a                         ; rdi=index, rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x85 0xd2]
        [(layout/relative-branch :x86-64/jz-rel32 trap-label)]
        [0x48 0x39 0xcf]
        [(layout/relative-branch :x86-64/jae-rel32 trap-label)]
        [0x88 0x04 0x3a]
        [(layout/relative-branch :x86-64/jmp-rel8 end-label)
         (layout/label trap-label)]
        [0x0f 0x0b]
        [(layout/label end-label)]))))

;; `kernel-load-u32`/`kernel-store-u32` are `kotoba.compiler.frontend`'s
;; `kernel-memory-operations` -- the portable half of the kernel surface, as
;; opposed to `kernel-privileged-operations` (cr2/cr3/invlpg/cli/sti/hlt/pause/
;; out/in), which name x86 facilities AArch64 has no counterpart for and are
;; legitimately x86-only. Both u32 forms already existed on AArch64; their
;; absence here meant a program the frontend admitted for
;; `x86_64-aiueos-kernel-v1` was rejected only much later, by `finalize`, as an
;; "unknown call target".
;;
;; The checks mirror `emit-kernel-load-u8` exactly -- profile maximum, non-null
;; base, in-range index -- with ONE deliberate difference matching AArch64's
;; own `bounds-check-u32`: a four-byte access needs `index + 4 <= length`, not
;; `index < length`, so the last three bytes of a buffer cannot be read or
;; written past. `lea` computes `index + 4` without disturbing the index, and
;; the comparison is unsigned (`ja`), so an index near 2^64 wraps into the trap
;; rather than out of it.
;;
;; Every `rel32` below is the distance from the end of its own jump to the UD2,
;; recomputed for this body's instruction lengths rather than copied from the
;; u8 forms, whose displacements differ because their move encodings do.
(defn- emit-kernel-load-u32 [[base length index] maximum env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "kernel-load-u32-trap")
        end-label (fresh-label counter "kernel-load-u32-end")]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2))
        [0x59 0x5a                              ; rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x85 0xd2]
        [(layout/relative-branch :x86-64/jz-rel32 trap-label)]
        [0x48 0x8d 0x70 0x04 0x48 0x39 0xce]
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x8b 0x04 0x02]
        [(layout/relative-branch :x86-64/jmp-rel8 end-label)
         (layout/label trap-label)]
        [0x0f 0x0b]
        [(layout/label end-label)]))))

(defn- emit-kernel-store-u32 [[base length index value] maximum env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "kernel-store-u32-trap")
        end-label (fresh-label counter "kernel-store-u32-end")]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2)) [0x50]
        (emit-expr value env (update ctx :temp-depth + 3))
        [0x5f 0x59 0x5a                         ; rdi=index, rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x48 0x85 0xd2]
        [(layout/relative-branch :x86-64/jz-rel32 trap-label)]
        [0x48 0x8d 0x77 0x04 0x48 0x39 0xce]
        [(layout/relative-branch :x86-64/ja-rel32 trap-label)]
        [0x89 0x04 0x3a]
        [(layout/relative-branch :x86-64/jmp-rel8 end-label)
         (layout/label trap-label)]
        [0x0f 0x0b]
        [(layout/label end-label)]))))

(defn- emit-kernel-out [[port value] width env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr port env ctx) [0x50]
                 (emit-expr value env (update ctx :temp-depth inc))
                 [0x5a] (if (= width 8) [0xee] [0xef])))))

;; The READ half of port I/O, and the reason it exists: PCI configuration
;; space is reached by writing an address to port 0xCF8 and then READING port
;; 0xCFC. With `kernel-out-*` alone, that second step had no spelling in
;; Kotoba, so PCI enumeration -- and with it every device driver -- could only
;; live in C.
;;
;; One argument, so unlike `emit-kernel-out` nothing needs to be spilled: the
;; port arrives in `rax` and is moved to `rdx`, whose low half `dx` is the only
;; register `in` will take a dynamic port from. A port wider than 16 bits is
;; truncated by the instruction, exactly as `out` already truncates it.
;;
;; The result is zero-extended to a full 64-bit i64, which is what the caller's
;; `:i64` type promises:
;;   * u8 -- `in al,dx` writes ONLY `al`, leaving bits 63:8 whatever the port
;;     expression left in `rax`. `xor eax,eax` first clears all 64 bits (a
;;     32-bit write zeroes 63:32), so the byte arrives clean.
;;   * u32 -- `in eax,dx` writes `eax`, and a 32-bit write zeroes 63:32 by
;;     itself. No clearing instruction is emitted, because emitting one into a
;;     kernel would be a byte that does nothing.
(defn- emit-kernel-in [[port] width env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr port env ctx)
                 [0x48 0x89 0xc2]                        ; mov rdx,rax  (port -> dx)
                 (if (= width 8)
                   [0x31 0xc0                            ; xor eax,eax
                    0xec]                                ; in al,dx
                   [0xed])))))                           ; in eax,dx

;; Model-specific registers. `rdmsr`/`wrmsr` both take the register index in
;; `ecx`, and both carry the 64-bit value SPLIT across two 32-bit registers --
;; high half in `edx`, low half in `eax`. That split is the only thing here
;; that is not a transcription of `emit-kernel-in`, and it is the whole
;; difficulty: an i64 in this backend is one register, so a read has to
;; reassemble and a write has to take apart.
;;
;; Reassembly is `(edx << 32) | eax`, and it is exact rather than approximate
;; because of a property of x86-64 that has to be relied on deliberately: a
;; 32-bit destination write ZEROES bits 63:32 of the containing 64-bit
;; register. `rdmsr` writes `eax` and `edx`, so after it `rax` is the low half
;; zero-extended and `rdx` is the high half zero-extended -- no garbage in
;; either upper half, and therefore no masking instruction needed before the
;; shift. `shl rdx,32` then moves the high half into place with zeros below
;; it, and `or` merges.
;;
;; That this is `or` over zero-extended halves, and not (say) a sign-extending
;; move of `eax` followed by an add, is what makes an MSR with bit 63 set
;; come out right. IA32_EFER is small, but IA32_APIC_BASE on a machine with
;; more than 4 GiB of physical address space is not, and several MSRs are
;; defined with bit 63 as an enable or lock. A sign-extended low half would
;; have filled 63:32 with ones and then `or`ed the real high half into an
;; already-saturated field: every such register would read back as -1's upper
;; word, silently. The negative i64 that a bit-63 MSR produces is the correct
;; result -- the bit pattern is exact, and `:i64` in this language is signed.
(defn- emit-kernel-read-msr [[index] env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr index env ctx)
                 [0x48 0x89 0xc1                         ; mov rcx,rax  (index -> ecx)
                  0x0f 0x32                              ; rdmsr        -> edx:eax
                  0x48 0xc1 0xe2 0x20                    ; shl rdx,32
                  0x48 0x09 0xd0]))))                    ; or  rax,rdx

;; The write direction, spilling its first operand exactly as `emit-kernel-out`
;; does because it likewise has two: the index is pushed, the value is
;; evaluated into `rax`, and the index is popped into `rcx` -- where `wrmsr`
;; wants it -- after the value expression has finished clobbering registers.
;;
;; Taking the value apart needs no mask either, for the mirror-image reason:
;; `wrmsr` READS only `eax` and `edx`, so the upper 32 bits of `rax` are
;; ignored by the instruction and the low half needs no isolating. Only the
;; high half has to be produced, by copying and shifting down.
;;
;; `rax` is left holding the value that was written, which is what
;; `emit-kernel-out` leaves and therefore what a caller who binds the result
;; of a kernel write already expects.
(defn- emit-kernel-write-msr [[index value] env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr index env ctx) [0x50]        ; push index
                 (emit-expr value env (update ctx :temp-depth inc))
                 [0x59                                   ; pop rcx      (index -> ecx)
                  0x48 0x89 0xc2                         ; mov rdx,rax
                  0x48 0xc1 0xea 0x20                    ; shr rdx,32   (high half)
                  0x0f 0x30]))))                         ; wrmsr        <- edx:eax

;; CPU feature detection. `cpuid` reads TWO inputs -- the leaf in `eax`, the
;; subleaf in `ecx` -- and writes ALL FOUR of `eax`/`ebx`/`ecx`/`edx`. The
;; language surface is four arity-2 primitives, one per result register, each
;; executing its own `cpuid`; `which` selects the register to leave in `rax`.
;;
;; THE `rbx` PROBLEM, which is the only real difficulty here. `rbx` is
;; callee-saved in SysV, and no other operator in this backend touches it --
;; `cpuid` is the first instruction emitted here that does -- so
;; `emit-function`'s prologue never saves it and never needed to. That is
;; correct for every other operator and catastrophic for this
;; one: `cpuid` writes `ebx` unconditionally, whether or not the caller asked
;; for it, so a `(kernel-cpuid-eax ...)` that never mentions `ebx` would still
;; return to the loader with the loader's `rbx` destroyed. The corruption
;; surfaces wherever that C frame next reads its own saved register -- an
;; arbitrary distance from the `cpuid`, in code that has nothing to do with
;; feature detection. `push rbx` / `pop rbx` around the instruction is what
;; makes all four primitives ABI-clean.
;;
;; The save is emitted AFTER both operand expressions, not before, and that
;; ordering is deliberate: `ctx`'s `:temp-depth` is what keeps the stack
;; 16-byte aligned at any `call` an operand might contain, and an extra
;; unaccounted push before those expressions would flip that parity. Nothing
;; between `push rbx` and `pop rbx` calls anything, so that stack slot needs no
;; accounting; the sequence as a whole is stack-neutral (push leaf / pop leaf,
;; push rbx / pop rbx), so nothing downstream sees it either.
;;
;; The result register is moved with a 32-BIT `mov` (`89 /r`), which is both
;; the shortest encoding and the zero-extension: a 32-bit destination write
;; zeroes bits 63:32 of the containing 64-bit register. `cpuid` itself writes
;; the four 32-bit registers, so `rax`/`rbx`/`rcx`/`rdx` already hold their
;; results zero-extended before anything is moved -- and `mov eax,ebx` then
;; re-establishes the same property in `rax`. So NO MASK IS NEEDED anywhere,
;; and every `cpuid` result arrives as a non-negative i64 in [0, 2^32).
;; That matters for the comparison the aiueos NX probe actually makes: the
;; maximum-extended-leaf check is `eax < 0x80000001`, and 0x80000001 read as a
;; SIGNED 64-bit value is a large positive number only because the upper half
;; is known zero. A sign-extended result would have made it negative and the
;; check would have inverted.
;;
;; `-eax` emits no move at all: the result is already in `rax`. An explicit
;; `mov eax,eax` would be a byte that does nothing, and `emit-kernel-in`
;; already established that this backend does not emit those into a kernel.
;; The move must precede `pop rbx`, which is only load-bearing for `-ebx` --
;; restoring the caller's `rbx` first would discard the very value asked for.
(defn- emit-kernel-cpuid [[leaf subleaf] which env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr leaf env ctx) [0x50]         ; push leaf
                 (emit-expr subleaf env (update ctx :temp-depth inc))
                 [0x48 0x89 0xc1                         ; mov rcx,rax  (subleaf -> ecx)
                  0x58                                   ; pop rax      (leaf    -> eax)
                  0x53                                   ; push rbx     (callee-saved)
                  0x0f 0xa2]                             ; cpuid        -> eax,ebx,ecx,edx
                 (case which                             ; 32-bit mov zero-extends
                   :eax []                               ;   already in rax
                   :ebx [0x89 0xd8]                      ;   mov eax,ebx
                   :ecx [0x89 0xc8]                      ;   mov eax,ecx
                   :edx [0x89 0xd0])                     ;   mov eax,edx
                 [0x5b]))))                              ; pop rbx      (restore)

;; A string VALUE is a pair(offset, length) handle -- offset addresses a
;; UTF-8 byte range either in the compiled artifact's own code+literal-data
;; region (non-negative) or in the runtime string pool (negative, see
;; tools/kexe_loader.c's checked_string_concat), uniformly resolved host-side.
;; A literal's bytes are appended once per DISTINCT content to the artifact's
;; :code array; its offset is only known once every function's code size is
;; summed, so this emits a deferred {:string-literal content} token
;; (finalize resolves it, token-size already reserves the 10 bytes a
;; resolved movabs needs) for just the offset half -- length is already
;; known here, at literal-encounter time, so needs no deferral. Mirrors
;; emit-heap-call's 2-arg (pair) shape exactly, just with a deferred first
;; "arg".
(defn- emit-string-literal [content {:keys [temp-depth] :as ctx}]
  (let [length (count (utf8-bytes content))
        align? (even? temp-depth)]
    (vec (concat [{:string-literal content}] [0x50]       ; push offset (rax)
                 (into [0x48 0xb8] (le64 length)) [0x50]    ; push length (rax)
                 [0x5a] [0x5e]                               ; pop rdx=length; pop rsi=offset
                 [0x41 0x51] (when align? [0x50])
                 [0x4c 0x89 0xcf 0x41 0xff 0x51 56]          ; rdi=r9; call [r9+56] (pair_new)
                 (when align? [0x48 0x83 0xc4 0x08])
                 [0x41 0x59]))))


;; `string-substring` restricted to a literal whose bytes are all ASCII.
;;
;; `kotoba.kir`'s contract is byte-offset based BUT requires both offsets to be
;; code-point boundaries, trapping otherwise. Verifying that in general needs a
;; byte read from the string's region -- and emitted code can address neither
;; the code/literal region nor the runtime string pool, both of which the loader
;; owns behind `resolve_string_bytes`. A general implementation therefore needs
;; a new context callback, which changes the sealed, measured runtime identity.
;;
;; This slice needs none of that. When the operand is a literal whose bytes are
;; all < 0x80, EVERY byte offset is a code-point boundary, so the boundary rule
;; is discharged at compile time. What remains at runtime is a range check and
;; one pair construction -- `pair(offset + start, end - start)` -- because a
;; string value already IS a pair(offset,length) handle and a literal's offset
;; is non-negative, addressing the code+literal region directly.
;;
;; It is deliberately narrow in the same way the native record and variant
;; slices are, and it is what `string-from-i64` needs: that operation desugars
;; to a recursive helper whose whole body is a substring of the ASCII literal
;; "0123456789" at runtime indices.
;;
;; Anything else -- a pool string, a non-ASCII literal, a computed string --
;; falls through to `emit-call` and is reported as not implemented on this
;; backend, which is accurate and fail-closed.
(defn- ascii-literal? [form]
  (and (string? form) (every? #(< % 0x80) (map #(bit-and (int %) 0xff) (utf8-bytes form)))))

(defn- emit-string-substring-of-ascii-literal
  [content start-form end-form env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        trap-label (fresh-label counter "substring-trap")
        end-label (fresh-label counter "substring-end")
        length (count (utf8-bytes content))
        align? (even? temp-depth)
        operands (concat (emit-expr start-form env ctx) [0x50]
                         (emit-expr end-form env (update ctx :temp-depth inc)) [0x50]
                         [{:string-literal content}]      ; rax = literal byte offset
                         [0x59 0x5a])                     ; pop rcx=end ; pop rdx=start
        success (vec (concat [0x48 0x01 0xd0]             ; add rax,rdx  -> offset+start
                             [0x48 0x29 0xd1]             ; sub rcx,rdx  -> end-start
                             [0x48 0x89 0xc6]             ; mov rsi,rax
                             [0x48 0x89 0xca]             ; mov rdx,rcx
                             [0x41 0x51] (when align? [0x50])
                             [0x4c 0x89 0xcf 0x41 0xff 0x51 56]   ; mov rdi,r9 ; call [r9+56]
                             (when align? [0x48 0x83 0xc4 0x08])
                             [0x41 0x59]))]
    (vec (concat operands
                 [0x48 0x85 0xd2]
                 [(layout/relative-branch :x86-64/js-rel32 trap-label)]
                 [0x48 0x39 0xd1]
                 [(layout/relative-branch :x86-64/jl-rel32 trap-label)]
                 [0x48 0x81 0xf9] (le32 length)
                 [(layout/relative-branch :x86-64/jg-rel32 trap-label)]
                 success
                 [(layout/relative-branch :x86-64/jmp-rel8 end-label)
                  (layout/label trap-label)]
                 [0x0f 0x0b]
                 [(layout/label end-label)]))))

(declare emit-record-get-of-new-construction)

(defn- record-new-binding [value]
  (when (and (seq? value) (= 'record-new (first value)))
    (let [[_ type & field-exprs] value]
      ;; Structural only, matching what `emit-record-get-of-new` itself checks:
      ;; whether the FIELD TYPES are ones this backend can carry was already
      ;; decided by `kotoba.kir/only-native-word-typed-features?` before lowering
      ;; produced this HIR, so re-deriving it here would duplicate that gate.
      (when (and (vector? type) (= :record (first type)) (= 3 (count type))
                 (sequential? (nth type 2))
                 (= (count (nth type 2)) (count field-exprs)))
        [type (vec field-exprs)]))))

(declare emit-let)

;; Expand one `let` binding into slots. A record value expands into one binding
;; PER FIELD, and a field that is ITSELF a record-new expands again -- so a
;; nested record is FLATTENED into consecutive slots and still never needs a
;; runtime representation of its own, which is the property ADR 0062
;; established and this keeps.
;;
;; Returns [code env' next-d]. `env'` binds `name` to either `{:let-depth d}`
;; (an ordinary one-word slot) or `{:record-type T :record-fields {field
;; child-name}}`, whose children are themselves bound in `env'` under either
;; shape. Resolution therefore walks the same env every other binding uses.
(defn- expand-binding [name value env ctx d]
  (if-let [[type field-exprs] (record-new-binding value)]
    (let [field-names (map first (nth type 2))]
      (loop [fs field-exprs fns field-names i 0 dd d e env code [] fm {}]
        (if (seq fs)
          (let [child (symbol (str name "-" i))
                [c e' dd'] (expand-binding child (first fs) e ctx dd)]
            (recur (next fs) (next fns) (inc i) dd' e' (concat code c)
                   (assoc fm (first fns) child)))
          [code (assoc e name {:record-type type :record-fields fm}) dd])))
    [(concat (emit-expr value env (assoc ctx :tail? false :temp-depth d)) [0x50])
     (assoc env name {:let-depth d})
     (inc d)]))

;; The record a form denotes, or nil. A symbol bound to one, or a `record-get`
;; selecting a record-typed field of one -- which is what makes a chained
;; projection resolvable without the intermediate ever becoming a value.
(defn- resolve-record-binding [form env]
  (cond
    (symbol? form) (let [b (get env form)] (when (:record-fields b) b))
    (and (seq? form) (= 'record-get (first form)) (= 4 (count form)))
    (let [[_ _type value field] form]
      (when-let [b (resolve-record-binding value env)]
        (let [child (get (:record-fields b) field)]
          (when-let [cb (and child (get env child))]
            (when (:record-fields cb) cb)))))
    :else nil))

(defn- emit-let [bindings body env {:keys [temp-depth] :as ctx}]
  ;; Genuinely sequential: each binding's value is evaluated exactly once, in
  ;; source order, and pushed onto its own 8-byte stack slot before the next
  ;; binding (or the body) is emitted -- unlike a compile-time substitution
  ;; pass, an unreferenced or repeatedly-referenced side-effecting binding
  ;; (kgraph-assert!, cap-call, pair, ...) still runs exactly once, and a
  ;; binding referenced from inside an `if` branch still runs unconditionally
  ;; before the branch is chosen (ADR-2607198300 follow-up). The body
  ;; inherits ctx's own :tail? (a let's body is in tail position exactly
  ;; when the let itself is); binding values never are.
  ;;
  ;; Slots are counted from the depth the expansion reached, not from the
  ;; binding count, because one record binding occupies one slot per field --
  ;; transitively.
  (let [pairs (partition 2 bindings)]
    (loop [remaining pairs d temp-depth env env code []]
      (if-let [[name value] (first remaining)]
        (let [[c env' d'] (expand-binding name value env ctx d)]
          (recur (next remaining) d' env' (concat code c)))
        (let [body-code (emit-expr body env (assoc ctx :temp-depth d))
              slots (- d temp-depth)]
          (vec (concat code body-code
                       (when (pos? slots) (concat [0x48 0x81 0xc4] (le32 (* 8 slots)))))))))))


;; A record that CROSSES A FUNCTION BOUNDARY is the one shape flattening cannot
;; reach: a record is N slots and a function returns one word. It is boxed into
;; a pair chain -- pair(f0, pair(f1, ... pair(fN-1, 0))) -- which is one word,
;; and which needs no new primitive, no ABI change and no loader change: `pair`,
;; `pair-first` and `pair-second` are the arena contract this backend has had
;; since ADR 0062's own bounded-pair work.
;;
;; Both directions are source rewrites into forms this backend already emits, so
;; nothing new is encoded: the callee's `record-new` becomes the chain, and the
;; caller's projection becomes a walk of it.
;;
;; This costs arena cells, which are bounded at 4,096 per execution with no
;; collection. That is not a regression: a record could not cross a boundary at
;; all before, so no program that compiles today gains an allocation. It IS a
;; property of the new shape, and the reason ADR 0062 chose slots for the shapes
;; that do not need to escape -- those keep using slots and allocate nothing.
(defn- boxed-record-chain [field-exprs]
  (reduce (fn [rest-chain v] (list 'pair v rest-chain)) 0 (reverse field-exprs)))

(defn- boxed-record-projection [handle-form field-index]
  (list 'pair-first (nth (iterate (fn [f] (list 'pair-second f)) handle-form) field-index)))

;; The record NAME a declared result denotes, or nil.
;;
;; A signature's result reaches a backend in either of two spellings, and both
;; name the same record. `[:record :t/r [[:a :i64] ...]]` is the expanded form.
;; `[:ref :t/r]` is the schema reference the source wrote, which survives into
;; KIR unexpanded ON PURPOSE: expanding a reference in a SIGNATURE moved the
;; `:kir-sha256` of every module that used one, on every target including its
;; Wasm bytes, so `lower` leaves signatures alone and expands references only
;; inside expressions (a `record-new`/`record-get` therefore always carries the
;; expanded `[:record …]`). Reading only the expanded spelling here is why a
;; murakumo core that declares its record results by reference -- which is how
;; they are written throughout -- could not return a record at all.
(defn- record-result-name [result]
  (when (and (vector? result) (<= 2 (count result))
             (contains? #{:record :ref} (first result)))
    (second result)))

;; Box a `record-new` that is in TAIL position of a function declared to return
;; that record. Boxing is the same ADR 0062 pair chain a record result has always
;; crossed on; the only thing added here is REACHING the construction.
;;
;; Tail position is not a syntactic property of the outermost form. It propagates
;; into both branches of an `if`, into the body (never a binding's value) of a
;; `let`, and into the last subexpression of a `do` -- exactly the positions
;; `emit-expr` hands its own `:tail?` down to, so this rewrite and codegen agree
;; about where a function's value is produced. Everything else -- a call, a
;; parameter, a projection -- is already a one-word handle and is left alone.
;;
;; The record-new's own name must equal the declared result's, because that is
;; the only local evidence that this construction is the one the signature
;; promised: a `[:ref :t/r]` result carries no field list to compare against.
;; A mismatch is left unrewritten and fails loudly downstream rather than being
;; boxed into a shape the caller will walk with the wrong field count.
(defn- box-record-tails [form record-name]
  (if-let [[type field-exprs] (record-new-binding form)]
    (if (= (second type) record-name) (boxed-record-chain field-exprs) form)
    (cond
      (and (seq? form) (= 'if (first form)) (= 4 (count form)))
      (let [[_ test then else] form]
        (list 'if test
              (box-record-tails then record-name)
              (box-record-tails else record-name)))

      (and (seq? form) (= 'let (first form)) (= 3 (count form)))
      (list 'let (second form) (box-record-tails (nth form 2) record-name))

      (and (seq? form) (= 'do (first form)) (seq (rest form)))
      (let [args (vec (rest form))]
        (list* 'do (conj (pop args) (box-record-tails (peek args) record-name))))

      :else form)))

(defn- emit-record-get-of-new [type value-form field env ctx]
  ;; A record we already know -- bound by `let`, or selected out of one by an
  ;; earlier projection -- has each of its scalar fields in its own slot, so the
  ;; projection is an ordinary depth-relative read of the corresponding binding.
  (if-let [bound (resolve-record-binding value-form env)]
    (do
      (when-not (= type (:record-type bound))
        (throw (ex-info "record-get's schema must be identical to the schema its operand was bound with"
                        {:phase :x86-64 :expected type :actual (:record-type bound)})))
      (let [child (get (:record-fields bound) field)]
        (when-not child
          (throw (ex-info "record-get references an undeclared field"
                          {:phase :x86-64 :type type :field field})))
        (when (:record-fields (get env child))
          ;; The field is itself a record, so this projection yields a record.
          ;; That is only meaningful as the operand of a further record-get,
          ;; which `resolve-record-binding` handles without ever materialising
          ;; it; anywhere else there is no word to produce.
          (throw (ex-info "a record-valued projection may only appear as the operand of record-get"
                          {:phase :x86-64 :type type :field field})))
        (emit-expr child env ctx)))
    (if (or (and (seq? value-form) (symbol? (first value-form))
                 (contains? (:function-names ctx) (first value-form)))
            ;; A PARAMETER holding a record arrived boxed for the same reason a
            ;; call's result does: the caller had N slots and the ABI has one
            ;; word. `env` binds a parameter to its bare index (not the
            ;; `{:record-fields …}` map a flattened `let` binding gets), so a
            ;; symbol that resolves to a non-map binding here is precisely a
            ;; parameter -- and a record-typed one, since `record-get` type-checked
            ;; against this schema upstream. It needs no new representation: the
            ;; word loads through `load-param` like any other, and the walk below
            ;; is the same one the call path already uses.
            ;;
            ;; A `let` SLOT holding a boxed handle -- `(let [ends (mk x)]
            ;; (record-get … ends :hi0))`, which is how murakumo's plan cores
            ;; read a multi-field result -- is the SAME one word arriving by a
            ;; different route, so it walks the same chain. `expand-binding`
            ;; gives a slot `{:let-depth d}` and a FLATTENED record binding
            ;; `{:record-fields …}`; only the latter has its fields in separate
            ;; slots and is resolved above, so `:record-fields` (rather than
            ;; `map?`) is what distinguishes "this name is a word" from "this
            ;; name is N words". A parameter's bare index is a word too, and
            ;; both reach the same walk.
            ;;
            ;; This was held back one release (docs/adr/0001): `kotoba.verifier`
            ;; independently required a projection's operand to be a nested
            ;; `record-new` or a parameter, so an emitted path for a let slot
            ;; could not be reached through the compiler pipeline and nothing
            ;; would ever have executed it. kotoba-verifier ADR 0004 admits the
            ;; shape, so it is now reachable and executed on both ISAs.
            (and (symbol? value-form) (not (:record-fields (get env value-form)))
                 (contains? env value-form)))
      (let [fields (nth type 2)
            field-index (first (keep-indexed (fn [i [n _]] (when (= n field) i)) fields))]
        (when (nil? field-index)
          (throw (ex-info "record-get references an undeclared field"
                          {:phase :x86-64 :type type :field field})))
        (emit-expr (boxed-record-projection value-form field-index) env ctx))
      (emit-record-get-of-new-construction type value-form field env ctx))))

(defn- emit-record-get-of-new-construction [type value-form field env ctx]
  (when-not (seq? value-form)
    (throw (ex-info "record-get is only supported directly over a matching record-new construction on the native backend"
                    {:phase :x86-64 :type type})))
  (let [[record-op record-type & field-exprs] value-form
        fields (nth type 2)
        field-index (first (keep-indexed (fn [i [name _]] (when (= name field) i)) fields))]
    (when-not (= 'record-new record-op)
      (throw (ex-info "record-get is only supported directly over a matching record-new construction on the native backend"
                      {:phase :x86-64 :type type})))
    (when-not (= type record-type)
      (throw (ex-info "record-get's schema must be identical to its record-new operand's schema"
                      {:phase :x86-64 :expected type :actual record-type})))
    (when-not (= (count fields) (count field-exprs))
      (throw (ex-info "record-new does not supply exactly one value per declared field"
                      {:phase :x86-64 :type type})))
    (when (nil? field-index)
      (throw (ex-info "record-get references an undeclared field"
                      {:phase :x86-64 :type type :field field})))
    (let [names (mapv #(symbol (str "$record-field-" %)) (range (count fields)))
          bindings (vec (mapcat vector names field-exprs))]
      (emit-let bindings (nth names field-index) env ctx))))

;; ADR 0063: the second native value-representation increment, immediately
;; following ADR 0062's record. A native sealed variant, like the record, has
;; NO independent heap/pointer representation -- it is rewritten at codegen
;; time into TWO synthetic 8-byte stack slots on the SAME synthetic-stack-slot
;; scheme `emit-let`/`load-let` already implement: slot 0 = discriminant (the
;; case's 0-based ordinal index within the type's own declared `cases`
;; vector, resolved at COMPILE TIME the same way `emit-record-get-of-new`
;; resolves a field name to its index), slot 1 = payload (the ONE word every
;; admitted case needs, since every admitted payload type -- `:i64`/`:bool`
;; -- is already a uniform 8-byte word on this backend, matching the record
;; ADR's own "no narrower packing" finding; a tag-only/"unit" case still
;; reserves this SAME word -- its value is simply never bound/read by that
;; case's own branch body, exactly the way a Rust `enum` variant without a
;; payload still occupies its union's full size). Both slots are pushed
;; UNCONDITIONALLY and exactly once (matching `emit-let`'s own side-
;; effecting-binding discipline: the payload expression runs once regardless
;; of which case it belongs to or whether that case's branch reads it).
;;
;; Dispatch is a REAL runtime compare-and-branch chain over the stored
;; discriminant word, not a compile-time selection: for each of the N
;; declared cases, in order, `cmp rax,i ; je case_i`, falling through past
;; ALL N comparisons to a defensive UD2 trap if none match. The codegen does
;; NOT special-case away any comparison based on a directly-nested
;; `variant-new`'s literal tag being known at that particular call site (see
;; `emit-variant-match-of-new` below) -- every one of the N comparisons is
;; always present in the emitted bytes, for every call site, regardless of
;; which case that site happens to construct. See docs/adr/0063-* for the
;; full design rationale, including why the UD2 fallback is unreachable from
;; any program this compiler's own pipeline will admit, sign, or execute (a
;; MULTI-LAYER, not just single-layer, guarantee: frontend's own tag
;; declaration check, this backend's own re-derived ordinal lookup,
;; `kotoba.verifier`'s independent re-derivation, AND -- unique to
;; this repository's native track -- `kotoba.verifier.signing/sign` and
;; `signing/verify` BOTH unconditionally re-run the full verifier before
;; producing or trusting a signature, so even a hand-crafted artifact
;; bypassing `frontend/analyze` cannot reach real execution with a
;; discriminant the type system did not itself validate).

;; How many slots a payload of this type occupies once flattened -- a record is
;; its fields transitively, anything else is one word.
(defn- type-slot-width [t]
  (if (and (vector? t) (= 3 (count t)) (= :record (first t)) (sequential? (nth t 2)))
    (reduce + (map (comp type-slot-width second) (nth t 2)))
    1))

;; Describe a region of already-pushed slots starting at `base` as a value of
;; `type`. The dispatch pushed the slots; this only names them, so a record case
;; sees a record and a scalar case sees a word.
(defn- bind-over-slots [name type base env]
  (if (and (vector? type) (= 3 (count type)) (= :record (first type)) (sequential? (nth type 2)))
    (loop [fs (nth type 2) i 0 d base e env fm {}]
      (if (seq fs)
        (let [[fname ftype] (first fs)
              child (symbol (str name "-" i))]
          (recur (next fs) (inc i) (+ d (type-slot-width ftype))
                 (bind-over-slots child ftype d e) (assoc fm fname child)))
        (assoc e name {:record-type type :record-fields fm})))
    (assoc env name {:let-depth base})))

(defn- emit-variant-dispatch
  "ORDINAL-EXPR and PAYLOAD-EXPR are ordinary KIR expressions (ORDINAL-EXPR
  is normally a compile-time-computed plain integer, but nothing here
  requires that -- see the direct low-level trap test in
  native_executor_test.clj, which passes an out-of-range integer here
  directly, bypassing `emit-variant-match-of-new`'s own tag-lookup entirely,
  specifically to exercise this dispatch chain's fallback trap with a value
  no admitted `.kotoba` program could ever produce). BRANCH-SPECS is an
  ordered vector of `{:binder sym :body kir-form}`, one per declared case, in
  the SAME order as the discriminant ordinal each one corresponds to."
  [ordinal-expr payload-expr branch-specs env {:keys [temp-depth] :as ctx}]
  (let [resolve-locally? (nil? (:mir-label-counter ctx))
        counter (or (:mir-label-counter ctx) (atom -1))
        ctx (assoc ctx :mir-label-counter counter)
        tail-ctx (assoc ctx :tail? false)
        push-ordinal (vec (concat (emit-expr ordinal-expr env tail-ctx) [0x50]))
        payload-depth (inc temp-depth)
        ;; The payload region is sized by the WIDEST declared case, not by the
        ;; constructed one. Only the constructed case is materialised, but every
        ;; branch is still emitted, and a branch whose declared payload is wider
        ;; would otherwise name slots that were never pushed -- emitting a load
        ;; whose displacement runs off the frame. Unreachable, but not something
        ;; to emit; padding makes it structurally impossible.
        payload-slots (reduce max 1 (map #(type-slot-width (:payload-type %)) branch-specs))
        [payload-code _ payload-end] (expand-binding '$variant-payload payload-expr env tail-ctx payload-depth)
        push-payload (vec (concat payload-code
                                  (mapcat (fn [_] (concat (into [0x48 0xb8] (le64 0)) [0x50]))
                                          (range (max 0 (- payload-slots (- payload-end payload-depth)))))))
        dispatch-depth (+ temp-depth 1 payload-slots)
        load-tag (load-let temp-depth dispatch-depth)
        n (count branch-specs)
        case-labels (mapv (fn [i] (fresh-label counter (str "variant-case-" i))) (range n))
        end-label (fresh-label counter "variant-end")
        body-ctx (assoc ctx :temp-depth dispatch-depth)
        ;; add rsp, N -- drops the ordinal slot and the payload region this
        ;; dispatch alone pushed, run at the end of EVERY case body before
        ;; falling through to whatever follows (mirrors `emit-let`'s own
        ;; final pop, just deferred until after the SELECTED branch runs
        ;; instead of after a single body expression).
        cleanup (vec (concat [0x48 0x81 0xc4] (le32 (* 8 (inc payload-slots)))))
        body-codes (mapv (fn [{:keys [binder body payload-type]}]
                           (vec (emit-expr body
                                           (bind-over-slots binder payload-type payload-depth env)
                                           body-ctx)))
                         branch-specs)
        trap [0x0f 0x0b]                                  ; ud2
        compare-block
        (vec (mapcat
              (fn [i]
                (concat [0x48 0x3d] (le32 i)
                        [(layout/relative-branch :x86-64/jz-rel32
                                                 (nth case-labels i))]))
              (range n)))
        body-blocks
        (vec (mapcat
              (fn [i body-code]
                (concat [(layout/label (nth case-labels i))]
                        body-code cleanup
                        (when (< i (dec n))
                          [(layout/relative-branch :x86-64/jmp-rel32 end-label)])))
              (range n) body-codes))]
    (let [tokens (vec (concat push-ordinal push-payload load-tag compare-block trap body-blocks
                              [(layout/label end-label)]))]
      ;; `emit-variant-dispatch` predates the layout seam and one executor
      ;; qualification deliberately calls this private helper directly to emit
      ;; an impossible discriminant. Preserve that byte-vector contract when
      ;; no function-owned label counter was supplied; production recursion
      ;; keeps tokens deferred until whole-function layout.
      (if resolve-locally? (finalize tokens 0 0 {} {}) tokens))))

;; The public-facing admitted shape, mirroring `emit-record-get-of-new`
;; exactly: `variant-match`'s value operand must be a DIRECTLY-nested,
;; SAME-schema `variant-new` (never a parameter, a `let`-bound name, an
;; `if`, or a different-schema construction) -- a variant value never
;; escapes past this one call, so no new host arena, no new function-
;; boundary ABI (variants never appear in `param-types` or `result`, exactly
;; matching the record ADR's own restriction), and no lifetime question to
;; answer. `branches` arrives in the SAME order as the type's own declared
;; `cases` (frontend's shared, unchanged `variant-match` validation already
;; enforces `(= (mapv first cases) (mapv first branches))`), so the branch at
;; index i always corresponds to the case whose ordinal is i.
(defn- emit-variant-match-of-new [type value-form branches env ctx]
  (when-not (seq? value-form)
    (throw (ex-info "variant-match is only supported directly over a matching variant-new construction on the native backend"
                    {:phase :x86-64 :type type})))
  (let [[ctor-op ctor-type tag payload-expr] value-form
        cases (nth type 2)
        ordinal (first (keep-indexed (fn [i [case-tag _]] (when (= case-tag tag) i)) cases))]
    (when-not (= 'variant-new ctor-op)
      (throw (ex-info "variant-match is only supported directly over a matching variant-new construction on the native backend"
                      {:phase :x86-64 :type type})))
    (when-not (= type ctor-type)
      (throw (ex-info "variant-match's schema must be identical to its variant-new operand's schema"
                      {:phase :x86-64 :expected type :actual ctor-type})))
    (when (nil? ordinal)
      (throw (ex-info "variant-new references an undeclared case"
                      {:phase :x86-64 :type type :tag tag})))
    (when-not (= (count cases) (count branches))
      (throw (ex-info "variant-match does not supply exactly one branch per declared case"
                      {:phase :x86-64 :type type})))
    (let [branch-specs (mapv (fn [[case-tag case-payload-type] [_ binder body]]
                               {:binder binder :body body :payload-type case-payload-type})
                             cases branches)]
      (emit-variant-dispatch ordinal payload-expr branch-specs env ctx))))

(defn emit-expr [form env {:keys [param-count pad? temp-depth] :as ctx}]
  (cond
    ;; `integer?` alone does not reliably recognize a cljs `bigint` (see
    ;; `kotoba.kir.cljs-i64`'s own namespace docstring) -- mirrors
    ;; `kotoba.wasm.core`'s identical dispatch guard.
    #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form)))
    (into [0x48 0xb8] (le64 form))
    ;; A literal `true`/`false` -- the only source of a genuine `:bool`
    ;; VALUE in this frontend's type system (see
    ;; `emit-record-get-of-new`'s own doc comment above) -- is just the i64
    ;; word 1/0, encoded through the SAME `le64` path an ordinary integer
    ;; literal uses; this backend has never distinguished a narrower bool
    ;; width from a full 8-byte word anywhere else. MUST be checked before
    ;; the generic `:else`, which would otherwise try to sequentially
    ;; destructure a bare boolean (`(let [[op & args] true])`) and throw.
    (boolean? form) (into [0x48 0xb8] (le64 (if form 1 0)))
    (string? form) (emit-string-literal form ctx)

;; A keyword is carried as the same one-word `pair(offset,length)` handle a
    ;; string is, over its PRINTED text (`:z` -> the four bytes `:z`), which is
    ;; the representation `kotoba.wasm.core` already chose for keyword literals.
    ;; It needs nothing the string literal path does not already have, and that
    ;; is what makes `:keyword` a one-word field type the gate can admit.
    ;;
    ;; A keyword and the string of the same text are therefore indistinguishable
    ;; at runtime here. That is safe because the frontend types them apart long
    ;; before this point -- a keyword cannot reach a position expecting a string
    ;; -- and this backend has no descriptor to carry the distinction in.
    ;;
    ;; This admits keyword VALUES, not keyword OPERATIONS: `keyword-name` and
    ;; `keyword-from-string` would need a general substring and concatenation
    ;; over a runtime handle, and are not implemented.
    (keyword? form) (emit-string-literal (str form) ctx)
    (symbol? form)
    (let [binding (get env form)]
      ;; A record binding is not a value: it has one slot PER FIELD and no
      ;; single word to load. Reaching `load-let` with its nil `:let-depth`
      ;; would only produce a NullPointerException, naming nothing.
      (when (:record-fields binding)
        (throw (ex-info "a record-valued binding may only appear as the operand of record-get"
                        {:phase :x86-64 :binding form})))
      (if (map? binding)
        (load-let (:let-depth binding) temp-depth)
        (load-param binding param-count pad? temp-depth)))
    :else
    (let [[op & args] form]
      (cond
        (= op 'let)
        (emit-let (first args) (second args) env ctx)

        (= op 'if)
        (let [[test then else] args
              ;; A direct emit-expr test may omit the function-owned counter;
              ;; establish one here and thread the SAME counter into nested
              ;; branches. emit-function supplies it for the normal path.
              counter (or (:mir-label-counter ctx) (atom -1))
              ctx (assoc ctx :mir-label-counter counter)
              else-label (fresh-label counter "if-else")
              end-label (fresh-label counter "if-end")
              test-code (emit-expr test env (assoc ctx :tail? false))
              then-code (emit-expr then env ctx)
              else-code (emit-expr else env ctx)]
          (vec (concat test-code [0x48 0x85 0xc0]
                       [(layout/relative-branch :x86-64/jz-rel32 else-label)]
                       then-code
                       [(layout/relative-branch :x86-64/jmp-rel32 end-label)
                        (layout/label else-label)]
                       else-code
                       [(layout/label end-label)])))

        ;; `do`: emit each subexpression in order; each leaves its result in rax,
        ;; the next overwrites it, so only the last value survives while every
        ;; subexpression's side effects run exactly once, in order. All but the
        ;; last are in non-tail position.
        (= op 'do)
        (let [n (count args)]
          (vec (mapcat (fn [i arg]
                         (emit-expr arg env (if (= i (dec n)) ctx (assoc ctx :tail? false))))
                       (range n) args)))

        (= op 'cap-call)
        (emit-cap-call (first args) (second args) env ctx)

        (= op 'typed-cap-call)
        (let [[cap-id request-type result-type request] args]
          (cond
            (= :i64 request-type result-type)
            (emit-cap-call cap-id request env ctx)
            (= :string request-type result-type)
            (emit-typed-cap-call cap-id 1 request env ctx)
            (= :option-i64 request-type result-type)
            (emit-typed-cap-call cap-id 2 request env ctx)
            (= :result-i64 request-type result-type)
            (emit-typed-cap-call cap-id 3 request env ctx)
            :else
            (throw (ex-info "native typed capability ABI does not support this boundary"
                            {:phase :x86-64 :request-type request-type
                             :result-type result-type}))))

        (= op 'option-some)
        (emit-heap-call 'pair [1 (first args)] env ctx)

        (= op 'option-none)
        (emit-heap-call 'pair [0 0] env ctx)

        (= op 'option-some?)
        (emit-heap-call 'pair-first [(first args)] env ctx)

        (= op 'option-value)
        (let [[value fallback] args
              tagged-value '__native_option_value]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'pair-second tagged-value)
                          fallback)
                    env ctx))

        (= op 'option-some-of)
        (emit-heap-call 'pair [1 (second args)] env ctx)

        (= op 'option-none-of)
        (emit-heap-call 'pair [0 0] env ctx)

        (= op 'option-some?-of)
        (emit-heap-call 'pair-first [(second args)] env ctx)

        (= op 'option-value-of)
        (let [[_type value fallback] args
              tagged-value '__native_generic_option_value]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'pair-second tagged-value)
                          fallback)
                    env ctx))

        (= op 'option-match)
        (let [[_type value none-body binder some-body] args
              tagged-value '__native_generic_option_match]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'let [binder (list 'pair-second tagged-value)]
                                some-body)
                          none-body)
                    env ctx))

        (= op 'result-ok)
        (emit-heap-call 'pair [1 (first args)] env ctx)

        (= op 'result-err)
        (emit-heap-call 'pair [0 (first args)] env ctx)

        (= op 'result-ok?)
        (emit-heap-call 'pair-first [(first args)] env ctx)

        (contains? '#{result-value result-error} op)
        (let [[value fallback] args
              tagged-value '__native_result_value
              ok? (list 'pair-first tagged-value)
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (if (= op 'result-value)
                      (list 'if ok? payload fallback)
                      (list 'if ok? fallback payload))
                    env ctx))

        (contains? '#{result-ok-of result-err-of} op)
        (emit-heap-call 'pair [(if (= op 'result-ok-of) 1 0) (second args)] env ctx)

        (= op 'result-ok?-of)
        (emit-heap-call 'pair-first [(second args)] env ctx)

        (contains? '#{result-value-of result-error-of} op)
        (let [[_type value fallback] args
              tagged-value '__native_generic_result_value
              ok? (list 'pair-first tagged-value)
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (if (= op 'result-value-of)
                      (list 'if ok? payload fallback)
                      (list 'if ok? fallback payload))
                    env ctx))

        (= op 'result-match-of)
        (let [[_type value ok-binder ok-body err-binder err-body] args
              tagged-value '__native_generic_result_match
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'let [ok-binder payload] ok-body)
                          (list 'let [err-binder payload] err-body))
                    env ctx))

        (= op 'record-get)
        (let [[type value-form field] args]
          (emit-record-get-of-new type value-form field env ctx))

        (= op 'record-new)
        (throw (ex-info "record-new is only supported as the direct operand of a matching record-get on the native backend"
                        {:phase :x86-64}))

        (= op 'variant-match)
        (let [[type value-form branches] args]
          (emit-variant-match-of-new type value-form branches env ctx))

        (= op 'variant-new)
        (throw (ex-info "variant-new is only supported as the direct operand of a matching variant-match on the native backend"
                        {:phase :x86-64}))

        ;; See `emit-string-substring-of-ascii-literal`. Any other shape falls
        ;; through and is reported as not implemented on this backend.
        (and (= op 'string-substring) (= 3 (count args))
             (ascii-literal? (first args)))
        (emit-string-substring-of-ascii-literal (first args) (second args) (nth args 2) env ctx)

        ;; The two string SEARCH operations. `kotoba.native.string-search`
        ;; explains why they are a source rewrite over the four string
        ;; callbacks this backend already has rather than a fifth one at a new
        ;; context offset, and why the scan walks code points instead of
        ;; bytes. Both ISAs consume the identical rewrite from that namespace,
        ;; so a divergence between them would have to be in the shared
        ;; operations underneath, not in the search itself.
        (and (= op 'string-contains?) (= 2 (count args)))
        (emit-expr (string-search/lower-contains args) env ctx)

        (and (= op 'string-replace-all) (= 3 (count args)))
        (emit-expr (string-search/lower-replace-all args) env ctx)

        (and (contains? '#{string-index-new string-index-count
                           string-index-contains string-index-get
                           string-index-assoc}
                         op)
             (contains? '{string-index-new 0 string-index-count 1
                          string-index-contains 2 string-index-get 2
                          string-index-assoc 3}
                        op)
             (= (count args)
                (get '{string-index-new 0 string-index-count 1
                       string-index-contains 2 string-index-get 2
                       string-index-assoc 3}
                     op)))
        (emit-expr (string-index/lower op args) env ctx)

        ;; An f64 vector operation IS the i64 one (see vector-op-aliases):
        ;; rewrite the head and re-dispatch, so there is exactly one lowering
        ;; per operation rather than two that must be kept in step.
        (contains? vector-op-aliases op)
        (emit-expr (cons (get vector-op-aliases op) args) env ctx)

        ;; KIR's vector-new is variadic; the context ABI is not. The arity is
        ;; static, so this expands to an empty vector plus one conj per
        ;; element -- and because each conj extends the arena region the
        ;; previous one just wrote, the host takes its copy-free append path
        ;; throughout, making construction linear rather than quadratic.
        (= op 'vector-new)
        (emit-expr (reduce (fn [acc item] (list 'vector-conj acc item))
                           (list 'vector-new-empty)
                           args)
                   env ctx)

        ;; vector-get is vector-at plus a total fallback, so it must not trap.
        ;; Both operands are bound first: the reference interpreter evaluates
        ;; each exactly once, and the index is read twice below. The fallback
        ;; appears once, so nesting cannot duplicate code exponentially.
        (= op 'vector-get)
        (let [[items-form index-form fallback-form] args
              items '__native_vector_get_items
              index '__native_vector_get_index]
          (emit-let [items items-form]
                    (list 'let [index index-form]
                          (list 'if (list 'if (list '< index 0)
                                          0
                                          (list '< index (list 'vector-count items)))
                                (list 'vector-at items index)
                                fallback-form))
                    env ctx))

        (contains? '#{pair pair-first pair-second
                      kgraph-assert! kgraph-get kgraph-count kgraph-entity-at
                      string-byte-length string=? string-concat
                      string-substring string-code-point-at
                      vector-new-empty vector-conj vector-count
                      vector-at vector-assoc vector-drop} op)
        (emit-heap-call op args env ctx)

        (= op 'kernel-load-u8)
        (emit-kernel-load-u8 args 512 env ctx)

        (= op 'kernel-load-u8-4k)
        (emit-kernel-load-u8 args 4096 env ctx)

        (= op 'kernel-load-u8-16k)
        (emit-kernel-load-u8 args 16384 env ctx)

        (= op 'kernel-subregion)
        (emit-kernel-subregion args env ctx)

        (= op 'kernel-store-u8)
        (emit-kernel-store-u8 args 512 env ctx)

        (= op 'kernel-store-u8-4k)
        (emit-kernel-store-u8 args 4096 env ctx)

        ;; Same 512-byte profile maximum `kotoba.native.aarch64`'s own u32
        ;; dispatch uses, so the two ISAs admit the identical buffer bound.
        (= op 'kernel-load-u32)
        (emit-kernel-load-u32 args 512 env ctx)

        (= op 'kernel-store-u32)
        (emit-kernel-store-u32 args 512 env ctx)

        (= op 'kernel-boot-info) [0x49 0x8b 0x41 0x50]
        (= op 'kernel-read-cr2) [0x0f 0x20 0xd0]
        (= op 'kernel-read-cr3) [0x0f 0x20 0xd8]
        (= op 'kernel-write-cr3)
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false)) [0x0f 0x22 0xd8]))
        (= op 'kernel-invlpg)
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false)) [0x0f 0x01 0x38]))
        (= op 'kernel-cli) [0xfa 0x31 0xc0]
        (= op 'kernel-sti) [0xfb 0x31 0xc0]
        (= op 'kernel-hlt) [0xf4 0x31 0xc0]
        (= op 'kernel-pause) [0xf3 0x90 0x31 0xc0]
        (= op 'kernel-out-u8) (emit-kernel-out args 8 env ctx)
        (= op 'kernel-out-u32) (emit-kernel-out args 32 env ctx)
        (= op 'kernel-in-u8) (emit-kernel-in args 8 env ctx)
        (= op 'kernel-in-u32) (emit-kernel-in args 32 env ctx)
        (= op 'kernel-read-msr) (emit-kernel-read-msr args env ctx)
        (= op 'kernel-write-msr) (emit-kernel-write-msr args env ctx)
        (= op 'kernel-cpuid-eax) (emit-kernel-cpuid args :eax env ctx)
        (= op 'kernel-cpuid-ebx) (emit-kernel-cpuid args :ebx env ctx)
        (= op 'kernel-cpuid-ecx) (emit-kernel-cpuid args :ecx env ctx)
        (= op 'kernel-cpuid-edx) (emit-kernel-cpuid args :edx env ctx)

        (contains? '#{f64-from-bits f64-to-bits} op)
        (emit-expr (first args) env ctx)
        ;; A keyword is carried as a pair(offset,length) over its PRINTED
        ;; text, colon included, so its NAME is the substring past that colon
        ;; and building one from a string is a concatenation with it. Both
        ;; were listed as unimplemented for want of a general substring over a
        ;; runtime handle -- which the loader's string_substring now provides.
        ;; The subject is bound first: it is evaluated once, because the
        ;; operand may be a call and the oracle evaluates it once.
        (and (= op 'keyword-name) (= 1 (count args)))
        (emit-expr (list 'let ['kotoba$keyword-subject (first args)]
                         (list 'string-substring 'kotoba$keyword-subject 1
                               (list 'string-byte-length
                                     'kotoba$keyword-subject)))
                   env ctx)
        (and (= op 'keyword-from-string) (= 1 (count args)))
        (emit-expr (list 'string-concat ":" (first args)) env ctx)
        (contains? f64-compare-ops op)
        (emit-binary (first args) (second args)
                     (vec (concat movq-rax-xmm0 movq-rcx-xmm1 (f64-compare-ops op)))
                     env ctx)
        (contains? f64-binary-ops op)
        (emit-binary (first args) (second args)
                     (vec (concat movq-rax-xmm0 movq-rcx-xmm1
                                  (f64-binary-ops op) movq-xmm0-rax))
                     env ctx)
        (contains? f64-unary-ops op)
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false))
                     (f64-unary-ops op)))
        (and (= op '-) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false)) [0x48 0xf7 0xd8]))

        ;; `kotoba.compiler.frontend`'s `i64-operations`. Admitted for every
        ;; native target, implemented in `kotoba.kir`'s evaluator (so the
        ;; compile-time oracle already agrees), and until now missing from both
        ;; backends -- which meant they reached `emit-call` and were reported as
        ;; an "unknown call target", as though the program had called a function
        ;; that does not exist.
        ;;
        ;; NOT r/m64 shares the group-3 opcode with the NEG just above it,
        ;; differing only in the ModRM reg field (/2 vs /3).
        ;; `bool-not` decodes the same way `kotoba.kir/kotoba-false?` does:
        ;; zero is false, anything else is true. Testing against zero rather
        ;; than flipping bit 0 is what makes that true for ANY word, not only
        ;; a canonical 0/1 -- and it is the same test/setcc/movzx tail every
        ;; comparison in this file already emits, so the two agree by
        ;; construction.
        ;;
        ;; kotoba-kir a28ea11 fixed that decoding in the interpreter, where
        ;; `bool-not` had been a bare `(not value)` and so returned false for
        ;; every input. Implementing it here before that would have meant
        ;; matching a broken oracle.
        (and (= op 'bool-not) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false))
                     [0x48 0x85 0xc0          ; test rax,rax
                      0x0f 0x94 0xc0          ; sete al
                      0x48 0x0f 0xb6 0xc0]))  ; movzx eax,al

        (and (= op 'bit-not) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false)) [0x48 0xf7 0xd0]))

        ;; The shift count rides the ordinary binary window, so it arrives in
        ;; rcx -- and CL, which the variable-count shift group reads, is that
        ;; register's low byte. No masking or range check is emitted: the
        ;; frontend admits the count only as an integer literal in [0,63]
        ;; (`i64 shift count must be an integer literal in [0,63]`), so the
        ;; hardware's own mod-64 truncation of CL is unreachable. That literal
        ;; also means `emit-rhs-window` always takes its constant path here,
        ;; materializing the count straight into rcx.
        ;;
        ;; `i64-shift-right` is ARITHMETIC and `u64-shift-right` is LOGICAL,
        ;; matching `kotoba.kir`'s own `i64-shr` (`bit-shift-right`) and
        ;; `u64-shr` (`unsigned-bit-shift-right`). Swapping them would produce
        ;; an artifact whose sealed oracle value disagrees with its own code for
        ;; every negative operand.
        ;; `kotoba.compiler.frontend`'s `i32-operations`. There is no `:i32`
        ;; value type -- `kotoba.kir` has exactly one mention of `:i32` and it
        ;; is a trap keyword -- so these are ordinary i64 words carrying
        ;; 32-bit wrapping semantics, and they need no new representation,
        ;; no ABI change and no host call. Only the normalization differs:
        ;; every `i32-*` result is SIGN-extended from bit 31 (`kotoba.kir`'s
        ;; helpers go through `unchecked-int` / `i32-wrap`), while `u32-*`
        ;; results are ZERO-extended (`u32-wrap`).
        ;;
        ;; That falls out of the ISA almost for free here: a 32-bit operation
        ;; on x86-64 already zero-extends its result into the full register,
        ;; so the unsigned forms need nothing after them, and the signed forms
        ;; need exactly one `movsxd rax,eax`.
        ;;
        ;; Shift counts ride the ordinary binary window into rcx, and CL is
        ;; its low byte. No masking is emitted: the frontend admits an i32
        ;; shift count only as an integer literal in [0,31], so the hardware's
        ;; own mod-32 truncation of CL is unreachable -- the same argument the
        ;; i64 shifts above make with [0,63].
        (and (= op 'i32-wrap) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false))
                     [0x48 0x63 0xc0]))                    ; movsxd rax,eax

        (and (= op 'u32-wrap) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env (assoc ctx :tail? false))
                     [0x89 0xc0]))                         ; mov eax,eax (zero-extends)

        (contains? '#{i32-wrapping-add i32-wrapping-mul i32-xor
                      i32-shift-left i32-shift-right u32-shift-right} op)
        (let [ctx (assoc ctx :tail? false)
              [left right] args]
          (vec (concat (emit-expr left env ctx)
                       (emit-rhs-window right env ctx)
                       (case op
                         i32-wrapping-add [0x01 0xc8 0x48 0x63 0xc0]      ; add eax,ecx ; movsxd
                         i32-wrapping-mul [0x0f 0xaf 0xc1 0x48 0x63 0xc0] ; imul eax,ecx ; movsxd
                         i32-xor [0x31 0xc8 0x48 0x63 0xc0]               ; xor eax,ecx ; movsxd
                         i32-shift-left [0xd3 0xe0 0x48 0x63 0xc0]        ; shl eax,cl ; movsxd
                         i32-shift-right [0xd3 0xf8 0x48 0x63 0xc0]       ; sar eax,cl ; movsxd
                         ;; logical: the 32-bit shift already zero-extends
                         u32-shift-right [0xd3 0xe8]))))                  ; shr eax,cl

        (contains? '#{i64-shift-left i64-shift-right u64-shift-right} op)
        (let [ctx (assoc ctx :tail? false)
              [value count-form] args]
          (vec (concat (emit-expr value env ctx)
                       (emit-rhs-window count-form env ctx)
                       (case op
                         i64-shift-left [0x48 0xd3 0xe0]    ; shl rax,cl
                         i64-shift-right [0x48 0xd3 0xf8]   ; sar rax,cl
                         u64-shift-right [0x48 0xd3 0xe8])))) ; shr rax,cl

        (contains? '#{+ - * quot bit-xor bit-and bit-or} op)
        (let [ctx (assoc ctx :tail? false)]
          (reduce (fn [left-code right]
                  (vec (concat left-code
                               (emit-rhs-window right env ctx)
                               (case op + [0x48 0x01 0xc8] - [0x48 0x29 0xc8]
                                      * [0x48 0x0f 0xaf 0xc1]
                                      quot [0x48 0x99 0x48 0xf7 0xf9]
                                      bit-xor [0x48 0x31 0xc8]
                                      bit-and [0x48 0x21 0xc8]
                                      ;; ADR-2607254600 D2: OR r/m64,r64
                                      ;; (REX.W 09 /r), the sibling of the
                                      ;; and/xor encodings above.
                                      bit-or [0x48 0x09 0xc8]))))
                  (emit-expr (first args) env ctx) (rest args)))

        (contains? '#{= < > <= >=} op)
        (let [[left right] args setcc ({'= 0x94 '< 0x9c '> 0x9f '<= 0x9e '>= 0x9d} op)]
          (emit-binary left right
                       [0x48 0x39 0xc8 0x0f setcc 0xc0 0x48 0x0f 0xb6 0xc0] env ctx))

        :else (emit-call op args env ctx)))))

(defn- emit-function [{:keys [name params body result]} function-names]
  (when (> (count params) 5)
    (throw (ex-info "x86-64 fuel ABI supports at most five integer parameters"
                    {:phase :x86-64 :function name :arity (count params)})))
  (let [source-body body
        ;; A function declared to return a record hands back the boxed chain,
        ;; from wherever in the body the construction actually sits.
        body (if-let [record-name (record-result-name result)]
               (box-record-tails body record-name)
               body)
        n (count params)]
    (if (and (contains? #{nil :i64 :bool} result)
             (machine-ir/pilot-expression? (vec params) source-body))
      (let [label-counter (atom -1)
            prologue (vec (fuel-charge-tokens label-counter))
            expression (machine-ir/compile-expression :x86-64 (vec params) source-body)]
        {:tokens (vec (concat prologue expression))
         :expression-start (count prologue)})
      (let [
        pad? (even? n)
        env (zipmap params (range))
        label-counter (atom -1)
        prologue (concat (fuel-charge-tokens label-counter) (mapcat #(nth param-pushes %) (range n))
                         (when pad? [0x50]))
        expression (emit-expr body env {:param-count n :pad? pad? :temp-depth 0
                                        :function-name name :tail? true
                                        :function-names function-names
                                        :mir-label-counter label-counter})
        frame-bytes (* 8 (+ n (if pad? 1 0)))
        epilogue (concat [0x48 0x81 0xc4] (le32 frame-bytes) [0xc3])]
        {:tokens (vec (concat prologue expression epilogue))
         :expression-start (count prologue)}))))

;; See `kotoba.native.aarch64/unimplemented-operation!` for why an unresolved
;; call target can only be an unimplemented operator: both the frontend and the
;; verifier prove every call target exists before emission, and `emit-program`
;; puts every declared function into `offsets`.
(defn- unimplemented-operation! [op]
  (throw (ex-info "operation not implemented on this backend"
                  {:phase :x86-64 :backend :x86_64-kotoba-v1 :operation op})))

(defn- finalize [tokens function-offset expression-offset offsets literal-offsets]
  (let [labels (layout/label-offsets tokens token-size)]
    (layout/resolve-tokens
     tokens token-size labels
     (fn [{:mir/keys [encoding]} displacement]
       (case encoding
         :x86-64/jz-rel32 (into [0x0f 0x84] (le32 displacement))
         :x86-64/js-rel32 (into [0x0f 0x88] (le32 displacement))
         :x86-64/jl-rel32 (into [0x0f 0x8c] (le32 displacement))
         :x86-64/jg-rel32 (into [0x0f 0x8f] (le32 displacement))
         :x86-64/ja-rel32 (into [0x0f 0x87] (le32 displacement))
         :x86-64/jae-rel32 (into [0x0f 0x83] (le32 displacement))
         :x86-64/jmp-rel32 (into [0xe9] (le32 displacement))
         :x86-64/jmp-rel8 [0xeb (bit-and displacement 0xff)]
         :x86-64/jne-rel8 [0x75 (bit-and displacement 0xff)]))
     (fn [token position]
       (cond
         (and (map? token) (:call token))
         (let [absolute (+ function-offset position)
               target (get offsets (:call token))]
           (when-not target (unimplemented-operation! (:call token)))
           (into [0xe8] (le32 (- target (+ absolute 5)))))

         (and (map? token) (:tail-self token))
         (let [absolute (+ function-offset position)]
           (into [0xe9] (le32 (- expression-offset (+ absolute 5)))))

         (and (map? token) (:string-literal token))
         (let [content (:string-literal token) offset (get literal-offsets content)]
           (when-not offset
             (throw (ex-info "unknown x86-64 string literal" {:content content})))
           (into [0x48 0xb8] (le64 offset)))

         :else [token])))))

;; Every distinct string literal's content used anywhere in the program,
;; collected once (order-preserving, first occurrence wins) so `finalize`
;; can resolve every `{:string-literal content}` reference deterministically
;; -- the SAME source compiled twice must produce byte-identical output for
;; verifier.clj's independent re-emission check to hold.
(defn- collect-string-literals [token-bodies]
  (distinct (for [[_ emitted] token-bodies
                  token (:tokens emitted)
                  :when (and (map? token) (:string-literal token))]
              (:string-literal token))))

(defn emit-program [kir]
  (if (machine-ir/pilot-module? kir)
    (machine-ir/compile-kir-module
     :x86-64 kir
     (into {} (map (fn [{:keys [name]}]
                     [name (vec (fuel-charge-tokens (atom -1)))])
                   (:functions kir))))
    (let [;; Export set from the DECLARED functions, before the search helpers
        ;; are appended: a program's public surface must not change because it
        ;; searched a string. (`:exports` is usually absent, in which case
        ;; every declared function is exported -- which is exactly why this
        ;; has to be read first.)
        exported-names (set (or (:exports kir) (map :name (:functions kir))))
        functions (-> (:functions kir)
                      string-search/augment-functions
                      string-index/augment-functions)
        function-names (set (map :name functions))
        token-bodies (mapv (fn [f] [f (emit-function f function-names)]) functions)
        offsets (loop [items token-bodies offset 0 out {}]
                  (if-let [[f emitted] (first items)]
                    (recur (next items) (+ offset (code-size (:tokens emitted)))
                           (assoc out (:name f) offset))
                    out))
        code-size-total (reduce + 0 (map (fn [[_ emitted]] (code-size (:tokens emitted))) token-bodies))
        literal-contents (collect-string-literals token-bodies)
        literal-offsets (loop [remaining literal-contents pos code-size-total out {}]
                          (if-let [content (first remaining)]
                            (recur (next remaining)
                                   (+ pos (count (utf8-bytes content)))
                                   (assoc out content pos))
                            out))
        literal-bytes (vec (mapcat (fn [content]
                                     (map #(bit-and (int %) 0xff) (utf8-bytes content)))
                                   literal-contents))]
    (loop [items token-bodies code [] exports {}]
      (if-let [[function emitted] (first items)]
        (let [offset (get offsets (:name function))
              tokens (:tokens emitted)
              body (finalize tokens offset (+ offset (:expression-start emitted)) offsets literal-offsets)]
          (recur (next items) (into code body)
                 (cond-> exports
                   (contains? exported-names (:name function))
                   (assoc (:name function)
                          {:offset offset :length (count body) :arity (count (:params function))}))))
        {:code (vec (concat code literal-bytes)) :exports exports})))))
