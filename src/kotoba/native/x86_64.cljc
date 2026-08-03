(ns kotoba.native.x86-64
  ;; `kotoba.native.peephole` is required on BOTH runtimes, so the reader
  ;; conditional that used to wrap the whole `:require` (see
  ;; `kotoba.wasm.core`'s ns form for that original reasoning -- the `:clj`
  ;; branch needed no requires at all) now wraps only the cljs-only item.
  (:require [kotoba.native.peephole :as peephole]
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
(def ^:private fuel-charge
  ;; context v2: fuel is qword [r9+8].
  [0x49 0x83 0x79 0x08 0x00 0x75 0x02 0x0f 0x0b 0x49 0xff 0x49 0x08])

(defn- token-size [token]
  (cond (and (map? token) (or (:call token) (:tail-self token))) 5
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

(def ^:private f64-unary-ops
  {'f64-sqrt (vec (concat movq-rax-xmm0 [0xf2 0x0f 0x51 0xc0] movq-xmm0-rax))
   'f64-neg [0x48 0x0f 0xba 0xf8 0x3f]
   'f64-abs [0x48 0x0f 0xba 0xf0 0x3f]})

(declare emit-expr)

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
      (let [replacement (into [0x48 0xb9] (le64 constant))]
        (peephole/pad-to replacement
                         (+ (count binary-spill) (count replacement) (count binary-reload))
                         peephole/nop-x86-64))
      (vec (concat binary-spill
                   (emit-expr right env (update ctx :temp-depth inc))
                   binary-reload)))))

(defn- emit-binary [left right opcode env ctx]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr left env ctx)
                 (emit-rhs-window right env ctx)
                 opcode))))

(defn- emit-tail-self-call [args env {:keys [param-count pad? temp-depth] :as ctx}]
  ;; All arguments are evaluated before any parameter slot is overwritten.
  ;; r11 then anchors the existing function frame while the temporary values
  ;; are popped in reverse order into their corresponding slots.  Charging
  ;; fuel here preserves ordinary call semantics; the final jump re-enters
  ;; the expression body without growing the native stack.
  (let [argc (count args)
        values (loop [remaining args depth temp-depth out []]
                 (if-let [arg (first remaining)]
                   (recur (next remaining) (inc depth)
                          (into out (concat (emit-expr arg env (assoc ctx :tail? false :temp-depth depth))
                                            [0x50])))
                   out))
        anchor [0x4c 0x8d 0x9c 0x24] ; lea r11,[rsp+argc*8]
        stores (mapcat (fn [param-index]
                         (let [disp (* 8 (+ (if pad? 1 0)
                                              (- param-count 1 param-index)))]
                           (concat [0x58 0x49 0x89 0x83] (le32 disp))))
                       (reverse (range argc)))]
    (vec (concat values anchor (le32 (* argc 8)) stores fuel-charge
                 [{:tail-self true}]))))

(defn- emit-call [op args env {:keys [temp-depth function-name tail?] :as ctx}]
  (let [argc (count args)]
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
      (loop [remaining args depth temp-depth out []]
      (if-let [arg (first remaining)]
        (recur (next remaining) (inc depth)
               (into out (concat (emit-expr arg env (assoc ctx :tail? false :temp-depth depth)) [0x50])))
        (let [pops (mapcat #(nth arg-pops %) (reverse (range argc)))
              ;; SysV requires rsp%16==0 immediately before CALL. The fixed
              ;; function frame is aligned; expression temporaries may flip it.
              align? (odd? temp-depth)]
          (vec (concat out pops (when align? [0x50]) [{:call op}]
                       (when align? [0x48 0x83 0xc4 0x08])))))))))

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
  (let [cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        byte-offset (+ 16 (quot cap-id 8))
        mask (bit-shift-left 1 (mod cap-id 8))
        ;; Save context across the host ABI call. The fixed guest frame is
        ;; aligned; an even temp depth needs one additional 8-byte pad after
        ;; pushing r9.
        align? (even? temp-depth)]
    (vec (concat
          [0x41 0xf6 0x41 byte-offset mask 0x75 0x02 0x0f 0x0b]
          (emit-expr value env (assoc ctx :tail? false))
          [0x48 0x89 0xc2 0x41 0x51]             ; rdx=value; push r9
          (when align? [0x50])
          [0xbe] (le32 cap-id)                    ; esi=cap-id
          [0x4c 0x89 0xcf 0x41 0xff 0x51 0x30]   ; rdi=r9; call [r9+48]
          (when align? [0x48 0x83 0xc4 0x08])
          [0x41 0x59]))))                         ; pop r9

(defn- emit-typed-cap-call [cap-id kind value env {:keys [temp-depth] :as ctx}]
  (let [cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        byte-offset (+ 16 (quot cap-id 8))
        mask (bit-shift-left 1 (mod cap-id 8))
        align? (even? temp-depth)]
    (vec (concat
          [0x41 0xf6 0x41 byte-offset mask 0x75 0x02 0x0f 0x0b]
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
   'string=? 112 'string-concat 120})

(defn- emit-heap-call [op args env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)
        offset (get heap-call-offsets op)
        argc (count args)
        ;; Evaluate each arg left-to-right onto the stack (mirrors emit-call's
        ;; push shape), then pop them off in reverse into rsi/rdx/rcx/r8 (skip
        ;; index 0 = rdi, reserved below for the context pointer moved from
        ;; r9) -- net stack effect is zero, so `align?` still reads the
        ;; original (pre-call) temp-depth exactly like the pair-only version.
        values (loop [remaining args depth temp-depth out []]
                 (if-let [arg (first remaining)]
                   (recur (next remaining) (inc depth)
                          (into out (concat (emit-expr arg env (assoc ctx :temp-depth depth)) [0x50])))
                   out))
        pops (mapcat #(nth arg-pops (inc %)) (reverse (range argc)))
        align? (even? temp-depth)]
    (vec (concat values pops [0x41 0x51] (when align? [0x50])
                 [0x4c 0x89 0xcf 0x41 0xff 0x51 offset]
                 (when align? [0x48 0x83 0xc4 0x08]) [0x41 0x59]))))

(defn- emit-kernel-load-u8 [[base length index] maximum env {:keys [temp-depth] :as ctx}]
  ;; Evaluate exactly once, then enforce a non-null base, an unsigned index
  ;; below length, and the operation profile's maximum transfer
  ;; bytes. Every violation reaches UD2 before memory is touched.
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2))
        [0x59 0x5a                              ; rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [0x0f 0x87 0x18 0x00 0x00 0x00         ; ja trap
         0x48 0x85 0xd2                         ; test rdx,rdx
         0x0f 0x84 0x0f 0x00 0x00 0x00         ; jz trap
         0x48 0x39 0xc8                         ; cmp rax,rcx
         0x0f 0x83 0x06 0x00 0x00 0x00         ; jae trap
         0x0f 0xb6 0x04 0x02                    ; movzx eax,byte [rdx+rax]
         0xeb 0x02 0x0f 0x0b]))))               ; skip UD2 / trap

(defn- emit-kernel-store-u8 [[base length index value] maximum env {:keys [temp-depth] :as ctx}]
  ;; Evaluate once and perform the same null/length/index checks as load-u8.
  ;; AL is stored only after every check succeeds; RAX remains the expression
  ;; result. Invalid writes trap before mutating memory.
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2)) [0x50]
        (emit-expr value env (update ctx :temp-depth + 3))
        [0x5f 0x59 0x5a                         ; rdi=index, rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [0x0f 0x87 0x17 0x00 0x00 0x00         ; ja trap
         0x48 0x85 0xd2                         ; test rdx,rdx
         0x0f 0x84 0x0e 0x00 0x00 0x00         ; jz trap
         0x48 0x39 0xcf                         ; cmp rdi,rcx
         0x0f 0x83 0x05 0x00 0x00 0x00         ; jae trap
         0x88 0x04 0x3a                         ; mov byte [rdx+rdi],al
         0xeb 0x02 0x0f 0x0b]))))               ; skip UD2 / trap

;; `kernel-load-u32`/`kernel-store-u32` are `kotoba.compiler.frontend`'s
;; `kernel-memory-operations` -- the portable half of the kernel surface, as
;; opposed to `kernel-privileged-operations` (cr2/cr3/invlpg/cli/sti/hlt/pause/
;; out), which name x86 facilities AArch64 has no counterpart for and are
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
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2))
        [0x59 0x5a                              ; rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [0x0f 0x87 0x1b 0x00 0x00 0x00         ; ja trap
         0x48 0x85 0xd2                         ; test rdx,rdx
         0x0f 0x84 0x12 0x00 0x00 0x00         ; jz trap
         0x48 0x8d 0x70 0x04                    ; lea rsi,[rax+4]
         0x48 0x39 0xce                         ; cmp rsi,rcx
         0x0f 0x87 0x05 0x00 0x00 0x00         ; ja trap  (index+4 > length)
         0x8b 0x04 0x02                         ; mov eax,dword [rdx+rax]
         0xeb 0x02 0x0f 0x0b]))))               ; skip UD2 / trap

(defn- emit-kernel-store-u32 [[base length index value] maximum env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat
        (emit-expr base env ctx) [0x50]
        (emit-expr length env (update ctx :temp-depth inc)) [0x50]
        (emit-expr index env (update ctx :temp-depth + 2)) [0x50]
        (emit-expr value env (update ctx :temp-depth + 3))
        [0x5f 0x59 0x5a                         ; rdi=index, rcx=length, rdx=base
         0x48 0x81 0xf9] (le32 maximum)          ; cmp rcx,maximum
        [0x0f 0x87 0x1b 0x00 0x00 0x00         ; ja trap
         0x48 0x85 0xd2                         ; test rdx,rdx
         0x0f 0x84 0x12 0x00 0x00 0x00         ; jz trap
         0x48 0x8d 0x77 0x04                    ; lea rsi,[rdi+4]
         0x48 0x39 0xce                         ; cmp rsi,rcx
         0x0f 0x87 0x05 0x00 0x00 0x00         ; ja trap  (index+4 > length)
         0x89 0x04 0x3a                         ; mov dword [rdx+rdi],eax
         0xeb 0x02 0x0f 0x0b]))))               ; skip UD2 / trap

(defn- emit-kernel-out [[port value] width env {:keys [temp-depth] :as ctx}]
  (let [ctx (assoc ctx :tail? false)]
    (vec (concat (emit-expr port env ctx) [0x50]
                 (emit-expr value env (update ctx :temp-depth inc))
                 [0x5a] (if (= width 8) [0xee] [0xef])))))

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
  (let [pairs (partition 2 bindings)]
    (loop [remaining pairs d temp-depth env env code []]
      (if-let [[name value] (first remaining)]
        (recur (next remaining) (inc d)
               (assoc env name {:let-depth d})
               (concat code (emit-expr value env (assoc ctx :tail? false :temp-depth d)) [0x50]))
        (let [body-code (emit-expr body env (assoc ctx :temp-depth d))
              n (count pairs)]
          (vec (concat code body-code
                       (when (pos? n) (concat [0x48 0x81 0xc4] (le32 (* 8 n)))))))))))

;; A native scalar record has NO independent runtime representation at all --
;; no pointer, no heap-arena allocation (unlike `pair`, which IS heap-backed
;; via a host call), no new host ABI offset, no kexe_loader.c change. This
;; increment's ENTIRE admitted shape is `(record-get type (record-new type
;; v0 v1 ... vN-1) field)` -- a `record-get` immediately, directly nested
;; over a matching `record-new` -- which is REWRITTEN here into exactly the
;; `emit-let`/`load-let` machinery an ordinary `(let [f0 v0 f1 v1 ... fN-1
;; vN-1] fI)` already uses: one synthetic 8-byte stack slot per field,
;; pushed once each in source order (so a side-effecting field expression
;; still runs exactly once, per the ADR-2607198300 `let`-sequencing fix),
;; read back via the SAME depth-relative `load-let` arithmetic. This lands
;; on the same "packed, 8-byte-per-field, offsets 0, 8, 16, ..." layout ADR
;; 0043 chose for its own WASM linear-memory encoding, just realized on the
;; native SysV stack frame instead: every value in this backend (including
;; a `:bool`) is already a uniform 8-byte machine word, so there is no
;; narrower packing to do. Because it degrades to a plain `let`, this is
;; provably correct via machinery already proven by every existing `let`
;; test in `native_executor_test.clj`; it needs zero new machine
;; instructions of its own.
;;
;; Deliberately narrow, matching ADR 0043/0044/0045's own discipline: a
;; bare `record-new` (used anywhere other than as `record-get`'s direct
;; operand), a `record-get` over anything else (a parameter, a `let`-bound
;; name, an `if`, a different-schema construction, a mismatched field
;; count), and `record-assoc`/`record-equal`/nested records are all
;; rejected here with a clear `ex-info`, not silently miscompiled -- no
;; record value can ever escape past this one call, so no new host arena,
;; no new function-boundary ABI (records never appear in `param-types`
;; or `result`), and no lifetime question to answer.
(defn- emit-record-get-of-new [type value-form field env ctx]
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
  (let [tail-ctx (assoc ctx :tail? false)
        push-ordinal (vec (concat (emit-expr ordinal-expr env tail-ctx) [0x50]))
        payload-depth (inc temp-depth)
        push-payload (vec (concat (emit-expr payload-expr env (assoc tail-ctx :temp-depth payload-depth))
                                  [0x50]))
        dispatch-depth (+ temp-depth 2)
        load-tag (load-let temp-depth dispatch-depth)
        n (count branch-specs)
        body-ctx (assoc ctx :temp-depth dispatch-depth)
        ;; add rsp, 16 -- drops the two synthetic slots this dispatch alone
        ;; pushed, run at the end of EVERY case body before falling through
        ;; to whatever follows this whole construct (mirrors `emit-let`'s own
        ;; final pop, just deferred until after the SELECTED branch runs
        ;; instead of after a single body expression).
        cleanup [0x48 0x81 0xc4 0x10 0x00 0x00 0x00]
        body-codes (mapv (fn [{:keys [binder body]}]
                           (vec (emit-expr body (assoc env binder {:let-depth payload-depth}) body-ctx)))
                         branch-specs)
        ;; Build the final per-case bodies right-to-left: the LAST case never
        ;; needs a trailing jump (nothing follows it but whatever comes after
        ;; this whole dispatch), so its size is fixed first; each earlier
        ;; case's own trailing `jmp` distance is exactly the total size of
        ;; every case that will be laid out after it, which is already known
        ;; once the fold reaches that case -- no forward-reference patching
        ;; needed.
        full-bodies
        (vec (reverse
              (reduce (fn [built body-code]
                        (let [remaining (reduce + (map code-size built))]
                          (conj built
                                (if (empty? built)
                                  (vec (concat body-code cleanup))
                                  (vec (concat body-code cleanup [0xe9] (le32 remaining)))))))
                      []
                      (reverse body-codes))))
        body-sizes (mapv code-size full-bodies)
        body-start-offsets (reductions + 0 (butlast body-sizes))
        trap [0x0f 0x0b]                                  ; ud2
        compare-entry-size 12                              ; cmp rax,imm32 (6) + je rel32 (6)
        compare-block
        (vec (mapcat
              (fn [i]
                (let [remaining-compares (- n i 1)
                      distance (+ (* remaining-compares compare-entry-size)
                                  (count trap)
                                  (nth body-start-offsets i))]
                  (concat [0x48 0x3d] (le32 i) [0x0f 0x84] (le32 distance))))
              (range n)))]
    (vec (concat push-ordinal push-payload load-tag compare-block trap (apply concat full-bodies)))))

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
    (let [branch-specs (mapv (fn [[_ binder body]] {:binder binder :body body}) branches)]
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
    (symbol? form)
    (let [binding (get env form)]
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
              test-code (emit-expr test env (assoc ctx :tail? false))
              then-code (emit-expr then env ctx)
              else-code (emit-expr else env ctx)]
          (vec (concat test-code [0x48 0x85 0xc0]
                       [0x0f 0x84] (le32 (+ (code-size then-code) 5))
                       then-code [0xe9] (le32 (code-size else-code)) else-code)))

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

        (contains? '#{pair pair-first pair-second
                      kgraph-assert! kgraph-get kgraph-count kgraph-entity-at
                      string-byte-length string=? string-concat} op)
        (emit-heap-call op args env ctx)

        (= op 'kernel-load-u8)
        (emit-kernel-load-u8 args 512 env ctx)

        (= op 'kernel-load-u8-4k)
        (emit-kernel-load-u8 args 4096 env ctx)

        (= op 'kernel-load-u8-16k)
        (emit-kernel-load-u8 args 16384 env ctx)

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

        (contains? '#{f64-from-bits f64-to-bits} op)
        (emit-expr (first args) env ctx)
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

(defn- emit-function [{:keys [name params body]}]
  (when (> (count params) 5)
    (throw (ex-info "x86-64 fuel ABI supports at most five integer parameters"
                    {:phase :x86-64 :function name :arity (count params)})))
  (let [n (count params)
        pad? (even? n)
        env (zipmap params (range))
        prologue (concat fuel-charge (mapcat #(nth param-pushes %) (range n))
                         (when pad? [0x50]))
        expression (emit-expr body env {:param-count n :pad? pad? :temp-depth 0
                                        :function-name name :tail? true})
        frame-bytes (* 8 (+ n (if pad? 1 0)))
        epilogue (concat [0x48 0x81 0xc4] (le32 frame-bytes) [0xc3])]
    {:tokens (vec (concat prologue expression epilogue))
     :expression-start (count prologue)}))

;; See `kotoba.native.aarch64/unimplemented-operation!` for why an unresolved
;; call target can only be an unimplemented operator: both the frontend and the
;; verifier prove every call target exists before emission, and `emit-program`
;; puts every declared function into `offsets`.
(defn- unimplemented-operation! [op]
  (throw (ex-info "operation not implemented on this backend"
                  {:phase :x86-64 :backend :x86_64-kotoba-v1 :operation op})))

(defn- finalize [tokens function-offset expression-offset offsets literal-offsets]
  (loop [remaining tokens position 0 out []]
    (if-let [token (first remaining)]
      (cond
        (and (map? token) (:call token))
        (let [absolute (+ function-offset position)
              target (get offsets (:call token))]
          (when-not target (unimplemented-operation! (:call token)))
          (recur (next remaining) (+ position 5)
                 (into out (concat [0xe8] (le32 (- target (+ absolute 5)))))))

        (and (map? token) (:tail-self token))
        (let [absolute (+ function-offset position)]
          (recur (next remaining) (+ position 5)
                 (into out (concat [0xe9] (le32 (- expression-offset (+ absolute 5)))))))

        (and (map? token) (:string-literal token))
        (let [content (:string-literal token) offset (get literal-offsets content)]
          (when-not offset
            (throw (ex-info "unknown x86-64 string literal" {:content content})))
          (recur (next remaining) (+ position 10) (into out (into [0x48 0xb8] (le64 offset)))))

        :else
        (recur (next remaining) (inc position) (conj out token)))
      out)))

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
  (let [exported-names (set (or (:exports kir) (map :name (:functions kir))))
        token-bodies (mapv (fn [f] [f (emit-function f)]) (:functions kir))
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
        {:code (vec (concat code literal-bytes)) :exports exports}))))
