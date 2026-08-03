(ns kotoba.native.aarch64
  ;; `kotoba.native.peephole` is required on BOTH runtimes, so the reader
  ;; conditional that used to wrap the whole `:require` (see
  ;; `kotoba.wasm.core`'s ns form for that original reasoning) now wraps only
  ;; the cljs-only item.
  (:require [kotoba.native.peephole :as peephole]
            #?@(:cljs [[kotoba.kir.cljs-i64 :as i64]])))

;; `u32le` only ever encodes a fully-constructed 32-bit ARM instruction
;; WORD (opcode bits + small operand fields, always in [0, 2^32)) -- never
;; an arbitrary `.kotoba` i64 VALUE -- so it stays plain JS-number-based on
;; both runtimes, same reasoning `kotoba.wasm.core`'s `uleb`
;; comment gives (and `kotoba.native.x86-64`'s `le32` mirrors):
;; `(long word)` was already a no-op cast on :clj for values in this range;
;; dropped for :cljs since cljs has no `long`. A JS int32 bitwise op on a
;; word whose top bit is set (e.g. `0xd2800000`, which exceeds signed
;; 32-bit max) still produces the byte-identical bit pattern
;; `unsigned-bit-shift-right`+`bit-and 0xff` extracts on the JVM --
;; interpreting the SAME 32 bits as negative vs. unsigned only matters for
;; display, not for shift/and.
;; Mirrors `kotoba.wasm.core`'s `utf8` -- `.getBytes` is JVM-only,
;; cljs has no `String`/`Charset`; `TextEncoder` is the UTF-8-safe equivalent.
(defn- utf8-bytes [s]
  #?(:clj (.getBytes ^String s "UTF-8")
     :cljs (js/Array.from (.encode (js/TextEncoder.) s))))

(defn- u32le [word]
  (mapv #(bit-and (unsigned-bit-shift-right #?(:clj (long word) :cljs word) (* 8 %)) 0xff) (range 4)))
(defn- insn [word] (u32le word))
(defn- mov-reg [dst src] (insn (bit-or 0xaa0003e0 (bit-shift-left src 16) dst)))
(defn- movz [rd imm shift]
  (insn (bit-or 0xd2800000 (bit-shift-left (quot shift 16) 21)
                (bit-shift-left (bit-and imm 0xffff) 5) rd)))
(defn- movk [rd imm shift]
  (insn (bit-or 0xf2800000 (bit-shift-left (quot shift 16) 21)
                (bit-shift-left (bit-and imm 0xffff) 5) rd)))

;; `value` DOES carry an arbitrary `.kotoba` i64 literal here (both from
;; `emit-expr`'s `(integer? form)` case via `load-constant`, AND from
;; `signed-division`'s `Long/MIN_VALUE` special case below) -- same
;; highest-risk class of port `kotoba.native.x86-64/le64`'s own
;; comment documents. `unsigned-bit-shift-right value 32`/`48` on the JVM
;; is genuine 64-bit-wide unsigned shifting; a naive cljs port using plain
;; `>>>` would silently be a no-op or wrap mod-32 (JS bitwise shift amounts
;; are taken mod 32), extracting the WRONG 16-bit chunk into `movk` and
;; corrupting the loaded constant. The `:cljs` branch reduces VALUE to its
;; unsigned 64-bit bit-pattern once (`BigInt.asUintN`), then extracts each
;; 16-bit chunk via repeated division by a small, always-int32-safe bigint
;; constant (65536) -- NOT `i64/ashr`, whose own divisor computation via a
;; plain `bit-shift-left` silently wraps for shift>=32 (confirmed live,
;; same bug `le64`'s own comment documents at length; see there) --
;; converting to a plain JS number only for the final `imm` argument
;; `movz`/`movk` receive; their own bit-or/bit-shift-left construction of
;; the 32-bit instruction word is then exactly `u32le`'s already-safe
;; 32-bit-bounded case.
(defn- load-constant-reg [rd value]
  #?(:clj
     (vec (concat (movz rd value 0) (movk rd (unsigned-bit-shift-right value 16) 16)
                  (movk rd (unsigned-bit-shift-right value 32) 32)
                  (movk rd (unsigned-bit-shift-right value 48) 48)))
     :cljs
     (let [u (js/BigInt.asUintN 64 (i64/->bigint value))
           base (js/BigInt 65536)
           c0 (js/Number (bit-and u (js/BigInt 0xffff)))
           r1 (/ u base)
           c1 (js/Number (bit-and r1 (js/BigInt 0xffff)))
           r2 (/ r1 base)
           c2 (js/Number (bit-and r2 (js/BigInt 0xffff)))
           r3 (/ r2 base)
           c3 (js/Number (bit-and r3 (js/BigInt 0xffff)))]
       (vec (concat (movz rd c0 0) (movk rd c1 16) (movk rd c2 32) (movk rd c3 48))))))
(defn- load-constant [value] (load-constant-reg 0 value))
(defn- b-ne [byte-offset]
  (insn (bit-or 0x54000001 (bit-shift-left (bit-and (quot byte-offset 4) 0x7ffff) 5))))

(def ^:private signed-division
  (concat (insn 0xb5000041) (insn 0xd4200000)
          (load-constant-reg 2 #?(:clj Long/MIN_VALUE :cljs i64/min-i64)) (insn 0xeb02001f) (b-ne 32)
          (load-constant-reg 2 -1) (insn 0xeb02003f) (b-ne 8)
          (insn 0xd4200000) (insn 0x9ac10c00)))

(def ^:private fuel-charge
  ;; context v2: fuel is qword [x7,#8].
  (concat (insn 0xf94004f0) (insn 0xb5000050) (insn 0xd4200000)
          (insn 0xd1000610) (insn 0xf90004f0)))

(defn- token-size [token]
  (cond (and (map? token) (:call token)) 4
        (and (map? token) (:string-literal token)) 16
        :else 1))
(defn- code-size [tokens] (reduce + (map token-size tokens)))
(defn- sub-sp [amount] (insn (bit-or 0xd10003ff (bit-shift-left amount 10))))
(defn- add-sp [amount] (insn (bit-or 0x910003ff (bit-shift-left amount 10))))
(defn- str-sp [reg offset]
  (insn (bit-or 0xf90003e0 (bit-shift-left (quot offset 8) 10) reg)))
(defn- ldr-sp [reg offset]
  (insn (bit-or 0xf94003e0 (bit-shift-left (quot offset 8) 10) reg)))
(defn- save-x0 [] (concat (sub-sp 16) (str-sp 0 0)))
(defn- restore-to [reg] (concat (ldr-sp reg 0) (add-sp 16)))
(defn- restore-binary []
  ;; rhs is in x0; preserve it in x1, then restore lhs into x0.
  (concat (mov-reg 1 0) (ldr-sp 0 0) (add-sp 16)))
(defn- branch [byte-offset]
  (insn (bit-or 0x14000000 (bit-and (quot byte-offset 4) 0x03ffffff))))
(defn- cbz-x0 [byte-offset]
  (insn (bit-or 0xb4000000 (bit-shift-left (bit-and (quot byte-offset 4) 0x7ffff) 5))))

;; A `let`-bound value's own 16-byte-aligned stack slot, addressed relative
;; to the CURRENT depth (16-byte slots pushed since function entry) rather
;; than a fixed offset. Unlike params (fixed callee-saved registers x19+i,
;; immune to stack movement), a let value can be read after further nested
;; pushes (more arithmetic temporaries, nested lets), so its offset from the
;; live stack pointer must be recomputed from how much *more* has been
;; pushed since it was stored: `current-depth` slots are live now, the value
;; was stored when only `let-depth` were, so it sits
;; `(current-depth - let-depth - 1)` slots above the current stack pointer.
(defn- load-let [reg let-depth current-depth]
  (ldr-sp reg (* 16 (- current-depth let-depth 1))))
(defn- pop-n [n] (when (pos? n) (add-sp (* 16 n))))


;; ── f64 ──────────────────────────────────────────────────────────────────
;;
;; An f64 value lives in the same integer register and the same 16-byte stack
;; slot as everything else on this backend, as its IEEE-754 bit pattern. That
;; is what makes `f64-from-bits` and `f64-to-bits` **identities** here: they
;; are representation changes the wasm backend genuinely needs, because its
;; operand stack is typed, and this one does not. It also means f64 literals
;; need no new constant path — the frontend already lowers them to
;; `(f64-from-bits <i64>)`, and the existing movz/movk sequence loads the
;; pattern unchanged.
;;
;; Arithmetic is the only place the value has to become a real double, so the
;; sequence is: move into the FP bank, operate, move back. Every encoding
;; below was checked against `clang -target arm64-apple-macos` rather than
;; derived from the manual and trusted.

(def ^:private fmov-d0-x0 (insn 0x9e670000))
(def ^:private fmov-d1-x1 (insn 0x9e670021))
(def ^:private fmov-x0-d0 (insn 0x9e660000))

(def ^:private f64-binary-ops
  {'f64-add 0x1e612800 'f64-sub 0x1e613800 'f64-mul 0x1e610800
   'f64-div 0x1e611800 'f64-max 0x1e614800 'f64-min 0x1e615800})

(def ^:private f64-unary-ops
  {'f64-abs 0x1e60c000 'f64-neg 0x1e614000 'f64-sqrt 0x1e61c000})

(declare emit-expr)

;; The spill/reload window that both `emit-binary` and the n-ary arithmetic
;; loop place between the left operand's code and the operation itself:
;; `save-x0` claims a 16-byte stack slot and stores the left operand, the
;; right operand's code then targets x0, and `restore-binary` moves that
;; result into x1 before reloading the left operand and releasing the slot.
;;
;; When the right operand is a compile-time constant, none of that is needed:
;; the constant can be materialized straight into x1, and `load-constant-reg`
;; encodes into the same four instructions for any destination register, so
;; the replacement occupies exactly what the constant's own code would have.
;; What the window sheds is the entire stack round trip -- a stack-pointer
;; decrement, a store, a load, a register move and an increment -- replaced by
;; canonical `nop`s. See `kotoba.native.peephole`'s namespace docstring for
;; why the length must be preserved rather than reclaimed.
;;
;; The window length is DERIVED from the surrounding encodings rather than
;; written as a literal 36, so it cannot drift if any of them change.
(defn- emit-rhs-window [right env depth]
  (let [constant (peephole/constant-operand right)]
    (if (some? constant)
      (let [replacement (load-constant-reg 1 constant)]
        (peephole/pad-to replacement
                         (+ (count (save-x0)) (count replacement) (count (restore-binary)))
                         peephole/nop-aarch64))
      (vec (concat (save-x0) (emit-expr right env (inc depth)) (restore-binary))))))

(defn- emit-binary [left right operation env depth]
  (vec (concat (emit-expr left env depth)
               (emit-rhs-window right env depth)
               operation)))

(defn- emit-call [op args env depth]
  (when (> (count args) 5)
    (throw (ex-info "AArch64 fuel ABI supports at most five arguments"
                    {:phase :aarch64 :function op :arity (count args)})))
  (let [saved (mapcat (fn [i a] (concat (emit-expr a env (+ depth i)) (save-x0)))
                      (range) args)
        restored (mapcat #(restore-to %) (reverse (range (count args))))]
    (vec (concat saved restored [{:call op}]))))

(defn- ldr-context [reg offset]
  (insn (bit-or 0xf9400000 (bit-shift-left (quot offset 8) 10)
                (bit-shift-left 7 5) reg)))

(defn- tbnz [reg bit-index byte-offset]
  (insn (bit-or 0x37000000
                (bit-shift-left (bit-and bit-index 0x20) 26)
                (bit-shift-left (bit-and bit-index 0x1f) 19)
                (bit-shift-left (bit-and (quot byte-offset 4) 0x3fff) 5)
                reg)))

;; Bounded kernel memory access (aiueos kernel target). Mirrors the x86-64
;; backend's kernel-load-u8/store-u8: evaluate base/length/index(/value) once,
;; then enforce length<=maximum, base!=0, and index<length -- every violation
;; reaches `brk #0` before memory is touched. AArch64 uses MMIO load/store for
;; device access; there is no port-I/O intrinsic.
(defn- b-cond [cond-code byte-offset]
  (insn (bit-or 0x54000000 (bit-shift-left (bit-and (quot byte-offset 4) 0x7ffff) 5) cond-code)))
(defn- cbz-reg [rt byte-offset]
  (insn (bit-or 0xb4000000 (bit-shift-left (bit-and (quot byte-offset 4) 0x7ffff) 5) rt)))
;; `CMP Xn, #imm12` (alias of `SUBS XZR, Xn, #imm12`, no shift). Used by
;; `emit-variant-dispatch` below to compare the discriminant register
;; against each case's own small, always-non-negative, compile-time-known
;; ordinal -- never an arbitrary `.kotoba` i64 VALUE (that class of value
;; goes through the general `contains? '#{= < > <= >=}` register-vs-register
;; path already in `emit-expr`, unchanged), so a plain JS-number-safe imm12
;; is always sufficient here (this increment's own case counts are a
;; handful, nowhere near imm12's 4096 ceiling).
(defn- cmp-imm [rn imm12]
  (insn (bit-or 0xf100001f (bit-shift-left (bit-and imm12 0xfff) 10) (bit-shift-left rn 5))))
(def ^:private cond-hi 8)     ; unsigned length > maximum
(def ^:private cond-hs 2)     ; unsigned index >= length

(defn- bounds-check [maximum]
  ;; Precondition: x1=base, x2=length, x3=index. The caller appends a two-insn
  ;; access (add x1,x1,x3 ; strb/ldrb w0,[x1]), then `b skip`, then the `brk`
  ;; trap. Byte layout from this block's first branch:
  ;;   +0 cmp x2,x4  +4 b.hi trap  +8 cbz x1,trap  +12 cmp x3,x2  +16 b.hs trap
  ;;   +20 add       +24 access    +28 b skip      +32 brk(trap)  +36 skip
  (concat (load-constant-reg 4 maximum)
          (insn 0xeb04005f)          ; cmp x2, x4  (length vs maximum)
          (b-cond cond-hi 28)        ; b.hi trap
          (cbz-reg 1 24)             ; cbz x1, trap
          (insn 0xeb02007f)          ; cmp x3, x2  (index vs length)
          (b-cond cond-hs 16)))      ; b.hs trap

;; NB: the access uses base-register addressing `strb/ldrb w0, [x1]` after
;; computing `x1 = base + index` (add x1,x1,x3). Register-offset addressing
;; (`[x1, x3]`) leaves the ESR instruction-syndrome invalid (ISV=0) for the MMIO
;; that a device store/load triggers, so KVM cannot emulate it (it injects a
;; data abort instead of exiting) -- base-register addressing keeps ISV=1.
(defn- emit-kernel-store-u8 [[base length index value] maximum env depth]
  (vec (concat
        (emit-expr base env depth) (save-x0)
        (emit-expr length env (+ depth 1)) (save-x0)
        (emit-expr index env (+ depth 2)) (save-x0)
        (emit-expr value env (+ depth 3))    ; x0 = value (also the result)
        (ldr-sp 3 0) (add-sp 16)             ; x3 = index
        (ldr-sp 2 0) (add-sp 16)             ; x2 = length
        (ldr-sp 1 0) (add-sp 16)             ; x1 = base
        (bounds-check maximum)
        (insn 0x8b030021)                    ; add x1, x1, x3   (x1 = base+index)
        (insn 0x39000020)                    ; strb w0, [x1]
        (branch 8)                           ; b skip
        (insn 0xd4200000))))                 ; trap: brk ; skip:

(defn- emit-kernel-load-u8 [[base length index] maximum env depth]
  (vec (concat
        (emit-expr base env depth) (save-x0)
        (emit-expr length env (+ depth 1)) (save-x0)
        (emit-expr index env (+ depth 2))    ; x0 = index
        (mov-reg 3 0)                        ; x3 = index
        (ldr-sp 2 0) (add-sp 16)             ; x2 = length
        (ldr-sp 1 0) (add-sp 16)             ; x1 = base
        (bounds-check maximum)
        (insn 0x8b030021)                    ; add x1, x1, x3   (x1 = base+index)
        (insn 0x39400020)                    ; ldrb w0, [x1]  -> x0 = byte
        (branch 8)                           ; b skip
        (insn 0xd4200000))))                 ; trap: brk ; skip:

;; 32-bit MMIO (virtio registers are u32). Same bounds discipline, but the
;; 4-byte access must fit: index+4 <= length. Byte layout from the first branch:
;;   +0 cmp x2,x4  +4 b.hi trap  +8 cbz x1,trap  +12 add x5,x3,#4  +16 cmp x5,x2
;;   +20 b.hi trap +24 add x1,x1,x3 +28 access  +32 b skip  +36 brk(trap)  +40 skip
(defn- bounds-check-u32 [maximum]
  (concat (load-constant-reg 4 maximum)
          (insn 0xeb04005f)          ; cmp x2, x4  (length vs maximum)
          (b-cond cond-hi 32)        ; b.hi trap
          (cbz-reg 1 28)             ; cbz x1, trap
          (insn 0x91001065)          ; add x5, x3, #4   (index + 4)
          (insn 0xeb0200bf)          ; cmp x5, x2       (index+4 vs length)
          (b-cond cond-hi 16)))      ; b.hi trap  (index+4 > length)

(defn- emit-kernel-store-u32 [[base length index value] maximum env depth]
  (vec (concat
        (emit-expr base env depth) (save-x0)
        (emit-expr length env (+ depth 1)) (save-x0)
        (emit-expr index env (+ depth 2)) (save-x0)
        (emit-expr value env (+ depth 3))    ; x0 = value (also the result)
        (ldr-sp 3 0) (add-sp 16)             ; x3 = index
        (ldr-sp 2 0) (add-sp 16)             ; x2 = length
        (ldr-sp 1 0) (add-sp 16)             ; x1 = base
        (bounds-check-u32 maximum)
        (insn 0x8b030021)                    ; add x1, x1, x3
        (insn 0xb9000020)                    ; str w0, [x1]
        (branch 8)                           ; b skip
        (insn 0xd4200000))))                 ; trap: brk ; skip:

(defn- emit-kernel-load-u32 [[base length index] maximum env depth]
  (vec (concat
        (emit-expr base env depth) (save-x0)
        (emit-expr length env (+ depth 1)) (save-x0)
        (emit-expr index env (+ depth 2))    ; x0 = index
        (mov-reg 3 0)                        ; x3 = index
        (ldr-sp 2 0) (add-sp 16)             ; x2 = length
        (ldr-sp 1 0) (add-sp 16)             ; x1 = base
        (bounds-check-u32 maximum)
        (insn 0x8b030021)                    ; add x1, x1, x3
        (insn 0xb9400020)                    ; ldr w0, [x1]  -> x0 = word
        (branch 8)                           ; b skip
        (insn 0xd4200000))))                 ; trap: brk ; skip:

;; Same `cap-id`-is-a-cljs-`bigint` issue `kotoba.native.x86-64`'s
;; `emit-cap-call` documents at length -- coerced to a plain JS number once
;; up front (always safely in [0,255]) rather than propagating bigint
;; through `quot`/`mod`/`*`, which throw when mixed with a plain-number
;; operand like the literal `64` here.
(defn- emit-cap-call [cap-id value env depth]
  (let [cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        word-offset (+ 16 (* 8 (quot cap-id 64)))
        bit-index (mod cap-id 64)]
    (vec (concat
          (ldr-context 16 word-offset) (tbnz 16 bit-index 8) (insn 0xd4200000)
          (emit-expr value env depth)
          (mov-reg 2 0)                           ; x2=value
          (sub-sp 16) (str-sp 7 0)                ; preserve context
          (load-constant-reg 1 cap-id) (mov-reg 0 7)
          (ldr-context 16 48) (insn 0xd63f0200)   ; blr x16
          (ldr-sp 7 0) (add-sp 16)))))

(defn- emit-typed-cap-call [cap-id kind value env depth]
  (let [cap-id #?(:clj cap-id :cljs (js/Number cap-id))
        word-offset (+ 16 (* 8 (quot cap-id 64)))
        bit-index (mod cap-id 64)]
    (vec (concat
          (ldr-context 16 word-offset) (tbnz 16 bit-index 8) (insn 0xd4200000)
          (emit-expr value env depth)
          (mov-reg 4 0)                           ; x4=request handle
          (sub-sp 16) (str-sp 7 0)
          (load-constant-reg 1 cap-id)
          (load-constant-reg 2 kind)              ; request kind
          (load-constant-reg 3 kind)              ; result kind
          (mov-reg 0 7)
          (ldr-context 16 128) (insn 0xd63f0200)
          (ldr-sp 7 0) (add-sp 16)))))

(def ^:private heap-call-offsets
  {'pair 56 'pair-first 64 'pair-second 72
   'kgraph-assert! 80 'kgraph-get 88 'kgraph-count 96 'kgraph-entity-at 104
   ;; A string value IS a pair(offset,length) handle (see emit-string-literal
   ;; below) -- string-byte-length is exactly pair-second, no new host
   ;; function needed. string=?/string-concat resolve their handles' bytes
   ;; host-side (content comparison / pool allocation), so they need a new
   ;; offset each.
   'string-byte-length 72
   'string=? 112 'string-concat 120})

(defn- emit-heap-call [op args env depth]
  (let [offset (get heap-call-offsets op)
        argc (count args)
        ;; Evaluate each arg left-to-right onto the stack (mirrors emit-call's
        ;; save/restore shape), then pop them off in reverse into x1..x(argc)
        ;; -- x0 is reserved for the context pointer moved in from x7 below.
        saved (mapcat (fn [i a] (concat (emit-expr a env (+ depth i)) (save-x0)))
                      (range) args)
        restored (mapcat (fn [i] (restore-to (inc i))) (reverse (range argc)))]
    (vec (concat saved restored
                 (sub-sp 16) (str-sp 7 0)
                 (mov-reg 0 7) (ldr-context 16 offset) (insn 0xd63f0200)
                 (ldr-sp 7 0) (add-sp 16)))))

;; A string VALUE is a pair(offset, length) handle -- offset addresses a
;; UTF-8 byte range either in the compiled artifact's own code+literal-data
;; region (non-negative) or in the runtime string pool (negative, see
;; tools/kexe_loader.c's checked_string_concat), uniformly resolved host-side.
;; A literal's bytes are appended once per DISTINCT content to the artifact's
;; :code array (read+exec, never written after mprotect -- literal data is
;; read-only, no different from reading one's own instructions as data); its
;; offset is only known once every function's code size is summed, so this
;; emits a deferred {:string-literal content} token (finalize resolves it,
;; token-size already reserves the 16 bytes a resolved load-constant needs)
;; for JUST the offset half -- length is already known here, at literal-
;; encounter time, so it needs no deferral.
(defn- emit-string-literal [content]
  (let [length (count (utf8-bytes content))]
    (vec (concat [{:string-literal content}] (save-x0)     ; push offset
                 (load-constant length) (save-x0)          ; push length
                 (restore-to 2) (restore-to 1)              ; x2=length, x1=offset
                 (sub-sp 16) (str-sp 7 0)
                 (mov-reg 0 7) (ldr-context 16 56) (insn 0xd63f0200) ; call pair_new
                 (ldr-sp 7 0) (add-sp 16)))))

(defn- emit-let [bindings body env depth]
  ;; Genuinely sequential: each binding's value is evaluated exactly once, in
  ;; source order, and pushed onto its own 16-byte stack slot before the next
  ;; binding (or the body) is emitted -- unlike a compile-time substitution
  ;; pass, an unreferenced or repeatedly-referenced side-effecting binding
  ;; (kgraph-assert!, cap-call, pair, ...) still runs exactly once, and a
  ;; binding referenced from inside an `if` branch still runs unconditionally
  ;; before the branch is chosen (ADR-2607198300 follow-up).
  (let [pairs (partition 2 bindings)]
    (loop [remaining pairs d depth env env code []]
      (if-let [[name value] (first remaining)]
        (recur (next remaining) (inc d)
               (assoc env name {:let-depth d})
               (concat code (emit-expr value env d) (save-x0)))
        (let [body-code (emit-expr body env d)]
          (vec (concat code body-code (pop-n (count pairs)))))))))

;; A native scalar record has NO independent runtime representation at all --
;; no pointer, no heap-arena allocation (unlike `pair`, which IS heap-backed
;; via a host call), no new host ABI offset. Mirrors
;; `kotoba.native.x86-64/emit-record-get-of-new`'s own docstring
;; exactly (this is the AArch64 half of the SAME design decision, see that
;; comment for the full rationale): this increment's ENTIRE admitted shape
;; is `(record-get type (record-new type v0 v1 ... vN-1) field)`, rewritten
;; into the SAME `emit-let`/`load-let` machinery an ordinary `(let [f0 v0 f1
;; v1 ... fN-1 vN-1] fI)` already uses -- one synthetic 16-byte-aligned
;; stack slot per field (this backend's own `let` slot size), read back via
;; the same depth-relative `load-let` arithmetic already proven correct by
;; every existing `let` test.
(defn- emit-record-get-of-new [type value-form field env depth]
  (when-not (seq? value-form)
    (throw (ex-info "record-get is only supported directly over a matching record-new construction on the native backend"
                    {:phase :aarch64 :type type})))
  (let [[record-op record-type & field-exprs] value-form
        fields (nth type 2)
        field-index (first (keep-indexed (fn [i [name _]] (when (= name field) i)) fields))]
    (when-not (= 'record-new record-op)
      (throw (ex-info "record-get is only supported directly over a matching record-new construction on the native backend"
                      {:phase :aarch64 :type type})))
    (when-not (= type record-type)
      (throw (ex-info "record-get's schema must be identical to its record-new operand's schema"
                      {:phase :aarch64 :expected type :actual record-type})))
    (when-not (= (count fields) (count field-exprs))
      (throw (ex-info "record-new does not supply exactly one value per declared field"
                      {:phase :aarch64 :type type})))
    (when (nil? field-index)
      (throw (ex-info "record-get references an undeclared field"
                      {:phase :aarch64 :type type :field field})))
    (let [names (mapv #(symbol (str "$record-field-" %)) (range (count fields)))
          bindings (vec (mapcat vector names field-exprs))]
      (emit-let bindings (nth names field-index) env depth))))

;; ADR 0063: AArch64 half of the SAME design decision
;; `backend/x86-64.cljc/emit-variant-dispatch`'s own docstring documents in
;; full (this is the second native value-representation increment, right
;; after ADR 0062's record). A native sealed variant has no independent
;; heap/pointer representation: it is rewritten into TWO synthetic 16-byte-
;; aligned stack slots (this backend's own `let` slot size) on the SAME
;; `emit-let`/`load-let` machinery -- slot 0 = discriminant (the case's
;; 0-based ordinal within the type's declared `cases`), slot 1 = payload (one
;; word, uniformly reserved for every case including a tag-only/"unit" one,
;; whose branch body simply never reads it). Dispatch is a real runtime
;; compare-and-branch chain over the stored discriminant (x0 after
;; `load-let`): `cmp x0,#i ; b.eq case_i` for each of the N declared cases in
;; order, falling through past all N comparisons to a defensive `brk`trap if
;; none match -- never special-cased away by a directly-nested `variant-
;; new`'s literal tag being statically known at that call site (see
;; `emit-variant-match-of-new` below).
(defn- emit-variant-dispatch
  "Mirrors `backend/x86-64.cljc`'s own `emit-variant-dispatch` exactly, on
  this backend's own AArch64 instruction encodings and 16-byte let-slot
  convention. See that function's docstring for the full contract (including
  why ORDINAL-EXPR is intentionally NOT restricted to a compiler-derived
  in-range value here)."
  [ordinal-expr payload-expr branch-specs env depth]
  (let [push-ordinal (vec (concat (emit-expr ordinal-expr env depth) (save-x0)))
        payload-depth (inc depth)
        push-payload (vec (concat (emit-expr payload-expr env payload-depth) (save-x0)))
        dispatch-depth (+ depth 2)
        load-tag (load-let 0 depth dispatch-depth)
        n (count branch-specs)
        ;; add sp, sp, #32 -- drops the two synthetic 16-byte slots this
        ;; dispatch alone pushed, run at the end of EVERY case body.
        cleanup (add-sp 32)
        body-codes (mapv (fn [{:keys [binder body]}]
                           (vec (emit-expr body (assoc env binder {:let-depth payload-depth}) dispatch-depth)))
                         branch-specs)
        ;; Right-to-left fold, same reasoning as the x86-64 half: the last
        ;; case never needs a trailing branch, so its size is known first,
        ;; and each earlier case's own trailing `b` distance is exactly the
        ;; already-known total size of every case laid out after it. Unlike
        ;; x86-64's `jmp rel32` (relative to the NEXT instruction), AArch64's
        ;; `b`/`b.cond` immediate is relative to the BRANCH INSTRUCTION'S OWN
        ;; address (confirmed against this file's own pre-existing `if` and
        ;; `bounds-check` byte-layout comments/offsets) -- every offset here
        ;; therefore adds this instruction's own 4-byte width on top of the
        ;; byte count between the END of this instruction and its target.
        full-bodies
        (vec (reverse
              (reduce (fn [built body-code]
                        (let [remaining (reduce + (map code-size built))]
                          (conj built
                                (if (empty? built)
                                  (vec (concat body-code cleanup))
                                  (vec (concat body-code cleanup (branch (+ 4 remaining))))))))
                      []
                      (reverse body-codes))))
        body-sizes (mapv code-size full-bodies)
        body-start-offsets (reductions + 0 (butlast body-sizes))
        trap (insn 0xd4200000)                              ; brk #0
        compare-entry-size 8                                 ; cmp-imm (4) + b.eq (4)
        compare-block
        (vec (mapcat
              (fn [i]
                (let [remaining-compares (- n i 1)
                      ;; +4: `b.eq`'s own self-relative width, see the
                      ;; `full-bodies` comment above for why.
                      distance (+ 4 (* remaining-compares compare-entry-size)
                                  (count trap)
                                  (nth body-start-offsets i))]
                  (concat (cmp-imm 0 i) (b-cond 0 distance))))    ; cond-eq = 0
              (range n)))]
    (vec (concat push-ordinal push-payload load-tag compare-block trap (apply concat full-bodies)))))

;; Mirrors `backend/x86-64.cljc/emit-variant-match-of-new` exactly: `value-
;; form` must be a directly-nested, same-schema `variant-new` -- a variant
;; value never crosses a function boundary, matching the record ADR's own
;; restriction, so no new host arena and no lifetime question to answer.
(defn- emit-variant-match-of-new [type value-form branches env depth]
  (when-not (seq? value-form)
    (throw (ex-info "variant-match is only supported directly over a matching variant-new construction on the native backend"
                    {:phase :aarch64 :type type})))
  (let [[ctor-op ctor-type tag payload-expr] value-form
        cases (nth type 2)
        ordinal (first (keep-indexed (fn [i [case-tag _]] (when (= case-tag tag) i)) cases))]
    (when-not (= 'variant-new ctor-op)
      (throw (ex-info "variant-match is only supported directly over a matching variant-new construction on the native backend"
                      {:phase :aarch64 :type type})))
    (when-not (= type ctor-type)
      (throw (ex-info "variant-match's schema must be identical to its variant-new operand's schema"
                      {:phase :aarch64 :expected type :actual ctor-type})))
    (when (nil? ordinal)
      (throw (ex-info "variant-new references an undeclared case"
                      {:phase :aarch64 :type type :tag tag})))
    (when-not (= (count cases) (count branches))
      (throw (ex-info "variant-match does not supply exactly one branch per declared case"
                      {:phase :aarch64 :type type})))
    (let [branch-specs (mapv (fn [[_ binder body]] {:binder binder :body body}) branches)]
      (emit-variant-dispatch ordinal payload-expr branch-specs env depth))))

(defn emit-expr [form env depth]
  (cond
    ;; `integer?` alone does not reliably recognize a cljs `bigint` (see
    ;; `kotoba.kir.cljs-i64`'s own namespace docstring) -- mirrors
    ;; `kotoba.wasm.core`'s identical dispatch guard.
    #?(:clj (integer? form) :cljs (or (i64/bigint-value? form) (integer? form)))
    (load-constant form)
    ;; A literal `true`/`false` -- the only source of a genuine `:bool`
    ;; VALUE in this frontend's type system (see
    ;; `emit-record-get-of-new`'s own doc comment above) -- is just the i64
    ;; word 1/0, encoded through the SAME `load-constant` path an ordinary
    ;; integer literal uses. MUST be checked before the generic `:else`,
    ;; which would otherwise try to sequentially destructure a bare boolean
    ;; and throw.
    (boolean? form) (load-constant (if form 1 0))
    (string? form) (emit-string-literal form)
    (symbol? form)
    (let [binding (get env form)]
      (if (map? binding)
        (load-let 0 (:let-depth binding) depth)
        (mov-reg 0 (+ 19 binding))))
    :else
    (let [[op & args] form]
      (cond
        (= op 'if)
        (let [[test then else] args test-code (emit-expr test env depth)
              then-code (emit-expr then env depth) else-code (emit-expr else env depth)]
          (vec (concat test-code (cbz-x0 (+ 8 (code-size then-code)))
                       then-code (branch (+ 4 (code-size else-code))) else-code)))
        ;; `do`: emit each subexpression in order at the SAME depth (each is
        ;; self-contained -- net zero stack effect -- so no push/pop needed
        ;; between them); each leaves its result in x0, the next overwrites
        ;; it, so only the last value survives, but every subexpression's
        ;; side effects execute exactly once, in order.
        (= op 'do)
        (vec (mapcat #(emit-expr % env depth) args))
        (= op 'let)
        (emit-let (first args) (second args) env depth)
        (= op 'cap-call)
        (emit-cap-call (first args) (second args) env depth)
        (= op 'typed-cap-call)
        (let [[cap-id request-type result-type request] args]
          (cond
            (= :i64 request-type result-type)
            (emit-cap-call cap-id request env depth)
            (= :string request-type result-type)
            (emit-typed-cap-call cap-id 1 request env depth)
            (= :option-i64 request-type result-type)
            (emit-typed-cap-call cap-id 2 request env depth)
            (= :result-i64 request-type result-type)
            (emit-typed-cap-call cap-id 3 request env depth)
            :else
            (throw (ex-info "native typed capability ABI does not support this boundary"
                            {:phase :aarch64 :request-type request-type
                             :result-type result-type}))))
        (= op 'option-some)
        (emit-heap-call 'pair [1 (first args)] env depth)
        (= op 'option-none)
        (emit-heap-call 'pair [0 0] env depth)
        (= op 'option-some?)
        (emit-heap-call 'pair-first [(first args)] env depth)
        (= op 'option-value)
        (let [[value fallback] args
              tagged-value '__native_option_value]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'pair-second tagged-value)
                          fallback)
                    env depth))
        (= op 'option-some-of)
        (emit-heap-call 'pair [1 (second args)] env depth)
        (= op 'option-none-of)
        (emit-heap-call 'pair [0 0] env depth)
        (= op 'option-some?-of)
        (emit-heap-call 'pair-first [(second args)] env depth)
        (= op 'option-value-of)
        (let [[_type value fallback] args
              tagged-value '__native_generic_option_value]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'pair-second tagged-value)
                          fallback)
                    env depth))
        (= op 'option-match)
        (let [[_type value none-body binder some-body] args
              tagged-value '__native_generic_option_match]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'let [binder (list 'pair-second tagged-value)]
                                some-body)
                          none-body)
                    env depth))
        (= op 'result-ok)
        (emit-heap-call 'pair [1 (first args)] env depth)
        (= op 'result-err)
        (emit-heap-call 'pair [0 (first args)] env depth)
        (= op 'result-ok?)
        (emit-heap-call 'pair-first [(first args)] env depth)
        (contains? '#{result-value result-error} op)
        (let [[value fallback] args
              tagged-value '__native_result_value
              ok? (list 'pair-first tagged-value)
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (if (= op 'result-value)
                      (list 'if ok? payload fallback)
                      (list 'if ok? fallback payload))
                    env depth))
        (contains? '#{result-ok-of result-err-of} op)
        (emit-heap-call 'pair [(if (= op 'result-ok-of) 1 0) (second args)] env depth)
        (= op 'result-ok?-of)
        (emit-heap-call 'pair-first [(second args)] env depth)
        (contains? '#{result-value-of result-error-of} op)
        (let [[_type value fallback] args
              tagged-value '__native_generic_result_value
              ok? (list 'pair-first tagged-value)
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (if (= op 'result-value-of)
                      (list 'if ok? payload fallback)
                      (list 'if ok? fallback payload))
                    env depth))
        (= op 'result-match-of)
        (let [[_type value ok-binder ok-body err-binder err-body] args
              tagged-value '__native_generic_result_match
              payload (list 'pair-second tagged-value)]
          (emit-let [tagged-value value]
                    (list 'if (list 'pair-first tagged-value)
                          (list 'let [ok-binder payload] ok-body)
                          (list 'let [err-binder payload] err-body))
                    env depth))
        (= op 'record-get)
        (let [[type value-form field] args]
          (emit-record-get-of-new type value-form field env depth))
        (= op 'record-new)
        (throw (ex-info "record-new is only supported as the direct operand of a matching record-get on the native backend"
                        {:phase :aarch64}))
        (= op 'variant-match)
        (let [[type value-form branches] args]
          (emit-variant-match-of-new type value-form branches env depth))
        (= op 'variant-new)
        (throw (ex-info "variant-new is only supported as the direct operand of a matching variant-match on the native backend"
                        {:phase :aarch64}))
        (contains? '#{pair pair-first pair-second
                      kgraph-assert! kgraph-get kgraph-count kgraph-entity-at
                      string-byte-length string=? string-concat} op)
        (emit-heap-call op args env depth)
        ;; Pure representation changes: the bits are already in x0.
        (contains? '#{f64-from-bits f64-to-bits} op)
        (emit-expr (first args) env depth)
        (contains? f64-binary-ops op)
        (emit-binary (first args) (second args)
                     (concat fmov-d0-x0 fmov-d1-x1
                             (insn (f64-binary-ops op)) fmov-x0-d0)
                     env depth)
        (contains? f64-unary-ops op)
        (vec (concat (emit-expr (first args) env depth)
                     fmov-d0-x0 (insn (f64-unary-ops op)) fmov-x0-d0))
        (and (= op '-) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env depth) (insn 0xcb0003e0)))
        ;; `bit-and`/`bit-or`/`bit-xor` are portable integer arithmetic, not an
        ;; ISA-specific facility: `kotoba.compiler.frontend` admits them for
        ;; every native target and `kotoba.native.x86-64` has always emitted
        ;; them (AND/OR/XOR r/m64,r64). Their absence here was a silent gap --
        ;; they fell through to `emit-call`, were looked up as user functions,
        ;; and died in `finalize`. These are the logical (shifted-register)
        ;; encodings with Rm=x1, Rn=x0, Rd=x0, the same operand placement the
        ;; add/sub/mul cases beside them already use; `mov-reg`'s own
        ;; `0xaa0003e0` is this ORR base with Rn=xzr, which cross-checks the
        ;; opcode bits.
        (contains? '#{+ - * quot bit-and bit-or bit-xor} op)
        (loop [remaining (rest args) left-code (emit-expr (first args) env depth)]
          (if-let [right (first remaining)]
            (recur (next remaining)
                   (vec (concat left-code
                                (emit-rhs-window right env depth)
                                (case op + (insn 0x8b010000) - (insn 0xcb010000)
                                       * (insn 0x9b017c00) quot signed-division
                                       bit-and (insn 0x8a010000)
                                       bit-or (insn 0xaa010000)
                                       bit-xor (insn 0xca010000)))))
            left-code))
        (contains? '#{= < > <= >=} op)
        (let [[left right] args cset ({'= 0x9a9f17e0 '< 0x9a9fa7e0 '> 0x9a9fd7e0
                                      '<= 0x9a9fc7e0 '>= 0x9a9fb7e0} op)]
          (emit-binary left right (concat (insn 0xeb01001f) (insn cset)) env depth))
        (= op 'kernel-store-u8) (emit-kernel-store-u8 args 512 env depth)
        (= op 'kernel-store-u8-4k) (emit-kernel-store-u8 args 4096 env depth)
        (= op 'kernel-load-u8) (emit-kernel-load-u8 args 512 env depth)
        (= op 'kernel-load-u8-4k) (emit-kernel-load-u8 args 4096 env depth)
        (= op 'kernel-load-u8-16k) (emit-kernel-load-u8 args 16384 env depth)
        (= op 'kernel-store-u32) (emit-kernel-store-u32 args 512 env depth)
        (= op 'kernel-load-u32) (emit-kernel-load-u32 args 512 env depth)
        :else (emit-call op args env depth)))))

(defn- emit-function [{:keys [name params body]}]
  (when (> (count params) 5)
    (throw (ex-info "AArch64 fuel ABI supports at most five integer parameters"
                    {:phase :aarch64 :function name :arity (count params)})))
  (let [n (count params) register-frame (* 16 (quot (+ n 1) 2))
        save-frame (when (pos? register-frame)
                     (concat (sub-sp register-frame)
                             (mapcat (fn [i] (str-sp (+ 19 i) (* 8 i))) (range n))))
        restore-frame (when (pos? register-frame)
                        (concat (mapcat (fn [i] (ldr-sp (+ 19 i) (* 8 i))) (range n))
                                (add-sp register-frame)))
        params-to-saved (mapcat (fn [i] (mov-reg (+ 19 i) i)) (range n))
        expression (emit-expr body (zipmap params (range)) 0)]
    (vec (concat fuel-charge
                 (insn 0xa9bf7bfd) (insn 0x910003fd) ; stp fp,lr,[sp,#-16]!; mov fp,sp
                 save-frame params-to-saved expression restore-frame
                 (insn 0xa8c17bfd) (insn 0xd65f03c0))))) ; ldp fp,lr,[sp],#16; ret

(defn- finalize [tokens function-offset offsets literal-offsets]
  (loop [remaining tokens position 0 out []]
    (if-let [token (first remaining)]
      (cond
        (and (map? token) (:call token))
        ;; The unknown-target guard must run BEFORE `displacement` is computed.
        ;; It used to be bound alongside `target` in this same `let`, which made
        ;; the guard unreachable: `(- nil absolute)` threw a bare
        ;; NullPointerException first, so an unresolvable call surfaced as an
        ;; opaque host exception instead of this namespace's own diagnosable
        ;; `ex-info` -- the exact failure `kotoba.native.x86-64/finalize` has
        ;; always reported cleanly. Any operator this backend does not implement
        ;; reaches here through `emit-call`, so the ISA-parity gaps this commit
        ;; also closes were each surfacing as that same opaque NPE.
        (let [absolute (+ function-offset position) target (get offsets (:call token))
              _ (when-not target
                  (throw (ex-info "unknown AArch64 call target" {:target (:call token)})))
              displacement (- target absolute)]
          (when-not (zero? (mod displacement 4))
            (throw (ex-info "unaligned AArch64 BL target" {:target (:call token)})))
          (recur (next remaining) (+ position 4)
                 (into out (insn (bit-or 0x94000000
                                         (bit-and (quot displacement 4) 0x03ffffff))))))

        (and (map? token) (:string-literal token))
        (let [content (:string-literal token) offset (get literal-offsets content)]
          (when-not offset
            (throw (ex-info "unknown AArch64 string literal" {:content content})))
          (recur (next remaining) (+ position 16) (into out (load-constant-reg 0 offset))))

        :else
        (recur (next remaining) (inc position) (conj out token)))
      out)))

;; Every distinct string literal's content used anywhere in the program,
;; collected once (order-preserving, first occurrence wins) so `finalize`
;; can resolve every `{:string-literal content}` reference deterministically
;; -- the SAME source compiled twice must produce byte-identical output for
;; verifier.clj's independent re-emission check to hold.
(defn- collect-string-literals [token-bodies]
  (distinct (for [[_ tokens] token-bodies
                  token tokens
                  :when (and (map? token) (:string-literal token))]
              (:string-literal token))))

(defn emit-program [kir]
  (let [exported-names (set (or (:exports kir) (map :name (:functions kir))))
        token-bodies (mapv (fn [f] [f (emit-function f)]) (:functions kir))
        offsets (loop [items token-bodies offset 0 out {}]
                  (if-let [[f body] (first items)]
                    (recur (next items) (+ offset (code-size body)) (assoc out (:name f) offset)) out))
        code-size-total (reduce + 0 (map (fn [[_ body]] (code-size body)) token-bodies))
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
      (if-let [[function tokens] (first items)]
        (let [offset (get offsets (:name function)) body (finalize tokens offset offsets literal-offsets)]
          (recur (next items) (into code body)
                 (cond-> exports
                   (contains? exported-names (:name function))
                   (assoc (:name function)
                          {:offset offset :length (count body) :arity (count (:params function))}))))
        {:code (vec (concat code literal-bytes)) :exports exports}))))
