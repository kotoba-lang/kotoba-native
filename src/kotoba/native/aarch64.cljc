(ns kotoba.native.aarch64
  ;; `kotoba.native.peephole` is required on BOTH runtimes, so the reader
  ;; conditional that used to wrap the whole `:require` (see
  ;; `kotoba.wasm.core`'s ns form for that original reasoning) now wraps only
  ;; the cljs-only item.
  (:require [kotoba.native.peephole :as peephole]
            [kotoba.native.string-search :as string-search]
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

;; FCMP D0, D1 (0x1e612000) then CSET. The condition for each is the one that
;; is FALSE when the compare is unordered, which is what makes NaN never equal
;; and never ordered-less/greater: FCMP sets N=0 Z=0 C=1 V=1 for unordered, so
;; EQ/MI/LS/GT/GE all fail there and VS alone succeeds. eq/gt/ge reuse the very
;; CSET encodings this file's integer `=`/`>`/`>=` already emit.
(def ^:private f64-compare-ops
  {'f64-eq 0x9a9f17e0 'f64-lt 0x9a9f57e0 'f64-le 0x9a9f87e0
   'f64-gt 0x9a9fd7e0 'f64-ge 0x9a9fb7e0 'f64-unordered 0x9a9f77e0})

(def ^:private f64-unary-ops
  {'f64-abs 0x1e60c000 'f64-neg 0x1e614000 'f64-sqrt 0x1e61c000})

(declare emit-expr)
(declare record-new-binding)
(declare boxed-record-chain)

;; The caller's half of the record-parameter boundary; the x86-64 backend's
;; `box-record-argument` carries the full reasoning. A literal `record-new`
;; boxes its field expressions; a `let`-bound record was flattened into one slot
;; per field and is re-boxed from those slots in declared field order; anything
;; else is already a one-word handle and passes through.
(defn- box-record-argument [arg env]
  (cond
    (record-new-binding arg) (boxed-record-chain (vec (drop 2 arg)))
    (and (symbol? arg) (:record-fields (get env arg)))
    (let [{:keys [record-type record-fields]} (get env arg)]
      (boxed-record-chain (mapv (fn [[field-name _]] (get record-fields field-name))
                                (nth record-type 2))))
    :else arg))

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
  ;; See the x86-64 backend's `box-record-argument`: an argument denoting a
  ;; record is boxed into the pair chain the callee's parameter expects, since
  ;; a record is N slots and the ABI passes one word.
  (let [args (mapv #(box-record-argument % env) args)
        saved (mapcat (fn [i a] (concat (emit-expr a env (+ depth i)) (save-x0)))
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
(def ^:private cond-lt 11)    ; signed <
(def ^:private cond-gt 12)    ; signed >

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

;; `(kernel-subregion base length offset sublen)` -> base+offset, trapping
;; unless the sub-window fits inside the parent window.
;;
;; The load/store bounds check constrains an index within a DECLARED length,
;; and both the base and that length are supplied by the caller. So narrowing
;; a region by hand -- `(fnv (+ base object-offset) object-length)`, the shape
;; six aiueos objects use -- produced a window nothing had checked: the
;; frontend's provenance rule keeps the root traceable, but the offset and the
;; new length were free. This primitive makes the derivation itself checked,
;; so a correct entry window implies every window derived from it is correct.
;;
;; Overflow-free by construction: `offset > length` traps first, so
;; `length - offset` cannot underflow, and `sublen` is then compared against
;; that remainder rather than against `offset + sublen` (which could wrap for
;; a hostile pair). Unsigned comparisons throughout, so a negative i64 arrives
;; as a huge unsigned value and trips the same check rather than sneaking
;; under a signed one.
;;
;; Byte layout from the first branch, for the displacements below:
;;   +0 cbz x1,trap  +4 cmp x3,x2  +8 b.hi trap  +12 sub x4,x2,x3
;;   +16 cmp x5,x4   +20 b.hi trap +24 add x0,x1,x3  +28 b skip  +32 brk  +36 skip
(defn- emit-kernel-subregion [[base length offset sublen] env depth]
  (vec (concat
        (emit-expr base env depth) (save-x0)
        (emit-expr length env (+ depth 1)) (save-x0)
        (emit-expr offset env (+ depth 2)) (save-x0)
        (emit-expr sublen env (+ depth 3))   ; x0 = sublen
        (mov-reg 5 0)                        ; x5 = sublen
        (ldr-sp 3 0) (add-sp 16)             ; x3 = offset
        (ldr-sp 2 0) (add-sp 16)             ; x2 = length
        (ldr-sp 1 0) (add-sp 16)             ; x1 = base
        (cbz-reg 1 32)                       ; cbz x1, trap   (null parent)
        (insn 0xeb02007f)                    ; cmp x3, x2     (offset vs length)
        (b-cond cond-hi 24)                  ; b.hi trap      (offset > length)
        (insn 0xcb030044)                    ; sub x4, x2, x3 (remaining = length-offset)
        (insn 0xeb0400bf)                    ; cmp x5, x4     (sublen vs remaining)
        (b-cond cond-hi 12)                  ; b.hi trap
        (insn 0x8b030020)                    ; add x0, x1, x3 (result = base+offset)
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
   ;; construction primitive (see `vector-new` in emit-expr). All six offsets
   ;; stay inside LDR's unsigned-offset imm12 range (8 * 4095), the same
   ;; range `ldr-context` already encodes for every offset above.
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


;; See the x86-64 backend's own comment for why this slice needs no host
;; callback and no ABI change: an all-ASCII literal makes every byte offset a
;; code-point boundary, so `kotoba.kir`'s boundary rule is discharged at compile
;; time and only a range check and one pair construction remain at runtime.
(defn- ascii-literal? [form]
  (and (string? form) (every? #(< % 0x80) (map #(bit-and (int %) 0xff) (utf8-bytes form)))))

(defn- emit-string-substring-of-ascii-literal [content start-form end-form env depth]
  (let [length (count (utf8-bytes content))
        operands (concat (emit-expr start-form env depth) (save-x0)
                         (emit-expr end-form env (inc depth)) (save-x0)
                         [{:string-literal content}]   ; x0 = literal byte offset
                         (restore-to 2)                ; x2 = end
                         (restore-to 1))               ; x1 = start
        bound (load-constant-reg 3 length)
        success (vec (concat (insn 0xcb010042)         ; sub x2,x2,x1  -> end-start
                             (insn 0x8b010001)         ; add x1,x0,x1  -> offset+start
                             (sub-sp 16) (str-sp 7 0)
                             (mov-reg 0 7) (ldr-context 16 56) (insn 0xd63f0200)
                             (ldr-sp 7 0) (add-sp 16)
                             (branch 8)))              ; skip the trap
        ;; Distances are derived from the measured blocks, never written out.
        n-bound (count bound)
        s (count success)
        trap-at (+ 4 4 4 4 n-bound 4 4 s)]
    (vec (concat operands
                 (cmp-imm 1 0) (b-cond cond-lt (- trap-at 4))    ; cmp x1,#0 ; b.lt  (start < 0)
                 (insn 0xeb01005f) (b-cond cond-lt (- trap-at 12))   ; cmp x2,x1 ; b.lt  (end < start)
                 bound
                 (insn 0xeb03005f)
                 (b-cond cond-gt (- trap-at (+ 16 n-bound 4)))       ; cmp x2,x3 ; b.gt  (end > length)
                 success
                 (insn 0xd4200000)))))                               ; trap: BRK

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

;; See the x86-64 backend: a record binding expands into one binding PER FIELD,
;; and a field that is itself a record-new expands again, so a nested record is
;; FLATTENED into consecutive slots and never needs a runtime representation.
(defn- expand-binding [name value env depth d]
  (if-let [[type field-exprs] (record-new-binding value)]
    (let [field-names (map first (nth type 2))]
      (loop [fs field-exprs fns field-names i 0 dd d e env code [] fm {}]
        (if (seq fs)
          (let [child (symbol (str name "-" i))
                [c e' dd'] (expand-binding child (first fs) e depth dd)]
            (recur (next fs) (next fns) (inc i) dd' e' (concat code c)
                   (assoc fm (first fns) child)))
          [code (assoc e name {:record-type type :record-fields fm}) dd])))
    [(concat (emit-expr value env d) (save-x0))
     (assoc env name {:let-depth d})
     (inc d)]))

;; The record a form denotes, or nil -- a symbol bound to one, or a `record-get`
;; selecting a record-typed field of one.
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

(defn- emit-let [bindings body env depth]
  (let [pairs (partition 2 bindings)]
    (loop [remaining pairs d depth env env code []]
      (if-let [[name value] (first remaining)]
        (let [[c env' d'] (expand-binding name value env depth d)]
          (recur (next remaining) d' env' (concat code c)))
        (let [body-code (emit-expr body env d)]
          (vec (concat code body-code (pop-n (- d depth)))))))))

;; The declared function names of the program being emitted. This backend's
;; `emit-expr` takes only env and depth, so the set rides a binding rather than
;; threading a ctx map through every arm.
(def ^:dynamic *function-names* #{})

;; See the x86-64 backend: a record crossing a function boundary is boxed into a
;; pair chain, which is one word and uses only the arena contract this backend
;; already has. Both directions are source rewrites into existing forms.
(defn- boxed-record-chain [field-exprs]
  (reduce (fn [rest-chain v] (list 'pair v rest-chain)) 0 (reverse field-exprs)))

(defn- boxed-record-projection [handle-form field-index]
  (list 'pair-first (nth (iterate (fn [f] (list 'pair-second f)) handle-form) field-index)))

;; See the x86-64 backend's `record-result-name` and `box-record-tails`: a
;; declared result reaches a backend either expanded (`[:record :t/r [...]]`) or
;; as the unexpanded schema reference (`[:ref :t/r]`), and a `record-new` is in
;; tail position through `if`, `let` and `do` -- the same positions this
;; backend's own `emit-expr` produces a function's value from.
(defn- record-result-name [result]
  (when (and (vector? result) (<= 2 (count result))
             (contains? #{:record :ref} (first result)))
    (second result)))

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

(defn- emit-record-get-of-new [type value-form field env depth]
  ;; See the x86-64 backend: a record we already know has each scalar field in
  ;; its own slot, so the projection is an ordinary depth-relative read.
  (if-let [bound (resolve-record-binding value-form env)]
    (do
      (when-not (= type (:record-type bound))
        (throw (ex-info "record-get's schema must be identical to the schema its operand was bound with"
                        {:phase :aarch64 :expected type :actual (:record-type bound)})))
      (let [child (get (:record-fields bound) field)]
        (when-not child
          (throw (ex-info "record-get references an undeclared field"
                          {:phase :aarch64 :type type :field field})))
        (when (:record-fields (get env child))
          (throw (ex-info "a record-valued projection may only appear as the operand of record-get"
                          {:phase :aarch64 :type type :field field})))
        (emit-expr child env depth)))
    (if (or (and (seq? value-form) (symbol? (first value-form))
                 (contains? *function-names* (first value-form)))
            ;; A PARAMETER holding a record arrived boxed for the same reason a
            ;; call's result does: the caller had N slots and the ABI has one
            ;; word. `env` binds a parameter to its bare index, not the
            ;; `{:record-fields …}` map a flattened `let` binding gets. A `let`
            ;; SLOT holding a boxed handle is the same one word arriving by a
            ;; different route and walks the same chain, so what distinguishes
            ;; "this name is a word" from "this name is N words" is
            ;; `:record-fields`, not `map?` -- see the x86-64 backend and
            ;; docs/adr/0004. Held back one release because kotoba.verifier
            ;; rejected the shape; its ADR 0004 admits it.
            (and (symbol? value-form) (not (:record-fields (get env value-form)))
                 (contains? env value-form)))
      (let [fields (nth type 2)
            field-index (first (keep-indexed (fn [i [n _]] (when (= n field) i)) fields))]
        (when (nil? field-index)
          (throw (ex-info "record-get references an undeclared field"
                          {:phase :aarch64 :type type :field field})))
        (emit-expr (boxed-record-projection value-form field-index) env depth))
      (emit-record-get-of-new-construction type value-form field env depth))))

(defn- emit-record-get-of-new-construction [type value-form field env depth]
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

;; See the x86-64 backend for both helpers: slot width of a payload type, and
;; describing an already-pushed slot region as a value of a given type.
(defn- type-slot-width [t]
  (if (and (vector? t) (= 3 (count t)) (= :record (first t)) (sequential? (nth t 2)))
    (reduce + (map (comp type-slot-width second) (nth t 2)))
    1))

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
  "Mirrors `backend/x86-64.cljc`'s own `emit-variant-dispatch` exactly, on
  this backend's own AArch64 instruction encodings and 16-byte let-slot
  convention. See that function's docstring for the full contract (including
  why ORDINAL-EXPR is intentionally NOT restricted to a compiler-derived
  in-range value here)."
  [ordinal-expr payload-expr branch-specs env depth]
  (let [push-ordinal (vec (concat (emit-expr ordinal-expr env depth) (save-x0)))
        payload-depth (inc depth)
        ;; Sized by the WIDEST declared case -- see the x86-64 backend for why
        ;; the padding is not optional.
        payload-slots (reduce max 1 (map #(type-slot-width (:payload-type %)) branch-specs))
        [payload-code _ payload-end] (expand-binding (quote $variant-payload) payload-expr env depth payload-depth)
        push-payload (vec (concat payload-code
                                  (mapcat (fn [_] (concat (load-constant 0) (save-x0)))
                                          (range (max 0 (- payload-slots (- payload-end payload-depth)))))))
        dispatch-depth (+ depth 1 payload-slots)
        load-tag (load-let 0 depth dispatch-depth)
        n (count branch-specs)
        ;; add sp, sp, #32 -- drops the two synthetic 16-byte slots this
        ;; dispatch alone pushed, run at the end of EVERY case body.
        cleanup (add-sp (* 16 (inc payload-slots)))
        body-codes (mapv (fn [{:keys [binder body payload-type]}]
                           (vec (emit-expr body
                                           (bind-over-slots binder payload-type payload-depth env)
                                           dispatch-depth)))
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
    (let [branch-specs (mapv (fn [[case-tag case-payload-type] [_ binder body]]
                               {:binder binder :body body :payload-type case-payload-type})
                             cases branches)]
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
    (keyword? form) (emit-string-literal (str form))
    (symbol? form)
    (let [binding (get env form)]
      ;; See the x86-64 backend: a record binding is not a value, and reaching
      ;; `load-let` with its nil `:let-depth` would only produce a
      ;; NullPointerException, naming nothing.
      (when (:record-fields binding)
        (throw (ex-info "a record-valued binding may only appear as the operand of record-get"
                        {:phase :aarch64 :binding form})))
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
        (and (= op 'string-substring) (= 3 (count args))
             (ascii-literal? (first args)))
        (emit-string-substring-of-ascii-literal (first args) (second args) (nth args 2) env depth)

        ;; The two string SEARCH operations. See `kotoba.native.string-search`;
        ;; the rewrite is shared with the x86-64 backend rather than restated
        ;; here, so the two ISAs cannot drift in their search semantics.
        (and (= op 'string-contains?) (= 2 (count args)))
        (emit-expr (string-search/lower-contains args) env depth)

        (and (= op 'string-replace-all) (= 3 (count args)))
        (emit-expr (string-search/lower-replace-all args) env depth)

        ;; An f64 vector operation IS the i64 one (see vector-op-aliases):
        ;; rewrite the head and re-dispatch, so there is exactly one lowering
        ;; per operation rather than two that must be kept in step.
        (contains? vector-op-aliases op)
        (emit-expr (cons (get vector-op-aliases op) args) env depth)

        ;; KIR's vector-new is variadic; the context ABI is not. The arity is
        ;; static, so this expands to an empty vector plus one conj per
        ;; element -- and because each conj extends the arena region the
        ;; previous one just wrote, the host takes its copy-free append path
        ;; throughout, making construction linear rather than quadratic.
        (= op 'vector-new)
        (emit-expr (reduce (fn [acc item] (list 'vector-conj acc item))
                           (list 'vector-new-empty)
                           args)
                   env depth)

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
                    env depth))

        (contains? '#{pair pair-first pair-second
                      kgraph-assert! kgraph-get kgraph-count kgraph-entity-at
                      string-byte-length string=? string-concat
                      string-substring string-code-point-at
                      vector-new-empty vector-conj vector-count
                      vector-at vector-assoc vector-drop} op)
        (emit-heap-call op args env depth)
        ;; Pure representation changes: the bits are already in x0.
        (contains? '#{f64-from-bits f64-to-bits} op)
        (emit-expr (first args) env depth)
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
                   env depth)
        (and (= op 'keyword-from-string) (= 1 (count args)))
        (emit-expr (list 'string-concat ":" (first args)) env depth)
        (contains? f64-compare-ops op)
        (emit-binary (first args) (second args)
                     (concat fmov-d0-x0 fmov-d1-x1 (insn 0x1e612000)
                             (insn (f64-compare-ops op)))
                     env depth)
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

        ;; `kotoba.compiler.frontend`'s `i64-operations` -- see the x86-64
        ;; backend's own comment for why these were previously reported as an
        ;; "unknown call target" rather than as unimplemented.
        ;;
        ;; MVN is ORN with Rn=xzr, exactly as `mov-reg` is ORR with Rn=xzr:
        ;; 0xaa000000 (ORR) | 0x200000 (N) | Rm=x0 | Rn=xzr | Rd=x0.
        ;; See the x86-64 backend's comment: zero is false, anything else is
        ;; true, matching `kotoba.kir/kotoba-false?`. `cset x0, eq` is the same
        ;; encoding this file's `=` comparison already uses, so the two agree.
        (and (= op 'bool-not) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env depth)
                     (insn 0xf100001f)     ; subs xzr,x0,#0
                     (insn 0x9a9f17e0)))   ; cset x0,eq

        (and (= op 'bit-not) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env depth) (insn 0xaa2003e0)))

        ;; The count rides the ordinary binary window and so arrives in x1, the
        ;; register the variable-shift group reads. No range check is emitted:
        ;; the frontend admits the count only as an integer literal in [0,63],
        ;; so LSLV/ASRV/LSRV's own mod-64 truncation is unreachable -- the same
        ;; reasoning, and the same reachable range, as the x86-64 CL path, which
        ;; is what makes the two ISAs agree without either masking explicitly.
        ;;
        ;; Data-processing (2 source), Rm=x1 / Rn=x0 / Rd=x0, cross-checked
        ;; against `signed-division`'s own SDIV `0x9ac10c00` in this file: same
        ;; base, same Rm placement, opcode field 001000/001010/001001.
        ;; ASRV for `i64-shift-right` and LSRV for `u64-shift-right`, matching
        ;; `kotoba.kir`'s `i64-shr`/`u64-shr`.
        ;; `i32-operations` -- see the x86-64 backend's own comment for why
        ;; these need no new value representation: there is no `:i32` type,
        ;; only i64 words with 32-bit wrapping, and the sole difference is
        ;; that `i32-*` results are SIGN-extended from bit 31 while `u32-*`
        ;; results are ZERO-extended.
        ;;
        ;; AArch64 gives the unsigned half for free the same way x86-64 does:
        ;; writing a `w` register zeroes the upper 32 bits, so a `w`-form
        ;; operation is already `u32-wrap`ped. The signed forms need one
        ;; `sxtw x0, w0` after. Every encoding below is the `sf=0` sibling of
        ;; the 64-bit form used a few lines down, so the two move together.
        (and (= op 'i32-wrap) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env depth) (insn 0x93407c00)))  ; sxtw x0,w0

        (and (= op 'u32-wrap) (= 1 (count args)))
        (vec (concat (emit-expr (first args) env depth) (insn 0x2a0003e0)))  ; mov w0,w0

        (contains? '#{i32-wrapping-add i32-wrapping-mul i32-xor
                      i32-shift-left i32-shift-right u32-shift-right} op)
        (let [[left right] args
              sxtw (insn 0x93407c00)]
          (vec (concat (emit-expr left env depth)
                       (emit-rhs-window right env depth)
                       (case op
                         i32-wrapping-add (concat (insn 0x0b010000) sxtw)  ; add w0,w0,w1
                         i32-wrapping-mul (concat (insn 0x1b017c00) sxtw)  ; mul w0,w0,w1
                         i32-xor (concat (insn 0x4a010000) sxtw)           ; eor w0,w0,w1
                         i32-shift-left (concat (insn 0x1ac12000) sxtw)    ; lslv w0,w0,w1
                         i32-shift-right (concat (insn 0x1ac12800) sxtw)   ; asrv w0,w0,w1
                         ;; logical: the w-form write already zero-extends
                         u32-shift-right (insn 0x1ac12400)))))             ; lsrv w0,w0,w1

        (contains? '#{i64-shift-left i64-shift-right u64-shift-right} op)
        (let [[value count-form] args]
          (vec (concat (emit-expr value env depth)
                       (emit-rhs-window count-form env depth)
                       (case op
                         i64-shift-left (insn 0x9ac12000)    ; lslv x0,x0,x1
                         i64-shift-right (insn 0x9ac12800)   ; asrv x0,x0,x1
                         u64-shift-right (insn 0x9ac12400))))) ; lsrv x0,x0,x1
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
        (= op 'kernel-subregion) (emit-kernel-subregion args env depth)
        (= op 'kernel-store-u8) (emit-kernel-store-u8 args 512 env depth)
        (= op 'kernel-store-u8-4k) (emit-kernel-store-u8 args 4096 env depth)
        (= op 'kernel-load-u8) (emit-kernel-load-u8 args 512 env depth)
        (= op 'kernel-load-u8-4k) (emit-kernel-load-u8 args 4096 env depth)
        (= op 'kernel-load-u8-16k) (emit-kernel-load-u8 args 16384 env depth)
        (= op 'kernel-store-u32) (emit-kernel-store-u32 args 512 env depth)
        (= op 'kernel-load-u32) (emit-kernel-load-u32 args 512 env depth)
        :else (emit-call op args env depth)))))

(defn- emit-function [{:keys [name params body result]}]
  (when (> (count params) 5)
    (throw (ex-info "AArch64 fuel ABI supports at most five integer parameters"
                    {:phase :aarch64 :function name :arity (count params)})))
  (let [body (if-let [record-name (record-result-name result)]
               (box-record-tails body record-name)
               body)
        n (count params) register-frame (* 16 (quot (+ n 1) 2))
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

;; A call target that does not resolve is an OPERATOR this backend has not
;; implemented -- not a typo, and not a missing function.
;;
;; Both routes into this backend prove that before emission. `kotoba.compiler.
;; frontend` rejects a call to a name it does not know with "operation has no
;; admitted lowering" (`:phase :subset`), and `kotoba.verifier`, which treats
;; KIR as hostile, rejects any operation outside its own signature table before
;; re-emitting. So by the time a `{:call op}` token exists, `op` is either a
;; function declared in this very program -- and every declared function is in
;; `offsets`, because `emit-program` builds it from `(:functions kir)` -- or an
;; operation the frontend admitted and this file's `emit-expr` has no case for.
;;
;; Saying "unknown call target" therefore reported the one thing it could not
;; be. Every operator missing from a backend surfaced as though the program had
;; called a function that does not exist, which is how `bit-and`/`bit-or`/
;; `bit-xor`, `kernel-load-u32`/`kernel-store-u32` and the whole i64 family each
;; sat unnoticed until someone went looking. The 11 x86-only privileged
;; operations still land here on AArch64 by design, and now say so.
(defn- unimplemented-operation! [op]
  (throw (ex-info "operation not implemented on this backend"
                  {:phase :aarch64 :backend :aarch64-kotoba-v1 :operation op})))

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
              _ (when-not target (unimplemented-operation! (:call token)))
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
  (let [;; See the x86-64 backend's `emit-program`: the export set is read
        ;; from the DECLARED functions, before the search helpers are appended.
        exported-names (set (or (:exports kir) (map :name (:functions kir))))
        functions (string-search/augment-functions (:functions kir))
        token-bodies (binding [*function-names* (set (map :name functions))]
                       (mapv (fn [f] [f (emit-function f)]) functions))
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
                          (cond-> {:offset offset :length (count body)
                                   :arity (count (:params function))}
                            (and (empty? (:params function))
                                 (contains? #{:vector-i64 :vector-f64}
                                            (:result function)))
                            (assoc :marshal
                                   {:format :kotoba.kexe-export/copy-v1
                                    :result (:result function)
                                    :ownership :invocation-copy
                                    :maximum-items 16384}))))))
        {:code (vec (concat code literal-bytes)) :exports exports}))))
