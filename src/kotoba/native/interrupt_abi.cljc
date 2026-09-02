(ns kotoba.native.interrupt-abi
  "isr: the x86-64 interrupt entry a Kotoba body is called from.

  An interrupt is the one call into a kernel that nothing in the kernel makes.
  The CPU builds a frame, jumps to whatever address the IDT gate names, and
  from that instant the machine is in a state no compiled function's prologue
  is written for: no context register, no fuel, a direction flag that may be
  set, and fifteen general registers belonging to whatever was interrupted.
  This namespace is the fixed byte sequence that turns that into an ordinary
  four-argument SysV call and turns the return back into an `iretq`.

  It is TOOLCHAIN-GENERATED, which is the whole point. aiueos's
  `kernel/entry.S` writes this sequence by hand, once per vector, in assembly
  that is not Kotoba and is not emitted by anything -- and the K16 pure-native
  profile refuses a link that contains a handwritten object. A generated entry
  is admitted by that profile because it is reproducible: the same table and
  the same body offsets produce the same bytes.

  WHAT IT IS NOT. It contains no decisions. It does not read the error code to
  work out what happened, does not choose whether to acknowledge an interrupt
  controller, and does not act on what the body returns. Every one of those is
  a judgement, and a judgement belongs in the `.kotoba` body where it can be
  read, typed and verified -- the same boundary aiueos ADR-0015 draws around
  its C mechanism. The entry's job is to make the body callable and to leave
  the machine exactly as it found it.

  Two routes use this:

    IMAGE   `kotoba.native.elf64/package-kernel` lays one entry per vector in
            a reserved region of `.text` and records its base in the kernel
            context, so `kernel-isr-entry-address` can load it.
    OBJECT  `package-kernel-object` emits ONE entry as the object's public
            symbol, so a C IDT builder in the transitional image can install
            `kotoba_aiueos_isr_<vector>` directly. There is no entry table in
            an object -- objects cannot reference each other -- so
            `kernel-isr-entry-address` has no answer there and is refused."
  (:require [clojure.string :as str]))

;; ── the name ───────────────────────────────────────────────────────────────
;;
;; An entry is named for its vector: `aiueos-isr-3` handles vector 3. The name
;; carries the number because the generated sequence has to know its own
;; vector -- it passes it to the body as the first argument -- and a mnemonic
;; table (`bp`, `pf`, ...) would be a second place to keep in sync across
;; kotoba-sema, this file and both packagers, kept equal only by review. A
;; decimal suffix is derivable in both directions with no table at all.
;;
;; kotoba-sema refuses `aiueos-isr-bp` at analysis, which is where a source
;; mistake should surface. This file repeats the rule because it also has to
;; answer for an artifact it did not analyze.

(def entry-prefix "aiueos-isr-")

;; Vectors 0..63. The architectural exceptions are 0..31 and the rest is room
;; for the remapped legacy PIC (32..47) and a few message-signalled lines,
;; which is what a NIC driver needs. It is a RESERVATION in the image's text
;; segment -- one fixed-size entry per vector, whether or not a body exists --
;; so widening it costs bytes in every kernel image that has any entry at all.
;; That makes it an ADR-sized decision rather than a constant to nudge.
(def vector-limit 64)

;; The vectors on which the CPU pushes an error code before the frame. x86-64:
;; #DF 8, #TS 10, #NP 11, #SS 12, #GP 13, #PF 14, #AC 17, #CP 21, #VC 29,
;; #SX 30. Every other vector is entered with no error code, and the entry
;; pushes a zero in its place so that ONE frame layout serves both -- which is
;; what lets the body take the same four arguments whatever it handles.
(def error-code-vectors #{8 10 11 12 13 14 17 21 29 30})

(defn entry-vector
  "The vector `name` declares, or nil when it is not an entry name.

  Nil for a name that merely starts with the prefix and does not continue as a
  decimal vector inside the table. Callers refuse on nil; they do not guess."
  [name]
  (let [text (str name)]
    (when (and (str/starts-with? text entry-prefix)
               (re-matches #"(0|[1-9][0-9]*)" (subs text (count entry-prefix))))
      (let [v (#?(:clj Long/parseLong :cljs js/parseInt)
               (subs text (count entry-prefix)))]
        (when (< v vector-limit) v)))))

(defn entry-symbol
  "The public ELF symbol for the entry at `vector`."
  [vector]
  (str "kotoba_aiueos_isr_" vector))

(defn entry-name
  "The Kotoba function name for the entry at `vector` -- `entry-vector`'s
  inverse, used by the image packager to look up a body."
  [vector]
  (symbol (str entry-prefix vector)))

;; The body's SysV signature, restated here because this file is what calls
;; it. kotoba-sema enforces the same four `:i64` parameters and `:i64` result
;; on the source; an artifact's export record carries only an arity, so this
;; is the half of the contract a packager can still check.
(def body-arity 4)

;; ── the frame ──────────────────────────────────────────────────────────────
;;
;; Offsets from RSP AT THE CALL SITE -- after the whole prologue, immediately
;; before `call`. Reading them there rather than at entry is deliberate: it is
;; the one point where the layout is identical for a vector with an error code
;; and one without, because the entry has already supplied the missing zero.
;;
;;   +0    saved fuel        pushed by the prologue (see `fuel` below)
;;   +8    r15  +16 r14  +24 r13  +32 r12  +40 r11  +48 r10  +56 r9  +64 r8
;;   +72   rdi  +80 rsi  +88 rbp  +96 rbx  +104 rdx  +112 rcx  +120 rax
;;   +128  error code       CPU-pushed, or the prologue's zero
;;   +136  rip     +144 cs     +152 rflags     +160 rsp     +168 ss
;;
;; The five words from +136 are the frame the CPU itself builds (Intel SDM
;; Vol 3A 6.14.1); the fifteen below them are this entry's, pushed rax-first
;; so that `pop` in the mirror order restores them.

(def frame-offsets
  {:saved-fuel 0
   :r15 8 :r14 16 :r13 24 :r12 32 :r11 40 :r10 48 :r9 56 :r8 64
   :rdi 72 :rsi 80 :rbp 88 :rbx 96 :rdx 104 :rcx 112 :rax 120
   :error-code 128 :rip 136 :cs 144 :rflags 152 :rsp 160 :ss 168})

;; The context slot holding the base of the image's entry region.
;; `kernel-isr-entry-address` lowers to a load from it plus `vector * 128`.
;;
;; 0x148 and not lower: the recovery handler spills seven registers into
;; 0x110..0x140 and publishes a frame base and stack top at 0x100/0x108, and
;; the double-fault handler owns 0x180..0x190. 0x148 is the first free
;; quadword above the first block and below the second.
;;
;; This is the ONE number this namespace and `kotoba.native.x86_64` both
;; depend on, which is why it lives here and is read from here on both sides.
(def context-entry-base-offset 0x148)

;; Every entry occupies the same number of bytes whether or not a body exists
;; for its vector, because `kernel-isr-entry-address` computes an address by
;; multiplication rather than by consulting a table. The longest form below is
;; 112 bytes; 128 leaves room and keeps the arithmetic a shift.
(def entry-stride 128)

;; The fuel an entry replenishes before calling. ONE tier for every entry, and
;; a small one: an interrupt body reads a device's status registers, decides,
;; acknowledges and returns. It is the one place in a kernel where an
;; unbounded loop cannot be waited out, because the interrupt is disabled
;; until it returns and the next one is already pending.
;;
;; 4096 is the tier `elf64` gives the frame-walking objects -- a checksum over
;; a 1500-byte Ethernet payload is ~750 charged calls -- so a body that walks
;; one received frame fits with room, and one that walks a queue of them does
;; not. That is the intended shape: an entry that needs more work than this
;; should hand the work to a task rather than do it with interrupts off.
;;
;; The budget is per INTERRUPT, not per boot, because the replenish is inside
;; the entry. It is also SAVED AND RESTORED around the call, so an interrupt
;; cannot lift the budget of whatever it interrupted.
(def entry-fuel 4096)

;; ── the bytes ──────────────────────────────────────────────────────────────

(defn- le32
  "Four little-endian bytes of N, signed or unsigned.

  Arithmetic rather than bit operations, because a RIP-relative displacement
  is routinely negative and `bit-and` with 0xffffffff produces a value outside
  the 32-bit signed range that `(int n)` then refuses on the JVM and that
  `bit-shift-right` silently truncates on ClojureScript. `mod` answers with a
  non-negative number on both runtimes for a negative input, which is the
  two's-complement pattern this needs."
  [n]
  (let [v (mod n 4294967296)]
    (mapv #(mod (quot v (bit-shift-left 1 (* 8 %))) 256) (range 4))))

;; push rax, rcx, rdx, rbx, rbp, rsi, rdi, r8..r15 -- fifteen registers, every
;; one except RSP, which the CPU has already recorded in the frame. RBP is in
;; the list: a body that used it as a frame pointer would otherwise return to
;; interrupted code holding someone else's.
(def ^:private gpr-pushes
  [[0x50] [0x51] [0x52] [0x53] [0x55] [0x56] [0x57]
   [0x41 0x50] [0x41 0x51] [0x41 0x52] [0x41 0x53]
   [0x41 0x54] [0x41 0x55] [0x41 0x56] [0x41 0x57]])

(def ^:private gpr-pops
  [[0x41 0x5f] [0x41 0x5e] [0x41 0x5d] [0x41 0x5c]
   [0x41 0x5b] [0x41 0x5a] [0x41 0x59] [0x41 0x58]
   [0x5f] [0x5e] [0x5d] [0x5b] [0x5a] [0x59] [0x58]])

(defn- mov-reg-rsp-disp32
  "mov <reg>,[rsp+disp32]. REG is the 3-bit encoding; disp32 always, so the
  instruction is a fixed eight bytes whatever the offset."
  [reg disp]
  (into [0x48 0x8b (+ 0x84 (* 8 reg)) 0x24] (le32 disp)))

(defn entry-bytes
  "The complete interrupt entry for one vector.

  `vector`               which vector this entry serves
  `fuel`                 the replenish this entry writes before calling
  `context-displacement` RIP-relative displacement to the context, measured
                         from the END of the `lea` (the object route passes 0
                         and relocates it)
  `call-displacement`    RIP-relative displacement to the body, measured from
                         the END of the `call`

  The sequence, and why each piece is there:

      push 0                    only when the CPU pushed no error code, so
                                that one frame layout serves every vector
      push rax .. push r15      fifteen registers; RSP is already in the frame
      cld                       the interrupted code's direction flag is
                                unknown, and compiled code assumes it clear.
                                RFLAGS is restored by `iretq`, so this is not
                                undone by hand
      lea r9,[rip+context]      the context register. NOT inherited: an
                                interrupt can arrive while the boot shim is
                                still running, or (in the transitional image)
                                while C code holds r9 for something else
      push qword [r9+8]         save the interrupted computation's fuel...
      mov qword [r9+8],fuel     ...before replenishing, because the counter is
                                SHARED in the image route. Without the save,
                                an interrupt silently RAISES the remaining
                                budget of whatever it interrupted, and a fuel
                                bound that an interrupt can lift is not a
                                bound. It also supplies the 16-byte alignment
                                the object wrapper gets from `sub rsp,8`
      mov edi,vector            the four SysV arguments, read at the one point
      mov rsi,[rsp+128]         where the layout is the same for a vector with
      mov rdx,[rsp+136]         an error code and one without
      mov rcx,[rsp+160]
      call body
      pop qword [r9+8]          restore the interrupted fuel. r9 is still the
                                context here; it is restored seven pops later
      pop r15 .. pop rax
      add rsp,8                 drop the error code -- the CPU's or ours
      iretq

  RAX IS DISCARDED. The body returns an i64 and this sequence pops over it.
  Acting on it would mean the entry deciding something -- 'bit 0 means the
  interrupt was acknowledged' is a protocol, and a protocol is a judgement.
  The body acknowledges its own controller with `kernel-out-u8`, where the
  decision is visible in Kotoba and the compiler can see the effect. A return
  value is still useful to a caller that invokes the body directly (a test, or
  the object route's C caller through a non-interrupt path); it is simply not
  something this sequence reads.

  ALIGNMENT. In 64-bit mode the CPU aligns RSP to 16 before pushing the frame
  (Intel SDM Vol 3A 6.14.2), so RSP is 8 mod 16 after a five-word frame and 0
  mod 16 after a six-word one. The synthetic error-code push makes both 0; the
  fifteen GPR pushes make both 8; the fuel push makes both 0 -- which is what
  SysV requires immediately before a `call`. There is deliberately no
  `sub rsp,8` here: the object wrapper needs one because it pushes nothing,
  and adding one here would MIS-align by eight."
  [{:keys [vector fuel context-displacement call-displacement]}]
  (vec (concat
        (when-not (contains? error-code-vectors vector) [0x6a 0x00])
        (apply concat gpr-pushes)
        [0xfc]
        [0x4c 0x8d 0x0d] (le32 context-displacement)
        [0x41 0xff 0x71 0x08]
        [0x49 0xc7 0x41 0x08] (le32 fuel)
        [0xbf] (le32 vector)
        (mov-reg-rsp-disp32 6 (:error-code frame-offsets))
        (mov-reg-rsp-disp32 2 (:rip frame-offsets))
        (mov-reg-rsp-disp32 1 (:rsp frame-offsets))
        [0xe8] (le32 call-displacement)
        [0x41 0x8f 0x41 0x08]
        (apply concat gpr-pops)
        [0x48 0x83 0xc4 0x08]
        [0x48 0xcf])))

;; Where the two relocatable fields sit inside `entry-bytes`, so a packager
;; can patch or relocate them without recounting the sequence. Both are
;; measured from the start of the entry.
(defn context-displacement-offset [vector]
  (+ (if (contains? error-code-vectors vector) 0 2)
     (reduce + (map count gpr-pushes))   ; 23
     1                                   ; cld
     3))                                 ; lea r9,[rip+ -- disp32 follows

(defn call-displacement-offset [vector]
  (+ (context-displacement-offset vector)
     4    ; the displacement itself
     4    ; push qword [r9+8]
     8    ; mov qword [r9+8], imm32
     5    ; mov edi, imm32
     8 8 8 ; the three frame reads
     1))  ; the call opcode -- disp32 follows

(defn entry-size [vector]
  (+ (call-displacement-offset vector)
     4                                   ; the call displacement
     4                                   ; pop qword [r9+8]
     (reduce + (map count gpr-pops))     ; 23
     4                                   ; add rsp,8
     2))                                 ; iretq

;; An entry whose vector has no body. It is REACHABLE -- the region is indexed
;; by multiplication, so every vector in the table has an address whether or
;; not anything installed it -- and a spurious interrupt landing here must not
;; run the neighbouring entry's prologue against the wrong frame.
;;
;; `cli; hlt; jmp $-1` is the fail-closed answer: it stops rather than
;; returning into code that has no idea an interrupt occurred. Filled with
;; `int3` so that a jump into the middle of the slot also stops.
(def absent-entry-bytes
  (into [0xfa 0xf4 0xeb 0xfd] (repeat (- entry-stride 4) 0xcc)))

;; ── the address ────────────────────────────────────────────────────────────
;;
;; `kernel-isr-entry-address` answers with `entry-base + vector * stride`,
;; where the base is the context slot above. Two shapes, because the two
;; lowering paths in `kotoba.native` hand their operand over in different
;; registers; both are built from the constants in this file so the stride,
;; the ceiling and the slot have one home.
;;
;; The bound is emitted, not assumed. A vector outside the table has no entry,
;; and the region is indexed by MULTIPLICATION rather than by consulting a
;; table, so an unbounded index would compute an address past the region and
;; hand it to an IDT gate. `ud2` is the same trap the bounded memory
;; primitives raise, and it surfaces as vector 6.

(def entry-stride-shift
  (let [shift 7]
    (when-not (= entry-stride (bit-shift-left 1 shift))
      (throw (ex-info "isr entry stride must stay a power of two"
                      {:stride entry-stride :shift shift})))
    shift))

;; The ceiling is compared with an 8-bit immediate, which is exact for any
;; value up to 127. Raising `vector-limit` past that needs a different `cmp`
;; encoding, so it fails here rather than emitting a truncated comparison.
(when (> vector-limit 127)
  (throw (ex-info "isr vector ceiling exceeds the imm8 bound check"
                  {:limit vector-limit})))

(defn entry-address-from-rax
  "The vector arrives in RAX and the address is left in RAX. Used by the
  direct x86-64 lowering arm."
  []
  (vec (concat [0x48 0x83 0xf8 vector-limit]        ; cmp rax, vector-limit
               [0x72 0x02]                          ; jb +2
               [0x0f 0x0b]                          ; ud2
               [0x48 0xc1 0xe0 entry-stride-shift]  ; shl rax, 7
               [0x49 0x03 0x81]                     ; add rax,[r9+disp32]
               (le32 context-entry-base-offset))))

(defn entry-address-r10-to-r11
  "The vector arrives in R10 and the address is left in R11. Used by the
  machine-IR privileged arm, whose scratch tier is r10/r11 and whose caller
  copies the result out of r11."
  []
  (vec (concat [0x49 0x83 0xfa vector-limit]        ; cmp r10, vector-limit
               [0x72 0x02]                          ; jb +2
               [0x0f 0x0b]                          ; ud2
               [0x4d 0x89 0xd3]                     ; mov r11, r10
               [0x49 0xc1 0xe3 entry-stride-shift]  ; shl r11, 7
               [0x4d 0x03 0x99]                     ; add r11,[r9+disp32]
               (le32 context-entry-base-offset))))
