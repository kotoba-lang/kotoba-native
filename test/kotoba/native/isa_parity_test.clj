(ns kotoba.native.isa-parity-test
  "The two native backends must admit the same operator surface, except where
  an operator names a facility only one ISA has.

  Before this namespace existed, that contract was maintained by nobody: an
  operator implemented on one backend and forgotten on the other produced no
  diagnostic at all at the point of divergence. It fell through the operator
  dispatch to `emit-call`, was looked up as a user-defined function, and died
  in `finalize` -- cleanly on x86-64, and on AArch64 as a bare
  NullPointerException, because that backend's own unknown-target guard was
  unreachable behind an eager `displacement` binding.

  Three real gaps had accumulated behind that silence: `bit-and`/`bit-or`/
  `bit-xor` missing on AArch64, and `kernel-load-u32`/`kernel-store-u32`
  missing on x86-64. All three are portable operators that
  `kotoba.compiler.frontend` admits for every native target."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]))

(defn- program [params body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'main :params params :body body}]})

(defn- emits? [emit params body]
  (try (seq (:code (emit (program params body))))
       (catch Throwable _ false)))

;; ---------------------------------------------------------------------------
;; Portable operators -- both backends, no exceptions
;; ---------------------------------------------------------------------------

;; Arity and spelling follow `kotoba.compiler.frontend`'s own operator tables
;; (`kernel-memory-operations`, arithmetic, comparisons). Anything the frontend
;; admits for a native target must reach real code on BOTH native targets;
;; there is no per-ISA admission gate between the frontend and here.
(def ^:private portable
  [[['a 'b] '(+ a b)]
   [['a 'b] '(- a b)]
   [['a 'b] '(* a b)]
   [['a 'b] '(quot a b)]
   [['a 'b] '(bit-and a b)]
   [['a 'b] '(bit-or a b)]
   [['a 'b] '(bit-xor a b)]
   [['a] '(- a)]
   [['a 'b] '(= a b)]
   [['a 'b] '(< a b)]
   [['a 'b] '(> a b)]
   [['a 'b] '(<= a b)]
   [['a 'b] '(>= a b)]
   ;; `not`/`zero?`/`pos?`/`neg?` and the list operations are deliberately
   ;; absent: `kotoba.compiler.frontend` lowers them to the comparisons and
   ;; pair projections above before KIR exists, so they never reach a backend.
   ;; An earlier draft of this list included them and failed symmetrically on
   ;; both ISAs -- which is the correct answer to the wrong question. Only
   ;; operators that survive into KIR belong here.
   [['a] '(bit-not a)]
   [['a] '(i64-shift-left a 3)]
   [['a] '(i64-shift-right a 3)]
   [['a] '(u64-shift-right a 3)]
   [['b 'l 'i] '(kernel-load-u8 b l i)]
   [['b 'l 'i] '(kernel-load-u8-4k b l i)]
   [['b 'l 'i] '(kernel-load-u8-16k b l i)]
   [['b 'l 'i] '(kernel-load-u32 b l i)]
   [['b 'l 'i 'v] '(kernel-store-u8 b l i v)]
   [['b 'l 'i 'v] '(kernel-store-u8-4k b l i v)]
   [['b 'l 'i 'v] '(kernel-store-u32 b l i v)]
   [['b 'l 'o 's] '(kernel-subregion b l o s)]
   ;; vector-i64 and vector-f64. Both families lower to the same six host
   ;; calls, so a gap on one ISA would be a gap on every one of the fourteen
   ;; operators at once -- exactly the failure this namespace exists to make
   ;; loud.
   [[] '(vector-new)]
   [['a 'b] '(vector-new a b)]
   [['v] '(vector-count v)]
   [['v 'i] '(vector-at v i)]
   [['v 'i 'd] '(vector-get v i d)]
   [['v 'i 'x] '(vector-assoc v i x)]
   [['v 'x] '(vector-conj v x)]
   [['v 'n] '(vector-drop v n)]
   [[] '(vector-f64-new)]
   [['v] '(vector-f64-count v)]
   [['v 'i] '(vector-f64-at v i)]
   [['v 'i 'd] '(vector-f64-get v i d)]
   [['v 'i 'x] '(vector-f64-assoc v i x)]
   [['v 'x] '(vector-f64-conj v x)]
   [['v 'n] '(vector-f64-drop v n)]])

(deftest every-portable-operator-emits-on-both-isas
  (doseq [[params body] portable]
    (testing (str body)
      (is (emits? x86/emit-program params body) "x86-64 must emit this operator")
      (is (emits? arm/emit-program params body) "AArch64 must emit this operator"))))

;; ---------------------------------------------------------------------------
;; Intentional asymmetry -- pinned, so it cannot grow by accident
;; ---------------------------------------------------------------------------

;; `kotoba.compiler.frontend`'s `kernel-privileged-operations`. Every one names
;; an x86 facility with no AArch64 counterpart: control registers, the TLB
;; invalidation instruction, the interrupt-flag instructions, and port I/O.
;; AArch64 uses system registers, `tlbi`, `msr daifset/daifclr` and
;; memory-mapped I/O instead, so these are NOT gaps to close by translation --
;; an AArch64 privileged surface would be a different operator set, decided
;; elsewhere. They are listed here so that an operator quietly added to one
;; backend alone shows up as a failure rather than as silence.
(def ^:private x86-only
  [[[] '(kernel-boot-info)]
   [[] '(kernel-read-cr2)]
   [[] '(kernel-read-cr3)]
   [['v] '(kernel-write-cr3 v)]
   [['a] '(kernel-invlpg a)]
   [[] '(kernel-cli)]
   [[] '(kernel-sti)]
   [[] '(kernel-hlt)]
   [[] '(kernel-pause)]
   [['p 'v] '(kernel-out-u8 p v)]
   [['p 'v] '(kernel-out-u32 p v)]])

(deftest privileged-x86-operators-are-x86-only-by-design
  (doseq [[params body] x86-only]
    (testing (str body)
      (is (emits? x86/emit-program params body)
          "x86-64 owns the privileged surface")
      (is (not (emits? arm/emit-program params body))
          (str body " reached the AArch64 backend. If that is intended, this "
               "list and the AArch64 privileged surface must be decided "
               "together -- not by one backend drifting.")))))

;; ---------------------------------------------------------------------------
;; The silence that let the gaps accumulate
;; ---------------------------------------------------------------------------

(deftest an-unimplemented-operator-says-so-on-both-isas
  ;; Both backends route an unrecognized operator to `emit-call`, so at the
  ;; point of failure an unimplemented operator looks exactly like a call to a
  ;; function that does not exist. It cannot BE one: the frontend rejects an
  ;; unknown name with "operation has no admitted lowering" before KIR exists,
  ;; the verifier rejects any operation outside its own signature table before
  ;; re-emitting, and `emit-program` puts every declared function into
  ;; `offsets`. So the diagnostic can state the only remaining possibility --
  ;; and must, because "unknown call target" named the one thing it could not
  ;; be, which is how every missing operator so far stayed hidden.
  (doseq [[label emit phase] [["x86-64" x86/emit-program :x86-64]
                              ["AArch64" arm/emit-program :aarch64]]]
    (testing label
      (let [thrown (try (emit (program [] '(no-such-operator)))
                        (catch Throwable e e))]
        (is (instance? clojure.lang.ExceptionInfo thrown)
            (str label " must reject with ex-info, got "
                 (some-> thrown class .getSimpleName)))
        (is (= "operation not implemented on this backend" (ex-message thrown)))
        (is (= 'no-such-operator (:operation (ex-data thrown)))
            "the diagnostic must name the operation")
        (is (= phase (:phase (ex-data thrown)))
            "the phase must be this backend, matching its other throws")))))

(deftest the-x86-only-privileged-surface-reports-itself-as-unimplemented
  ;; The load-bearing case. These are real operators the frontend admits, that
  ;; x86-64 implements and AArch64 deliberately does not. Before this, asking
  ;; for one on AArch64 said the program had called a function that does not
  ;; exist. Now it names the operator, which is what makes the intentional
  ;; asymmetry legible instead of looking like a broken program.
  (doseq [[params body] x86-only]
    (let [thrown (try (arm/emit-program (program params body)) nil
                      (catch clojure.lang.ExceptionInfo e e))]
      (is (some? thrown) (str body " must be rejected on AArch64"))
      (is (= "operation not implemented on this backend" (ex-message thrown)))
      (is (= (first body) (:operation (ex-data thrown)))
          (str "the diagnostic must name " (first body))))))

;; ---------------------------------------------------------------------------
;; The u32 bound is four bytes wider than the u8 bound
;; ---------------------------------------------------------------------------

(deftest u32-accesses-reserve-four-bytes-not-one
  ;; A four-byte access at `length - 1` must trap, so the check is
  ;; `index + 4 <= length`, not `index < length`. Both backends compute the
  ;; widened index before comparing; asserting the instruction is present keeps
  ;; a future edit from silently narrowing the check back to the u8 form, which
  ;; would read or write three bytes past the buffer.
  (testing "x86-64 widens the index with lea before the range comparison"
    (let [load (:code (x86/emit-program (program '[b l i] '(kernel-load-u32 b l i))))
          store (:code (x86/emit-program (program '[b l i v] '(kernel-store-u32 b l i v))))]
      ;; lea rsi,[rax+4] / lea rsi,[rdi+4]
      (is (some #(= [0x48 0x8d 0x70 0x04] %) (partition 4 1 load)))
      (is (some #(= [0x48 0x8d 0x77 0x04] %) (partition 4 1 store)))
      ;; cmp rsi,rcx -- the widened index against the length
      (is (some #(= [0x48 0x39 0xce] %) (partition 3 1 load)))
      (is (some #(= [0x48 0x39 0xce] %) (partition 3 1 store)))))
  (testing "AArch64 widens the index with add x5,x3,#4 before the comparison"
    (let [load (:code (arm/emit-program (program '[b l i] '(kernel-load-u32 b l i))))]
      ;; 0x91001065 = add x5, x3, #4, little-endian
      (is (some #(= [0x65 0x10 0x00 0x91] %) (partition 4 1 load))))))

;; ---------------------------------------------------------------------------
;; The new operators are real instructions, not accidental no-ops
;; ---------------------------------------------------------------------------

(deftest aarch64-bitwise-operators-use-the-logical-shifted-register-encodings
  ;; Rm=x1, Rn=x0, Rd=x0 -- the same operand placement the add/sub/mul cases
  ;; beside them use. `mov-reg`'s own 0xaa0003e0 is the ORR base with Rn=xzr,
  ;; which independently cross-checks the opcode bits below.
  (doseq [[op word] {'bit-and 0x8a010000 'bit-or 0xaa010000 'bit-xor 0xca010000}]
    (let [expected (mapv #(bit-and (unsigned-bit-shift-right word (* 8 %)) 0xff) (range 4))
          code (:code (arm/emit-program (program '[a b] (list op 'a 'b))))]
      (is (some #(= expected %) (partition 4 1 code))
          (str op " must emit " (format "0x%08x" word))))))

(deftest both-isas-stay-deterministic-across-the-new-surface
  (doseq [[params body] (concat portable x86-only)]
    (doseq [emit [x86/emit-program arm/emit-program]]
      (when (emits? emit params body)
        (is (= (emit (program params body)) (emit (program params body)))
            (str "emission of " body " must be reproducible"))))))

;; ---------------------------------------------------------------------------
;; i64 bit operations -- exact encodings
;; ---------------------------------------------------------------------------

(deftest i64-operations-use-the-documented-encodings
  (testing "x86-64"
    (let [code #(:code (x86/emit-program (program '[a] %)))]
      ;; not rax -- group 3 /2, sharing its opcode with the neg (/3) beside it
      (is (some #(= [0x48 0xf7 0xd0] %) (partition 3 1 (code '(bit-not a)))))
      ;; shl/sar/shr rax,cl -- the count arrives in rcx, whose low byte is CL
      (is (some #(= [0x48 0xd3 0xe0] %) (partition 3 1 (code '(i64-shift-left a 3)))))
      (is (some #(= [0x48 0xd3 0xf8] %) (partition 3 1 (code '(i64-shift-right a 3)))))
      (is (some #(= [0x48 0xd3 0xe8] %) (partition 3 1 (code '(u64-shift-right a 3)))))))
  (testing "AArch64"
    (let [code #(:code (arm/emit-program (program '[a] %)))
          word (fn [w] (mapv #(bit-and (unsigned-bit-shift-right w (* 8 %)) 0xff) (range 4)))]
      (is (some #(= (word 0xaa2003e0) %) (partition 4 1 (code '(bit-not a)))))
      (is (some #(= (word 0x9ac12000) %) (partition 4 1 (code '(i64-shift-left a 3)))))
      (is (some #(= (word 0x9ac12800) %) (partition 4 1 (code '(i64-shift-right a 3)))))
      (is (some #(= (word 0x9ac12400) %) (partition 4 1 (code '(u64-shift-right a 3))))))))

(deftest arithmetic-and-logical-right-shifts-are-not-interchanged
  ;; `i64-shift-right` is arithmetic and `u64-shift-right` is logical, matching
  ;; `kotoba.kir`'s own `i64-shr`/`u64-shr`. Swapping them would seal an oracle
  ;; value that disagrees with the emitted code for every negative operand, so
  ;; assert the two differ rather than only that each is present.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (is (not= (:code (emit (program '[a] '(i64-shift-right a 3))))
                (:code (emit (program '[a] '(u64-shift-right a 3)))))))))

;; ---------------------------------------------------------------------------
;; string-substring over an all-ASCII literal
;; ---------------------------------------------------------------------------

(def ^:private substring-program
  (program '[n] '(string-byte-length (string-substring "0123456789" n (+ n 1)))))

(deftest an-ascii-literal-substring-emits-on-both-isas
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (is (seq (:code (emit substring-program))))
      (is (= (emit substring-program) (emit substring-program))
          "emission must be reproducible"))))

(deftest a-non-ascii-or-non-literal-operand-now-reaches-the-host
  ;; This used to assert these shapes were REJECTED as unimplemented, on the
  ;; grounds that checking their offsets needs a byte read the emitted code
  ;; cannot perform. That read is now exactly what the loader's
  ;; `string_substring` at context offset 136 does, so they emit. The
  ;; all-ASCII literal above still compiles to pure pair arithmetic and never
  ;; calls it -- that is the property worth keeping, and the reason the fast
  ;; path was not simply deleted.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body] [["multi-byte literal" '(string-substring "a\u00e9" 0 1)]
                          ["computed string" '(string-substring (string-concat "a" "b") 0 1)]]]
        (is (seq (:code (emit (program [] (list 'string-byte-length body))))) why)))))

;; ---------------------------------------------------------------------------
;; host-call displacement
;; ---------------------------------------------------------------------------

(deftest a-host-call-past-disp8-uses-the-long-displacement
  ;; `call qword ptr [r9+disp8]` takes a SIGNED byte, so a context offset above
  ;; 127 silently becomes negative -- 136 reads as -120 and calls whatever sits
  ;; there. AArch64 cannot hit this at all (its LDR immediate is a 12-bit
  ;; scaled field, good to 32760), and the only hardware here is AArch64, so
  ;; every execution test passed while x86-64 was wrong. It shipped twice
  ;; before this test existed. The check is over the TABLE, not one call site,
  ;; so the next offset added past 127 is covered without anyone remembering.
  (doseq [[op offset] @#'x86/heap-call-offsets]
    (when (> offset 127)
      (let [body (case op
                   string-substring '(string-substring (string-concat "a" "b") 0 1)
                   string-code-point-at '(string-code-point-at (string-concat "a" "b") 0)
                   nil)]
        (when body
          (let [bytes (mapv #(bit-and (int %) 0xff)
                            (:code (x86/emit-program
                                    (program [] (list 'string-byte-length body)))))
                windows (fn [n] (map vec (partition n 1 bytes)))]
            (testing (str op " at offset " offset)
              (is (not-any? #(= % [0x41 0xff 0x51 (bit-and offset 0xff)]) (windows 4))
                  "must not encode a >127 offset as a signed disp8")
              (is (some #(= % (vec (concat [0x41 0xff 0x91]
                                           [(bit-and offset 0xff) 0x00 0x00 0x00])))
                        (windows 7))
                  "must call through the disp32 form"))))))))

(deftest the-range-check-and-its-trap-are-emitted
  ;; Defence in depth, and not reachable through the ordinary pipeline: for a
  ;; pure entry the constant-folding oracle evaluates the substring at compile
  ;; time and rejects an out-of-range index as :phase :value long before the
  ;; emitted check could fire -- the same property ADR 0063 records for the
  ;; variant dispatch trap. So the check is asserted structurally.
  (let [x (:code (x86/emit-program substring-program))
        a (:code (arm/emit-program substring-program))
        word (fn [w] (mapv #(bit-and (unsigned-bit-shift-right w (* 8 %)) 0xff) (range 4)))]
    (testing "x86-64 tests the start, orders the bounds, and ends in UD2"
      (is (some #(= [0x48 0x85 0xd2] %) (partition 3 1 x)) "test rdx,rdx")
      (is (some #(= [0x48 0x39 0xd1] %) (partition 3 1 x)) "cmp rcx,rdx")
      (is (some #(= [0x0f 0x0b] %) (partition 2 1 x)) "UD2"))
    (testing "AArch64 does the same and ends in BRK"
      (is (some #(= (word 0xeb01005f) %) (partition 4 1 a)) "cmp x2,x1")
      (is (some #(= (word 0xd4200000) %) (partition 4 1 a)) "BRK"))))

;; ---------------------------------------------------------------------------
;; A let-bound record (ADR 0062's named remaining gap)
;; ---------------------------------------------------------------------------

(def ^:private rec-type '[:record :t/p [[:a :i64] [:b :i64]]])

(defn- rec-program [body] (program [] body))

(deftest a-let-bound-record-emits-on-both-isas
  ;; ADR 0062 gave the record no independent runtime representation: a
  ;; record-get directly over a matching record-new is rewritten into the very
  ;; let-slot machinery an ordinary multi-binding let already uses. A LET-BOUND
  ;; record needs the same thing, only reaching the body instead of being
  ;; consumed on the spot -- so one binding becomes one binding PER FIELD, and
  ;; every slot count and depth-relative load stays what it already was.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body]
              [["single projection"
                (list 'let ['r (list 'record-new rec-type 11 22)]
                      (list 'record-get rec-type 'r :a))]
               ["read twice -- the gap ADR 0062 names"
                (list 'let ['r (list 'record-new rec-type 11 22)]
                      (list '+ (list 'record-get rec-type 'r :a)
                            (list 'record-get rec-type 'r :b)))]
               ["mixed with scalar bindings"
                (list 'let ['x 5 'r (list 'record-new rec-type 1 2) 'y 3]
                      (list '+ 'x (list '+ 'y (list 'record-get rec-type 'r :b))))]]]
        (is (seq (:code (emit (rec-program body)))) why)
        (is (= (emit (rec-program body)) (emit (rec-program body)))
            (str why " must be reproducible"))))))

(deftest a-record-binding-is-not-a-value
  ;; The record still never exists as a value: `r` alone is not a word, so a
  ;; bare reference must be refused rather than loading one of its slots.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (is (thrown? clojure.lang.ExceptionInfo
                   (emit (rec-program (list 'let ['r (list 'record-new rec-type 1 2)] 'r))))))))

(deftest a-projection-must-match-the-schema-it-was-bound-with
  (let [other '[:record :t/q [[:a :i64] [:b :i64]]]]
    (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
      (testing label
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"identical to the schema its operand was bound with"
             (emit (rec-program (list 'let ['r (list 'record-new rec-type 1 2)]
                                      (list 'record-get other 'r :a))))))
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"undeclared field"
             (emit (rec-program (list 'let ['r (list 'record-new rec-type 1 2)]
                                      (list 'record-get rec-type 'r :nope))))))))))

;; ---------------------------------------------------------------------------
;; kernel-subregion encodes the checks it claims to.
;;
;; Emission parity above proves both backends produce SOMETHING for the op.
;; For a bounds check that is not enough: a sequence that emitted the right
;; number of bytes with a wrong branch displacement would pass parity and
;; silently never trap. Kernel targets are linkable ELF objects rather than
;; runnable processes, so there is no execute-and-observe available here the
;; way there is for userland artifacts -- these assertions pin the exact
;; encodings instead, and were derived by disassembling the emitted bytes
;; (otool -tvV) rather than by reading them back out of the source.

(defn- emitted [emit params body]
  (let [program {:format :kotoba.kir/v3
                 :functions [{:name 'main :params params :body body :result :i64}]}]
    (mapv #(bit-and % 0xff) (:code (emit program)))))

(defn- subsequence? [needle haystack]
  (some #(= needle (subvec haystack % (min (count haystack) (+ % (count needle)))))
        (range (inc (- (count haystack) (count needle))))))

(deftest x86-64-kernel-subregion-encodes-its-checks
  (let [code (emitted x86/emit-program '[b l o s] '(kernel-subregion b l o s))]
    (is (subsequence?
         [0x5f 0x59 0x5a                          ; pop rdi/rcx/rdx = offset/length/base
          0x48 0x85 0xd2                          ; test rdx,rdx
          0x0f 0x84 0x1b 0x00 0x00 0x00           ; jz  -> ud2 at +27
          0x48 0x39 0xcf                          ; cmp rdi,rcx
          0x0f 0x87 0x12 0x00 0x00 0x00           ; ja  -> ud2 at +18
          0x48 0x29 0xf9                          ; sub rcx,rdi  (remaining)
          0x48 0x39 0xc8                          ; cmp rax,rcx
          0x0f 0x87 0x06 0x00 0x00 0x00           ; ja  -> ud2 at +6
          0x48 0x8d 0x04 0x3a                     ; lea rax,[rdx+rdi]
          0xeb 0x02 0x0f 0x0b]                    ; jmp +2 / ud2
         code)
        "every branch must land on the UD2, or the check never fires")))

(deftest aarch64-kernel-subregion-encodes-its-checks
  (let [code (emitted arm/emit-program '[b l o s] '(kernel-subregion b l o s))
        word (fn [w] [(bit-and w 0xff) (bit-and (bit-shift-right w 8) 0xff)
                      (bit-and (bit-shift-right w 16) 0xff) (bit-and (bit-shift-right w 24) 0xff)])]
    (is (subsequence?
         (vec (mapcat word [0xb4000101   ; cbz x1, +32   (null parent)
                            0xeb02007f   ; cmp x3, x2    (offset vs length)
                            0x540000c8   ; b.hi +24
                            0xcb030044   ; sub x4, x2, x3 (remaining)
                            0xeb0400bf   ; cmp x5, x4    (sublen vs remaining)
                            0x54000068   ; b.hi +12
                            0x8b030020   ; add x0, x1, x3
                            0x14000002   ; b +8
                            0xd4200000])) ; brk #0
         code)
        "every branch must land on the BRK, or the check never fires")))
;; A nested record is flattened, not represented
;; ---------------------------------------------------------------------------

(def ^:private inner '[:record :t/s [[:a :i64] [:b :i64]]])
(def ^:private outer '[:record :t/n [[:i [:record :t/s [[:a :i64] [:b :i64]]]] [:m :i64]]])

(deftest a-nested-record-flattens-into-the-enclosing-slots
  ;; ADR 0062's property -- a record has no independent runtime representation
  ;; -- is kept, not traded away: a field that is itself a record expands into
  ;; the enclosing record's own slots, recursively. A chained projection then
  ;; needs no intermediate value at all.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body]
              [["outer field of a let-bound nested record"
                (list 'let ['r (list 'record-new outer (list 'record-new inner 1 2) 9)]
                      (list 'record-get outer 'r :m))]
               ["chained into the inner record"
                (list 'let ['r (list 'record-new outer (list 'record-new inner 1 2) 9)]
                      (list 'record-get inner (list 'record-get outer 'r :i) :b))]
               ["chained plus a sibling read"
                (list 'let ['r (list 'record-new outer (list 'record-new inner 4 5) 6)]
                      (list '+ (list 'record-get inner (list 'record-get outer 'r :i) :a)
                            (list 'record-get outer 'r :m)))]
               ["construction, outer field"
                (list 'record-get outer (list 'record-new outer (list 'record-new inner 1 2) 7) :m)]]]
        (is (seq (:code (emit (program [] body)))) why)
        (is (= (emit (program [] body)) (emit (program [] body)))
            (str why " must be reproducible"))))))

(deftest a-record-valued-projection-is-not-a-value
  ;; Selecting a record-typed field yields a record, which is only meaningful as
  ;; the operand of a further projection. Anywhere else there is no word to
  ;; produce, so it must be refused rather than loading one of the slots.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"record-valued projection may only appear"
           (emit (program [] (list 'let ['r (list 'record-new outer (list 'record-new inner 1 2) 9)]
                                   (list 'record-get outer 'r :i)))))))))

;; ---------------------------------------------------------------------------
;; A variant whose case payload is a record
;; ---------------------------------------------------------------------------

(def ^:private wall '[:record :kotoba.clock/wall [[:unix-millis :i64] [:observation-sequence :i64]]])
(def ^:private clock-error '[:record :kotoba.clock/error [[:code :keyword] [:message :string]]])
(def ^:private clock-result
  '[:variant :kotoba.clock/result
    [[:wall [:record :kotoba.clock/wall [[:unix-millis :i64] [:observation-sequence :i64]]]]
     [:error [:record :kotoba.clock/error [[:code :keyword] [:message :string]]]]]])

(deftest a-variant-case-payload-may-be-a-record
  ;; These are clock-v1's own declared shapes, not a reduction of them. The
  ;; payload flattens into the dispatch's slots exactly as a record field
  ;; flattens into its enclosing record's.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body]
              [["wall case, project a field"
                (list 'variant-match clock-result
                      (list 'variant-new clock-result :wall (list 'record-new wall 123 4))
                      [[:wall 'p (list 'record-get wall 'p :unix-millis)] [:error 'p 0]])]
               ["error case, project the string field"
                (list 'variant-match clock-result
                      (list 'variant-new clock-result :error (list 'record-new clock-error :timeout "slow"))
                      [[:wall 'p 0] [:error 'p (list 'string-byte-length (list 'record-get clock-error 'p :message))]])]]]
        (is (seq (:code (emit (program [] body)))) why)
        (is (= (emit (program [] body)) (emit (program [] body)))
            (str why " must be reproducible"))))))

(deftest the-payload-region-is-sized-by-the-widest-case
  ;; Only the constructed case is materialised, but every branch is emitted. A
  ;; branch whose declared payload is wider than the constructed one must still
  ;; describe slots that exist -- otherwise it emits a load running off the
  ;; frame, unreachable but wrong. Constructing the NARROW case of a variant
  ;; whose other case is wider is the shape that would expose it.
  (let [mixed '[:variant :t/m [[:small :i64]
                               [:big [:record :t/b [[:a :i64] [:b :i64] [:c :i64]]]]]]
        big '[:record :t/b [[:a :i64] [:b :i64] [:c :i64]]]
        body (list 'variant-match mixed (list 'variant-new mixed :small 5)
                   [[:small 'p 'p] [:big 'p (list 'record-get big 'p :c)]])]
    (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
      (testing label
        (is (seq (:code (emit (program [] body)))))
        (is (= (emit (program [] body)) (emit (program [] body))))))))

;; ---------------------------------------------------------------------------
;; A record crossing a function boundary
;; ---------------------------------------------------------------------------

(def ^:private pair-rec '[:record :t/s [[:a :i64] [:b :i64]]])

(defn- boundary-program [body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'mk :params [] :result pair-rec
                :body (list 'record-new pair-rec 11 22)}
               {:name 'main :params [] :body body}]})

(deftest a-record-crosses-a-function-boundary-boxed
  ;; The one shape flattening cannot reach: a record is N slots and a function
  ;; returns one word, so it is boxed into a pair chain -- one word, built from
  ;; the arena primitives this backend has had since ADR 0062's bounded-pair
  ;; work. No new primitive, no ABI change, no loader change.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body] [["first field" (list 'record-get pair-rec '(mk) :a)]
                          ["second field" (list 'record-get pair-rec '(mk) :b)]
                          ["both" (list '+ (list 'record-get pair-rec '(mk) :a)
                                        (list 'record-get pair-rec '(mk) :b))]]]
        (is (seq (:code (emit (boundary-program body)))) why)
        (is (= (emit (boundary-program body)) (emit (boundary-program body)))
            (str why " must be reproducible"))))))

(deftest slot-backed-records-still-allocate-nothing
  ;; Boxing is confined to the boundary. A record that does not escape keeps
  ;; using slots, so no program that compiled before gains an arena allocation
  ;; -- which is what makes this non-regressive despite the arena being bounded
  ;; and uncollected.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (let [slot-only (program [] (list 'let ['r (list 'record-new pair-rec 1 2)]
                                        (list 'record-get pair-rec 'r :a)))
            code (:code (emit slot-only))
            ;; pair_new is the arena call at context offset 56; a slot-backed
            ;; record must not reach it.
            calls-pair (if (= label "x86-64")
                         (some #(= [0x41 0xff 0x51 56] %) (partition 4 1 code))
                         (some #(= [0x38 0x40 0x40 0xf9] %) (partition 4 1 code)))]
        (is (seq code))
        (is (not calls-pair) "a non-escaping record must allocate nothing")))))

;; ---------------------------------------------------------------------------
;; A record-new in TAIL position, wherever in the body it sits
;; ---------------------------------------------------------------------------
;;
;; Boxing a record result used to require two things at once that nothing
;; guaranteed: the construction had to be the OUTERMOST form of the body, and
;; the declared result had to be the EXPANDED `[:record …]` spelling. Neither is
;; how a real module is written.
;;
;; A schema reference survives into a KIR SIGNATURE unexpanded on purpose --
;; expanding it moved the `:kir-sha256` of every module that used one, on every
;; target -- so `[:ref :t/s]` is the spelling murakumo's cores actually carry,
;; and a body is normally `(let [...] (if ... (record-new ...) ...))`.
;;
;; The rewrite therefore follows tail position through `if` (both branches),
;; `let` (the body, never a binding's value) and `do` (the last subexpression) --
;; the same positions `emit-expr` hands its own `:tail?` down to.

(def ^:private tail-rec pair-rec)                     ; [:record :t/s [[:a :i64] [:b :i64]]]
(def ^:private tail-ref '[:ref :t/s])

(defn- mk-program
  "A program whose `mk` returns a record built by BODY and whose `main`
  projects FIELD out of the result."
  [result body field]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'mk :params [] :result result :body body}
               {:name 'main :params []
                :body (list 'record-get tail-rec '(mk) field)}]})

(def ^:private boxed-chain
  ;; What ADR 0062's boundary shape IS, written out: pair(11, pair(22, 0)).
  ;; Every placement below must produce exactly this, in exactly this position.
  '(pair 11 (pair 22 0)))

(def ^:private tail-placements
  [["outermost"        (list 'record-new tail-rec 11 22)                boxed-chain]
   ["under a let"      (list 'let ['x 5] (list 'record-new tail-rec 11 22))
                       (list 'let ['x 5] boxed-chain)]
   ["under a do"       (list 'do 7 (list 'record-new tail-rec 11 22))
                       (list 'do 7 boxed-chain)]
   ["both if branches" (list 'if 1 (list 'record-new tail-rec 11 22)
                            (list 'record-new tail-rec 11 22))
                       (list 'if 1 boxed-chain boxed-chain)]
   ;; murakumo's own shape: a guard returning a zero record, and the real one
   ;; built at the bottom of a nested let.
   ["let / if / let"   (list 'let ['t 1]
                             (list 'if 't (list 'record-new tail-rec 11 22)
                                   (list 'let ['u 2] (list 'record-new tail-rec 11 22))))
                       (list 'let ['t 1]
                             (list 'if 't boxed-chain
                                   (list 'let ['u 2] boxed-chain)))]])

(deftest a-record-result-is-boxed-from-any-tail-position-on-both-isas
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body already-boxed] tail-placements
              ;; The two projections select DIFFERENT fields on purpose: a pair
              ;; chain walked to the wrong depth still yields a plausible i64,
              ;; so a table that only ever read `:a` could not see a rewrite
              ;; that boxed the fields in the wrong order or the wrong place.
              field [:a :b]]
        (let [emitted (:code (emit (mk-program tail-rec body field)))]
          (is (seq emitted) (str why " / " field))
          ;; Not merely "it emits": it emits THE SAME BYTES as the body whose
          ;; construction was already the pair chain. That is what makes this a
          ;; rewrite into a shape both backends already executed, rather than a
          ;; new encoding that happens to compile.
          (is (= emitted (:code (emit (mk-program tail-rec already-boxed field))))
              (str why " / " field
                   " must emit exactly the pre-boxed body's code")))))))

(deftest a-result-declared-by-schema-reference-boxes-identically
  ;; `[:ref :t/s]` and `[:record :t/s [...]]` name the same record, and KIR
  ;; leaves the reference unexpanded in a signature. Reading only the expanded
  ;; spelling is why a murakumo core that declares its record results by
  ;; reference -- which is how they are written throughout -- could not return
  ;; a record at all.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body _] tail-placements
              field [:a :b]]
        (is (= (:code (emit (mk-program tail-ref body field)))
               (:code (emit (mk-program tail-rec body field))))
            (str why " / " field " must not depend on which spelling declared it"))))))

(deftest boxing-reaches-tail-positions-only
  ;; A `record-new` that is NOT where the function's value comes from is still
  ;; refused. Boxing every construction anywhere would silently give the record
  ;; the runtime representation ADR 0062 declined to give it.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body]
              [["an arithmetic operand" (list '+ 1 (list 'record-new tail-rec 11 22))]
               ;; A binding's VALUE is not a tail: it flattens into slots, and a
               ;; bare record binding is not a word.
               ["a let binding read as a value"
                (list 'let ['r (list 'record-new tail-rec 11 22)] 'r)]]]
        (is (thrown? clojure.lang.ExceptionInfo
                     (emit (mk-program tail-rec body :a)))
            why)))))

(deftest a-tail-record-new-must-name-the-declared-result
  ;; `[:ref :t/s]` carries no field list, so the construction's own name is the
  ;; only local evidence that it is the record the signature promised. A
  ;; mismatch is left unboxed and fails loudly rather than being handed to a
  ;; caller that will walk it with the wrong field count.
  (let [other '[:record :t/other [[:a :i64] [:b :i64] [:c :i64]]]]
    (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
      (testing label
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"record-new is only supported"
             (emit (mk-program tail-ref (list 'record-new other 1 2 3) :a))))))))
