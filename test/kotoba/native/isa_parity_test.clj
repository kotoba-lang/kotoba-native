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
   [['b 'l 'i 'v] '(kernel-store-u32 b l i v)]])

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

(deftest a-non-ascii-or-non-literal-operand-is-reported-as-unimplemented
  ;; The slice is deliberately narrow. Everything outside it -- a pool string, a
  ;; computed string, a literal with a multi-byte code point -- has offsets that
  ;; are not provably code-point boundaries at compile time, and verifying them
  ;; needs a byte read the emitted code cannot perform. Those must fall through
  ;; and SAY they are unimplemented rather than emit something unchecked.
  (doseq [[label emit] [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]]]
    (testing label
      (doseq [[why body] [["multi-byte literal" '(string-substring "aé" 0 1)]
                          ["computed string" '(string-substring (string-concat "a" "b") 0 1)]]]
        (let [thrown (try (emit (program [] body)) nil
                          (catch clojure.lang.ExceptionInfo e e))]
          (is (some? thrown) (str why " must be rejected"))
          (is (= "operation not implemented on this backend" (ex-message thrown)) why)
          (is (= 'string-substring (:operation (ex-data thrown))) why))))))

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
