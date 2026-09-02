(ns kotoba.native.boot-scratch-test
  "boot-scratch: byte goldens for the writable region's base and for the
  address of a function in the same module.

  Both are four and seven bytes respectively, and both were read back with
  `llvm-mc` rather than assembled from the intent -- the ModRM byte is where
  this kind of encoding goes wrong, and a wrong one still validates."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.image-scratch :as image-scratch]
            [kotoba.native.machine-ir]
            [kotoba.native.x86-64 :as x86]))

(defn- module [functions]
  {:format :kotoba.kir/v4 :entry 'main :exports ['main]
   :functions functions})

(defn- code [functions]
  (vec (map #(bit-and (long %) 0xff)
            (:code (x86/emit-program (module functions))))))

(defn- index-of-bytes [haystack needle]
  (let [n (count needle)]
    (first (filter #(= needle (subvec haystack % (+ % n)))
                   (range 0 (inc (- (count haystack) n)))))))

(defn- contains-bytes? [haystack needle]
  (some? (index-of-bytes haystack needle)))

(defn- u32-at [bytes index]
  (reduce (fn [out offset]
            (+ out (bit-shift-left (nth bytes (+ index offset)) (* 8 offset))))
          0 (range 4)))

(defn- rip-lea-indexes
  "Opcode indexes of every `lea r64,[rip+disp32]` in BYTES, for any
  destination register. ModRM mod=00 rm=101 is the rip-relative form; masking
  with 0xc7 separates it from `lea dst,[base+disp32]`, which the
  immediate-add peephole also emits with opcode 0x8d."
  [bytes]
  (->> (range 0 (max 0 (- (count bytes) 7)))
       (filter (fn [index]
                 (and (= 0x48 (bit-and (nth bytes index) 0xf8))
                      (= 0x8d (nth bytes (inc index)))
                      (= 0x05 (bit-and (nth bytes (+ index 2)) 0xc7)))))
       vec))

(defn- lea-target
  "Where the `lea r64,[rip+disp32]` at OPCODE-INDEX points. x86 measures the
  displacement from the END of the instruction, which is what makes this
  arithmetic rather than a lookup."
  [bytes opcode-index]
  (+ opcode-index 7 (u32-at bytes (+ opcode-index 3))))

;; ── the writable region ────────────────────────────────────────────────────

(deftest the-scratch-region-is-one-lea-off-the-context-register
  ;; `4d 8d 51 60`:
  ;;   4d   REX.W + REX.R + REX.B
  ;;   8d   LEA
  ;;   51   ModRM mod=01 reg=010 (R10) rm=001 (R9)
  ;;   60   disp8, `kotoba.native.image-scratch/offset`
  (let [bytes (code [{:name 'main :params [] :body '(kernel-scratch-region)}])]
    (is (contains-bytes? bytes [0x4d 0x8d 0x51 image-scratch/offset]))
    (testing "it is an LEA and not the load `:boot-info` emits"
      ;; `4d 8b 51 50` is `mov r10,[r9+0x50]` -- the same ModRM shape with the
      ;; load opcode. The difference between "the word the firmware handed us"
      ;; and "somewhere we may write" is that one byte.
      (is (not (contains-bytes? bytes [0x4d 0x8b 0x51 image-scratch/offset]))))))

(deftest boot-info-and-the-region-differ-by-one-opcode-byte-and-one-displacement
  (let [region (code [{:name 'main :params [] :body '(kernel-scratch-region)}])
        info   (code [{:name 'main :params [] :body '(kernel-boot-info)}])]
    (is (contains-bytes? region [0x4d 0x8d 0x51 0x60]))
    (is (contains-bytes? info   [0x4d 0x8b 0x51 0x50]))
    (testing "and neither program contains the other's instruction"
      (is (not (contains-bytes? region [0x4d 0x8b 0x51 0x50])))
      (is (not (contains-bytes? info [0x4d 0x8d 0x51 0x60]))))))

(deftest the-reservation-is-declared-once-and-fits-its-encoding
  (is (= 0x60 image-scratch/offset))
  (is (= 16384 image-scratch/bytes-reserved))
  (is (= (+ image-scratch/offset image-scratch/bytes-reserved)
         image-scratch/limit))
  (testing "the offset is a disp8, which is what makes the encoding four bytes"
    (is (<= image-scratch/offset 127))))

;; ── the address of a function ──────────────────────────────────────────────

(def ^:private two-functions
  [{:name 'main :params [] :body '(kernel-function-address target)}
   {:name 'target :params [] :body 7}])

(deftest a-function-address-is-a-rip-relative-lea-at-that-functions-label
  (let [bytes (code two-functions)
        lea (first (rip-lea-indexes bytes))]
    (is (some? lea) "the address must be an lea, not a mov-immediate")
    (is (= 1 (count (rip-lea-indexes bytes))) "exactly one, so `lea` is unambiguous")
    (testing "and it points at a function entry, not into the middle of one"
      ;; `target` is the second function, so its label is the offset the
      ;; module's own export table gives it. Reading the export table rather
      ;; than a golden offset keeps this true when the entry prologue changes.
      (let [exports (:exports (x86/emit-program
                               (assoc (module two-functions)
                                      :exports ['main 'target])))]
        (is (= (:offset (get exports 'target)) (lea-target bytes lea)))))))

(deftest the-address-and-a-call-resolve-against-the-same-table
  ;; A program that both CALLS `target` and takes its address must name one
  ;; place. If the two used different tables this would still compile.
  (let [bytes (code [{:name 'main :params []
                      :body '(+ (kernel-function-address target) (target))}
                     {:name 'target :params [] :body 7}])
        lea (first (rip-lea-indexes bytes))
        call (index-of-bytes bytes [0xe8])]
    (is (some? lea))
    (is (some? call))
    (let [call-target (+ call 5 (let [raw (u32-at bytes (inc call))]
                                  (if (>= raw 0x80000000) (- raw 0x100000000) raw)))]
      (is (= call-target (lea-target bytes lea))
          "the lea and the call must name the same offset"))))

(deftest a-function-nothing-declares-is-refused-by-name
  ;; Refused by kotoba-gmir, which resolves the name against the module's own
  ;; function list before any of this file runs. The backend's own
  ;; `:unknown-function-address-target` is the FLOOR under that -- it can only
  ;; be reached by a hand-built MC module, which is why it is asserted
  ;; separately below rather than through the compiler.
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"unresolved-function-address"
       (code [{:name 'main :params []
               :body '(kernel-function-address absent)}]))))

(deftest the-backends-own-floor-refuses-a-label-the-module-does-not-have
  ;; `encode-mc` -- the FLAT route -- passes an EMPTY callee-label table, so
  ;; any function address there has no label at all. That is the one way to
  ;; reach this refusal without hand-building a module, and it is worth
  ;; reaching: it is the check that stops a backend emitting a `lea` at a
  ;; label it would have to invent.
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"unknown-function-address-target"
       (#'kotoba.native.machine-ir/encode-mc
        {:mc/version 2 :mc/target :x86-64 :mc/frame-slots 0
         :mc/instructions
         [{:mc/op :mc/instruction :mc/encoding :x86-64/function-address
           :mir/dst :x86-64/rax :mir/function 'target}
          {:mc/op :mc/instruction :mc/encoding :x86-64/return
           :mir/value :x86-64/rax}]}))))

(deftest an-address-is-usable-as-the-target-of-a-jump
  ;; The whole point: `kernel-jump-to` has been encoded and gated since the
  ;; UEFI boundary landed with nothing able to produce its first argument.
  ;; `41 ff e2` is `jmp r10`.
  (let [bytes (code [{:name 'main :params ['b]
                      :body '(kernel-jump-to (kernel-function-address target) b)}
                     {:name 'target :params [] :body 7}])]
    (is (contains-bytes? bytes [0x41 0xff 0xe2]))
    (is (= 1 (count (rip-lea-indexes bytes))))))
