(ns kotoba.native.machine-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]
            [kotoba.native.aggregate-abi :as aggregate-abi]
            [kotoba.codegen.layout :as layout]
            [kotoba.native.machine-ir :as machine]
            [kotoba.native.aarch64 :as arm]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.string-index :as string-index]
            [kotoba.native.string-search :as string-search]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))

(deftest aarch64-constants-use-the-shorter-wide-move-seed
  (let [encode #(#'machine/a64-constant :aarch64/x0 %)]
    (is (= [0x00 0x00 0x80 0xd2] (encode 0)) "zero is one MOVZ")
    (is (= 4 (count (encode 48271))) "a low positive constant is one MOVZ")
    (is (= [0x00 0x00 0x80 0x92] (encode -1)) "all ones is one MOVN")
    (is (= 4 (count (encode Long/MIN_VALUE))) "a lone high lane is one MOVZ")
    (is (= 4 (count (encode -281470681808896)))
        "a repeated mask beats the two-word MOVN sequence")
    (is (= 16 (count (encode 0x0001000200030004)))
        "four distinct non-zero lanes still require four words"))
  (is (= 16 (count (#'machine/a64-constant-fixed :aarch64/x0 1)))
      "fixed-layout sites retain their reserved width"))

(deftest aarch64-constants-use-one-word-logical-immediates-when-shorter
  (let [encode #(#'machine/a64-constant :aarch64/x0 %)]
    (is (= [0xe0 0x7b 0x40 0xb2] (encode 0x7fffffff))
        "the runtime kernel divisor is MOV X0,#0x7fffffff")
    (is (= 4 (count (encode 0x00ff00ff00ff00ff)))
        "replicated rotated bitmasks use one ORR-immediate word")
    (is (= [0x00 0x00 0x80 0x92] (encode -1))
        "the forbidden all-ones logical immediate stays one MOVN")
    (is (= 16 (count (encode 0x0001000200030004)))
        "non-bitmask constants retain their exact wide-move sequence")))

(deftest aarch64-branchless-leaves-cache-repeated-constants
  (let [leaf (mapv vec (partition 4
                                (machine/compile-expression
                                 :aarch64 ['n]
                                 '(let [a (bit-and n 7) b (bit-or a 7)]
                                    (bit-xor b 7)))))
        branched (mapv vec (partition 4
                                    (machine/compile-expression
                                     :aarch64 ['n]
                                     '(if n (+ n 4097) (+ n 4097)))))
        checked-memory (mapv vec (partition 4
                                          (machine/compile-expression
                                           :aarch64 ['base 'length]
                                           '(+ (kernel-load-u8 base length 7)
                                               (kernel-load-u8 base length 7)))))
        movz-seven? #(= [0x00 0x80 0xd2] (subvec % 1))
        movz-4097? #(= [0x00 0x82 0xd2] (subvec % 1))]
    (is (= 1 (count (filter movz-seven? leaf)))
        "three materializations share one reserved leaf register")
    (is (= [0xed 0x00 0x80 0xd2] (first leaf)) "MOVZ X13,#7")
    (is (= 2 (count (filter movz-4097? branched)))
        "control flow disables the caller-saved leaf cache")
    (is (= 2 (count (filter movz-seven? checked-memory)))
        "encoders with private scratch conventions do not opt in")))

(deftest aarch64-branchless-leaves-cache-a-reciprocal-multiplier
  (let [module (fn [body]
                 {:format :kotoba.kir/v3 :entry 'kernel :exports ['kernel]
                  :functions [{:name 'kernel :params ['n 'd] :body body}]})
        magic (:multiplier (machine/signed-division-magic 7))
        needle (vec (partition 4 (#'machine/a64-constant :aarch64/x16 magic)))
        occurrences (fn [body]
                      (let [words (vec (partition 4
                                                  (:code
                                                   (machine/compile-kir-module
                                                    :aarch64 (module body)))))
                            width (count needle)]
                        (count (filter #(= needle (subvec words % (+ % width)))
                                       (range (inc (- (count words) width)))))))]
    (is (= 1 (occurrences '(let [a (quot n 7)] (+ a (quot n 7)))))
        "equal reciprocals load x16 once")
    (is (= 2 (occurrences
              '(let [a (quot n 7) b (quot a d)] (+ b (quot n 7)))))
        "an intervening guarded SDIV clobbers x16 and forces a reload")))

(deftest aarch64-cached-mersenne-msub-uses-shifted-subtract
  (let [instruction {:mc/op :mc/instruction
                     :mc/encoding :aarch64/multiply-subtract
                     :mir/dst :aarch64/x0 :mir/left :aarch64/x2
                     :mir/right :aarch64/x13 :mir/addend :aarch64/x3
                     :native/a64-mersenne-shift 31
                     :native/a64-mersenne-factor :aarch64/x2}
        bytes (#'machine/encode-selected
               :aarch64 0 [0xc0 0x03 0x5f 0xd6] 0 true instruction)]
    (is (= [[0x51 0x7c 0x02 0xcb] [0x60 0x00 0x11 0x8b]]
           (mapv vec (partition 4 bytes)))
        "SUB X17,X2,X2,LSL#31; ADD X0,X3,X17")))

(deftest aarch64-strength-reduces-only-repeated-positive-mersenne-factors
  (let [lower (fn [value]
                (#'machine/a64-cache-leaf-constants
                 [{:mc/op :mc/instruction :mc/encoding :aarch64/constant
                   :mir/dst :aarch64/x1 :mir/value value}
                  {:mc/op :mc/instruction :mc/encoding :aarch64/multiply-subtract
                   :mir/dst :aarch64/x0 :mir/left :aarch64/x2
                   :mir/right :aarch64/x1 :mir/addend :aarch64/x3}
                  {:mc/op :mc/instruction :mc/encoding :aarch64/constant
                   :mir/dst :aarch64/x1 :mir/value value}
                  {:mc/op :mc/instruction :mc/encoding :aarch64/multiply-subtract
                   :mir/dst :aarch64/x0 :mir/left :aarch64/x2
                   :mir/right :aarch64/x1 :mir/addend :aarch64/x3}
                  {:mc/op :mc/instruction :mc/encoding :aarch64/return
                   :mir/value :aarch64/x0}]))
        reduced (lower 2147483647)
        small (lower 15)
        ordinary (lower 14)]
    (is (= [31 31] (mapv :native/a64-mersenne-shift (take 2 reduced))))
    (is (= [4 4] (mapv :native/a64-mersenne-shift (take 2 small))))
    (is (not-any? #(= :aarch64/constant (:mc/encoding %)) reduced)
        "the now-unused divisor materialization is removed")
    (is (= 1 (count (filter #(= :aarch64/constant (:mc/encoding %)) ordinary))))
    (is (not-any? :native/a64-mersenne-shift ordinary)
        "a non-Mersenne factor retains MSUB")))

(deftest aarch64-fuses-safe-multiply-add-and-subtract-after-allocation
  (let [expression '(let [v (+ (* n 7) 1)] (- v (* n 3)))
        arm (machine/compile-gmir
             :aarch64 (machine/lower-kir-expression ['n] expression))
        x86 (machine/compile-gmir
             :x86-64 (machine/lower-kir-expression ['n] expression))
        encodings #(mapv :mc/encoding (:mc/instructions %))
        words (mapv vec (partition 4 (machine/compile-expression
                                      :aarch64 ['n] expression)))]
    (is (= 1 (count (filter #{:aarch64/multiply-add} (encodings arm)))))
    (is (= 1 (count (filter #{:aarch64/multiply-subtract} (encodings arm)))))
    (is (not-any? #{:aarch64/multiply :aarch64/add :aarch64/subtract}
                  (encodings arm)))
    (is (= 2 (count (filter #{:x86-64/multiply} (encodings x86))))
        "the AArch64 selection does not rewrite x86-64")
    (is (some #{[0x01 0x0c 0x01 0x9b]} words) "MADD x1,x0,x1,x3")
    (is (some #{[0x00 0x84 0x02 0x9b]} words) "MSUB x0,x0,x2,x1")))

(defn- a64-le-words [code]
  (mapv (fn [[b0 b1 b2 b3]]
          (bit-or b0
                  (bit-shift-left b1 8)
                  (bit-shift-left b2 16)
                  (bit-shift-left b3 24)))
        (partition 4 code)))

(defn- a64-mul-kind
  "64-bit MADD/MUL/MSUB (bits 31-21 = 10011011000). SMULH is 10011011010."
  [word]
  (when (= (bit-and word 0xffe00000) 0x9b000000)
    (let [ra (bit-and (unsigned-bit-shift-right word 10) 0x1f)
          o0 (bit-and (unsigned-bit-shift-right word 15) 0x1)]
      (cond (pos? o0) :msub
            (= ra 31) :mul
            :else :madd))))

(deftest aarch64-fusion-rejects-a-multiply-with-two-add-users
  (let [program
        (machine/lower-mc
         {:mir/version 1 :mir/target :aarch64 :mir/registers :physical
          :mir/frame-slots 0
          :mir/instructions
          [{:mir/op :mir/multiply :mir/dst :aarch64/x2
            :mir/left :aarch64/x0 :mir/right :aarch64/x1}
           {:mir/op :mir/add :mir/dst :aarch64/x3
            :mir/left :aarch64/x2 :mir/right :aarch64/x4}
           {:mir/op :mir/add :mir/dst :aarch64/x5
            :mir/left :aarch64/x2 :mir/right :aarch64/x6}
           {:mir/op :mir/return :mir/value :aarch64/x5}]})]
    (is (some #{:aarch64/multiply}
              (map :mc/encoding (:mc/instructions program))))
    (is (not-any? #{:aarch64/multiply-add}
                  (map :mc/encoding (:mc/instructions program))))))

(deftest aarch64-fuses-multiply-add-after-leaf-cache-on-offset-lanes
  ;; `(+ (* (+ n k) C) 1)` across several k reuses C and 1. Distribute
  ;; `(n+k)*C` to `n*C+(k*C)`, fold the trailing +1, and GVN the shared
  ;; `n*C`. Round 1 is then 1 MUL and 8 constant adds — the product has
  ;; eight users, so fusion must refuse (wrong-code if it madds).
  (let [form '(let [a (+ (* n 48271) 1)
                    b (+ (* (+ n 1) 48271) 1)
                    c (+ (* (+ n 2) 48271) 1)
                    d (+ (* (+ n 3) 48271) 1)
                    e (+ (* (+ n 4) 48271) 1)
                    f (+ (* (+ n 5) 48271) 1)
                    g (+ (* (+ n 6) 48271) 1)
                    h (+ (* (+ n 7) 48271) 1)]
                (+ (+ (+ a b) (+ c d)) (+ (+ e f) (+ g h))))
        gmir (machine/lower-kir-expression ['n] form)
        insts (:gmir/instructions gmir)
        arg (some #(when (= :gmir/argument (:gmir/op %)) (:gmir/dst %)) insts)
        muls (filterv #(= :gmir/multiply (:gmir/op %)) insts)
        kinds (keep a64-mul-kind
                    (a64-le-words (machine/compile-expression :aarch64 ['n] form)))]
    (is (= 1 (count muls)) "eight lanes share one n*C")
    (is (contains? #{(:gmir/left (first muls)) (:gmir/right (first muls))} arg)
        "the multiply's non-constant operand is the argument, not n+k")
    (is (some #(= 337898 (:gmir/value %)) insts)
        "lane k=7 folds to the wrapping i64 7*48271+1")
    (is (= 1 (count (filter #{:mul} kinds)))
        "encoded bytes keep the shared product")
    (is (zero? (count (filter #{:madd} kinds)))
        "fusing a reused product would drop the mul while later adds read it")))

(deftest aarch64-kernel-wide-encodes-one-mul-and-eight-madds-after-reassoc
  ;; Production path: compile-kir-module, not the v2 expression helper.
  ;; Round 1 CSEs to one n*C (MUL, eight constant adds). Round 2 is still
  ;; unique-use serial a0*C+1 (8 MADD). Post-allocation MIR scheduling can
  ;; reorder pure integer work so native MADD fusion emits one additional
  ;; standalone MUL while the eight round-2 MADD chains stay intact. Remainder
  ;; is SMULH/MSUB and must not be counted as MUL.
  (let [body '(let [v_a0 (+ (* n 48271) 1)
                    a0 (- v_a0 (* (quot v_a0 2147483647) 2147483647))
                    v_b0 (+ (* (+ n 1) 48271) 1)
                    b0 (- v_b0 (* (quot v_b0 2147483647) 2147483647))
                    v_c0 (+ (* (+ n 2) 48271) 1)
                    c0 (- v_c0 (* (quot v_c0 2147483647) 2147483647))
                    v_d0 (+ (* (+ n 3) 48271) 1)
                    d0 (- v_d0 (* (quot v_d0 2147483647) 2147483647))
                    v_e0 (+ (* (+ n 4) 48271) 1)
                    e0 (- v_e0 (* (quot v_e0 2147483647) 2147483647))
                    v_f0 (+ (* (+ n 5) 48271) 1)
                    f0 (- v_f0 (* (quot v_f0 2147483647) 2147483647))
                    v_g0 (+ (* (+ n 6) 48271) 1)
                    g0 (- v_g0 (* (quot v_g0 2147483647) 2147483647))
                    v_h0 (+ (* (+ n 7) 48271) 1)
                    h0 (- v_h0 (* (quot v_h0 2147483647) 2147483647))
                    v_a1 (+ (* a0 48271) 1)
                    a1 (- v_a1 (* (quot v_a1 2147483647) 2147483647))
                    v_b1 (+ (* b0 48271) 1)
                    b1 (- v_b1 (* (quot v_b1 2147483647) 2147483647))
                    v_c1 (+ (* c0 48271) 1)
                    c1 (- v_c1 (* (quot v_c1 2147483647) 2147483647))
                    v_d1 (+ (* d0 48271) 1)
                    d1 (- v_d1 (* (quot v_d1 2147483647) 2147483647))
                    v_e1 (+ (* e0 48271) 1)
                    e1 (- v_e1 (* (quot v_e1 2147483647) 2147483647))
                    v_f1 (+ (* f0 48271) 1)
                    f1 (- v_f1 (* (quot v_f1 2147483647) 2147483647))
                    v_g1 (+ (* g0 48271) 1)
                    g1 (- v_g1 (* (quot v_g1 2147483647) 2147483647))
                    v_h1 (+ (* h0 48271) 1)
                    h1 (- v_h1 (* (quot v_h1 2147483647) 2147483647))]
                (+ (+ (+ a1 b1) (+ c1 d1)) (+ (+ e1 f1) (+ g1 h1))))
        kir {:format :kotoba.kir/v3 :entry 'kernel :exports ['kernel]
             :functions [{:name 'kernel :params ['n] :body body}]}
        kinds (keep a64-mul-kind
                    (a64-le-words
                     (:code (machine/compile-kir-module :aarch64 kir))))]
    (is (= 8 (count (filter #{:madd} kinds)))
        "round 2 remains unique-use madd")
    (is (= 1 (count (filter #{:mul} kinds)))
        "the shared n*C product is the only standalone multiply")))

(deftest gmir-keeps-an-independently-live-offset-add
  (let [form '(let [s (+ n 1)] (+ s (* s 48271)))
        insts (:gmir/instructions (machine/lower-kir-expression ['n] form))
        arg (some #(when (= :gmir/argument (:gmir/op %)) (:gmir/dst %)) insts)
        const-1 (some (fn [instruction]
                        (when (and (= :gmir/constant (:gmir/op instruction))
                                   (= 1 (:gmir/value instruction)))
                          (:gmir/dst instruction)))
                      insts)]
    (is (some (fn [instruction]
                (when (= :gmir/add (:gmir/op instruction))
                  (let [ops #{(:gmir/left instruction) (:gmir/right instruction)}]
                    (and (contains? ops arg)
                         (contains? ops const-1)))))
              insts)
        "distribution of s*C does not delete the live n+1")
    (is (= 1 (count (filter #(= :gmir/multiply (:gmir/op %)) insts))))))

(deftest gmir-distributes-offset-mul-with-wrapping-i64
  (let [form '(* (+ n 2) 9223372036854775807)
        insts (:gmir/instructions (machine/lower-kir-expression ['n] form))
        arg (some #(when (= :gmir/argument (:gmir/op %)) (:gmir/dst %)) insts)
        muls (filterv #(= :gmir/multiply (:gmir/op %)) insts)]
    (is (= 1 (count muls)))
    (is (contains? #{(:gmir/left (first muls)) (:gmir/right (first muls))} arg))
    (is (some #(= -2 (:gmir/value %)) insts)
        "2*Long/MAX_VALUE wraps to -2; Clojure * would become a BigInt")))


(deftest aarch64-coalesces-phi-edge-and-return-moves-into-direct-results
  (let [form '(+ 1 (if a (* a 2) (- a 3)))
        arm (machine/compile-gmir
             :aarch64 (machine/lower-kir-expression ['a] form))
        x86 (machine/compile-gmir
             :x86-64 (machine/lower-kir-expression ['a] form))]
    (is (not-any? #{:aarch64/move}
                  (keep :mc/encoding (:mc/instructions arm)))
        "both phi edges write their destination directly")
    (is (= 3 (count (filter #{:x86-64/move}
                            (keep :mc/encoding (:mc/instructions x86)))))
        "the AArch64 pass leaves x86 allocation unchanged")
    (is (seq (machine/encode-mc arm)))))

(deftest aarch64-keeps-an-edge-move-when-its-source-is-live-at-the-join
  (let [program
        (machine/lower-mc
         {:mir/version 1 :mir/target :aarch64 :mir/registers :physical
          :mir/frame-slots 0
          :mir/instructions
          [{:mir/op :mir/add :mir/dst :aarch64/x2
            :mir/left :aarch64/x0 :mir/right :aarch64/x1}
           {:mir/op :mir/move :mir/dst :aarch64/x3 :mir/src :aarch64/x2}
           {:mir/op :mir/jump :mir/target :test.label/join}
           {:mir/op :mir/label :mir/id :test.label/join}
           {:mir/op :mir/add :mir/dst :aarch64/x4
            :mir/left :aarch64/x2 :mir/right :aarch64/x3}
           {:mir/op :mir/return :mir/value :aarch64/x4}]})]
    (is (= 1 (count (filter #{:aarch64/move}
                            (keep :mc/encoding (:mc/instructions program)))))
        "the target-block live-in prevents unsafe physical-register reuse")))

(deftest aarch64-fusion-rejects-input-clobbers-and-product-minus-addends
  (let [lower (fn [instructions]
                (machine/lower-mc
                 {:mir/version 1 :mir/target :aarch64 :mir/registers :physical
                  :mir/frame-slots 0 :mir/instructions (vec instructions)}))
        multiply {:mir/op :mir/multiply :mir/dst :aarch64/x2
                  :mir/left :aarch64/x0 :mir/right :aarch64/x1}
        return {:mir/op :mir/return :mir/value :aarch64/x3}
        clobbered (lower [multiply
                          {:mir/op :mir/constant :mir/dst :aarch64/x0 :mir/value 9}
                          {:mir/op :mir/add :mir/dst :aarch64/x3
                           :mir/left :aarch64/x2 :mir/right :aarch64/x0}
                          return])
        wrong-order (lower [multiply
                            {:mir/op :mir/subtract :mir/dst :aarch64/x3
                             :mir/left :aarch64/x2 :mir/right :aarch64/x0}
                            return])]
    (doseq [program [clobbered wrong-order]]
      (is (some #{:aarch64/multiply}
                (map :mc/encoding (:mc/instructions program))))
      (is (not-any? #{:aarch64/multiply-add :aarch64/multiply-subtract}
                    (map :mc/encoding (:mc/instructions program)))))))

(deftest aarch64-fusion-allows-a-multiply-destination-to-alias-an-input
  (let [program
        (machine/lower-mc
         {:mir/version 1 :mir/target :aarch64 :mir/registers :physical
          :mir/frame-slots 0
          :mir/instructions
          [{:mir/op :mir/multiply :mir/dst :aarch64/x0
            :mir/left :aarch64/x0 :mir/right :aarch64/x1}
           {:mir/op :mir/constant :mir/dst :aarch64/x2 :mir/value 1}
           {:mir/op :mir/add :mir/dst :aarch64/x3
            :mir/left :aarch64/x0 :mir/right :aarch64/x2}
           {:mir/op :mir/return :mir/value :aarch64/x3}]})]
    (is (= 1 (count (filter #{:aarch64/multiply-add}
                            (map :mc/encoding (:mc/instructions program))))))))

(def spill-program
  (let [registers (mapv gmir/vreg (range 11))]
    {:gmir/version 1
     :gmir/instructions
     (vec (concat
           (map-indexed (fn [index register]
                          {:gmir/op :gmir/constant :gmir/dst register
                           :gmir/value index})
                        (subvec registers 0 6))
           [{:gmir/op :gmir/add :gmir/dst (registers 6)
             :gmir/left (registers 0) :gmir/right (registers 1)}
            {:gmir/op :gmir/add :gmir/dst (registers 7)
             :gmir/left (registers 2) :gmir/right (registers 3)}
            {:gmir/op :gmir/add :gmir/dst (registers 8)
             :gmir/left (registers 4) :gmir/right (registers 5)}
            {:gmir/op :gmir/add :gmir/dst (registers 9)
             :gmir/left (registers 6) :gmir/right (registers 7)}
            {:gmir/op :gmir/add :gmir/dst (registers 10)
             :gmir/left (registers 9) :gmir/right (registers 8)}
            {:gmir/op :gmir/return :gmir/value (registers 10)}]))}))

(def program
  {:gmir/version 1
   :gmir/instructions
   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
    {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
    {:gmir/op :gmir/branch-zero :gmir/test v2 :gmir/target :test.label/zero}
    {:gmir/op :gmir/return :gmir/value v2}
    {:gmir/op :gmir/label :gmir/id :test.label/zero}
    {:gmir/op :gmir/return :gmir/value v1}]})

(def dual-phi-program
  (let [[test then-a then-b else-a else-b join-a join-b result]
        (mapv gmir/vreg (range 8))]
    {:gmir/version 2
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst test :gmir/index 0}
      {:gmir/op :gmir/branch-zero :gmir/test test :gmir/target :test.label/else}
      {:gmir/op :gmir/label :gmir/id :test.label/then}
      {:gmir/op :gmir/constant :gmir/dst then-a :gmir/value 1}
      {:gmir/op :gmir/constant :gmir/dst then-b :gmir/value 2}
      {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/else}
      {:gmir/op :gmir/constant :gmir/dst else-a :gmir/value 3}
      {:gmir/op :gmir/constant :gmir/dst else-b :gmir/value 4}
      {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/join}
      {:gmir/op :gmir/phi :gmir/dst join-a
       :gmir/incomings [{:gmir/predecessor :test.label/then-exit
                         :gmir/value then-a}
                        {:gmir/predecessor :test.label/else-exit
                         :gmir/value else-a}]}
      {:gmir/op :gmir/phi :gmir/dst join-b
       :gmir/incomings [{:gmir/predecessor :test.label/then-exit
                         :gmir/value then-b}
                        {:gmir/predecessor :test.label/else-exit
                         :gmir/value else-b}]}
      {:gmir/op :gmir/add :gmir/dst result :gmir/left join-a :gmir/right join-b}
      {:gmir/op :gmir/return :gmir/value result}]}))

(def scalar-record-type
  [:record :test/pair [[:a :i64] [:b :i64]]])

(def record-sroa-form
  '(let [r (if a
             (record-new [:record :test/pair [[:a :i64] [:b :i64]]] 1 2)
             (record-new [:record :test/pair [[:a :i64] [:b :i64]]] 3 4))]
     (+ (record-get [:record :test/pair [[:a :i64] [:b :i64]]] r :a)
        (record-get [:record :test/pair [[:a :i64] [:b :i64]]] r :b))))

(def scalar-variant-type
  [:variant :test/number-or-flag [[:number :i64] [:flag :bool]]])

(def variant-sroa-form
  '(let [v (if a
             (variant-new [:variant :test/number-or-flag
                           [[:number :i64] [:flag :bool]]]
                          :number 41)
             (variant-new [:variant :test/number-or-flag
                           [[:number :i64] [:flag :bool]]]
                          :flag false))]
     (variant-match [:variant :test/number-or-flag
                     [[:number :i64] [:flag :bool]]]
                    v
                    [[:number payload (+ payload 1)]
                     [:flag payload (if payload 1 7)]])))

(deftest closed-gmir-reaches-allocated-mc-for-both-targets
  (doseq [target [:x86-64 :aarch64]]
    (let [mc (machine/compile-gmir target program)]
      (is (= target (:mc/target mc)))
      (is (= 1 (count (filter #(= :mc/branch-zero (:mc/op %))
                             (:mc/instructions mc)))))
      (is (= 1 (count (filter #(= :mir/label (:mir/op %))
                             (:mc/instructions mc)))))
      (is (not-any? #(and (keyword? %)
                          (= "kotoba.gmir.vreg" (namespace %)))
                    (tree-seq coll? seq mc))))))

(deftest runtime-handle-operations-lower-through-the-closed-call-boundary
  (let [cases [['[a b] '(pair a b) :pair]
               ['[p] '(pair-first p) :pair-first]
               ['[p] '(pair-second p) :pair-second]
               ['[e a v] '(kgraph-assert! e a v) :kgraph-assert!]
               ['[e a] '(kgraph-get e a) :kgraph-get]
               ['[a] '(kgraph-count a) :kgraph-count]
               ['[a i] '(kgraph-entity-at a i) :kgraph-entity-at]
               ['[s] '(string-byte-length s) :string-byte-length]
               ['[a b] '(string=? a b) :string=?]
               ['[a b] '(string-concat a b) :string-concat]
               ['[s i n] '(string-substring s i n) :string-substring]
               ['[s i] '(string-code-point-at s i) :string-code-point-at]
               [[] '(vector-new-empty) :vector-new-empty]
               ['[v x] '(vector-conj v x) :vector-conj]
               ['[v] '(vector-count v) :vector-count]
               ['[v i] '(vector-at v i) :vector-at]
               ['[v i x] '(vector-assoc v i x) :vector-assoc]
               ['[v n] '(vector-drop v n) :vector-drop]]]
    (doseq [[params form runtime] cases]
      (is (machine/pilot-expression? params form) (str runtime))
      (let [instructions (:gmir/instructions
                          (machine/lower-kir-expression params form))
            call (first (filter #(= :gmir/runtime-call (:gmir/op %))
                                instructions))]
        (is (= runtime (:gmir/runtime call)) (str runtime))
        (is (= (get gmir/runtime-operation-arities runtime)
               (count (:gmir/arguments call))) (str runtime))))))

(deftest runtime-call-encoders-preserve-the-hidden-context-register
  (let [x86-code (machine/compile-expression :x86-64 '[v] '(vector-count v))
        arm-code (machine/compile-expression :aarch64 '[v] '(vector-count v))
        contains-bytes? (fn [bytes needle]
                          (boolean (some #(= (vec needle) %)
                                         (partition (count needle) 1 bytes))))]
    (is (contains-bytes? x86-code [0x41 0xff 0x91 0xa8 0x00 0x00 0x00])
        "x86 calls qword ptr [r9+168]")
    (is (contains-bytes? x86-code [0x4c 0x89 0x8c 0x24])
        "x86 saves r9 in its reserved call-frame slot")
    (is (contains-bytes? x86-code [0x4c 0x8b 0x8c 0x24])
        "x86 restores r9 after the host call")
    (is (contains-bytes? arm-code [0xf0 0x54 0x40 0xf9])
        "AArch64 loads x16 from [x7,#168]")
    (is (contains-bytes? arm-code [0x00 0x02 0x3f 0xd6])
        "AArch64 calls x16")
    (is (contains-bytes? arm-code [0xe7 0x03 0x00 0xf9])
        "AArch64 saves x7 across the host call")
    (is (contains-bytes? arm-code [0xe7 0x03 0x40 0xf9])
        "AArch64 restores x7 after the host call")))

(deftest capability-calls-lower-with-a-closed-id-and-kind
  (doseq [[form kind] [['(cap-call 7 x) :i64]
                       ['(typed-cap-call 7 :i64 :i64 x) :i64]
                       ['(typed-cap-call 7 :string :string x) :string]
                       ['(typed-cap-call 7 :option-i64 :option-i64 x) :option-i64]
                       ['(typed-cap-call 7 :result-i64 :result-i64 x) :result-i64]]]
    (is (machine/pilot-expression? '[x] form) (str kind))
    (let [call (->> (machine/lower-kir-expression '[x] form)
                    :gmir/instructions
                    (filter #(= :gmir/capability-call (:gmir/op %)))
                    first)]
      (is (= 7 (:gmir/capability call)) (str kind))
      (is (= kind (:gmir/kind call)) (str kind))))
  (is (not (machine/pilot-expression? '[x] '(cap-call 256 x))))
  (is (not (machine/pilot-expression?
            '[x] '(typed-cap-call 7 :string :result-i64 x)))))

(deftest clock-provider-contract-lowers-through-the-module-pipeline
  (let [request [:variant :kotoba.clock/request
                 [[:wall :bool] [:monotonic :bool]]]
        wall [:record :kotoba.clock/wall
              [[:unix-millis :i64] [:observation-sequence :i64]]]
        monotonic [:record :kotoba.clock/monotonic
                   [[:nanos :i64] [:observation-sequence :i64]]]
        error [:record :kotoba.clock/error
               [[:code :keyword] [:message :string]]]
        result [:variant :kotoba.clock/result
                [[:wall wall] [:monotonic monotonic] [:error error]]]
        body (list 'let ['answer
                         (list 'typed-cap-call 7 request result
                               (list 'variant-new request :wall false))]
                   (list 'variant-match result 'answer
                         [[:wall 'w (list 'record-get wall 'w :unix-millis)]
                          [:monotonic 'm (list 'record-get monotonic 'm :nanos)]
                          [:error 'e 0]]))
        module {:format :kotoba.kir/v4 :entry 'main :exports ['main]
                :functions [{:name 'main :params [] :param-types []
                             :result :i64 :body body}]}
        gmir (machine/lower-kir-module module)
        calls (filter #(= :gmir/capability-call (:gmir/op %))
                      (get-in gmir [:gmir/functions 0 :gmir/instructions]))]
    (is (machine/pilot-module? module))
    (is (= 1 (count calls)))
    (is (= :clock-v1 (:gmir/kind (first calls))))
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (:mc/functions (machine/compile-gmir target gmir))) target))))

(deftest dataspace-provider-contract-lowers-through-the-module-pipeline
  (let [request [:variant :kotoba.dataspace/request
                 [[:assert [:record :kotoba.dataspace/assert
                            [[:assertion :document] [:facet :i64]]]]
                  [:retract [:record :kotoba.dataspace/retract
                             [[:assertion :document] [:facet :i64]]]]
                  [:observe [:record :kotoba.dataspace/observe
                             [[:pattern :document] [:facet :i64]]]]
                  [:facet-enter :bool]
                  [:facet-leave :i64]]]
        asserted [:record :kotoba.dataspace/asserted
                  [[:count :i64] [:notices :document]]]
        retracted [:record :kotoba.dataspace/retracted [[:count :i64]]]
        matches [:record :kotoba.dataspace/matches
                 [[:bindings :document] [:notices :document]]]
        facet [:record :kotoba.dataspace/facet [[:id :i64]]]
        error [:record :kotoba.dataspace/error
               [[:code :keyword] [:message :string]]]
        result [:variant :kotoba.dataspace/result
                [[:asserted asserted] [:retracted retracted]
                 [:matches matches] [:facet facet] [:error error]]]
        body (list 'let ['answer
                         (list 'typed-cap-call 24 request result
                               (list 'variant-new request :facet-enter false))]
                   (list 'variant-match result 'answer
                         [[:asserted 'a (list 'record-get asserted 'a :count)]
                          [:retracted 'r (list 'record-get retracted 'r :count)]
                          [:matches 'm 0]
                          [:facet 'f (list 'record-get facet 'f :id)]
                          [:error 'e 0]]))
        module {:format :kotoba.kir/v4 :entry 'main :exports ['main]
                :functions [{:name 'main :params [] :param-types []
                             :result :i64 :body body}]}
        gmir (machine/lower-kir-module module)
        calls (filter #(= :gmir/capability-call (:gmir/op %))
                      (get-in gmir [:gmir/functions 0 :gmir/instructions]))]
    (is (machine/pilot-module? module))
    (is (= 1 (count calls)))
    (is (= :dataspace-v1 (:gmir/kind (first calls))))
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (:mc/functions (machine/compile-gmir target gmir))) target))))

(deftest ui-provider-contract-lowers-through-the-module-pipeline
  (let [parent [:option :keyword]
        node [:record :kotoba.ui/node
              [[:id :keyword] [:parent parent] [:kind :keyword] [:text :string]]]
        nodes [:set node]
        request [:record :kotoba.ui/commit-request
                 [[:base-revision :i64] [:nodes nodes]]]
        result [:record :kotoba.ui/commit-result
                [[:revision :i64] [:node-count :i64]]]
        event-request [:record :kotoba.ui/event-request [[:after-revision :i64]]]
        event [:record :kotoba.ui/event
               [[:revision :i64] [:target :keyword] [:kind :keyword] [:value :string]]]
        event-result [:option event]
        body (list 'let ['nodes
                         (list 'typed-set-conj nodes
                               (list 'typed-set-new nodes)
                               (list 'record-new node :view/title
                                     (list 'option-none-of parent)
                                     :ui/text "ready"))
                         'committed
                         (list 'typed-cap-call 9 request result
                               (list 'record-new request 0 'nodes))
                         'pending
                         (list 'typed-cap-call 10 event-request event-result
                               (list 'record-new event-request 0))]
                   (list '+ (list 'record-get result 'committed :revision)
                         (list 'option-match event-result 'pending
                               0 'e (list 'record-get event 'e :revision))))
        module {:format :kotoba.kir/v4 :entry 'main :exports ['main]
                :functions [{:name 'main :params [] :param-types []
                             :result :i64 :body body}]}
        gmir (machine/lower-kir-module module)
        calls (filter #(= :gmir/capability-call (:gmir/op %))
                      (get-in gmir [:gmir/functions 0 :gmir/instructions]))]
    (is (machine/pilot-module? module))
    (is (= 2 (count calls)))
    (is (= #{:ui-commit-v1 :ui-event-v1} (set (map :gmir/kind calls))))
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (:mc/functions (machine/compile-gmir target gmir))) target))))

(deftest capability-call-encoders-check-policy-before-the-host-call
  (let [x86-scalar (machine/compile-expression :x86-64 '[x] '(cap-call 7 x))
        x86-typed (machine/compile-expression
                   :x86-64 '[x] '(typed-cap-call 7 :string :string x))
        arm-typed (machine/compile-expression
                   :aarch64 '[x] '(typed-cap-call 7 :string :string x))
        contains-bytes? (fn [bytes needle]
                          (boolean (some #(= (vec needle) %)
                                         (partition (count needle) 1 bytes))))]
    (is (contains-bytes? x86-scalar [0x41 0xf6 0x41 0x10 0x80
                                     0x75 0x02 0x0f 0x0b])
        "x86 tests capability bit 7 before UD2")
    (is (contains-bytes? x86-scalar [0x41 0xff 0x51 0x30])
        "scalar capability calls context offset 48")
    (is (contains-bytes? x86-typed [0x41 0xff 0x91 0x80 0x00 0x00 0x00])
        "typed capability calls context offset 128")
    (is (contains-bytes? arm-typed [0x00 0x00 0x20 0xd4])
        "AArch64 denial reaches BRK before BLR")
    (is (contains-bytes? arm-typed [0xf0 0x40 0x40 0xf9])
        "AArch64 loads the typed callback from [x7,#128]")
    (is (contains-bytes? arm-typed [0x00 0x02 0x3f 0xd6])
        "AArch64 calls the checked callback")))

(deftest option-and-result-sugar-normalizes-to-the-closed-pair-runtime
  (let [forms ['(option-some? (option-some 7))
               '(option-value (option-none) 9)
               '(option-some?-of [:option :i64]
                                 (option-some-of [:option :i64] 7))
               '(option-value-of [:option :i64]
                                 (option-none-of [:option :i64]) 9)
               '(option-match [:option :i64]
                              (option-some-of [:option :i64] 7)
                              0 value (+ value 1))
               '(result-ok? (result-ok 7))
               '(result-value (result-err 8) 9)
               '(result-error (result-ok 7) 9)
               '(result-ok?-of [:result :i64 :i64]
                               (result-err-of [:result :i64 :i64] 8))
               '(result-value-of [:result :i64 :i64]
                                 (result-ok-of [:result :i64 :i64] 7) 9)
               '(result-error-of [:result :i64 :i64]
                                 (result-err-of [:result :i64 :i64] 8) 9)
               '(result-match-of [:result :i64 :i64]
                                 (result-ok-of [:result :i64 :i64] 7)
                                 value (+ value 1) error (+ error 2))]]
    (doseq [form forms]
      (is (machine/pilot-expression? [] form) (pr-str form))
      (let [instructions (:gmir/instructions
                          (machine/lower-kir-expression [] form))]
        (is (some #(= :gmir/runtime-call (:gmir/op %)) instructions)
            (pr-str form))
        (is (= :gmir/return (:gmir/op (peek instructions))) (pr-str form)))))
  (let [instructions (:gmir/instructions
                      (machine/lower-kir-expression
                       [] '(option-value (pair 1 7) 0)))]
    (is (= 1 (count (filter #(= :pair (:gmir/runtime %)) instructions)))
        "the tagged expression is evaluated exactly once"))
  (is (not (machine/pilot-expression? [] '(option-match :bad 0 1 2 3))))
  (is (not (machine/pilot-expression? [] '(result-match-of :bad 0 x 1 2 3)))))

(deftest composite-vector-and-keyword-operations-use-the-runtime-ir
  (doseq [form ['(vector-count (vector-new 1 2 3))
                '(vector-f64-count (vector-f64-new 1 2 3))
                '(vector-get (vector-new 4 5) 1 9)
                '(vector-f64-get (vector-f64-new 4 5) -1 9)
                '(string-byte-length (keyword-name keyword-handle))]]
    (let [params (if (some #{'keyword-handle} (tree-seq coll? seq form))
                   '[keyword-handle] [])]
      (is (machine/pilot-expression? params form) (pr-str form))
      (is (seq (filter #(= :gmir/runtime-call (:gmir/op %))
                       (:gmir/instructions
                        (machine/lower-kir-expression params form))))
          (pr-str form))))
  (let [instructions (:gmir/instructions
                      (machine/lower-kir-expression
                       [] '(vector-get (vector-new 4 5) 1 9)))]
    (is (= 1 (count (filter #(= :vector-new-empty (:gmir/runtime %))
                            instructions))))
    (is (= 2 (count (filter #(= :vector-conj (:gmir/runtime %))
                            instructions))))))

(deftest search-and-index-helpers-use-the-word-call-module
  (doseq [function [{:name 'main :params '[subject needle]
                     :result :bool
                     :body '(string-contains? subject needle)}
                    {:name 'main :params '[subject needle replacement]
                     :result :string
                     :body '(string-replace-all subject needle replacement)}
                    {:name 'main :params '[index key]
                     :result :bool
                     :body '(string-index-contains index key)}]]
    (let [kir {:format :kotoba.kir/v4 :exports ['main]
               :functions (-> [function]
                              string-search/augment-functions
                              string-index/augment-functions)}]
      (is (machine/pilot-module? kir) (:body function))
      (doseq [target [:x86-64 :aarch64]]
        (is (seq (:code (machine/compile-kir-module target kir)))
            [target (:body function)])))))

(deftest immutable-utf8-data-is-laid-out-after-machine-code
  (doseq [form ["hello😀" :ready '(keyword-from-string "ready")
                '(keyword-name :ready)]]
    (let [lowered (machine/lower-kir-expression [] form)]
      (is (some #(= :gmir/data-address (:gmir/op %))
                (:gmir/instructions lowered)) (pr-str form))
      (is (some #(= :pair (:gmir/runtime %))
                (:gmir/instructions lowered)) (pr-str form))))
  (let [content "hello😀"
        bytes (mapv #(bit-and (int %) 0xff) (.getBytes content "UTF-8"))
        kir {:format :kotoba.kir/v4 :exports ['main]
             :functions [{:name 'main :params [] :param-types []
                          :result :string :body content}]}]
    (is (not (machine/pilot-expression? [] content))
        "literal placement requires whole-module layout")
    (is (machine/pilot-module? kir))
    (doseq [target [:x86-64 :aarch64]]
      (let [{:keys [code exports]} (machine/compile-kir-module target kir)
            {:keys [offset length]} (get exports 'main)]
        (is (= bytes (subvec code (- (count code) (count bytes)))) target)
        (is (= 0 offset) target)
        (is (= (- (count code) (count bytes)) length)
            "export length excludes the immutable data pool")))))

(deftest allocation-is-deterministic-and-fails-closed
  (is (= (machine/compile-gmir :x86-64 program)
         (machine/compile-gmir :x86-64 program)))
  (testing "use before definition"
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/compile-gmir
                  :x86-64
                  {:gmir/version 1
                   :gmir/instructions
                   [{:gmir/op :gmir/return :gmir/value v0}]}))))
  (testing "unknown operations do not fall through"
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/compile-gmir
                  :aarch64
                  {:gmir/version 1
                   :gmir/instructions [{:gmir/op :gmir/magic}]})))))

(deftest shared-mc-contract-gates-the-target-encoder
  (let [mc (machine/compile-gmir :x86-64 program)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/encode-mc
                  (assoc-in mc [:mc/instructions 0 :mc/encoding]
                            :aarch64/argument))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/encode-mc
                  (assoc-in mc [:mc/instructions 0 :ambient/policy] true))))))

(defmacro with-scratch-tier-only
  "Run BODY with only the always-available scratch tier on offer. Tests that
  pin what happens once the profile is exhausted have to be able to exhaust it;
  widening the pool would otherwise turn them into tests of nothing that keep
  passing under their original names."
  [& body]
  `(with-redefs [mir/leaf-registers {:x86-64 [] :aarch64 []}
                 mir/preserved-registers {:x86-64 [] :aarch64 []}]
     ~@body))

(deftest exhausted-register-profile-encodes-bounded-spills-for-both-isas
  (with-scratch-tier-only
    (let [x86-mc (machine/compile-gmir :x86-64 spill-program)
          arm-mc (machine/compile-gmir :aarch64 spill-program)
          x86 (machine/encode-mc x86-mc)
          arm (machine/encode-mc arm-mc)]
      ;; Eleven values in a four-register profile take two slots, not
      ;; eleven: the allocator spills the two it cannot keep and leaves the
      ;; rest in registers. A 16-byte frame rather than 96.
      (is (= 2 (:mc/frame-slots x86-mc)))
      (is (= 2 (:mc/frame-slots arm-mc)))
      (doseq [mc [x86-mc arm-mc]]
        (is (some #(= "spill-store" (some-> % :mc/encoding name))
                  (:mc/instructions mc)))
        (is (some #(= "spill-load" (some-> % :mc/encoding name))
                  (:mc/instructions mc))))
      (is (= [0x48 0x81 0xec 0x10 0x00 0x00 0x00]
             (subvec x86 0 7)))
      (is (= [0x48 0x81 0xc4 0x10 0x00 0x00 0x00 0xc3]
             (subvec x86 (- (count x86) 8))))
      (is (= [0xc0 0x03 0x5f 0xd6]
             (subvec arm (- (count arm) 4))))
      (is (= [0xff 0x43 0x00 0xd1]
             (subvec arm 0 4)))
      (is (= [0xff 0x43 0x00 0x91 0xc0 0x03 0x5f 0xd6]
             (subvec arm (- (count arm) 8)))))))

(deftest kir-expression-slice-encodes-final-bytes-for-both-isas
  (is (= [0x48 0x89 0xf8             ; mov rax,rdi
          0x48 0x89 0xf1             ; mov rcx,rsi
          0x48 0x89 0xc2             ; mov rdx,rax
          0x48 0x01 0xca             ; add rdx,rcx
          0x48 0x89 0xd0 0xc3]       ; mov rax,rdx; ret
         (machine/compile-expression :x86-64 ['a 'b] '(+ a b))))
  (is (= [0x00 0x00 0x01 0x8b       ; add x0,x0,x1
          0xc0 0x03 0x5f 0xd6]      ; ret
         (machine/compile-expression :aarch64 ['a 'b] '(+ a b)))))

(deftest recursive-i64-arithmetic-reaches-final-bytes-for-both-isas
  (doseq [form ['(- a) '(- a b) '(* a b) '(quot a b)
                '(bit-and a b) '(bit-or a b) '(bit-xor a b)
                '(+ (* a b) (- a b)) '(+ a b 3 4)
                '(bit-xor a b 3 4)]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x00 0x00 0x01 0xcb 0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 ['a 'b] '(- a b))))
  (is (machine/pilot-expression? ['a 'b]
                                 '(+ (* a 6) (bit-xor (- a b) 3)))))

(deftest native-word-operations-route-through-machine-ir
  (doseq [form ['(bool-not a) '(bit-not a)
                '(i64-shift-left a 3) '(i64-shift-right a 3)
                '(u64-shift-right a 3) '(i32-wrap a) '(u32-wrap a)
                '(i32-wrapping-add a b) '(i32-wrapping-mul a b)
                '(i32-xor a b) '(i32-shift-left a 3)
                '(i32-shift-right a 3) '(u32-shift-right a 3)]]
    (is (machine/pilot-expression? ['a 'b] form) form)
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (machine/compile-expression target ['a 'b] form))
          [target form])))
  (let [operations (->> '(i32-shift-right a 3)
                        (machine/lower-kir-expression ['a 'b])
                        :gmir/instructions
                        (mapv :gmir/op))]
    (is (some #{:gmir/shift-left} operations))
    (is (some #{:gmir/shift-right-signed} operations))))

(deftest bounded-kernel-memory-routes-through-machine-ir
  (let [forms ['(kernel-load-u8 b l i)
               '(kernel-load-u8-4k b l i)
               '(kernel-load-u8-16k b l i)
               '(kernel-store-u8 b l i v)
               '(kernel-store-u8-4k b l i v)
               '(kernel-load-u32 b l i)
               '(kernel-store-u32 b l i v)
               '(kernel-subregion b l i v)]]
    (doseq [form forms]
      (is (machine/pilot-expression? ['b 'l 'i 'v] form) form)
      (doseq [target [:x86-64 :aarch64]]
        (is (seq (machine/compile-expression target ['b 'l 'i 'v] form))
            [target form]))))
  (let [instructions (:gmir/instructions
                      (machine/lower-kir-expression
                       ['b 'l 'i] '(kernel-load-u8-16k b l i)))
        load (first (filter #(= :gmir/kernel-load-u8 (:gmir/op %))
                            instructions))]
    (is (= 16384 (:gmir/maximum load)))
    (is (= :gmir/return (:gmir/op (last instructions))))))

(deftest x86-privileged-operations-route-through-closed-machine-ir
  (let [cases
        [[[] '(kernel-boot-info) :boot-info [0x4d 0x8b 0x51 0x50]]
         [[] '(kernel-read-cr0) :read-cr0 [0x41 0x0f 0x20 0xc2]]
         [['a] '(kernel-write-cr0 a) :write-cr0 [0x41 0x0f 0x22 0xc2]]
         [[] '(kernel-read-cr2) :read-cr2 [0x41 0x0f 0x20 0xd2]]
         [[] '(kernel-read-cr3) :read-cr3 [0x41 0x0f 0x20 0xda]]
         [['a] '(kernel-write-cr3 a) :write-cr3 [0x41 0x0f 0x22 0xda]]
         [['a] '(kernel-invlpg a) :invlpg [0x41 0x0f 0x01 0x3a]]
         [[] '(kernel-read-cs) :read-cs [0x66 0x41 0x8c 0xca]]
         [[] '(kernel-page-fault-handler-address) :page-fault-handler-address
          [0x41 0x0f 0x20 0xd2 0x4c 0x8b 0x1c 0x24]]
         [[] '(kernel-page-fault-recovery-handler-address) :page-fault-recovery-handler-address
          [0x48 0xcf]]
         [['a 'b] '(kernel-configure-page-fault-recovery a b)
          :configure-page-fault-recovery [0x4c 0x89 0x14 0x25 0x00 0x01 0x11 0x00]]
         [[] '(kernel-double-fault-handler-address) :double-fault-handler-address
          [0x4d 0x8d 0x7e 0xd0 0x4d 0x39 0xfa]]
         [['a 'b] '(kernel-configure-double-fault-ist a b)
          :configure-double-fault-ist [0x4c 0x89 0x14 0x25 0x80 0x01 0x11 0x00]]
         [['a 'b] '(kernel-load-gdt-tss a b) :load-gdt-tss
          [0x41 0x0f 0x01 0x12]]
         [['a 'b] '(kernel-load-idt a b) :load-idt [0x41 0x0f 0x01 0x1a]]
         [[] '(kernel-probe-guard-write) :probe-guard-write
          [0xc6 0x04 0x25 0x00 0x00 0x10 0x00 0x00]]
         [[] '(kernel-probe-text-write) :probe-text-write
          [0xc6 0x04 0x25 0x00 0x10 0x10 0x00 0x00]]
         [[] '(kernel-probe-nx-execute) :probe-nx-execute
          [0x49 0xba 0x00 0x00 0x11 0x00 0x00 0x00 0x00 0x00]]
         [[] '(kernel-probe-recoverable-guard-write) :probe-recoverable-guard-write
          [0x49 0xc7 0xc2 0x00 0x00 0x10 0x00 0x41 0xc6 0x02 0x00
           0x4d 0x31 0xd2]]
         [[] '(kernel-probe-double-fault) :probe-double-fault
          [0x41 0xbb 0x00 0x00 0x10 0x00 0x41 0xc6 0x03 0x00]]
         [[] '(kernel-cli) :cli [0xfa]]
         [[] '(kernel-sti) :sti [0xfb]]
         [[] '(kernel-hlt) :hlt [0xf4]]
         [[] '(kernel-pause) :pause [0xf3 0x90]]
         [['a 'b] '(kernel-out-u8 a b) :out-u8 [0xee]]
         [['a 'b] '(kernel-out-u32 a b) :out-u32 [0xef]]
         [['a] '(kernel-in-u8 a) :in-u8 [0xec]]
         [['a] '(kernel-in-u32 a) :in-u32 [0xed]]
         [['a] '(kernel-read-msr a) :read-msr [0x0f 0x32]]
         [['a 'b] '(kernel-write-msr a b) :write-msr [0x0f 0x30]]
         [['a 'b] '(kernel-cpuid-eax a b) :cpuid-eax [0x0f 0xa2]]
         [['a 'b] '(kernel-cpuid-ebx a b) :cpuid-ebx [0x0f 0xa2]]
         [['a 'b] '(kernel-cpuid-ecx a b) :cpuid-ecx [0x0f 0xa2]]
         [['a 'b] '(kernel-cpuid-edx a b) :cpuid-edx [0x0f 0xa2]]]
        contains-bytes? (fn [bytes needle]
                          (boolean (some #{needle}
                                         (partition (count needle) 1 bytes))))]
    (doseq [[params form action needle] cases]
      (testing (str form)
        (is (machine/pilot-expression? params form))
        (let [gmir (machine/lower-kir-expression params form)
              operation (first (filter #(= :gmir/x86-privileged (:gmir/op %))
                                       (:gmir/instructions gmir)))
              bytes (machine/compile-expression :x86-64 params form)]
          (is (= action (:gmir/action operation)))
          (is (contains-bytes? bytes needle)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"x86-privileged-target-mismatch"
                              (machine/compile-expression :aarch64 params form)))))))

(deftest parameters-are-materialized-before-expression-temporaries
  ;; AArch64 passes arguments in the same x0-x4 register set used by this
  ;; bounded allocator. If a constant is emitted first, it can overwrite an
  ;; ABI argument before the later `:gmir/argument` instruction reads it.
  (doseq [form ['(- a) '(+ 1 a) '(* 2 (+ 3 a)) '(* a 48271N)]]
    (let [instructions (:gmir/instructions
                        (machine/lower-kir-expression ['a] form))]
      (is (= :gmir/argument (:gmir/op (first instructions))) form)
      (is (= 0 (:gmir/index (first instructions))) form)
      (is (seq (machine/compile-expression :aarch64 ['a] form)) form))))

(deftest x86-signed-division-preserves-all-implicit-registers
  (let [bytes (machine/compile-expression
               :x86-64 [] '(+ (* 3 4) (quot 10 2)))
        division-window [0x50             ; push rax
                         0x52             ; push rdx (live product)
                         0x51             ; push rcx
                         0x48 0x8b 0x8c 0x24 0x10 0x00 0x00 0x00 ; divisor
                         0x4c 0x89 0xc0   ; mov rax,r8 (dividend)
                         0x48 0x99         ; cqo
                         0x48 0xf7 0xf9   ; idiv rcx
                         0x48 0x89 0xc1   ; quotient -> allocated rcx
                         0x48 0x81 0xc4 0x08 0x00 0x00 0x00 ; discard old rcx
                         0x5a             ; restore live rdx
                         0x58]]           ; restore rax
    (is (= 1 (count (filter #(= division-window %)
                            (partition (count division-window) 1 bytes)))))))

(deftest aarch64-signed-division-explicitly-traps-kir-error-cases
  (let [bytes (machine/compile-expression :aarch64 ['a 'b] '(quot a b))
        words (mapv vec (partition 4 bytes))]
    (is (= 1 (count (filter #(= [0x00 0x00 0x20 0xd4] %) words)))
        "BRK is shared by the zero and MIN/-1 guards")
    (is (some #(= [0x02 0x0c 0xc1 0x9a] %) words)
        "the guarded operation remains sdiv x2,x0,x1 after allocation")))

(defn- floor-div [left right]
  (let [q (quot left right)
        remainder (- left (* q right))]
    (if (and (neg? left) (not (zero? remainder))) (dec q) q)))

(defn- apply-signed-division-magic [numerator divisor]
  (let [numerator (bigint numerator)
        {:keys [multiplier shift add-numerator? subtract-numerator?]}
        (machine/signed-division-magic divisor)
        high (floor-div (* numerator multiplier)
                        18446744073709551616N)
        corrected (cond add-numerator? (+ high numerator)
                        subtract-numerator? (- high numerator)
                        :else high)
        shifted (floor-div corrected (bit-shift-left 1 shift))]
    (+ shifted (if (neg? shifted) 1 0))))

(deftest signed-constant-division-reciprocals-match-i64-truncation
  (let [divisors [2 3 5 7 10 31 127 255 1024 2147483647
                  -2 -3 -5 -7 -10 -31 -127 -255 -1024 -2147483647
                  Long/MAX_VALUE (- Long/MAX_VALUE)]
        numerators [Long/MIN_VALUE (inc Long/MIN_VALUE) -1000000000000
                    -1000 -1 0 1 2 1000 1000000000000
                    (dec Long/MAX_VALUE) Long/MAX_VALUE]]
    (doseq [divisor divisors, numerator numerators]
      (is (= (quot numerator divisor)
             (apply-signed-division-magic numerator divisor))
          {:numerator numerator :divisor divisor})))
  (is (nil? (machine/signed-division-magic 0)))
  (is (nil? (machine/signed-division-magic 1)))
  (is (nil? (machine/signed-division-magic -1))))

(deftest aarch64-reciprocal-combines-the-sign-correction
  (let [bytes (#'machine/a64-quotient-constant
               :aarch64/x2 :aarch64/x0 2147483647 true)
        words (mapv vec (partition 4 bytes))]
    (is (= [0x22 0xfe 0x51 0x8b] (peek words))
        "ADD X2,X17,X17,LSR#63")
    (is (= 7 (count words))
        "three-word magic plus SMULH, numerator ADD, ASR, shifted ADD")
    (is (not-any? #{[0x30 0xfe 0x7f 0xd3]} words)
        "the standalone LSR correction is gone")))

(deftest aarch64-folds-single-use-add-sub-immediates
  (let [words (fn [form]
                (mapv vec (partition 4
                                     (machine/compile-expression
                                      :aarch64 ['n] form))))]
    (is (= [0x00 0x1c 0x00 0x91] (first (words '(+ n 7))))
        "ADD X0,X0,#7 writes the return register directly")
    (is (= [0x00 0x1c 0x00 0xd1] (first (words '(+ n -7))))
        "negative ADD becomes SUB immediate")
    (is (= [0x00 0x04 0x40 0xd1] (first (words '(- n 4096))))
        "SUB X0,X0,#1,LSL#12")
    (is (= [0x00 0x04 0x40 0x91] (first (words '(- n -4096))))
        "negative SUB becomes ADD immediate")
    (is (= 3 (count (words '(- 7 n))))
        "constant-minus-register cannot use the immediate form")
    (is (= 3 (count (words '(+ n 4097))))
        "a non-encodable immediate retains materialization")
    (is (= 5 (count (words '(if n (+ n 7) (- n 7)))))
        "each control-flow arm can fold its adjacent immediate")))

(deftest aarch64-immediate-folding-preserves-repeated-constant-cache-and-x86
  (let [form '(let [a (+ n 7)] (+ a 7))
        arm (mapv vec (partition 4
                               (machine/compile-expression :aarch64 ['n] form)))
        x86 (machine/compile-expression :x86-64 ['n] '(+ n 7))]
    (is (= [0x00 0x38 0x00 0x91] (first arm))
        "add-of-add-const folds to ADD X0,X0,#14; 7 is no longer repeated")
    (is (= 2 (count arm)))
    ;; The whole function, stated whole, because it is now small enough to be:
    ;;
    ;;   lea rdx,[rdi+7]   the parameter read straight into address arithmetic
    ;;   mov rax,rdx       the result into the return register
    ;;   ret
    ;;
    ;; It began as a constant materialized into a register, a copy, and an add.
    ;; Folding removed the materialization, `lea` removed the add, and copy
    ;; propagation removed the copy — three passes, each of which left this
    ;; assertion stale, which is why it is now the entire body rather than a
    ;; window at an offset that moves every time the code gets shorter.
    ;;
    ;; What it guards is unchanged: AArch64 shows a cached constant register
    ;; here, and none of that reaches x86-64, which selects for itself.
    (is (= [0x48 0x8d 0x97 0x07 0x00 0x00 0x00 0x48 0x89 0xd0 0xc3] x86)
        "x86-64 selects its own address arithmetic rather than AArch64's shape")
    (is (not-any? #{0xb8 0xb9} x86)
        "and materializes no constant register on the way")))

(deftest v3-constant-division-selects-reciprocal-machine-code
  (let [kir {:format :kotoba.kir/v3 :entry 'kernel :exports ['kernel]
             :functions [{:name 'kernel :params ['n]
                          :body '(quot n 2147483647)}]}
        gmir (machine/lower-kir-module kir)]
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)
            instructions (mapcat :mc/instructions (:mc/functions mc))
            quotient (first (filter #(= (keyword (name target)
                                                 "quotient-constant")
                                          (:mc/encoding %))
                                    instructions))
            code (:code (machine/compile-kir-module target kir))]
        (is (= 2147483647 (:mir/divisor quotient)) target)
        (is (not (contains? quotient :mir/right)) target)
        (is (not-any? #(and (= (keyword (name target) "constant")
                              (:mc/encoding %))
                           (= 2147483647 (:mir/value %)))
                      instructions)
            "the consumed divisor has no materialize instruction")
        (if (= :x86-64 target)
          (do
            (is (not-any? #{[0x48 0xf7 0xf9]} (partition 3 1 code))
                "constant division emits no idiv")
            (is (some #{[0x49 0xf7 0xea]} (partition 3 1 code))
                "constant division uses signed multiply-high"))
          (let [words (mapv vec (partition 4 code))]
            (is (not-any? #{[0x02 0x0c 0xc1 0x9a]} words)
                "constant division emits no SDIV family opcode")
            (is (some #(= [0x11 0x7c 0x50 0x9b] %) words)
                "constant division uses SMULH x17,x16 input allocation")))))))

(deftest scalar-comparisons-and-predicates-reach-final-bytes-for-both-isas
  (doseq [form ['(= a b) '(< a b) '(> a b) '(<= a b) '(>= a b)
                '(< a b 9) '(= a b 9)
                '(not a) '(zero? a) '(pos? a) '(neg? a)]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x48 0x89 0xf8 0x48 0x89 0xf1
          0x48 0x39 0xc8 0x0f 0x9c 0xc2 0x48 0x0f 0xb6 0xd2
          0x48 0x89 0xd0 0xc3]
         (machine/compile-expression :x86-64 ['a 'b] '(< a b))))
  (is (= [0x1f 0x00 0x01 0xeb 0xe0 0xa7 0x9f 0x9a
          0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 ['a 'b] '(< a b)))))

(deftest booleans-let-nested-tail-if-and-five-arguments-are-admitted
  (doseq [form [true false
                '(let [x (+ a b) y (* x c)] (if (< y d) y e))
                '(if (< a b) (if c 11 12) (if d 21 22))]]
    (is (machine/pilot-expression? ['a 'b 'c 'd 'e] form) form)
    (is (seq (machine/compile-expression :x86-64 ['a 'b 'c 'd 'e] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b 'c 'd 'e] form)) form)))

(deftest ordered-do-reaches-production-ir-without-dropping-traps
  (let [form '(do (+ a 1) (quot a b) (* a b))
        instructions (:gmir/instructions
                      (machine/lower-kir-expression ['a 'b] form))
        operations (mapv :gmir/op instructions)
        x86 (machine/compile-expression :x86-64 ['a 'b] form)
        arm (machine/compile-expression :aarch64 ['a 'b] form)]
    (is (machine/pilot-expression? ['a 'b] form))
    (is (< (.indexOf operations :gmir/add)
           (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/multiply))
        "all do forms retain source evaluation order")
    (is (= :gmir/return (last operations)))
    (is (= 1 (count (filter #(= [0x48 0xf7 0xf9] %)
                            (partition 3 1 x86))))
        "an unused x86 quotient still executes and can trap")
    (is (= 1 (count (filter #(= [0x00 0x00 0x20 0xd4] %)
                            (partition 4 arm))))
        "an unused AArch64 quotient retains the shared BRK guards"))
  (is (machine/pilot-expression? [] '(do 1)))
  (is (not (machine/pilot-expression? [] '(do)))
      "empty do has nil semantics and is outside the scalar i64 contract"))

(deftest ordered-do-can-delegate-its-final-expression-to-tail-control
  (let [form '(do (+ a 1) (quot a b) (if (< a b) 11 22))
        instructions (:gmir/instructions
                      (machine/lower-kir-expression ['a 'b] form))
        operations (mapv :gmir/op instructions)]
    (is (machine/pilot-expression? ['a 'b] form))
    (is (< (.indexOf operations :gmir/add)
           (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/less-than)
           (.indexOf operations :gmir/branch-zero))
        "prefix effects and traps execute before the tail condition")
    (is (= 2 (count (filter #(= :gmir/return %) operations)))
        "both tail arms return without a synthetic merge")
    (doseq [target [:x86-64 :aarch64]]
      (is (seq (machine/compile-expression target ['a 'b] form)) target)))
  (is (machine/pilot-expression? ['a]
                                 '(do (do (+ a 1))
                                      (if a (do 11) (do 22)))))
  (is (machine/pilot-expression? ['a] '(do (if a 1 2) 3))
      "a non-final if is now a real merge value and still executes in order"))

(deftest final-layout-resolves-branches-after-selected-instruction-sizes
  (let [x86 (machine/compile-expression :x86-64 ['p] '(if p 11 22))
        arm (machine/compile-expression :aarch64 ['p] '(if p 11 22))]
    ;; The displacement is 9 rather than 14 because the then arm is `mov
    ;; eax,11` now instead of `movabs rax,11` — five bytes narrower. That the
    ;; jz followed it is the property under test: layout resolved the branch
    ;; from the final selected sizes, not from a width assumed beforehand.
    (is (= [0x0f 0x84 0x09 0x00 0x00 0x00] (subvec x86 6 12))
        "x86 jz skips the selected then arm using next-PC rel32")
    (is (= [0x60 0x00 0x00 0xb4] (subvec arm 0 4))
        "AArch64 cbz x0 reaches the compact else label at +12 bytes")
    (is (= 30 (count x86)))
    (is (= 20 (count arm)))))

(deftest kir-to-gmir-boundary-rejects-unsupported-shapes
  (is (machine/pilot-expression? ['a] '(+ a (if a 1 2))))
  (is (seq (machine/compile-expression :aarch64 ['a] '(+ a (if a 1 2)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/compile-expression :aarch64 ['a] '(if a 1))))
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/compile-expression :aarch64 ['a] '(unknown a)))))

(deftest value-position-if-uses-versioned-phi-and-direct-edge-moves
  (let [form '(+ 1 (if a (* a 2) (- a 3)))
        gmir (machine/lower-kir-expression ['a] form)
        phi (first (filter #(= :gmir/phi (:gmir/op %))
                           (:gmir/instructions gmir)))]
    (is (= 2 (:gmir/version gmir)))
    (is (= 2 (count (:gmir/incomings phi))))
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)
            instructions (:mc/instructions mc)]
        (is (zero? (:mc/frame-slots mc)) target)
        (is (not-any? #(= :mir/phi (:mir/op %)) instructions) target)
        (is (= (if (= :x86-64 target) 3 0)
               (count (filter #(= (keyword (name target) "move")
                                     (:mc/encoding %))
                                instructions))) target)
        (is (not-any? #(contains? #{(keyword (name target) "spill-store")
                                    (keyword (name target) "spill-load")}
                                  (:mc/encoding %))
                      instructions) target)
        (is (seq (machine/encode-mc mc)) target))))
  (doseq [form ['(let [x (if a 2 3)] (* x 4))
                '(+ 1 (if a (if b 2 3) 4))
                '(do (if a 1 2) 3)
                '(if (if a 0 1) 7 8)]]
    (is (machine/pilot-expression? ['a 'b] form) form)
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form)))

(deftest acyclic-dual-phi-uses-scheduled-moves-without-a-frame
  (doseq [target [:x86-64 :aarch64]]
    (let [mc (machine/compile-gmir target dual-phi-program)
          encodings (mapv :mc/encoding (:mc/instructions mc))]
      (is (zero? (:mc/frame-slots mc)) target)
      (is (= (if (= :x86-64 target) 3 2)
             (count (filter #(= (keyword (name target) "move") %)
                              encodings)))
          target)
      (is (not-any? #(contains? #{(keyword (name target) "spill-store")
                                  (keyword (name target) "spill-load")}
                                %)
                    encodings)
          target)
      (is (seq (machine/encode-mc mc)) target)
      (is (= mc (machine/compile-gmir target dual-phi-program)) target))))

(deftest scalar-record-sroa-reaches-multi-phi-machine-ir
  (is (machine/pilot-expression? ['a] record-sroa-form))
  (let [gmir (machine/lower-kir-expression ['a] record-sroa-form)
        phis (filter #(= :gmir/phi (:gmir/op %)) (:gmir/instructions gmir))]
    (is (= 2 (:gmir/version gmir)))
    (is (= 2 (count phis)))
    (is (= gmir (machine/lower-kir-expression ['a] record-sroa-form)))
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)
            encodings (keep :mc/encoding (:mc/instructions mc))]
        (is (zero? (:mc/frame-slots mc)) target)
        (is (= (if (= :x86-64 target) 3 2)
               (count (filter #(= (keyword (name target) "move") %)
                                encodings)))
            target)
        (is (not-any? #(contains? #{(keyword (name target) "spill-store")
                                    (keyword (name target) "spill-load")}
                                  %)
                      encodings)
            target)
        (is (seq (machine/encode-mc mc)) target)))))

(deftest record-sroa-preserves-evaluation-of-unprojected-fields
  (let [form (list 'record-get scalar-record-type
                   (list 'record-new scalar-record-type (list 'quot 1 0) 9)
                   :b)
        gmir (machine/lower-kir-expression [] form)
        operations (mapv :gmir/op (:gmir/instructions gmir))]
    (is (machine/pilot-expression? [] form))
    (is (= 1 (count (filter #{:gmir/quotient} operations))))
    (is (< (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/return))
        "an unprojected field still evaluates and traps before the projection")))

(deftest record-sroa-fails-closed-outside-the-fixed-scalar-field-contract
  (let [different-type [:record :test/other [[:a :i64] [:b :i64]]]
        nested-type [:record :test/nested [[:child scalar-record-type]]]]
    (is (not (machine/pilot-expression?
              ['a]
              (list 'if 'a
                    (list 'record-new scalar-record-type 1 2)
                    (list 'record-new different-type 3 4)))))
    (is (not (machine/pilot-expression?
              [] (list 'record-new scalar-record-type 1 2))))
    (is (not (machine/pilot-expression?
              [] (list 'record-get scalar-record-type
                       (list 'record-new scalar-record-type 1 2) :missing))))
    (is (not (machine/pilot-expression?
              [] (list 'record-get nested-type
                       (list 'record-new nested-type
                             (list 'record-new scalar-record-type 1 2))
                       :child))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/lower-kir-expression
                  [] (list '+ (list 'record-new scalar-record-type 1 2) 3))))))

(deftest scalar-variant-sroa-reaches-tag-payload-phis-and-dispatch
  (is (machine/pilot-expression? ['a] variant-sroa-form))
  (let [gmir (machine/lower-kir-expression ['a] variant-sroa-form)
        instructions (:gmir/instructions gmir)
        phis (filter #(= :gmir/phi (:gmir/op %)) instructions)]
    (is (= 2 (:gmir/version gmir)))
    (is (= 4 (count phis))
        "tag and payload join independently; dispatch and branch result also join")
    (is (= 1 (count (filter #(= :gmir/equal (:gmir/op %)) instructions))))
    (is (= gmir (machine/lower-kir-expression ['a] variant-sroa-form)))
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)]
        (is (zero? (:mc/frame-slots mc)) target)
        (is (seq (machine/encode-mc mc)) target)))))

(deftest scalar-variant-payload-evaluates-once-even-when-branch-ignores-it
  (let [form (list 'variant-match scalar-variant-type
                   (list 'variant-new scalar-variant-type :number (list 'quot 1 0))
                   [[:number 'payload 9] [:flag 'payload 8]])
        operations (mapv :gmir/op
                         (:gmir/instructions
                          (machine/lower-kir-expression [] form)))]
    (is (machine/pilot-expression? [] form))
    (is (= 1 (count (filter #{:gmir/quotient} operations))))
    (is (< (.indexOf operations :gmir/quotient)
           (.indexOf operations :gmir/branch-zero)))))

(deftest scalar-variant-sroa-fails-closed-outside-its-local-contract
  (let [other [:variant :test/other [[:number :i64] [:flag :bool]]]
        non-scalar [:variant :test/text [[:number :i64] [:text :string]]]]
    (is (not (machine/pilot-expression?
              [] (list 'variant-new scalar-variant-type :number 1))))
    (is (not (machine/pilot-expression?
              [] (list 'variant-match scalar-variant-type
                       (list 'variant-new other :number 1)
                       [[:number 'x 'x] [:flag 'x 0]]))))
    (is (not (machine/pilot-expression?
              [] (list 'variant-match non-scalar
                       (list 'variant-new non-scalar :number 1)
                       [[:number 'x 'x] [:text 'x 0]]))))
    (is (not (machine/pilot-expression?
              [] (list 'variant-match scalar-variant-type
                       (list 'variant-new scalar-variant-type :number 1)
                       [[:flag 'x 0] [:number 'x 'x]]))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/lower-kir-expression
                  [] (list '+ (list 'variant-new scalar-variant-type :number 1) 3))))))

(deftest full-signed-i64-immediates-have-canonical-wire-bytes
  (is (= [0x48 0xb8 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0xc3]
         (machine/compile-expression :x86-64 [] Long/MAX_VALUE)))
  (is (= [0x00 0x00 0xf0 0x92 0xc0 0x03 0x5f 0xd6]
         (machine/compile-expression :aarch64 [] Long/MAX_VALUE)))
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/compile-expression :x86-64 [] (inc (bigint Long/MAX_VALUE))))))

(def scalar-call-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'add-one :params ['x] :result :i64 :body '(+ x 1)}
    {:name 'main :params ['x] :result :i64
     :body '(let [live 10] (+ live (add-one x)))}]})

(def scalar-call-branch-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'add-one :params ['x] :result :i64 :body '(+ x 1)}
    {:name 'main :params ['x] :result :i64
     :body '(let [live 10]
              (if (= x 0) 0 (+ live (add-one x))))}]})

(def four-argument-call-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'sum-four :params ['a 'b 'c 'd] :result :i64
     :body '(+ (+ a b) (+ c d))}
    {:name 'main :params ['a 'b 'c 'd] :result :i64
     :body '(sum-four a b c d)}]})

(def five-argument-call-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'sum-five :params ['a 'b 'c 'd 'e] :result :i64
     :body '(+ (+ (+ a b) (+ c d)) e)}
    {:name 'main :params ['a 'b 'c 'd 'e] :result :i64
     :body '(sum-five a b c d e)}]})

(def scalar-variant-boundary-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'identity :params ['value] :param-types [scalar-variant-type]
     :result scalar-variant-type :body 'value}
    {:name 'main :params ['value] :param-types [:i64] :result :i64
     :body (list 'variant-match scalar-variant-type
                 (list 'identity
                       (list 'variant-new scalar-variant-type :number 'value))
                 [[:number 'payload (list '+ 'payload 1)]
                  [:flag 'payload (list 'if 'payload 1 0)]])}]})

(def scalar-variant-result-kir
  {:format :kotoba.kir/v4
   :exports ['make]
   :functions
   [{:name 'make :params ['value] :param-types [:bool]
     :result scalar-variant-type
     :body (list 'variant-new scalar-variant-type :flag 'value)}]})

(def aggregate-variant-type
  [:variant :test/record-or-count
   [[:record scalar-record-type] [:count :i64]]])

(def aggregate-variant-boundary-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'identity :params ['value] :param-types [aggregate-variant-type]
     :result aggregate-variant-type :body 'value}
    {:name 'main :params [] :result :i64
     :body (list 'variant-match aggregate-variant-type
                 (list 'identity
                       (list 'variant-new aggregate-variant-type :record
                             (list 'record-new scalar-record-type 20 22)))
                 [[:record 'payload
                   (list '+
                         (list 'record-get scalar-record-type 'payload :a)
                         (list 'record-get scalar-record-type 'payload :b))]
                  [:count 'payload 'payload]])}]})

(def sealed-callable-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'add-two :params ['a 'b] :result :i64 :body '(+ a b)}
    {:name 'lambda-add-two :params ['a 'b] :result :i64
     :body '(add-two a b)}
    {:name 'invoke$arity2 :params ['closure 'a 'b] :result :i64
     :body '(if (= (pair-first closure) 0)
              (lambda-add-two a b)
              (quot 1 0))}
    {:name 'apply$arity2 :params ['closure 'arguments] :result :i64
     :body '(invoke$arity2 closure
                           (pair-first arguments)
                           (pair-first (pair-second arguments)))}
    {:name 'main :params [] :result :i64
     :body '(+ (invoke$arity2 (pair 0 0) 20 22)
               (apply$arity2 (pair 0 0) (pair 4 (pair 5 0))))}]})

(def scalar-record-boundary-kir
  {:format :kotoba.kir/v4
   :exports ['main]
   :functions
   [{:name 'identity :params ['value] :param-types [scalar-record-type]
     :result scalar-record-type :body 'value}
    {:name 'main :params ['value] :param-types [:i64] :result :i64
     :body (list 'record-get scalar-record-type
                 (list 'identity
                       (list 'record-new scalar-record-type 'value 9))
                 :a)}]})

(def scalar-record-result-kir
  {:format :kotoba.kir/v4
   :exports ['make]
   :functions
   [{:name 'make :params ['value] :param-types [:i64]
     :result scalar-record-type
     :body (list 'record-new scalar-record-type 'value 9)}]})

(def nested-record-type
  [:record :test/nested [[:value scalar-record-type] [:count :i64]]])

(def nested-record-result-kir
  {:format :kotoba.kir/v4
   :exports ['make]
   :functions
   [{:name 'make :params ['value] :param-types [:i64]
     :result nested-record-type
     :body (list 'record-new nested-record-type
                 (list 'record-new scalar-record-type 'value true)
                 2)}]})

(deftest kir-module-lowers-to-versioned-function-and-call-ir
  (is (machine/pilot-module? scalar-call-kir))
  (let [gmir (machine/lower-kir-module scalar-call-kir)
        call (first (filter #(= :gmir/call (:gmir/op %))
                            (get-in gmir [:gmir/functions 1 :gmir/instructions])))]
    (is (= 3 (:gmir/version gmir)))
    (is (= 'main (:gmir/entry gmir)))
    (is (= ['add-one 'main] (mapv :gmir/name (:gmir/functions gmir))))
    (is (= 'add-one (:gmir/callee call)))
    (is (= 1 (count (:gmir/arguments call))))
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)
            caller (second (:mc/functions mc))]
        (is (= 3 (:mc/version mc)) target)
        (is (= :call-live (:mc/frame-policy caller)) target)
        (is (= 1 (:mc/frame-slots caller)) target)
        (is (= 1 (count (filter #(= (keyword (name target) "spill-store")
                                     (:mc/encoding %))
                                (:mc/instructions caller)))) target)
        (is (= 1 (count (filter #(= (keyword (name target) "spill-load")
                                     (:mc/encoding %))
                                (:mc/instructions caller)))) target)
        (is (= 1 (count (filter #(= (keyword (name target) "call")
                                     (:mc/encoding %))
                                (:mc/instructions caller)))) target)))))

(deftest kir-call-with-control-flow-stays-on-the-call-live-frame
  (let [gmir (machine/lower-kir-module scalar-call-branch-kir)]
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (machine/compile-gmir target gmir)
            caller (second (:mc/functions mc))
            straight (second (:mc/functions
                              (machine/compile-gmir target
                                                    (machine/lower-kir-module
                                                     scalar-call-kir))))]
        (is (= :call-live (:mc/frame-policy caller)) target)
        (is (< (:mc/frame-slots caller) 6) target)
        (is (<= (:mc/frame-slots caller) (+ 2 (:mc/frame-slots straight)))
            (str target " does not inflate the frame to all-vreg because of one if"))
        (is (seq (:code (machine/compile-kir-module target scalar-call-branch-kir)))
            target)))))

(deftest sequential-call-crossings-share-one-native-frame-save
  (let [[a call-one ignored b call-two result] (mapv gmir/vreg (range 6))
        gmir {:gmir/version 3 :gmir/entry 'main
              :gmir/functions
              [{:gmir/name 'one :gmir/arity 0
                :gmir/instructions
                [{:gmir/op :gmir/constant :gmir/dst (gmir/vreg 20)
                  :gmir/value 1}
                 {:gmir/op :gmir/return :gmir/value (gmir/vreg 20)}]}
               {:gmir/name 'main :gmir/arity 0
                :gmir/instructions
                [{:gmir/op :gmir/label :gmir/id :test.label/entry}
                 {:gmir/op :gmir/constant :gmir/dst a :gmir/value 40}
                 {:gmir/op :gmir/call :gmir/dst call-one
                  :gmir/callee 'one :gmir/arguments []}
                 {:gmir/op :gmir/add :gmir/dst ignored
                  :gmir/left a :gmir/right call-one}
                 {:gmir/op :gmir/constant :gmir/dst b :gmir/value 50}
                 {:gmir/op :gmir/call :gmir/dst call-two
                  :gmir/callee 'one :gmir/arguments []}
                 {:gmir/op :gmir/add :gmir/dst result
                  :gmir/left b :gmir/right call-two}
                 {:gmir/op :gmir/return :gmir/value result}]}]}]
    (doseq [target mir/targets]
      (let [caller (second (:mc/functions (machine/compile-gmir target gmir)))
            instructions (:mc/instructions caller)]
        (is (= :call-live (:mc/frame-policy caller)) target)
        (is (= 1 (count (mir/saved-registers target instructions))) target)
        (is (not-any? #(contains? #{(keyword (name target) "spill-store")
                                   (keyword (name target) "spill-load")}
                                  (:mc/encoding %))
                      instructions) target)))))

(def ^:private loop-call-kir
  {:format :kotoba.kir/v4 :exports ['kernel]
   :functions
   [{:name 'id :params ['x] :result :i64 :body 'x}
    {:name 'kernel :params ['i 'acc] :result :i64
     :body '(if (= i 0)
              acc
              (kernel (- i 1) (+ acc (id 1))))}]})

(deftest loop-call-parameters-stay-in-registers-through-self-tail-reentry
  ;; This is the benchmark's exact control-flow shape after frontend `loop`
  ;; lowering: two parameters cross a real call and then feed a self tail edge.
  ;; A scratch-first entry plan used to back both parameters with frame slots,
  ;; adding two stores and two loads to every iteration.
  (let [gmir (machine/lower-kir-module loop-call-kir)]
    (doseq [target mir/targets]
      (let [function (->> (machine/compile-gmir target gmir)
                          :mc/functions
                          (filter #(= 'kernel (:mc/name %)))
                          first)
            spill-encodings #{(keyword (name target) "spill-store")
                              (keyword (name target) "spill-load")}]
        (is (= :call-live (:mc/frame-policy function)) target)
        (if (= :aarch64 target)
          (do
            (is (zero? (:mc/frame-slots function)) target)
            (is (not-any? #(contains? spill-encodings (:mc/encoding %))
                          (:mc/instructions function)) target))
          (do
            ;; The broader preserved-entry placement exposed an x86 host-call
            ;; execution regression downstream. Its prior, qualified plan
            ;; backs only the accumulator and remains explicit here.
            (is (= 1 (:mc/frame-slots function)) target)
            (is (= 2 (count (filter #(contains? spill-encodings (:mc/encoding %))
                                    (:mc/instructions function)))) target)))
        (if (= :aarch64 target)
          (do
            (is (= 1 (count (filter #(= :mc/reentry (:mc/op %))
                                    (:mc/instructions function)))) target)
            (is (= 1 (count (filter #(= :mc/recur (:mc/op %))
                                    (:mc/instructions function)))) target)
            (is (not-any? #(= :aarch64/tail-call (:mc/encoding %))
                          (:mc/instructions function)) target))
          (do
            (is (= 1 (count (filter #(= :x86-64/tail-call (:mc/encoding %))
                                    (:mc/instructions function)))) target)
            (is (not-any? #(contains? #{:mc/reentry :mc/recur} (:mc/op %))
                          (:mc/instructions function)) target)))))))

(deftest string-index-self-recur-updates-all-three-explicit-parameter-homes
  ;; Regression for the minimized stale-third-parameter failure: the new
  ;; position was already in ABI x2, so an encoder pattern looking only for
  ;; staging MOVs saw two moves and skipped the rewrite. The allocator's
  ;; explicit boundary now lets the unique-use ADD produce x21 directly.
  (let [kir {:format :kotoba.kir/v4 :exports ['main]
             :functions
             (string-index/augment-functions
              [{:name 'main :params [] :param-types [] :result :i64
                :body '(string-index-count (string-index-new))}])}
        helper (->> (machine/compile-gmir :aarch64
                                          (machine/lower-kir-module kir))
                    :mc/functions
                    (filter #(= string-index/find-name (:mc/name %))) first)
        instructions (:mc/instructions helper)
        boundary (first (filter #(= :mc/reentry (:mc/op %)) instructions))
        recur-index (first (keep-indexed #(when (= :mc/recur (:mc/op %2)) %1)
                                         instructions))]
    (is (= [:aarch64/x19 :aarch64/x20 :aarch64/x21]
           (:mc/parameters boundary)))
    (is (= {:mc/op :mc/instruction :mc/encoding :aarch64/add
            :mir/dst :aarch64/x21 :mir/left :aarch64/x21
            :mir/right :aarch64/x1}
           (nth instructions (dec recur-index))))
    (is (= (:mc/parameters boundary)
           (:mc/arguments (nth instructions recur-index))))
    (is (not-any? #(= :aarch64/tail-call (:mc/encoding %)) instructions))))

(deftest encoder-direct-reentry-label-is-fresh-against-admitted-labels
  (let [colliding (keyword "kotoba.native.internal.self-tail" "0.0")
        qualification-collision :kotoba.native.internal/self-tail.0.0
        module (fn [ordinary-label]
                 {:mc/version 3 :mc/target :aarch64 :mc/entry 'loop
                  :mc/functions
                  [{:mc/name 'loop :mc/arity 1 :mc/frame-slots 0
                    :mc/frame-policy :call-live
                    :mc/instructions
                    [{:mc/op :mc/instruction :mc/encoding :aarch64/argument
                      :mir/dst :aarch64/x0 :mir/index 0}
                     {:mc/op :mc/reentry :mc/parameters [:aarch64/x0]}
                     {:mc/op :mc/recur :mc/arguments [:aarch64/x0]}
                     (layout/label ordinary-label)
                     {:mc/op :mc/instruction :mc/encoding :aarch64/return
                      :mir/value :aarch64/x0}]}]})]
    (doseq [ordinary-label [colliding qualification-collision]]
      (let [encoded (machine/encode-mc-module (module ordinary-label))]
        (is (seq (:code encoded)) ordinary-label)
        (is (= {:offset 0 :length (count (:code encoded)) :arity 1}
               (get-in encoded [:exports 'loop])) ordinary-label)))))

(deftest tail-position-direct-calls-lower-to-terminal-non-linking-transfer
  (let [gmir (machine/lower-kir-module four-argument-call-kir)
        caller (second (:gmir/functions gmir))
        tail (peek (:gmir/instructions caller))]
    (is (= :gmir/tail-call (:gmir/op tail)))
    (is (= 'sum-four (:gmir/callee tail)))
    (doseq [target [:x86-64 :aarch64]]
      (let [mc-caller (second (:mc/functions (machine/compile-gmir target gmir)))
            encodings (mapv :mc/encoding (:mc/instructions mc-caller))]
        (is (= (keyword (name target) "tail-call") (peek encodings)) target)
        (is (not-any? #(= (keyword (name target) "call") %) encodings) target)))))

(deftest scalar-call-module-reaches-final-target-layout-deterministically
  (doseq [target [:x86-64 :aarch64]]
    (let [first-result (machine/compile-kir-module target scalar-call-kir)
          second-result (machine/compile-kir-module target scalar-call-kir)
          code (:code first-result)
          export (get-in first-result [:exports 'main])]
      (is (= first-result second-result) target)
      (is (seq code) target)
      (is (pos? (:offset export)) target)
      (is (pos? (:length export)) target)
      (is (= 1 (:arity export)) target)
      (is (if (= :x86-64 target)
            (some #{0xe8} code)
            (some #(= 0x94 (bit-and % 0xfc)) (take-nth 4 (drop 3 code))))
          (str target " contains its direct-call opcode")))))

(deftest scalar-variant-parameters-and-results-use-the-versioned-pair-boundary
  (doseq [kir [scalar-variant-boundary-kir scalar-variant-result-kir]]
    (is (machine/pilot-module? kir))
    (let [gmir (machine/lower-kir-module kir)
          instructions (mapcat :gmir/instructions (:gmir/functions gmir))]
      (is (some #(and (= :gmir/runtime-call (:gmir/op %))
                      (= :pair (:gmir/runtime %)))
                instructions))
      (doseq [target [:x86-64 :aarch64]]
        (let [compiled (machine/compile-kir-module target kir)]
          (is (seq (:code compiled)) target)
          (is (= 1 (get-in compiled [:exports (first (:exports kir)) :arity]))
              target)))))
  (testing "case order and payload family remain fail closed in the producer"
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/lower-kir-module
                  (assoc-in scalar-variant-boundary-kir [:functions 1 :body]
                            (list 'variant-match scalar-variant-type
                                  (list 'variant-new scalar-variant-type :number 1)
                                  [[:flag 'payload 0]
                                   [:number 'payload 'payload]])))))
    (is (not (machine/pilot-module?
              (assoc-in scalar-variant-result-kir [:functions 0 :result]
                        [:variant :test/text [[:text :string]]]))))))

(deftest aggregate-payload-variants-cross-calls-as-recursive-handles
  (is (aggregate-abi/aggregate-payload-variant-type? aggregate-variant-type))
  (is (machine/pilot-module? aggregate-variant-boundary-kir))
  (let [gmir (machine/lower-kir-module aggregate-variant-boundary-kir)
        runtime-ops (->> (:gmir/functions gmir)
                         (mapcat :gmir/instructions)
                         (keep :gmir/runtime)
                         set)]
    (is (every? runtime-ops [:pair :pair-first :pair-second]))
    (doseq [target [:x86-64 :aarch64]]
      (let [compiled (machine/compile-kir-module
                      target aggregate-variant-boundary-kir)]
        (is (seq (:code compiled)) target)
        (is (= 0 (get-in compiled [:exports 'main :arity])) target)))))

(deftest sealed-indirect-call-and-bounded-apply-remain-direct-machine-calls
  (is (machine/pilot-module? sealed-callable-kir))
  (let [gmir (machine/lower-kir-module sealed-callable-kir)
        instructions (mapcat :gmir/instructions (:gmir/functions gmir))
        calls (filter #(contains? #{:gmir/call :gmir/tail-call} (:gmir/op %))
                      instructions)]
    (is (seq calls))
    (is (every? symbol? (map :gmir/callee calls)))
    (is (not-any? #(contains? #{:gmir/indirect-call :gmir/call-address}
                               (:gmir/op %))
                  instructions))
    (doseq [target [:x86-64 :aarch64]]
      (let [compiled (machine/compile-kir-module target sealed-callable-kir)]
        (is (seq (:code compiled)) target)
        (is (= 0 (get-in compiled [:exports 'main :arity])) target)))))

(deftest scalar-record-parameters-and-results-use-the-versioned-pair-chain
  (doseq [kir [scalar-record-boundary-kir scalar-record-result-kir]]
    (is (machine/pilot-module? kir))
    (let [gmir (machine/lower-kir-module kir)
          instructions (mapcat :gmir/instructions (:gmir/functions gmir))]
      (is (some #(and (= :gmir/runtime-call (:gmir/op %))
                      (= :pair (:gmir/runtime %)))
                instructions))
      (doseq [target [:x86-64 :aarch64]]
        (let [compiled (machine/compile-kir-module target kir)]
          (is (seq (:code compiled)) target)
          (is (= 1 (get-in compiled [:exports (first (:exports kir)) :arity]))
              target)))))
  (is (machine/pilot-module? nested-record-result-kir))
  (doseq [target [:x86-64 :aarch64]]
    (is (seq (:code (machine/compile-kir-module
                     target nested-record-result-kir)))
        target)))

(deftest canonical-option-and-result-handles-are-native-words
  (doseq [type [:option-i64 :result-i64]]
    (is (machine/word-result-type? type) type))
  (let [instructions
        (get-in (machine/lower-kir-module
                 {:format :kotoba.kir/v4 :exports ['main]
                  :functions
                  [{:name 'main :params ['r]
                    :param-types [[:record :test/word
                                   [[:maybe [:option :i64]] [:text :string]]]]
                    :result :i64
                    :body '(record-get
                            [:record :test/word
                             [[:maybe [:option :i64]] [:text :string]]]
                            r :maybe)}]})
                [:gmir/functions 0 :gmir/instructions])]
    (is (some #(and (= :gmir/runtime-call (:gmir/op %))
                    (= :pair-first (:gmir/runtime %)))
              instructions))))

(deftest four-entry-arguments-reach-both-encoders-without-a-spill-frame
  (doseq [target [:x86-64 :aarch64]]
    (let [gmir (machine/lower-kir-module four-argument-call-kir)
          mc (machine/compile-gmir target gmir)
          [callee caller] (:mc/functions mc)
          argument-encoding (keyword (name target) "argument")
          spill-encodings #{(keyword (name target) "spill-store")
                            (keyword (name target) "spill-load")}
          expected-inputs (if (= :x86-64 target)
                            [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx]
                            [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3])]
      (is (= [:allocator :call-live]
             (mapv :mc/frame-policy [callee caller])) target)
      (is (= [0 0] (mapv :mc/frame-slots [callee caller])) target)
      (doseq [function [callee caller]]
        (is (= expected-inputs
               (mapv :mir/dst
                     (filter #(= argument-encoding (:mc/encoding %))
                             (:mc/instructions function))))
            [target (:mc/name function)])
        (is (not-any? #(contains? spill-encodings (:mc/encoding %))
                      (:mc/instructions function))
            [target (:mc/name function)]))
      (is (seq (:code (machine/compile-kir-module target four-argument-call-kir)))
          target))))

(deftest five-live-entry-arguments-encode-one-bounded-lazy-spill
  (with-scratch-tier-only
    (doseq [target [:x86-64 :aarch64]]
      (let [mc (->> five-argument-call-kir machine/lower-kir-module
                    (machine/compile-gmir target))
            [callee caller] (:mc/functions mc)
            spill-store (keyword (name target) "spill-store")
            spill-load (keyword (name target) "spill-load")
            compiled (machine/compile-kir-module target five-argument-call-kir)]
        (is (= [:allocator :call-live]
               (mapv :mc/frame-policy [callee caller])) target)
        (is (= [1 1] (mapv :mc/frame-slots [callee caller])) target)
        (doseq [function [callee caller]]
          (is (= 1 (count (filter #(= spill-store (:mc/encoding %))
                                  (:mc/instructions function))))
              [target (:mc/name function)])
          (is (= 1 (count (filter #(= spill-load (:mc/encoding %))
                                  (:mc/instructions function))))
              [target (:mc/name function)]))
        (is (= (if (= :x86-64 target) 114 68)
               (count (:code compiled))) target)))))

(deftest word-call-module-boundary-supports-multiple-exports-and-fails-closed
  (let [multi-export (assoc scalar-call-kir :exports ['main 'add-one])]
    (is (machine/pilot-module? multi-export))
    (doseq [target [:x86-64 :aarch64]]
      (is (= #{'main 'add-one}
             (set (keys (:exports (machine/compile-kir-module target multi-export))))))))
  (is (not (machine/pilot-module?
            (assoc-in scalar-call-kir [:functions 1 :body] '(missing x)))))
  (is (thrown? clojure.lang.ExceptionInfo
               (machine/lower-kir-module
                (assoc-in scalar-call-kir [:functions 1 :body] '(add-one x x)))))
  (is (= 3 (:gmir/version
            (machine/lower-kir-module
             (assoc-in scalar-call-kir [:functions 0 :result] :string)))))
  (is (= 3 (:gmir/version
            (machine/lower-kir-module
             (-> scalar-call-kir
                 (assoc-in [:functions 0 :result]
                           [:record :demo/value [[:value :i64]]])
                 (assoc-in [:functions 0 :body]
                           '(record-new [:record :demo/value [[:value :i64]]]
                                        x)))))))
  (let [too-deep
        (reduce (fn [field-type index]
                  [:record (keyword "demo" (str "level-" index))
                   [[:value field-type]]])
                :i64
                (range 33))]
    (is (thrown? clojure.lang.ExceptionInfo
                 (machine/lower-kir-module
                  (assoc-in scalar-call-kir [:functions 0 :result]
                            too-deep))))))

;; ── the callee-saved frame ───────────────────────────────────────────────────
;;
;; A frame that saves a callee-saved register and forgets to restore it is
;; silent at the point of the defect: the caller keeps running with a corrupted
;; register and the wrong number turns up somewhere else entirely. So assert the
;; two halves against each other rather than against a recorded byte string.

;; The window in which a target reaches the preserved tier is bounded on both
;; sides: below it the leaf tier still has room, above it the allocator gives up
;; and every value takes a stack slot. x86-64 offers four scratch, two leaf and
;; five preserved, so its window is seven to eleven live values; AArch64 offers
;; four, seven and eight, so its window is twelve to nineteen. The windows do
;; not overlap, and a single body cannot exercise both.

(def ^:private preserved-tier-body
  {:x86-64 '(let [a (+ (* n 3) 1) b (+ (* n 5) 2) c (+ (* n 7) 3) d (+ (* n 11) 4)
                  e (+ (* n 13) 5) f (+ (* n 17) 6) g (+ (* n 19) 7) h (+ (* n 23) 8)]
              (+ (+ (+ a b) (+ c d)) (+ (+ e f) (+ g h))))
   :aarch64 '(let [a (+ (* n 3) 1) b (+ (* n 5) 2) c (+ (* n 7) 3) d (+ (* n 11) 4)
                   e (+ (* n 13) 5) f (+ (* n 17) 6) g (+ (* n 19) 7) h (+ (* n 23) 8)
                   i (+ (* n 29) 9) j (+ (* n 31) 10) k (+ (* n 37) 11)
                   l (+ (* n 41) 12) m (+ (* n 43) 13) o (+ (* n 47) 14)]
               (+ (+ (+ (+ a b) (+ c d)) (+ (+ e f) (+ g h)))
                  (+ (+ (+ i j) (+ k l)) (+ m o))))})

(def ^:private scratch-tier-body '(+ (* n 3) 1))

(def ^:private x86-push-code
  {:x86-64/rbx [0x53] :x86-64/r12 [0x41 0x54] :x86-64/r13 [0x41 0x55]
   :x86-64/r14 [0x41 0x56] :x86-64/r15 [0x41 0x57]})

(def ^:private x86-pop-code
  {:x86-64/rbx [0x5b] :x86-64/r12 [0x41 0x5c] :x86-64/r13 [0x41 0x5d]
   :x86-64/r14 [0x41 0x5e] :x86-64/r15 [0x41 0x5f]})

(defn- allocated-instructions [target body]
  (:mir/instructions
   (mir/allocate-registers
    (mir/select-target target (machine/lower-kir-expression '[n] body)))))

(deftest x86-64-frame-saves-and-restores-exactly-the-preserved-registers-it-uses
  (let [body (get preserved-tier-body :x86-64)
        saved (mir/saved-registers :x86-64 (allocated-instructions :x86-64 body))
        code (mapv #(bit-and % 0xff)
                   (machine/compile-expression :x86-64 '[n] body))
        ;; An odd number of pushes would leave RSP misaligned, so the frame
        ;; pre-indexes the stack by eight. That padding sits above the pushes,
        ;; which is why it comes first here and last on the way out.
        pad (if (odd? (count saved)) [0x48 0x81 0xec 0x08 0x00 0x00 0x00] [])
        unpad (if (odd? (count saved)) [0x48 0x81 0xc4 0x08 0x00 0x00 0x00] [])
        pushes (vec (mapcat x86-push-code saved))
        pops (vec (mapcat x86-pop-code (reverse saved)))]
    (is (seq saved) "this body has to reach the preserved tier for the rest to mean anything")
    (is (= (into (vec pad) pushes)
           (subvec code 0 (+ (count pad) (count pushes))))
        "the prologue pushes exactly the preserved registers the body names, in pool order")
    (let [expected (-> pops (into unpad) (conj 0xc3))]
      (is (= expected (subvec code (- (count code) (count expected))))
          "and the epilogue undoes exactly that, in reverse, before returning"))))

(deftest a-body-inside-the-scratch-tier-carries-no-frame-save
  (doseq [target mir/targets]
    (let [saved (mir/saved-registers
                 target (allocated-instructions target scratch-tier-body))]
      (is (empty? saved) target))))

(deftest saved-registers-follows-the-body-rather-than-a-recorded-list
  ;; The narrow body and the wide one differ only in how many values are live;
  ;; if the save set were a constant, or keyed off the target alone, these two
  ;; would agree.
  (doseq [target mir/targets]
    (let [narrow (mir/saved-registers
                  target (allocated-instructions target scratch-tier-body))
          wide (mir/saved-registers
                target (allocated-instructions target (get preserved-tier-body target)))]
      (is (not= narrow wide) target)
      (is (every? (set (get mir/preserved-registers target)) wide) target)
      (is (= wide (filterv (set wide) (get mir/preserved-registers target)))
          "reported in pool order, so save-in-order/restore-in-reverse needs no sort"))))

(defn- a64-code [register] (parse-long (subs (name register) 1)))

(defn- a64-words [bytes]
  (mapv (fn [[a b c d]] (+ a (* b 256) (* c 65536) (* d 16777216)))
        (partition 4 (mapv #(bit-and % 0xff) bytes))))

(deftest aarch64-frame-saves-and-restores-exactly-the-preserved-registers-it-uses
  (let [body (get preserved-tier-body :aarch64)
        saved (mir/saved-registers :aarch64 (allocated-instructions :aarch64 body))
        words (a64-words (machine/compile-expression :aarch64 '[n] body))
        ;; SP has to stay 16-byte aligned, so registers go down in pairs and an
        ;; odd one spends the same sixteen bytes on its own.
        pairs (partition-all 2 saved)
        save (mapv (fn [[a b]]
                     (if b
                       (bit-or 0xa9bf0000 (bit-shift-left (a64-code b) 10)
                               (bit-shift-left 31 5) (a64-code a))
                       (bit-or 0xf81f0c00 (bit-shift-left 31 5) (a64-code a))))
                   pairs)
        restore (mapv (fn [[a b]]
                        (if b
                          (bit-or 0xa8c10000 (bit-shift-left (a64-code b) 10)
                                  (bit-shift-left 31 5) (a64-code a))
                          (bit-or 0xf8410400 (bit-shift-left 31 5) (a64-code a))))
                      (reverse pairs))]
    (is (seq saved) "this body has to reach the preserved tier for the rest to mean anything")
    (is (= save (subvec words 0 (count save)))
        "the prologue saves exactly the preserved registers the body names, in pool order")
    (let [expected (conj restore 0xd65f03c0)]
      (is (= expected (subvec words (- (count words) (count expected))))
          "and the epilogue restores exactly those, in reverse, before returning"))))

(def ^:private a64-fuel-ldr 0xf94004f0)
(def ^:private x86-fuel-cmp [0x49 0x83 0x79 0x08 0x00])

(deftest production-acyclic-leaf-omits-entry-fuel
  ;; emit-program used to prefix every function. The 100k C harness then paid
  ;; a load, a decrement, and a store on every kernel_wide call. An acyclic
  ;; leaf cannot re-enter guest code; fuel does not bound it. Break: put the
  ;; prefix back on every name and this assertion is false.
  (let [kir {:format :kotoba.kir/v4 :exports ['kernel]
             :functions [{:name 'kernel :params ['n] :result :i64
                          :body '(+ (* n 48271) 1)}]}
        arm (vec (:code (arm/emit-program kir)))
        x86-code (vec (:code (x86/emit-program kir)))]
    (is (not= a64-fuel-ldr (first (a64-le-words arm)))
        "AArch64 leaf does not start with ldr x16,[x7,#8]")
    (is (not= x86-fuel-cmp (subvec x86-code 0 5))
        "x86-64 leaf does not start with cmp qword [r9+8],0")
    (is (empty? (machine/entry-fuel-prefixes kir (constantly [:fuel]))))))

(deftest production-self-call-keeps-entry-fuel
  ;; The bound is for functions that can run unbounded work. Break: skip the
  ;; prefix for every name and a 512-deep countdown no longer traps.
  (let [kir {:format :kotoba.kir/v4 :exports ['down]
             :functions [{:name 'down :params ['n] :result :i64
                          :body '(if (< n 1) n (down (- n 1)))}]}
        arm (vec (:code (arm/emit-program kir)))
        x86-code (vec (:code (x86/emit-program kir)))
        prefixes (machine/entry-fuel-prefixes kir (constantly [:fuel]))]
    (is (= a64-fuel-ldr (first (a64-le-words arm))))
    (is (= x86-fuel-cmp (subvec x86-code 0 5)))
    (is (= {'down [:fuel]} prefixes))))

(defn- subvector-count [haystack needle]
  (count (filter #(= needle (vec %))
                 (partition (count needle) 1 haystack))))

(deftest production-self-tail-call-reuses-one-frame-and-recharges-fuel
  ;; `loop/recur` lowers to a self tail call. Releasing the frame and branching
  ;; to the public function label rebuilt the complete call-live frame on every
  ;; iteration. The optimized edge enters after the one-time prologue, but it
  ;; carries its own fuel charge; dropping that charge would make this an
  ;; unbounded native loop.
  (let [kir {:format :kotoba.kir/v4 :exports ['down]
             :functions [{:name 'down :params ['n] :result :i64
                          :body '(if (< n 1) n (down (- n 1)))}]}
        arm-code (vec (:code (arm/emit-program kir)))
        arm-words (a64-le-words arm-code)
        x86-code (vec (:code (x86/emit-program kir)))
        x86-sub-frame [0x48 0x81 0xec 0x08 0x00 0x00 0x00]
        x86-add-frame [0x48 0x81 0xc4 0x08 0x00 0x00 0x00]]
    (testing "AArch64"
      (is (= 2 (count (filter #{a64-fuel-ldr} arm-words)))
          "entry and self-tail edge each contain one fuel charge")
      (is (= 1 (count (filter #{0xa9bf7bfd} arm-words)))
          "FP/LR prologue is emitted once")
      (is (= 1 (count (filter #{0xa8c17bfd} arm-words)))
          "only the returning arm tears the frame down"))
    (testing "x86-64 remains on its independently qualified teardown path"
      ;; Reusing the MIR frame is not yet safe for x86 helpers containing host
      ;; callbacks. Keep its prior tail teardown until that ABI interaction has
      ;; an execution proof; the AArch64 benchmark optimization must not widen
      ;; its claim across an unqualified ISA.
      (is (= 1 (subvector-count x86-code x86-fuel-cmp))
          "the public entry prefix is reached again after tail teardown")
      (is (= 1 (subvector-count x86-code x86-sub-frame))
          "one static call-live prologue remains")
      (is (= 2 (subvector-count x86-code x86-add-frame))
          "return and self-tail edges each release the frame"))))

(deftest production-loop-call-uses-direct-aarch64-cbnz
  (let [module (machine/compile-gmir :aarch64
                                     (machine/lower-kir-module loop-call-kir))
        loop-instructions (->> (:mc/functions module)
                               (filter #(= 'kernel (:mc/name %)))
                               first :mc/instructions)
        arm-code (:code (arm/emit-program loop-call-kir))
        words (a64-le-words arm-code)
        x86-code (vec (:code (x86/emit-program loop-call-kir)))
        cbnz-x0? #(= 0xb5000000
                      (bit-and % 0xff00001f))
        encoded (#'kotoba.native.machine-ir/encode-layout-branch
                 (layout/relative-branch :aarch64/cbnz-imm19
                                         :test.label/continue [19])
                 8)]
    (is (= [0x53 0x00 0x00 0xb5] encoded)
        "CBNZ x19,+8 is 0xb5000053 in little-endian bytes")
    (is (= 1 (count (filter cbnz-x0? words)))
        "equal(i,0) followed by branch-zero emits one CBNZ i")
    (is (= 1 (count (filter #(= :mc/branch-nonzero (:mc/op %))
                            loop-instructions))))
    (is (not-any? #(and (= :aarch64/constant (:mc/encoding %))
                        (zero? (:mir/value %)))
                  loop-instructions)
        "the uniquely consumed virtual zero definition is absent from MC")
    (is (not-any? #(contains? #{:aarch64/equal :mc/branch-zero}
                              (or (:mc/encoding %) (:mc/op %)))
                  loop-instructions)
        "equality materialization and its inverted branch are absent from MC")
    (is (not-any? #{0xeb01001f 0x9a9f17e2} words)
        "the former CMP x0,x1 and CSET x2,eq pair is absent")
    (is (= 2 (count (filter #{a64-fuel-ldr} words)))
        "entry and self-tail re-entry still each charge fuel")
    (is (pos? (subvector-count x86-code [0x0f 0x84]))
        "x86 retains its canonical TEST/JZ branch path")
    ;; Virtual SSA ownership proves both definitions dead, removing MOV zero as
    ;; well as CMP+CSET. This pins a 4-to-1 production reduction.
    (is (= 27 (count words))
        "one safe direct-home producer removes one more hot-edge word; the static module is 27 words")))


(defn- lcg-rounds-form
  "N rounds of `x <- (x*48271 + 1) mod 2147483647`, the shape of
  `bench/runtime-comparison/kernel.kotoba`. Each round contributes two constant
  multiplies with a fresh left operand, so the GVN map grows by two per round
  and shares nothing."
  [n]
  (let [bindings
        (vec (mapcat (fn [i]
                       (let [v (symbol (str "v" i))
                             x (symbol (str "x" i))
                             prev (if (= i 1) 'n (symbol (str "x" (dec i))))]
                         [v (list '+ (list '* prev 48271) 1)
                          x (list '- v (list '* (list 'quot v 2147483647) 2147483647))]))
                     (range 1 (inc n))))]
    (list 'let bindings (symbol (str "x" n)))))

(deftest gvn-constant-multiply-keys-carry-no-raw-i64
  ;; ClojureScript represents an i64 as a JS BigInt and `hash` on a BigInt
  ;; throws `Cannot create property 'closure_uid_…' on bigint`, so the constant
  ;; inside a GVN map key must not be the raw value. Below nine entries the map
  ;; is a PersistentArrayMap and compares with `=` without ever hashing, which
  ;; is why the failure appeared only past a size: measured 2026-08-18 with this
  ;; repository pinned at d4b050ae, four rounds compiled under nbb and five
  ;; answered `internal compiler error`, while both compiled on the JVM.
  ;;
  ;; A JVM Long hashes fine, so this assertion can only pin the SHAPE of the
  ;; key. The host-level gate is amu's JDK-free native conformance, which
  ;; compiles the five-round form above through the plain-Node front.
  (testing "the key component is a string on every host"
    (is (string? (#'machine/const-key 48271)))
    (is (= (#'machine/const-key 48271) (#'machine/const-key 48271)))
    (is (not= (#'machine/const-key 48271) (#'machine/const-key 48272))))
  (testing "a kernel past the array-map boundary still lowers and encodes"
    (doseq [rounds [4 5 8]]
      (let [form (lcg-rounds-form rounds)]
        (is (machine/pilot-expression? '[n] form) rounds)
        (is (seq (machine/compile-expression :x86-64 '[n] form)) rounds)
        (is (seq (machine/compile-expression :aarch64 '[n] form)) rounds)))))

(deftest gvn-still-shares-a-repeated-constant-multiply
  ;; The stringified key must not stop the pass doing its job: two multiplies of
  ;; the same register by the same constant remain one instruction.
  (let [form '(let [p (* n 48271) q (* n 48271)] (+ p q))
        operations (mapv :gmir/op (:gmir/instructions
                                   (machine/lower-kir-expression '[n] form)))]
    (is (= 1 (count (filter #{:gmir/multiply} operations)))
        "the second product is aliased to the first")))

;; ---------------------------------------------------------------------------
;; kernel-try-lock-u32 / kernel-unlock-u32 (amu#625)
;; ---------------------------------------------------------------------------

;; These two are the only atomic read-modify-write in the native profile, and
;; both encodings are written by hand here rather than by an assembler, so the
;; instruction words are pinned as literals. That is not belt-and-braces: the
;; STLXR word was wrong on the first attempt -- 0x8811fe00 hand-carried to
;; 0x8910fe00 -- and it assembled, laid out, and emitted a program of exactly
;; the right length. Only a disassembler said "invalid". A length check or a
;; round-trip through our own encoder would both have passed.
;;
;; The bytes below were taken from clang (`ldaxr w17, [x16]` -> 885ffe11,
;; `stlxr w17, w3, [x16]` -> 8811fe03, `clrex` -> d5033f5f) and from an
;; independent disassembly of the emitted program, not from re-running the
;; arithmetic in `machine-ir` a second time.

(defn- lock-program [body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'main :params '[b l i] :body body}]})

(defn- contains-subvector? [haystack needle]
  (boolean (some #(= needle (subvec (vec haystack) % (+ % (count needle))))
                 (range (inc (- (count haystack) (count needle)))))))

(deftest x86-lock-is-one-lock-cmpxchg-with-rax-saved-around-it
  (let [code (fn [body] (vec (:code (x86/emit-program (lock-program body)))))
        acquire (code '(kernel-try-lock-u32 b l i))
        release (code '(kernel-unlock-u32 b l i))]
    (testing "the atomic itself: lock cmpxchg dword [r11], r10d"
      (doseq [[label bytes] [["acquire" acquire] ["release" release]]]
        (is (contains-subvector? bytes [0xf0 0x45 0x0f 0xb1 0x13])
            (str label " must carry the LOCK-prefixed CMPXCHG"))))
    (testing "RAX is the fixed comparand, so it is pushed and popped"
      (is (contains-subvector? acquire [0x50]) "push rax")
      (is (contains-subvector? acquire [0x58]) "pop rax")
      (is (< (.indexOf ^java.util.List acquire (int 0x50))
             (.indexOf ^java.util.List acquire (int 0x58)))
          "the push precedes the pop"))
    (testing "the comparand and replacement are the operation's, not the guest's"
      ;; mov eax, imm32 / mov r10d, imm32
      (is (contains-subvector? acquire [0xb8 0x00 0x00 0x00 0x00]) "acquire expects 0")
      (is (contains-subvector? acquire [0x41 0xba 0x01 0x00 0x00 0x00]) "acquire writes 1")
      (is (contains-subvector? release [0xb8 0x01 0x00 0x00 0x00]) "release expects 1")
      (is (contains-subvector? release [0x41 0xba 0x00 0x00 0x00 0x00]) "release writes 0"))
    (testing "acquire and release differ only in those two immediates"
      (is (= (count acquire) (count release)))
      (is (= 2 (count (remove zero? (map #(if (= %1 %2) 0 1) acquire release))))
          "exactly two bytes differ, and they are the two constants"))))

(deftest aarch64-lock-is-the-exclusive-monitor-pair-with-a-retry
  (let [code (fn [body] (vec (:code (arm/emit-program (lock-program body)))))
        acquire (code '(kernel-try-lock-u32 b l i))
        release (code '(kernel-unlock-u32 b l i))
        word (fn [w] [(bit-and w 0xff) (bit-and (bit-shift-right w 8) 0xff)
                      (bit-and (bit-shift-right w 16) 0xff)
                      (bit-and (bit-shift-right w 24) 0xff)])]
    (testing "LDAXR/STLXR, and CLREX on the path that loses the race"
      (doseq [[label bytes] [["acquire" acquire] ["release" release]]]
        (is (contains-subvector? bytes (word 0x885ffe11))
            (str label " must LDAXR w17 from [x16]"))
        (is (contains-subvector? bytes (word 0x8811fe03))
            (str label " must STLXR w17, w3, [x16] -- 0x8910fe03 decodes as nothing"))
        (is (contains-subvector? bytes (word 0xd5033f5f))
            (str label " must CLREX rather than leave the monitor set"))))
    (testing "a failed store retries, which means a backward branch"
      ;; B.NE with a negative displacement: the top byte of the word is 0x54
      ;; and the imm19 field is all ones at the high end.
      (is (contains-subvector? acquire (word 0x54ffff41))
            "the store-failed branch must target the LDAXR, not fall through"))
    (testing "the comparand is the operation's"
      (is (contains-subvector? acquire (word 0xf100023f)) "acquire compares against 0")
      (is (contains-subvector? release (word 0xf100063f)) "release compares against 1"))))
