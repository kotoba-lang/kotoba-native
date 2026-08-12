(ns kotoba.native.machine-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.native.aggregate-abi :as aggregate-abi]
            [kotoba.native.machine-ir :as machine]
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
    (is (= 8 (count (encode -281470681808896)))
        "MOVN wins when most lanes are all ones")
    (is (= 16 (count (encode 0x0001000200030004)))
        "four distinct non-zero lanes still require four words"))
  (is (= 16 (count (#'machine/a64-constant-fixed :aarch64/x0 1)))
      "fixed-layout sites retain their reserved width"))

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

(deftest exhausted-register-profile-encodes-bounded-spills-for-both-isas
  (let [x86-mc (machine/compile-gmir :x86-64 spill-program)
        arm-mc (machine/compile-gmir :aarch64 spill-program)
        x86 (machine/encode-mc x86-mc)
        arm (machine/encode-mc arm-mc)]
    (is (= 11 (:mc/frame-slots x86-mc)))
    (is (= 11 (:mc/frame-slots arm-mc)))
    (doseq [mc [x86-mc arm-mc]]
      (is (some #(= "spill-store" (some-> % :mc/encoding name))
                (:mc/instructions mc)))
      (is (some #(= "spill-load" (some-> % :mc/encoding name))
                (:mc/instructions mc))))
    (is (= [0x48 0x81 0xec 0x60 0x00 0x00 0x00]
           (subvec x86 0 7)))
    (is (= [0x48 0x81 0xc4 0x60 0x00 0x00 0x00 0xc3]
           (subvec x86 (- (count x86) 8))))
    (is (= [0xc0 0x03 0x5f 0xd6]
           (subvec arm (- (count arm) 4))))
    (is (= [0xff 0x83 0x01 0xd1]
           (subvec arm 0 4)))
    (is (= [0xff 0x83 0x01 0x91 0xc0 0x03 0x5f 0xd6]
           (subvec arm (- (count arm) 8))))))

(deftest kir-expression-slice-encodes-final-bytes-for-both-isas
  (is (= [0x48 0x89 0xf8             ; mov rax,rdi
          0x48 0x89 0xf1             ; mov rcx,rsi
          0x48 0x89 0xc2             ; mov rdx,rax
          0x48 0x01 0xca             ; add rdx,rcx
          0x48 0x89 0xd0 0xc3]       ; mov rax,rdx; ret
         (machine/compile-expression :x86-64 ['a 'b] '(+ a b))))
  (is (= [0x02 0x00 0x01 0x8b       ; add x2,x0,x1
          0xe0 0x03 0x02 0xaa       ; mov x0,x2
          0xc0 0x03 0x5f 0xd6]      ; ret
         (machine/compile-expression :aarch64 ['a 'b] '(+ a b)))))

(deftest recursive-i64-arithmetic-reaches-final-bytes-for-both-isas
  (doseq [form ['(- a) '(- a b) '(* a b) '(quot a b)
                '(bit-and a b) '(bit-or a b) '(bit-xor a b)
                '(+ (* a b) (- a b)) '(+ a b 3 4)
                '(bit-xor a b 3 4)]]
    (is (seq (machine/compile-expression :x86-64 ['a 'b] form)) form)
    (is (seq (machine/compile-expression :aarch64 ['a 'b] form)) form))
  (is (= [0x02 0x00 0x01 0xcb 0xe0 0x03 0x02 0xaa 0xc0 0x03 0x5f 0xd6]
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
          :configure-page-fault-recovery [0x4c 0x89 0x14 0x25 0x00 0xc1 0x10 0x00]]
         [[] '(kernel-double-fault-handler-address) :double-fault-handler-address
          [0x4d 0x8d 0x7e 0xd0 0x4d 0x39 0xfa]]
         [['a 'b] '(kernel-configure-double-fault-ist a b)
          :configure-double-fault-ist [0x4c 0x89 0x14 0x25 0x80 0xc1 0x10 0x00]]
         [['a 'b] '(kernel-load-gdt-tss a b) :load-gdt-tss
          [0x41 0x0f 0x01 0x12]]
         [['a 'b] '(kernel-load-idt a b) :load-idt [0x41 0x0f 0x01 0x1a]]
         [[] '(kernel-probe-guard-write) :probe-guard-write
          [0xc6 0x04 0x25 0x00 0x00 0x10 0x00 0x00]]
         [[] '(kernel-probe-text-write) :probe-text-write
          [0xc6 0x04 0x25 0x00 0x10 0x10 0x00 0x00]]
         [[] '(kernel-probe-nx-execute) :probe-nx-execute
          [0x49 0xba 0x00 0xc0 0x10 0x00 0x00 0x00 0x00 0x00]]
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
  (is (= [0x1f 0x00 0x01 0xeb 0xe2 0xa7 0x9f 0x9a
          0xe0 0x03 0x02 0xaa 0xc0 0x03 0x5f 0xd6]
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
    (is (= [0x0f 0x84 0x0e 0x00 0x00 0x00] (subvec x86 6 12))
        "x86 jz skips the selected then arm using next-PC rel32")
    (is (= [0x80 0x00 0x00 0xb4] (subvec arm 0 4))
        "AArch64 cbz x0 reaches the final else label at +16 bytes")
    (is (= 40 (count x86)))
    (is (= 28 (count arm)))))

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
        (is (= (if (= :x86-64 target) 3 2)
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
             (count (:code compiled))) target))))

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
