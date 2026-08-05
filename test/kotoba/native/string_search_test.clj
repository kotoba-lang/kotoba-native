(ns kotoba.native.string-search-test
  "`string-contains?` / `string-replace-all` on both native ISAs.

  Two things have to be true and they are proved separately.

  **The rewrite computes the right answer.** Every row below is run TWICE
  through `kotoba.kir/execute`: once as the operation itself, which the
  reference interpreter implements directly, and once as the rewrite the
  backends emit. The expected value is never written down -- the oracle
  produces it -- so a row cannot be passed by an implementation and an
  expectation being wrong in the same direction. This is a byte-search, which
  is the classic place a wrong implementation returns a plausible answer, so
  the table is built out of near misses: a needle at offset 0, a needle
  touching the last byte, a needle absent but sharing a prefix with every
  window, a needle longer than the haystack, overlapping occurrences, a
  replacement that contains the needle, and multi-byte UTF-8 on both sides.

  **Both backends emit it, identically shaped.** `emit-program` of a program
  that uses the operation is asserted to produce EXACTLY the bytes of the
  program with the rewrite already written out and the helpers already
  declared -- so this is a rewrite into code both backends already emitted,
  not a new encoding. Per ISA, on both ISAs.

  Machine-code EXECUTION is not here: this repository has no loader
  (`tools/kexe_loader.c` belongs to kotoba-lang/compiler), as
  `kotoba.native.isa-parity-test` also records. The rows executed as real
  processes on both ISAs are reproduced in `docs/adr/0002-*`."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.kir :as ir]
            [kotoba.native.aarch64 :as arm]
            [kotoba.native.string-search :as search]
            [kotoba.native.x86-64 :as x86]))

(def ^:private backends [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]])

(defn- program
  "A one-function KIR module, with the search helpers injected exactly as
  `emit-program` injects them."
  [result body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions (search/augment-functions
               [{:name 'main :params [] :result result :body body}])})

(defn- rewritten
  "The same module with `main`'s body replaced by the rewrite `emit-expr`
  performs for a top-level occurrence -- i.e. what the backends actually
  emit, written out."
  [result body lowered]
  (let [functions (:functions (program result body))]
    {:format :kotoba.kir/v4 :exports ['main]
     :functions (into [(assoc (first functions) :body lowered)] (rest functions))}))

;; Interpreter fuel is raised well above the qualification loader's 512 so that
;; the ORACLE comparison is about semantics only. The loader's budget is a
;; property of that host, and it is what bounds how long a haystack these rows
;; may use when they are run as real processes; see the ADR.
(def ^:private interpreter-fuel 1000000)

(defn- run [module] (ir/execute module 'main [] {:fuel interpreter-fuel}))

;; ---------------------------------------------------------------------------
;; string-contains?
;; ---------------------------------------------------------------------------

(def ^:private contains-rows
  [["needle at the very start" "abcdef" "abc"]
   ["needle at the very end" "abcdef" "def"]
   ["needle in the middle" "abcdef" "cd"]
   ["needle is the whole haystack" "abc" "abc"]
   ["single-byte needle, single-byte haystack" "a" "a"]
   ["absent" "abcdef" "xyz"]
   ;; Every window of length 3 in "abcde" shares two bytes with "cdf". An
   ;; implementation that stops comparing early, or that compares only the
   ;; first byte, says yes here.
   ["absent, but a window shares a prefix with it" "abcde" "cdf"]
   ["absent, differing only in the last byte" "abcd" "abce"]
   ["needle longer than the haystack" "ab" "abcd"]
   ["needle one byte longer than the haystack" "abc" "abcd"]
   ["empty haystack" "" "a"]
   ["two occurrences, the first at offset 0" "abab" "ab"]
   ["two occurrences, neither at offset 0" "xabxab" "ab"]
   ["overlapping occurrences" "aaa" "aa"]
   ;; A byte-indexed scan asks for `(string-substring h 0 2)` here, and 2
   ;; splits the first code point, so it traps instead of answering.
   ["ASCII needle against a 3-byte-per-code-point haystack" "日本語" "ab"]
   ["multi-byte needle inside a multi-byte haystack" "日本語" "本語"]
   ["multi-byte needle at the start" "日本語" "日"]
   ["multi-byte needle at the end" "日本語" "語"]
   ["multi-byte needle absent, same code-point count" "日本語" "日語"]
   ["mixed-width haystack" "aé日b" "é日"]
   ["mixed-width haystack, needle absent" "aé日b" "é語"]
   ;; A 4-byte code point: the width derivation's last branch.
   ["astral-plane needle" "a𝄞b" "𝄞"]
   ["astral-plane haystack, ASCII needle absent" "𝄞𝄞" "a"]])

(deftest string-contains-agrees-with-the-reference-interpreter
  (doseq [[why haystack needle] contains-rows]
    (testing why
      (let [op (list 'string-contains? haystack needle)]
        (is (= (run (program :i64 op))
               (run (rewritten :i64 op (search/lower-contains [haystack needle]))))
            (str "the rewrite must answer what `string-contains?` answers: "
                 (pr-str haystack) " / " (pr-str needle)))))))

(deftest string-contains-is-emitted-as-the-written-out-rewrite-on-both-isas
  (doseq [[label emit] backends]
    (testing label
      (doseq [[why haystack needle] contains-rows]
        (let [op (list 'string-contains? haystack needle)
              emitted (:code (emit (program :i64 op)))]
          (is (seq emitted) why)
          (is (= emitted
                 (:code (emit (rewritten :i64 op (search/lower-contains [haystack needle])))))
              (str why " must emit exactly the written-out rewrite")))))))

;; ---------------------------------------------------------------------------
;; string-replace-all
;; ---------------------------------------------------------------------------

(def ^:private replace-rows
  [["one occurrence in the middle" "a-b" "-" "+"]
   ["at the very start" "-ab" "-" "+"]
   ["at the very end" "ab-" "-" "+"]
   ["two occurrences" "a,b,c" "," ";"]
   ["adjacent occurrences" "--" "-" "+"]
   ["absent" "abc" "x" "y"]
   ["needle longer than the haystack" "ab" "abc" "z"]
   ["empty haystack" "" "a" "b"]
   ["needle is the whole haystack" "abc" "abc" "z"]
   ;; A rewrite that rescanned its own output would either loop until it ran
   ;; out of fuel or return "xaaax"; `clojure.string/replace` returns "xaax".
   ["the replacement contains the needle" "xax" "a" "aa"]
   ["the replacement is the needle doubled" "a.b" "." ".."]
   ["the replacement is the needle" "a-b" "-" "-"]
   ["replacement shorter than the needle" "a--b--c" "--" "-"]
   ["replacement longer than the needle" "a-b" "-" "==="]
   ["empty replacement" "a-b" "-" ""]
   ;; Non-overlapping and left to right: "ba", not "b" and not "ab".
   ["overlapping candidates" "aaa" "aa" "b"]
   ["overlapping candidates, four wide" "aaaa" "aa" "b"]
   ["multi-byte needle" "日本語" "本" "X"]
   ["multi-byte replacement" "a-b" "-" "日"]
   ["multi-byte needle and replacement" "日本語" "本" "語"]
   ["astral-plane needle" "a𝄞b" "𝄞" "x"]
   ["mixed widths throughout" "aé日b-é" "é" "𝄞"]])

(deftest string-replace-all-agrees-with-the-reference-interpreter
  (doseq [[why subject needle replacement] replace-rows]
    (testing why
      (let [op (list 'string-replace-all subject needle replacement)]
        (is (= (run (program :string op))
               (run (rewritten :string op
                               (search/lower-replace-all [subject needle replacement]))))
            (str "the rewrite must answer what `string-replace-all` answers: "
                 (pr-str subject) " / " (pr-str needle) " / " (pr-str replacement)))))))

(deftest string-replace-all-is-emitted-as-the-written-out-rewrite-on-both-isas
  (doseq [[label emit] backends]
    (testing label
      (doseq [[why subject needle replacement] replace-rows]
        (let [op (list 'string-replace-all subject needle replacement)
              emitted (:code (emit (program :string op)))]
          (is (seq emitted) why)
          (is (= emitted
                 (:code (emit (rewritten :string op
                                         (search/lower-replace-all
                                          [subject needle replacement])))))
              (str why " must emit exactly the written-out rewrite")))))))

;; ---------------------------------------------------------------------------
;; The empty needle
;; ---------------------------------------------------------------------------

(deftest an-empty-needle-traps-in-the-rewrite-because-it-traps-in-the-oracle
  ;; `kotoba.kir` traps rather than answering, so the rewrite must not answer
  ;; either. It reaches a trap through `(string-code-point-at n 0)`, which is
  ;; out of bounds exactly when the needle is empty -- no new trap encoding in
  ;; either backend.
  (doseq [[why op lowered result]
          [["contains?" '(string-contains? "abc" "")
            (search/lower-contains ["abc" ""]) :i64]
           ["contains?, empty haystack too" '(string-contains? "" "")
            (search/lower-contains ["" ""]) :i64]
           ["replace-all" '(string-replace-all "abc" "" "x")
            (search/lower-replace-all ["abc" "" "x"]) :string]]]
    (testing why
      (is (thrown? clojure.lang.ExceptionInfo (run (program result op)))
          "the oracle traps")
      (is (thrown? clojure.lang.ExceptionInfo (run (rewritten result op lowered)))
          "so the rewrite must trap")))
  ;; And it still reaches machine code on both backends: the trap is a runtime
  ;; outcome, not an emission-time refusal.
  (doseq [[label emit] backends]
    (testing label
      (is (seq (:code (emit (program :i64 '(string-contains? "abc" "")))))))))

;; ---------------------------------------------------------------------------
;; Injection discipline
;; ---------------------------------------------------------------------------

(deftest a-program-that-searches-nothing-is-left-alone
  ;; The helpers are what would be prepended to the code image, so a program
  ;; that never searches must come back identical -- otherwise this change
  ;; would have moved the emission of every existing program.
  (let [functions [{:name 'main :params '[a] :body '(+ a 1)}]]
    (is (identical? functions (search/augment-functions functions))
        "not merely equal: the same collection, so nothing can have been added")
    ;; The other string operations must not drag the helpers in either --
    ;; only the two SEARCH operations do.
    (doseq [body '[(string-byte-length a)
                   (string-concat a "x")
                   (string-substring a 0 1)
                   (string-code-point-at a 0)
                   (keyword-name a)]]
      (let [fs [{:name 'main :params '[a] :body body}]]
        (is (identical? fs (search/augment-functions fs)) (pr-str body)))))
  (doseq [[label emit] backends]
    (testing label
      ;; And the code image really is helper-free: adding them would have
      ;; changed these bytes, which is exactly why a non-searching program
      ;; must not get them.
      (let [plain {:format :kotoba.kir/v4 :exports ['main]
                   :functions [{:name 'main :params '[a] :body '(+ a 1)}]}
            searching {:format :kotoba.kir/v4 :exports ['main]
                       :functions [{:name 'main :params '[a] :result :i64
                                    :param-types [:i64]
                                    :body '(+ a (string-contains? "abc" "b"))}]}]
        (is (not= (count (:code (emit plain))) (count (:code (emit searching))))
            "the helpers are real code, so their absence is observable")))))

(deftest the-helpers-are-injected-once-and-never-exported
  (let [module (program :i64 '(string-contains? "abc" "b"))
        names (mapv :name (:functions module))]
    (is (= ['main search/span-name search/find-name] names)
        "contains? needs the span and the find, and nothing else")
    (is (= ['main search/span-name search/find-name search/replace-from-name]
           (mapv :name (:functions (program :string '(string-replace-all "a" "a" "b")))))
        "replace-all additionally needs the driver")
    ;; Idempotent: emitting an already-augmented module must not append a
    ;; second copy, or every call displacement past the first copy would be
    ;; wrong.
    (is (= (:functions module) (search/augment-functions (:functions module)))))
  (doseq [[label emit] backends]
    (testing label
      (doseq [[why body] [["contains?" '(string-contains? "abc" "b")]
                          ["replace-all" '(string-replace-all "a" "a" "b")]]]
        (is (= ['main]
               (keys (:exports (emit (program (if (= why "contains?") :i64 :string) body)))))
            (str why ": a program's public surface must not change because it "
                 "searched a string"))))))

(deftest a-helper-name-collision-is-refused
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"collides with a native string-search helper"
       (search/augment-functions
        [{:name 'main :params [] :body '(string-contains? "a" "a")}
         {:name search/find-name :params '[a b c d] :body 'a}]))))

(deftest a-search-operation-of-the-wrong-arity-is-not-lowered
  ;; The arity guard is on the lowering clause, so a malformed call falls
  ;; through to `emit-call` and is reported as an operation this backend does
  ;; not implement -- rather than being silently lowered as if an argument had
  ;; been supplied.
  (doseq [[label emit] backends]
    (testing label
      (doseq [body ['(string-contains? "a")
                    '(string-contains? "a" "b" "c")
                    '(string-replace-all "a" "b")
                    '(string-replace-all "a" "b" "c" "d")]]
        (is (thrown? clojure.lang.ExceptionInfo
                     (emit {:format :kotoba.kir/v4 :exports ['main]
                            :functions [{:name 'main :params [] :body body}]}))
            (pr-str body))))))

(deftest a-search-nested-inside-other-work-still-lowers-on-both-isas
  ;; The rewrite is re-entered through `emit-expr`, so an occurrence that is
  ;; not the whole body -- inside a `let`, inside an `if`, inside arithmetic,
  ;; or feeding another string operation -- has to reach the same code.
  (doseq [[label emit] backends]
    (testing label
      (doseq [[why body]
              [["inside an if test" '(if (string-contains? "abc" "b") 1 0)]
               ["inside arithmetic" '(+ 1 (string-contains? "abc" "b"))]
               ["inside a let binding"
                '(let [found (string-contains? "abc" "b")] (+ found 1))]
               ["twice in one body"
                '(+ (string-contains? "abc" "b") (string-contains? "xyz" "y"))]
               ["feeding another string operation"
                '(string-byte-length (string-replace-all "a-b" "-" "+"))]
               ["a search over a replaced string"
                '(if (string-contains? (string-replace-all "a-b" "-" "+") "+") 1 0)]]]
        (is (seq (:code (emit {:format :kotoba.kir/v4 :exports ['main]
                               :functions (search/augment-functions
                                           [{:name 'main :params [] :body body}])})))
            why)))))

(deftest a-search-over-runtime-strings-lowers-and-agrees-with-the-oracle
  ;; Every row above searches literals. The operands may equally be
  ;; parameters or computed strings, and the rewrite binds them exactly once
  ;; -- which is what the reference interpreter does and what a duplicated
  ;; operand would break.
  (let [module {:format :kotoba.kir/v4 :exports ['main]
                :functions (search/augment-functions
                            [{:name 'main :params '[h n]
                              :param-types [:string :string] :result :i64
                              :body '(string-contains? h n)}])}
        oracle {:format :kotoba.kir/v4 :exports ['main]
                :functions [{:name 'main :params '[h n]
                             :param-types [:string :string] :result :i64
                             :body '(string-contains? h n)}]}
        lowered (assoc-in (vec (:functions module)) [0 :body]
                          (search/lower-contains ['h 'n]))]
    (doseq [[haystack needle] [["abcdef" "cd"] ["abcdef" "zz"] ["日本語" "本"]
                               ["" "a"] ["aa" "aaa"]]]
      (is (= (ir/execute oracle 'main [haystack needle] {:fuel interpreter-fuel})
             (ir/execute (assoc module :functions lowered) 'main [haystack needle]
                         {:fuel interpreter-fuel}))
          (str (pr-str haystack) " / " (pr-str needle))))
    (doseq [[label emit] backends]
      (testing label (is (seq (:code (emit module))))))))
