(ns kotoba.native.string-search
  "`string-contains?` and `string-replace-all`, lowered for BOTH native ISAs
  out of operations the backends already emit.

  ## Why this is a source rewrite and not a new context callback

  A string value on native is a one-word `pair(offset,length)` handle, and the
  only things that can READ the bytes behind that handle are the host context
  callbacks -- `string=?` (112), `string-concat` (120), `string-substring`
  (136), `string-code-point-at` (144). A search could therefore have been one
  more callback at a new context offset. It is not, because a new slot is a
  **v4 context ABI bump**, and the loader that would have to supply it
  (`tools/kexe_loader.c`) is not in this repository and has its source digest
  pinned by `kotoba.artifact.runtime-identity`. Search is expressible from the
  four callbacks that already exist, so nothing here costs an ABI bump, a
  loader change, a new value representation or a new instruction encoding --
  the same discipline `keyword-name`/`keyword-from-string` already follow
  (they desugar into `string-substring`/`string-concat`).

  ## Why the scan advances by CODE POINTS, not by bytes

  The obvious lowering -- slide a byte cursor and compare
  `(string-substring h i (+ i nlen))` against the needle -- TRAPS on any
  multi-byte haystack. `kotoba.kir.value/utf8-substring!` requires both
  offsets to be code-point boundaries, and `(+ i nlen)` is not one in general:
  searching for the 2-byte needle `\"ab\"` in `\"日本\"` asks for
  `(string-substring h 0 2)`, and 2 splits the first code point. There is no
  boundary predicate to test with and a trap cannot be caught, so the scan can
  never construct an offset it has not walked to.

  So both cursors are walked. `string-code-point-at`'s own docstring states
  the contract this relies on: the code point's UTF-8 width is derivable from
  its VALUE (< 0x80 -> 1, < 0x800 -> 2, < 0x10000 -> 3, else 4), \"so a single
  op is enough to walk a string\". `code-point-width` is exactly that
  derivation, written inline rather than as a helper function, because a
  function call costs fuel and a host callback does not (see below).

  `string-span` establishes the END offset of the first candidate window by
  advancing the haystack cursor one code point for every code point of the
  needle. `string-find` then slides BOTH cursors together, so the window
  always spans exactly as many code points as the needle and both of its
  offsets are always boundaries the walk reached. Comparison is then a single
  `string=?` over a `string-substring` -- and two strings are equal iff they
  are the same code points, so a same-code-point-count window is the right
  window even though its byte length may differ from the needle's.

  When the window DOES match, its byte length is the needle's, so a match at
  `k` ends at exactly `k + (string-byte-length n)`. That is what lets
  `string-replace-from` skip a match with plain arithmetic.

  ## Fuel, and why the helpers are shaped the way they are

  `emit-function` charges one unit of fuel per function entry, and
  `emit-tail-self-call` charges one per iteration -- but a host context
  callback charges none. The qualification loader starts a program with 512
  units. Every helper here is therefore shaped to spend ONE fuel unit per
  code point examined and to push everything else onto free callbacks, which
  is why `code-point-width` is inlined (re-reading the code point through
  `string-code-point-at` up to three times is free; calling a width function
  once is not) and why the substring/compare/concat work is never hoisted into
  a `let`.

  The `let` avoidance is also load-bearing on x86-64 for a second reason:
  `emit-call`'s tail-self-call fast path requires `(zero? temp-depth)`, so a
  self-call from inside a `let` body falls back to a real CALL and grows the
  stack. Every recursive call below is in tail position at depth zero, so on
  x86-64 the scan is a jump. AArch64 has no tail-self-call path and does grow
  its stack, one small frame per iteration -- bounded by the same fuel budget
  that bounds the iteration count, so the two ISAs differ in stack use and not
  in results.

  ## The empty needle

  `kotoba.kir`'s evaluator TRAPS on an empty needle
  (`:empty-string-search-needle` / `:empty-string-replacement-needle`) rather
  than returning a value, so the lowering must not return one either. It traps
  by evaluating `(string-code-point-at n 0)`, which is out of bounds exactly
  when `n` is empty. The trap's identity differs from the interpreter's
  keyword -- native traps carry no keyword at all, the loader reports
  `KEXE_TRAP` -- but the observable behaviour (no value is produced) agrees,
  and it needs no new trap encoding in either backend.")

;; Bound to the two operands so each is evaluated exactly once, matching the
;; reference interpreter, which evaluates every argument once before applying.
(def ^:private haystack 'kotoba$string-search-haystack)
(def ^:private needle 'kotoba$string-search-needle)
(def ^:private subject 'kotoba$string-replace-subject)
(def ^:private replace-needle 'kotoba$string-replace-needle)
(def ^:private replacement 'kotoba$string-replace-replacement)

(def span-name 'kotoba$string-span)
(def find-name 'kotoba$string-find)
(def replace-from-name 'kotoba$string-replace-from)

(def ^:private helper-names #{span-name find-name replace-from-name})

(defn- code-point-width
  "The UTF-8 byte width of the code point that STARTS at byte offset I of S.

  S and I must be symbols: the form reads the code point up to three times,
  which is free only because `string-code-point-at` is a host callback with no
  fuel cost and no allocation. OFFSET I must be a code-point boundary strictly
  inside S -- every use below has already established that."
  [s i]
  (let [c (list 'string-code-point-at s i)]
    (list 'if (list '< c 128) 1
          (list 'if (list '< c 2048) 2
                (list 'if (list '< c 65536) 3 4)))))

;; Advance I over S and J over N in lockstep, one code point at a time, until
;; the needle is exhausted; answer the haystack offset reached. `-1` means the
;; haystack ran out first, i.e. fewer code points remain at I than the needle
;; has -- so no window starting at I can match and neither can any later one.
;;
;; This is what establishes the first window's END. `string-find` maintains it
;; from there without calling back in.
(def ^:private span-function
  {:name span-name
   :params '[s n i j]
   ;; Declared like any other KIR function, not just enough for the backends:
   ;; a backend reads only `:name`/`:params`/`:body`/`:result`, but the
   ;; reference interpreter type-checks arguments, and being runnable BY THE
   ;; ORACLE is what lets the lowering be compared against `string-contains?`
   ;; itself rather than against a hand-computed answer.
   :param-types [:string :string :i64 :i64]
   :result :i64
   :body (list 'if (list '>= 'j (list 'string-byte-length 'n))
               'i
               (list 'if (list '>= 'i (list 'string-byte-length 's))
                     -1
                     (list span-name 's 'n
                           (list '+ 'i (code-point-width 's 'i))
                           (list '+ 'j (code-point-width 'n 'j)))))})

;; The first byte offset at or after I where N occurs in S, or -1.
;;
;; E is the end of the window starting at I -- exactly as many code points
;; after I as N has -- or -1 once the haystack cannot supply that many. Both I
;; and E are boundaries reached by walking, so the `string-substring` below can
;; never split a code point.
;;
;; A window that compares EQUAL to N has N's byte length, so the caller may
;; read the match's end as `(+ i (string-byte-length n))` without walking
;; again.
(def ^:private find-function
  {:name find-name
   :params '[s n i e]
   :param-types [:string :string :i64 :i64]
   :result :i64
   :body (list 'if (list '< 'e 0)
               -1
               (list 'if (list 'string=? (list 'string-substring 's 'i 'e) 'n)
                     'i
                     (list find-name 's 'n
                           (list '+ 'i (code-point-width 's 'i))
                           ;; E steps by one code point too, so the window
                           ;; keeps its code-point width; once E is the end of
                           ;; S there is no further window.
                           (list 'if (list '>= 'e (list 'string-byte-length 's))
                                 -1
                                 (list '+ 'e (code-point-width 's 'e))))))})

;; ACC ++ S with every occurrence of N replaced by R. K is the offset of the
;; next occurrence in S, or -1 -- the caller finds the first one, and each
;; iteration finds the next in the SUFFIX it hands on, so the replacement is
;; never rescanned. That is what makes a replacement containing the needle
;; terminate and match `clojure.string/replace`'s non-overlapping,
;; left-to-right result.
;;
;; The suffix expression appears three times rather than being `let`-bound:
;; binding it would cost the x86-64 tail-self-call (see the namespace
;; docstring), while repeating it costs only host callbacks, which are free of
;; fuel and -- for `string-substring`, which returns a VIEW -- free of pool
;; bytes as well.
(def ^:private replace-from-function
  (let [suffix (list 'string-substring 's
                     (list '+ 'k (list 'string-byte-length 'n))
                     (list 'string-byte-length 's))]
    {:name replace-from-name
     :params '[acc s n r k]
     :param-types [:string :string :string :string :i64]
     :result :string
     :body (list 'if (list '< 'k 0)
                 (list 'string-concat 'acc 's)
                 (list replace-from-name
                       (list 'string-concat 'acc
                             (list 'string-concat
                                   (list 'string-substring 's 0 'k) 'r))
                       suffix 'n 'r
                       (list find-name suffix 'n 0
                             (list span-name suffix 'n 0 0))))}))

(defn- uses? [ops form]
  (cond
    (seq? form) (or (contains? ops (first form))
                    (boolean (some #(uses? ops %) (rest form))))
    (vector? form) (boolean (some #(uses? ops %) form))
    :else false))

(defn lower-contains
  "`(string-contains? h n)` over the operations both backends already emit."
  [args]
  (let [[h n] args]
    (list 'let [haystack h needle n]
          (list 'do
                ;; Traps iff the needle is empty; see the namespace docstring.
                (list 'string-code-point-at needle 0)
                (list 'if (list '< (list find-name haystack needle 0
                                         (list span-name haystack needle 0 0))
                                0)
                      0 1)))))

(defn lower-replace-all
  "`(string-replace-all s n r)` over the operations both backends already emit."
  [args]
  (let [[s n r] args]
    (list 'let [subject s replace-needle n replacement r]
          (list 'do
                (list 'string-code-point-at replace-needle 0)
                (list replace-from-name
                      ;; The empty accumulator is a zero-length view of the
                      ;; subject rather than the literal "": offset 0 is a
                      ;; boundary of every string, and this asks nothing of
                      ;; the literal table.
                      (list 'string-substring subject 0 0)
                      subject replace-needle replacement
                      (list find-name subject replace-needle 0
                            (list span-name subject replace-needle 0 0)))))))

(defn augment-functions
  "FUNCTIONS plus exactly the search helpers its bodies actually reach.

  A program that uses neither operation is returned unchanged -- byte for
  byte, since the helper code is what would otherwise be appended -- so this
  cannot move the emission of any existing program.

  The helpers are appended, never exported: `emit-program` derives its export
  set from the ORIGINAL function list, so a program's public surface is the
  same whether or not it searches a string.

  IDEMPOTENT. A helper already present with the definition this would append
  is left alone rather than appended a second time -- a second copy would put
  every call displacement past the first copy at the wrong distance. A name
  present with a DIFFERENT definition is a real collision and is refused,
  because the calls this lowering emits would silently go there instead."
  [functions]
  (let [bodies (map :body functions)
        searches? (some #(uses? '#{string-contains?} %) bodies)
        replaces? (some #(uses? '#{string-replace-all} %) bodies)]
    (if-not (or searches? replaces?)
      functions
      (let [declared (into {} (map (juxt :name identity)) functions)
            wanted (cond-> [span-function find-function]
                     replaces? (conj replace-from-function))
            clash (filter
                   (fn [helper]
                     (when-let [existing (get declared (:name helper))]
                       (not= existing helper)))
                   wanted)]
        (when (seq clash)
          (throw (ex-info "a program function collides with a native string-search helper"
                          {:phase :native :functions (mapv :name clash)})))
        (vec (concat functions
                     (remove #(contains? declared (:name %)) wanted)))))))
