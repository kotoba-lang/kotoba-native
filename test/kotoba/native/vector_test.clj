(ns kotoba.native.vector-test
  "`vector-i64` / `vector-f64` on both native ISAs (ADR-2608030300).

  `kotoba-kir` has declared these operators since before either native backend
  existed and `kotoba-wasm` has implemented them all along; only native had
  nothing. What closed the gap is NOT a new value representation: a vector
  value is a one-word handle, the same width and the same discipline as the
  pair handle every option, result, string and keyword already travels as, so
  all six operations are ordinary context calls.

  These tests pin the three claims that make that lowering true rather than
  merely plausible: the host table offsets, that construction is linear rather
  than quadratic, and that the f64 family is the SAME lowering rather than a
  parallel one that could drift."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.x86-64 :as x86]
            [kotoba.native.aarch64 :as arm]))

(defn- program [params body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions [{:name 'main :params params :body body}]})

(defn- code [emit params body]
  (vec (:code (emit (program params body)))))

;; `call qword ptr [r9+disp32]` -- the encoding emit-heap-call uses for every
;; offset above 127, which all six vector offsets are.
(defn- x86-context-call [offset]
  [0x41 0xff 0x91
   (bit-and offset 0xff) (bit-and (bit-shift-right offset 8) 0xff)
   (bit-and (bit-shift-right offset 16) 0xff) (bit-and (bit-shift-right offset 24) 0xff)])

(defn- occurrences [haystack needle]
  (count (filter #(= needle (subvec haystack % (+ % (count needle))))
                 (range (inc (- (count haystack) (count needle)))))))

;; ---------------------------------------------------------------------------
;; The host table offsets
;; ---------------------------------------------------------------------------

;; Pinned here as well as in `tools/kexe_loader.c`'s own `_Static_assert`s and
;; `kotoba.verifier`'s expected context ABI, because a silent disagreement
;; between producer and host is exactly the class of bug the loader's asserts
;; cannot catch: they only prove the C struct's own layout, never that the
;; compiler calls the slot it means to.
(deftest each-operation-calls-its-own-context-slot
  (doseq [[body offset] [['(vector-count v) 168]
                         ['(vector-at v i) 176]
                         ['(vector-assoc v i x) 184]
                         ['(vector-conj v x) 160]
                         ['(vector-drop v n) 192]]]
    (testing (str body)
      (is (= 1 (occurrences (code x86/emit-program '[v i x n] body)
                            (x86-context-call offset)))
          "exactly one call, to this operation's own slot"))))

(deftest an-empty-vector-is-one-call-to-the-construction-slot
  (is (= 1 (occurrences (code x86/emit-program [] '(vector-new))
                        (x86-context-call 152)))))

;; ---------------------------------------------------------------------------
;; Construction is linear
;; ---------------------------------------------------------------------------

;; KIR's `vector-new` is variadic and the context ABI is not, so construction
;; expands to one `conj` per element. That expansion is only acceptable
;; because the host appends in place when the source slice ends at the arena
;; top -- which every intermediate here does, by construction. If a future
;; change made `vector-new` allocate a fresh copy per element instead, this
;; count would not move but the loader's copy counter would; the paired
;; guarantee lives in `checked_vector_conj`.
(deftest construction-is-one-conj-per-element
  (doseq [arity (range 0 5)]
    (let [body (cons 'vector-new (take arity '[a b c d]))
          emitted (code x86/emit-program '[a b c d] body)]
      (testing (str body)
        (is (= 1 (occurrences emitted (x86-context-call 152)))
            "one empty-vector construction")
        (is (= arity (occurrences emitted (x86-context-call 160)))
            "one conj per element, and no more")))))

;; ---------------------------------------------------------------------------
;; The f64 family is the same lowering, not a parallel one
;; ---------------------------------------------------------------------------

;; A native f64 is already an i64 word carrying an IEEE-754 bit pattern, so an
;; f64 vector is a vector of those words. Byte equality is the strongest
;; available statement that the two KIR families cannot drift apart below this
;; layer: not "both work", but "they are one emission".
(deftest f64-vector-operations-emit-identically-to-their-i64-counterparts
  (doseq [[i64-body f64-body params]
          [['(vector-new a b) '(vector-f64-new a b) '[a b]]
           ['(vector-count v) '(vector-f64-count v) '[v]]
           ['(vector-at v i) '(vector-f64-at v i) '[v i]]
           ['(vector-get v i d) '(vector-f64-get v i d) '[v i d]]
           ['(vector-assoc v i x) '(vector-f64-assoc v i x) '[v i x]]
           ['(vector-conj v x) '(vector-f64-conj v x) '[v x]]
           ['(vector-drop v n) '(vector-f64-drop v n) '[v n]]]]
    (testing (str f64-body)
      (is (= (code x86/emit-program params i64-body)
             (code x86/emit-program params f64-body))
          "x86-64: same emission")
      (is (= (code arm/emit-program params i64-body)
             (code arm/emit-program params f64-body))
          "AArch64: same emission"))))

;; ---------------------------------------------------------------------------
;; vector-get is total
;; ---------------------------------------------------------------------------

;; `vector-at` traps out of range; `vector-get` must not, because it carries a
;; fallback. It therefore lowers to a bounds test around `vector-at` -- and
;; the fallback is emitted ONCE, so nesting a `vector-get` inside another
;; one's fallback cannot double the code size at each level.
(deftest vector-get-tests-both-bounds-and-emits-its-fallback-once
  (let [emitted (code x86/emit-program '[v i d] '(vector-get v i d))]
    (is (= 1 (occurrences emitted (x86-context-call 168)))
        "the upper bound is read from the vector's own count")
    (is (= 1 (occurrences emitted (x86-context-call 176)))
        "the element is read through vector-at, once"))
  (let [single (code x86/emit-program '[v i d] '(vector-get v i d))
        nested (code x86/emit-program '[v i d]
                     '(vector-get v i (vector-get v i d)))]
    (is (= 2 (occurrences nested (x86-context-call 176)))
        "one vector-at per nesting level, not one per level squared")
    (is (< (count nested) (* 2 (count single)))
        "nesting adds a level, it does not double the whole expansion")))

;; A vector handle is an ordinary one-word value, so it composes with the
;; value forms that already exist rather than needing its own copies of them.
(deftest a-vector-handle-is-an-ordinary-word
  (doseq [[params body] [['[a] '(let [v (vector-new a)] (vector-count v))]
                         ['[a] '(if (vector-count (vector-new a)) 1 0)]
                         ['[a] '(vector-count (vector-conj (vector-new a) a))]]]
    (testing (str body)
      (is (seq (code x86/emit-program params body)) "x86-64")
      (is (seq (code arm/emit-program params body)) "AArch64"))))
