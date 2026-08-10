(ns kotoba.native.string-index-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.native.aarch64 :as arm]
            [kotoba.native.string-index :as string-index]
            [kotoba.native.x86-64 :as x86]))

(def ^:private backends
  [["x86-64" x86/emit-program] ["AArch64" arm/emit-program]])

(defn- program [result body]
  {:format :kotoba.kir/v4 :exports ['main]
   :functions
   (string-index/augment-functions
    [{:name 'main :params [] :param-types [] :result result :body body}])})

(defn- rewritten [result body]
  (let [op (first body)
        functions (:functions (program result body))]
    {:format :kotoba.kir/v4 :exports ['main]
     :functions
     (into [(assoc (first functions)
                   :body (string-index/lower op (rest body)))]
           (rest functions))}))

(deftest every-operation-is-the-shared-written-out-rewrite-on-both-isas
  (doseq [[result body]
          [[:string-index '(string-index-new)]
           [:i64 '(string-index-count (string-index-new))]
           [:bool '(string-index-contains (string-index-new) "cid")]
           [[:option :i64] '(string-index-get (string-index-new) "cid")]
           [:string-index
            '(string-index-assoc (string-index-new) "cid" 7)]]]
    (doseq [[label emit] backends]
      (testing (str label " " body)
        (let [direct (emit (program result body))
              expanded (emit (rewritten result body))]
          (is (seq (:code direct)))
          (is (= (:code direct) (:code expanded)))
          (is (= ['main] (keys (:exports direct)))
              "private helpers must not expand the kexe surface"))))))

(deftest helper-injection-is-bounded-idempotent-and-collision-safe
  (let [plain [{:name 'main :params [] :body '(+ 1 2)}]
        indexed (:functions
                 (program :i64
                          '(string-index-count
                            (string-index-assoc
                             (string-index-new) "cid" 1))))]
    (is (identical? plain (string-index/augment-functions plain)))
    (is (= ['main string-index/find-name string-index/key-bytes-name]
           (mapv :name indexed)))
    (is (= indexed (string-index/augment-functions indexed))))
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"collides with a native string-index helper"
       (string-index/augment-functions
        [{:name 'main :params [] :body '(string-index-new)}
         {:name string-index/find-name :params [] :body 0}]))))

(deftest assoc-rederives-both-language-limits-in-emitted-kotoba
  (let [form (string-index/lower
              'string-index-assoc
              ['index "new-key" 9])
        nodes (tree-seq coll? seq form)]
    (is (some #{256} nodes) "128 entries occupy 256 alternating words")
    (is (some #{65536} nodes) "aggregate UTF-8 key bytes stay bounded")
    (is (some #{'vector-at} nodes)
        "limit rejection uses the existing native trap path")))
