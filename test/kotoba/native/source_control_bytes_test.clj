(ns kotoba.native.source-control-bytes-test
  "A raw control byte makes grep treat a source file as binary, so it prints
  nothing and exits 1 -- which is what a file NOT containing the searched word
  does. `src/kotoba/native/elf64.clj` carried four raw NULs inside the ELF
  shstrtab literal, and it is the JVM allowlist for every aiueos kernel export
  symbol (ADR-0036). Auditing that table with grep returned silence."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]))

(defn- control-bytes [^java.io.File f]
  (let [bytes (with-open [in (io/input-stream f)]
                (.readAllBytes in))]
    (count (filter (fn [b]
                     (let [v (bit-and (int b) 0xff)]
                       (or (< v 9) (= v 11) (= v 12) (and (< 13 v) (< v 32)))))
                   bytes))))

(deftest sources-carry-no-raw-control-bytes
  (let [sources (->> (file-seq (io/file "src"))
                     (filter #(.isFile ^java.io.File %))
                     (filter #(re-find #"\.cljc?$" (.getName ^java.io.File %))))
        offenders (into (sorted-map)
                        (keep (fn [f]
                                (let [n (control-bytes f)]
                                  (when (pos? n) [(.getPath ^java.io.File f) n])))
                              sources))]
    ;; Evidence floor: a scan that found no files has not found no offenders.
    (is (pos? (count sources)) "no sources were scanned")
    (is (= {} offenders))))
