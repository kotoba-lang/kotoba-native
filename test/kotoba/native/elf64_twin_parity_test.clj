(ns kotoba.native.elf64-twin-parity-test
  "`elf64.clj` and `elf64.cljc` are a twin (ADR-0036), and the JVM loads the
  `.clj`. The ADR states the rule as *the JVM file must not be a weaker
  allowlist than the portable one*, and nothing measured it.

  It drifted, in both directions. Measured 2026-08-31 at kotoba-native
  `ff02fd24`: the `.clj` table had 74 entries and the `.cljc` table 69, with
  three names only in `.cljc` and eight only in `.clj`. The three the JVM was
  missing were `aiueos-dhcp-option-u32`, `aiueos-dhcp-reply-valid` and
  `aiueos-ecdsa-p256-sha256-verify` -- and because the JVM packager is the one
  that runs, three aiueos objects that build against the pinned kotoba-native
  stopped building at the tip. They surfaced as `:kotoba/internal-error`,
  \"internal compiler error\", which reads like a compiler crash and is not one.

  The two DHCP entries were in `.clj` at the pinned `a60da444` (where `.cljc`
  did not yet exist). Introducing the portable twin moved them instead of
  copying them.

  This compares the two tables directly, because the rule is about the tables
  and every other way of checking it is a proxy.

  The table was not the only axis. Measured 2026-08-31 through a cross-route
  comparison of the aiueos objects: `package-kernel-object`'s FUEL TIERS had
  drifted the same way. The `.clj` had four arms and the `.cljc` six, missing
  `ecdsa-fuel?` and `dhcp-fuel?`, so on the JVM `aiueos-ecdsa-p256-sha256-verify`
  fell through to RSA's 250,000,000 instead of 2,147,483,647 and the two DHCP
  objects fell all the way to the 1,024 default -- a 64x under-fuelling whose
  failure mode is a prologue `ud2`, surfacing as an unexpected vector 6 that
  reads as a protocol bug rather than a fuel bug.

  The three shipped objects carry the `.cljc` values (`ffffff7f`, `00000100`,
  `00000100` at file offset 75), so the JVM twin was the stale one and rebuilding
  them through it would have quietly weakened them.

  Why nothing here saw it: Clojure loads `.clj` for this namespace and nbb loads
  `.cljc`, so NO SINGLE RUNTIME can call both. A behavioural comparison has to
  run the two packagers under two runtimes and compare the bytes, which is what
  aiueos's `verify-jvm-free-object-parity.cljs` does. This test is the cheap
  source-level guard that catches the drift earlier."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]))

(def ^:private entry-pattern
  ;; `'name {:arity N :symbol "sym"}`, with the map allowed to sit on the next
  ;; line -- the `.cljc` table wraps where the `.clj` one does not.
  #"'(aiueos-[a-z0-9-]+)\s*\{:arity\s+(\d+)\s+:symbol\s+\"([a-z0-9_]+)\"\}")

(defn- table [path]
  (let [text (slurp (io/file path))
        entries (into {} (map (fn [[_ n a s]] [n [(parse-long a) s]]))
                      (re-seq entry-pattern (str/replace text #"\n\s+\{:arity" " {:arity")))]
    entries))

;; `name-fuel? [0x49 0xc7 0x41 0x08 b b b b]`: the cond arm that writes the
;; object's fuel immediate. Captured with its four bytes, so a tier that exists
;; in both files under one name but with different fuel is still a difference.
(def ^:private fuel-arm-pattern
  #"([a-z0-9-]+)-fuel\?\s+\[0x49 0xc7 0x41 0x08((?:\s+0x[0-9a-f]{2}){4})\]")

(defn- fuel-tiers [path]
  (into {} (map (fn [[_ n bytes]] [n (str/trim bytes)]))
        (re-seq fuel-arm-pattern (slurp (io/file path)))))

(deftest the-two-elf64-fuel-tiers-are-the-same-tiers
  (let [clj (fuel-tiers "src/kotoba/native/elf64.clj")
        cljc (fuel-tiers "src/kotoba/native/elf64.cljc")]
    ;; Evidence floor: a pattern that matched nothing has not found agreement.
    (is (< 3 (count clj)) "the .clj fuel tiers did not parse")
    (is (< 3 (count cljc)) "the .cljc fuel tiers did not parse")
    (is (= (set (keys clj)) (set (keys cljc)))
        (str "fuel tier only in .clj: " (sort (remove (set (keys cljc)) (keys clj)))
             " | only in .cljc: " (sort (remove (set (keys clj)) (keys cljc)))))
    (let [disagreeing (into (sorted-map)
                            (keep (fn [[n bytes]]
                                    (when-let [other (get cljc n)]
                                      (when-not (= bytes other)
                                        [n {:clj bytes :cljc other}])))
                                  clj))]
      (is (empty? disagreeing) (str "fuel tiers disagree: " disagreeing)))))

(deftest the-two-elf64-tables-are-the-same-table
  (let [clj (table "src/kotoba/native/elf64.clj")
        cljc (table "src/kotoba/native/elf64.cljc")]
    ;; Evidence floor: a parse that found nothing has not found no difference.
    (is (< 50 (count clj)) "the .clj table did not parse")
    (is (< 50 (count cljc)) "the .cljc table did not parse")
    (is (= (set (keys clj)) (set (keys cljc)))
        (str "only in .clj: " (sort (remove (set (keys cljc)) (keys clj)))
             " | only in .cljc: " (sort (remove (set (keys clj)) (keys cljc)))))
    ;; Report only the rows that disagree. `(is (= clj cljc))` prints both
    ;; 79-entry maps in full, which is 20 KB of output for a one-row
    ;; difference and buries the answer in the evidence.
    (let [shared (filter (set (keys cljc)) (keys clj))
          conflicts (into (sorted-map)
                          (keep (fn [k] (when (not= (clj k) (cljc k))
                                          [k {:clj (clj k) :cljc (cljc k)}])))
                          shared)]
      (is (= {} conflicts) "an entry disagrees on arity or symbol between the twins"))))

(deftest every-symbol-carries-the-admitted-prefix
  (doseq [[name [_ symbol]] (table "src/kotoba/native/elf64.clj")]
    (is (str/starts-with? symbol "kotoba_aiueos_")
        (str name " -> " symbol))
    (is (= symbol (str "kotoba_" (str/replace name "-" "_")))
        (str "symbol is not the mechanical transcription of " name))))
