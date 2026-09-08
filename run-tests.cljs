(ns run-tests
  "The portable slice of the native backend on nbb -- no JVM in this path.

   nbb --classpath \"src:test:$(clojure -Spath -M:test)\" run-tests.cljs"
  (:require [cljs.test :as t]
            ;; 2026-09-08: `affine.cljc` carries no reader conditional at all --
            ;; it is portable by construction -- and its test was `.cljc` too, and
            ;; still ran on one host, because this runner is an explicit list and
            ;; did not name it. `scripts/verify-cljs-runner-completeness.cljs` did.
            [kotoba.native.affine-test]
            [kotoba.native.elf64-portable-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

(t/run-tests 'kotoba.native.affine-test
             'kotoba.native.elf64-portable-test)
