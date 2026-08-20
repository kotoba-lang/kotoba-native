(ns run-tests
  "The portable slice of the native backend on nbb -- no JVM in this path.

   nbb --classpath \"src:test:$(clojure -Spath -M:test)\" run-tests.cljs"
  (:require [cljs.test :as t]
            [kotoba.native.elf64-portable-test]))

(defmethod t/report [:cljs.test/default :end-run-tests] [m]
  (println (str "\nnbb: " (:test m) " tests, " (:pass m) " passed, "
                (:fail m) " failed, " (:error m) " errors"))
  (when (pos? (+ (or (:fail m) 0) (or (:error m) 0)))
    (set! (.-exitCode js/process) 1)))

(t/run-tests 'kotoba.native.elf64-portable-test)
