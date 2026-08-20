(ns kotoba.native.elf64-portable-test
  "The ELF64 packager, exercised on BOTH runtimes.

   `kotoba.native.elf64` was the last `.clj` in this repo: eight sibling files
   were already `.cljc`, so one file was the whole reason the machine-code
   backend needed a JVM. It is `.cljc` now, and this is the evidence for that
   rename -- a rename on its own asserts portability without executing it.

   Run without a JVM:
     nbb --classpath \"src:test:<deps>\" run-tests.cljs"
  (:require [clojure.test :refer [deftest is]]
            [kotoba.artifact.core :as artifact]
            [kotoba.native.elf64 :as elf64]))

(defn- sealed-kernel [target fuel]
  (artifact/seal
   {:target target
    :target-profile {:runtime :none :ambient-syscalls false}
    :program {:entry 'main}
    :exports {'main {:offset 0 :arity 0}}
    :limits {:fuel fuel}
    :fuel-abi {:initial fuel}
    :code [0xc3]}))

(deftest packs-an-elf64-kernel-image
  (let [image (:bytes (elf64/package-kernel
                       (sealed-kernel :x86_64-aiueos-kernel-v1 4096)))]
    ;; ELF magic. If `utf8-bytes` or the section-name table were wrong on this
    ;; runtime, the header would not survive this.
    (is (= [0x7f 0x45 0x4c 0x46] (vec (take 4 image))))
    (is (pos? (count image)))
    ;; every emitted byte is a byte
    (is (every? #(<= 0 % 255) image))))

(deftest packs-an-aarch64-kernel-image
  (let [image (:bytes (elf64/package-kernel-aarch64
                       (sealed-kernel :aarch64-aiueos-kernel-v1 4096)))]
    (is (= [0x7f 0x45 0x4c 0x46] (vec (take 4 image))))
    (is (every? #(<= 0 % 255) image))))

(deftest rejects-an-unsealed-fuel-bound
  ;; This is the branch that used to read `Long/MAX_VALUE`.
  (is (thrown? #?(:clj Exception :cljs js/Error)
               (elf64/package-kernel
                (artifact/seal
                 {:target :x86_64-aiueos-kernel-v1
                  :target-profile {:runtime :none :ambient-syscalls false}
                  :program {:entry 'main}
                  :exports {'main {:offset 0 :arity 0}}
                  :limits {:fuel 4096}
                  :fuel-abi {:initial 8192}
                  :code [0xc3]})))))

(deftest packs-a-user-image
  ;; `package-user` builds its own section-name and symbol tables, so this is
  ;; the path that exercises `utf8-bytes` over a computed string rather than a
  ;; literal.
  (let [image (:bytes (elf64/package-user
                       (sealed-kernel :x86_64-aiueos-user-v1 4096)))]
    (is (= [0x7f 0x45 0x4c 0x46] (vec (take 4 image))))
    (is (every? #(<= 0 % 255) image))))

(deftest packs-a-linkable-kernel-object
  ;; `package-kernel-object` is the remaining `utf8-bytes` caller: it builds
  ;; `shstr` and a symbol string table from runtime values. Without this the
  ;; portable suite passed even with a `.getBytes` restored there -- a method
  ;; call compiles in cljs and only fails when executed, so an unexercised
  ;; branch keeps its JVM interop invisibly.
  (let [object (:bytes (elf64/package-kernel-object
                        (sealed-kernel :x86_64-aiueos-kernel-v1 4096)))]
    (is (= [0x7f 0x45 0x4c 0x46] (vec (take 4 object))))
    (is (every? #(<= 0 % 255) object))))
