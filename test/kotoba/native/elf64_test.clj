(ns kotoba.native.elf64-test
  (:require [clojure.test :refer [deftest is testing]]
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

(defn- le64 [bytes offset]
  (reduce (fn [value index]
            (+ value (bit-shift-left (long (nth bytes (+ offset index)))
                                     (* index 8))))
          0 (range 8)))

(deftest kernel-image-context-uses-the-sealed-fuel-bound
  (doseq [[target package]
          [[:x86_64-aiueos-kernel-v1 elf64/package-kernel]
           [:aarch64-aiueos-kernel-v1 elf64/package-kernel-aarch64]]]
    (let [fuel 4096
          image (:bytes (package (sealed-kernel target fuel)))]
      (is (= fuel (le64 image (+ 0x8000 8))) (str target)))))

(deftest x86-kernel-image-owns-gdt-tss-and-rsp0-stack
  (let [image (:bytes (elf64/package-kernel
                       (sealed-kernel :x86_64-aiueos-kernel-v1 4096)))
        data 0x8000]
    (is (= 0x00af9a000000ffff (le64 image (+ data 104))))
    (is (= 0x00cf92000000ffff (le64 image (+ data 112))))
    (is (= 55 (+ (nth image (+ data 152))
                 (bit-shift-left (nth image (+ data 153)) 8))))
    (is (= 0x11b000 (le64 image (+ data 172))))
    (is (= [0x0f 0x01 0x15] (subvec image 0x100c 0x100f)))
    (is (= [0x0f 0x00 0xd8] (subvec image 0x1033 0x1036)))))

(deftest value-runtime-kernel-installs-and-enters-a-closed-syscall-shim
  (let [artifact (-> (sealed-kernel :x86_64-aiueos-kernel-v1 4096)
                     (assoc :exports {'main {:offset 0 :arity 0}
                                      'aiueos-value-runtime-syscall-plan
                                      {:offset 1 :arity 5}
                                      'aiueos-value-runtime-entry
                                      {:offset 2 :arity 5}}
                            :code [0xc3 0xc3 0xc3])
                     (dissoc :sha256)
                     artifact/seal)
        packaged (elf64/package-kernel artifact)
        image (:bytes packaged)
        syscall-file-offset (+ 0x1000 144)]
    (is (:value-runtime-live? packaged))
    (is (= 0x101090 (:syscall-entry-address packaged)))
    (is (some #(= [0xb9 0x82 0x00 0x00 0xc0 0xb8] %)
              (partition 6 1 (subvec image 0x1000 syscall-file-offset)))
        "boot writes IA32_LSTAR")
    (is (= [0x48 0x89 0x25]
           (subvec image syscall-file-offset (+ syscall-file-offset 3)))
        "SYSCALL saves user RSP before switching stacks")
    (is (= [0x0f 0x85 0x07 0x00 0x00 0x00 0x31 0xc0
            0xe9 0x34 0x00 0x00 0x00]
           (subvec image (+ syscall-file-offset 88)
                         (+ syscall-file-offset 101)))
        "a rejected plan returns zero without entering ValueRuntime")
    (is (= [0xb9 0x84 0x00 0x00 0xc0
            0xb8 0x00 0x77 0x04 0x00 0x31 0xd2 0x0f 0x30]
           (subvec image (- syscall-file-offset 33)
                         (- syscall-file-offset 19)))
        "FMASK clears trap/interrupt/direction and privileged user flags")
    (is (some #(= [0x48 0x0f 0x07] %)
              (partition 3 1 (subvec image syscall-file-offset
                                     (+ syscall-file-offset 192))))
        "admitted and rejected calls return through SYSRETQ")
    (is (= 77824 (le64 image (+ 64 56 40)))
        "RW memory owns metadata, scratch, capability table, arena and stack")))

(deftest a-half-value-runtime-boundary-never-installs-lstar
  (let [artifact (-> (sealed-kernel :x86_64-aiueos-kernel-v1 4096)
                     (assoc-in [:exports 'aiueos-value-runtime-entry]
                               {:offset 0 :arity 5})
                     (dissoc :sha256)
                     artifact/seal)]
    (let [packaged (elf64/package-kernel artifact)]
      (is (false? (:value-runtime-live? packaged)))
      (is (nil? (:syscall-entry-address packaged))))))

(deftest large-kernel-image-moves-data-to-the-next-page
  (let [fuel 4096
        large (-> (sealed-kernel :x86_64-aiueos-kernel-v1 fuel)
                  (assoc :code (vec (concat (repeat 30000 0x90) [0xc3])))
                  (dissoc :sha256)
                  artifact/seal)
        image (:bytes (elf64/package-kernel large))]
    (is (= fuel (le64 image (+ 0x9000 8))))
    (is (> (count image) 0x9000))))

(deftest kernel-image-rejects-disagreeing-fuel-identities
  (let [value (assoc (sealed-kernel :x86_64-aiueos-kernel-v1 4096)
                     :fuel-abi {:initial 512})]
    (testing "resealing does not make contradictory context authority valid"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"one valid sealed fuel bound"
                            (elf64/package-kernel
                             (artifact/seal (dissoc value :sha256))))))))

(deftest aiueos-user-packaging-refuses-value-runtime-until-c-free-provider-qualification
  (let [value (artifact/seal
               {:target :x86_64-aiueos-user-v1
                :program {:entry 'main
                          :functions [{:name 'main :params []
                                       :body '(value-release 1)}]}
                :exports {'main {:offset 0 :arity 0}}
                :effects #{}
                :code [0xc3]})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"ValueRuntime provider is not qualified"
                          (elf64/package-user value)))))
