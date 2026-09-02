(ns kotoba.native.elf64
  (:require [clojure.string :as str]
            [kotoba.artifact.core :as artifact]
            [kotoba.native.interrupt-abi :as interrupt-abi]
            [kotoba.object.elf64 :as object-elf]))

(def ^:private kernel-target :x86_64-aiueos-kernel-v1)
(def ^:private user-target :x86_64-aiueos-user-v1)
(def ^:private page-size 0x1000)
(def ^:private image-base 0x100000)
(def ^:private text-offset page-size)
(def ^:private data-offset (* 2 page-size))
(def ^:private minimum-kernel-data-offset (* 8 page-size))
(def ^:private context-size 80)
(def ^:private kernel-image-context-size 88)
(def ^:private kernel-gdt-offset 96)
(def ^:private kernel-gdtr-offset 152)
(def ^:private kernel-tss-offset 168)
(def ^:private kernel-current-domain-offset 0x110)
(def ^:private kernel-saved-rsp-offset 0x118)
(def ^:private kernel-saved-rip-offset 0x120)
(def ^:private kernel-saved-rflags-offset 0x128)
(def ^:private kernel-request-pointer-offset 0x130)
(def ^:private kernel-request-offset 0x200)
(def ^:private kernel-capability-table-offset 0x1000)
(def ^:private kernel-arena-offset 0x2000)
(def ^:private kernel-stack-offset 0x3000)
(def ^:private kernel-stack-bytes 65536)
(def ^:private kernel-runtime-data-size (+ kernel-stack-offset kernel-stack-bytes))
(def ^:private live-boot-shim-size 144)
(def ^:private live-syscall-shim-size 192)
(def ^:private user-context-size 88)
(def ^:private user-image-base 0x1e0000)

(defn- align16 [n] (* 16 (quot (+ n 15) 16)))

;; isr: the toolchain-generated interrupt entries an image carries.
;;
;; `interrupt-entry-exports` answers vector -> export for every `aiueos-isr-*`
;; export, and REFUSES a name that reads as an entry and is not one. There is
;; no third answer: a name in that shape either denotes a vector this packager
;; will lay an entry down for, or it is a mistake that would otherwise compile
;; into a function nothing can ever reach.
(defn- interrupt-entry-exports [artifact]
  (let [named (->> (keys (:exports artifact))
                   (filter #(str/starts-with? (name %)
                                              interrupt-abi/entry-prefix)))
        malformed (remove interrupt-abi/entry-vector named)]
    (when (seq malformed)
      (throw (ex-info "Kotoba kernel interrupt entry name does not denote a vector"
                      {:reason :isr-name-not-a-vector
                       :names (vec (sort malformed))
                       :vector-limit interrupt-abi/vector-limit})))
    (into {} (map (fn [n] [(interrupt-abi/entry-vector n)
                           (get-in artifact [:exports n])]))
          named)))

;; isr: does the function `entry` reach `kernel-isr-entry-address`?
;;
;; Reachability and not mere presence, because an OBJECT has exactly one
;; public symbol: code the object's entry cannot reach can never execute
;; there, and the same compile produces both an image and an object (amu's
;; `compile-source*` calls both packagers). A kernel image's `main` builds an
;; IDT and so uses the operation; the entry bodies it installs do not, and
;; refusing their object because a sibling function used it would refuse the
;; object route to every image that has one.
(defn- reaches-isr-address? [artifact entry]
  (let [functions (get-in artifact [:program :functions])
        by-name (into {} (map (juxt :name identity)) functions)
        heads (fn [name]
                (->> (tree-seq coll? seq (:body (get by-name name)))
                     (filter seq?) (map first) (filter symbol?)))]
    (loop [seen #{} queue [entry]]
      (if-let [n (first queue)]
        (cond
          (contains? seen n) (recur seen (rest queue))
          (nil? (get by-name n)) (recur (conj seen n) (rest queue))
          :else
          (let [called (heads n)]
            (if (some #(= 'kernel-isr-entry-address %) called)
              true
              (recur (conj seen n)
                     (concat (rest queue) (filter by-name called))))))
        false))))

(defn- kernel-data-offset-for [text-size]
  (max minimum-kernel-data-offset
       (* page-size (quot (+ text-offset text-size (dec page-size)) page-size))))
(def ^:private value-runtime-operations
  '#{value-intern value-hydrate value-resolve value-cid-of value-release})

(defn- uses-value-runtime? [artifact]
  (boolean
   (some #(and (seq? %) (contains? value-runtime-operations (first %)))
         (tree-seq coll? seq (get-in artifact [:program :functions])))))

(def ^:private journal-entry 'aiueos-journal-plan)
(def ^:private kernel-object-entries
  {journal-entry {:arity 4 :symbol "kotoba_aiueos_journal_plan"}
   'aiueos-fnv1a {:arity 2 :symbol "kotoba_aiueos_fnv1a"}
   'aiueos-journal-record-valid {:arity 2 :symbol "kotoba_aiueos_journal_record_valid"}
   'aiueos-object-transaction-valid {:arity 2 :symbol "kotoba_aiueos_object_transaction_valid"}
   'aiueos-object-transaction-route {:arity 2 :symbol "kotoba_aiueos_object_transaction_route"}
   'aiueos-mutable-object-valid {:arity 5 :symbol "kotoba_aiueos_mutable_object_valid"}
   'aiueos-superblock-valid {:arity 2 :symbol "kotoba_aiueos_superblock_valid"}
   'aiueos-journal-record-build {:arity 3 :symbol "kotoba_aiueos_journal_record_build"}
   'aiueos-mutable-object-build {:arity 5 :symbol "kotoba_aiueos_mutable_object_build"}
   'aiueos-virtio-cap-valid {:arity 5 :symbol "kotoba_aiueos_virtio_cap_valid"}
   'aiueos-pci-extent-valid {:arity 2 :symbol "kotoba_aiueos_pci_extent_valid"}
   'aiueos-pci-region-valid {:arity 3 :symbol "kotoba_aiueos_pci_region_valid"}
   'aiueos-syscall-range-valid {:arity 4 :symbol "kotoba_aiueos_syscall_range_valid"}
   'aiueos-copy-in {:arity 5 :symbol "kotoba_aiueos_copy_in"}
   'aiueos-capability-plan {:arity 5 :symbol "kotoba_aiueos_capability_plan"}
   'aiueos-value-handle-plan {:arity 5 :symbol "kotoba_aiueos_value_handle_plan"}
   'aiueos-value-handle-arena {:arity 5 :symbol "kotoba_aiueos_value_handle_arena"}
   'aiueos-value-runtime-dispatch {:arity 5 :symbol "kotoba_aiueos_value_runtime_dispatch"}
   'aiueos-value-runtime-entry {:arity 5 :symbol "kotoba_aiueos_value_runtime_entry"}
   'aiueos-value-runtime-syscall-plan {:arity 5 :symbol "kotoba_aiueos_value_runtime_syscall_plan"}
   'aiueos-value-runtime-publish-domain {:arity 1 :symbol "kotoba_aiueos_value_runtime_publish_domain"}
   'aiueos-value-runtime-capability-mutate {:arity 5 :symbol "kotoba_aiueos_value_runtime_capability_mutate"}
   'aiueos-value-runtime-provider-status {:arity 2 :symbol "kotoba_aiueos_value_runtime_provider_status"}
   'aiueos-value-runtime-capability-grant {:arity 5 :symbol "kotoba_aiueos_value_runtime_capability_grant"}
   'aiueos-value-runtime-provider-claim {:arity 0 :symbol "kotoba_aiueos_value_runtime_provider_claim"}
   'aiueos-value-runtime-provider-complete {:arity 5 :symbol "kotoba_aiueos_value_runtime_provider_complete"}
   'aiueos-value-runtime-cas-verify {:arity 5 :symbol "kotoba_aiueos_value_runtime_cas_verify"}
   ;; The CID envelope beside the digest. `cas-verify` above compares a block
   ;; against 32 bytes the caller supplies, and its contract declares
   ;; `:identity {:cid-version 1 :codec :dag-cbor :multihash :sha2-256}` next
   ;; to it -- a declaration, not a check. This object reads those four prefix
   ;; bytes out of the CID. Symbol transcribed from aiueos
   ;; `contracts/cid-v1-admit-v1.edn`.
   'aiueos-cid-v1-admit {:arity 5 :symbol "kotoba_aiueos_cid_v1_admit"}
   ;; The UnixFS file root beside the leaf. `cid-v1-admit` above verifies ONE
   ;; block, and SHA-256 there caps a block at 12,288 bytes; the artifacts
   ;; aiueos fetches are gigabytes. A UnixFS root names its children by CID, so
   ;; an unbounded file is verified block by block against one name. Symbol
   ;; transcribed from aiueos `contracts/unixfs-file-admit-v1.edn`.
   'aiueos-unixfs-file-admit {:arity 4 :symbol "kotoba_aiueos_unixfs_file_admit"}
   'aiueos-capability-mutation-plan {:arity 5 :symbol "kotoba_aiueos_capability_mutation_plan"}
   'aiueos-service-lifecycle {:arity 4 :symbol "kotoba_aiueos_service_lifecycle"}
   'aiueos-service-registry-build {:arity 5 :symbol "kotoba_aiueos_service_registry_build"}
   'aiueos-service-registry-state {:arity 3 :symbol "kotoba_aiueos_service_registry_state"}
   'aiueos-user-object-journal-build {:arity 5 :symbol "kotoba_aiueos_user_object_journal_build"}
   'aiueos-user-object-journal-valid {:arity 3 :symbol "kotoba_aiueos_user_object_journal_valid"}
   'aiueos-user-object-journal-value {:arity 2 :symbol "kotoba_aiueos_user_object_journal_value"}
   'aiueos-sha256 {:arity 5 :symbol "kotoba_aiueos_sha256"}
   'aiueos-digest-equal {:arity 3 :symbol "kotoba_aiueos_digest_equal"}
   'aiueos-app-catalog-valid {:arity 5 :symbol "kotoba_aiueos_app_catalog_valid"}
   'aiueos-app-lookup-plan {:arity 5 :symbol "kotoba_aiueos_app_lookup_plan"}
   'aiueos-user-elf-valid {:arity 2 :symbol "kotoba_aiueos_user_elf_valid"}
   'aiueos-user-context-build {:arity 4 :symbol "kotoba_aiueos_user_context_build"}
   ;; The kernel-selector twin of user-context-build: same interrupt frame,
   ;; entered by iret into a C function rather than into ring 3, so no user
   ;; stack argument and CS/SS are the kernel selectors.
   'aiueos-kernel-context-build {:arity 3 :symbol "kotoba_aiueos_kernel_context_build"}
   'aiueos-page-mapping-plan {:arity 5 :symbol "kotoba_aiueos_page_mapping_plan"}
   'aiueos-process-create-plan {:arity 5 :symbol "kotoba_aiueos_process_create_plan"}
   'aiueos-process-teardown-plan {:arity 5 :symbol "kotoba_aiueos_process_teardown_plan"}
   'aiueos-task-slot-plan {:arity 5 :symbol "kotoba_aiueos_task_slot_plan"}
   'aiueos-scheduler-dispatch-plan {:arity 5 :symbol "kotoba_aiueos_scheduler_dispatch_plan"}
   'aiueos-task-exit-route {:arity 5 :symbol "kotoba_aiueos_task_exit_route"}
   'aiueos-service-task-transition {:arity 5 :symbol "kotoba_aiueos_service_task_transition"}
   'aiueos-rsa2048-sha256-verify {:arity 5 :symbol "kotoba_aiueos_rsa2048_sha256_verify"}
   'aiueos-dhcp-option-u32 {:arity 3 :symbol "kotoba_aiueos_dhcp_option_u32"}
   'aiueos-dhcp-reply-valid {:arity 5 :symbol "kotoba_aiueos_dhcp_reply_valid"}
   'aiueos-ecdsa-p256-public {:arity 3 :symbol "kotoba_aiueos_ecdsa_p256_public"}
   'aiueos-ecdsa-p256-sha256-verify {:arity 5 :symbol "kotoba_aiueos_ecdsa_p256_sha256_verify"}
   'aiueos-ecdsa-p256-sign {:arity 5 :symbol "kotoba_aiueos_ecdsa_p256_sign"}
   ;; Network frame admission. The virtio-net driver owns the mechanism (queue
   ;; setup, DMA, doorbells); whether the bytes that came back are the reply it
   ;; asked for is a decision, and decisions are Kotoba objects here.
   'aiueos-net-arp-reply-valid {:arity 3 :symbol "kotoba_aiueos_net_arp_reply_valid"}
   ;; IPv4. The one's-complement checksum is a computation the header and every
   ;; protocol above it share, so it is exported on its own rather than being
   ;; duplicated inside each validator; the reply admission is the decision that
   ;; a received datagram is the one that was asked for.
   'aiueos-ipv4-checksum {:arity 2 :symbol "kotoba_aiueos_ipv4_checksum"}
   'aiueos-ipv4-icmp-reply-valid {:arity 5 :symbol "kotoba_aiueos_ipv4_icmp_reply_valid"}
   ;; TCP. The checksum is separate from the segment admission because it needs
   ;; the IPv4 pseudo-header -- source, destination, protocol and TCP length --
   ;; which the admission would otherwise have to take on trust from C.
   'aiueos-tcp-checksum-ok {:arity 4 :symbol "kotoba_aiueos_tcp_checksum_ok"}
   'aiueos-tcp-segment-valid {:arity 5 :symbol "kotoba_aiueos_tcp_segment_valid"}
   ;; PCI configuration space, the first MECHANISM to move out of C rather than
   ;; another decision. It is expressible only because `kernel-in-u32` now
   ;; exists: config access is a write to 0xCF8 followed by a READ of 0xCFC, and
   ;; with write-only port I/O the read half had no encoding at all.
   'aiueos-pci-config-read {:arity 4 :symbol "kotoba_aiueos_pci_config_read"}
   'aiueos-pci-config-write {:arity 5 :symbol "kotoba_aiueos_pci_config_write"}
   ;; X25519 (RFC 7748). Unlike every other object here it consumes a
   ;; SECRET scalar, so its timing is a security property and not merely a
   ;; performance one -- see the object's own header for what that does and
   ;; does not guarantee in this subset.
   'aiueos-x25519 {:arity 4 :symbol "kotoba_aiueos_x25519"}
   ;; Guest IME (aiueos ADR-0090). Romaji pair → kana codepoint. Hosted
   ;; JVM `aiueos.compositor.ime` does not count. C prints the vector;
   ;; this object owns the conversion. Nested if, not a map — native
   ;; word types only (temporary; not a language ceiling).
   'aiueos-ime-commit {:arity 2 :symbol "kotoba_aiueos_ime_commit"}
   ;; Guest WM (aiueos ADR-0091). Two overlapping boot-desktop rects,
   ;; z-front hit-test. Hosted `clojure -M:compositor wm` does not count.
   ;; C prints the four vectors; this object owns which surface is hit.
   ;; Nested if, word types only (temporary; not a language ceiling).
   'aiueos-wm-hit {:arity 4 :symbol "kotoba_aiueos_wm_hit"}
   ;; Guest scanout-two (aiueos ADR-0095). Bind a second virtio-gpu
   ;; scanout when two 2D resources and two enabled modes exist.
   ;; Hosted `clojure -M:compositor wm` does not count. C SET_SCANOUT
   ;; is mechanism; this object owns how many scanouts to bind.
   ;; Nested if, word types only (temporary; not a language ceiling).
   'aiueos-scanout-bind {:arity 2 :symbol "kotoba_aiueos_scanout_bind"}
   ;; Guest permission broker (aiueos ADR-0096). Clipboard/file-picker
   ;; admit. Hosted JVM compositor does not count. C copies the
   ;; clipboard scratch; this object owns whether the op is granted.
   ;; Nested if, word types only (temporary; not a language ceiling).
   'aiueos-broker-admit {:arity 2 :symbol "kotoba_aiueos_broker_admit"}
   ;; Guest session restore (aiueos ADR-0098). Packed boot session
   ;; word -> front window id. Hosted JVM compositor does not count.
   ;; C applies the restored front to wm-hit; this object owns which
   ;; front the sealed session admits. Nested if, word types only
   ;; (temporary; not a language ceiling).
   'aiueos-session-restore {:arity 1 :symbol "kotoba_aiueos_session_restore"}
   ;; MMIO mapping admission. The page-table walk stays C -- it allocates
   ;; directory slots and writes PTEs -- but WHETHER a physical range may be
   ;; mapped at all is a decision, and it was the last one still living in
   ;; paging.c's mechanism.
   'aiueos-mmio-map-admit {:arity 2 :symbol "kotoba_aiueos_mmio_map_admit"}
   ;; ACPI table admission. These tables are FIRMWARE-supplied input the kernel
   ;; otherwise takes on trust, and acpi.c was the largest file with no decision
   ;; moved out of it at all -- every checksum and bound was still C.
   ;; The checksum walks a table, so it sits in the 4096 tier; the header check
   ;; is a handful of comparisons and takes the 1024 default.
   'aiueos-acpi-checksum-ok {:arity 2 :symbol "kotoba_aiueos_acpi_checksum_ok"}
   'aiueos-acpi-table-valid {:arity 4 :symbol "kotoba_aiueos_acpi_table_valid"}
   ;; VT-d admission. vtd.c was the last kernel file with no decision moved out,
   ;; and one of its decisions is security-relevant: the IOTLB register offset is
   ;; DERIVED from a hardware-reported ECAP field and then bounds-checked, so an
   ;; unbounded value would address outside the 4 KiB register window. Deriving
   ;; an offset from untrusted input is a judgement, not a register write.
   ;;
   ;; That derivation is also where signedness bites. `(ecap >> 8) & 0x3ff` must
   ;; mask BEFORE dividing: `quot` truncates toward zero where `>>` floors, and
   ;; the C masks after shifting so sign-extended high bits are discarded rather
   ;; than folded down. Measured -- with ecap = 0xffff_ffff_ffff_ffff the
   ;; divide-first form yields offset 8 and ADMITS where the C refuses.
   ;;
   ;; A handful of bit tests -- no walk, so it takes the 1024 default tier.
   'aiueos-vtd-admit {:arity 5 :symbol "kotoba_aiueos_vtd_admit"}
   ;; MSR access. This is MECHANISM moving out of C rather than another
   ;; decision -- three files each carried their own read_msr/write_msr inline
   ;; asm pair -- but it carries a decision with it: the object admits only the
   ;; MSR indices this kernel has a reason to touch, so the set of
   ;; model-specific registers reachable at all becomes a reviewed list rather
   ;; than whatever a caller passes.
   'aiueos-msr-read {:arity 1 :symbol "kotoba_aiueos_msr_read"}
   'aiueos-msr-write {:arity 2 :symbol "kotoba_aiueos_msr_write"}
   ;; IDT gate construction. Splitting a 64-bit handler address across an
   ;; interrupt descriptor's three offset fields is bit-packing, and getting it
   ;; wrong points a vector at the wrong address -- which is a silent, exploitable
   ;; failure rather than a crash. Writes the 16-byte descriptor into a
   ;; caller-owned region, like aiueos-user-context-build.
   'aiueos-idt-gate-build {:arity 5 :symbol "kotoba_aiueos_idt_gate_build"}
   ;; Legacy 8259 shutdown. Pure port I/O, so it is expressible only because
   ;; kernel-out-u8 exists -- and it closes a latent bug in the UEFI path, which
   ;; never masked the PIC and is green only because OVMF happens to do it before
   ;; handoff (ADR-0028). Firmware-dependent correctness, now the OS's own.
   ;; The vector bases are validated rather than trusted: remapping onto the CPU
   ;; exception range is how IRQ0 masqueraded as #DF and stayed opaque.
   'aiueos-pic-disable {:arity 2 :symbol "kotoba_aiueos_pic_disable"}
   ;; CPU feature detection. Six cpuid sites in the kernel, asking three
   ;; different questions -- and only two of them are feature tests. The knowledge
   ;; of WHICH leaf and WHICH bit answers a question is the decision; leaving it
   ;; as magic numbers at a C call site is what these replace.
   'aiueos-cpu-feature-nx {:arity 0 :symbol "kotoba_aiueos_cpu_feature_nx"}
   'aiueos-cpu-feature-syscall {:arity 0 :symbol "kotoba_aiueos_cpu_feature_syscall"}
   ;; NOT a feature test: leaf 1 EBX 31:24 is the initial APIC ID, which pci.c
   ;; uses as the MSI-X message destination.
   'aiueos-cpu-apic-id {:arity 0 :symbol "kotoba_aiueos_cpu_apic_id"}
   ;; AES-128-GCM (FIPS 197 + SP 800-38D), the AEAD under every TLS 1.3 record
   ;; this OS sends or accepts. It replaces `kernel/tls_aes_gcm.c` -- 275 lines
   ;; of C holding the S-box, the key schedule, the cipher, GHASH, CTR and the
   ;; tag comparison. aiueos ADR-0015 draws the C boundary at MECHANISM, and
   ;; "are these the bytes the peer sent, under the key we agreed" is not
   ;; mechanism; it is the confidentiality and integrity decision itself.
   ;;
   ;; NOT A BOOLEAN. Like the two DHCP rows above, this returns a REASON CODE
   ;; and ZERO IS SUCCESS (1 ctx too small, 2 data too long, 3 aad too long,
   ;; 4 bad mode, 5 tag mismatch). The C it replaces returned 1 for success, so
   ;; the call sites have to change -- deliberately, because a caller writing
   ;; `if (aes128_gcm(...))` would accept exactly the records this refuses.
   ;;
   ;; One region and a mode, because the ABI admits five parameters: key,
   ;; nonce, AAD, tag and every scratch buffer live in `ctx`, and `data` is
   ;; transformed in place. The object's own header states the layout.
   'aiueos-aes128-gcm {:arity 5 :symbol "kotoba_aiueos_aes128_gcm"}
   ;; HMAC-SHA256 and HKDF-Expand-Label (RFC 5869 + RFC 8446 7.1) -- the key
   ;; schedule that turns the X25519 shared secret into the traffic keys the
   ;; row above encrypts with. It replaces four static functions in
   ;; `kernel/tls13.c` (`hmac_sha256`, `hkdf_extract`, `hkdf_expand_label` and
   ;; the HMAC half of `finish_check`). Which bytes become the traffic key is
   ;; not mechanism.
   ;;
   ;; NOT A BOOLEAN, same convention as the row above: zero is done, 1..6 name
   ;; the clause that refused.
   ;;
   ;; RFC 5869's Extract is not a mode. It is `HMAC(salt, ikm)` with the salt
   ;; in the key slot, and the C's "an empty salt means 32 zero bytes" rule is
   ;; not a rule either -- HMAC pads its key to the block, so the two produce
   ;; the same padded block. The object's contract asserts that with a vector.
   ;;
   ;; SHA-256 is inlined rather than required from `aiueos.sha256`: a namespace
   ;; that declares `(:require ...)` is a multi-module project and
   ;; `amu compile` will not package one for this target at all (measured
   ;; 2026-09-02 against amu b1fdaad2), which is why `cid-v1-admit.kotoba` has
   ;; no committed `.o` beside it.
   'aiueos-hkdf-sha256 {:arity 3 :symbol "kotoba_aiueos_hkdf_sha256"}
   ;; Qwen3.8-27B GGUF v3 admission, three objects covering what
   ;; `kernel/qwen35_runtime.c` does before a single weight is read:
   ;; container header, metadata key/value scan, tensor table. The graph they
   ;; admit is aiueos `contracts/qwen38-qwen35-runtime-v1.edn` -- 866 tensors,
   ;; 65 layers, 15 quantisation types, one artifact of 10,934,860,704 bytes.
   ;;
   ;; Three rather than one because a kernel object exports ONE symbol and
   ;; cannot call another, and because the three answer different questions:
   ;; "is this the file", "what does it say it is", "where is every tensor".
   ;;
   ;; NONE OF THE THREE IS A BOOLEAN. Each returns a REASON CODE with **zero as
   ;; the success value**, the `aiueos-dhcp-reply-valid` convention -- a caller
   ;; that writes `if (parse(...))` inverts the decision and admits exactly the
   ;; files these objects rejected. The codes are negative so that the two that
   ;; would otherwise return a useful non-negative number (a file offset) cannot
   ;; be confused with one.
   'aiueos-qwen35-gguf-header-valid
   {:arity 3 :symbol "kotoba_aiueos_qwen35_gguf_header_valid"}
   ;; The metadata scan writes its findings into a caller-owned workspace
   ;; region rather than returning them: 27 scalars and six tokenizer-array
   ;; coordinates do not fit in one word, and the ABI admits five parameters.
   'aiueos-qwen35-gguf-kv-scan
   {:arity 4 :symbol "kotoba_aiueos_qwen35_gguf_kv_scan"}
   ;; Same workspace shape, 866 fixed-size binding slots. Takes the table's own
   ;; region rather than the model's, because the tensor table is 51,242 bytes
   ;; inside a 10.9 GiB mapping and `kernel-subregion` is what makes the
   ;; narrowing checked -- the caller has already been told where it starts.
   'aiueos-qwen35-tensor-table-bind
   {:arity 5 :symbol "kotoba_aiueos_qwen35_tensor_table_bind"}
   ;; The tokenizer beside them. The three admission objects above answer
   ;; "is this the file" without ever reading a token STRING; these three read
   ;; the two arrays those coordinates name -- 248,320 vocabulary entries and
   ;; 247,587 merge rules -- and turn text into token ids and back.
   ;;
   ;; Three rather than one for the same reason as above: one exported symbol
   ;; per object, no cross-object calls. The split follows the cost. The index
   ;; is built ONCE per boot and costs a walk of both arrays; tokenize and
   ;; detokenize then run per prompt and per emitted token against tables that
   ;; are already there. Folding the build into the tokenizer would pay 4.7 MB
   ;; of string walking on every prompt.
   ;;
   ;; None of the three copies the vocabulary. The index holds a 4-byte file
   ;; offset per id and the strings stay in the model mapping, so an object
   ;; that needs the bytes of token 173,092 reads them where the GGUF put them.
   ;; Same reason-code convention: zero admits, negative refuses, and neither
   ;; tokenize nor detokenize returns a count.
   'aiueos-qwen35-vocab-index-build
   {:arity 4 :symbol "kotoba_aiueos_qwen35_vocab_index_build"}
   'aiueos-qwen35-tokenize
   {:arity 4 :symbol "kotoba_aiueos_qwen35_tokenize"}
   'aiueos-qwen35-detokenize
   {:arity 4 :symbol "kotoba_aiueos_qwen35_detokenize"}
   ;; The TLS 1.3 record layer (RFC 8446 5.2), which is `aiueos-aes128-gcm`
   ;; plus the framing that decides what the AEAD is applied TO. It replaces
   ;; `protect` and `unprotect` in aiueos `kernel/tls13.c`. The framing is
   ;; where a record layer gets exploited: the 5-byte header is the additional
   ;; authenticated data, so a length taken from the wrong place is a forgery
   ;; the AEAD accepts; the sequence number is XORed into the nonce, so a
   ;; reused sequence is a reused keystream; and the inner content type is the
   ;; last non-zero plaintext byte, so a padding strip that stops early hands
   ;; the caller the wrong record type.
   ;;
   ;; NOT A BOOLEAN, same convention as the two TLS rows above: zero is done.
   'aiueos-tls13-record {:arity 5 :symbol "kotoba_aiueos_tls13_record"}})

(def ^:private admitted-entry-prefix
  "The prefix every `kernel-object-entries` key carries, checked against the
  table rather than merely written down beside it. `package-kernel-object`
  uses it to decide whether a source is claiming a kernel object identity, so
  an entry added under a different prefix must not silently widen what gets a
  symbol without being in the table -- this throws at load instead.

  This lives in the `.clj` that the JVM actually loads. elf64.cljc already
  had the same allowlist; Clojure loads `.clj` first, so the cljc refusal
  was dead on the compiler's JVM path (amu#626 / aiueos ADR-0054)."
  (let [prefix "aiueos-"
        offenders (->> (keys kernel-object-entries)
                       (map name)
                       (remove #(str/starts-with? % prefix))
                       sort vec)]
    (when (seq offenders)
      (throw (ex-info "kernel-object-entries keys must all carry the admitted prefix"
                      {:prefix prefix :offenders offenders})))
    prefix))

(defn- le [n width]
  (object-elf/little-endian n width))

(defn- padded [bytes size]
  (object-elf/pad-to bytes size))

(defn- elf-header*
  [machine entry program-header-count section-offset section-count]
  (object-elf/encode-header
   {:type :executable
    :machine machine
    :entry entry
    :program-header-offset 64
    :program-header-count program-header-count
    :section-header-offset section-offset
    :section-header-count section-count
    :section-name-index 3}))

(defn- elf-header [entry program-header-count section-offset section-count]
  (elf-header* :x86-64 entry program-header-count section-offset section-count))

(defn- program-header [flags offset address file-size memory-size]
  (object-elf/encode-program-header
   {:type :load
    :flags flags
    :offset offset
    :virtual-address address
    :physical-address address
    :file-size file-size
    :memory-size memory-size
    :alignment page-size}))

(defn- section-header [name type flags address offset size alignment]
  (object-elf/encode-section-header
   {:name-offset name
    :type type
    :flags flags
    :address address
    :offset offset
    :size size
    :alignment alignment}))

(defn- tss-descriptor [base]
  (let [limit 103]
    [(bit-and limit 255) (bit-and (quot limit 256) 255)
     (bit-and base 255) (bit-and (quot base 256) 255)
     (bit-and (quot base 65536) 255) 0x89 0
     (bit-and (quot base 16777216) 255)
     (bit-and (quot base 4294967296) 255)
     (bit-and (quot base 1099511627776) 255)
     (bit-and (quot base 281474976710656) 255)
     (bit-and (quot base 72057594037927936) 255) 0 0 0 0]))

(defn- kernel-runtime-data [fuel context-address isr-base]
  (let [gdt-address (+ context-address kernel-gdt-offset)
        tss-address (+ context-address kernel-tss-offset)
        stack-top (+ context-address kernel-runtime-data-size)
        context (vec (concat (repeat 8 0) (le fuel 8)
                             (repeat (- kernel-image-context-size 16) 0)))
        gdt (vec (concat (le 0 8)
                         (le 0x00af9a000000ffff 8)
                         (le 0x00cf92000000ffff 8)
                         (le 0x00cff2000000ffff 8)
                         (le 0x00affa000000ffff 8)
                         (tss-descriptor tss-address)))
        gdtr (vec (concat (le (dec (count gdt)) 2) (le gdt-address 8)))
        tss (vec (concat (repeat 4 0) (le stack-top 8)
                         (repeat (- 102 12) 0) (le 104 2)))]
    (-> context
        (padded kernel-gdt-offset)
        (into gdt)
        (padded kernel-gdtr-offset)
        (into gdtr)
        (padded kernel-tss-offset)
        (into tss)
        ;; isr: the base of the interrupt entry region, which is what
        ;; `kernel-isr-entry-address` loads. Zero when the image declares no
        ;; entry -- and zero is the right answer there rather than an omission,
        ;; because an image with no entries has no region, and a guest that
        ;; asks anyway gets an address of `vector * 128` in the first page,
        ;; which is unmapped. It faults instead of jumping into the image.
        (padded interrupt-abi/context-entry-base-offset)
        (into (le (or isr-base 0) 8))
        (padded kernel-runtime-data-size))))

;; isr: the entry region an image lays down -- one fixed-size slot per vector
;; in the table, whether or not a body exists for it, because
;; `kernel-isr-entry-address` finds a slot by MULTIPLYING rather than by
;; consulting a table.
;;
;; `isr-base` is where the region starts, `artifact-address` where the
;; compiled code starts, `exports` the vector -> export map.
(defn- interrupt-entry-region [isr-base artifact-address context-address exports]
  (vec (mapcat
        (fn [vector]
          (if-let [export (get exports vector)]
            (let [address (+ isr-base (* vector interrupt-abi/entry-stride))
                  ctx-field (+ address (interrupt-abi/context-displacement-offset vector))
                  call-field (+ address (interrupt-abi/call-displacement-offset vector))
                  bytes (interrupt-abi/entry-bytes
                         {:vector vector
                          :fuel interrupt-abi/entry-fuel
                          :context-displacement (- context-address (+ ctx-field 4))
                          :call-displacement (- (+ artifact-address (:offset export))
                                                (+ call-field 4))})]
              (when-not (= interrupt-abi/body-arity (:arity export))
                (throw (ex-info "Kotoba interrupt entry body has an invalid SysV arity"
                                {:reason :isr-body-arity
                                 :vector vector :arity (:arity export)
                                 :expected interrupt-abi/body-arity})))
              (into bytes (repeat (- interrupt-abi/entry-stride (count bytes)) 0xcc)))
            interrupt-abi/absent-entry-bytes))
        (range interrupt-abi/vector-limit))))

(defn- entry-shim [main-address context-address syscall-address]
  ;; Enter on an image-owned 64 KiB stack, install the closed GDT/TSS, reload
  ;; all segment selectors, preserve the loader boot-info pointer, initialize
  ;; r9 and call the zero-arity Kotoba entry. The TSS RSP0 names the same stack.
  (let [shim-address (+ image-base text-offset)
        stack-top (+ context-address kernel-runtime-data-size)
        gdtr-address (+ context-address kernel-gdtr-offset)
        prefix (vec (concat [0xfa
                  0x48 0x8d 0x25] (le (- stack-top (+ shim-address 8)) 4)
                 [0x48 0x83 0xe4 0xf0
                  0x0f 0x01 0x15] (le (- gdtr-address (+ shim-address 19)) 4)
                 [0x6a 0x08
                  0x48 0x8d 0x05] (le 3 4)
                 [0x50 0x48 0xcb
                  0x66 0xb8 0x10 0x00
                  0x8e 0xd8 0x8e 0xc0 0x8e 0xd0
                  0x31 0xc0 0x8e 0xe0 0x8e 0xe8
                  0x66 0xb8 0x28 0x00 0x0f 0x00 0xd8
                  0x48 0x89 0x3d] (le (- (+ context-address 80) (+ shim-address 61)) 4)
                 [0x4c 0x8d 0x0d] (le (- context-address (+ shim-address 68)) 4)))
        msrs (when syscall-address
               (vec (concat
                     ;; IA32_EFER.SCE, STAR, LSTAR and FMASK. STAR selects
                     ;; kernel CS 0x08 and SYSRET user SS/CS 0x1b/0x23.
                     [0xb9 0x80 0x00 0x00 0xc0 0x0f 0x32 0x83 0xc8 0x01 0x0f 0x30
                      0xb9 0x81 0x00 0x00 0xc0 0x31 0xc0
                      0xba 0x08 0x00 0x10 0x00 0x0f 0x30
                      0xb9 0x82 0x00 0x00 0xc0 0xb8]
                     (le (bit-and syscall-address 0xffffffff) 4)
                     [0xba] (le (quot syscall-address 4294967296) 4)
                     [0x0f 0x30
                      0xb9 0x84 0x00 0x00 0xc0
                      ;; Mask TF/IF/DF, IOPL, NT and AC in kernel RFLAGS.
                      0xb8 0x00 0x77 0x04 0x00 0x31 0xd2 0x0f 0x30])))
        before-call (vec (concat prefix msrs))
        call-site (+ shim-address (count before-call))
        bytes (vec (concat before-call [0xe8]
                           (le (- main-address (+ call-site 5)) 4)
                           [0xfa 0xf4 0xeb 0xfd]))]
    (if syscall-address (padded bytes live-boot-shim-size) bytes)))

(defn- live-syscall-shim
  [shim-address context-address planner-address runtime-entry-address]
  ;; SYSCALL leaves the user RIP/RFLAGS in RCX/R11 and does not switch RSP.
  ;; Save its untrusted state before selecting the image-owned stack. Kotoba's
  ;; planner admits the complete envelope and return state before the bounded
  ;; entry receives any pointer.
  (let [slot (fn [offset next-ip]
               (le (- (+ context-address offset) next-ip) 4))
        stack-top (+ context-address kernel-runtime-data-size)
        arena (+ context-address kernel-arena-offset)
        request (+ context-address kernel-request-offset)
        cap-table (+ context-address kernel-capability-table-offset)
        prefix (vec
                (concat
                 [0x48 0x89 0x25] (slot kernel-saved-rsp-offset (+ shim-address 7))
                 [0x48 0x89 0x0d] (slot kernel-saved-rip-offset (+ shim-address 14))
                 [0x4c 0x89 0x1d] (slot kernel-saved-rflags-offset (+ shim-address 21))
                 [0x48 0x89 0x3d] (slot kernel-request-pointer-offset (+ shim-address 28))
                 [0x48 0x8d 0x25] (le (- stack-top (+ shim-address 35)) 4)
                 [0x48 0x83 0xe4 0xf0
                  0x49 0xb9] (le context-address 8)
                 [0x48 0x89 0xc7
                  0x41 0x8b 0xb1 0x10 0x01 0x00 0x00
                  0x49 0x8b 0x91 0x30 0x01 0x00 0x00
                  0x49 0x8b 0x89 0x20 0x01 0x00 0x00
                  0x4d 0x8b 0x81 0x18 0x01 0x00 0x00]))
        planner-call-site (+ shim-address (count prefix))
        through-plan (vec
                      (concat prefix [0xe8]
                              (le (- planner-address (+ planner-call-site 5)) 4)
                              [0x48 0x85 0xc0
                               ;; accepted is seven bytes after the branch.
                               0x0f 0x85 0x07 0x00 0x00 0x00
                               0x31 0xc0
                               ;; Skip the 52-byte accepted-call sequence.
                               0xe9 0x34 0x00 0x00 0x00
                               0x48 0x89 0xc6
                               0x48 0xbf] (le arena 8)
                              [0x49 0x8b 0x91 0x30 0x01 0x00 0x00
                               0x48 0x81 0xe2 0x00 0xf0 0xff 0xff
                               0x48 0xb9] (le request 8)
                              [0x49 0xb8] (le cap-table 8)))
        entry-call-site (+ shim-address (count through-plan))
        bytes (vec
               (concat through-plan [0xe8]
                       (le (- runtime-entry-address (+ entry-call-site 5)) 4)
                       [0x49 0x8b 0x89 0x20 0x01 0x00 0x00
                        0x4d 0x8b 0x99 0x28 0x01 0x00 0x00
                        ;; Whitelist arithmetic flags plus IF and force bit 1;
                        ;; IOPL/NT/RF/VM/AC never reach SYSRET.
                        0x41 0x81 0xe3 0xd5 0x0a 0x00 0x00
                        0x41 0x83 0xcb 0x02
                        0x49 0x8b 0xa1 0x18 0x01 0x00 0x00
                        0x48 0x0f 0x07]))]
    (when (> (count bytes) live-syscall-shim-size)
      (throw (ex-info "ValueRuntime SYSCALL shim exceeds its sealed slot"
                      {:bytes (count bytes) :maximum live-syscall-shim-size})))
    (padded bytes live-syscall-shim-size)))

(defn- user-entry-shim [main-address context-address]
  (let [entry-address (+ user-image-base text-offset)
        after-lea (+ entry-address 7)
        after-call (+ entry-address 12)
        after-store (+ entry-address 19)
        runtime-trampoline (+ entry-address 32)]
    (vec (concat [0x4c 0x8d 0x0d] (le (- context-address after-lea) 4)
                 [0xe8] (le (- main-address after-call) 4)
                 [0x48 0x89 0x05] (le (- context-address after-store) 4)
                 [0xf3 0x90 0xeb 0xfc]
                 (repeat 9 0x90)
                 ;; Kotoba cap-call callback: the compiler-derived bitmap has
                 ;; already admitted rsi=capability-id. rdx carries its scalar
                 ;; argument. Load the kernel-issued, domain-owned handle from
                 ;; context+80 and enter aiueos syscall 5. No ambient address or
                 ;; host import is exposed to the program.
                 [0xb8 0x05 0x00 0x00 0x00       ; mov eax,5
                  0x48 0x8b 0x7f 0x50            ; mov rdi,[rdi+80]
                  0x0f 0x05 0xc3]                ; syscall; ret
                 (repeat (- 64 44) 0x90)))))

(defn- capability-bitmap [effects]
  (reduce (fn [bitmap [_ id]]
            (update bitmap (quot id 8) bit-or (bit-shift-left 1 (mod id 8))))
          (vec (repeat 32 0))
          (filter #(= :cap/call (first %)) effects)))

(defn- artifact-fuel [artifact]
  (let [fuel (get-in artifact [:limits :fuel])
        abi-fuel (get-in artifact [:fuel-abi :initial])]
    (when-not (and (integer? fuel) (pos? fuel) (<= fuel Long/MAX_VALUE)
                   (= fuel abi-fuel))
      (throw (ex-info "ELF64 kernel packaging requires one valid sealed fuel bound"
                      {:fuel fuel :fuel-abi-initial abi-fuel})))
    fuel))

(defn package-kernel
  "Package a sealed aiueos kernel artifact as a freestanding ELF64 ET_EXEC.
  The returned byte vector has no interpreter, dynamic section, or host imports."
  [artifact]
  (when-not (artifact/valid-seal? artifact)
    (throw (ex-info "ELF64 kernel packaging requires a sealed artifact" {})))
  (when-not (= kernel-target (:target artifact))
    (throw (ex-info "ELF64 kernel packaging requires the aiueos kernel target"
                    {:target (:target artifact)})))
  (when-not (and (= :none (get-in artifact [:target-profile :runtime]))
                 (false? (get-in artifact [:target-profile :ambient-syscalls])))
    (throw (ex-info "ELF64 kernel packaging requires a freestanding profile"
                    {:target-profile (:target-profile artifact)})))
  (let [source-entry (get-in artifact [:program :entry])
        export (get-in artifact [:exports source-entry])
        planner (get-in artifact [:exports 'aiueos-value-runtime-syscall-plan])
        runtime-entry (get-in artifact [:exports 'aiueos-value-runtime-entry])]
    (when-not export
      (throw (ex-info "Kotoba kernel entry is not exported" {:entry source-entry})))
    (when (and planner runtime-entry
               (not= [5 5] [(:arity planner) (:arity runtime-entry)]))
      (throw (ex-info "ValueRuntime kernel syscall exports have invalid arity"
                      {:planner (:arity planner) :entry (:arity runtime-entry)})))
    (let [live? (boolean (and planner runtime-entry))
          entry-address (+ image-base text-offset)
          boot-size (if live? live-boot-shim-size 77)
          syscall-size (if live? live-syscall-shim-size 0)
          prefix-size (+ boot-size syscall-size)
          artifact-address (+ entry-address prefix-size)
          ;; isr: the entry region follows the compiled code, so nothing above
          ;; it moves and an image that declares no entry is byte-identical to
          ;; what it was. Its size is the WHOLE table, not the number of
          ;; bodies: `kernel-isr-entry-address` finds a slot by multiplying,
          ;; so a slot has to exist for every vector the table admits.
          isr-exports (interrupt-entry-exports artifact)
          isr-offset (align16 (+ prefix-size (count (:code artifact))))
          isr-region-size (if (seq isr-exports)
                            (* interrupt-abi/vector-limit interrupt-abi/entry-stride)
                            0)
          isr-base (when (seq isr-exports) (+ entry-address isr-offset))
          data-offset (kernel-data-offset-for (+ isr-offset isr-region-size))
          context-address (+ image-base data-offset)
          syscall-address (when live? (+ entry-address boot-size))
          boot (entry-shim (+ artifact-address (:offset export))
                           context-address syscall-address)
          syscall (when live?
                    (live-syscall-shim
                     syscall-address context-address
                     (+ artifact-address (:offset planner))
                     (+ artifact-address (:offset runtime-entry))))
          isr-region (when isr-base
                       (interrupt-entry-region isr-base artifact-address
                                               context-address isr-exports))
          text (vec (concat boot syscall (:code artifact)
                            (repeat (- isr-offset prefix-size
                                       (count (:code artifact)))
                                    0xcc)
                            isr-region))
          context (kernel-runtime-data (artifact-fuel artifact) context-address
                                       isr-base)
          names (mapv int (.getBytes "\u0000.text\u0000.data\u0000.shstrtab\u0000" "UTF-8"))
          names-offset (+ data-offset kernel-runtime-data-size)
          section-offset (+ names-offset (count names)
                            (mod (- 8 (mod (+ names-offset (count names)) 8)) 8))
          sections [(vec (repeat 64 0))
                    (section-header 1 1 0x6 entry-address text-offset (count text) 16)
                    (section-header 7 1 0x3 context-address data-offset kernel-runtime-data-size 4096)
                    (section-header 13 3 0 0 names-offset (count names) 1)]
          header (elf-header entry-address 2 section-offset (count sections))
          phdrs (concat (program-header 0x5 text-offset entry-address (count text) (count text))
                        (program-header 0x6 data-offset context-address
                                        kernel-runtime-data-size kernel-runtime-data-size))
          before-text (padded (concat header phdrs) text-offset)
          before-data (padded (concat before-text text) data-offset)
          before-sections (padded (concat before-data context names) section-offset)
          bytes (vec (concat before-sections (mapcat identity sections)))]
      {:format :elf64/v1
       :target kernel-target
       :entry :aiueos_kernel_entry
       :source-entry source-entry
       :entry-address entry-address
       :syscall-entry-address syscall-address
       :value-runtime-live? live?
       ;; isr: the manifest half. A caller that wants to check what the image
       ;; installed, or to build an IDT outside it, reads these rather than
       ;; recomputing the layout.
       :interrupt-entry-base isr-base
       :interrupt-entry-stride interrupt-abi/entry-stride
       :interrupt-entries (into (sorted-map)
                                (map (fn [[v _]]
                                       [v (+ isr-base (* v interrupt-abi/entry-stride))]))
                                isr-exports)
       :sections [:text :data :shstrtab]
       :imports []
       :interpreter nil
       :bytes bytes})))

(def ^:private aarch64-kernel-target :aarch64-aiueos-kernel-v1)

(defn- entry-shim-aarch64 [main-address context-address]
  ;; AArch64 kernel entry: set the hidden context register x7 = context, call
  ;; the zero-arity Kotoba entry, then park. (The x86-64 shim also stashes the
  ;; SysV rdi boot-info pointer; AArch64's boot-info convention is separate and
  ;; a program that needs it would take it another way -- this bare shim only
  ;; establishes the fuel/capability context.)
  (let [shim-address (+ image-base text-offset)
        bl-pc (+ shim-address 8)
        ctx-lo (bit-and context-address 0xffff)
        ctx-hi (bit-and (unsigned-bit-shift-right context-address 16) 0xffff)]
    (vec (concat
          (le (bit-or 0xd2800007 (bit-shift-left ctx-lo 5)) 4)  ; movz x7, #ctx-lo
          (le (bit-or 0xf2a00007 (bit-shift-left ctx-hi 5)) 4)  ; movk x7, #ctx-hi, lsl #16
          (le (bit-or 0x94000000
                      (bit-and (quot (- main-address bl-pc) 4) 0x03ffffff)) 4) ; bl main
          (le 0x14000000 4)))))                                 ; b . (park)

(defn package-kernel-aarch64
  "Package a sealed aiueos AArch64 kernel artifact as a freestanding ELF64
  ET_EXEC (EM_AARCH64), mirroring `package-kernel`: an entry shim establishes the
  hidden x7 context (with fuel), then calls the zero-arity Kotoba entry."
  [artifact]
  (when-not (artifact/valid-seal? artifact)
    (throw (ex-info "ELF64 kernel packaging requires a sealed artifact" {})))
  (when-not (= aarch64-kernel-target (:target artifact))
    (throw (ex-info "AArch64 ELF64 kernel packaging requires the aarch64 aiueos kernel target"
                    {:target (:target artifact)})))
  (when-not (and (= :none (get-in artifact [:target-profile :runtime]))
                 (false? (get-in artifact [:target-profile :ambient-syscalls])))
    (throw (ex-info "ELF64 kernel packaging requires a freestanding profile"
                    {:target-profile (:target-profile artifact)})))
  (let [source-entry (get-in artifact [:program :entry])
        export (get-in artifact [:exports source-entry])]
    (when-not export
      (throw (ex-info "Kotoba kernel entry is not exported" {:entry source-entry})))
    (let [entry-address (+ image-base text-offset)
          data-offset (kernel-data-offset-for (+ 16 (count (:code artifact))))
          context-address (+ image-base data-offset)
          ;; the aarch64 shim is 16 bytes (4 instructions).
          shim (entry-shim-aarch64 (+ entry-address 16 (:offset export)) context-address)
          text (into shim (:code artifact))
          context (into (vec (repeat 8 0))
                        (concat (le (artifact-fuel artifact) 8)
                                (repeat (- kernel-image-context-size 16) 0)))
          names (mapv int (.getBytes "\u0000.text\u0000.data\u0000.shstrtab\u0000" "UTF-8"))
          names-offset (+ data-offset kernel-image-context-size)
          section-offset (+ names-offset (count names)
                            (mod (- 8 (mod (+ names-offset (count names)) 8)) 8))
          sections [(vec (repeat 64 0))
                    (section-header 1 1 0x6 entry-address text-offset (count text) 16)
                    (section-header 7 1 0x3 context-address data-offset kernel-image-context-size 8)
                    (section-header 13 3 0 0 names-offset (count names) 1)]
          header (elf-header* :aarch64 entry-address 2 section-offset (count sections))
          phdrs (concat (program-header 0x5 text-offset entry-address (count text) (count text))
                        (program-header 0x6 data-offset context-address
                                        kernel-image-context-size kernel-image-context-size))
          before-text (padded (concat header phdrs) text-offset)
          before-data (padded (concat before-text text) data-offset)
          before-sections (padded (concat before-data context names) section-offset)
          bytes (vec (concat before-sections (mapcat identity sections)))]
      {:format :elf64/v1
       :target aarch64-kernel-target
       :entry :aiueos_kernel_entry
       :source-entry source-entry
       :entry-address entry-address
       :sections [:text :data :shstrtab]
       :imports []
       :interpreter nil
       :bytes bytes})))

(defn package-user
  "Package a sealed zero-arity Kotoba program as an aiueos CPL3 ELF64 image."
  [artifact]
  (when-not (artifact/valid-seal? artifact)
    (throw (ex-info "ELF64 user packaging requires a sealed artifact" {})))
  (when-not (= user-target (:target artifact))
    (throw (ex-info "ELF64 user packaging requires the aiueos user target"
                    {:target (:target artifact)})))
  ;; ValueRuntime persistence must cross aiueos' typed capability broker and
  ;; local operations need a process-owned bounded arena. runtime-v2 supplies
  ;; neither yet. Refuse even a manually sealed artifact here so the hosted C
  ;; context ABI can never become an accidental production fallback.
  (when (uses-value-runtime? artifact)
    (throw (ex-info "aiueos ValueRuntime provider is not qualified"
                    {:target user-target
                     :execution-surface :aiueos-c-free-bare-metal-v1
                     :required-transport :typed-capability-syscall})))
  (let [source-entry (get-in artifact [:program :entry])
        export (get-in artifact [:exports source-entry])]
    (when-not (and export (zero? (:arity export)))
      (throw (ex-info "aiueos process entry requires zero arguments" {:entry source-entry})))
    (let [entry-address (+ user-image-base text-offset)
          context-address (+ user-image-base data-offset)
          shim (user-entry-shim (+ entry-address 64 (:offset export)) context-address)
          text (into shim (:code artifact))
          bitmap (capability-bitmap (:effects artifact))
          callback (if (some #(= :cap/call (first %)) (:effects artifact))
                     (+ entry-address 32) 0)
          context (vec (concat (repeat 8 0) (le 512 8) bitmap
                               (le callback 8) (repeat 24 0)
                               (repeat 8 0)))
          names (mapv int (.getBytes "\u0000.text\u0000.data\u0000.shstrtab\u0000" "UTF-8"))
          names-offset (+ data-offset user-context-size)
          section-offset (+ names-offset (count names)
                            (mod (- 8 (mod (+ names-offset (count names)) 8)) 8))
          sections [(vec (repeat 64 0))
                    (section-header 1 1 0x6 entry-address text-offset (count text) 16)
                    (section-header 7 1 0x3 context-address data-offset user-context-size 8)
                    (section-header 13 3 0 0 names-offset (count names) 1)]
          header (elf-header entry-address 2 section-offset (count sections))
          phdrs (concat (program-header 0x5 text-offset entry-address (count text) (count text))
                        (program-header 0x6 data-offset context-address user-context-size user-context-size))
          before-text (padded (concat header phdrs) text-offset)
          before-data (padded (concat before-text text) data-offset)
          before-sections (padded (concat before-data context names) section-offset)]
      {:format :elf64/v1 :target user-target :entry :aiueos_process_entry
       :source-entry source-entry :entry-address entry-address
       :result-address context-address :sections [:text :data :shstrtab]
       :imports [] :interpreter nil
       :entry-contract :kotoba-sysv-context-r9-aiueos-runtime-v2
       :runtime-handle-offset 80
       :bytes (vec (concat before-sections (mapcat identity sections)))})))

(defn- rela [offset symbol type addend]
  (object-elf/encode-rela
   {:offset offset :symbol-index symbol :type type :addend addend}))

(defn- symbol-entry [name info section value size]
  (object-elf/encode-symbol
   {:name-offset name
    :info info
    :section-index section
    :value value
    :size size}))

(defn- reloc-section-header [name type flags offset size link info alignment entry-size]
  (object-elf/encode-section-header
   {:name-offset name
    :type type
    :flags flags
    :offset offset
    :size size
    :link link
    :info info
    :alignment alignment
    :entry-size entry-size}))

(defn package-kernel-object
  "Emit a linkable x86-64 ET_REL object whose public SysV probe calls the
  compiler-generated Kotoba entry with a private freestanding context.  The
  object deliberately contains no dynamic metadata or unresolved host symbol."
  [artifact]
  (when-not (artifact/valid-seal? artifact)
    (throw (ex-info "ELF64 kernel object packaging requires a sealed artifact" {})))
  (when-not (= kernel-target (:target artifact))
    (throw (ex-info "ELF64 kernel object packaging requires the aiueos kernel target"
                    {:target (:target artifact)})))
  (when-not (and (= :none (get-in artifact [:target-profile :runtime]))
                 (false? (get-in artifact [:target-profile :ambient-syscalls])))
    (throw (ex-info "ELF64 kernel object packaging requires a freestanding profile"
                    {:target-profile (:target-profile artifact)})))
  (let [source-entry (get-in artifact [:program :entry])
        ;; isr: an interrupt entry claims the object's one public symbol
        ;; before the table does. A source that declares one is an entry
        ;; object -- the C IDT builder in the transitional image installs
        ;; `kotoba_aiueos_isr_<vector>` directly -- and an object has exactly
        ;; one public symbol, so two entries in one source have no answer.
        isr-exports (interrupt-entry-exports artifact)
        _ (when (< 1 (count isr-exports))
            (throw (ex-info "Kotoba kernel object declares more than one interrupt entry"
                            {:reason :isr-object-has-one-entry
                             :vectors (vec (sort (keys isr-exports)))})))
        isr-vector (first (keys isr-exports))
        object-entry (or (when isr-vector (interrupt-abi/entry-name isr-vector))
                         (some #(when (contains? (:exports artifact) %) %)
                               (keys kernel-object-entries))
                         source-entry)
        ;; isr: `kernel-isr-entry-address` has no answer in this route, and
        ;; the refusal is scoped to what this object can REACH from its one
        ;; public symbol. The entry region and the context slot that names it
        ;; belong to the bootable image; an object's context is its own
        ;; private 80 bytes, and offset 0x148 is past the end of it. Reading
        ;; there would answer with whatever follows the object's `.data`.
        ;;
        ;; Scoped rather than whole-artifact because ONE compile produces both
        ;; forms (amu's `compile-source*` calls both packagers), and a kernel
        ;; image's `main` uses this operation to build its IDT. Refusing the
        ;; object because a sibling function used it would refuse the object
        ;; route to every image that installs an entry.
        _ (when (reaches-isr-address? artifact object-entry)
            (throw (ex-info "kernel-isr-entry-address has no answer in the object route"
                            {:reason :isr-address-needs-image
                             :entry object-entry
                             :context-slot interrupt-abi/context-entry-base-offset
                             :object-context-size context-size})))
        export (get-in artifact [:exports object-entry])
        ;; `kernel-object-entries` is the WHOLE rule for an object's public
        ;; symbol, and it is an allowlist. A source that declares an
        ;; `aiueos-*` public function and is NOT in it has no symbol of its
        ;; own, and this function does not know what that symbol should be.
        ;;
        ;; It used to take the probe's contract as the `get` default, which is
        ;; a different claim: that every unlisted object IS the probe. Three
        ;; of aiueos's `value-*` objects each compiled to a valid-looking
        ;; ET_REL exporting `kotoba_aiueos_probe`, colliding with
        ;; `kernel-probe` and with each other, and nothing in the compile said
        ;; so. The rule was then not derivable from the sources that depend on
        ;; it, precisely because the miss was silent -- amu#626, aiueos
        ;; ADR-0054, which records that every minimal source anyone wrote to
        ;; find the rule got the generic symbol and the real file did not.
        ;;
        ;; The discriminator is the `aiueos-` prefix every one of the table's
        ;; keys carries. It separates a kernel object that MEANT to be linked
        ;; under its own name from the two things that legitimately reach the
        ;; probe contract: aiueos's own `kernel-probe.kotoba`, whose entire
        ;; source is `(defn main [] 42)`, and this compiler's own codegen
        ;; tests, whose sources export helpers (`fact`) and generated loop
        ;; functions (`__kotoba_loop_1`) and never claim an aiueos name.
        ;;
        ;; Refusing is the only answer here that is not a guess, and a
        ;; colliding symbol is worse than no object: it links.
        ;; isr: a well-formed `aiueos-isr-<vector>` is admitted by the name
        ;; rule rather than by the table, which is what "prefix matching"
        ;; means here -- there is no row to add per vector. A name in that
        ;; shape that does NOT denote a vector never reaches this line:
        ;; `interrupt-entry-exports` above has already refused it.
        unlisted-aiueos-exports (->> (keys (:exports artifact))
                                     (filter #(str/starts-with? (name %) admitted-entry-prefix))
                                     (remove kernel-object-entries)
                                     (remove interrupt-abi/entry-vector)
                                     sort vec)
        contract (or (when isr-vector
                       {:arity interrupt-abi/body-arity
                        :symbol (interrupt-abi/entry-symbol isr-vector)})
                     (get kernel-object-entries object-entry)
                     (when (empty? unlisted-aiueos-exports)
                       {:arity 0 :symbol "kotoba_aiueos_probe"}))
        _ (when-not contract
            (throw (ex-info "Kotoba kernel object declares an aiueos export with no admitted symbol"
                            {:entry object-entry
                             :unlisted-exports unlisted-aiueos-exports
                             :admitted-entry-count (count kernel-object-entries)})))
        public-symbol (:symbol contract)]
    (when-not (and export (= (:arity export) (:arity contract)))
      (throw (ex-info "Kotoba kernel object entry has an invalid SysV arity"
                      {:entry object-entry :arity (:arity export)})))
    ;; lea r9,[rip+.data] (relocated); replenish this object's fuel; sub rsp,8;
    ;; call local Kotoba entry; add rsp,8; ret.
    ;;
    ;; EVERY object replenishes, unconditionally. The tiers below choose HOW
    ;; MUCH; they never choose WHETHER. That makes the budget per CALL, so an
    ;; object's fuel bound constrains one invocation and nothing wider -- which
    ;; is the only reading under which a fuel bound is a bound on work rather
    ;; than a quota on how many times the kernel may ever ask.
    ;;
    ;; It used to be conditional, and being outside the set was never a policy
    ;; anyone chose. 23 of the 57 shipped objects emitted no replenish at all
    ;; and so decremented a single 512 across the WHOLE BOOT, after which the
    ;; prologue `ud2` fires. Several of them scale with workload rather than
    ;; with boot structure -- net-arp-reply-valid is charged per received frame,
    ;; capability-plan per syscall dispatch, syscall-range-valid per LOG_WRITE,
    ;; idt-gate-build once per gate against a 256-entry IDT -- so the ceiling is
    ;; not merely low, it is reached by ordinary use and not by boot at all.
    ;; A lifetime call cap is not a fuel bound; it is a delayed trap.
    ;;
    ;; The counter is per object, not shared: in the .o path each object's
    ;; `lea …,%r9` relocates `R_X86_64_PC32` against its OWN `.data` symbol, so
    ;; every object carries a separate 80-byte context whose second quadword is
    ;; the 512 it starts life with. (The single shared context belongs to the
    ;; bootable-IMAGE path, which aiueos does not use for these.) Neighbours
    ;; never top each other up, and an earlier version of this comment claiming
    ;; they did was wrong in the unsafe direction.
    (let [sha-fuel? (= 'aiueos-sha256 object-entry)
          ;; X25519 shares RSA's 250,000,000 tier: one scalar multiplication is
          ;; 255 ladder steps of multi-limb field arithmetic, measured at
          ;; 4,815,405 bounded-memory operations. Without a replenish it spends
          ;; its 512 and hits the prologue `ud2` -- measured, not predicted:
          ;; that is exactly how it failed, as AIUEOS_EXCEPTION_FAIL
          ;; unexpected-vector (vector 6 is `ud2`).
          rsa-fuel? (contains? '#{aiueos-rsa2048-sha256-verify aiueos-x25519
                                  aiueos-ecdsa-p256-sha256-verify
                                  aiueos-ecdsa-p256-sign
                                  aiueos-ecdsa-p256-public}
                               object-entry)
          ;; Two Jacobian scalar muls plus inverses. The RSA/X25519
          ;; 250,000,000 tier is unmeasured for this object. Affine exhausted
          ;; this imm32 ceiling; Solinas Jacobian completed inside it.
          ecdsa-fuel? (= 'aiueos-ecdsa-p256-sha256-verify object-entry)
          ;; AES-128-GCM over a full 12,288-byte record. Not measured on the
          ;; machine -- COMPUTED, and said so, because every loop bound in the
          ;; object is a literal or a length and the cost is therefore closed
          ;; form rather than data-dependent.
          ;;
          ;; One GHASH multiply is 4,565 calls (16 bytes x 8 bits x a 17-call
          ;; XOR plus a 16-call shift, and the XOR is counted at its worst,
          ;; every bit set). A 12,288-byte record with a 5-byte AAD takes 770
          ;; of them -- one for the AAD block, 768 for the data, one for the
          ;; length block -- which is 3.52M. CTR adds 768 AES blocks at 646
          ;; calls apiece, 0.50M. The derived S-box and the key schedule are
          ;; ~2.3K and do not move with the record. Total 4.03M calls, or 9.4M
          ;; if the counter charges bounded-memory operations rather than
          ;; calls; the tier covers the larger of the two 26x over.
          ;;
          ;; It shares X25519's constant and is a SEPARATE ARM on purpose, the
          ;; same reason `dhcp-fuel?` is separate from `context-fuel?`:
          ;; measuring one must not silently move the other. That the two
          ;; magnitudes agree is a fact about the work (X25519's ladder was
          ;; measured at 4,815,405 bounded-memory operations), not a shared
          ;; derivation.
          ;; `aiueos-tls13-record` shares this arm, and it is the one case
          ;; here where sharing a constant is a SHARED DERIVATION rather than a
          ;; coincidence of magnitude: that object's AEAD is this object's
          ;; source, copied, and its framing adds a few hundred calls to four
          ;; million. Re-measuring one genuinely re-measures the other.
          aead-fuel? (contains? '#{aiueos-aes128-gcm aiueos-tls13-record}
                                object-entry)
          ;; HMAC-SHA256 / HKDF-Expand-Label. COMPUTED, like the arm above and
          ;; like `dhcp-fuel?`, and said so.
          ;;
          ;; Unlike `aiueos-sha256`, whose message may be 12,288 bytes, this
          ;; object's message is bounded IN THE OBJECT at 192: HMAC only ever
          ;; hashes a 64-byte padded key block plus an info string that RFC 8446
          ;; 7.1 caps at 91 bytes here. That is at most four block
          ;; compressions per hash and two hashes per call, and one compression
          ;; is ~800 calls (a 17-call prepare, a 49-call extend, 64 rounds each
          ;; carrying a 9-call register rotation, an 8-call add). Call it 7,000
          ;; with the pad-block writes and the info construction.
          ;;
          ;; It takes SHA-256's own tier rather than something tighter. 65,536
          ;; would be a 9x margin on an estimate, not a measurement, and the
          ;; failure a tight bound produces is a prologue `ud2` -- an unexpected
          ;; vector 6 that reads as a protocol bug rather than a fuel bug. The
          ;; arm is separate from `sha-fuel?` so that measuring either one
          ;; cannot silently move the other.
          hkdf-fuel? (= 'aiueos-hkdf-sha256 object-entry)
          ;; Qwen3.8 GGUF metadata scan. COMPUTED, like the two arms above,
          ;; and said so -- nothing has executed this object yet.
          ;;
          ;; The bound is NOT the admitted artifact's own shape. That file's
          ;; two tokenizer arrays hold 248,320 and 247,587 strings, and a
          ;; length-prefixed string array can only be traversed element by
          ;; element, so accepting it costs ~496,000 calls. But the object also
          ;; has to REFUSE files, and the widest refusable shape is the one
          ;; `qwen35_runtime.c`'s own `skip_value` admits: an element count of
          ;; up to 1,000,000, in each of the 50 metadata entries, when the
          ;; element type is itself a string. That is 50,000,000 traversal
          ;; steps spent before the object can say no -- a hundred times the
          ;; cost of the file it exists to accept.
          ;;
          ;; 250,000,000 is a 5x margin on that worst case. The 10,000,000 tier
          ;; below would clear the admitted artifact by 20x and `ud2` partway
          ;; through refusing a hostile one, which is the size-dependent trap
          ;; this file's other comments keep naming.
          qwen-metadata-fuel? (= 'aiueos-qwen35-gguf-kv-scan object-entry)
          ;; Qwen3.8 tensor table. COMPUTED. 866 tensor records, each matched
          ;; against 27 role literals of at most 30 bytes -- 810 comparison
          ;; calls if every candidate is exhausted -- plus the dimension, type
          ;; and extent arithmetic and the workspace writes. ~1,000,000.
          ;;
          ;; It does NOT inherit the arm above: a tensor NAME is skipped by
          ;; arithmetic rather than traversed, so a hostile length buys no
          ;; steps here, and the record count is fixed at 866 before the walk
          ;; starts. A separate arm, so that measuring either one cannot
          ;; silently move the other.
          qwen-tensor-fuel? (= 'aiueos-qwen35-tensor-table-bind object-entry)
          ;; The GPT-2 BPE index build. COMPUTED, and the computation depends
          ;; on an argument, which is why the object refuses a model window
          ;; above 16 MiB: every token and every merge string is hashed and
          ;; compared byte by byte, so this object's cost is LINEAR IN THE
          ;; WINDOW IT IS GIVEN, not in the element counts. Handed the whole
          ;; 10.9 GiB mapping instead of the 10,996,640-byte metadata prefix
          ;; it needs, no finite bound would hold; the object refuses that
          ;; instead of trapping partway through.
          ;;
          ;; Within a 16 MiB window and the ceilings the object enforces
          ;; (1,048,576 tokens, 1,048,576 merges): clearing both tables is
          ;; C1 + 3*C2 <= 8,388,608 stores; the token pass is ~16 charged
          ;; calls per id plus one FNV step per byte of the array; the merge
          ;; pass is ~55 per rule plus two hashes and up to two comparisons
          ;; over the same bytes. That is ~120,000,000 at the ceiling and
          ;; ~50,000,000 for the admitted artifact. 2,147,483,647 is ~18x the
          ;; former; it shares the ECDSA arm's constant by coincidence of
          ;; magnitude, and is a separate arm so that measuring either one
          ;; cannot silently move the other.
          qwen-index-fuel? (= 'aiueos-qwen35-vocab-index-build object-entry)
          ;; Tokenize. COMPUTED. The merge loop is quadratic in the length of
          ;; ONE pre-tokenizer chunk -- it rescans the chunk's symbol list to
          ;; find the lowest-rank adjacent pair, and there are as many merges
          ;; as symbols -- so the object refuses a chunk above 512 symbols and
          ;; an input above 32,768 bytes. Worst case is then
          ;; 512 * 98,304 = 50,331,648 scan steps (98,304 because normalising
          ;; invalid UTF-8 to U+FFFD can triple the byte count), plus the
          ;; encode and the per-symbol vocabulary lookups. ~60,000,000, so
          ;; 250,000,000 is a 4x margin.
          qwen-tokenize-fuel? (= 'aiueos-qwen35-tokenize object-entry)
          ;; Detokenize. COMPUTED. Bounded by the ids it is given (at most
          ;; 32,768) and by the output capacity it refuses to exceed (at most
          ;; 65,536 bytes), at a handful of calls each: ~1,400,000.
          qwen-detokenize-fuel? (= 'aiueos-qwen35-detokenize object-entry)
          context-fuel? (contains? '#{aiueos-user-context-build
                                     aiueos-kernel-context-build}
                                   object-entry)
          ;; 4096 rather than the plain 1024, because each of these walks a
          ;; whole frame: a checksum over a 1500-byte Ethernet payload is ~750
          ;; recursive calls at one fuel apiece, and `tcp-segment-valid` runs two
          ;; of them (IPv4 header, then the segment). 1024 would clear a small
          ;; frame and trap on a full one -- exactly the size-dependent failure
          ;; that looks like a protocol bug.
          ;; 4096 rather than the plain 1024, because each of these walks a
          ;; whole frame: a checksum over a 1500-byte Ethernet payload is ~750
          ;; recursive calls at one fuel apiece, and `tcp-segment-valid` runs two
          ;; of them (IPv4 header, then the segment). 1024 would clear a small
          ;; frame and trap on a full one -- exactly the size-dependent failure
          ;; that looks like a protocol bug.
          ;; DHCP walks the frame more times than anything above it: one
          ;; one's-complement sum over the whole UDP datagram (~576 bytes on
          ;; SLIRP = ~288 recursive steps), one over the 20-byte IPv4 header,
          ;; one options walk to prove the field parses, and one more per
          ;; option the decision needs. The options field's WORST shape is not
          ;; its typical one: a field of PAD bytes advances one byte per step,
          ;; so a 308-byte field costs 308 steps per walk rather than the
          ;; half-dozen a real server's six options cost. Five walks of that
          ;; shape plus the two checksums is ~1,900 steps.
          ;;
          ;; 65536 is a computed bound at ~34x that, not an executed
          ;; measurement -- unlike the tiers below it, and it should be
          ;; replaced by one. It shares the context tier's constant by
          ;; coincidence of magnitude, not because the two are related; it is
          ;; a separate arm so that measuring one cannot silently move the
          ;; other. It is set high deliberately: the failure a tight
          ;; bound produces is a prologue `ud2` on a differently-shaped reply,
          ;; which surfaces as an unexpected vector 6 and reads as a protocol
          ;; bug rather than a fuel bug. The all-PAD shape is exercised by
          ;; aiueos's own gate, so the bound is at least tested at its worst.
          dhcp-fuel? (contains? '#{aiueos-dhcp-reply-valid aiueos-dhcp-option-u32}
                                object-entry)
          high-fuel? (contains? '#{aiueos-user-object-journal-build
                                    aiueos-user-object-journal-valid
                                    aiueos-ipv4-checksum
                                    aiueos-ipv4-icmp-reply-valid
                                    aiueos-tcp-checksum-ok
                                    aiueos-tcp-segment-valid
                                    ;; The bounded-load primitives top out at
                                    ;; 16384, so that is the largest table this
                                    ;; can admit -- not 64 KiB, as an earlier
                                    ;; version of this comment claimed.
                                    ;;
                                    ;; 4096 is sufficient only because the object
                                    ;; walks EIGHT bytes per recursive step: the
                                    ;; natural one-byte shape costs N+2 fuel and
                                    ;; would `ud2` on a 4 KiB table, four times
                                    ;; over at the 16 KiB ceiling. Measured from
                                    ;; the disassembly, worst case is 2056 at
                                    ;; N=16383. Changing that step size without
                                    ;; changing this tier reintroduces a
                                    ;; size-dependent trap.
                                    aiueos-acpi-checksum-ok} object-entry)
          ;; The tail of the cond. 1024 is the DEFAULT, not a membership: an
          ;; object that names no tier is one whose worst legitimate call was
          ;; measured well under 1024, not one nobody has looked at.
          ;;
          ;; Measured by execution, one call each, against the largest input the
          ;; object's C callers can legitimately hand it -- flatten the `.o`,
          ;; resolve its `.data` relocation, mmap, call, read the fuel word back
          ;; out. Counting charge sites off a disassembly gets this wrong: each
          ;; object carries TWO, and the second belongs to the unreachable
          ;; `(defn main [] 0)`.
          ;;
          ;; Of the 23 objects that previously emitted no replenish, TWENTY-ONE
          ;; cost exactly 1 fuel per call -- they are a single function whose
          ;; body is a handful of comparisons, and the bounded load/store
          ;; primitives they use are inlined rather than charged. The two that
          ;; cost more:
          ;;
          ;;   net-arp-reply-valid       6   (two u16 helpers plus a u32 helper)
          ;;   service-registry-build  135   (FNV over subregions of 16, 32 and
          ;;                                  28 bytes, plus a 16-step field
          ;;                                  writer -- every bound a compile-
          ;;                                  time constant, so the cost does
          ;;                                  not move with any argument)
          ;;
          ;; 135 against 1024 is a 7.6x margin, so nothing here needs promoting
          ;; to 4096. Neither number moves with input size. net-arp-reply-valid
          ;; reads nine FIXED offsets, all below 32, and uses `length` only in
          ;; its 42..2048 guard -- measured identical at 42, at a full 1514-byte
          ;; Ethernet frame, and at the object's own 2048 maximum.
          ;; service-registry-build refuses any `length` other than 512.
          ;;
          ;; What the old default actually cost, walked down for real against
          ;; the shipped 512: the 1-fuel objects trapped on call 513,
          ;; net-arp-reply-valid on frame 86, and SERVICE-REGISTRY-BUILD ON ITS
          ;; FOURTH CALL -- three service-registry journal writes per boot, and
          ;; the fourth `ud2`s partway through leaving the sector half written.
          replenish (cond
                      ecdsa-fuel? [0x49 0xc7 0x41 0x08 0xff 0xff 0xff 0x7f] ; 2,147,483,647
                      aead-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      hkdf-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      qwen-metadata-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      qwen-tensor-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      qwen-index-fuel? [0x49 0xc7 0x41 0x08 0xff 0xff 0xff 0x7f] ; 2,147,483,647
                      qwen-tokenize-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      qwen-detokenize-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      rsa-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      sha-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      context-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x01 0x00] ; 65,536
                      dhcp-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x01 0x00] ; 65,536
                      high-fuel? [0x49 0xc7 0x41 0x08 0x00 0x10 0x00 0x00] ; 4096
                      :else [0x49 0xc7 0x41 0x08 0x00 0x04 0x00 0x00]) ; 1024
          ;; isr: an entry object's public symbol IS the interrupt entry, so
          ;; it replaces the SysV wrapper rather than sitting beside it. The
          ;; shape a linked object has to satisfy is unchanged -- one
          ;; R_X86_64_PC32 into its own `.data` and no imports (aiueos's
          ;; `verify-kotoba-kernel-object.py`) -- because the entry's
          ;; `lea r9,[rip+ ]` is that one relocation, exactly as the wrapper's
          ;; was. Only its OFFSET within the text moves, which is why the
          ;; relocation offset is computed from the ABI rather than written as
          ;; the literal 3.
          ;;
          ;; The entry's own replenish is the ABI's per-interrupt tier and not
          ;; the `replenish` chosen above: this symbol is entered by the CPU,
          ;; not called by C, and its budget is per interrupt.
          isr-prologue (when isr-vector
                         (interrupt-abi/entry-bytes
                          {:vector isr-vector
                           :fuel interrupt-abi/entry-fuel
                           :context-displacement -4
                           :call-displacement 0}))
          reloc-offset (if isr-vector
                         (interrupt-abi/context-displacement-offset isr-vector)
                         3)
          wrapper (vec (concat [0x4c 0x8d 0x0d 0 0 0 0] replenish
                               [0x48 0x83 0xec 0x08 0xe8]))
          call-end (if isr-vector
                     (+ (interrupt-abi/call-displacement-offset isr-vector) 4)
                     (+ (count wrapper) 4))
          wrapper-size (if isr-vector
                         (interrupt-abi/entry-size isr-vector)
                         (+ call-end 5))
          main-offset (+ wrapper-size (:offset export))
          call-disp (- main-offset call-end)
          text (vec (concat
                     (if isr-vector
                       ;; The call displacement is the one field the ABI could
                       ;; not know: it depends on where this packager put the
                       ;; body. Patch it rather than rebuild, so the bytes
                       ;; either side are the ABI's own.
                       (vec (concat (subvec isr-prologue 0 (- call-end 4))
                                    (le call-disp 4)
                                    (subvec isr-prologue call-end)))
                       (vec (concat wrapper (le call-disp 4)
                                    [0x48 0x83 0xc4 0x08 0xc3])))
                     (:code artifact)))
          context (vec (concat (repeat 8 0) (le 512 8)
                               (repeat (- context-size 16) 0)))
          shstr "\u0000.text\u0000.data\u0000.rela.text\u0000.symtab\u0000.strtab\u0000.shstrtab\u0000"
          shstr-bytes (mapv int (.getBytes shstr "UTF-8"))
          strtab (mapv int (.getBytes (str "\u0000" public-symbol "\u0000kotoba_source_entry\u0000") "UTF-8"))
          text-off 64
          data-off (+ text-off (count text))
          rela-off (+ data-off (count context))
          reloc (rela reloc-offset 2 2 -4) ; R_X86_64_PC32 against section symbol .data
          symtab-off (+ rela-off (count reloc))
          ;; null, local .text/.data section symbols, local source, global probe.
          ;; ELF requires every local symbol to precede the first global one.
          symbols (vec (concat (repeat 24 0)
                               (symbol-entry 0 0x03 1 0 0)
                               (symbol-entry 0 0x03 2 0 0)
                               (symbol-entry (+ 2 (count public-symbol)) 0x02 1 main-offset
                                             (count (:code artifact)))
                               ;; The public symbol owns the wrapper prefix; the
                               ;; selected Kotoba function remains a local symbol.
                               (symbol-entry 1 0x12 1 0 main-offset)))
          strtab-off (+ symtab-off (count symbols))
          shstr-off (+ strtab-off (count strtab))
          section-off (+ shstr-off (count shstr-bytes)
                         (mod (- 8 (mod (+ shstr-off (count shstr-bytes)) 8)) 8))
          header (object-elf/encode-header
                  {:type :relocatable
                   :machine :x86-64
                   :section-header-offset section-off
                   :section-header-count 7
                   :section-name-index 6})
          sections [(vec (repeat 64 0))
                    (reloc-section-header 1 1 0x6 text-off (count text) 0 0 16 0)
                    (reloc-section-header 7 1 0x3 data-off (count context) 0 0 8 0)
                    (reloc-section-header 13 4 0 rela-off (count reloc) 4 1 8 24)
                    (reloc-section-header 24 2 0 symtab-off (count symbols) 5 4 8 24)
                    (reloc-section-header 32 3 0 strtab-off (count strtab) 0 0 1 0)
                    (reloc-section-header 40 3 0 shstr-off (count shstr-bytes) 0 0 1 0)]
          before-sections (padded (concat header text context reloc symbols strtab shstr-bytes)
                                  section-off)
          bytes (vec (concat before-sections (mapcat identity sections)))]
      {:format :elf64-relocatable/v1
       :target kernel-target
       :elf-type :relocatable
       :machine :x86_64
       :abi :sysv
       :export public-symbol
       :source-entry object-entry
       :sections [:text :data :rela.text :symtab :strtab :shstrtab]
       :relocations [{:section :text :offset reloc-offset :type :r-x86-64-pc32
                      :symbol :data :addend -4}]
       :imports []
       :interpreter nil
       ;; isr: provenance, not structure. aiueos's K16 pure-native gate
       ;; classifies an object from the receipt its build writes, and its
       ;; `:toolchain-stub` class exists for exactly this shape ("an interrupt
       ;; entry, a context switch"). This field is what that build copies into
       ;; the receipt's `:stub`. The object also passes the gate's ordinary
       ;; `:kotoba-object` check unchanged -- it has Kotoba source, one global
       ;; function whose name starts `kotoba_aiueos_`, and one PC32 relocation
       ;; into its own `.data` -- so no aiueos change is required for it to be
       ;; admitted; the field lets that build say what it is rather than let
       ;; the structure imply it.
       :stub-kind (when isr-vector :interrupt-entry)
       :interrupt-vector isr-vector
       :bytes bytes})))
