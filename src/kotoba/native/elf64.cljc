(ns kotoba.native.elf64
  (:require [clojure.string :as str]
            [kotoba.artifact.core :as artifact]
            [kotoba.native.interrupt-abi :as interrupt-abi]
            [kotoba.object.elf64 :as object-elf]
            #?(:cljs [kotoba.kir.cljs-i64 :as i64])))

;; Mirrors `kotoba.native.aarch64`'s helper of the same name: `.getBytes` is
;; JVM-only and cljs has no `String`/`Charset`, so `TextEncoder` is the
;; UTF-8-safe peer. Every string this is applied to here is an ASCII
;; section-name or symbol-name table, so the two agree byte for byte.
(defn- utf8-bytes [s]
  #?(:clj (.getBytes ^String s "UTF-8")
     :cljs (js/Array.from (.encode (js/TextEncoder.) s))))

(def ^:private kernel-target :x86_64-aiueos-kernel-v1)
(def ^:private user-target :x86_64-aiueos-user-v1)
(def ^:private page-size 0x1000)
(def ^:private image-base 0x100000)
(def ^:private text-offset page-size)
(def ^:private data-offset (* 2 page-size))
(def ^:private kernel-data-offset (* 8 page-size))
(def ^:private x86-kernel-data-offset (* 16 page-size))
(def ^:private context-size 80)
(def ^:private kernel-image-context-size 88)
(def ^:private user-context-size 88)
(def ^:private user-image-base 0x1e0000)

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
   'aiueos-ecdsa-p256-public {:arity 3 :symbol "kotoba_aiueos_ecdsa_p256_public"}
   'aiueos-ecdsa-p256-sign {:arity 5 :symbol "kotoba_aiueos_ecdsa_p256_sign"}
   'aiueos-value-runtime-capability-grant {:arity 5 :symbol "kotoba_aiueos_value_runtime_capability_grant"}
   'aiueos-value-runtime-capability-mutate {:arity 5 :symbol "kotoba_aiueos_value_runtime_capability_mutate"}
   'aiueos-value-runtime-dispatch {:arity 5 :symbol "kotoba_aiueos_value_runtime_dispatch"}
   'aiueos-value-runtime-entry {:arity 5 :symbol "kotoba_aiueos_value_runtime_entry"}
   'aiueos-value-runtime-provider-claim {:arity 0 :symbol "kotoba_aiueos_value_runtime_provider_claim"}
   'aiueos-value-runtime-provider-complete {:arity 5 :symbol "kotoba_aiueos_value_runtime_provider_complete"}
   'aiueos-value-runtime-provider-status {:arity 2 :symbol "kotoba_aiueos_value_runtime_provider_status"}
   'aiueos-value-runtime-publish-domain {:arity 1 :symbol "kotoba_aiueos_value_runtime_publish_domain"}
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
   ;; DHCPv4 (aiueos ADR-0074, kotoba-native#57). Two entries, and the first
   ;; one on this list that does NOT return a boolean.
   ;;
   ;; `aiueos-dhcp-reply-valid` returns a REASON CODE:
   ;;
   ;;     0            admitted
   ;;     1..12        refused, and the value names which clause refused
   ;;     anything else  is not produced and must not be relied on
   ;;
   ;; **Zero is the success value.** A caller that writes `if (validate(...))`
   ;; -- the shape every other entry here invites -- inverts the decision and
   ;; admits exactly the frames the object rejected. Non-zero is never a
   ;; truthy success. Every existing boolean entry keeps its boolean; this
   ;; convention is local to the two entries below and does not generalise.
   ;;
   ;; Why not a boolean: a DHCP client has to tell a foreign transaction id
   ;; from a wrong message type from an options field whose length runs past
   ;; the end of the frame. Those are three clauses of one decision, and the
   ;; object is the only thing that knows which one fired -- deriving it in C
   ;; would put the decision back in C, which is what ADR-0015 forbids. The
   ;; codes are ordered by how far into the frame the check reaches, so a
   ;; caller comparing candidates can report the one that got furthest without
   ;; deciding anything.
   'aiueos-dhcp-reply-valid {:arity 5 :symbol "kotoba_aiueos_dhcp_reply_valid"}
   ;; The extractor. Separate because the admission's arity is spent, and
   ;; because it re-walks the options under the same bound rather than
   ;; trusting that the admission already did -- an option's location is not a
   ;; fact a caller can pass in. Returns 0 for absent, malformed, or a length
   ;; that is not the four bytes the caller asked for; presence is the
   ;; admission's decision, not this one's.
   'aiueos-dhcp-option-u32 {:arity 3 :symbol "kotoba_aiueos_dhcp_option_u32"}
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
   ;; ECDSA P-256 / SHA-256 admission for TLS 1.3 CertificateVerify.
   ;; Hashing the handshake bytes without this object is not verification.
   ;; RSA-2048 PKCS#1 is the wrong scheme (PSS or ECDSA). Affine verify
   ;; exhausted the imm32 fuel ceiling (vector 6). Jacobian + NIST Solinas
   ;; reduction completes under that ceiling (measured: RFC 6979 + live
   ;; kotobase.net CertVerify). x86 kernel images already use the 16-page
   ;; data offset; this entry does not change layout.
   'aiueos-ecdsa-p256-sha256-verify {:arity 5 :symbol "kotoba_aiueos_ecdsa_p256_sha256_verify"}
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
   ;; The value runtime's two entries whose contracts name their own symbol:
   ;; `contracts/value-runtime-syscall-plan-v1.edn` and
   ;; `contracts/value-runtime-cas-verify-v1.edn` each carry
   ;; `:native {:export "..."}`, so these are transcribed rather than chosen.
   ;;
   ;; Until they were listed, `package-kernel-object` had no entry for them and
   ;; they took the probe's contract, which is how aiueos ADR-0054 came to
   ;; measure three objects all exporting `kotoba_aiueos_probe`. Listing them
   ;; is the other half of making that table an allowlist: refusing an unknown
   ;; name is only useful if a known one can be added.
   ;;
   ;; `value-handle-plan` was deliberately NOT here while its contract carried
   ;; no `:native` block: there was no declared symbol to transcribe, and this
   ;; table does not invent one. aiueos added the block on 2026-08-20 -- the
   ;; symbol had always been required, by a hardcoded comparison in
   ;; `verify-value-handle-plan`, and was simply never declared where a
   ;; producer could read it. Now that it is, this row transcribes it.
   ;;
   ;; `value-handle-arena` IS here, and the difference is exactly that: its
   ;; contract declares `:export "kotoba_aiueos_value_handle_arena"`, so this
   ;; row transcribes a symbol rather than choosing one. Measured 2026-08-20:
   ;; with amu#625's lock landed, the arena stopped failing on
   ;; `kernel-compare-exchange-u32` and started failing on the export refusal
   ;; instead -- the second failure was there all along, behind the first.
   'aiueos-value-handle-plan
   {:arity 5 :symbol "kotoba_aiueos_value_handle_plan"}
   'aiueos-value-handle-arena
   {:arity 5 :symbol "kotoba_aiueos_value_handle_arena"}
   'aiueos-value-runtime-syscall-plan
   {:arity 5 :symbol "kotoba_aiueos_value_runtime_syscall_plan"}
   'aiueos-value-runtime-cas-verify
   {:arity 5 :symbol "kotoba_aiueos_value_runtime_cas_verify"}
   ;; `cas-verify` above compares a block against a 32-byte digest the caller
   ;; supplies, and its contract declares `:identity {:cid-version 1 :codec
   ;; :dag-cbor :multihash :sha2-256}` beside it -- a declaration, not a check.
   ;; This row transcribes the symbol from
   ;; `contracts/cid-v1-admit-v1.edn`, whose object reads those four prefix
   ;; bytes out of the CID itself, so the machine decides which CID it holds
   ;; rather than trusting that some digest it was handed is the right one.
   'aiueos-cid-v1-admit
   {:arity 5 :symbol "kotoba_aiueos_cid_v1_admit"}
   ;; The UnixFS file root beside the leaf. `cid-v1-admit` above verifies ONE
   ;; block, and SHA-256 there caps a block at 12,288 bytes; the artifacts
   ;; aiueos fetches are gigabytes. A UnixFS root names its children by CID, so
   ;; an unbounded file is verified block by block against one name. Symbol
   ;; transcribed from aiueos `contracts/unixfs-file-admit-v1.edn`.
   'aiueos-unixfs-file-admit
   {:arity 4 :symbol "kotoba_aiueos_unixfs_file_admit"}
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
   ;; The Qwen3.5 forward pass, first tranche: the arithmetic under
   ;; `matvec_range` in aiueos `kernel/qwen35_infer.c`. Three rows because a
   ;; kernel object exports ONE symbol and cannot call another, and the C has
   ;; three seams a caller can want separately -- dequantise a row, take a dot
   ;; product, or do both over a range of rows. `aiueos-qwen35-matvec` INLINES
   ;; the other two rather than calling them, so the three are three copies of
   ;; one piece of arithmetic and their contracts pin them to the same vectors.
   ;; A divergence between them is a test failure, not a discovery.
   ;;
   ;; F32, Q8_0, Q4_K and Q6_K only. The four IQ types that dominate the
   ;; shipping model (IQ3_XXS, IQ3_S, IQ4_XS, IQ2_S -- 306 of 866 tensors)
   ;; decode through codebook grids that `qwen35_quant_tables.inc` holds as
   ;; static const data, and this dialect has no rodata and no bytes literal to
   ;; put one in. Those types stay in the C.
   ;;
   ;; THE ONE OBJECT HERE WHOSE ANSWER IS A WORD rather than a verdict. It
   ;; returns the binary32 bit pattern of the dot product, sign-extended from
   ;; bit 31 the way this backend represents an f32, so a reason code cannot be
   ;; a small negative number -- every one of those is a legal float. Its
   ;; refusals are below -2^32, which no f32 pattern can reach.
   ;;
   ;; `[a a-length b b-length count]`, with both lengths required to equal
   ;; `count * 4`, so the object cannot be handed two vectors of different
   ;; extents and silently read past the shorter one.
   ;;
   ;; It is `dot_scalar` (`qwen35_infer.c:234`) and not `dot_avx2`: four
   ;; accumulators, `(s0+s1)+(s2+s3)`, then a scalar tail. THE TWO DISAGREE IN
   ;; THE C -- `dot_avx2` reduces its four lanes left to right -- so naming
   ;; which one is reproduced is part of the contract rather than a detail.
   ;;
   ;; `kernel-dot-f32` (kotoba-gmir ADR 0010, landed in this repo at `db33743`)
   ;; is the SIMD swap-in and is deliberately NOT used yet: `kotoba.verifier`
   ;; has no row for it, so an artifact that uses it is refused by
   ;; `verify-native-artifact!` with "runtime KIR operation rejected" (measured
   ;; 2026-09-02 against amu 25907a65). Its accumulation tree is the same one
   ;; and it agrees with `dot_scalar` exactly when the element count is a
   ;; multiple of eight, which every Qwen3.5 dimension is.
   'aiueos-qwen35-dot-f32 {:arity 5 :symbol "kotoba_aiueos_qwen35_dot_f32"}
   ;; `[qtype src src-length dst dst-length]`. Zero is the success value. The
   ;; element count is DERIVED from `dst-length / 4` rather than passed,
   ;; because a count and a destination length that disagree is the one shape a
   ;; bounds check cannot catch: both are inside their regions and the row is
   ;; silently truncated.
   'aiueos-qwen35-dequant-row
   {:arity 5 :symbol "kotoba_aiueos_qwen35_dequant_row"}
   ;; `[arena arena-length plan plan-length]` -- four arguments for four
   ;; regions, because `kernel-subregion` requires a BASE to be a parameter and
   ;; the ABI admits five. The caller puts weights, input, output and row
   ;; scratch in one arena and describes them in a 96-byte plan; an OFFSET may
   ;; be computed, and the offsets are 64-bit because the model mapping is
   ;; 10,934,860,704 bytes and a u32 slot would truncate every tensor past
   ;; 4 GiB. The plan also carries a ROW RANGE, which is what makes the fuel
   ;; bound finite and an SMP split expressible without a second object.
   'aiueos-qwen35-matvec {:arity 4 :symbol "kotoba_aiueos_qwen35_matvec"}
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
   'aiueos-tls13-record {:arity 5 :symbol "kotoba_aiueos_tls13_record"}
   ;; The Murakumo device-P256 worker client (aiueos ADR-0136,
   ;; `docs/device-worker-v3.md` in network-awai/cloud-murakumo-api). Three
   ;; objects covering what `kernel/device_result.c` and
   ;; `kernel/device_worker_protocol.c` do around the TLS socket: the bytes the
   ;; device SIGNS, the bytes it SENDS, and what it believes about the bytes
   ;; that come back.
   ;;
   ;; Three rather than one for the reason the qwen35 rows above give: a kernel
   ;; object exports ONE symbol and cannot call another. The split follows the
   ;; three different questions -- "what does this device assert", "how is that
   ;; framed for the wire", "what did the server just tell me" -- and the first
   ;; two are the only ones whose output is hashed.
   ;;
   ;; NONE OF THE THREE IS A BOOLEAN, and none of them uses `aiueos-aes128-gcm`'s
   ;; zero-is-success convention either. They take the `aiueos-qwen35-*` shape:
   ;; a POSITIVE result is the useful number (bytes written, or a parsed job
   ;; kind), a NEGATIVE result is a reason code, and zero is never returned. A
   ;; length and a reason code cannot share a non-negative value space.
   'aiueos-device-worker-canonical
   {:arity 4 :symbol "kotoba_aiueos_device_worker_canonical"}
   'aiueos-device-worker-body
   {:arity 5 :symbol "kotoba_aiueos_device_worker_body"}
   'aiueos-device-worker-parse
   {:arity 5 :symbol "kotoba_aiueos_device_worker_parse"}
   ;; nic: the RTL8125 2.5GbE driver. `kernel/rtl8125.c` is 306 lines of C that
   ;; reaches its device through a six-function-pointer `struct
   ;; aiueos_rtl8125_io`, and the six names below are the Kotoba objects that
   ;; replace it.
   ;;
   ;; SIX RATHER THAN ONE, and only part of that is the rule the qwen35 and
   ;; device-worker rows already give (one symbol per object, no object may
   ;; call another, no export above five arguments). The part that is specific
   ;; to a DRIVER is region provenance: `kernel-load-*` and `kernel-store-*`
   ;; take a literal, `kernel-boot-info` or an ARGUMENT as their base and
   ;; nothing else. A port that kept device state in one struct and read the
   ;; BAR address back out of it could not be written at all -- the load would
   ;; be based on a computed value. So the BAR window, each descriptor and each
   ;; frame address arrive as their own argument, and the shape of the driver
   ;; follows from that rather than from the shape of the C.
   ;;
   ;; MMIO uses the `-4k` window tier: `aiueos_map_pci_mmio(bar,4096)` maps one
   ;; page per BAR and the highest register the driver touches is RXDESC_HI at
   ;; 0xe8. The plain 512 tier would fit every offset and then refuse the
   ;; caller's own declared length. Descriptors use the plain tier with a
   ;; literal 32, which is what a descriptor is.
   ;;
   ;; RETURN CONVENTIONS, and they are deliberately not all the same:
   ;;
   ;;   identify, program, ring-build, tx-submit
   ;;       ZERO IS SUCCESS. Non-zero is the `enum aiueos_rtl8125_result` the C
   ;;       returned at that point, unchanged, so a caller transcribed from the
   ;;       C keeps its meaning.
   ;;   link-up
   ;;       a boolean, 0 or 1, like the `int` the C returned.
   ;;   rx-poll
   ;;       NON-NEGATIVE is a frame length with the four FCS bytes already
   ;;       subtracted, and zero means the descriptor is still owned by the
   ;;       device -- which is the C's `*frame_length = 0` with `OK`. NEGATIVE
   ;;       is a reason code. A length and a reason cannot share a non-negative
   ;;       value space, which is why this one object breaks the family's
   ;;       convention instead of taking an out-parameter it has no room for.
   'aiueos-rtl8125-identify
   {:arity 4 :symbol "kotoba_aiueos_rtl8125_identify"}
   'aiueos-rtl8125-link-up
   {:arity 2 :symbol "kotoba_aiueos_rtl8125_link_up"}
   'aiueos-rtl8125-ring-build
   {:arity 5 :symbol "kotoba_aiueos_rtl8125_ring_build"}
   'aiueos-rtl8125-program
   {:arity 5 :symbol "kotoba_aiueos_rtl8125_program"}
   'aiueos-rtl8125-tx-submit
   {:arity 5 :symbol "kotoba_aiueos_rtl8125_tx_submit"}
   'aiueos-rtl8125-rx-poll
   {:arity 2 :symbol "kotoba_aiueos_rtl8125_rx_poll"}})

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

(defn- entry-shim [main-address context-address]
  ;; Preserve the loader's SysV rdi boot-info pointer in context+80, then
  ;; initialize r9 and call the zero-arity Kotoba entry.
  (let [shim-address (+ image-base text-offset)
        after-store (+ shim-address 7)
        after-lea (+ shim-address 14)
        after-call (+ shim-address 19)]
    (vec (concat [0x48 0x89 0x3d] (le (- (+ context-address 80) after-store) 4)
                 [0x4c 0x8d 0x0d] (le (- context-address after-lea) 4)
                 [0xe8] (le (- main-address after-call) 4)
                 [0xfa 0xf4 0xeb 0xfd]))))

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
    (when-not (and (integer? fuel) (pos? fuel) (<= fuel #?(:clj Long/MAX_VALUE :cljs i64/max-i64))
                   (= fuel abi-fuel))
      (throw (ex-info "ELF64 kernel packaging requires one valid sealed fuel bound"
                      {:fuel fuel :fuel-abi-initial abi-fuel})))
    fuel))

;; isr: the same two helpers the JVM twin carries, for the same reasons. This
;; file's OBJECT route is the one `kotoba.compiler.nbb.native-package` serves,
;; and the two routes' objects are byte-identical -- so the entry rule has to
;; be stated on both sides or the JVM-free route emits a different object.
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
        export (get-in artifact [:exports source-entry])]
    (when-not export
      (throw (ex-info "Kotoba kernel entry is not exported" {:entry source-entry})))
    ;; isr: this twin's x86-64 kernel IMAGE lays a bare 88-byte context and no
    ;; GDT/TSS/stack -- kotoba-native ADR-0036 keeps the two files apart on
    ;; purpose, and `kotoba.compiler.nbb.native-package` already refuses this
    ;; route rather than serving a materially different image. The interrupt
    ;; entry region needs a context slot at 0x148, which is past the end of
    ;; the context this route builds.
    ;;
    ;; Refused rather than emitted with the base omitted. An image whose
    ;; entries exist but whose base slot reads zero installs gate descriptors
    ;; pointing into the first page: it boots, and the first interrupt
    ;; triple-faults. Saying so here costs a compile and saves that.
    (when (seq (interrupt-entry-exports artifact))
      (throw (ex-info "the portable elf64 twin's kernel image has no interrupt entry region"
                      {:reason :isr-image-needs-the-jvm-packager
                       :vectors (vec (sort (keys (interrupt-entry-exports artifact))))
                       :context-bytes kernel-image-context-size
                       :required-slot interrupt-abi/context-entry-base-offset})))
    (let [entry-address (+ image-base text-offset)
          context-address (+ image-base x86-kernel-data-offset)
          shim (entry-shim (+ entry-address 23 (:offset export)) context-address)
          text (into shim (:code artifact))
          context (into (vec (repeat 8 0))
                        (concat (le (artifact-fuel artifact) 8)
                                (repeat (- kernel-image-context-size 16) 0)))
          names (mapv int (utf8-bytes "\u0000.text\u0000.data\u0000.shstrtab\u0000"))
          names-offset (+ x86-kernel-data-offset kernel-image-context-size)
          section-offset (+ names-offset (count names)
                            (mod (- 8 (mod (+ names-offset (count names)) 8)) 8))
          sections [(vec (repeat 64 0))
                    (section-header 1 1 0x6 entry-address text-offset (count text) 16)
                    (section-header 7 1 0x3 context-address x86-kernel-data-offset kernel-image-context-size 8)
                    (section-header 13 3 0 0 names-offset (count names) 1)]
          header (elf-header entry-address 2 section-offset (count sections))
          phdrs (concat (program-header 0x5 text-offset entry-address (count text) (count text))
                        (program-header 0x6 x86-kernel-data-offset context-address
                                        kernel-image-context-size kernel-image-context-size))
          before-text (padded (concat header phdrs) text-offset)
          before-data (padded (concat before-text text) x86-kernel-data-offset)
          before-sections (padded (concat before-data context names) section-offset)
          bytes (vec (concat before-sections (mapcat identity sections)))]
      {:format :elf64/v1
       :target kernel-target
       :entry :aiueos_kernel_entry
       :source-entry source-entry
       :entry-address entry-address
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
          context-address (+ image-base kernel-data-offset)
          ;; the aarch64 shim is 16 bytes (4 instructions).
          shim (entry-shim-aarch64 (+ entry-address 16 (:offset export)) context-address)
          text (into shim (:code artifact))
          context (into (vec (repeat 8 0))
                        (concat (le (artifact-fuel artifact) 8)
                                (repeat (- kernel-image-context-size 16) 0)))
          names (mapv int (utf8-bytes "\u0000.text\u0000.data\u0000.shstrtab\u0000"))
          names-offset (+ kernel-data-offset kernel-image-context-size)
          section-offset (+ names-offset (count names)
                            (mod (- 8 (mod (+ names-offset (count names)) 8)) 8))
          sections [(vec (repeat 64 0))
                    (section-header 1 1 0x6 entry-address text-offset (count text) 16)
                    (section-header 7 1 0x3 context-address kernel-data-offset kernel-image-context-size 8)
                    (section-header 13 3 0 0 names-offset (count names) 1)]
          header (elf-header* :aarch64 entry-address 2 section-offset (count sections))
          phdrs (concat (program-header 0x5 text-offset entry-address (count text) (count text))
                        (program-header 0x6 kernel-data-offset context-address
                                        kernel-image-context-size kernel-image-context-size))
          before-text (padded (concat header phdrs) text-offset)
          before-data (padded (concat before-text text) kernel-data-offset)
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
          names (mapv int (utf8-bytes "\u0000.text\u0000.data\u0000.shstrtab\u0000"))
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

(def ^:private admitted-entry-prefix
  "The prefix every `kernel-object-entries` key carries, checked against the
  table rather than merely written down beside it. `package-kernel-object`
  uses it to decide whether a source is claiming a kernel object identity, so
  an entry added under a different prefix must not silently widen what gets a
  symbol without being in the table -- this throws at load instead."
  (let [prefix "aiueos-"
        offenders (->> (keys kernel-object-entries)
                       (map name)
                       (remove #(str/starts-with? % prefix))
                       sort vec)]
    (when (seq offenders)
      (throw (ex-info "kernel-object-entries keys must all carry the admitted prefix"
                      {:prefix prefix :offenders offenders})))
    prefix))

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
        ;; before the table does, and an object HAS one public symbol, so two
        ;; entries in one source have no answer here.
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
        ;; isr: `kernel-isr-entry-address` has no answer in this route. The
        ;; entry region and the context slot naming it belong to the bootable
        ;; image; an object's context is its own private 80 bytes and offset
        ;; 0x148 is past the end of it. Scoped to what the object's ONE public
        ;; symbol can reach, because one compile produces both forms and a
        ;; kernel image's `main` legitimately uses the operation.
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
        ;; rule rather than by the table. A name in that shape that does not
        ;; denote a vector never reaches here -- it was refused above.
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
          ;; The device-worker client's three objects. COMPUTED, like the AEAD
          ;; and HKDF arms above, and said so -- nothing has executed these on
          ;; a machine yet. Every loop in all three is bounded by a literal or
          ;; by a length the object itself refuses above, so the cost is closed
          ;; form rather than data-dependent.
          ;;
          ;; canonical: the widest v3 result is 716 output bytes. Each byte is
          ;; one charged call in `put-lit` / `copy-n` / `put-zeros` plus one in
          ;; `wb`; the thirteen numeric slots cost nine calls apiece to read
          ;; big-endian and about eighty-five apiece to render at seventeen
          ;; digits. That is ~2,400 calls. 65,536 is a 27x margin.
          ;;
          ;; body: the same writers over a 4,096-byte JSON buffer, with the
          ;; output-token array bounded IN THE OBJECT at 384 ids of at most six
          ;; digits. ~24,000 calls, so the same tier is a 2.7x margin -- which
          ;; is why it is a separate arm from `canonical` even though the two
          ;; constants agree today: measuring one must not silently move the
          ;; other.
          ;;
          ;; parse: a substring walk over an HTTP response the object refuses
          ;; above 8,192 bytes, times a pattern of at most 24 bytes, times the
          ;; eight fields it looks for -- 1,572,864 comparisons at the worst
          ;; shape, each a charged call. This one takes SHA-256's 10,000,000
          ;; tier: 65,536 would clear a short "job":null poll and `ud2` partway
          ;; through a real job, which is the size-dependent trap this file's
          ;; other comments keep naming.
          device-client-fuel? (contains? '#{aiueos-device-worker-canonical
                                            aiueos-device-worker-body}
                                         object-entry)
          device-parse-fuel? (= 'aiueos-device-worker-parse object-entry)
          ;; nic: the RTL8125 transmit-FIFO drain, and it is the one object in
          ;; that driver whose cost is not a handful of calls. COMPUTED.
          ;;
          ;; `rings_restart` in `kernel/rtl8125.c` sets the STOP bit and then
          ;; spins up to 300,000 times reading MCUCMD until both FIFO-empty bits
          ;; report empty. The Kotoba port keeps that literal budget, so the two
          ;; agree on when they give up; each spin is one recursive call at one
          ;; fuel apiece and the register programming either side of it is
          ;; another twenty or so, for 300,020 at the worst shape.
          ;;
          ;; 10,000,000 is a 33x margin on that. 65,536 would clear a device
          ;; whose FIFO is already empty -- which is every boot where the
          ;; firmware left the engine idle, and every run of the software model
          ;; -- and `ud2` partway through the one case the budget exists for.
          ;; That is the size-dependent trap this file's other comments name,
          ;; with the added hazard that the shape which triggers it is exactly
          ;; the shape nobody tests.
          ;;
          ;; The port also carries a `kernel-rdtsc` deadline the C does not
          ;; have, which does not change this number: the deadline can only make
          ;; the loop end EARLIER than the 300,000th spin.
          ;;
          ;; The other five objects in the family take the 1024 default. Each is
          ;; a single function whose body is comparisons and bounded
          ;; loads/stores, and the primitives are inlined rather than charged;
          ;; the largest, `ring-build`, zeroes a 32-byte descriptor with four
          ;; u64 stores and writes three fields.
          rtl8125-program-fuel? (= 'aiueos-rtl8125-program object-entry)
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
          ;; The three forward-pass objects. MEASURED, in the `kotoba.kir`
          ;; interpreter rather than on a CPU, by bisecting the fuel each
          ;; needs to return for a given input size and fitting the line. The
          ;; interpreter charges one unit per Kotoba call, which is the same
          ;; accounting the emitted prologue does, so the fits transfer -- but
          ;; a fit is not an execution, and none of these has run on hardware
          ;; at the time this arm was written. Say so rather than round up
          ;; silently: `aiueos-hkdf-sha256` passed the same interpreter and
          ;; then failed to return on the machine.
          ;;
          ;;   dot        3n + 6         n = element count, ceiling 65,536
          ;;                             -> 196,614 worst case
          ;;   dequant    19n + 5        Q4_K, the dearest of the four types
          ;;                             (F32 n+5, Q6_K 13n+5, Q8_0 10n+5)
          ;;                             -> 1,245,189 at the same ceiling
          ;;   matvec     22 per element of work + 18 per row + 39
          ;;                             -> ~65,011,751 at the object's own
          ;;                             2,097,152-element work ceiling and
          ;;                             1,048,576-row ceiling
          ;;
          ;; THE MATVEC CEILING IS WHY ITS BOUND IS FINITE. A single K16
          ;; matvec is 17,408 rows of 5,120 -- 89 million multiply-accumulates
          ;; -- and no fuel tier bounds that. The object refuses more than
          ;; 2,097,152 elements of work per call and the caller chunks, which
          ;; is also how the C's SMP split is expressed.
          ;;
          ;; Three arms rather than one, so that re-measuring any one of them
          ;; cannot silently move the other two.
          qwen-dot-fuel? (= 'aiueos-qwen35-dot-f32 object-entry)
          qwen-dequant-fuel? (= 'aiueos-qwen35-dequant-row object-entry)
          qwen-matvec-fuel? (= 'aiueos-qwen35-matvec object-entry)
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
                      device-client-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x01 0x00] ; 65,536
                      device-parse-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      rtl8125-program-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      qwen-metadata-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      qwen-tensor-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      qwen-dot-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x40 0x00] ; 4,194,304 (21x)
                      qwen-dequant-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x00 0x01] ; 16,777,216 (13x)
                      qwen-matvec-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000 (3.8x)
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
          ;; it replaces the SysV wrapper. The linked shape is unchanged --
          ;; one R_X86_64_PC32 into the object's own `.data`, no imports --
          ;; because the entry's `lea r9,[rip+ ]` is that relocation; only its
          ;; offset within the text moves, which is why the relocation offset
          ;; is computed rather than written as the literal 3. The entry's
          ;; replenish is the ABI's per-interrupt tier, not the `replenish`
          ;; chosen above: this symbol is entered by the CPU, not called.
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
                       (vec (concat (subvec isr-prologue 0 (- call-end 4))
                                    (le call-disp 4)
                                    (subvec isr-prologue call-end)))
                       (vec (concat wrapper (le call-disp 4)
                                    [0x48 0x83 0xc4 0x08 0xc3])))
                     (:code artifact)))
          context (vec (concat (repeat 8 0) (le 512 8)
                               (repeat (- context-size 16) 0)))
          shstr "\u0000.text\u0000.data\u0000.rela.text\u0000.symtab\u0000.strtab\u0000.shstrtab\u0000"
          shstr-bytes (mapv int (utf8-bytes shstr))
          strtab (mapv int (utf8-bytes (str "\u0000" public-symbol "\u0000kotoba_source_entry\u0000")))
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
       ;; isr: provenance for aiueos's K16 pure-native gate, whose
       ;; `:toolchain-stub` class exists for exactly this shape. The object
       ;; also passes that gate's ordinary `:kotoba-object` check unchanged.
       :stub-kind (when isr-vector :interrupt-entry)
       :interrupt-vector isr-vector
       :imports []
       :interpreter nil
       :bytes bytes})))
