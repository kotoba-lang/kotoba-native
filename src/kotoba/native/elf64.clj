(ns kotoba.native.elf64
  (:require [kotoba.artifact.core :as artifact]
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
   'aiueos-cpu-apic-id {:arity 0 :symbol "kotoba_aiueos_cpu_apic_id"}})

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

(defn- kernel-runtime-data [fuel context-address]
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
        (padded kernel-runtime-data-size))))

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
          data-offset (kernel-data-offset-for (+ prefix-size (count (:code artifact))))
          context-address (+ image-base data-offset)
          syscall-address (when live? (+ entry-address boot-size))
          boot (entry-shim (+ artifact-address (:offset export))
                           context-address syscall-address)
          syscall (when live?
                    (live-syscall-shim
                     syscall-address context-address
                     (+ artifact-address (:offset planner))
                     (+ artifact-address (:offset runtime-entry))))
          text (vec (concat boot syscall (:code artifact)))
          context (kernel-runtime-data (artifact-fuel artifact) context-address)
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
          names (mapv int (.getBytes " .text .data .shstrtab " "UTF-8"))
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
        object-entry (or (some #(when (contains? (:exports artifact) %) %)
                               (keys kernel-object-entries))
                         source-entry)
        export (get-in artifact [:exports object-entry])
        contract (get kernel-object-entries object-entry {:arity 0 :symbol "kotoba_aiueos_probe"})
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
          rsa-fuel? (contains? '#{aiueos-rsa2048-sha256-verify aiueos-x25519}
                               object-entry)
          context-fuel? (contains? '#{aiueos-user-context-build
                                     aiueos-kernel-context-build}
                                   object-entry)
          ;; 4096 rather than the plain 1024, because each of these walks a
          ;; whole frame: a checksum over a 1500-byte Ethernet payload is ~750
          ;; recursive calls at one fuel apiece, and `tcp-segment-valid` runs two
          ;; of them (IPv4 header, then the segment). 1024 would clear a small
          ;; frame and trap on a full one -- exactly the size-dependent failure
          ;; that looks like a protocol bug.
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
                      rsa-fuel? [0x49 0xc7 0x41 0x08 0x80 0xb2 0xe6 0x0e] ; 250,000,000
                      sha-fuel? [0x49 0xc7 0x41 0x08 0x80 0x96 0x98 0x00] ; 10,000,000
                      context-fuel? [0x49 0xc7 0x41 0x08 0x00 0x00 0x01 0x00] ; 65,536
                      high-fuel? [0x49 0xc7 0x41 0x08 0x00 0x10 0x00 0x00] ; 4096
                      :else [0x49 0xc7 0x41 0x08 0x00 0x04 0x00 0x00]) ; 1024
          wrapper (vec (concat [0x4c 0x8d 0x0d 0 0 0 0] replenish
                               [0x48 0x83 0xec 0x08 0xe8]))
          call-end (+ (count wrapper) 4)
          wrapper-size (+ call-end 5)
          main-offset (+ wrapper-size (:offset export))
          call-disp (- main-offset call-end)
          text (vec (concat wrapper (le call-disp 4)
                            [0x48 0x83 0xc4 0x08 0xc3]
                            (:code artifact)))
          context (vec (concat (repeat 8 0) (le 512 8)
                               (repeat (- context-size 16) 0)))
          shstr "\u0000.text\u0000.data\u0000.rela.text\u0000.symtab\u0000.strtab\u0000.shstrtab\u0000"
          shstr-bytes (mapv int (.getBytes shstr "UTF-8"))
          strtab (mapv int (.getBytes (str "\u0000" public-symbol "\u0000kotoba_source_entry\u0000") "UTF-8"))
          text-off 64
          data-off (+ text-off (count text))
          rela-off (+ data-off (count context))
          reloc (rela 3 2 2 -4) ; R_X86_64_PC32 against section symbol .data
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
       :relocations [{:section :text :offset 3 :type :r-x86-64-pc32
                      :symbol :data :addend -4}]
       :imports []
       :interpreter nil
       :bytes bytes})))
