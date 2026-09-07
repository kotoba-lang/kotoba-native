(ns kotoba.native.context-slots-test
  "cr3-h1 / cr3-h4 (aiueos ADR-0156): the kernel context slots the canned
  handlers and their configurators share are r9-/GDTR-relative and live in
  the RW context page, and no memory operand in emitted text names an
  absolute address inside the text itself.

  WHY THESE TESTS EXIST. Until 2026-09-06 `kernel-configure-page-fault-recovery`
  stored to the ABSOLUTE addresses 0x110100 / 0x110108, fixed on 2026-08-12
  (3726aa8) assuming the RW context page at image-base+0x10000. The packager
  had since moved the page to the first one past the text; the aiueos
  kernel's text ends at 0x11e000, so those four operands (two stores, two
  read-back compares) pointed INTO RX text. Under CR0.WP the first store
  page-faulted before the kernel's own #PF gate existed, and every QEMU boot
  triple-faulted (CR2=0x110100, error 3). The IP moved as text grew; CR2 did
  not. Nothing in this repo's suite could see it, because nothing here
  compared an emitted operand against the image's segments.

  The fixtures below rebuild that geometry -- text padded past 0x110100 -- so
  the scan is asked the question the kernel actually failed, and the
  re-hardcoded control shows the scan answering 4 for the old bytes and 0
  for the new ones on the same text."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.artifact.core :as artifact]
            [kotoba.native.elf64 :as elf64]
            [kotoba.native.interrupt-abi :as isr]
            [kotoba.native.machine-ir :as machine]
            [kotoba.native.x86-64 :as x86-64]))

;; ---------------------------------------------------------------------------
;; helpers
;; ---------------------------------------------------------------------------

(defn- le
  "Little-endian unsigned integer of WIDTH bytes at OFFSET."
  [bytes offset width]
  (reduce (fn [v i] (+ v (bit-shift-left (long (nth bytes (+ offset i))) (* 8 i))))
          0 (range width)))

(defn- le32 [n]
  (let [v (mod n 4294967296)]
    (mapv #(mod (quot v (bit-shift-left 1 (* 8 %))) 256) (range 4))))

(defn- program-headers
  "The ELF64 program headers of IMAGE: e_phoff at 0x20, e_phentsize at 0x36,
  e_phnum at 0x38; each entry p_type p_flags p_offset p_vaddr p_paddr
  p_filesz p_memsz p_align."
  [image]
  (let [phoff (le image 0x20 8)
        phentsize (le image 0x36 2)
        phnum (le image 0x38 2)]
    (mapv (fn [i]
            (let [o (+ phoff (* i phentsize))]
              {:type (le image o 4) :flags (le image (+ o 4) 4)
               :offset (le image (+ o 8) 8) :vaddr (le image (+ o 16) 8)
               :filesz (le image (+ o 32) 8) :memsz (le image (+ o 40) 8)}))
          (range phnum))))

(def ^:private pf-rx 5)   ; PF_R | PF_X
(def ^:private pf-rw 6)   ; PF_R | PF_W

(defn- segment [image flags]
  (let [found (filter #(= flags (:flags %)) (program-headers image))]
    (is (= 1 (count found)) (str "exactly one segment with p_flags " flags))
    (first found)))

(defn- sealed-kernel [code]
  (artifact/seal
   {:target :x86_64-aiueos-kernel-v1
    :target-profile {:runtime :none :ambient-syscalls false}
    :program {:entry 'main}
    :exports {'main {:offset 0 :arity 0}}
    :limits {:fuel 4096} :fuel-abi {:initial 4096}
    :code code}))

(defn- padded-to
  "CODE followed by `nop`s up to SIZE bytes and a final `ret`, so the packed
  text spans past the addresses the old absolute slots named."
  [code size]
  (conj (into (vec code) (repeat (- size (count code)) 0x90)) 0xc3))

;; Enough code that the RW page lands past 0x110000, as the aiueos kernel's
;; does (its text ends at 0x11e000). 0x1d000 bytes of text + the boot shim
;; ends past 0x11e000 and the packager puts the RW page on the next one.
(def ^:private aiueos-sized 0x1d000)

(defn absolute-text-operands
  "Every `[disp32]` memory operand in TEXT whose absolute address falls in
  [LO, HI). The encoding is a ModRM byte with mod=00 and rm=100 followed by
  the SIB byte 0x25 (no index, no base, disp32): `(bit-and modrm 0xc7)` is
  0x04 for every reg field. BASE is the address of TEXT's first byte.

  A byte scan, not a disassembly: a coincidental `.. 04 25 ..` in an
  immediate could match, which is why the address filter is part of the
  question -- an operand that names a byte inside the text is what a kernel
  under CR0.WP page-faults on, whatever bytes surround it. The number it
  returns is a count with locations, not a boolean."
  [text base lo hi]
  (vec (for [i (range (max 0 (- (count text) 6)))
             :when (and (= 0x04 (bit-and (nth text i) 0xc7))
                        (= 0x25 (nth text (inc i))))
             :let [address (le text (+ i 2) 4)]
             :when (and (<= lo address) (< address hi))]
         {:offset (+ base i) :address address})))

(defn- scan-image
  "Scan the RX segment of a packaged kernel for absolute operands into itself."
  [packaged]
  (let [image (:bytes packaged)
        {:keys [offset vaddr filesz]} (segment image pf-rx)
        text (subvec image offset (+ offset filesz))]
    {:rx [vaddr (+ vaddr filesz)]
     :hits (absolute-text-operands text vaddr vaddr (+ vaddr filesz))}))

;; The bytes `configure-page-fault-recovery-bytes` had before this series --
;; the four absolute operands at 0x110100 / 0x110108 -- kept here VERBATIM
;; as the re-hardcoded control the scan has to go red on.
(def ^:private pre-fix-configure-page-fault-recovery
  [0x4c 0x89 0xd0 0x4c 0x09 0xd8 0x48 0xa9 0xff 0x0f 0x00 0x00
   0x75 0x43 0x4d 0x85 0xd2 0x74 0x3e 0x4d 0x85 0xdb 0x74 0x39
   0x4d 0x39 0xd3 0x74 0x34 0x4c 0x89 0x14 0x25 0x00 0x01 0x11 0x00
   0x49 0x8d 0x83 0xf0 0x0f 0x00 0x00 0x48 0x89 0x04 0x25 0x08 0x01 0x11 0x00
   0x4c 0x3b 0x14 0x25 0x00 0x01 0x11 0x00 0x75 0x13
   0x48 0x3b 0x04 0x25 0x08 0x01 0x11 0x00 0x75 0x09
   0x49 0xc7 0xc2 0x01 0x00 0x00 0x00 0xeb 0x03 0x4d 0x31 0xd2])

;; ---------------------------------------------------------------------------
;; cr3-h1: the slot block is in the RW segment
;; ---------------------------------------------------------------------------

(deftest the-slot-block-lies-inside-the-rw-segment
  (doseq [[label code] [["one-byte text" [0xc3]]
                        ["30000-byte text (RW page moves to 0x9000)"
                         (padded-to [] 30000)]
                        ["aiueos-sized text (RW page past 0x110000)"
                         (padded-to [] aiueos-sized)]]]
    (testing label
      (let [packaged (elf64/package-kernel (sealed-kernel code))
            image (:bytes packaged)
            rw (segment image pf-rw)
            rx (segment image pf-rx)
            [start end] (:context-slot-block packaged)]
        (is (= (:vaddr rw) (:context-address packaged))
            "the RW segment IS the context page")
        (is (= start (+ (:vaddr rw) isr/context-slot-block-offset)))
        (is (= end (+ start isr/context-slot-block-size)))
        (is (and (<= (:vaddr rw) start) (<= end (+ (:vaddr rw) (:memsz rw))))
            "the block is inside PH1's memory size")
        (is (<= end (+ (:vaddr rw) (:filesz rw)))
            "and inside its file image, so it is zero-initialised, not merely mapped")
        (is (or (<= end (:vaddr rx)) (<= (+ (:vaddr rx) (:memsz rx)) start))
            "and disjoint from the RX segment")))))

(deftest the-aiueos-geometry-put-the-old-slots-inside-rx-text
  ;; The control for the control: with an aiueos-sized text the OLD absolute
  ;; slot 0x110100 falls inside the RX segment. If this stopped being true the
  ;; scan test below would be asking an easier question than the kernel did.
  (let [packaged (elf64/package-kernel (sealed-kernel (padded-to [] aiueos-sized)))
        rx (segment (:bytes packaged) pf-rx)
        rw (segment (:bytes packaged) pf-rw)]
    (is (< 0x110100 (+ (:vaddr rx) (:memsz rx)))
        "0x110100 is inside the text of an aiueos-sized image")
    (is (> (:vaddr rw) 0x110000)
        "and the RW page is above 0x110000, as the aiueos kernel's is")))

;; ---------------------------------------------------------------------------
;; cr3-h4: no absolute operand in emitted text names the text
;; ---------------------------------------------------------------------------

(def ^:private all-slot-operations
  {:format :kotoba.kir/v3 :entry 'main :exports ['main]
   :effects #{} :signature {:params [] :result :i64}
   :functions [{:name 'main :params [] :result :i64 :effects #{}
                :body '(+ (kernel-configure-page-fault-recovery 4096 8192)
                          (+ (kernel-configure-double-fault-ist 12288 16384)
                             (+ (kernel-page-fault-recovery-handler-address)
                                (+ (kernel-double-fault-handler-address)
                                   (kernel-rt-timer-handler-address)))))}]})

(deftest emitted-text-has-no-absolute-operand-into-itself
  (let [code (:code (x86-64/emit-program all-slot-operations))
        contains? (fn [needle] (boolean (some #{needle} (partition (count needle) 1 code))))
        packaged (elf64/package-kernel (sealed-kernel (padded-to code aiueos-sized)))
        {:keys [rx hits]} (scan-image packaged)]
    ;; evidence floor: the five sequences really are in the text we scan
    (is (contains? (vec isr/configure-page-fault-recovery-bytes)))
    (is (contains? (vec isr/configure-double-fault-ist-bytes)))
    (is (contains? (vec isr/page-fault-recovery-handler-bytes)))
    (is (contains? (vec isr/double-fault-handler-bytes)))
    (is (contains? (vec isr/rt-timer-handler-bytes)))
    (is (< 0x110100 (second rx)) "the scanned text spans the old slot addresses")
    (is (= [] hits) (str "absolute operands into RX " rx))))

(deftest the-scan-goes-red-on-a-re-hardcoded-slot
  ;; Same text, same geometry, the one configurator swapped for its pre-fix
  ;; bytes: the scan must find exactly the four operands the kernel died on.
  (let [old (padded-to pre-fix-configure-page-fault-recovery aiueos-sized)
        new (padded-to isr/configure-page-fault-recovery-bytes aiueos-sized)
        red (scan-image (elf64/package-kernel (sealed-kernel old)))
        green (scan-image (elf64/package-kernel (sealed-kernel new)))]
    (is (= 4 (count (:hits red))) (pr-str (:hits red)))
    (is (= #{0x110100 0x110108} (set (map :address (:hits red))))
        "two stores and two read-back compares, at the two old slots")
    (is (= [] (:hits green)))))

;; ---------------------------------------------------------------------------
;; the two derivations name the same slots
;; ---------------------------------------------------------------------------

(defn- mem-disp32 [opcode reg base disp]
  (into [(bit-or 0x48 (if (>= reg 8) 4 0) (if (>= base 8) 1 0))
         opcode
         (bit-or 0x80 (bit-shift-left (bit-and reg 7) 3) (bit-and base 7))]
        (le32 disp)))

(deftest configurators-and-handlers-address-the-same-slots
  (let [has? (fn [bytes needle]
               (boolean (some #{needle} (partition (count needle) 1 bytes))))
        r9 9 r15 15 rax 0 r10 10 r12 12 r13 13 r14 14]
    (testing "recoverable #PF: configurator writes [r9+slot], handler reads [r15+slot]"
      (is (has? isr/configure-page-fault-recovery-bytes
                (mem-disp32 0x89 r10 r9 isr/recovery-frame-slot)))
      (is (has? isr/configure-page-fault-recovery-bytes
                (mem-disp32 0x89 rax r9 isr/recovery-stack-top-slot)))
      (is (has? isr/page-fault-recovery-handler-bytes
                (mem-disp32 0x8b r12 r15 isr/recovery-frame-slot)))
      (is (has? isr/page-fault-recovery-handler-bytes
                (mem-disp32 0x8b r13 r15 isr/recovery-stack-top-slot)))
      (doseq [i (range isr/recovery-spill-count)]
        ;; every spill slot is both written and read back
        (let [slot (+ isr/recovery-spill-slot (* 8 i))
              stores (filter #(= (subvec (vec %) 3) (le32 slot))
                             (filter #(= 0x89 (second %))
                                     (partition 7 1 isr/page-fault-recovery-handler-bytes)))
              loads (filter #(= (subvec (vec %) 3) (le32 slot))
                            (filter #(= 0x8b (second %))
                                    (partition 7 1 isr/page-fault-recovery-handler-bytes)))]
          (is (= 1 (count stores)) (str "one store to spill " i))
          (is (= 1 (count loads)) (str "one load from spill " i)))))
    (testing "#DF: configurator writes [r9+slot], handler reads [r15+slot]"
      (is (has? isr/configure-double-fault-ist-bytes
                (mem-disp32 0x89 r10 r9 isr/double-fault-frame-slot)))
      (is (has? isr/double-fault-handler-bytes
                (mem-disp32 0x8b r12 r15 isr/double-fault-frame-slot)))
      (is (has? isr/double-fault-handler-bytes
                (mem-disp32 0x8b r13 r15 isr/double-fault-stack-slot)))
      (is (has? isr/double-fault-handler-bytes
                (mem-disp32 0x8b r14 r15 isr/double-fault-stack-top-slot))))
    (testing "timer: inc qword [rax+tick]"
      (is (has? isr/rt-timer-handler-bytes
                (mem-disp32 0xff 0 rax isr/rt-timer-tick-slot))))
    (testing "every handler derives the context from the GDTR and checks it"
      (doseq [[name bytes base] [["#PF recovery" isr/page-fault-recovery-handler-bytes r15]
                                 ["#DF" isr/double-fault-handler-bytes r15]
                                 ["timer" isr/rt-timer-handler-bytes rax]]]
        (is (has? bytes [0x0f 0x01 0x04 0x24]) (str name " sgdt [rsp]"))
        (is (has? bytes (mem-disp32 0x3b base base
                                    (- (+ isr/context-gdtr-offset 2) isr/context-gdt-offset)))
            (str name " compares GDTR.base with the context's own GDTR copy"))))
    (testing "no handler or configurator carries an absolute disp32 operand at all"
      (doseq [bytes [isr/configure-page-fault-recovery-bytes
                     isr/configure-double-fault-ist-bytes
                     isr/page-fault-recovery-handler-bytes
                     isr/double-fault-handler-bytes
                     isr/rt-timer-handler-bytes]]
        (is (= [] (absolute-text-operands bytes 0 0 0x100000000)))))))

(deftest the-machine-ir-arm-emits-the-same-sequences
  ;; `emit-program` pilots through machine-ir; the direct x86-64 arm is kept
  ;; for parity. Both must embed the shared vectors, not a private copy.
  (doseq [[form needle] [['(kernel-configure-page-fault-recovery a b)
                          isr/configure-page-fault-recovery-bytes]
                         ['(kernel-configure-double-fault-ist a b)
                          isr/configure-double-fault-ist-bytes]]]
    (let [bytes (machine/compile-expression :x86-64 '[a b] form)]
      (is (some #{(vec needle)} (partition (count needle) 1 bytes)) (str form))))
  (doseq [[form needle] [['(kernel-page-fault-recovery-handler-address)
                          isr/page-fault-recovery-handler-bytes]
                         ['(kernel-double-fault-handler-address)
                          isr/double-fault-handler-bytes]
                         ['(kernel-rt-timer-handler-address)
                          isr/rt-timer-handler-bytes]]]
    (let [bytes (machine/compile-expression :x86-64 [] form)]
      (is (some #{(vec needle)} (partition (count needle) 1 bytes)) (str form)))))
