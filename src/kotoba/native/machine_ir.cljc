(ns kotoba.native.machine-ir
  "Closed pilot contract for GMIR -> target MIR -> allocated MC data.

  The existing production emitters are migrated incrementally. This namespace
  makes the missing layers explicit without pretending arbitrary KIR is already
  covered: the admitted integer/control subset is closed and every unknown op,
  use-before-definition, register exhaustion, or malformed label fails closed."
  (:require [kotoba.native.layout :as layout]))

(def targets #{:x86-64 :aarch64})

(def ^:private physical-registers
  {:x86-64 [:x86-64/rax :x86-64/rcx :x86-64/rdx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3]})

(defn vreg [n]
  (when-not (and (integer? n) (not (neg? n)))
    (throw (ex-info "virtual register index must be non-negative"
                    {:phase :gmir :index n})))
  (keyword "kotoba.gmir.vreg" (str n)))

(defn- vreg? [x]
  (and (keyword? x) (= "kotoba.gmir.vreg" (namespace x))))

(defn- label? [x]
  (and (keyword? x) (some? (namespace x))))

(defn- reject! [phase problem instruction]
  (throw (ex-info (str "machine IR rejected: " (name problem))
                  {:phase phase :problem problem :instruction instruction})))

(def ^:private gmir-keysets
  {:gmir/argument #{:gmir/op :gmir/dst :gmir/index}
   :gmir/constant #{:gmir/op :gmir/dst :gmir/value}
   :gmir/add #{:gmir/op :gmir/dst :gmir/left :gmir/right}
   :gmir/label #{:gmir/op :gmir/id}
   :gmir/branch-zero #{:gmir/op :gmir/test :gmir/target}
   :gmir/jump #{:gmir/op :gmir/target}
   :gmir/return #{:gmir/op :gmir/value}})

(defn validate-gmir!
  "Validate and return a closed `{:gmir/version 1 :gmir/instructions [...]}`."
  [program]
  (when-not (and (map? program)
                 (= #{:gmir/version :gmir/instructions} (set (keys program)))
                 (= 1 (:gmir/version program))
                 (vector? (:gmir/instructions program)))
    (reject! :gmir :non-canonical-program program))
  (doseq [instruction (:gmir/instructions program)]
    (let [op (:gmir/op instruction)]
      (when-not (= (get gmir-keysets op) (set (keys instruction)))
        (reject! :gmir :non-canonical-instruction instruction))
      (doseq [r (keep instruction [:gmir/dst :gmir/left :gmir/right
                                    :gmir/test :gmir/value])]
        (when (and (not= op :gmir/constant) (not (vreg? r)))
          (reject! :gmir :invalid-virtual-register instruction)))
      (when (and (= op :gmir/constant) (not (integer? (:gmir/value instruction))))
        (reject! :gmir :constant-not-integer instruction))
      (when (and (= op :gmir/argument)
                 (not (and (integer? (:gmir/index instruction))
                           (not (neg? (:gmir/index instruction))))))
        (reject! :gmir :argument-index-invalid instruction))
      (when (contains? #{:gmir/label :gmir/branch-zero :gmir/jump} op)
        (let [id (if (= op :gmir/label) (:gmir/id instruction) (:gmir/target instruction))]
          (when-not (label? id) (reject! :gmir :invalid-label instruction))))))
  program)

(defn select-target
  "Instruction-select the closed GMIR subset, preserving virtual registers."
  [target program]
  (when-not (contains? targets target)
    (reject! :mir :unsupported-target {:target target}))
  (validate-gmir! program)
  {:mir/version 1
   :mir/target target
   :mir/instructions
   (mapv (fn [instruction]
           (reduce-kv (fn [out k v]
                        (assoc out
                               (case k
                                 :gmir/op :mir/op
                                 :gmir/dst :mir/dst
                                 :gmir/index :mir/index
                                 :gmir/value :mir/value
                                 :gmir/left :mir/left
                                 :gmir/right :mir/right
                                 :gmir/id :mir/id
                                 :gmir/test :mir/test
                                 :gmir/target :mir/target)
                               (if (= k :gmir/op)
                                 (keyword "mir" (name v))
                                 v)))
                      {} instruction))
         (:gmir/instructions program))})

(defn- sources [instruction]
  (keep instruction [:mir/left :mir/right :mir/test :mir/value]))

(defn- last-uses [instructions]
  (reduce-kv (fn [uses index instruction]
               (reduce #(assoc %1 %2 index) uses (filter vreg? (sources instruction))))
             {} instructions))

(defn allocate-registers
  "Deterministic minimal allocator for the pilot MIR subset.

  It uses the target's ordered scratch set and frees a virtual register after
  its last source use. Spilling is intentionally not implicit in v1."
  [{:mir/keys [version target instructions] :as program}]
  (when-not (and (= 1 version) (contains? targets target) (vector? instructions))
    (reject! :regalloc :non-canonical-program program))
  (let [last-use (last-uses instructions)
        registers (get physical-registers target)]
    (loop [index 0, remaining instructions, assigned {}, free registers, out []]
      (if-let [instruction (first remaining)]
        (let [srcs (filter vreg? (sources instruction))]
          (doseq [source srcs]
            (when-not (contains? assigned source)
              (reject! :regalloc :use-before-definition instruction)))
          (let [dst (:mir/dst instruction)
                [assigned free]
                (if (vreg? dst)
                  (do
                    (when (contains? assigned dst)
                      (reject! :regalloc :multiple-definition instruction))
                    (when-not (seq free)
                      (reject! :regalloc :spill-required instruction))
                    [(assoc assigned dst (first free)) (vec (rest free))])
                  [assigned free])
                allocated (reduce-kv
                           (fn [m k v] (assoc m k (if (vreg? v) (get assigned v) v)))
                           {} instruction)
                expired (->> assigned keys
                             (filter #(= index (get last-use %)))
                             (sort-by str))
                free (into free (map assigned expired))
                assigned (apply dissoc assigned expired)]
            (recur (inc index) (next remaining) assigned (vec free)
                   (conj out allocated))))
        {:mir/version 1 :mir/target target :mir/registers :physical
         :mir/instructions out}))))

(defn lower-mc
  "Lower allocated MIR to explicit MC instruction/layout data.

  Instruction bytes remain owned by the target encoders. Branches become the
  same layout tokens used by production backends, so PC-relative values cannot
  be baked before final sizes are known."
  [{:mir/keys [target registers instructions] :as program}]
  (when-not (= :physical registers)
    (reject! :mc :registers-not-allocated program))
  {:mc/version 1
   :mc/target target
   :mc/instructions
   (mapv (fn [{:mir/keys [op id target] :as instruction}]
           (case op
             :mir/label (layout/label id)
             :mir/branch-zero
             (layout/relative-branch
              (if (= :x86-64 (:mir/target program))
                :x86-64/jz-rel32
                :aarch64/cbz-x0-imm19)
              target)
             :mir/jump
             (layout/relative-branch
              (if (= :x86-64 (:mir/target program))
                :x86-64/jmp-rel32
                :aarch64/b-imm26)
              target)
             (into {:mc/op :mc/instruction
                    :mc/encoding (keyword (name (:mir/target program)) (name op))}
                   (remove (fn [[k _]] (= k :mir/op)) instruction))))
         instructions)})

(defn compile-gmir [target program]
  (->> program (select-target target) allocate-registers lower-mc))
