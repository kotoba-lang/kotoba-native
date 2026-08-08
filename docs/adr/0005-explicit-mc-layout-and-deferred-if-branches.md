# ADR 0005: Introduce an explicit MC/layout boundary and defer ordinary `if` branches

**Status:** accepted and implemented  
**Date:** 2026-08-08
**Scope:** x86-64 and AArch64 intra-function branches and variable-width rewriting

## Context

`kotoba-native` already lowers checked KIR directly to x86-64/AArch64 machine
bytes and writes ELF64. The missing middle is explicit machine data: register
choice, instruction selection, branch layout, encoding, and peephole rewriting
are still largely interleaved.

The visible consequence is the size-preserving peephole invariant. Branch
displacements are embedded before the optimizer can change code size, so a
shorter replacement must be padded back to its original width.

## Decision

Introduce `kotoba.native.layout` as the first MC/layout boundary. Its reference
EDN instruction tokens are maps with closed key sets:

```clojure
{:mir/op :mir/label
 :mir/id :kotoba.mir.label/if-end-1}

{:mir/op :mir/relative-branch
 :mir/encoding :x86-64/jz-rel32
 :mir/target :kotoba.mir.label/if-else-0}
```

The semantic model is Kotoba-defined. EDN is its human/developer reference
notation and Clojure/ClojureScript is its reference implementation; these maps
are data, not executable Clojure forms.

The reference EDN bytes are not content identity. `pr-str` and JSON output must
not be hashed as IR identity. Once this machine IR participates in the content
graph, normalize the abstract value and encode deterministic DAG-CBOR for CID
calculation. JSON is an interop projection. DAG-CBOR Links carry dependency
CIDs as graph edges rather than strings.

Keep the identities distinct:

- SourceCID identifies pinned source/module bytes;
- DefCID identifies normalized checked KIR semantics, including type, effects,
  capabilities, and dependency DefCIDs;
- BuildCID identifies compiler, target, flags, and build dependencies;
- ArtifactCID identifies the emitted Wasm/native artifact and descriptor.

This native repository does not take ownership of the KIR DAG-CBOR codec.
`kotoba-kir` owns semantic identity; `artifact` owns target artifact identity.

Layout has two passes:

1. reserve each instruction's declared width and assign offsets to zero-width
   labels;
2. resolve each relative branch as
   `target - (instruction-position + instruction-size)` and require the encoder
   to produce exactly the reserved width.

The contract rejects duplicate labels, unresolved targets, unsupported
encodings, unqualified label IDs, extra keys, unknown widths, and encoder width
drift.

Migrate ordinary x86-64 and AArch64 `if` lowering first, then every audited
intra-function branch family. x86 uses next-instruction-relative `rel8`/`rel32`;
AArch64 uses the branch instruction's own address and requires four-byte-aligned
`imm14`/`imm19`/`imm26`. Nested branches share one function-local deterministic
label counter.

Do not create `kotoba-mir` or `kotoba-gmir` repositories yet. The boundary must
first be exercised inside `kotoba-native`; repository extraction happens only
after the contract has more than one producer or consumer and changes less
frequently than the backend implementation.

## Consequences

- x86-64 and AArch64 intra-function displacements are computed from final token
  sizes rather than from sizes embedded by expression emitters.
- Repeated compilation remains deterministic and existing artifact bytes do
  not change for this instruction family.
- Variant dispatch, kernel/string bounds, capability/fuel gates, division traps,
  and tail control flow now use label tokens. Calls remain final-pass relocation
  tokens rather than pre-laid bytes.
- Peephole NOP padding has been removed. Constant RHS rewrites shrink their
  windows and the layout pass recomputes downstream branches.
- Virtual registers, register allocation, and a target-independent GMIR remain
  later layers; this ADR establishes the MC/layout seam they will feed.

## Verification

`layout_test.clj` fixes the following properties:

- forward and backward signed displacements;
- displacement recomputation when an arm changes size;
- fail-closed canonical token validation;
- reserved-width enforcement;
- byte-for-byte compatibility of both ordinary `if` pilots, including their
  different PC-relative bases.
- branch-heavy parity after variable-width constant rewrites.
