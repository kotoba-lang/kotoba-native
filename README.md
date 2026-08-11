# kotoba-native

Kotoba native backend — checked KIR to x86_64/aarch64 machine code and ELF64.

**Tier**: `T2`  **Role**: `backend`

Split out of the overloaded core repos by ADR-2607266000 so that each
responsibility has exactly one owner and the dependency direction is
checkable from outside.

## Owns

- `kotoba.native.x86-64`
- `kotoba.native.aarch64`
- `kotoba.native.elf64` target layout, entry shims, and aiueos policy
- `kotoba.native.peephole`
- `kotoba.native.string-search`

## String search

`string-contains?` and `string-replace-all` are the one operator family whose
lowering lives in neither backend: both consume the SAME rewrite, from
`kotoba.native.string-search`, because the property under test is that one
program produces one value on both ISAs and two copies could drift while both
stayed green.

They lower entirely out of the four string callbacks the context ABI already
has — `string=?`, `string-concat`, `string-substring`, `string-code-point-at` —
so they cost no ABI bump, no loader change and no new value representation. The
scan walks CODE POINTS rather than bytes because `string-substring` traps on an
offset that splits one, and a trap cannot be caught; and the three helper
functions it needs are appended to the program by `emit-program`, only when a
body actually reaches one, and never exported. See ADR 0002.

## Optimization

`kotoba.codegen.layout` is the explicit MC/layout boundary. Its closed
reference EDN projection uses qualified keys and qualified label IDs:

```clojure
{:mir/op :mir/label
 :mir/id :kotoba.mir.label/if-end-1}

{:mir/op :mir/relative-branch
 :mir/encoding :x86-64/jz-rel32
 :mir/target :kotoba.mir.label/if-else-0}
```

Layout is two-pass: labels receive byte offsets first, then every relative
branch receives `target - (position + instruction-size)`. Duplicate labels,
unknown targets, unknown encodings, non-qualified IDs, extra token keys, and
encoder width drift all fail closed.

All audited x86-64 and AArch64 intra-function branch families now use this
boundary: ordinary conditionals, variant dispatch, kernel/string bounds,
capability and fuel gates, signed-division traps, and tail control flow.
Calls and tail-self relocation are resolved by the same final backend pass.
No optimizer therefore depends on a displacement baked before final layout.

The first rewrite materializes a constant right operand directly into the
scratch register (`rcx` / `x1`), dropping the spill-and-reload round trip that
protects the accumulator when the right operand needs it. Recognition is on
the KIR **form**, never on emitted bytes — matching byte patterns in an
undelimited instruction stream would rewrite immediates that happen to spell
an opcode.

The first variable-width rewrite reclaims the removed spill/reload bytes:
x86-64 constant RHS materialization is 10 bytes and AArch64 is 16 bytes, with
no architectural NOP padding. Final layout recomputes every affected branch.

`kotoba-gmir` now owns the closed target-independent GMIR contract and
`kotoba-mir` owns target selection plus explicit virtual/physical register
state and deterministic allocation, including liveness-minimal straight-line
call frames, parallel function-entry assignment for four live scalar
parameters, and the explicit all-vreg fallback at five-live-parameter pressure.
`kotoba.native.machine-ir` consumes those
contracts and owns only the bounded KIR-to-GMIR producer, physical MC lowering,
and x86-64/AArch64 encoding. Register exhaustion is represented by bounded MIR
frame slots and encoded here as target stack-frame load/store instructions.
Final layout and the allocated MC v2/v3 schemas are consumed from
`kotoba-codegen`.
The scalar/control subset is selected by the production emitters and covers
integer/boolean literals, up to five parameters, lexical `let`, `+`, `-`, `*`,
`quot`, bitwise operations, signed comparisons, scalar predicates, ordered
word shifts, signed/unsigned 32-bit wrapping operations, f64 arithmetic,
ordered/unordered f64 comparisons, f64 bit-pattern conversions and unary
abs/neg/sqrt operations, ordered non-empty
`do`, and nested tail `if`, with deterministic spilling. `bit-not`, `bool-not`,
and the i32 family are target-neutral compositions over constants, arithmetic,
comparisons, and the three portable shift instructions. `do` keeps
every intermediate expression in source order, including unused operations
that may trap; only its final value is returned. When that final expression is
tail control, `do` delegates it to tail lowering after emitting every scalar
prefix, so both arms return directly without a synthetic merge. Other typed KIR
expression families remain on the established emitter and migrate incrementally.
Native f64 values stay as their IEEE-754 bit patterns in the general-register
IR; selected instructions alone move them through the target FP bank, so GMIR
does not acquire target register classes.

Non-escaping fixed records whose fields are only `:i64` or `:bool` use scalar
replacement before GMIR. Construction evaluates every field in declaration
order, bindings retain an ordered SSA bundle, projection selects one scalar,
and record-valued `if` emits one phi per field. Acyclic field transport reaches
the existing parallel-copy scheduler with no allocation or phi frame. Escaping,
nested, and non-scalar-field records remain on the established boxed/flattened
path until their ABI is migrated explicitly.

Non-escaping sealed variants whose case payloads are only `:i64` or `:bool`
use the same extracted path without a stack aggregate. Construction creates an
internal tag-and-payload SSA bundle, variant-valued `if` joins it with two
phis, and `variant-match` becomes target-neutral tag comparison CFG while
binding the payload register only in the selected source branch. Payload
evaluation remains exactly once. Variant parameters/results, nested or
non-scalar payloads, mismatched schemas, and bare escaping variant values stay
on the established legacy path.

Function-boundary aggregates are described by the versioned portable contract
in `resources/aggregate-abi.edn`. The established record ABI remains a single
context-owned pair-chain handle with a 4,096-cell execution bound. Extracted
scalar calls are admitted by ABI v2: GMIR/MIR/MC v3 own a module of independent
functions, and a call-containing function backs every vreg with its own bounded
frame. Arguments load in parallel from stable slots into the five target ABI
registers, every allocator register may be clobbered, and the return register is
captured before later use. x86-64 adds an eight-byte call-alignment pad;
AArch64 call functions save and restore FP/LR. The correctness-first all-vreg
policy is deliberately conservative and can later be replaced by liveness-only
spills without changing the v3 call contract.

Extracted record and variant boundaries remain held. Scalar-call admission does
not admit pair-chain handles, variants, nested aggregates, indirect calls,
varargs, or external linkage, and it is not a Rust-parity claim.

Value-position scalar `if` uses GMIR/MIR v2 phi values. Each branch reaches an
explicit predecessor exit. Single- and multi-phi joins lower through MIR's
deterministic parallel-copy scheduler: acyclic edges use zero phi frame bytes,
while cycles share one temporary slot. Final layout resolves all resulting
branches. Unselected branches do not execute, including trapping operations.

`kotoba-object` owns the target-neutral ELF64 record encoders. This repository
supplies the target-specific section layout, virtual addresses, relocation
requests, entry shims, and runtime/capability policy; it no longer carries a
second implementation of ELF headers, symbols, or RELA records.

`kotoba.native.macho/encode-text-object` is the single native integration path
from shared typed relocation requests to ARM64/x86-64 Mach-O section records;
it validates target and section ownership before `kotoba-object` packs bytes.

## Representations and identity

The EDN maps above are the developer/reference notation for the abstract
instruction data. They are not identity bytes and must never be hashed through
`pr-str`. JSON may project the same abstract model for tooling, but is likewise
not authoritative.

Content identity is computed from normalized abstract values encoded as
deterministic DAG-CBOR, with IPLD links for dependency CIDs. The implementation
lives at the current authority boundary: the `kotoba-lang` language contract
provides DefCID and `artifact` provides SourceCID, BuildCID, and ArtifactCID.
`kotoba-kir` owns the checked IR model but does not introduce a second DefCID
codec. This native repository consumes those contracts rather than defining
another codec.

## Does not own

- parse .kotoba source
- own language semantics
- require Rust in the core path

## Depends on

- `kotoba-lang/kotoba-kir`
- `kotoba-lang/kotoba-gmir`
- `kotoba-lang/kotoba-mir`
- `kotoba-lang/kotoba-codegen`
- `kotoba-lang/kotoba-object`
- `kotoba-lang/artifact`

## Test

```bash
clojure -M:test
```
