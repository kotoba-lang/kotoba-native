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
state and deterministic allocation. `kotoba.native.machine-ir` consumes those
contracts and owns only the bounded KIR-to-GMIR producer, physical MC lowering,
and x86-64/AArch64 encoding. Final layout is consumed from `kotoba-codegen`.
The atomic-add/tail-if subset is selected
by the production emitters and has cross-ISA real-process coverage. Other KIR
expression families remain on the established emitter and migrate
incrementally.

`kotoba-object` owns the target-neutral ELF64 record encoders. This repository
supplies the target-specific section layout, virtual addresses, relocation
requests, entry shims, and runtime/capability policy; it no longer carries a
second implementation of ELF headers, symbols, or RELA records.

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
