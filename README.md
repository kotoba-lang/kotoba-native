# kotoba-native

Kotoba native backend — checked KIR to x86_64/aarch64 machine code and ELF64.

**Tier**: `T2`  **Role**: `backend`

Split out of the overloaded core repos by ADR-2607266000 so that each
responsibility has exactly one owner and the dependency direction is
checkable from outside.

## Owns

- `kotoba.native.x86-64`
- `kotoba.native.aarch64`
- `kotoba.native.elf64`
- `kotoba.native.peephole`

## Optimization

Both backends bake intra-function branch displacements into plain bytes at
emission time, so a rewriting pass that changed any byte *count* would
silently invalidate every displacement spanning it — with nothing to catch it,
because the token vector carries no instruction boundaries. `peephole`
therefore rewrites **size-preservingly**: a replacement occupies exactly the
window it replaces, padded with canonical architectural no-ops. What is
reclaimed is memory traffic, not bytes.

The first rewrite materializes a constant right operand directly into the
scratch register (`rcx` / `x1`), dropping the spill-and-reload round trip that
protects the accumulator when the right operand needs it. Recognition is on
the KIR **form**, never on emitted bytes — matching byte patterns in an
undelimited instruction stream would rewrite immediates that happen to spell
an opcode.

Reclaiming the padding, rather than preserving it, requires turning those
baked displacements into deferred tokens first. That is a separate change.

## Does not own

- parse .kotoba source
- own language semantics
- require Rust in the core path

## Depends on

- `kotoba-lang/kotoba-kir`
- `kotoba-lang/artifact`

## Test

```bash
clojure -M:test
```
