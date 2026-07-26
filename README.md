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
