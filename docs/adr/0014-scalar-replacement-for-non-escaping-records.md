# ADR 0014: Scalar replacement for non-escaping records

## Status

Accepted.

## Context

The legacy native emitters represent a local record as one stack slot per
field, flatten nested records, and box records into pair chains when they cross
a function boundary. Moving that entire representation into machine IR at once
would mix local optimization, heap/context calls, ownership, and ABI policy.

A fixed record with only scalar fields does not need a runtime identity when it
is constructed, bound locally, merged through control flow, and projected
inside one function. Materializing a box in that case would add allocation and
make the native path heavier rather than more mature.

## Decision

The bounded KIR-to-GMIR producer performs scalar replacement of aggregates for
non-empty `[:record name fields]` values when every declared field is `:i64` or
`:bool`:

- `record-new` evaluates every field exactly once in declaration order and
  records an ordered bundle of SSA registers;
- lexical `let` may bind that bundle without allocating or flattening stack
  storage;
- `record-get` requires the identical canonical type and selects its declared
  field register;
- an `if` whose branches produce the identical record type emits one GMIR phi
  per field, preserving the bundle shape across the join;
- the function tail must still be scalar, so no new function ABI is implied.

The bundle is internal producer state, not a new serialized GMIR operation.
GMIR and MIR continue to carry canonical scalar definitions and phis; MIR's
parallel-copy scheduler owns their physical transport. Unknown fields,
mismatched branch types, nested records, non-scalar fields, escaping record
results, and record parameters fail the pilot predicate and remain on the
established backend path.

## Consequences

Eligible source records reach both native targets without heap allocation or a
record frame. A two-field record-valued branch produces the real multi-phi path
and, when acyclic, has zero frame slots and zero spill traffic. Evaluation of an
unprojected field is retained, including division traps.

This does not unify the boxed function-boundary ABI, nested aggregate layout,
variant payloads, or runtime record identity. Those remain explicit follow-up
contracts rather than being inferred from this non-escaping optimization.
