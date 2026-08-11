# ADR 0026: Remove production legacy routing

Status: accepted

## Decision

Both production native entry points now augment checked KIR helpers and invoke
the whole-module KIR → GMIR → MIR → MC pipeline unconditionally. An IR
rejection propagates as a fail-closed result; it cannot select either retired
recursive ISA expression emitter.

Whole-module lowering accepts one or more declared exports. GMIR retains the
first export as its entry identity, while final native layout publishes exact
offset, length, and arity metadata for every requested export.

The old emitters remain reachable only when the dynamic test compatibility
seam is explicitly disabled. This preserves byte-level regression evidence for
held nested/non-scalar aggregate representations without making those shapes a
production native claim.

## Consequences

- Every production native operation crosses versioned GMIR, target-selected
  MIR, allocated MC, and the closed target encoder.
- Unknown operations and held value shapes fail before ISA emission.
- Multi-export modules no longer require the old layout path.
- Test-only legacy evidence is structurally separated from production routing.
