# Native compiler bootstrap: string runtime connection

This branch extends native #205 (`3504590ee306437235fc61b321b0e258b10747ee`).
It is an implementation candidate, **not a built initial compiler**. No
compiler, assembler/generator, ELF, fixture or self-rebuild has executed.

The historical Amu #1316 compiler is selfhost-built machine code, but its
`KX64V1` container calls v11 helpers in a separate C loader. In
`seed/71-x86_64-runtime.kotoba`, `xr-slot` admits 23 offsets. The canonical
Linux-static candidate supplied 20 slots; two compiler string operations
were absent: `string-code-point-at` (144) and `string-compare` (240).

Both operations now generate full register IR for the existing two-ISA
assembler, share checked pair/window resolution and canonical UTF-8
validation, bind their actual entry labels, and participate in ordinary
planner/prelude/context composition. They allocate neither item words nor
result pairs. The old C helper source was read as historical semantics, not
compiled or used as a runtime or required oracle.

Code-point access requires a nonnegative **byte** index below the string's
byte length and refuses continuation-byte positions. Its decoder handles
all canonical scalars through U+10FFFF. It handles both code-relative literals
and negative-offset pool views. Comparison validates both whole strings,
compares unsigned bytes through the common prefix, then lengths, and returns
exactly -1/0/1. Embedded NUL is ordinary string data. UTF-8 scalar order is
intentional; UTF-16 surrogate ordering must not replace it.

## Required runtime evidence

`test/fixtures/bootstrap/strings.kotoba` contains 31 positive observations:
12 scalar/byte-index checks, five pooled/literal-view checks and 14 ordering
checks. Build and execute it with each declared loaderless Linux target;
exit 0 is required. Run all four separate `code_point_*.kotoba` controls and
require the native signal/trap outcome, not a successful integer result.
Keep generated-artifact/source/profile hashes and forbidden-process traces.

The exported `point` and `order` entries take dynamic typed parameters for
the native ABI harness. Observe their actual helper call sites in generated
code: the fixture's literal observations may be folded by the producer. ABI tests
must additionally cover invalid handles, forged code/pool windows, invalid
UTF-8, cached and uncached validation, register preservation and unchanged
fuel/arena counters. These checks are **pending**, including actual byte
assembly and execution on both ISAs.

## Remaining initial compiler work

The candidate supplies 22 slots. Legacy `cap-call` (48), admitted by the
generic x86 emitter, is still not implemented by the static packager. It
must either be absent from the actual compiler's effects/call graph or be
implemented and qualified; do not map it to `typed-cap-call` with a guessed
signature. Slot coverage is necessary, not whole-compiler qualification.

The historical compiler also reads complete source strings and sends raw
bytes through wire 35 kind 8. Its 628691-byte recorded unity input does not
fit the current 65536 per-value closed native profile. The current canonical
IO candidate uses segmented kinds 10/11. Therefore merely surrounding the
old compiler payload with an ELF header is insufficient. Preserve the full
source and byte semantics while connecting the compiler IO, admitted value
bounds and matching sealed decision/handler artifacts. Do not widen a
profile, drop a source/lock option, or substitute a C provider to make a
bootstrap pass.

The complete native path must materialize its initial compiler, rebuild the
same full source/packager closure through subsequent native generations,
verify fixed-point artifact identity, then run all 19 Embench workloads and
the public `amu`/`kotoba compile` commands using that compiler identity.
Historical #1188 GraalVM, #1222/#1313/#1316 C-loader selfhost, #1428 product
ports and current #205 source are distinct evidence. Disabled Actions remain
disabled. No main admission or public CLI replacement follows this source
change.
