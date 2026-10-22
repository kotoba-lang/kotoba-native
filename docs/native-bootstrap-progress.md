# Native compiler bootstrap progress — 2026-10-22

This remains a draft source candidate, not native product admission. The
compiler core is Amu's measured `seed/MANIFEST` lineage. No C/JVM/Node
compiler or C loader was used for the native executions recorded below.

## Observed execution

An experimental, standalone AArch64 Linux ELF checked and compiled a small
Kotoba source. It compiled the current C1/C3 decision sources from Amu #1440
commit `ff9cae8cca54a61ea167dbc3bb9f1b4b3b783417`, then used those
native-generated decisions for byte-file output. The resulting smoke
container exactly matched native stdout-hex output from the earlier stage.

It then compiled all sixteen adopted compiler-core modules. The resulting
2,552,512-byte raw code SHA-256 is
`b10e381344a1f5a8b82cac981c0011bd20ecbcc4b48dd5f5dce97364c74e8a00`,
exactly the recorded M105 fixed point. Its KSEED container SHA-256 is
`c0dca203533619be80cb0b45dc1951d0dd37444c61f4185d2829ab3cfb05e3bf`.
This is a new native core compilation, not recomputation of saved receipts.
The experimental compiler ELF has neither PT_INTERP nor PT_DYNAMIC.

The canonical `context_sentinels.kotoba` fixture and its four-module closure
passed native check and compilation. The emitted program ran directly on
AArch64 Linux and returned `0`. The source hashes, compiler output hashes
and qualification limits are in
[`evidence/native-bootstrap-20261022/progress.json`](evidence/native-bootstrap-20261022/progress.json).

## Runtime fixes needed to reach this stage

- Initialize 2048 bytes inside the existing 4096-byte data page. The owned
  output journal extends past the former 1024-byte initialized area. Permit
  `-1` only at the four empty owned-FD words; preserve other negative-value,
  duplicate-word and bitmap-overlap refusals. Frame headers and sections use
  the same initialized-size accessor.
- Populate v11 data words 384/392 as well as the provider's private code-span
  state. The measured compiler directly reads those words for literal-table
  fast paths. Their absence caused a native SIGSEGV during code generation.
- Allocate a separate 512-byte decision context. Before every C1/C3 call,
  bind that component's actual code base/length and decision fuel. The former
  inline decision context overlapped private IO/spawn state and could not
  support selfhost-generated decisions with literal-table fast paths. All
  private/public decision call builders share the same initializer.
- Concatenate image bytes into a fresh destination instead of creating a
  persistent vector root per byte. A compiler image contains millions of
  bytes. The complete native image-builder regeneration still needs testing.

## Bootstrap limitations and required next gates

### Subsequent native FS2 execution

The Amu draft now contains the mandatory-FS2 successor and actual native
generation/workload records at commit
`996cc5af061464518d85503cd51fd67fbb4201ae` (Amu #1428). That prototype ran
check and byte-file compile with this runtime's current FS2 implementation,
and its G1/G2 containers matched. All nineteen freshly compiled Embench
programs returned `1` from their complete `bench-verify(1)` workload. This is
prototype correctness, not a new timing score or final toolchain admission.

An explicit internal `:command-i64` entry mode now preserves status 0..255
as the process exit and performs owned-output cleanup without printing the
status. Native experiments returned 0 for successful check and 1 for an
unsupported target or unknown source symbol. The public planner/profile
does not yet admit this mode. Ordinary program-value output is unchanged.

The internal image-builder include fixture exercises the real build/frame
functions on native CPU; it is not an alternate public package API. Its
source closure and native execution still need completion. The full closure
also exposed a three-argument `string-concat` in planning's set conversion;
the source now uses the declared two-argument operation.

### Admission still open

Initial byte materialization used a disposable Python calculator of the
canonical IR builders, outside the required toolchain. That is not an
Amu-selfbuilt packager. Native regeneration of the complete builder and
controller closure remains required before admission.

The initial raw compiler predates FS2. A pinned historical **Kotoba/native**
filesystem snapshot is used only for this labelled bootstrap experiment;
it is not a public fallback. The current runtime's FS2 decisions must be
paired with the current Amu IO/decision source before production admission.
Native-generated decision containers have not yet been admitted as sealed
product artifacts. No seal or profile verifier was disabled in the public
package entry.

The historical seed accepts `aarch64-macos` as its emission target; its raw
AAPCS64 code was executed with the experimental Linux native runtime. This
does not establish Linux-static target admission. The current native-static
profile/value bounds and all refusal/authority/resource behavior still need
alignment and qualification.

The fixture uses an explicit `--unpinned` bootstrap source snapshot with
all source hashes recorded. The seed's default refusal for such multi-module
inputs remains intact. This does not pass the public module-lock/import
gate, which still needs actual locked native execution.

Complete compiler/CLI/packager self-rebuild and G2/G3 identity, all nineteen
fresh Embench workloads, current sealed/profile admission, public dotted-ID
and alias import, and public CLI success/refusal behavior remain open.
Amu's public entrypoints remain unavailable until those gates pass. No main
merge, Actions/protection change, shared WIP cleanup or service change is
authorized by these experimental results.
