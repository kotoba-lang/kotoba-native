# Owned output lifecycle source candidate

The new `linux_static_output.kotoba` component prepares native leaf routines
for explicit managed staging. It is **not yet connected** to filesystem
entry/exit paths. Current output-set still has the terminal-cleanup gap;
no cleanup, provider, compiler or CDCI qualification is claimed.

## Prepared mechanism

- A single synchronous output-set registry retains its opened parent and
  private directory descriptors, the current member descriptor, full path,
  basename, actual created-member count and cleanup state.
- Preparation records ownership before subsequent policy/result code can
  trap. Only a dedicated managed creation operation may arm it; ordinary
  MKTEMP must retain its existing persistence semantics.
- Managed members match the complete normalized owned path plus the next
  canonical index.tmp. They open exclusively through the retained directory
  FD. A successful open is journaled before a sealed decision or result
  conversion; no per-member reopen after mode application is needed.
- Cleanup closes the current member, attempts every known index.tmp through
  the retained directory FD, and checks device/inode equality with the name
  currently beneath the retained parent before attempting directory removal.
  Missing members after publication are ordinary; other errors are retained.
  It never recursively enumerates/deletes arbitrary directory contents.
- Leaf routines allocate no language values, call no guest code or sealed
  decisions, and do not depend on remaining guest fuel. They save the six C3
  words and use distinct s0..s4/t0..t3 registers on both ISAs. Cleanup has a
  re-entry guard and returns failure when its work is incomplete.
- Planner reserves a real, disjoint 5120-byte workspace in addition to the
  unchanged value/run arenas. Twelve private words (1752..1840) and explicit
  initial sentinel values carry registry state; the public ABI is unchanged.

The first two stat words (device/inode) were checked against Linux v6.17's
[x86-64 stat definition](https://github.com/torvalds/linux/blob/v6.17/arch/x86/include/uapi/asm/stat.h)
and [generic 64-bit stat definition](https://github.com/torvalds/linux/blob/v6.17/include/uapi/asm-generic/stat.h).

## Integration and correctness still required

Add explicit managed begin/discard FS2 contracts, their owning decisions and
Amu APIs, journal mkdir/open success before any fallible conversion, retain
the actual parent/directory descriptors, and route normal/fatal/signal exits
through the same cleanup while preserving the original result/diagnostic and
reporting cleanup failure. Ordinary MKTEMP, all original forms and other
users' paths must keep their meaning. Single-active staging follows the
synchronous IO API; nesting/concurrent re-entry must refuse, not overwrite a
live registry. The new component is not wired into a controller or workflow.

Identity inspection followed by unlinkat is not an atomic inode-bound remove
operation. Replacement/rename races, the mkdir/open journaling windows,
signals during those windows, close errors, SIGKILL/process death and actual
filesystem failures are not proven solved. This source must not be promoted
as a guarantee that every crash removes staging or that a directory name
cannot change between inspection and removal. The full owning path/race and
positive/refusal/resource corpus must decide admission; no smaller workload
or newly restrictive parent whitelist is substituted.

The user requested native-only build/execution verification on 2026-10-22.
No currently located loaderless compiler/runner can compile the whole
candidate closure: the historical CLI image paths are missing; available
seed payloads require a C loader, and the standalone ELF evidence is a small
probe. Those routes were not used as a substitute. This component has only
source/API/record/arity/register/layout inspection, with no emitted/runtime
proof. Complete canonical GMIR/lowering/ABI and whole compiler/runner work
remain required before actual self-rebuild and native-only CDCI admission.
