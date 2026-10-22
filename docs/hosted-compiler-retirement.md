# Hosted compiler retirement

The owner directed removal of C/JVM/Node compiler routes on 2026-10-22.
This #205 candidate removes the eighteen CLJK compiler/backend modules from
`src/`, the four hosted operational/test drivers, NBB configuration and the
hosted test launcher. The canonical `.kotoba` compiler/backend/runtime
sources and test/refusal inputs are unchanged.

[`retirement/hosted-compilers.json`](retirement/hosted-compilers.json) records
each removed path, SHA-256 and Git blob at preserved ancestor commit
`0ee380c35bdca5e4711ace590fd443c01bc60259`. The original source remains
available through `git show <preservedCommit>:<path>` and the local task
archive for port review. Shared WIP, other branches and historical evidence
are preserved. `deps.edn` retains dependency declarations as provenance;
neither that metadata nor historical test inputs provide a compiler host.

Canonical source is not a compiled native compiler. #205 stays draft until
the measured Embench core produces the complete independent compiler,
native self-rebuild and all nineteen Embench workloads pass, and public
import/CLI behavior is verified through that same route. The removed hosted
runner is not replaced by another hosted fallback. Actions and protection
settings are unchanged.
