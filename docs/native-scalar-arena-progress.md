# Native scalar arena checkpoint candidate

This extends the rooted native packager at `86c691e4`. The structural
`arena-enter`/`arena-leave` slots retain ABI offsets 224/232 and the original
256-deep LIFO bound. Enter snapshots pair, string-pool, vector-handle and
vector-item use; leave validates every saved value before restoring any of
them. The private depth word is at 1936, within the initialized state page;
the separate 8192-byte mark region is derived and bounded by image planning.
No capability grant or guest allocator budget is increased.

The measured Amu `seed/MANIFEST` successor retains scalar scope markers and
emits enter/body/leave with the scalar preserved across leave. Native tests
performed 600,000 releases, preserved outer values and i64/bool/f64 results,
accepted depth 256, refused depth 257, and retained the vector-table refusal
for the same unscoped allocation count. Returning a vector from a scope is
refused by the compiler. Exact identities and results are in the adjacent
evidence JSON. The ordinary whole-MIR eight-component aggregate also exited
0 with these native artifacts.

This is an internal AArch64 CPU framing fixture, not public target/profile,
seal, CLI, native controller or release admission. General abort/recur cleanup,
the complete existing corpus and the large MIR resource gates remain open.
The prior 19-workload correctness result belongs to the pre-arena compiler;
the current successor still requires its own full19 rerun. No historical C,
Node, JVM, CLJK or Python materializer build route was used for these runs.
