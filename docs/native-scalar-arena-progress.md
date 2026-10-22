# Native scalar arena checkpoint candidate

The initial checkpoint generation at `6ee15fd` extends the rooted native
packager at `86c691e4`. The structural
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
No historical C, Node, JVM, CLJK or Python materializer build route was used
for these runs.

## Growth-region successor

The successor retains persistent vector prefixes and forks while reserving
geometric tail room after an interleaved allocation. It uses a private
per-handle region map and fill/capacity rows. A stale prefix forks by copying;
views and new/recycled handles clear their region identity. If reservation
cannot fit, the exact-size path remains available; actual exhaustion retains
the original item-budget refusal. Guest cell/vector/item limits and grants
are unchanged. Only bounded private metadata is added by image planning.

Scopes now save five counters, including region-row use, in 256 records of
64 bytes. All five values are checked before any restoration. Region map/row
spans are derived and checked against the mapping before launch.

[growth-correctness.json](evidence/native-arena-20261023/growth-correctness.json)
records 16,385 interleaved appends, persistent forks, assoc/view/byte-view
behavior, 600,000 region rollbacks, exact-size fallback with 20 item cells,
and unchanged refusal with 18 cells. The original scope/depth/unscoped cases
also pass on this generation. G5 freshly compiled all 19 correctness workloads
and they all exited zero using this packager; no new timing score is claimed.
MIR large/resource results are maintained with the owning MIR source receipt.
