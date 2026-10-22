# Complete app-data absence after scope denial

Tracking: JUN-241 / JUN-201 / JUN-202, Kotoba Labs. Source candidate only;
no filesystem/project implementation, compiler/generator/assembler, native
admission/artifact/runtime or test was executed. No tests were added.

The catalog requires every out-of-scope fs/app-data path to answer as absent,
without an existence leak. The former generic path-failure branch returned
false only for EXISTS and otherwise trapped. This source supplies the full
sixteen-form absence path, including both rename operands.

## Distinguish scope from invalid state

The complete `resolve-path` API and its eight arguments remain unchanged.
Each request clears a private `path-denied` word at data+1632 within the
reserved header page. After normalization and root availability, both sealed
and captured-physical root spellings still ask the real C1 scope decision.
Only normal denial of those applicable scope comparisons sets the word to
one before branching to the caller's failure target.

Invalid spans/path plans, unavailable cwd/root, malformed state and unknown
decision values do not become absence. Root-spelling and C1 scope answers
must be their defined zero/one values; unknown answers trap. The previous
EXISTS false behavior for an invalid path is retained; other malformed or
unavailable paths keep their terminal failure behavior.

The entire admitted path span is checked for NUL before copying/normalizing.
This includes the rename destination. A NUL cannot silently truncate a target
to a different path. TAB/LF/Unicode/former separator tokens remain valid data;
write/append content is not subjected to a path-only NUL restriction.

For scope `/`, the byte after the one-byte prefix is normally the first name
byte rather than another slash. Native now passes the actual admitted root
spelling length to the previously unused fourth data argument of C1 op 8.
The owning rule handles length-one absolute root explicitly; zero retains
the previous argument contract. Prefix mismatch and path bounds still deny,
and malformed root lengths return an invalid decision rather than absence.
No public decision arity or cap grant changes.

All shared open-at/parent fragments now request resolution flags 14:
BENEATH, NO_MAGICLINKS and NO_SYMLINKS. Final-only O_NOFOLLOW was insufficient
for the catalog's all-component no-symlink rule. O_PATH/O_NOFOLLOW metadata
may still inspect the final link itself without traversing it. The numeric
bits are the [Linux v6.12 UAPI](https://github.com/torvalds/linux/blob/v6.12/include/uapi/linux/openat2.h);
the final-link metadata exception is documented by
[openat2(2)](https://man7.org/linux/man-pages/man2/openat2.2.html).
These source settings do not prove their actual kernel behavior.
Normalization still precedes opening. Original dot-segment/symlink semantics
must be included in whole-provider qualification; the flags alone do not
prove the behavior of a component removed by lexical normalization.

## All sixteen answers, before target filesystem access

The mechanism asks the sealed handler decision artifact's new op 48 for the
absent answer kind. It does not hardcode a second policy table in native IR.
The public five-i64 `decide` ABI remains; all 48 prior operations are retained.

| Kind | Forms | App-data operation answer |
| --- | --- | --- |
| 1 | 3 exists; 7 chmod; 8 mkdir; 9 unlink; 10 rmdir; 11 rename; 12 fsync | `0` |
| 0 | 0 read; 1 write; 2 append; 4 range; 5 stat; 6 mtime; 13 make-temp-dir; 14 no-follow stat; 15 owner | empty text |
| -1 | any unknown form | terminal failure |

This covers the complete operation set. A scope-denied path reaches neither
the operation body nor a target open/stat/mutation. In rename, destination
resolution occurs before either parent descriptor is opened, so denying
either source or destination returns false without probing the target or
holding a new parent fd. In-scope operation/errno behavior stays with the
complete existing native bodies and sealed decisions.

FS2 absence still carries the required acknowledgement; legacy requests retain
their unwrapped absence answer pending caller/decoder retirement. Both use
real byte/cell checks and result UTF-8/handle validation. Genuine resource
failures remain terminal and never use a synthetic successful response.

## Required matching artifact and remaining qualification

Amu #1440 adds `scope-absent-answer` and op 48 in the owning canonical handler
source. A previously compiled artifact that lacks op 48 returns the old
unknown-op failure, which this mechanism refuses. Rebuild and admit the exact
ISA-matched Amu-produced sealed handler source plus the updated C1 scope
source; never activate this native candidate with an old decision artifact.
Both public five-i64 decision ABIs remain unchanged. No C-loader or generated C header
is a requirement or replacement qualification path.

This is source control-flow/API/constant inspection, not proof of actual
kernel confinement, descriptor/no-follow/race behavior or existence-leak
timing. Full native positive/refusal/resource evidence, general runtime/ABI,
raw-byte digest, resolver/materializer/authoring callers, legacy-decoder
retirement, reviewed owning main/pins and compiler self-rebuild remain open.
No workflow/protection/live service/production route changed.
