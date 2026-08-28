# Cold merged namespace identity repair

Disposition: the seven cold namespace identity changes are fixed. All selected
unit tests pass. The complete Go comparison still fails on the separate display
and source-admission gaps. No full parity claim is made.

## Source and scope

- Root base: `1198df51e6453e88e97257e73b29539e7b4346e8`.
- Original review: `7b980c79`.
- Unchanged observer import: `996871c9` as `582221c3`.
- Unchanged comparator import: `e946f749` as `d187aeb4`.
- Tested repair: `040336dd`.

Production changes are limited to two functions in `artifact_queries.rs`.
`module_declaration_artifact_type` now routes merged class namespace names
through the symbol value query. It rejects conflicting name type or symbol
caches before the query can publish a class value.

When `type_of_artifact_symbol` reaches a merged class without a value cache,
it calls the existing `get_nongeneric_class_members` provider and uses that
provider's static identity. It no longer falls through to the declared instance
type. The existing provider checks the complete class and namespace sources
and prepares the real member and constructor graph. No synthetic value cache,
replacement symbol, or reduced declaration list was added.

Warm values keep their existing path. Class declarations and `export =`
expressions keep their declared identity. Ordinary value reads and namespace
names keep the static value identity. The export cache helpers, class provider,
root global-binding files, and formatter are unchanged from the root base.

## Verified behavior

The complete unchanged observer ran against fresh Rust and pinned Go builds.
Both produced all 84 rows. These seven namespace-first rows now return the value
type on the first query, matching Go, and retain that exact identity afterward:

| Case | Cold type role | First query stable | Forced replay stable |
| --- | --- | --- | --- |
| `global_original` | value | yes | yes |
| `global_export_only` | value | yes | yes |
| `global_members` | value | yes | yes |
| `global_namespace_first` | value | yes | yes |
| `global_consumer_first` | value | yes | yes |
| `global_namespace_first_export_only` | value | yes | yes |
| `global_two_namespaces` | value | yes | yes |

All 63 checked Rust rows now have stable first-query identities, stable forced
replays, and empty diagnostics. The checked rows have no comparison differences
outside type display and member-symbol display. Complete symbol declarations,
value declarations, flags, member lists, member types, canonical parent and
declaration-symbol identities, constructor return identity, alias targets, and
declared/value roles still match Go.

Both original inputs, all global source orders, export-only dependency setup,
the local namespace export, and local class shadowing remain checked. All probe
source strings, compiler options, query orders, observed fields, and comparison
rules are unchanged. The new Go observation file is byte-identical to the
original reference result.

The three new unit tests check cold and declared-first queries in both global
declaration orders, unchanged class members across source checking and replay,
conflicting name caches before and after value preparation, healthy restoration,
and repeated rejection of a nonempty global namespace without writes.

The full artifact-query selection also retains passing tests for both original
class/namespace cases, cold local and global export declarations without
publication, changed redirect/flag pairs, and foreign same-name global targets.
Those existing test bodies were not changed.

## Remaining gaps

The comparator exits 1, not 0. Its complete counts remain:

- 63 checked-source mismatches from type and member-symbol display.
- Six known unsupported global nonempty-namespace rows.
- Twelve local namespace-before-class source failures.
- Three inapplicable read-first orders.

Merged class type display still returns `MalformedType`. Member-symbol display
still adds class prefixes absent in pinned Go. The empty local namespace before
a class remains unsupported. The nonempty local namespace before a class still
fails source checking instead of producing Go's TS2434 diagnostic. These gaps
were neither repaired nor normalized away here.

The prototype type-display field remains null in both unchanged observers.
Prototype symbol/parent and constructor return identity remain checked.

## Runs and evidence

| Session | Command | Result |
| --- | --- | --- |
| `56875` | Complete Rust observer | Exit 0, 84 rows. Fresh build: 52.01 seconds. |
| `99537` | `ts_checker --lib`, filtered to `artifact_queries` | Exit 0. 91 passed, none failed or ignored, 3,984 filtered. Tests: 0.45 seconds. |
| `18078` | Complete pinned Go observer | Exit 0, 84 rows. Test: 0.21 seconds. |

All sessions are collected. Compilation and test times above exclude queue wait.
The Rust observer retained 18 existing checker warnings. No source or probe
changed between queueing and collection. All recorded input hashes still match.

Worktree: `target/agent-worktrees/wave154/cold-merged-namespace-identity`.
Target: `target/agent-targets/wave154/cold-merged-namespace-identity`.
The physical target was absent before the first command. The Rust observer
built first. The unit test then reused only this same worktree's own target.
No artifact or fingerprint was copied, reflinked, hardlinked, or seeded.

All jobs used the common lock, 16 GiB memory, 16 MiB stacks, and unchanged TMPDIR.
Rust used the absolute main capped runner, absolute manifests, and locked offline
dependencies. Go used a fresh private build cache and the existing module cache.
The Go checkout remains clean at `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
Its TypeScript submodule is also clean. No upstream update occurred.

Raw reports, comparison, and input hashes are under
`target/review-merged-class-exports` in this worktree. Outer logs are
`/tmp/ts-rust-wave154-cold-merged-namespace-` with suffixes `tests.log`,
`rust.log`, and `go.log`.

| Evidence | SHA256 |
| --- | --- |
| Go observations | `fe994d181e47a7a3d3d08d6fa92baf4dd38160dcfb90bf2def2b296306a5b8cf` |
| Rust observations | `2a2fe8f5ff96267d2f86a48d124e78144f332c7779ee6a320f2b23a1ca9cb3a3` |
| Complete comparison | `76b63701c74aa4bdf4058807280a36ea6d5520cd837a46c393a73e323d301610` |
| Unit test log | `175bd583e3d15c1c24ac9d9ecb5a0735a6782396dde36b513b48ba7c51c9e440` |
| Rust observer log | `b0b35fe83a54b546bb119a4f66344229e5ab2abee8b34c12b64cf776f2f3a88b` |
| `artifact_queries.rs` | `e31b28f86b9508f3bf2954b18cf3a94b928eb8459b38f3c95a6197c3bafe06af` |
| New unit test module | `b56849ae943dc51d74f2aba7eb0d0808bce26de65eaa105cb92b4ac1a27a523e` |

Formatting and whitespace checks pass. This report does not claim a new full
workspace run, a strict Clippy pass, a primary promotion, or full port completion.
