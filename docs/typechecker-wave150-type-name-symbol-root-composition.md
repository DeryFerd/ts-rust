# Root type-name symbol composition

Status: the first focused root run passed all 21 tests. The three Go cases
passed with an empty compiled cache. The completed twelve root controls await
full root validation and original-fixture replay. No primary promotion is planned.

Base: `4327f7f345c90d59d6057a3f53c4d1c0e81eed9c`.
Author source: `efad1ef7313ae516ffb123a7532c734ba6c128a9`.
Worktree: `target/agent-worktrees/wave150/type-name-symbol-root-composition`.
Target: `target/worktrees/wave150-type-name-symbol-root-composition`.
Go pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

## Dependency map

Whole-commit equivalent-patch checks found no equivalent for the two provider
commits, the author adapter, or root's separate export validation repair.
No parent history was cherry-picked. The exact checks and stable patch IDs are
recorded in `docs/probes/type_name_author_controls.json`.

| Source | Imported | Excluded |
| --- | --- | --- |
| `89d86f80` | Unresolved symbol key/cache, record validation, parent-chain checks | Error-type key/cache, alias-type allocation, type-argument keys |
| `14e71e05` | Symbol-only lookup and allocation | Error-type producer and readers |
| `efad1ef7` | Exact production adapter, type-name position and cache checks, early symbol route | Author error-alias type-cache dependency and source-dependent tests |
| `37920d23` | None | Source publication, type formatting, callable and constraint changes |
| `34b12ce7` | None | Separate direct export-equals lexical-validation mode |

The root still uses its existing intrinsic error type for admitted missing
references. The reader accepts only the existing root recovery shapes when a
type cache is present. It does not allocate error types or change type output.
The source, constraint, bootstrap, formatter, and symbol-display files are
unchanged. The shared lexical and export-equals functions are unchanged.

The root reader also checks an alias target's requested meaning. An ALIAS flag
alone does not make a value export a type. Alias lookup errors remain errors.
No whole-file check or type-argument resolution is added to type-name queries.

## Retained controls

The author worktree and all 58 assertions remain unchanged at `efad1ef7`.
Its passing log contains the 42 earlier source/provider controls. This root
base contains 15 of those 58 test names. Name presence is not a claim that the
two branches use the same type representation or assertions.

The complete 58-name map records which tests exist on the root base. Controls
for the excluded error-alias and constraint work are not counted as root
passes. Twelve root-specific symbol controls cover lazy known and missing names,
qualified prefixes, root error-type recovery, cache rejection, empty and
foreign names, value aliases, and const assertions. The set also retains
real-name cache rejection, the type/namespace meaning table, malformed-input
binding rejection, and unavailable alias lookup.

The original value-export-as-type unit source remains an explicit negative
control, including the resolved-export table that points at a value symbol.
The `typeof` version remains a positive control. The pinned Go probe checks
the original source without an `Exposed` export, a real value re-export used
as a type, and the matching `typeof` source.

## Verification

Go session `78519` passed all three cases, but is unaccepted because it used a
Go build cache seeded from an earlier probe. Its log and JSON are preserved.
Session `59042` replayed the same Go source and three-case selection with an
empty compiled cache and passed. Its observations match the preserved
unaccepted result exactly. The fresh observations are committed as
`docs/probes/type_name_go_observations.json`.
No Cargo workspace artifacts or fingerprints were copied into the new target.

| Go case | Symbol | Type | Diagnostic |
| --- | --- | --- | --- |
| Original source with no `Exposed` export | Unresolved `Exposed` | `Types.Exposed` | TS2694 |
| Real value re-export used as a type | Unresolved `Exposed` | `Types.Exposed` | TS2749 |
| Real value re-export used through `typeof` | Resolved `Exposed` | `number` | None |

Fresh Go log: `/tmp/ts-rust-wave150-type-name-go-fresh.log`.
SHA256: `788300dad1a5a5edc4d0b602ee9a9e5b7fdd6b971191c855d2ffe43e3e68b395`.
Observation JSON SHA256:
`6ddfeeac68a134bc376fb0557d49af1c1d022263b0378a5eca4870a85a448d08`.
The pinned Go checkout remained clean.

Formatting session `50539` and focused Rust session `44663` passed. The latter
ran 21 tests with zero failures or ignored tests. The pre-existing unused
`allows_string_fallback` warning was left unchanged. Four additional root
counterparts were then attached for the full root run.

Go probes, formatting, and focused Rust tests use the common lock and
16 GiB limit. Rust uses the standard capped runner, absolute manifests, locked
offline dependencies, 16 MiB process and Rust stacks, and the exclusive target.
Go uses an overlay on the unchanged pin with a separate fresh compiled cache.
TMPDIR is unchanged. No other worker or primary branch is changed.

The full root test selection and complete-artifact replay of
`braceEscapedSurrogatePairLiteralType.ts` and
`declarationEmitKeywordPropertyNames.ts` will run on the actual root candidate.
Original fixture sources and baselines will remain unchanged.
