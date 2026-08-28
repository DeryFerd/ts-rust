# Class source and artifact composition

Tested source: `1cde5d30c9330b416d27aa99de02909e95d5efc1`.
Root base: `4327f7f345c90d59d6057a3f53c4d1c0e81eed9c`.
All 4,930 tests pass across 49 binaries. Both full pinned private-class
artifacts match exactly. No Rust or probe source changed after these runs.
Nothing was promoted to primary.

## Import map

The first 43 imports retain the tested class source, write, and diagnostic
stack. Each commit has the full original hash in its cherry-pick trailer.
The common source ancestor is `0358fa7a`. Report-only `71243590` was omitted.
The option transport in `fc6a496b` was already present in root and was not
replayed. No unrelated parent history was merged.

| Original class commit | Root import |
| --- | --- |
| `e7c0438a` | `da40e9ac` |
| `ff3e1f58` | `df156324` |
| `fb150e58` | `2215a699` |
| `89a08184` | `3f9d927c` |
| `446ceb90` | `12e8d884` |
| `5ad1fe66` | `aef4c14f` |
| `f87fa245` | `5a7fbdcf` |
| `e6a5e01b` | `1788c7c0` |
| `7f1bdd8e` | `906ca7a1` |
| `10869319` | `a1c867a1` |
| `86a19541` | `753877ea` |
| `be73f3d7` | `e1236c23` |
| `8dfe51f8` | `56c6e796` |
| `b791931d` | `20ea58ea` |
| `f37dbbb5` | `47c469d9` |
| `61baf201` | `b7a9189d` |
| `b85d4ca6` | `56aff3f4` |
| `bc1f75c2` | `a784dfbf` |
| `51749e3f` | `e0b31773` |
| `33849614` | `7e44b9a6` |
| `80599394` | `007b02fa` |
| `454ee213` | `d895f972` |
| `a376c889` | `773f2c4b` |
| `884c4203` | `60380009` |
| `ae7d94e6` | `2bf7ecba` |
| `e54f1fad` | `b3bc787d` |
| `2b3be630` | `a6d8f77a` |
| `6176840c` | `7dcb3950` |
| `f9f02d87` | `f8046756` |
| `98c8cddf` | `5f135659` |
| `cdecbee6` | `560112e1` |
| `ec32afbb` | `2de368ff` |
| `68970e3d` | `95feb6a1` |
| `ff07b250` | `84f3f936` |
| `95d18697` | `03b1f8ec` |
| `2232de6e` | `988fd475` |
| `ccc93291` | `b262953a` |
| `f8636a50` | `db547c3c` |
| `41bc7f77` | `636ac7af` |
| `c75f4217` | `f88bbfe1` |
| `02b3d606` | `bfeec3e9` |
| `e87dbde9` | `7a897b55` |
| `49ec6003` | `d5d188eb` |

| Further change | Commit |
| --- | --- |
| Approved private-artifact delta `0efdd881` | `a0e1956a` |
| Two namespace assertions adapted to the diagnostics list | `dd02db98` |
| Artifact property reader adapted to the diagnostics list | `e07fc2f8` |
| Exact corrected Rust and Go probes from `cc03faa8` | `d91445e1` |
| Approved constructor first-token span repair | `1cde5d30` |

The artifact delta is the root adaptation of `cbc814ac`. Its original stable
patch ID is `d816271abe2845b6be77be2164e870cca76af82a`. The artifact owner's
final report `532d14a6` was read before import. There are 48 source and test
commits after root. No class/namespace provider or later direct-export repair
was imported from the separate owners.

Root chose the logical file delta `0efdd881..e07fc2f8` for its newer composition,
where the private-artifact change is already present. That is not a merge of
the two parent histories. The later probe and range commits remain separate.
These test results belong to the source and root base above, not that newer
root composition.

## Shared code

The source import had one import-list conflict in source_properties.rs. Both
namespace and class-flow imports remain. The artifact import had one conflict
in the formatter. The source-class `this` check stays first, followed by the
query-class check. No whole source file was replaced.

The shared class allocation helpers are present once. Query-only plans remain
separate from full source writers and their validation. Root export
authentication remains before artifact cache reads. The class fallback follows
those reads. Namespace formatter validation and source recovery remain.

The first source-root build found two namespace test initializers using the
old `diagnostic` field. They now require an empty `diagnostics` list, with the
same input, expected type, cache mutations, and replay checks. The artifact
property reader likewise rejects a nonempty diagnostics list. That one-line
adaptation keeps its prior rejection behavior.

## Constructor span repair

Independent review `cc03faa8b8c48f7da1fd74257400fbfe3f44fe84` confirmed two
TS2377 start-position errors. Its corrected Go run passed all nine inputs.
The imported Rust and Go files match that commit exactly. This repair changes
only `class_constructor_keyword_range` in source.rs.

The start now comes from the actual constructor node's first token. The
validated modifier offset, constructor-keyword check, keyword end, diagnostic
node, message, and ordering are unchanged. No class admission or cache policy
was widened.

All five corrected Rust test functions pass. They cover four TS2662 inputs,
four admitted TS2377 inputs, and the separate unsupported line-break input.
The public spans now match `41..59` and `41..82`. Bare `41..52` and comment
`66..77` remain correct. Class types and symbols survive forced replay. Bare
TS2662 references remain unresolved. The line-break input still has a separate
unannotated `public` field and remains unsupported in Rust.

| Corrected review evidence | SHA-256 |
| --- | --- |
| Rust probe | `408cc3307b43f6e4acdd69900d297c474f7a429f4f8aad3201c4a24a7a2e20c2` |
| Go probe | `2fcb61905ed770a1f161a5393612bd3ad826d0fa75906625aea6e60b84f65f1d` |
| Independent corrected Go log | `6dc2245c14bfefa626e564b720c9bcbb8e53c93cfe5f4bc30db668ca4c61f40d` |

## Executed results

Session `34072` exited 0. All 49 requested binaries ran without failed,
ignored, measured, or filtered tests. The selection includes the preceding
48-target composition and the unchanged corrected diagnostic review target.

| Group | Passed |
| --- | ---: |
| Binder units | 216 |
| Checker units | 4,004 |
| Compiler units | 259 |
| Fixture units | 165 |
| Public controls | 286 |
| Total | 4,930 |

The earlier clean composition `e07fc2f8` passed 4,925 tests across 48 binaries
in session `98201`. Its exact artifact run `71153` also passed. Those results
were collected before this repair and are not substituted for the final runs.

The final name comparison retains all 4,925 preceding tests and adds only the
five corrected review functions. Comparisons against older source and root
runs retain these previously recorded name and expectation changes:

- Root `c5d2aa33` changed `namespace_imports_preserve_module_identity_across_authenticated_module_modes` to `namespace_imports_preserve_mode_specific_module_identity`.
- The approved constructor update changed `unsupported_constructor_parameters_and_nonempty_bodies_leave_classes_cold` to `constructor_bodies_preserve_class_identities_and_diagnostics`, keeping its original sources.
- The approved compiler update changed `canonical_program_rejects_a_later_unsupported_file_without_fallback` to `canonical_program_checks_later_class_methods_without_losing_earlier_diagnostics`, keeping its original files. The separate unsupported-construction control remains.
- Earlier class-body commit `5ad1fe66` changed `javascript_class_expandos_are_typed_unsupported_before_class_publication` to `unsupported_javascript_class_expando_values_leave_the_class_unpublished`. It replaces numeric-expando rejection inputs with array and arrow inputs. The positive numeric-expando and static-super case is in source_class_bodies.rs. This is not an unchanged-input claim for that old unit test.

The name audit retains 4,623 of 4,624 prior source names, 4,473 of 4,476 prior
artifact-composition names, and 4,413 of 4,415 prior root names. The differences
are exactly those mappings. The new composition drops no other test.

## Pinned artifacts

Session `40755` exited 0. It executed exactly one variant of the unchanged
`classFieldsPrivatePropertyAccessSameNameAsClass.ts` fixture. Both complete
artifacts are exact, with 52 visited type nodes and 54 visited symbol nodes.
Diagnostics, unsupported details, mismatches, and fatal invariants are zero.

The scorecard records clean Rust `1cde5d30` and clean Go
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. The oracle manifest digest is
unchanged at `667bc371832bee995194e09bc5b6e968`. The fixture and both expected
artifacts retain their original hashes. No full-corpus or full-smoke result
is claimed by this one-case comparison.

## Execution and evidence

Both successful compositions started with empty Cargo targets. Each target
was confirmed absent before its first run. No build output, fingerprint,
hardlink, reflink, or cache was copied between these worktrees. Each artifact
command reused only its own physical worktree's target. The earlier failed
source-only build used its separate target and provides no runtime result.

All Cargo commands used the root capped runner, an absolute manifest, locked
offline dependencies, 16 GiB memory, a 16 MiB Rust stack, unchanged TMPDIR, and
the common lock. No outer lock or queue bypass was used.

```text
target/agent-worktrees/wave150/class-source-artifact-span-repair
target/worktrees/wave150-class-source-artifact-span-repair
```

The earlier source-only session `89973` exited 101 before tests because of the
two test initializers described above. Its log remains unchanged. Stale queued
sessions `25877`, `1721`, `72043`, and `58924` were stopped and collected before
compilation. Only their confirmed waiting flock children were stopped. They
provide no runtime evidence. The common lock owner and other workers were not
changed. No run here requires rejection for copied build artifacts.

All command sessions are collected. Changed-file rustfmt and the full import
diff check pass. No full-workspace or strict Clippy result is claimed.

| Final evidence | SHA-256 |
| --- | --- |
| `/tmp/ts-rust-wave150-class-source-artifact-span-repair-gate.log` | `a855ca8a28afa18fce11c29ba9e93cec658ce9455beac772402563004848847c` |
| `/tmp/ts-rust-wave150-class-source-artifact-span-repair-artifacts.log` | `10d51b4a489a5b7012b2f6ec27662742c4009222c221c717fd0b41ca40fd293b` |
| `target/wave150-class-source-artifact-span-repair.json` | `2d5584b53db5d7872bb34556c8f7ef9a2685123221ebe9c7c22e15555c8dfce2` |
| `target/wave150-class-source-artifact-span-repair-test-retention.json` | `6848860a671f8099c5c71ff2089d855bf85785cfb7de4c24f79ea8a0c804ecf1` |
