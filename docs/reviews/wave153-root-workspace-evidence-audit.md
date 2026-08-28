# Root workspace evidence audit

Report: `5b23c2d3c4a7769faff44ff1e30cb9794f030a30`.
Source: `ebe995e1cd7c342ebb7c89fc8ca66600f7ef9715`.
Source tree: `7e2e67f2661ac28156cbaf127853c6aef9af4710`.

No count mismatch, unaccounted missing name, or undisclosed weakening was found
in the five replacement diffs. The saved log agrees with the JSON and Markdown
report in the checked scope. This is not approval of the full port or a
resolution of the later merged-export findings.

## Independent recount

The audit parser checks every announced count, named result, and section
summary before comparing it with the report. It rejects duplicate qualified
names, duplicate binary paths, incomplete sections, and unparsed result lines.
An independent awk count agrees with the section and named-result totals.

| Item | Measured count |
| --- | --- |
| Named passing tests | 6,811 |
| Binary tests | 6,810 |
| Documentation tests | 1 compile-fail test |
| Test binaries | 164 |
| Documentation groups | 32 |
| Completed matching summaries | 196 |
| Failed, ignored, measured, filtered | 0 each |

The documentation test is `ProductionNameResolverHost` in
`semantic/name_resolution.rs`, line 66. The other 31 documentation groups are
empty. The report correctly calls them groups, not 32 documentation tests.

| Prior log | Prior results | Retained passing names | Passing replacements | Unaccounted |
| --- | --- | --- | --- | --- |
| wave151 workspace | 6,676 passed, 2 failed | 6,673 | 5 | 0 |
| wave150 root selection | 4,429 passed, 2 failed | 4,428 | 3 | 0 |

The 6,678 prior names were not 6,678 prior passes. Both earlier failures are the
global and local class/namespace identity tests. They retain their names and
pass in the new log. The current run has 138 names absent from the prior
workspace log, consisting of five replacements and 133 additional names.
Every replacement target is distinct and was absent from the prior run.

## Replacement source audit

The first four replacements entered root in `33081c24`, compared with its
parent `91c16a21`. The artifact replacement entered in `91c16a21`, compared
with `3ae315e8`. Each resulting definition was also checked at `ebe995e1`.
The adjacent JSON records exact old and new names, files, lines, and file hashes.

| Replacement | Verified change |
| --- | --- |
| Constructor bodies | All three source strings remain. The new test checks initially cold links, supported results, exact TS2377 location and text, separate class/value identities, and stable forced replay. |
| Binder static block | Source is unchanged. The original incomplete-flow checks and direct-call counts remain. The generic static-block gap becomes an incomplete block with no start node and `CrossContainerFlowEffects`. |
| JavaScript expandos | This is the disclosed input change. Array and arrow values replace numeric cases in the negative test. Binder flags, the exact assignment boundary, two attempts, cold links, and unchanged query state remain checked. |
| Later compiler file | Both files, roots, and options remain. The test now checks the canonical checker and the earlier exact TS2322 diagnostic after the method is supported. The separate later unsupported-construction control ran and passed. |
| Artifact errors | Both original symbol-display errors keep their expected failure classes. The same source fixture now also supplies a type ID for seven additional typed query/display cases. |

The JavaScript positive control at `source_class_bodies.rs:611` adds a Console
library and strict options. It checks numeric expando and static-super reads,
the exact TS2565 diagnostic, `number` property displays, class receiver identity,
the `456` assignment result, and stable replay. It passed. This is feature coverage, not
a byte-identical replay of the old default-option programs. The separate
poisoned-static-field control also retains its old input and passes.

The two formerly failing class/namespace tests and their helpers lie within the
first 991 lines of `export_equals_final_invariant_tests.rs`. That prefix is
identical at `34b12ce7` and `ebe995e1`, with SHA-256
`349a248845df8b9ba2688b4f24e81ffa5d3d147fd986d450b9f2b6a14eeb280c`.
Its source-checking helper still requires success before the identity checks.
This audit does not claim every other retained test body is unchanged.

## Source and evidence checks

The report commit directly follows the recorded source commit. Its source tree
matches Git. All three saved test-log hashes and the report JSON hash match the
report. The format log is still empty with the recorded empty-file hash. None
of those files was modified by this audit.

The class import claim also checks out. The source delta and root import have
the same zero-context patch ID, `182b307679de22c1bc8019eb38115a3bb6b13352`.
At `33081c24`, 35 of 37 file contents match `e07fc2f8`. The two shared files are
`callable_sets.rs` and `store.rs`. Their retained root differences match the
pre-import root differences, with patch ID
`4a17f65597697790428600406f071b104541e1ac`.

The log identifies the recorded worktree and target but does not embed a Git
commit. This audit checks the supplied source pin against Git and the report.
It does not rebuild the binaries or independently repeat the original clean
source, fresh-target, exit-code, or formatting checks.

## Reproduce

```sh
node scripts/audit-wave152-root-workspace-evidence.mjs \
  --logs /home/theo/Code/sandbox/ts-rust/target \
  --output /tmp/ts-rust-wave153-root-workspace-evidence-audit.json
```

The final audit command and `node --check` pass. No Cargo command ran. Changes
are limited to this note, the audit script, and its result JSON. Rest-tail
preparation remains unchanged at `b78c4e21`, pending the complete clean owner leaf.
