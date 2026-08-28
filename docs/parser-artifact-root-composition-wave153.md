# Parser and artifact root composition

Tested source: `01432ad25fe249401f0f9b044297ffd10be5347f`.
Source tree: `1b45a0876a346821da38c00cb3eb957f9e21a487`.
Base: `1d6c49fd7e6889f996d99db8e918be3b701d12d1`.
Branch: `agent/wave153-parser-artifact-integration`.

The full workspace has 6,947 passes and three inherited fixture-setup failures.
Strict parser Clippy passes. All 6,850 base test names remain, and all 100 added
tests pass. This is not a passing full workspace or approval of the full port.

## Import map

The complete parser and assertion-display reports were read before importing.
Every import uses `-x` and has one parent. No broader source-branch history was
merged, and no production call-site adaptation was needed.

| Source | Import | Scope |
| --- | --- | --- |
| `41b3d51d` | `0a53fd2c` | Original artifact classification review |
| `cbfa3ccb` | `dc729769` | Public artifact mode guard and parity controls |
| `ce22c86d` | `fd54f855` | Checked parser recovery and range stack |
| `4b3c1a94` | `dc77b89f` | Original nested-return review probe |
| `1a3a1c7a` | `5727dfcf` | Nested-signature range correction |
| `a9101367` | `93a95acb` | Original assertion precedence fixture |
| `2143d0bb` | `6be8e1d1` | Assertion precedence correction |
| `e1bdfd3d` | `6a396f4a` | Complete parser composition report |
| `96a2ccd9` | `f0046f60` | Checked signature and annotation display |
| `be3546c8` | `25b2ee64` | Per-location symbol identity assertions |
| `5a58a5dc` | `97b9d207` | Separate unsupported assertion-arrow control |
| `a64a95ae` | `01432ad2` | Complete assertion-display report |

The only conflict was the parser report. `e1bdfd3d` modified a document absent
from root. The conflict was reported before resolution. The complete incoming
document was verified byte for byte and added as a new file. No production
file was replaced to resolve this conflict.

The detailed source maps remain in
`docs/parser-range-root-composition-wave150.md` and
`docs/typechecker-wave150-assertion-signature-display.md`.

## Measured checks

| Check | Session | Result |
| --- | --- | --- |
| Unfiltered workspace tests | `31301` | 6,947 passed, 3 failed, exit 101 |
| Strict all-target parser Clippy | `20058` | No warnings, exit 0 |

Both sessions are collected. All 184 test binaries and 32 documentation groups
completed. There are 6,950 named results, including one compile-fail
documentation test. No test is ignored, measured, or filtered. An independent
awk recount agrees with every announced count and all 216 result summaries.

The workspace build took 3m 46s. Strict parser Clippy took 4.46s. These are
Cargo's measured times and exclude the shared-lock wait. The source stayed
fixed and clean until both sessions were collected. No extra full run was
made to absorb a later root repair.

Within the workspace run, all 329 parser controls pass. This includes the
original range probes, all five assertion precedence tests, and the test that
requires all 108 bundled libraries. All four public assertion-display tests
and the changed-predicate invariant pass. All 51 available artifact controls
pass, including the unchanged invalid-library-mode reproduction.

`TS_GO_REPO` was set to the initialized pinned checkout, so the upstream parser
test did not return early. It passed. `TS_GO_ORACLE` was also set explicitly,
and all 30 CLI compile/oracle tests passed. The pinned checkout and executable
remained unchanged. This does not claim full corpus semantic parity.

## Inherited failures

These three tests fail in both the base and this candidate:

- `review_global_binding_capture_keeps_exports_valid_after_ambient_module_checks`.
- `review_global_binding_capture_refuses_repeated_capture_without_writes`.
- `review_global_binding_capture_rejects_replacement_tables_before_cached_reads`.

Their full names are in the adjacent JSON. Each stops in the fixture helper at
`crates/ts_checker/src/semantic/artifact_queries/export_equals_final_invariant_tests.rs:117`
on the unchanged source `const observed = Value; export = Value;`.
The source checker returns `Unsupported(Variable(NonVariableSymbol))` with
class flags. All three error payloads match the base log exactly, including
their source node and symbol identities.

These failures occur before the affected guard assertions. Six of the nine
new root export-review tests pass. The other three fail in setup. All nine
tests, both complete test files, and all older tests in those files remain
byte-identical to the base. Root owns the standalone-class source dependency
and export repair. No later repair was imported or credited here.

## Test retention

| Prior run | Prior names | Retained names | Result |
| --- | ---: | ---: | --- |
| Root base `1d6c49fd` | 6,850 | 6,850 | Same 6,847 passes and 3 failures |
| Earlier root `ebe995e1` | 6,811 | 6,811 | All pass |
| Parser composition `2143d0bb` | 329 | 329 | All pass |
| Artifact guard leaf | 53 | 51 | All available controls pass |
| Assertion-display leaf | 4,423 | 4,420 | All retained names and 3 prior root replacements pass |

The static source inventory also retains all 6,849 base test labels and adds
100 labels. The final inventory matches the pre-run imported inventory byte
for byte. Static labels are source evidence, not a substitute for runtime
results. No current-base test was removed, renamed, or given a weaker assertion.

### Two absent corpus dependencies

The artifact leaf also ran these tests, whose modules are absent from this
root and from the approved imports:

- `corpus_execution::tests::batch_executes_decoded_options_and_hashes_actual_artifacts`.
- `corpus_ledger::tests::ledger_auxiliary_artifacts_do_not_replace_semantic_oracles`.

Root approved verification with the 51 available controls. Both missing names
remain in the report as missing subsystem dependencies. No corpus module,
stub, or ignored test was added. The separate 53-test leaf result is not
reported as a 53-test combined pass.

### Three earlier root replacements

The older assertion-display leaf predates three reviewed root changes. The
exact old and new names and their reasons are retained in the adjacent JSON,
using the existing map in `docs/typechecker-wave152-root-workspace.json`.

- The JavaScript expando negative control now uses unsupported arrays and
  arrows. This was an input change. The separate numeric-expando and
  static-super positive control also passes here.
- The compiler control keeps its original files and now checks supported
  class methods without losing earlier diagnostics. The separate unsupported
  construction control remains and passes.
- The artifact control retains both original symbol-display error cases and
  adds typed missing, unsupported, and fatal query/display cases.

All three replacement targets are distinct, were absent from the older leaf,
and pass in this run. Their source files are unchanged from the current base.
No replacement or input change was made during this integration.

## Source preservation

The full parser crate and both original probe files match `2143d0bb` exactly.
The public assertion-display test file matches `5a58a5dc` exactly. The binding
files `name_resolution.rs`, `production.rs`, and `store.rs` match the base byte
for byte. Binding repair `09fb0b96` remains an ancestor. The class, span, and
property/index source changes remain intact.

Mapped callback display retains the real `callable.signature`. Optional
annotation identities come from the existing checked providers. No signature
placeholder or unchecked annotation identity was added. The separate inferred
predicate source gap remains open. The prior complete fixture parity results
in the assertion-display report were not rerun or transferred to this source.

## Execution and evidence

Worktree: `target/agent-worktrees/wave153/parser-artifact-integration`.
Target: `target/worktrees/wave153-parser-artifact-integration`.
The target was absent before launch. Clippy created it first. Workspace tests
reused only this same physical worktree's output. No artifacts or fingerprints
were copied, reflinked, hardlinked, or seeded from another worktree.

Both commands used the absolute root capped runner and absolute manifest,
locked offline dependencies, 16 GiB memory, 16 MiB process and Rust stacks,
the common lock, and unchanged unset `TMPDIR`. The pinned Go commit remains
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. The oracle executable retains
SHA-256 `204f15c767025fc9238b748399be7d1293f6d0f8ea9ddec8eab65995ecf4bb39`.

The launcher, logs, command metadata, inventory snapshots, and final audit
script are under `target/review` in this worktree. The JSON records the full
commands, source hashes, import map, retained controls, and every test section.

| Evidence | SHA-256 |
| --- | --- |
| `target/review/workspace.log` | `26e8ccbd59a6cd7dbe0fb29e66d4b8e4204f53afd27b0ddb891022f515c46363` |
| `target/review/parser-clippy.log` | `769addc0489b6f4e361b0aa7a3d278dc43834e8dc9a2b189dce0a5fcb97d231f` |
| `docs/parser-artifact-root-composition-wave153.json` | `109ab9eee451ec8314a3d4fab49d8b42e3c4a8c433b8cb6eaa8f60778741998b` |

No pending colon, JSDoc, inferred-predicate, defaults, array, class-display,
or later identity family is included. Historical corpus rows and leaf logs
remain unchanged. No primary promotion, passing full workspace, full corpus
parity, modern-project success, performance result, or upstream roll-forward
is claimed. The full port goal remains active.
