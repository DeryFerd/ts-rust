# Root workspace verification

Tested source: `1d6c49fd`.
Result: 6,847 passed and three failed. All 6,811 previous test names remain
present and pass. Formatting passed. This is not full port approval.

## Complete run

Session `6272` exited 101 and is collected. Cargo ran every workspace target
with `--workspace --no-fail-fast --locked --offline`. All 166 test binaries
and 32 documentation groups completed. The 6,850 named tests have no ignored,
measured or filtered cases. The 39 additions have 36 passes and three failures.

Session `86449` exited 0 and is collected. Its read-only workspace format log
is empty. No source changed while either command was queued or running.

The structured report is `docs/typechecker-wave154-root-workspace.json`.
The log parser checks every section's named-test count against its summary
and compares all names with the previous complete workspace log.

## Three new failures

These tests stop in fixture source checking before their binding assertions:

- `review_global_binding_capture_keeps_exports_valid_after_ambient_module_checks`
- `review_global_binding_capture_refuses_repeated_capture_without_writes`
- `review_global_binding_capture_rejects_replacement_tables_before_cached_reads`

Each includes a real ambient class in a script declaration file and an external
consumer with `const observed = Value; export = Value;`. The source checker
returns `Unsupported(Variable(NonVariableSymbol))` for the class, whose flags
are `CLASS`. The class has no namespace merge. No mutation assertion ran in
these three cases, and their source inputs remain unchanged.

The original paired redirect/flag and foreign-global tests pass. The corrected
cold merged-export test also passes, as do the other three new capture controls.
Both original class/namespace source tests still pass. The new source failures
do not undo that measured result, but keep this workspace result red.

## Retained source

The source includes the prior constructor-span and property/index changes,
global binding repair `09fb0b96`, unchanged probes `1bc9e76f`, fixture-only
repair `47eae0c9`, and six new probes `4409589d`.

The two review files match their source commits. The only combined difference
is the added test-module include at the end of the existing fixture file.
No review body or assertion was changed. The three production files for the
binding repair still match `09fb0b96` exactly.

The previous source `ebe995e1` passed all 6,811 workspace tests. Its report
`5b23c2d3` and independent audit `d25b13f0` remain preserved. That earlier
report discloses five test replacements. This result does not claim those
earlier test bodies or inputs were unchanged.

## Execution and evidence

Worktree: `target/agent-worktrees/wave154/root-global-export-composition`.
Target: `target/worktrees/wave154-root-global-export-composition`.
The new target was absent before launch. No build output or fingerprint was
copied, reflinked, hardlinked or seeded from another physical worktree.

Both commands used the absolute root capped runner and manifest, 16 GiB memory,
16 MiB process and Rust stacks, the common lock and unchanged TMPDIR.
No command was stopped or moved to another lock.

Logs in the primary workspace:

- `target/wave154-root-workspace-tests.log`, SHA-256
  `4af9c48f9726c622cfe5235bb0ba9083cb4f251e3dc96ea3d25465d74e0ceac5`.
- `target/wave154-root-workspace-format.log`, SHA-256
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The standalone global class source dependency now needs repair. The separate
symbol-cache, namespace identity, class display and JSDoc review findings also
remain open. No primary branch promotion, complete corpus result, project
parity, performance result or upstream update is claimed.
