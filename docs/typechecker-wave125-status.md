# Typechecker wave 125

- Status: artifact batch verified; port goal active
- Date: 2026-08-26
- Main branch: `july-ultra`
- Main checkpoint before this batch: `be579e16`
- Verified code: `root/wave125-artifacts` at `5e2f9e37`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

Full repository verification passed. The fixed reports show eight new semantic
matches and no exact losses. Full upstream semantic parity remains incomplete.

## Verified results

The verified code passed these unit suites in its own build directory:

| Package | Tests passed |
|---|---:|
| `ts_binder` | 214 |
| `ts_checker` | 3,486 |
| `ts_compiler` | 208 |
| `ts_fixture` | 130 |
| `ts_scanner` | 61 |

The fixed semantic smoke run checks diagnostics, `.types`, and `.symbols`.
It executed 95 variants and retained one upstream skip. Results at the clean
verified commit are 32 exact, 56 unsupported, seven artifact mismatches, and
zero fatal invariants. Compared with wave 124, eight variants became exact
and none lost an exact match.

Evidence: `/tmp/ts-rust-wave125-final-semantic-smoke.json`.
Previous evidence: `/tmp/ts-rust-wave124-semantic-smoke.json`.

The final diagnostics-only milestone retained all 395 exact results in 511
executed variants. The other 116 remain unsupported. There are no supported
diagnostic mismatches or fatal invariants. Evidence:
`/tmp/ts-rust-wave125-final-milestone.json`.

`scripts/verify.sh` passed with the pinned upstream checkout enabled. This
includes formatting, generated AST checks, all workspace tests, strict Clippy,
and the upstream-case parser test. The parser test does not establish checker
parity. Full log: `/tmp/ts-rust-wave125-verify.log`.

## Build isolation

Each worktree must use its own Cargo target directory. Keep those directories
under the main workspace's `target/worktrees`, not on `/tmp`.

Two early branch runs reused an old test binary from a shared target directory.
They reported 3,461 passing tests, but a fresh build of the intended branch
failed compilation. Those two runs are not branch verification evidence.
An explicit manifest path alone does not prevent this cache problem.

For every branch run:

1. Supply the absolute `--manifest-path`.
2. Supply a target directory used by that worktree only.
3. Use `scripts/run-cargo-capped.sh` with its shared Git-based lock intact.
4. Confirm the compile path and a nonzero count of the expected tests.
5. Use `TS_CARGO_MEMORY_LIMIT_KIB=16777216` and `RUST_MIN_STACK=16777216`.

Root owns integration, workspace checks, Clippy, and fixture scorecards.
Owners may run only explicitly assigned focused tests through the same locked
runner. The lock keeps builds serial even when several owners queue commands.

## Prepared changes

These branches are separate from main. Focused test counts are test executions
across the named filters, not proof of full fixture coverage.

| Branch | Checkpoint | State |
|---|---|---|
| `agent/wave124-arrays` | `041b54b7` | All 25 assigned test executions passed. Iterator protocol cases remain explicitly unsupported. |
| `agent/wave124-typequery` | `b858b775` | All 22 assigned test executions passed. Full semantic fixture gate remains. |
| `agent/wave125-react-cache` | `773db606` | Eight assigned tests passed, including named global-array annotations. Integration tests remain. |
| `agent/wave125-class-parameters` | `6e115f0f` | Optional parameters and visibility checks await final review and tests. |
| `agent/wave125-construct` | `f008cb9b` | Date and optional-parameter changes await branch tests. The earlier constructor-union result fix is in the candidate. |
| `agent/wave125-conditional-display` | `a1e7716a` | All assigned focused filters passed with the repaired union dependency. Final review and artifact checks remain. |
| `agent/wave125-union-aliases` | `4380a175` | The repaired stack passed 62 focused tests. Final review and artifact checks remain. |

The earlier Boolean-call, generic-index, loop, package, computed-binding,
object-rest, JSDoc, and recursive-mapped proposals remain unmerged. Reviews
found semantic errors, weak cache checks, or fixture-specific handling.
Do not merge them based on old static approvals.

## Next work

1. Test and review each prepared feature branch before integration.
2. Finish receiver-specific Array method types and location-aware symbol display.
3. Finish conditional and generic union alias identity after cache review.
4. Rerun the fixed reports after each coherent change and retain exact matches.
5. Complete the modern-project and upstream semantic tests. Do not equate a
   diagnostics match with a full semantic match.
