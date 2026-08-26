# Typechecker wave 125

- Status: active
- Date: 2026-08-26
- Main branch: `july-ultra`
- Main checkpoint before this batch: `be579e16`
- Tested candidate: `root/wave125-artifacts` at `98aa6b62`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

The candidate is not yet merged. Its remaining cold-class display review and
workspace checks must pass first. The full port goal remains active.

## Verified results

The candidate passed these unit suites in its own build directory:

| Package | Tests passed |
|---|---:|
| `ts_binder` | 214 |
| `ts_checker` | 3,484 |
| `ts_compiler` | 208 |
| `ts_fixture` | 130 |
| `ts_scanner` | 61 |

The fixed semantic smoke run checks diagnostics, `.types`, and `.symbols`.
It executed 95 variants and retained one upstream skip. Results at the clean
candidate commit are 32 exact, 56 unsupported, seven artifact mismatches, and
zero fatal invariants. Compared with wave 124, eight variants became exact
and none lost an exact match.

Evidence: `/tmp/ts-rust-wave125-semantic-smoke.json`.
Previous evidence: `/tmp/ts-rust-wave124-semantic-smoke.json`.

The previous diagnostics-only milestone has 395 exact results in 511 executed
variants. It does not establish semantic parity. Its evidence is
`/tmp/ts-rust-wave124-milestone.json`.

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
| `agent/wave125-react-cache` | `b6610908` | Eight assigned tests passed. Review found a named global-array annotation case still being repaired. |
| `agent/wave125-class-parameters` | `6e115f0f` | Optional parameters and visibility checks await final review and tests. |
| `agent/wave125-construct` | `f008cb9b` | Date and optional-parameter changes await branch tests. The earlier constructor-union result fix is in the candidate. |
| `agent/wave125-conditional-display` | `751d4fe2` | New alias proofs await review and tests. Depends on the held union changes. |
| `agent/wave125-union-aliases` | `b3b59580` | Held for alias instantiation, cache, and origin repairs. |

The earlier Boolean-call, generic-index, loop, package, computed-binding,
object-rest, JSDoc, and recursive-mapped proposals remain unmerged. Reviews
found semantic errors, weak cache checks, or fixture-specific handling.
Do not merge them based on old static approvals.

## Next gates

1. Finish the cold-class display review without requiring member algorithms
   just to print a class name.
2. Pass the public artifact query tests, workspace formatting, generated AST
   checks, and strict Clippy on the final candidate.
3. Rerun the fixed scorecards from a clean commit and retain exact matches.
4. Merge only verified changes into `july-ultra`.
5. Test each prepared feature branch before integration. Do not equate a
   diagnostics match with a full semantic match.
