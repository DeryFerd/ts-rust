# Artifact classification review

Reviewed fix: `8a4a11c98ef3bff8a4fe0526dc217d012dd716a8`.
Base and author report: `e38f461cf45f3e63fa522238627042267958bc0a`.
Root import, reviewed statically: `91c16a21ac228daf0d29e4cdb7fa5ab83b42ddce`.
Root parent: `3ae315e8`.
Worktree: `target/agent-worktrees/wave151/artifact-classification-final-review`.

Result: the canonical classification checks pass. One existing public-library
exact-credit defect is reproduced. It is not a new regression from the typed
error change. No production fix is included.

## Finding

### P2: library API credits unreached artifacts as exact

`run_upstream_diagnostic_baselines` accepts a request for semantic artifacts
without the canonical checker. The legacy compilation returns no generated
artifacts. `semantic_artifact_result` records both requested artifacts as
`NotReached`, but the variant path does not treat that status as a failure.
An exact diagnostic comparison can therefore return a successful summary and
one exact configuration without producing either requested artifact.

Relevant locations in this review worktree:

- `tools/ts_fixture/src/lib.rs:2444`: public runner entry has no mode guard.
- `tools/ts_fixture/src/lib.rs:1874`: absent artifacts become `NotReached` without an error detail.
- `tools/ts_fixture/src/lib.rs:2192`: the comparison checks unsupported details and mismatches, but not `NotReached`.
- `tools/ts_fixture/src/lib.rs:2223`: the resulting exact status receives exact credit.
- `tools/ts_fixture/src/main.rs:133`: the CLI rejects the same mode combination.

The smallest reproduction uses one fixture with `const value: number = 1;`
and no baselines. Call the public runner with:

```rust
RunnerOptions {
    diagnostics: true,
    semantic_artifacts: true,
    canonical_checker: false,
    ..RunnerOptions::default()
}
```

The API returns `Ok` and `summary.is_success()` is true. Its scorecard has:

```json
{
  "checkerMode": "legacy",
  "summary": { "executedVariants": 1, "exactMatches": 1 },
  "status": "exact_match",
  "outcomeClass": "exact",
  "types": "not_reached",
  "symbols": "not_reached"
}
```

This excerpt shows selected fields, not the full scorecard schema. Both
per-artifact `notReached` counters are 1. Both per-artifact exact counters are 0.
The complete record is retained in `target/review/library-api-unreached.json`.

The failing reproduction is
`review_artifact_library_api_never_credits_unreached_requested_artifacts` in
`tools/ts_fixture/tests/baseline_cli.rs`. The corresponding CLI test confirms
exit code 2 and no scorecard for this invalid flag combination. The defect is
therefore library-only. Valid canonical CLI requests did not escape as success.

Smallest fix suggestion: reject `semantic_artifacts && !canonical_checker` with
`io::ErrorKind::InvalidInput` at the public runner entry, before the fixed-manifest
branch. A separate defensive check could also forbid exact credit for requested,
unskipped `NotReached` artifacts. Neither change is made here.

The public runner entry is byte-identical in `95114a7d`, the reviewed leaf,
and the root import. The pre-fix legacy branch also returns no artifacts, and
the pre-fix comparison grants exact credit when the diagnostics match and no
checker frontier exists. This establishes the existing path by source review.
No separate pre-fix or combined-root binary was built.

## Canonical results

Real-source tests run through the compiler and `execute_diagnostic_variant`
via the public runner. They confirm these outcomes:

| Input | Outcome | Code | Exact credit |
| --- | --- | --- | ---: |
| Enum initializer with no cached artifact type | `checker_capability` | `ARTIFACT.MISSING_TYPE` | 0 |
| Callable with a property that cannot be displayed | `checker_capability` | `T07.TYPE_DISPLAY` | 0 |
| Array augmentation and ambient re-export display failure | `fatal_invariant` | `INV.SOURCE.TYPE_DISPLAY` | 0 |
| Disabled checker, including an empty source | `harness_config` | None | 0 |

The fatal source retains both TS2451 diagnostics, their ranges and messages,
and both related TS6203 records. The real CLI test keeps those records when
the diagnostic and symbol baselines differ. It exits 1, prints the complete
fatal detail, and increments the fatal counter once.

Four paired diagnostics-only controls pass, including the fatal source and the
disabled-checker source. They have no semantic-artifact scorecard. Thus
unrequested render failures do not invalidate diagnostics-only runs. The
production interface requests types and symbols together, not one selectable
artifact kind.

For classification tests, unit artifact baselines are taken from the same
fixture's successful output. They isolate classification and counters. They
are not independent Go parity evidence. The original fixture inputs were
inspected in the clean Go checkout at
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. No new Go observation was run.

## Mixed failures

A `cfg(test)` override replaces only the generated artifact results after a
real compilation. It tests both fatal/unsupported orders through the complete
variant comparison, accounting, scorecard, and output path. The tested cases
include matching and differing diagnostic baselines.

The error classes are typed. The fatal payload begins with unsupported-looking
text, and the unsupported payload begins with fatal-looking text. Each also
contains more than 2,000 characters and multiple lines. Fatal priority follows
the class, not the text. Both complete per-artifact details, the selected
frontier detail, and the fatal output remain intact. Diagnostic records remain
unchanged, the fatal count is 1, and exact credit is 0.

The CLI links the normal library without this override. Its tests use real
checker failures. Removing the two `cfg(test)` additions reproduces the base
`lib.rs` byte for byte. `artifacts/mod.rs` is unchanged. No non-test
implementation was edited.

## Root adaptation

The root import combines the old class-error imports with the new display-error
imports. The existing class classifier and
`class_query_errors_keep_unsupported_and_invariant_outcomes_separate` test are
unchanged. The new `artifact_failure` query follows `render_error_baseline`.
No leaf corpus-evidence code was copied into the older root.

The leaf and root have byte-identical implementations of
`semantic_artifact_result`, `semantic_artifact_failure`, and
`comparison_frontier`. The static check found no adaptation defect. Root's
combined runtime verification remains separate.

## Verification

Session `46084` is collected and exited 101 for the single library-API defect
probe. The run passed 50 of 51 selected tests. None were ignored.

| Target | Passed | Failed | Runtime |
| --- | ---: | ---: | --- |
| Library artifact tests | 35 | 0 | 41.77s |
| CLI artifact tests | 15 | 1 | 17.89s |

All 43 original artifact controls pass. Seven of the eight added review tests
pass. The eighth is the retained failing reproduction above. The build took
1m 02s after the shared lock became available. The unchanged checker emitted
the same 18 warnings reported by the author.

Log: `target/review/artifact-tests.log`.
SHA-256: `72f92cbc2cce9cd5a54ac5db750c0e167e5a68d3e4bdbc92da9b87f88e3da418`.

Bad API scorecard: `target/review/library-api-unreached.json`.
SHA-256: `015e10187f2ca14004724c5fd736d7736cc7af5eff3d63668210550d99b7ef21`.

The 13 library execution records and their output are retained under
`target/review/cases`. Source hashes before and after the run match. The review
does not claim a full workspace run or root-runtime pass.

## Preserved history

The completed run-2 `attempt-00001` and `attempt-00002` records under
`target/agent-worktrees/wave146/full-frozen-corpus-execution/target/corpus-execution`
still contain the same 17 historical `harness_config` failures. All six
scorecard, evidence, and process hashes match the author's report before and
after this review. No saved row was relabeled from error text. No historical
or live corpus output was written or copied.

## Build provenance

This new physical worktree began with no Cargo target directory. The first
build created its own target at
`target/worktrees/wave151-artifact-classification-final-review`. No artifact or
fingerprint was copied, reflinked, or hardlinked from another source tree.
No run in this review is affected by the target-copy rule.

The command used the absolute root capped runner, an absolute manifest,
locked offline dependencies, 16 GiB memory, 16 MiB process and Rust stacks,
the unchanged common lock, and unchanged `TMPDIR`. Source stayed fixed while
the command waited and ran. All owned command sessions are collected.

Reproduce with the same limits and the root runner:

```text
test --manifest-path <absolute-worktree>/Cargo.toml --offline --locked --no-fail-fast
  -p ts_fixture --lib --test baseline_cli artifact -- --nocapture
```

Set `TS_ARTIFACT_CLASS_REVIEW_DIR` to an owned output directory to retain the
unit execution records. The failing API probe is intentionally not ignored.
