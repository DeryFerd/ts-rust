# Artifact library mode guard

Base and review: `41b3d51de1d5594cffd758ff9267e16d77301d52`.
Branch: `agent/wave152-artifact-library-mode-guard`.
Worktree: `target/agent-worktrees/wave152/artifact-library-mode-guard`.

Status: repair verified. All 53 focused tests pass, including the unchanged
review reproduction that previously received false exact credit.

## Change

`run_upstream_diagnostic_baselines` now rejects
`semantic_artifacts && !canonical_checker` at its public entry. It returns an
`io::Error` with `InvalidInput` and the CLI's existing text:

```text
--semantic-artifacts requires --canonical-checker
```

The guard runs before fixed-manifest dispatch, fixture discovery, compilation,
comparison, counters, or scorecard writes. Invalid requests cannot reach the
old path that credited two `NotReached` artifacts as an exact configuration.

The production change is six guard lines and two error-documentation lines in
`tools/ts_fixture/src/lib.rs`. The CLI production code, artifact classifier,
comparison logic, and root's separate global binding work are unchanged.
Legacy diagnostics-only requests and valid canonical artifact requests remain
available. A disabled checker inside a valid canonical request still uses the
existing `harness_config` result.

## Tests

Two API/CLI parity tests were added:

- Normal and fixed-manifest requests use a missing repository and a missing
  manifest. Both are rejected with the same message before those paths can be
  read. API output stays empty. The CLI exits 2 with empty standard output.
  Existing scorecard bytes remain unchanged after both calls.
- Valid legacy diagnostics-only calls still succeed through both API and CLI.
  Their summaries and variant records agree, with no semantic-artifact record.

The original failing review probe is byte-identical to its reviewed version.
It now passes because the API returns `InvalidInput`. The complete prior review
suite also passes, including real typed failures, fatal priority in both
artifact orders, diagnostic detail preservation, and diagnostics-only isolation.

## Verification

Session `14933` is collected and exited 0. The first build in the new empty
target took 1m 00s. The unchanged checker emitted its 18 existing warnings.

| Target | Passed | Failed | Runtime |
| --- | ---: | ---: | --- |
| Library artifact controls | 35 | 0 | 42.18s |
| CLI and API artifact controls | 18 | 0 | 20.02s |

None of the 53 selected tests failed or were ignored. This includes all 51
review tests and the two new parity tests. No Clippy, full workspace, frozen
corpus, combined-root runtime, or new Go run is claimed.

Log: `target/review/artifact-tests.log`.
SHA-256: `632d537d37e2e0246656724437c5f6a0d74bcb20c8778220826250179f145ec2`.

The source hashes are unchanged before and after the run:

- `tools/ts_fixture/src/lib.rs`: `876c91d4a367016a8ef2cb72b541dfa2de36b868f7404950de8f69acce39e1e2`.
- `tools/ts_fixture/tests/baseline_cli.rs`: `ed120390c923c7c9a599a8c0268bc5f024b2e085cdd5698fde8476b2870d0a11`.

## Preserved evidence

The prior review report, test module, shared inputs, and failing probe remain
unchanged. Its original failed run and bad scorecard remain in the wave151
review worktree with these hashes:

- Review log: `72f92cbc2cce9cd5a54ac5db750c0e167e5a68d3e4bdbc92da9b87f88e3da418`.
- Bad scorecard: `015e10187f2ca14004724c5fd736d7736cc7af5eff3d63668210550d99b7ef21`.

All 17 historical failure rows in completed run-2 attempts `00001` and `00002`
retain their original classifications. The six scorecard, evidence, and process
hashes still match the original report. No historical row or live corpus output
was edited, relabeled, or copied.

## Build provenance

This separate physical worktree began without a Cargo target directory. Cargo
created its own target at `target/worktrees/wave152-artifact-library-mode-guard`.
No output or fingerprint was copied, reflinked, or hardlinked from another tree.
No run is affected by the target-copy rule.

The command used the absolute root capped runner, an absolute manifest, locked
offline dependencies, 16 GiB memory, 16 MiB process and Rust stacks, the unchanged
common lock, and unchanged `TMPDIR`. Source stayed fixed while the command was
queued and running. All owned sessions are collected.

Reproduce with the same limits and the root runner:

```text
test --manifest-path <absolute-worktree>/Cargo.toml --offline --locked --no-fail-fast
  -p ts_fixture --lib --test baseline_cli artifact -- --nocapture
```
