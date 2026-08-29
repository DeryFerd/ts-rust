# Typechecker checkpoint after Date and decorator repairs

Tested source: `f1fbca702306d5d98bc81868d5d1d1a8a0c79d04`.
Pinned Go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

The full workspace passes. The original-case checkpoint is not accepted yet.
One previously exact arrow-function case now fails. No modern-project pass or
primary-branch promotion is claimed.

## Verified results

These groups overlap. Do not add them to get a unique test count.

| Check | Result |
| --- | --- |
| Full workspace | 7,219 passed, zero failed, zero ignored |
| Fixed diagnostics | 417 exact, 93 unsupported, one fatal in 511 variants |
| Supplementary originals | All 85 exact across 69 reports |
| Extra originals | 36 exact, one known header mismatch, two known fatal results in 39 variants |
| Newly integrated originals | All ten exact across seven reports |
| Parser retention | Six exact and one unchanged unsupported result in seven variants |
| Semantic smoke | 55 exact, 33 unsupported, two artifact mismatches, five fatal results in 95 variants |

Formatting, both generated AST checks, and strict workspace Clippy passed.
Clippy checked all targets with `-D warnings`. The workspace test command used
`--workspace --no-fail-fast --locked --offline` with `TS_GO_REPO` set.
All 246 target summaries completed.

Semantic smoke has 50 exact type artifacts and 59 exact symbol artifacts.
Each artifact group has 89 expected baselines. These are not full-project
typechecking results.

## What changed

The Date parameter-property original and its extended case are exact again.
The anonymous-decorator symbol artifact is also exact again. That decorator
case still has its earlier unsupported type query.

The JS conditional case and all four package-export module modes are now exact
in the new-original group. The namespace, conditional, and automatic-type
changes are part of this tested source.

Every previously exact supplementary, extra, and parser record is retained.
Every previously exact semantic record and individual semantic artifact is
retained against both the wave148 and pre-Date reports. The five remaining
semantic fatal outcomes are unchanged from the pre-Date report. They remain
open work, not accepted behavior.

## New regression

`arrowFunctionWithObjectLiteralBody5.ts` changed from exact to
`INV.SOURCE.FUNCTION`. Its key is
`v1:17297efacef36d7db22b8b7802774cb8`.
The failure is at the first arrow, which returns an asserted `Error` object.
This replaces the repaired Date failure in the fixed total. The unchanged
count of 417 exact cases therefore does not show retention.

A bounded debugger trace confirmed the failing return-type validation.
The new default-library property validator expects an optional read union.
The nongeneric property publisher stores the raw annotation instead.
`Error.stack` therefore has a valid stored `string` type that the validator
rejects. The repair must validate that raw type and preserve optional reads,
source ownership, array checks, and the complete declared-method dependency
checks. Do not accept both raw and derived cache forms.

The repair is in a separate worktree. It adds a cache-corruption control and
checks all four arrows in the unchanged original. It is not part of this
checkpoint's measured results.

## Execution

The integration worktree is
`target/agent-worktrees/wave154/root-global-export-composition`.
Its dedicated build target is
`target/worktrees/wave154-root-global-export-composition`.

Baseline binary SHA-256:
`ac762a5524eb73db6c6e9e78303530ac9b479e9fc27c7e6c145384c15cef8b20`.
Project-oracle binary SHA-256:
`4fc2f32058cfa0ad3eeaee864320a3bf72d0cee8cf56f2e3f67bee05ea1bfebe`.

The source, binary, and pinned Go checkout were checked before and after the
runs. All original inputs, options, baselines, selected variant keys, and
non-Rust provenance stayed unchanged. The fixed group keeps its one upstream
skip. Supplementary and extra groups keep six and one skips.

Builds used the absolute capped Cargo runner, the shared Cargo lock, locked
offline dependencies, and a 16 GiB memory limit. Original fixture processes
used the shared diagnostic lock, a 16 GiB memory limit, no swap, an 8 MiB main
stack, and 64 GiB virtual memory. Timeouts stayed at 1,200 seconds for fixed
groups and 300 seconds for individual reports. No limit was raised to pass
an original.

## Evidence

The structured result is `docs/typechecker-wave196-verified-checkpoint.json`.
It retains the report hashes and corpus identities.

Complete logs and reports remain in the primary workspace:

- `target/wave196-combined-*.log`
- `target/wave196-verified-original-cases/`
- `target/wave196-verified-extra-originals/`
- `target/wave196-verified-new-originals/`
- `target/wave196-verified-semantic-smoke.json`
- `target/wave196-verified-fixed-vs-*.json`
- `target/wave196-verified-supplementary-extra-comparisons.json`
- `target/wave196-verified-new-parser-comparisons.json`
- `target/wave196-verified-semantic-vs-*.json`
- `target/wave197-arrow-return-trace.log`

Full-record comparisons cover both wave193 and wave194 diagnostics, plus the
pre-Date fixed report. Semantic comparisons also check each previously exact
type and symbol artifact separately. A successful runner exit is not treated
as an exact result.

The React mapped-type and constructor-value workers have separate builds and
test results. Their unmerged code does not contribute to these numbers.
