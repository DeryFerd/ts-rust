# Typechecker wave 126

- Status: verified checkpoint; port goal active
- Date: 2026-08-26
- Main branch: `july-ultra`
- Previous main checkpoint: `0b314d97`
- Verified code: `c440602d` on `root/wave126-integration`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

The repository checks pass. The fixed reports retain every previous exact
match. Full upstream semantic parity and modern-project coverage remain
incomplete.

## Verified results

The full workspace run passed 6,001 tests with zero failures and zero ignored
tests. This includes 3,567 checker unit tests and the pinned upstream parser
test. Strict Clippy passed for all workspace targets. Formatting and generated
AST checks also passed.

The semantic smoke report compares diagnostics, `.types`, and `.symbols`:

| Outcome | Variants |
|---|---:|
| Executed | 95 |
| Exact | 37 |
| Unsupported | 50 |
| Artifact mismatch | 8 |
| Fatal invariant | 0 |

One upstream skip remains. Five variants became exact, with no exact losses:

- `inferFromTupleRestAndVariadic`
- `constructSignatureWithInferReturnType`
- `sliceTupleTypeOutOfBounds`
- `stringMappingSpecialCasing`
- `templateLiteralInferenceSupplementarySplit`

Two cases that previously stopped at an arrow query now expose existing type
display gaps: `functionExpandoPropertyDeclaration` and
`jsDocTypedefTagNamespace`. They are not exact matches. The Array callback
fixture now has receiver-specific types, but its constructor union order still
differs from upstream.

The diagnostics-only milestone has 397 exact results in 511 executed variants.
The other 114 remain unsupported. There are no supported diagnostic
mismatches, exact losses, or fatal invariants. The two new exact cases are
`noTypeToStringStackOverflow` and `parameterPropertyWithDefaultValue`.

A separate full-artifact run of `noTypeToStringStackOverflow` is exact in all
three artifacts. Both expected diagnostics remain present.

## Evidence

All final reports identify clean code at `c440602d`.

- `/tmp/ts-rust-wave126-final-workspace.log`
- `/tmp/ts-rust-wave126-final-clippy.log`
- `/tmp/ts-rust-wave126-final-semantic-smoke.json`
- `/tmp/ts-rust-wave126-final-milestone.json`
- `/tmp/ts-rust-wave126-final-typequery.json`

Comparisons use `/tmp/ts-rust-wave125-final-semantic-smoke.json` and
`/tmp/ts-rust-wave125-final-milestone.json`. The earlier wave 126 logs include
failed intermediate runs and are not final verification evidence.

## Integrated changes

- Arrow location queries use the checked callable identity. They retain
  private arrow symbols and reject inconsistent declaration, node, and return
  caches.
- Inferred returns retain a checked identity independent of raw signature
  cache writes. Recovery still requires a real return cycle.
- Imported namespace value queries preserve array annotations, arity recovery,
  source-order independence, and bounded annotation cycles.
- Date constructor queries and optional constructor parameters retain their
  source identities. Private and protected access and assignment diagnostics
  use the declaring class.
- Array methods retain receiver-specific callback types and validate supported
  constraints and defaults before mapping.
- Generic union and conditional aliases retain source identities and private
  creation records. The formatter consumes validated conditional aliases.
- Computed literal keys use ordinary expression checking and keep their literal
  query types.

## Separate work

These branches are not part of this checkpoint. Focused test results do not
establish full artifact parity.

| Work | Last reported state |
|---|---|
| Direct generic references | `f01d7b6f`, 12 focused executions passed; full integration pending |
| Array-like binding reads | `254f326f`, 28 focused tests passed; inherited-only interfaces remain unsupported |
| Iterator protocol | `36556725`, six focused tests passed and two failed; source integration still needs method providers |
| Generic interface heritage | `40c1d173`, three production tests remain failing; identity and inherited proxy work continues |
| Computed and optional methods | `9cd5232e`, rest binding tests pass; optional publication is incomplete |
| Signature positions | `e1cdc04b`, production check and 131 focused tests passed; final review pending |
| Constructor annotations | `e6ac3b33`, implementation prepared; focused verification pending |
| Merged interface display | `7c33ae1d`, 81 formatter tests passed; hostless ownership and paired property-cache findings remain |
| Location-aware display | `3a1df482`, 21 focused tests passed; binding context, package routes, and synthetic namespace rollback still need repair |
| Namespace import preparation | `b552cb22`, 133 focused tests passed and final semantic review approved; integration pending |
| Computed binding keys | `e2c005fc`, production check and 24 focused tests passed; final cache review pending |
| Canonical project config | `d967ec00`, 16 public tests passed; final empty-project review pending |
| JSDoc overload grouping | `d4cb6905`, three parser and nine checker tests passed; final review pending |
| Expando, typedef, and union-order display | Separate owners are repairing the remaining artifact differences |

The older loop, Boolean-call, generic-index, spread, and recursive-mapped
proposals remain held. Do not integrate them from old approvals alone.

## Build and ownership rules

Each worker has a separate worktree and named file or function ownership. Root
owns integration, full checks, and fixture reports. Workers run only assigned
focused checks through the shared Cargo lock.

Use an absolute manifest path and a target directory exclusive to the
worktree. Keep build output under the main workspace's `target/worktrees`, not
on `/tmp`. Shared target directories previously reused stale binaries.

Use `TS_CARGO_MEMORY_LIMIT_KIB=16777216` and `RUST_MIN_STACK=16777216` with
`scripts/run-cargo-capped.sh`. Do not remove its shared Git-based lock. New
production APIs also need a non-test `check --lib`; unit tests can hide uses of
test-only helpers.

The canonical project config API is not yet in main. The current project CLI
still uses the legacy checker. There is no verified modern-project manifest or
project ring, and diagnostics-only matches do not close that gap.
