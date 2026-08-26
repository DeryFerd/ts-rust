# Typechecker wave 127

- Status: verified checkpoint, port goal active
- Date: 2026-08-26
- Main branch: `july-ultra`
- Previous main checkpoint: `0e681709`
- Runtime checkpoint: `ed33229a`
- Lint follow-up: `4a6f52fe`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

The workspace tests and fixed reports retain their previous passing results.
Full upstream semantic parity and modern-project coverage remain incomplete.

## Verified results

All 6,105 workspace tests passed, with zero failures and zero ignored tests.
Strict Clippy passed for every workspace target. Formatting and generated AST
checks also passed. The workspace run included the pinned upstream parser test.

Both fixed reports identify clean source at `ed33229a`. The later commit
`4a6f52fe` only renames compiler locals and replaces two closures with
equivalent method references. Strict Clippy passed after those style changes.

The semantic smoke report compares diagnostics, `.types`, and `.symbols`:

| Outcome | Variants |
| --- | ---: |
| Executed | 95 |
| Exact | 40 |
| Unsupported | 50 |
| Artifact mismatch | 5 |
| Fatal invariant | 0 |

One upstream skip remains. These three cases became exact, with no exact losses:

- `explicitMembersBeforeInherited`
- `asyncJsxArgumentsAttributeName`
- `allowSyntheticDefaultImports9`

The diagnostics-only milestone retained all 397 exact results in 511 executed
variants. The other 114 remain unsupported. It has no new supported diagnostic
mismatches or fatal invariants. A diagnostics-only match is not semantic parity.

`jsDocTypedefTagNamespace` now has exact symbol artifacts and retains qualified
object typedef names. Its callback type still prints as a function rather than
`NS.MyCallback`, so the complete fixture is not exact.

## Integrated changes

- Generic references retain cross-file defaults and skip unused default work.
- Signature positions preserve fixed tuple and tuple-union argument rules.
- Namespace preparation retains source identity and rejects cycles before writes.
- Computed binding keys keep diagnostics and cached annotations consistent.
- JSDoc overload grouping uses decoded tag names without changing source offsets.
- Canonical project config loading handles empty roots and explicit boundaries.
- `tsgo --check-canonical PROJECT` checks an on-disk config through the canonical
  checker. It does not emit or fall back to the legacy checker. Unsupported
  checking and `noCheck` return nonzero status. Normal compile, build, and watch
  behavior is unchanged.
- Location-aware display uses visible aliases and package routes from the
  containing file. Failed queries do not retain alias or synthetic namespace writes.
- Qualified JSDoc object typedefs retain distinct identities. Warm reuse and
  display validate their full member graphs without depending on output limits.
- Generic union aliases print their stored type arguments. JSX symbol queries
  preserve their original declarations and qualified names.

## Evidence

- `/tmp/ts-rust-wave127-final-workspace.log`
- `/tmp/ts-rust-wave127-final-clippy.log`
- `/tmp/ts-rust-wave127-final-format.log`
- `/tmp/ts-rust-wave127-final-ast-kind.log`
- `/tmp/ts-rust-wave127-final-ast.log`
- `/tmp/ts-rust-wave127-final-semantic-smoke.json`
- `/tmp/ts-rust-wave127-final-milestone.json`

Comparisons use the final wave 126 semantic and milestone reports. Intermediate
logs include failed build and review attempts. They are not final evidence.

## Separate work

The iterator assembly is not part of this checkpoint. Its production library
build passes. Its latest combined checker run has 3,691 passes and 14 failures.
Thirteen of fourteen iterator kernel tests pass. The remaining failures include
type-literal method lookup, heritage composition, React members, JSX preflight,
and merged null-base classes. Those failures remain active.

Selected method queries, computed method mapping, source iterator dispatch,
merged-interface display, constructor annotations, loop repairs, global module
values, and expando functions have separate owners and worktrees. Focused tests
or an isolated review approval do not make an unmerged stack part of this gate.

The reviewed modern-project input inventory is in
[`typechecker-modern-project-inputs.md`](typechecker-modern-project-inputs.md).
Its five core repositories have 224,500 non-generated TypeScript code lines.
Fourteen selected configs are strict, with NodeNext, TSX, and JS/JSDoc inputs.
Dependencies, exact Go artifacts, forced replay, and performance evidence are
still pending. The complete modern-project TSV manifest does not exist yet.

Project graph snapshots, forced replay, the Rust project report runner, and Go
oracle overlays are prepared in separate branches. They are not in this gate.
The Rust report runner still lacks pinned project `.errors.txt` rendering.
Structured diagnostics must not be counted as that artifact.

## Build rules

Use a worktree-exclusive target directory under the main workspace's
`target/worktrees`. Keep absolute manifest paths and the shared Cargo lock.
Use `TS_CARGO_MEMORY_LIMIT_KIB=16777216` and `RUST_MIN_STACK=16777216` with
`scripts/run-cargo-capped.sh`. New production APIs need a non-test library check.

New source worktrees belong under the main workspace's `target/agent-worktrees`,
not the nearly full `/tmp` filesystem. Each writer owns named files or functions.
Root owns integration, full verification, and fixed upstream reports.
