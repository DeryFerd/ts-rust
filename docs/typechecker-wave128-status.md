# Typechecker wave 128

- Status: verified checkpoint, full port goal active
- Date: 2026-08-26
- Main branch: `july-ultra`
- Previous main checkpoint: `b1acb9e5`
- Runtime checkpoint: `df2ba7bc`
- Lint follow-up: `4a7102b6`, `f07dc2f1`
- Upstream: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

The fixed reports retain every previous exact result. Full upstream semantic
parity and modern-project parity remain incomplete.

## Verified results

All 6,173 workspace tests passed at `df2ba7bc`, with zero failures and zero
ignored tests. The run included the pinned upstream parser cases. Formatting
and both generated AST checks passed.

Strict workspace Clippy passed for every target at `f07dc2f1`. The lint changes
add a `must_use` attribute, use equivalent method references, and extract two
unchanged helper bodies. A 64 KiB file-hashing buffer now uses the heap. Its
input selection, read size, and hash algorithm are unchanged. All 139 fixture
unit tests and five project-report tests also passed after these changes.
Formatting passed for all changed Rust files.

The semantic smoke report compares diagnostics, `.types`, and `.symbols`:

| Outcome | Variants |
| --- | ---: |
| Executed | 95 |
| Exact | 47 |
| Unsupported | 46 |
| Artifact mismatch | 2 |
| Fatal invariant | 0 |

One upstream skip remains. Seven cases became exact, with no exact losses:

- `automaticTypeDirectiveResolutionBundler`
- `declarationEmitSubpathImportsReexport`
- `moduleKeywordSkipLibCheck`
- `parameterPropertyWithDefaultValue`
- `abstractClassUnionInstantiation`
- `jsxElementTypeUnexpectedType`
- `jsxLibraryManagedAttributesUnexpectedType`

The remaining artifact mismatches are `functionExpandoPropertyDeclaration` and
`jsDocTypedefTagNamespace`. The diagnostic-only milestone retains 397 exact
results in 511 executed variants. Its other 114 results remain unsupported.
It has no status changes, exact losses, supported diagnostic mismatches, or
fatal invariants. Diagnostic-only equality is not semantic parity.

Both fixed reports identify clean source at `df2ba7bc`. The later lint commits
do not change checker behavior or artifact formatting rules.

## Integrated changes

- Constructor unions use source declaration order and preserve canonical
  identities. Shared ownership checks use retained binder declarations.
- Merged interface display validates declaration, scope, and member ownership.
- Canonical binding and checking use pinned library priorities without moving
  source storage or changing `FileId` values.
- Module values resolve lazily. Namespace queries and source execution retain
  the same identities, including recursive namespace and class use.
- Type-reference symbol queries preserve import aliases.
- Enum declarations and their names return the declared type. Value queries
  retain the separate value type. The query rejects changed caches, unrelated
  declarations, forged flags, and chained owner redirects before publication.
- The compiler exposes owned graph observations and forced source replay.
  The project runner reports available diagnostics and semantic artifacts,
  checks query identities, and keeps missing evidence explicit.
- Project reports retain location-specific package choices. Manifest failures
  use stable paths and source ranges instead of process-local node IDs.
- Test-path replacement uses one ordered pass, matching pinned Go behavior.

## Evidence

- `/tmp/ts-rust-wave129-final-workspace.log`
- `/tmp/ts-rust-wave129-final-format.log`
- `/tmp/ts-rust-wave129-final-ast-kind.log`
- `/tmp/ts-rust-wave129-final-ast.log`
- `/tmp/ts-rust-wave129-final-semantic-smoke.json`
- `/tmp/ts-rust-wave129-final-milestone.json`
- `/tmp/ts-rust-wave129-primary-lints-clippy-2.log`
- `/tmp/ts-rust-wave129-primary-lints-tests.log`
- `/tmp/ts-rust-wave129-primary-lints-format.log`

Comparisons use the final wave 127 reports. Earlier logs include failed test
fixtures and review attempts. They are not final verification evidence.

## Separate work

The held iterator branch at `a39fb88d` passes all 3,734 checker unit tests.
Its source adapter remains separate and incomplete. Passing kernel tests does
not establish source-level iterator support.

Constructor composition, selected member queries, loop effects, expando flow,
and JSDoc callback aliases still have separate implementation and review work.
The next project-loading batch contains reviewed `noLib`, dependency-order,
and mode-specific module-target fixes. It is not part of this checkpoint.

All seven project dependency inputs now have isolated prepared copies under
`target/project-inputs`. Their scripts and evidence have separate reviews.
No complete modern-project manifest or passing project ring is claimed.

Initial Go runs for Hono and ts-pattern are not parity passes. Follow-up probes
show that artifact queries can add diagnostics and return fresh type objects
without source reset. The replay contract is under review. Existing reports
and gates have not been relaxed or relabeled.

The current project runner still lacks the separately developed exact project
`.errors.txt` renderer. Config parse inputs, package facts, source realpaths,
fresh diagnostic evidence, and other graph limits remain explicit where they
are unavailable. Structured diagnostics do not replace exact artifact bytes.

## Build rules

Use `scripts/run-cargo-capped.sh`, an absolute manifest path, the shared Cargo
lock, and a target directory exclusive to each physical worktree. Set
`TS_CARGO_MEMORY_LIMIT_KIB=16777216` and `RUST_MIN_STACK=16777216`.

New source worktrees and large outputs belong under the main workspace's
`target` directory. Keep the pinned upstream checkout and global toolchains
unchanged. Do not mark the full port complete from this checkpoint.
