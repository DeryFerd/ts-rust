# Real-project binder declaration names

The implementation starts at compiler commit `3947c8ba`. The parser, AST,
and binder have no changes from frozen evidence commit `400b2072`. The
frozen worktree and reports remain unchanged.

## Exact node maps

Both prepared source hashes match their original source manifests. A probe
through `CanonicalBinder` reproduced both failures before binder edits.

| Project | Node | Source location | Actual syntax |
| --- | --- | --- | --- |
| ts-pattern | `NodeId(2097)` | `src/patterns.ts:541`, bytes `16251..16771` | Arrow function assigned to computed property `[matcher]` |
| Hono | `NodeId(908)` | `src/router/reg-exp-router/prepared-router.ts:147`, bytes `4449..4515` | `all[1][i] = all[1][i] ? [] : (0 as unknown as HandlerData<string>)` |

Both original calls returned `UnsupportedDeclarationFamily` before any
symbol writes. These are incorrect declaration-name preflight rejections,
not missing statement traversal.

The verified source file SHA-256 values are:

- ts-pattern `patterns.ts`: `f14c0cb52f00ed9477e60caa677b2d9ca9212693d8b999708616d087afacf5a9`.
- Hono `prepared-router.ts`: `58d3056767f5be328c8bc8003e3cceb388f046a1ff6798ca049272ee1510cdab`.

## Pinned algorithm

The port follows TypeScript-Go commit
`dc37b5249ab60e2bbce936f71b883e6c8136167e`:

- `internal/binder/binder.go`, `bindFunctionExpression` and
  `bindClassLikeDeclaration`, give unnamed expressions their own function
  or class symbol. An assigned computed property name does not replace it.
- `internal/ast/utilities.go`, `GetNonAssignedNameOfDeclaration` and
  `GetAssignmentDeclarationKind`, use the source language to classify
  assignment declarations. A nested element-access base such as `all[1]`
  is not a TypeScript entity-name expression.
- `internal/binder/binder.go`, `bindDeferredExpandoAssignments`, retains
  declaration order and uses the existing symbol owner for real expandos.

The Rust preflight now accepts the existing anonymous expression binding
route. Assignment preflight, naming, and the deferred queue share source
language classification. The language comes from `CanonicalSourceFileFacts`,
not a filename or a reconstructed parser context.

All changed interfaces are private to the binder. Symbol allocation,
declaration merging, owner tables, and source identities keep their existing
implementations. No input files, configs, dependencies, exclusions, or
checker code changed.

## Validation

All 216 binder unit tests pass. Binder-only Clippy passes with `-D warnings`.
The added controls check anonymous initializer symbols, computed property
ownership, unallocated member tables, file identity, shared-store extraction,
and the different TypeScript and JavaScript assignment declaration rules.
The existing atomicity control now places a valid computed initializer before
an unsupported declaration.

The public binder probe now completes declarations for both unchanged files:

| Project file | Binding phase | Symbols | Parser diagnostics |
| --- | --- | --- | --- |
| ts-pattern `src/patterns.ts` | `Declarations` | 743 | 32 |
| Hono `prepared-router.ts` | `Declarations` | 119 | 0 |

The original source hashes still match after these runs. These are single-file
binder results, not complete project checks. The existing
`canonical_config_preserves_inherited_inputs_and_declaration_module_graph`
control also passes.

All Cargo commands used the shared capped runner, a 16 GiB memory cap,
`RUST_MIN_STACK=16777216`, `--locked --offline`, an absolute manifest path,
and the exclusive `wave132-project-binder-families` build target.

Evidence is under `target/project-evidence/wave132-binder-families` in the
main workspace. The node map is `node-maps.json`. The temporary probe source
is archived there as `project_declaration_probe.rs`.

The passing binder, probe, and graph logs have the `attempt-2` suffix. The first
attempt logs retain an intermediate compile error from a missed source-fact
call site. Clippy passed on its first run.

## Full-project reruns

The reporter was built from clean commit
`3c0dfb2dd6fc284cb7ee151e9b236c7de4f51b59`. Each original config ran in two
fresh processes. Both processes reproduced the same result for each project:

| Project | Result | Source |
| --- | --- | --- |
| ts-pattern | Unsupported `E00.SOURCE_SYNTAX`, class `NodeId(42)` | `src/errors.ts`, `NonExhaustiveError` |
| Hono | Unsupported `E00.SOURCE_SYNTAX`, class `NodeId(128)` | `src/http-exception.ts`, `HTTPException` |

Both projects now reach source checking instead of stopping at declaration
binding. The next owner is the source checker. Both reported declarations
extend `Error`, but the reports do not identify a narrower unsupported
operation. No source-checker code was changed in this work.

All four process exits were 0 because the reporter wrote its report. Checking
did not complete. Rust graphs, diagnostic artifacts, types, symbols, and replay
remain unavailable. There is no root, option, or resolution comparison with Go.

The before and after input snapshots are byte-identical. They also match the
frozen input snapshots from the `400b2072` runs. The executable hash stayed
unchanged across all four processes:
`a751cf5d14a85a27ad0cbe9b54d2bf2c108a2af0293d01ce11e656c71775b263`.

`project-summary.json` records the four reports, process IDs, hashes, and
unavailable stages. Raw reports and run records are under
`project-runs/3c0dfb2dd6fc284cb7ee151e9b236c7de4f51b59` in the evidence folder.
Input checks verify bytes at checkpoints, not a filesystem-read trace. Prepared
source manifests identify each project. Reporter Git ancestry can identify the
compiler repository because the prepared inputs are extracted archives.

The unchanged ts-pattern source also produces parser diagnostics. Those
diagnostics start at `export type infer<pattern>` on line 116 and generic
arrows with `const` type parameters on lines 817, 831, 845, 857, and 869.
These are a separate parser task. Full-project parity and performance remain
unproven.
