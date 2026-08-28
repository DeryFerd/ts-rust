# Export assignment grammar

The exact `exportAssignmentMerging4.ts` case now reports TS2309.
The base is `4327f7f345c90d59d6057a3f53c4d1c0e81eed9c`.
The Go pin is `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

## Result

The original variant is `v1:d6fd977e671fa29c9c218343947206f4`. It uses
CommonJS, declaration output, strict checking, ES2025, Node10 resolution, and
the normal libraries. Its current directory is `/.src`. Its only root is
`/.src/b.ts`, which imports `a.ts`.

The clean base reported no diagnostics. The repair reports the expected
TS2309 at `/.src/a.ts`, byte 134, length 30. The header, code, span, message,
and order comparisons have no mismatch. There is no unsupported result or
fatal invariant.

The full fixture still fails because two existing artifacts differ:

- Types, line 20: `a.Foo` versus `import("./a").Foo`.
- Symbols, line 22: `Symbol(a.Foo, ...)` versus `Symbol(Foo, ...)`.

Both artifact records, including their visited-node counts, match the base
records exactly. This repair does not claim full fixture parity.

## Implementation

`source.rs` checks module exports after source value publication and after
accepted ambient namespace exports merge. The new helpers follow pinned
`checkExternalModuleExports`, `hasExportedMembersOfKind`, and
`hasShadowedNamespace` in Go's `internal/checker/checker.go`.

Value exports use `CanonicalSymbolFlagsResolver`. Namespace targets use
`CanonicalAliasResolver`. Type-only exports remain allowed unless the
exported namespace also has exported types or namespaces and the export
assignment has the namespace meaning required by Go's rule.

Go's `bindCommonJSTypeExports` promotes direct type and namespace exports
onto export= in TypeScript and ambient modules. The current Rust binder only
does this for CommonJS source facts. The grammar helper reads those same raw
export flags when the namespace flag is absent. It does not change symbols,
export tables, or namespace types. A named alias does not count as this raw
promotion. A negative control checks that distinction.

The diagnostic uses the last alias declaration, or the value declaration for
a non-alias export. The existing `alias_declaration` method only gains
`pub(super)` visibility. Its body is unchanged. The external module
augmentation exception checks the actual module parents and source facts.

No artifact query, source-admission rule, binder, class construction, namespace
construction, imported-enum query, compiler mode, or baseline changed.

## Validation

Every session below completed and was collected.

| Session | Check | Result |
| --- | --- | --- |
| `20600` | Clean base, exact corpus variant | Exit 1. Missing TS2309 and the existing artifacts. |
| `93309` | Final export-related tests | Exit 0. 340 passed, none failed or ignored. |
| `12661` | Final exact corpus variant | Exit 1. Diagnostics match. Existing artifacts still differ. |
| `51635` | Strict fixture-test Clippy, no dependency linting | Exit 0. |
| `81447` | Strict checker Clippy | Exit 101. The same 23 errors in eight unchanged files. |
| `21019` | Fresh pinned Go comparison | Exit 0. All 17 controls match. |

The 340 passing tests include 322 checker units, 12 compiler units, the
unchanged public export-equals artifact test, two fixture units, and three new
fixture tests. Public tests check exact diagnostics after two source replays.
Checker units also check repeated grammar calls and augmentation parent rules.

The 17 Go controls cover 12 public programs and five bound-module grammar
controls. The five bound controls do not claim public source support. They
include a named value that is also the assignment target, implicit type-only
named exports, and runtime namespaces with const members. Those programs still
hit existing source-checking limits. The public controls use supported explicit
type exports and runtime var namespaces as well.

The earlier 13 Go input records retain their exact bytes. Four added controls
check the raw promotion rule and the supported public forms. The final public
helper uses ES2025. Earlier ES5 test results remain separate evidence and are
not used as proof of the exact corpus configuration.

Both Clippy commands deny `clippy::all` and `clippy::pedantic`. The checker
errors match the earlier error messages, paths, lines, and columns. All eight
files match their base-commit bytes. The 18 existing dead-code warnings remain.
No unrelated lint was suppressed or fixed. Rustfmt and whitespace checks pass.

## Inputs and execution

The fixture copy retains all 382 original bytes. Its SHA-256 is
`e76399b4cc5db8cd74a623bb9cea6d18522ab6ef05b781cdd8f1dcd7de250b0c`.
A fixture-local Git rule preserves those bytes without line-ending conversion
and recognizes the upstream CRLF endings during whitespace checks.
The unchanged error baseline has SHA-256
`445a0a1edbbf8e60638c9097ad3f752f911b5e70b5f06935743866d508081943`.

`Case::parse` produces `a.ts` at 164 bytes and `b.ts` at 121 bytes. Their
XXH3-128 hashes are `a733dd29c272bf0d2001451f505920b9` and
`b79224631f4527bf729b36ddce9cb855`. The same parsed units feed Rust and Go.

The saved Go compiler has SHA-256
`204f15c767025fc9238b748399be7d1293f6d0f8ea9ddec8eab65995ecf4bb39`.
Its build metadata records the clean pin above and Go 1.26.4. The Go checkout
also remains clean at that pin.

The worktree is `target/agent-worktrees/wave149/export-assignment-merging-diagnostic`.
Its private Cargo target started empty. No artifacts or fingerprints were
copied from another target. All Cargo commands used the root capped runner,
an absolute manifest, `--locked --offline`, 16 GiB memory, 16 MiB process and
Rust stacks, the common lock, and unchanged TMPDIR.

The worktree's `target/review/run-v4.sh` records the exact commands. Its
`sources-v4.sha256` file records the eight hashes checked before and after
each run. The final source.rs hash is
`90bec0d67ac50f3f72096c8e5bda4567798fe6b0aa5b6ab664113542b4e87a31`.
Logs, both corpus scorecards, and `go-results-v4.json` are in `target/review`.
