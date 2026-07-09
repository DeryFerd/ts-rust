# Implementation breakdown

This document preserves the detailed implementation map and development
commands that used to live in the README. It describes code that exists in the
repository, not a promise of production readiness or `typescript-go` parity.
See the [README](../README.md#current-state) for the current audit and
[minimal working v0](minimal-working-v0.md) for the supported contract.

## Compiler layers

The implementation is split into layers so they can be exercised against
upstream TypeScript fixtures independently:

- `ts_core`: source positions and diagnostics
- `ts_ast`: generated syntax kinds and arena-backed AST nodes
- `ts_scanner`: lexical analysis
- `ts_parser`: the TypeScript grammar and error recovery
- `ts_binder` / `ts_checker`: symbols, scopes, and semantic types
- `ts_module` / `ts_glob`: module resolution and project file discovery
- `ts_project`: project-reference graph loading and ordered builds
- `ts_incremental`: deterministic build information and project invalidation
- `ts_fswatch`: portable recursive file watching and event coalescing
- `ts_watch`: watch-mode compilation orchestration
- `ts_options`: normalized compiler options
- `ts_outputpaths`: JavaScript and declaration output path calculation
- `ts_semver`: npm-style semantic versions and package range matching
- `ts_jsnum`: JavaScript number operations, formatting, and pseudo-bigints
- `ts_evaluator`: compile-time expression and constant evaluation
- `ts_jsonrpc`: typed JSON-RPC messages and LSP protocol framing
- `ts_lsp`: document synchronization, diagnostics, navigation, and editor
  protocol handling
- `ts_compiler`: program graph, diagnostics, checking, and emit orchestration
- `ts_printer` / `ts_sourcemap`: target-aware JavaScript and source-map emit
- `ts_bundled`: the pinned TypeScript default-library declarations
- `ts_diagnostics`: the generated TypeScript diagnostic catalog
- `ts_diagnostic_writer`: plain and contextual diagnostic formatting
- `ts_config`: JSONC and `tsconfig.json` parsing
- `ts_path` / `ts_vfs`: compiler path and filesystem abstractions
- `ts_cli`: the `tsgo` executable

Supporting workspace tools are:

- `ts_ast_codegen`: generated syntax-kind and AST source maintenance
- `ts_diagnostics_codegen`: generated diagnostic catalog maintenance
- `ts_compare`: differential command execution against another compiler
- `ts_fixture`: upstream fixture parsing and baseline comparison

## Execution flow

At a high level, the broad prototype follows this path:

```text
files / tsconfig
  -> options, paths, module resolution, and project graph
  -> scanner and parser
  -> binder and checker
  -> compiler orchestration
  -> printer, declarations, JavaScript, and source maps
  -> CLI output
```

Incremental state, project references, and watch mode wrap the project/compiler
layers. JSON-RPC and LSP expose related compiler state to editor clients.

The narrow v0 path deliberately bypasses much of this graph for explicit-file
`--noCheck` transpilation. That narrower path is the only surface with the
current supported-contract claim.

## CLI surfaces

The following entry points are implemented, but everything except the narrow
v0 invocation should be treated as experimental:

- `tsgo file.ts` and `tsgo --project tsconfig.json` enter the broad compilation
  pipeline, including default libraries, checking, JavaScript or declaration
  emit, and source maps as requested.
- Project-reference builds contain incremental `.tsbuildinfo` support.
- `--watch` is wired for file and build invocations.
- `tsgo --lsp` starts the editor protocol server.
- Development-only `--tokenize`, `--parse`, and `--compile-dev` modes expose
  individual compiler layers.

These commands have local smoke and integration coverage, but they have not
passed the complete upstream CLI, build, watch, baseline, fourslash, and API
suites.

## Verification commands

The focused supported-slice checks are listed in the
[README](../README.md#running-the-verified-slice). The broad local checks are:

```sh
./scripts/run-cargo-capped.sh test --workspace
./scripts/run-cargo-capped.sh clippy --workspace --all-targets -- -D warnings
```

The aggregate gate also checks formatting and generated sources:

```sh
./scripts/verify.sh
```

These broad commands are useful development diagnostics, but they are not
currently green. The README records the audited failures rather than presenting
the commands as proof of compatibility.

With a pinned upstream checkout available, compiler emit baselines can be
sampled and filtered deterministically:

```sh
TS_GO_REPO=/path/to/typescript-go ./scripts/run-fixture-baseline.sh \
  --filter ClassDeclaration --limit 20
```

Parsing a fixture without crashing or matching one emitted section is only a
partial signal. Full parity requires the broader gates in
[PORTING.md](PORTING.md), including diagnostics, emit, declarations, types,
symbols, traces, source maps, CLI/build/watch behavior, fourslash, and API
coverage.
