# TypeScript compiler in Rust

This repository is a Rust port of
[`microsoft/typescript-go`](https://github.com/microsoft/typescript-go). It is
under active development and is not yet a replacement for `tsgo` or `tsc`.

Current typechecker work follows the [reset plan](docs/typechecker-reset-plan.md)
and [accountability rules](docs/typechecker-accountability.md). Read the
[saved state](docs/typechecker-accountability-state.json) before resuming work.

The current sellable experiment is the deliberately narrow
[minimal working v0](docs/minimal-working-v0.md): `--noCheck`, ESNext,
preserved ESM, type erasure, and preserved JSX with explicit parity and
performance gates.

The implementation is split into compiler layers so each layer can be tested
against the upstream TypeScript fixtures independently:

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
- `ts_outputpaths`: JavaScript/declaration output path calculation
- `ts_semver`: npm-style semantic versions and package range matching
- `ts_jsnum`: JavaScript number operations, formatting, and pseudo-bigints
- `ts_evaluator`: compile-time expression and constant evaluation
- `ts_jsonrpc`: typed JSON-RPC messages and LSP protocol framing
- `ts_lsp`: document synchronization, diagnostics, navigation, and editor protocol handling
- `ts_compiler`: Program graph, diagnostics, checking, and emit orchestration
- `ts_printer` / `ts_sourcemap`: target-aware JavaScript and source-map emission
- `ts_bundled`: the pinned TypeScript default-library declarations
- `ts_diagnostics`: generated TypeScript diagnostic catalog
- `ts_diagnostic_writer`: plain and contextual diagnostic formatting
- `ts_config`: JSONC and `tsconfig.json` parsing
- `ts_path` / `ts_vfs`: compiler path and filesystem abstractions
- `ts_cli`: the `tsgo` executable

Run the current checks with:

```sh
./scripts/run-cargo-capped.sh test --workspace
./scripts/run-cargo-capped.sh clippy --workspace --all-targets -- -D warnings
```

Or run the complete local gate, including generated-source checks:

```sh
./scripts/verify.sh
```

With an upstream checkout available, compiler emit baselines can be sampled
directly and filtered deterministically:

```sh
TS_GO_REPO=/path/to/typescript-go ./scripts/run-fixture-baseline.sh \
  --filter ClassDeclaration --limit 20
```

`tsgo file.ts` and `tsgo --project tsconfig.json` run the standard compilation
pipeline, including default libraries, checking, JavaScript/declaration emit,
and source maps. Project-reference builds support incremental `.tsbuildinfo`
state, and `--watch` works for file and build invocations. `tsgo --lsp` runs the
editor protocol server. Development-only `--tokenize`, `--parse`, and
`--compile-dev` modes expose individual layers.
