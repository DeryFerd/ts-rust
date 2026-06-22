# TypeScript compiler in Rust

This repository is a Rust port of
[`microsoft/typescript-go`](https://github.com/microsoft/typescript-go). It is
under active development and is not yet a replacement for `tsgo` or `tsc`.

The implementation is split into compiler layers so each layer can be tested
against the upstream TypeScript fixtures independently:

- `ts_core`: source positions and diagnostics
- `ts_ast`: generated syntax kinds and arena-backed AST nodes
- `ts_scanner`: lexical analysis
- `ts_parser`: the TypeScript grammar and error recovery
- `ts_binder` / `ts_checker`: symbols, scopes, and semantic types
- `ts_module` / `ts_glob`: module resolution and project file discovery
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
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Or run the complete local gate, including generated-source checks:

```sh
./scripts/verify.sh
```

Development-only `tsgo --tokenize file.ts`, `tsgo --parse file.ts`, and
`tsgo --compile-dev file.ts` commands expose the scanner/parser and current
end-to-end compiler pipeline. Standard compilation still exits explicitly as
not implemented until option/default-library/diagnostic parity is sufficient.
