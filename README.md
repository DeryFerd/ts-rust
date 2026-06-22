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
- `ts_diagnostics`: generated TypeScript diagnostic catalog
- `ts_config`: JSONC and `tsconfig.json` parsing
- `ts_path` / `ts_vfs`: compiler path and filesystem abstractions
- `ts_cli`: the `tsgo` executable

Run the current checks with:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Development-only `tsgo --tokenize file.ts` and `tsgo --parse file.ts`
commands expose the current scanner/parser vertical slice. Standard compilation
still exits explicitly as not implemented until Program, binding, checking, and
emit are connected.
