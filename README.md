# TypeScript compiler in Rust

This repository is a Rust port of
[`microsoft/typescript-go`](https://github.com/microsoft/typescript-go). It is
under active development and is not yet a replacement for `tsgo` or `tsc`.

The implementation is split into compiler layers so each layer can be tested
against the upstream TypeScript fixtures independently:

- `ts_core`: source positions and diagnostics
- `ts_ast`: syntax kinds and, eventually, AST nodes
- `ts_scanner`: lexical analysis
- `ts_cli`: the `tsgo` executable

Run the current checks with:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```
