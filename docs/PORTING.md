# Porting plan

The port follows the upstream dependency spine rather than translating files
in arbitrary order:

1. Core source positions, JavaScript strings, diagnostics, paths, and VFS.
2. Schema-generated syntax kinds and arena-owned AST nodes.
3. Scanner and parser, including all context-sensitive rescan modes.
4. Binder, symbols, and control-flow graph construction.
5. Configuration, package/module resolution, compiler host, and Program graph.
6. Type checker clusters: relations, inference, flow, generics, JS/JSDoc, JSX.
7. Transform, printer, JavaScript/declaration emit, and source maps.
8. Incremental/build mode, project references, and watch mode.
9. Language service, project service, LSP, and native API protocols.

Every phase retains an executable vertical slice. The first compatibility gate
is a legitimate syntax-only invocation (`--noCheck --noEmit --noLib
--ignoreConfig`) with exact scanner/parser diagnostics; ordinary compilation
must not silently omit semantic checking.

## Verification strategy

The Go test runner invokes Go packages directly, so replacing
`built/local/tsgo` does not reuse the compiler baselines. The Rust port needs a
native baseline runner that reads the same directive-based cases and produces
the same `.errors.txt`, `.js`, `.types`, `.symbols`, source-map, and trace
artifacts. The native-preview API suite is the first upstream suite with an
existing process boundary and can run against a Rust binary once `--api` is
implemented.

Near-term gates are:

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Full completion requires all upstream local and TypeScript-submodule baselines,
CLI/build/watch scenarios, fourslash tests, and API tests to pass against Rust
implementations. Passing only the initial Cargo tests is not compiler parity.
