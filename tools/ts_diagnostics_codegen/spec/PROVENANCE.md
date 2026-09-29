# Diagnostic catalog provenance

The files crates/ts_goport/src/diagnostics/catalog.rs and
crates/ts_goport/src/diag.rs are generated from
internal/diagnostics/diagnostics_generated.go in the cached
microsoft/typescript-go checkout at commit
16c25522e1230b69b11210cfad066d779e6319ba (2026-08-19, the bump B pin).
They hold exactly the pin's 2,206 messages. There is no overlay.

That Go catalog is the merged output of the pinned TypeScript submodule's
src/compiler/diagnosticMessages.json and ts-go's
internal/diagnostics/extraDiagnosticMessages.json. The code generator also
accepts those JSON inputs directly with repeated --input arguments when the
submodule is available. `--names-output` (diag.rs) needs `--go-generated`,
because the Go variable names are only in the Go file.

To generate both files again (for example at a pin bump), from the repository
root:

```
cargo run --release -p ts_diagnostics_codegen -- \
  --go-generated <go>/internal/diagnostics/diagnostics_generated.go \
  --output crates/ts_goport/src/diagnostics/catalog.rs \
  --names-output crates/ts_goport/src/diag.rs \
  --provenance "microsoft/typescript-go@<commit> internal/diagnostics/diagnostics_generated.go"
rustfmt --edition 2024 crates/ts_goport/src/diag.rs
```

Then update the commit above and the catalog size in
`generated_catalog_is_complete_and_sorted` (diagnostics/mod.rs). A Rust user of
a message that Go removed stops the build, so port the Go change that removed
it at the same time.
