# Diagnostic catalog provenance

The file crates/ts_goport/src/diagnostics/catalog.rs is generated from
internal/diagnostics/diagnostics_generated.go in the cached
microsoft/typescript-go checkout at commit
dc37b5249ab60e2bbce936f71b883e6c8136167e (2026-06-19).

That Go catalog is the merged output of the pinned TypeScript submodule's
src/compiler/diagnosticMessages.json and ts-go's
internal/diagnostics/extraDiagnosticMessages.json. The code generator also
accepts those JSON inputs directly with repeated --input arguments when the
submodule is available.
