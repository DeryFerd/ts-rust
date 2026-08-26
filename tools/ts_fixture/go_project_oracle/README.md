# Pinned Go project oracle

This driver uses Go source overlays at upstream commit
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. It does not edit the upstream
checkout or the project. The Go executable is an explicit helper argument.
The helper does not download a toolchain, install packages, or change a config.

## Invocation contract

`scripts/run-go-project-oracle.sh GO UPSTREAM CONFIG OUT [prepare|build|run]`
requires absolute paths. `OUT` must not exist. The default mode is `run`.
`prepare` writes overlays and provenance without invoking Go. `build` also
builds the test executable. `run` then starts two fresh test processes.
Builds use `GOTOOLCHAIN=local`, `GOPROXY=off`, and an output-local Go cache.
They retain the normal bundled libraries and do not use `-trimpath`.

The test executable reads these environment variables:

- `TS_RUST_ORACLE_PROJECT`: absolute config path.
- `TS_RUST_ORACLE_OUTPUT`: new output directory for one process.
- `TS_RUST_ORACLE_HEADER`: artifact header, default `project`.
- `TS_RUST_ORACLE_PROVENANCE`: helper-produced build manifest path.
- `TS_RUST_ORACLE_RUN_ID`: caller-supplied process run ID.

## Report contract

Each process writes `report.json` with `schema_version: 1` and
`implementation: "typescript-go"`. `outcome` is one of `complete`,
`config_error`, `no_check`, `no_sources`, `invariant_error`, or `oracle_error`.
`complete` means that the oracle ran. It does not mean that the project has
no diagnostics or that Rust matches Go.

Top-level fields are `schema_version`, `implementation`, `upstream_sha`,
`run_id`, `header`, `outcome`, `failure`, `graph`, `graph_sha256`, `cold`,
`warm`, `replay`, `provenance`, and `runtime`.

`graph` has `config_path`, `current_directory`, `case_sensitive`, `roots`,
`sources`, `artifact_order`, `config_inputs`, `file_reads`, `realpaths`,
`symlink_entries`, `resolutions`, `references`, `compiler_options`,
`effective_options`, and `missing_evidence`.
Roots retain config order and duplicates. Sources retain Program order and
record content SHA-256, byte length, declaration status, default-library
status, source package scope, and module modes. Artifact order is the first
loaded occurrence of each config root, followed by every other non-default
source in path order. Consumed declaration files remain in this list.
Only `bundled:///libs/` becomes `/__typescript/lib/` in graph identities.
The baseline text itself is not rewritten.

Resolution records retain their kind, source, specifier, request mode,
resolved path, original path, target mode, extension, package identity,
external-library flag, and resolution diagnostic records. The graph includes
automatic type directives and JSX runtime imports. File reads retain actual
content digests at the time the normal host reads each file. Config inputs
name the selected config and the loader's transitive extends inputs.
Missing evidence is explicit. A missing fact is not an empty fact.

`cold` and `warm` each have `diagnostics`, `errors_file_order`, `errors`,
`types`, `symbols`, and `walk`. Error input order uses the artifact order,
then diagnostic-bearing config inputs in path order. With no diagnostics,
the error input order is empty. Artifact records have `state`, `path`,
`sha256`, `bytes`, and `reason`.
`state` is `present`, `no_content`, or `unavailable`. Absent artifacts use
null paths and hashes. A present artifact uses the exact pinned renderer
bytes, including its line endings. Errors with no diagnostics use
`no_content`, not the digest of an empty file.

`walk` counts AST visits, type queries, and symbol queries from the actual
baseline walker. `replay` records the Program-eligible source order, reset
completion flags, exact artifact and diagnostic equality, walk equality,
and retained type and symbol identity equality. Identities are compared
inside one Program. Pointer values are not published or compared across
processes. The helper runs the process twice and retains both results.

## Upstream calls

The driver constructs `compiler.NewCompilerHost` with a read-only tracking
wrapper around `bundled.WrapFS(osvfs.FS())`, then calls
`tsoptions.GetParsedCommandLineOfConfigFile` and `compiler.NewProgram` with
`SingleThreaded: core.TSTrue`. It does not change compiler options.

Diagnostic collection uses config, Program, syntactic, semantic, global,
and applicable declaration diagnostic APIs. Program applies comment
directives and no-emit filtering. The driver calls `GetErrorBaseline` and
`generateBaseline` directly. It does not call `baseline.Run` or
`harnessutil.CompileFiles`.

The replay overlay clears only `typeChecked` and `unusedChecked` in existing
`sourceFileLinks`. The caller holds `GetTypeCheckerForFileExclusive` while
it clears those flags, releases the checker, then repeats the same Program
diagnostic collection. Eligibility uses `Program.SkipTypeChecking(file, false)`.
An overlay of the pinned walker adds observation hooks only. It does not
replace its renderer, query selection, or formatting rules.

The build manifest records every overlay mapping, source hash, tool version,
build arguments, explicit environment overrides, upstream dirty state, and
the executable hash when a build succeeds. Runtime evidence is not checked
into this source directory.

## Current evidence limits

The graph reports failed file lookups but the pinned Program does not expose
their association with each module resolution. Its resolution cache also
does not retain call order. The report names both limits in `missing_evidence`.
It does not claim full graph equality while evidence is missing.
`compiler_options` retains all typed upstream inputs. `effective_options`
uses upstream getters for computed values and preserves null for other
unspecified settings. A consumer must compare these options by meaning,
not equate unspecified settings with false.
