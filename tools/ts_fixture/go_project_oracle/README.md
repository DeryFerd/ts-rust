# Pinned Go project oracle

This driver uses Go source overlays at upstream commit
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. It does not edit the upstream
checkout or the project. The Go executable is an explicit helper argument.
The helper does not download a toolchain, install project packages, or change
a config. Go module downloads require an explicit opt-in.

## Invocation contract

`scripts/run-go-project-oracle.sh GO UPSTREAM CONFIG OUT [prepare|build|test|run]`
requires absolute paths. `OUT` must not exist. The default mode is `run`.
`prepare` writes overlays and provenance without invoking Go. `build` also
builds the test executable. `test` also runs the focused instrumentation
tests without checking the supplied project. `run` instead starts two fresh
project oracle processes.
Builds use `GOTOOLCHAIN=local`, `GOPROXY=off`, and an output-local Go cache.
They retain the normal bundled libraries and do not use `-trimpath`.
Python 3 records elapsed time, peak child-process RSS, and exit status on
Linux. It uses the standard library and requires no package install.

`TS_GO_ORACLE_DOWNLOAD_PINNED=1` permits a dependency download before the
build. It selects only versions in the pinned `go.mod` and requires a content
checksum for each in the pinned `go.sum`. The helper copies both files into
the output directory, uses `-modfile`, and rejects any change to the copies.
The build itself still uses `GOPROXY=off`. An inherited `GOMODCACHE` must be
absolute. Its canonical path must be under the output parent and separate
from `OUT` and both source checkouts. Symlinks into source directories are
rejected before Go can run. The check repeats after the build lock is acquired.
Without an override, the helper uses a cache inside `OUT`. No dependency
download runs in `prepare` mode.

The test executable reads these environment variables:

- `TS_RUST_ORACLE_PROJECT`: absolute config path.
- `TS_RUST_ORACLE_OUTPUT`: new output directory for one process.
- `TS_RUST_ORACLE_HEADER`: artifact header, default `project`.
- `TS_RUST_ORACLE_PROVENANCE`: helper-produced build manifest path.
- `TS_RUST_ORACLE_RUN_ID`: caller-supplied process run ID.

## Report contract

Each process writes `report.json` with `schema_version: 2` and
`implementation: "typescript-go"`. Outcomes include `config_error`,
`no_check`, `no_sources`, `missing_replay_evidence`, `incomplete_evidence`,
`invariant_error`, and `oracle_error`. This version cannot produce complete
replay evidence. A source replay with stable retained outputs returns
`incomplete_evidence` because freshly produced diagnostics are not isolated
from cached results. No run is counted as semantic success on that basis.

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

`cold` and `warm` each have `diagnostics`, `diagnostic_evidence`,
`errors_file_order`, `errors`, `types`, `symbols`, and `walk`.
Warm diagnostics use `retained_program_snapshot`. This includes cached
checker and declaration diagnostics. Error input order uses the artifact order,
then diagnostic-bearing config inputs in path order. With no diagnostics,
the error input order is empty. Artifact records have `state`, `path`,
`sha256`, `bytes`, and `reason`.
`state` is `present`, `no_content`, or `unavailable`. Absent artifacts use
null paths and hashes. A present artifact uses the exact pinned renderer
bytes, including its line endings. Errors with no diagnostics use
`no_content`, not the digest of an empty file.

`walk.type_queries` counts each direct `GetTypeAtLocation` call in the pinned
baseline walker, with its actual argument node. A class-base expression can
query its parent, then query itself as an `any` fallback. `rendered_types`
counts the final types selected for rendering. These counts are separate.
AST visits and direct symbol queries are also counted.

`replay` records actual source resets, eligible project and default-library
source counts, exact artifact bytes, retained diagnostic equality, walk
equality, and retained identities. Query type identities and final rendered
type identities have separate equality fields. Pointer values are compared
only inside one Program and are not published.

`replay.fresh_diagnostics` has `state: "unavailable"`, `equal: null`, and a
reason. `retained_diagnostics_equal` is not proof that each cold diagnostic
was produced again. The driver keeps checker collections, lazy/global
diagnostics, and declaration caches intact. It does not clear them to obtain
an apparently fresh result. A completed source re-entry has replay state
`partial`, not `complete`.

If no non-default-library source is eligible, replay state is
`no_eligible_project_sources` and the outcome is `missing_replay_evidence`.
Default-library checks alone do not count as project replay. Cold artifacts
still include declaration inputs. Warm artifacts are unavailable in this case.
The helper retains both fresh-process reports, including non-success reports.
`runs.json` also uses schema version 2. If either process does not complete,
`comparison_state` is `unavailable` and `fresh_processes_equal` is null.

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

Module-cache path checks can run without Go:

```sh
python3 tools/ts_fixture/go_project_oracle/test_cache_paths.py UPSTREAM CONFIG OUTPUT_PARENT
```

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
