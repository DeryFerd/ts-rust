# Protected goport tests

The protected goport test set replaces the legacy cargo roster (legacy removal stage 1, Theo approved on 2026-09-28; state notes `legacy-removal-direction-2026-09-28` and `legacy-removal-rule-approval-2026-09-28`). No test name that passes in the base may be lost.

## Files

| File | What it is | sha256 |
|---|---|---|
| `tests-r131.json.gz` | `results.json` of `scripts/goport/goport-tests.sh` on the R131 test bins, pin 52168999f3dc, as compact JSON with sorted keys in gzip | `d1b90114690033ea0d3450182b7340c7f87df27d7e3c45af07192506a2476b7a` |

`tests-r131.json.gz` is the base of the first candidate after R131. After that, each accepted revision writes its `results.json` to its evidence cache, and the base of a candidate is the `results.json` of the last accepted revision.

Format: `{"source": {"commit", "tree", "testbinSha256"}, "pin", "suites": {"<suite>": {"<test name>": "ok" | "failed" | "ignored" | "unrun"}}, "incomplete": [<suite>...]}`. `tree` is the crates tree of `commit`. `testbinSha256` is the sha256 of the test bin dir's `bins.sha256`. The JSON is 12.4 MB, because it holds every compiler runner subtest and reference file. So the repository keeps it in gzip (1.1 MB).

The gzip file has deterministic bytes. To make it again from a `results.json`:

```
jq -cS . results.json | gzip -n -9 > docs/goport-protected/tests-r131.json.gz
```

`jq -cS` writes compact JSON with sorted keys and one final newline (Python `json.dumps(doc, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"` gives the same bytes). `gzip -n` writes no name and no time. With jq 1.8.2 and gzip 1.15: the JSON sha256 is `e6e301b42ebbb635a9d9801de6933a096d5a70a7322a72d1a527c1235084bb0a` and the gzip sha256 is the one in the table. The parsed JSON is equal to the pretty-printed `results.json` of the run (`target/continuation-r97-goport/legacy-removal/t1/tests-r131-v2/results.json`, sha256 `99b160efe18f29badaf861b83bebc4f64dc94c25ed1680d667e1984343c61e1d`, 13.2 MB), which was committed as `tests-r131.json` before this file replaced it.

The readers take `.json` or `.json.gz`: a path that ends in `.gz` is read as gzip. The sha256 that a batch, `compare-tests.py` and `check-typechecker-batch.mjs` use is the sha256 of the file as stored (the gzip bytes).

## Tools

- `scripts/goport/build-goport-tests.sh <checkout> <testbin-dir>`: builds the test binaries at a checkout (release, `--locked`, the default toolchain (1.93.0 now), no incremental, the shared candidate target) and copies them with `SUITES`, `relbin/`, `COMMIT`, `TREE`, `BUILD_ROOT`, `BUILD_TARGET`, `TOOLCHAIN` and `bins.sha256`. It reads `cargo metadata`: every workspace member that is not in its `NOT_PROTECTED` list (the legacy crates and the tools) gives its lib tests and each of its `[[test]]` targets. So a new crate or a new `tests/*.rs` joins the set without an edit. `SUITES` gives the crate dir of each binary. About 9 minutes on zbook.
- `scripts/goport/goport-tests.sh <testbin-dir> <out-dir> [--pin PIN]`: runs every binary of `SUITES` in its crate dir (one test thread) and writes `<out-dir>/results.json`. About 5 minutes on zbook. It starts itself again under `env -i` with only `PATH`, `HOME`, `USER`, `XDG_RUNTIME_DIR`, `DBUS_SESSION_BUS_ADDRESS` and `LANG=C.UTF-8`, so a caller's `TSCTEST_FILTER`, `TS_GOPORT_BASELINE_*`, `S2_*` or `GOPORT_*` does not change a run. Each binary runs in a bwrap that binds a git archive of `COMMIT`'s `crates/` and the saved `relbin/` over the compiled-in paths, so a later edit or build of the checkout does not change the run. A test binary that is not in `SUITES` stops the run.
- `scripts/goport/compare-tests.py <base> <new> [--name-map TSV] [--out FILE]`: per-name compare. Each input is a `.json` or `.json.gz` file. Exit 1 when a base `ok` name is lost, absent or unrun, or a map line is rejected. Exit 2 on bad input, which includes a `pin` that is not 7 to 64 hex characters (a spoofed pin would count as a pin change and allow a removal). The name map has one line per moved, renamed or removed test: `<old suite>\t<old name>\t<new suite>\t<new name>\t<evidence>`. `-\t-` as the new suite and name marks a removed test. A map line is rejected when its old name is still in the new results, when its new name is a base name (no swaps or chains), or when it removes a name with no Go pin change outside a kept-crate suite. `check-typechecker-batch.mjs` applies the same rules. The reviewer checks each map line against its evidence. Tests: `node --test scripts/goport/compare-tests.test.mjs`.

## Suites at R131

| Suite | What runs | Names | ok | ignored |
|---|---|---|---|---|
| `lib_snapshot` | `ts_goport_lib snapshot_matches_live`, first | 2 | 2 | 0 |
| `ts_goport_lib` | ts_goport lib tests | 90 | 88 | 2 |
| `goport_util_lib` | goport_util lib tests | 14 | 14 | 0 |
| `goport_lsproto_lib` | goport_lsproto lib tests | 66 | 66 | 0 |
| `go_baselines` | the default set | 897 | 896 | 1 |
| `go_baselines_local` | TestLocal subtests (`<kind> <key>`) | 2,933 | 2,929 | 4 |
| `go_baselines_submodule_shards` | TestSubmodule, 4 shards, `COMPILER_RUNNER_JOBS=8` | 4 | 4 | 0 |
| `go_baselines_submodule` | TestSubmodule subtests | 116,095 | 113,969 | 2,126 |
| `go_baselines_reference` | every Go reference file (`testdata/baselines/reference`) | 49,316 | 47,438 | 1,878 |
| `multi_program` | tests/multi_program.rs | 9 | 9 | 0 |
| `emit_pool` | tests/emit_pool.rs | 1 | 1 | 0 |
| `early_emit` | tests/early_emit.rs | 3 | 3 | 0 |
| `fswatch_linux` | tests/fswatch_linux.rs | 3 | 3 | 0 |
| `ts_scanner_lib` | kept crate unit tests | 66 | 66 | 0 |
| `ts_ast_lib` | kept crate unit tests | 25 | 25 | 0 |
| `ts_diagnostics_lib` | kept crate unit tests | 10 | 10 | 0 |
| `ts_path_lib` | kept crate unit tests | 9 | 9 | 0 |
| `ts_core_lib` | kept crate unit tests | 6 | 6 | 0 |
| `ts_jsnum_lib` | kept crate unit tests | 6 | 6 | 0 |
| total | | 169,555 | 165,544 | 4,011 |

No name failed and no suite is incomplete. The 2 ignored lib tests write the lib snapshot blobs. The ignored `go_baselines` name is `compiler_runner::test_submodule`, which the shard suite runs. The 4 ignored local subtests and the 2,126 ignored submodule subtests are Go runner skips: unsupported configurations (2,122) and the Go `skippedEmitTests` list (8).

`go_baselines_reference` status of a file:

- A compiler runner compared it (a `baseline` row of a runner results file): the status of its subtest. `submoduleAccepted/` and `submoduleTriaged/` read as `submodule/`, and `.diff` and the kind extension are dropped to find it.
- Else another `go_baselines` test compared it (`TS_GOPORT_BASELINE_TRACK` of the default run, as Go `TSGO_BASELINE_TRACKING_DIR`), or a runner compared it and has no subtest of its kind: `ok` when no `go_baselines` test and no TestSubmodule shard failed or is unrun, else `failed`. The track file does not say which test compared a file.
- Else `ignored`.

At R131: 44,463 `compiler`, `conformance` and `submodule` files; 2,323 `.diff` files in `submodule`, `submoduleAccepted` and `submoduleTriaged`; 652 tracked files (tsc 191, tsbuild 186, tsbuildWatch 65, tscWatch 40, tsoptions 80, config 78, astnav 7, api 2, lsp 3). Ignored: the 1,877 `fourslash` files (goport runs no fourslash baselines) and `tscWatch/commandLineWatch/watch-handles-many-bun-dependency-files.js` (no R131 test compares it).

`go_baselines_transpile` (TestTranspile subtests, `TRANSPILE_RUNNER_RESULTS`) is added automatically when `go_baselines` has `compiler_runner::test_transpile`. R131 does not have it. It comes with bump B (tsgo#4849). Its compared files (`submodule/transpile`) then count in the reference suite.

## How the baseline was made

Test bin dir `target/continuation-r97-goport/legacy-removal/t1/testbin-r131-v2` (`bins.sha256` sha256 `26ad716d092d6467bbf3944a9e07f86f44f5d0a1824b8289dfa3f4eb97720165`, `PROVENANCE` in the dir). It holds hard links of `testbin-r131` (`bins.sha256` sha256 `f9be84bf810835917bb6ff06714e1bbd0f727e92df9cafe5e4383890bb111c4e`) and a `SUITES` file from `cargo metadata` of crates tree a4aae8d62022:

- The 8 goport test binaries are copies of `buildspeed/split1/testbin-r131` (COMMIT 50b0593b5, crates tree a4aae8d62022, built in `target/worktrees/goport-split1`, rustc 1.98.0-nightly 2026-06-16). These are the test bins of the R131 split prep.
- `relbin/` is a copy of `buildspeed/split1/bin-r131`, the release bins of the same build.
- The 6 kept crate test binaries come from `build-goport-tests.sh` of `goport-legacy1` (crates tree a4aae8d62022, the same as R131; rustc 1.93.0). These crates read no files.

Command: `scripts/goport/goport-tests.sh target/continuation-r97-goport/legacy-removal/t1/testbin-r131-v2 target/continuation-r97-goport/legacy-removal/t1/tests-r131-v2`, with `GOPORT_PIN=52168999f3dc`, `TSCTEST_FILTER=planted-no-match` and `TS_GOPORT_BASELINE_LOCAL=/nonexistent/planted` in the caller's environment (the clean environment drops them: every tsc file is tracked and every test passes). Then `jq -cS . results.json | gzip -n -9` made `tests-r131.json.gz` (see Files).

Checks:

- Per name, the 9 libtest suites are equal to the split prep logs in `buildspeed/split1/r131/logs` (lib 170 names in 3 binaries, 168 ok and 2 ignored; go_baselines 897 with 896 ok; multi_program 9, emit_pool 1, early_emit 3, lib snapshot 2, fswatch_linux 3).
- The TestLocal results file is equal (sorted lines) to `buildspeed/split1/r131/go-baselines-N-local.tsv` (4,547 lines: 2,933 subtests and 1,614 compared baselines).
- The TestSubmodule results files are equal (sorted lines) to both sides of the lsshells M2 check (`lsshells/m2/m2/tests/{base,m2}/sub-N-*.tsv`; base is R130).
- The 44,463 reference files that `upstream/bumpB/wave3/r1/tools/coverage.py` reads are all matched there and `ok` here.
- Against the first baseline (`legacy-removal/t1/tests-r131`, sha256 `34dd578e...`, before the `.diff` and tracked files and the clean environment): every suite except `go_baselines_reference` is equal, and `compare-tests.py` gives retained 162,569, lost 0, absent 0, unrun 0, new names 4,853 (all in `go_baselines_reference`).
- A full 1.93.0 build with the metadata-driven `build-goport-tests.sh` at `goport-legacy1` c8fd55fb4 (`legacy-removal/t1/testbin-fresh2-r131`) gives the same 14 binaries and the same `SUITES`, and `results.json` with equal suites and an equal track file: `compare-tests.py` retained 165,544, lost 0, absent 0, unrun 0, new 0.
- `compare-tests.py` exits 1 on a planted failed, ignored, unrun or absent name, a missing, empty or renamed suite, and on the map lines that could hide a loss (a removal or rename whose old name is still in the new results, a swap with a base name). `legacy-removal/t1/review2/cases_compare.py` runs these on the real baseline.

## Not in the set

- The lib snapshot generators (`generate_lib_bind_snapshot`, `generate_lib_parse_snapshot`): they are ignored tools that write `lib_bind.bin` and `lib_parse.bin`, not checks. They stay in `ts_goport_lib` as ignored names.
- The code generators of the kept crates, `tools/ts_ast_codegen` (7 tests) and `tools/ts_diagnostics_codegen` (5 tests), and their freshness checks (`scripts/verify.sh`: `ts_ast_codegen -- check` and `check-ast`). They generate `ts_ast/src/syntax_kind.rs`, `ast_generated.rs` and `ts_diagnostics/src/catalog.rs`. A change of those files shows in the kept crate and goport tests. Stage 4 (one diagnostics catalog) must run the generator checks as its own evidence.
- The other tools (`ts_compare`, `ts_fixture`) and the legacy crates (`ts_checker`, `ts_compiler`, `ts_parser`, `ts_binder`, `upstream_cases` and the rest of `NOT_PROTECTED` in `build-goport-tests.sh`): they do not run goport code.
- Doc tests: no goport or kept crate doc test runs today, and `--no-run` does not build them.
- Bin and example targets: they have no tests, and the build does not build their test harnesses.
- The LSP oracle battery, the API battery, the gate, the bound runs, clippy and rustfmt: other evidence steps, not test binaries.
- The concurrent-program runner mode (`TS_TEST_PROGRAM_SINGLE_THREADED=false`): no script runs it today.
