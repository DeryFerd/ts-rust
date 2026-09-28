# Protected goport tests

The protected goport test set replaces the legacy cargo roster (legacy removal stage 1, Theo approved on 2026-09-28; state notes `legacy-removal-direction-2026-09-28` and `legacy-removal-rule-approval-2026-09-28`). No test name that passes in the base may be lost.

## Files

| File | What it is | sha256 |
|---|---|---|
| `tests-r131.json` | `results.json` of `scripts/goport/goport-tests.sh` on the R131 test bins, pin 52168999f3dc | `34dd578e0464f38a46a7ae9bbfd326961ebefdb096c11dbd6688156979348496` |

`tests-r131.json` is the base of the first candidate after R131. After that, each accepted revision writes its `results.json` to its evidence cache, and the base of a candidate is the `results.json` of the last accepted revision.

Format: `{"source": {"commit", "tree", "testbinSha256"}, "pin", "suites": {"<suite>": {"<test name>": "ok" | "failed" | "ignored" | "unrun"}}, "incomplete": [<suite>...]}`. `tree` is the crates tree of `commit`. `testbinSha256` is the sha256 of the test bin dir's `bins.sha256`. The file is 12.8 MB (1.1 MB gzip), because it holds every compiler runner subtest and reference file.

## Tools

- `scripts/goport/build-goport-tests.sh <checkout> <testbin-dir>`: builds all test binaries at a checkout (release, `--locked`, the default toolchain (1.93.0 now), no incremental, the shared candidate target) and copies them with `relbin/`, `COMMIT`, `TREE`, `BUILD_ROOT`, `BUILD_TARGET`, `TOOLCHAIN` and `bins.sha256`. About 9 minutes on zbook.
- `scripts/goport/goport-tests.sh <testbin-dir> <out-dir> [--pin PIN]`: runs every suite below (one test thread) and writes `<out-dir>/results.json`. About 5 minutes on zbook. Each binary runs in a bwrap that binds a git archive of `COMMIT`'s `crates/` and the saved `relbin/` over the compiled-in paths, so a later edit or build of the checkout does not change the run.
- `scripts/goport/compare-tests.py <base> <new> [--name-map TSV] [--out FILE]`: per-name compare. Exit 1 when a base `ok` name is lost, absent or unrun. The name map has one line per moved, renamed or removed test: `<old suite>\t<old name>\t<new suite>\t<new name>\t<evidence>`. `-\t-` as the new suite and name marks a test that the Go pin removed. The reviewer checks each map line against its evidence.

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
| `go_baselines_reference` | Go reference files (compiler, conformance and their submodule dirs) | 44,463 | 44,463 | 0 |
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
| total | | 164,702 | 162,569 | 2,133 |

No name failed and no suite is incomplete. The 2 ignored lib tests write the lib snapshot blobs. The ignored `go_baselines` name is `compiler_runner::test_submodule`, which the shard suite runs. The 4 ignored local subtests and the 2,126 ignored submodule subtests are Go runner skips: unsupported configurations (2,122) and the Go `skippedEmitTests` list (8).

`go_baselines_transpile` (TestTranspile subtests, `TRANSPILE_RUNNER_RESULTS`) is added automatically when `go_baselines` has `compiler_runner::test_transpile`. R131 does not have it. It comes with bump B (tsgo#4849).

## How the baseline was made

Test bin dir `target/continuation-r97-goport/legacy-removal/t1/testbin-r131` (`bins.sha256` sha256 `f9be84bf810835917bb6ff06714e1bbd0f727e92df9cafe5e4383890bb111c4e`, `PROVENANCE` in the dir):

- The 8 goport test binaries are copies of `buildspeed/split1/testbin-r131` (COMMIT 50b0593b5, crates tree a4aae8d62022, built in `target/worktrees/goport-split1`, rustc 1.98.0-nightly 2026-06-16). These are the test bins of the R131 split prep.
- `relbin/` is a copy of `buildspeed/split1/bin-r131`, the release bins of the same build.
- The 6 kept crate test binaries come from `build-goport-tests.sh` of `goport-legacy1` (crates tree a4aae8d62022, the same as R131; rustc 1.93.0). These crates read no files.

Command: `scripts/goport/goport-tests.sh target/continuation-r97-goport/legacy-removal/t1/testbin-r131 target/continuation-r97-goport/legacy-removal/t1/tests-r131 --pin 52168999f3dc`.

Checks:

- Per name, the 9 libtest suites are equal to the split prep logs in `buildspeed/split1/r131/logs` (lib 170 names in 3 binaries, 168 ok and 2 ignored; go_baselines 897 with 896 ok; multi_program 9, emit_pool 1, early_emit 3, lib snapshot 2, fswatch_linux 3).
- The TestLocal results file is equal (sorted lines) to `buildspeed/split1/r131/go-baselines-N-local.tsv` (4,547 lines: 2,933 subtests and 1,614 compared baselines).
- The TestSubmodule results files are equal (sorted lines) to both sides of the lsshells M2 check (`lsshells/m2/m2/tests/{base,m2}/sub-N-*.tsv`; base is R130).
- The reference suite equals `upstream/bumpB/wave3/r1/tools/coverage.py` on the same files: 44,463 matched.
- A full 1.93.0 build of all 14 test binaries with `build-goport-tests.sh` (`legacy-removal/t1/testbin-fresh-r131`) gives the same suites: `compare-tests.py` retained 162,569, lost 0, absent 0, unrun 0, new 0.
- Two runs of the final script on the same test bins gave the same `results.json` sha256.
- `compare-tests.py` exits 1 on a planted failed subtest and on a missing suite.

## Not in the set

- The lib snapshot generators (`generate_lib_bind_snapshot`, `generate_lib_parse_snapshot`): they are ignored tools that write `lib_bind.bin` and `lib_parse.bin`, not checks. They stay in `ts_goport_lib` as ignored names.
- Doc tests: no goport or kept crate doc test runs today, and `--no-run` does not build them.
- The LSP oracle battery, the API battery, the gate, the bound runs, clippy and rustfmt: other evidence steps, not test binaries.
- The concurrent-program runner mode (`TS_TEST_PROGRAM_SINGLE_THREADED=false`): no script runs it today.
- The legacy crate tests (`ts_checker`, `ts_compiler`, `ts_parser`, `ts_binder`, `ts_fixture` and `upstream_cases`): they do not run goport code.
