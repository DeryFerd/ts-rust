# Fresh property and index verification correction

The runtime claims in reports `5527e720` and `932698e5` are unaccepted.
Their Cargo targets were copied between physical worktrees. The old reports,
logs, patches, audit files, and binaries remain unchanged. Do not use those
runs as fresh verification.

This correction records a new test run and configured Clippy run for the fixed
wave150 source. Both passed. The separate wave149 run remains unaccepted.
This work does not change the implementation or promote the primary branch.

## Previous runs

| Wave | Implementation | Report | Affected sessions | Copied target source |
| --- | --- | --- | --- | --- |
| 149 | `296bd1b4` | `5527e720` | Binder `97451`, checker/public `27664`, strict Clippy `74074`, configured Clippy `65798` | Wave146 |
| 150 | `ce5c1451` | `932698e5` | Full tests `88310`, Clippy `10422`, audit `73585` | Wave149 |

The old wave150 `verification.json` is only a test-name comparison list. Its
test and Clippy results remain unaccepted despite matching the new results.

## Fixed source

Worktree:
`/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave150/property-index-root-composition`.

Implementation: `ce5c1451f1584cb1b351507500e6357e0f5c2acb`.
Tested HEAD: `932698e518ed2a6bdd9f9dc911429ebbc9a63f90`.
Tested tree: `503f001c0096e05ea26f36c3c7d9d980fb0deae7`.

The worktree stayed clean through both Cargo runs and the final audits. Every
implementation path matches ce5c1451. This report is the only new tracked file.
The original report is not rewritten.

## Fresh target

The target was created atomically with `mktemp -d`:
`target/cargo-fresh.BWu2kgO9` under the physical worktree above.
No files or fingerprints were copied, reflinked, hardlinked, or seeded into it.

`initial-state.json` records an empty entry list before any Cargo build, the
exact realpath, device `44`, inode `17112316`, and creation time. Its directory
identity still matches after both runs. The initial-state session `11884`
exited 0 and is collected.

Evidence is outside the target in `target/fresh-evidence.e9xrU40s`. The old
`target/cargo` was read only for preservation hashes. It was not a build input.
Clippy reused only artifacts built from this physical worktree in the new
target during this correction.

Both commands used the absolute original root runner
`/home/theo/Code/sandbox/ts-rust/scripts/run-cargo-capped.sh` and the absolute
worktree `Cargo.toml`. Their selections were:

```text
test -p ts_binder -p ts_checker --locked --offline --no-fail-fast --verbose
clippy -p ts_binder -p ts_checker --all-targets --locked --offline --no-deps --verbose
```

Verbose mode records compiler commands. It does not change the test selection
or lint levels. `CARGO_TARGET_DIR` was the absolute fresh target above.
`TS_CARGO_MEMORY_LIMIT_KIB=16777216` set the 16 GiB memory cap.
`prlimit --stack=16777216:16777216` and `RUST_MIN_STACK=16777216` set 16 MiB
stacks. `TS_GO_REPO=/home/theo/.explore/repos/microsoft__typescript-go` was
unchanged. The original common lock was used. `TMPDIR` and `TS_CARGO_LOCK_ID`
remained unset. No valid queue wait was canceled or bypassed.

## Fresh test results

Session `39662` exited 0 and is collected. Cargo reported 2 minutes 12 seconds
for compilation, excluding the shared-runner queue wait.

| Group | Passed | Failed | Ignored | Filtered |
| --- | ---: | ---: | ---: | ---: |
| Binder units | 219 | 0 | 0 | 0 |
| Checker units | 3,959 | 0 | 0 | 0 |
| Checker public tests, 65 binaries | 421 | 0 | 0 | 0 |
| Documentation tests | 1 | 0 | 0 | 0 |
| Total | 4,600 | 0 | 0 | 0 |

No test was measured. Both documentation groups completed. Binder has zero
documentation cases. Checker's expected compile-fail case passed.

The audit compared all 4,600 test names within their respective suites.
There are no added or removed names or suites. The 65 executed public targets
equal the complete checker public test-file list. The two original
inherited-index public tests ran unchanged. No filter or assertion was removed.

## Configured Clippy

Session `45761` started only after the test session was collected. It exited 0
and is collected. Cargo reported 1 minute 41 seconds after the queue opened.

Clippy reports 41 checker-library warnings, one inherited-index public-test
warning, and 43 checker-library-test warnings including 22 duplicates. Binder
has no warning summary. These match the prior log's counts. No extra deny or
allow flags, lint suppression, or cleanup was added. This is not a strict or
warning-free Clippy result.

## Evidence audit

The test log contains 101 fresh rustc invocations. These include 17 library
and unit-test invocations for 15 workspace crates. Each of the 67 executed
test binaries maps to a fresh link command and a new regular file in the
recorded target. Every recorded `--out-dir`, `-L dependency`, and file-based
`--extern` path points into that target.

The final path audit checks both documentation commands and their source
directories. It also checks 96 Clippy compiler invocations. Clippy's 67 test
targets match the complete executed test-source list. No Cargo configuration,
alternate build directory, compiler wrapper, or inherited override appeared.

All ten frozen source/runner input hashes and all 77 frozen old wave150
evidence hashes match after both runs. The latter include all 67 old binaries,
the old report, logs, patches, and audit files. The original input checksum
manifest also passes. All fresh binaries stayed unchanged through Clippy.

The 67 fresh binaries have the same content hashes as their old counterparts.
They were still compiled anew in the empty target. Equal hashes do not change
the unaccepted status of the old runs.

Test audit session `35923` and final audit session `26342` exited 0 and are
collected. The final path audit also exited 0. The first test-audit attempt
stopped on sandbox `spawnSync git EPERM`; its log is preserved. The approved
retry passed without changing the source or checks. No owned verification
command remains running or queued.

All paths in this table are under `target/fresh-evidence.e9xrU40s`:

| Evidence | SHA-256 |
| --- | --- |
| `initial-state.json` | `00e437365f68cc52a2393aa5ca17f38e354d12753f6b3de9f05f1bcf0f7a65ff` |
| `full-tests-v1.log` | `ba0a5a0573096ec607e3bb4950cf6a52a346837531aa981569cf68ff149a2f21` |
| `clippy-v1.log` | `7bbd2c6c7ae1e5b0d5aeda082b8578d16b4b1a9f59f0b083b89cba3c1f06aae8` |
| `verification.json` | `5902f687207b3eec774bbd5517b3776b66ef458796e22551a35ad2d4542b8829` |
| `final-build-paths.json` | `d9424d8c78caea33e3a323e2d980b6405bb1cd8787efb16be11250d7a0d03a8b` |

The JSON records contain the exact executable paths, hashes, test names,
per-suite results, compiler commands, and preservation checks. The separate
`test-verification.json` records the earlier test-only audit with Clippy
explicitly pending.

## Remaining limits

These four owner-held array controls remain absent and unmet in this source:

- `generic_index_member_resolution_uses_the_caller_session`
- `inherited_array_relation_keeps_nested_index_proofs_query_local`
- `inherited_array_relation_rejects_index_cache_source_mismatch`
- `cold_array_review_inherited_read_uses_the_canonical_merged_parent`

No array, readonly-interface, Promise, recovery, or other repair was imported
or duplicated. In particular, `bd9c1f12` and its report `df2ee897` stay with the
separate array composition. `library_order_review` owns the final array
dependency map. Those dependencies are not skipped or passing tests here.

This correction claims only the fixed binder/checker package tests and
configured Clippy result above. It does not claim a full compiler, workspace,
fixture, modern-project, replay, benchmark, or new Go parity result. Source
recovery and composite-value limits remain separate. Root owns final
all-component integration and primary promotion.
