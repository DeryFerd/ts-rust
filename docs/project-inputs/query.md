# TanStack Query inputs

Recorded on August 26, 2026. The selected inputs are prepared. This is not a
compiler pass or a ready conformance ring. No Rust check or Go oracle was run.

- Source pin: `44645e9eb1dafba5f2f229adb328582075484f36`.
- Lockfile SHA-256: `dabc851b54103afd7fb67d00d07663d554c89393c2ffde5254ca539f84d81e71`.
- Tool pins: Node `24.16.0`, from `.nvmrc`, and pnpm `11.9.0`, from `package.json`.
- Output: main checkout `target/project-inputs/query`.
- Script: `scripts/prepare-query-inputs.mjs`.

The prepared source is
`/home/theo/Code/sandbox/ts-rust/target/project-inputs/query/source`.
The report and command logs are in the sibling `metadata` and `logs` directories.
The cache checkout remains clean at the same pin. No upstream source or config
was changed.

The script preserves the five production configs and the independent NodeNext
consumer listed in `docs/typechecker-modern-project-inputs.md`. It checks their
original root-list digests. It does not add exclusions or change compiler options.

## Config inputs

Paths in this table are relative to the prepared source. Loaded-file counts are
from TypeScript 6.0.3 `--listFilesOnly`. They are not semantic checks or proof of
the Go or Rust module graph. Do not add these overlapping counts together.

| Config                                                            | Roots | Loaded files |
| ----------------------------------------------------------------- | ----: | -----------: |
| `packages/query-core/tsconfig.prod.json`                          |    23 |          186 |
| `packages/query-persist-client-core/tsconfig.prod.json`           |     4 |          190 |
| `packages/query-sync-storage-persister/tsconfig.prod.json`        |     2 |          192 |
| `packages/query-async-storage-persister/tsconfig.prod.json`       |     3 |          193 |
| `packages/query-broadcast-client-experimental/tsconfig.prod.json` |     1 |          190 |
| `integrations/react-nodenext/tsconfig.json`                       |     2 |          152 |

All six root-list digests match the earlier inventory. The five production
configs retain `customConditions: ["@tanstack/custom-condition"]` and
`types: ["node"]`. Their module settings remain ESNext and Bundler. The
independent consumer remains NodeNext with no custom condition or explicit
`types` list. None of these six parsed configs has inherited project references.

Resolution records confirm that the production packages consume the checked-in
Query core and persistence source. The broadcast package loads
`broadcast-channel@7.3.0/types/index.d.ts` and its referenced declarations.
The consumer's `hooks.ts` resolves the modern React Query `.d.ts` entry.
Its `hooks.cts` resolves the `.d.cts` entry. Both entries resolve the matching
modern Query core declaration. These records are in `metadata/resolutions.json`.

## Safety review

The source cache is read only. The script creates an independent Git copy.
The two checked-in lifecycle hooks are Vue 2 example `postinstall` commands.
Upstream workspace rules already exclude those examples. The initial full
workspace install still disables every lifecycle hook explicitly.

No pnpm hook file was found. The workspace build allowlist names `nx`, `esbuild`,
and `@swc/core`. It does not authorize this preparation to run their hooks.

Each stage runs in a user systemd scope with a 2 GiB memory limit, no swap, and
at most 128 tasks. pnpm has one tarball worker, four network requests, and one
child build slot. The Node heap limit is 1,536 MiB. Cache, package store,
temporary files, tools, and source stay under the Query output directory.
Global package managers are not changed.

The script checks existing ancestors, managed directories, and managed files
before its first write. It rejects symlinks in managed write paths and hard
links in metadata, logs, and downloads. The coordinator's file writes use
checked, non-following file descriptors. Private home, cache, config, temporary, and
package-store paths are checked separately from source and package links.
The package store's project link is allowed only when it resolves to this
prepared source directory.

Bootstrap commands use fixed `/usr/bin` paths and a fixed system `PATH`.
The script does not pass through caller Git overrides or module search paths.
Before any pinned Node or pnpm execution, it checks the archive hashes and
compares the full extracted trees with fresh private extractions. File lists,
bytes, modes, link counts, and symlink targets must match. Version output and
saved metadata are not accepted as integrity checks. This check also runs
before the pinned Node stage handoff and when install or build reuses tools.
Fresh tools are moved from private extraction directories. Existing partial
or changed tool directories are rejected, not overwritten.

The first install hit the 2 GiB limit. The user-service journal records an
`oom-kill` and a 2 GiB peak in `metadata/first-install-resource.log`. pnpm's
separate tarball pool still used its CPU-based default. The pinned CLI supports
`PNPM_MAX_WORKERS`, so the retry set it to `1`. The same full frozen install then
completed in 2 minutes 43 seconds. The memory cap and package selection did not
change.

The successful install covered all 102 upstream workspace projects and 2,839
installed package entries. Its 3,111-entry supply-chain policy check passed.
Dependencies, dev dependencies, and optional dependencies were included. Normal
platform pruning is recorded in `metadata/package-manager-layout.json`.
The source lockfile was not rewritten.

The installed package audit records 239 manifest entries with lifecycle scripts.
None of those scripts was run.
pnpm still lists 11 pending builds, including esbuild and Nx. No rebuild or hook
approval was needed for the two declaration producers. The pending list remains
in `metadata/state.json`; it is not hidden or described as a completed package
build.

The NodeNext consumer has no source custom condition. Its exports require the
normal `query-core` build and the `react-query` `build:tsdown` subscript. The
reviewed tsdown configs generate modern and legacy declarations and code under
each package's `build` directory. The codemod copy, release commands, Nx cloud,
and unrelated package builds are not required for these declaration exports.
The producer is the locked `tsdown@0.22.14`. Both normal declaration builds
completed without source patches. A second build produced byte-identical
generated-file manifests and the same six loaded-file manifests.

## Recorded hashes

Each manifest is JSON with sorted repository-relative paths, file sizes, file
content SHA-256 values, and literal symlink targets. These digests cover the
manifest bytes, including the final LF. The dependency snapshot also contains
package-manager metadata. It is an observed installed tree, not a substitute
for lockfile integrity or an assertion about a fresh install on another machine.

| Manifest                               | Entries | SHA-256                                                            |
| -------------------------------------- | ------: | ------------------------------------------------------------------ |
| `metadata/source.json`                 |   2,373 | `a676eb6dc8968e34a1caf928b48b3cae21c98d11429d096c7e5ecdd5f3b595b0` |
| `metadata/dependencies.json`           | 141,279 | `066ec0e312b28627e7e443bad687ff6cedecfcb3f78bac11f77803d759faedcd` |
| `metadata/generated.json`              |     706 | `5c93347a1fea93f5cede5cdd1b7911e175b49438ab358e9cb8dda46c8194b81b` |
| `metadata/generated-declarations.json` |     196 | `6d950270cecc6f8e867eda0e09a38177486c55c2fd5674f46ae559505b07312e` |
| `metadata/libraries.json`              |      82 | `957ff1939e7dc38e4186161b68909043adc81ecb6d836112b3c35addbcd100d1` |

The resolution-record SHA-256 is
`d2c9e2776b408df09ced21986412e59e733c6e707f32fd7e00be7ed894f0abcc`.

| Modern declaration entry                        | SHA-256                                                            |
| ----------------------------------------------- | ------------------------------------------------------------------ |
| `packages/query-core/build/modern/index.d.ts`   | `fb99c17668dec4539955a47e691e08339019cc6fc3a2aefe483bb24480a6cb3f` |
| `packages/query-core/build/modern/index.d.cts`  | `c4fee57b81f64b2fd6ece3783d9694ac8e2900bb2b115c1ca0564b4e8cb59c2a` |
| `packages/react-query/build/modern/index.d.ts`  | `333a8d500cfc9ba377c7ea02a250bcf2f9cbc56bdcbb9fd9b0402e89807d085f` |
| `packages/react-query/build/modern/index.d.cts` | `158702e1322f448776b213dc267b7579ba073901367f51b459a702db278a755f` |

The tool records include these SHA-256 values. The two archive digests are pinned
in the script:

- Node archive: `d804845d34eddc21dc1092b519d643ef40b1f58ec5dec5c22b1f4bd8fabde6c9`.
- pnpm archive: `2b567aa66026238078ac2e0a33bec3febd60e962987aac697456f3180819b287`.
- TypeScript 6.0.3 `lib/typescript.js`: `569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39`.

## Replay

Run each stage from a ts-rust checkout on Linux x64 with a user systemd manager.
Network stages need network approval. The script starts the bounded systemd
scope through trusted `/usr/bin` tools and uses its own verified Node and pnpm
binaries. Start it with the trusted host Node and no caller preload options.
It refuses a dirty cache,
a different pin, changed source, or a changed root selection.

```sh
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs source
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs tools
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs install
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs build
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs inventory
/usr/bin/env -u NODE_OPTIONS -u NODE_PATH /usr/bin/node scripts/prepare-query-inputs.mjs replay
```

`all` runs the first five stages. `replay` repeats the declaration builds and
inventory, then checks the generated and loaded-file hashes against the first
inventory. It does not reinstall dependencies.

The install command uses `--frozen-lockfile --ignore-scripts`, no filter, and the
isolated `pnpm-store` directory. The exact commands and exit codes are in
`metadata/commands.ndjson`. `metadata/state.json` links the resulting manifests.
Failed stages do not leave `prepared: true`.

## Script checks

`scripts/test-prepare-query-inputs.mjs` uses disposable Git repositories and
copies of the pinned archives. Set `QUERY_INPUTS_TEST_ARCHIVES` to the reviewed
prepared tree's `downloads` directory and `QUERY_INPUTS_TEST_SOURCE` to the
read-only pinned Query cache. Set `TMPDIR` to a private workspace directory
when `/tmp` lacks space. Run the tests under the same 2 GiB systemd limit.

```sh
/usr/bin/systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2147483648 -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/env -u NODE_PATH NODE_OPTIONS=--max-old-space-size=1536 \
  TMPDIR=/absolute/worktree/target/query-input-tests \
  QUERY_INPUTS_TEST_ARCHIVES=/absolute/main/target/project-inputs/query/downloads \
  QUERY_INPUTS_TEST_SOURCE=/absolute/cache/TanStack__query \
  /usr/bin/node --test scripts/test-prepare-query-inputs.mjs
```

The tests cover redirected ancestors, private cache paths, managed files,
version-spoofing tools, changed pnpm bundles, extra files, mode changes, and
symlink changes. They also check tool reuse during the install-stage entry.
No install or build runs. The tests verify that the real prepared metadata,
all 706 generated outputs, archives, source Git state, and cache Git state are
unchanged. Disposable files are removed after the tests.

## Remaining evidence

There is no current dependency-preparation blocker for these six configs.
The first install's memory failure is resolved by the bounded worker setting.
The unexecuted lifecycle hooks remain explicit and were not needed by the
reviewed declaration builds.

Rust input-graph comparison, the pinned unpatched Go oracle, diagnostics,
`.types`, `.symbols`, and cold/warm compiler parity are still pending. No hashes
or successful outcomes for those stages are supplied here.
