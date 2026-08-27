# Hono input preparation

Recorded on August 26, 2026. This is a source and dependency preparation result.
It is not a complete project manifest or a compiler parity result. No Hono
build, TypeScript typecheck, Rust build, or Go oracle run was done.

## Prepared paths

- Source and installed dependencies:
  `/home/theo/Code/sandbox/ts-rust/target/project-inputs/hono/source`
- Fresh replay:
  `/home/theo/Code/sandbox/ts-rust/target/project-inputs/hono/replay/source`
- Evidence:
  `/home/theo/Code/sandbox/ts-rust/target/project-inputs/hono/evidence`

The source is `honojs/hono` at commit
`06880c4a2b04de9dd74217f26dd831209b9c01f1`, package version `4.13.5`.
The cached checkout at `/home/theo/.explore/repos/honojs__hono` was clean before
and after both runs. Its files and Git state were not changed.

All 486 tracked files were copied with `git archive`. The script checked each
copied file against its Git blob hash and executable bit before and after the
install. It retained the license, docs, tests, benchmarks, runtime fixtures,
and all source files. It did not copy only the selected compiler roots.

## Config and source

The config is the unchanged `tsconfig.build.json`, which extends
`tsconfig.base.json`. It selects 188 roots and retains `strict: true`,
`module: ES2020`, `moduleResolution: Bundler`, and `types: [node]`.

The root list includes `src/adapter/deno/deno.d.ts`. The upstream
`src/**/*.mts` include rule remains unchanged. This pin has no `.mts` roots.
Only the upstream test exclusions apply. TypeScript 6.0.3 read the config
without checking types or loading the full program graph.

| Input | SHA-256 |
| --- | --- |
| `source.tar` | `2067129afb31dd150c899c58e8fe9d12a7719ff76f0f15f1df1ac8237778f8d8` |
| `source-files.jsonl` | `e69d516150f81c17a762cebb5f1e2764ac927be600efc5569fb31e25bb780912` |
| `package.json` | `f72a19433e0464741e559bdfdf0ac5184fc95f2e00ff238d7f521d665b3d337c` |
| `bun.lock` | `910eec46012b95777558e1a8b568e63cf48c7167d12e7deaa60382d474fcdfff` |
| `tsconfig.build.json` | `e3105932180e5845959744d315a68fbfe887abc592eb795d0fbf0444996f418e` |
| `tsconfig.base.json` | `760c889e56720a57bf31b567851adef87779381a2dc39aa2b38090f89bde307d` |
| `tsconfig.build.files` | `4014df7bbea8c85b02685c887d1ac55ab00d96c7987775a02943e91e4360fb12` |
| `src/adapter/deno/deno.d.ts` | `f34887e7d3ff8901241f572d27d6e51d06c5d6b1890f02d1c9e6414bb2de2313` |

The source Git tree is `21207a08415aa7137036102d59ddbb677936c3cb`.
`source-files.jsonl` has one JSON record followed by LF per tracked path,
sorted by path. Each record has the Git mode, Git blob ID, byte length, and
SHA-256 of the copied bytes. The root list has one relative path and LF per
file, including the final file.

## Tools

Bun is `1.2.20+6ad208bc3`. Its Linux x64 archive matches the official release
asset digest and the downloaded `SHASUMS256.txt` entry. The retained release
metadata and checksum list are under `toolchain/` beside the archive.

| Tool input | SHA-256 |
| --- | --- |
| Bun `bun-linux-x64.zip` | `4e9edc4cba0c7c1623a288be01e53bbde11a4d073f2cf339cab026627858b548` |
| Extracted Bun binary | `79af131f0f24e48e419ae4ce3dd1c8d46d615c2b9c2e10b0259959a2e17847c0` |
| Bun `SHASUMS256.txt` | `1a64e04e1cb7f0a94e627aacfeb79badc5a37a7026cf361b6bec5d19777bd903` |
| Node `v24.13.0` binary | `53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc` |
| TypeScript `6.0.3` `lib/typescript.js` | `569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39` |
| Initial preparation script | `585a99cc20d0c7bb6b390369ebf62f900bbd899f01fadbb99fe845fd93340227` |
| Script with path checks | `15abcd320a371becc5fc680fe7cbb0fb4be2f7ebe8fb2b39339db2eac335a016` |

The host was Linux x64, kernel `7.0.12-1-cachyos`, glibc `2.43`, Git `2.54.0`,
and GNU tar `1.35`. Both runs used a systemd scope with a 2 GiB memory limit
and no swap. Each run had its own home, Bun cache, temporary directory, and
dependency tree under `target/project-inputs/hono`. No global package manager
was installed or changed. The replay reused only the verified Bun archive.

Hono's `package.json` selects `bun@1.2.20`, while its checked-in `.tool-versions`
still lists Bun `1.2.19` and Node `24.7.0`. Both files were retained unchanged.
The package manager pin and this task selected Bun `1.2.20`. The Node version
above is the measured preparation tool, not a claim that the CI tool versions
match this machine.

## Install policy

The install used the pinned Bun binary with these arguments:

```text
install --frozen-lockfile --ignore-scripts --backend=copyfile --linker=hoisted
--network-concurrency=8 --no-progress --registry=https://registry.npmjs.org
--cache-dir=<output>/cache/bun
```

No dependency category was omitted. Bun selected platform packages for Linux
x64. Package integrity verification stayed enabled. Both runs returned exit
code 0 and reported 781 installed packages. The installed tree has 920 package
locations, including nested copies, 33,249 regular files, and 70 symbolic links.
The symbolic links stay inside the prepared source tree.

| Installed evidence | SHA-256 |
| --- | --- |
| `dependency-files.jsonl` | `791bc91b9186ac37f25b879774264bca8ebc3ef99a90a8d6d3cf75155b05c063` |
| `packages.json` | `4f67964e9f3d602d8cfa96ef74548d3ac14de801b5daa2d1198fa3842ffc5482` |
| `lifecycle-hooks.json` | `f283aea44754ea927b2de35ac7f2e0199607c51bd829cf190e9a7672ec7b3119` |
| `missing-package-paths.json` | `735f62efedb760dc393b754a7fcecd5923264007a36d811cef02cba6eb1eeb2d` |

The dependency file inventory visits each directory in sorted name order.
Each regular-file record has its path relative to `node_modules`, mode, byte
length, and SHA-256. Each symbolic-link record has its relative path and exact
link text. Directories, timestamps, ownership, and cache contents are not part
of this digest. The whole inventory uses JSON records with one LF per record.

Locked direct versions include `typescript@6.0.3`, `@types/node@24.3.0`,
`bun-types@1.3.2`, and `@typescript/native-preview@7.0.0-dev.20260210.1`.
The native-preview package was not run. It is not the separately pinned Go
oracle from `UPSTREAM.md`.

## Hooks and missing output

The root package has no install or prepare hook. Its `build` script removes
`dist`, emits JavaScript and declarations, rewrites private declaration fields,
and copies the CommonJS package files. Its `postbuild` script runs `publint`.
Neither was run.

The installed packages declare install hooks at eight locations:

- Four esbuild versions run `node install.js`: `0.21.5`, `0.23.1`, `0.27.1`,
  and `0.28.1`.
- `workerd@1.20260701.1` runs `node install.js`.
- `msw@2.6.0` has a postinstall script that can copy configured worker files.
- `sharp@0.34.5` checks native library use and can request a source build.
- `unrs-resolver@1.11.1` calls `napi-postinstall`.

All these hooks stayed disabled. The complete hook inventory has 87 locations
when prepare and publish hooks are also counted. The Linux esbuild and workerd
binary packages are present. Their package launchers remain JavaScript files,
so their install-time launcher replacement did not occur.

Hono's `dist` directory is absent. This includes `dist/types/index.d.ts`,
`dist/index.js`, and `dist/cjs/index.js`. Package-consumer checks that need those
outputs still require a separate reviewed build.

The path scan also reports absent literal paths in 36 dependency locations.
Examples include Babel helper `lib/index.d.ts` paths and
`@bytecodealliance/componentize-js/types.d.ts`. These findings are retained in
`missing-package-paths.json`. They are not 36 confirmed module-resolution
failures. Some package fields omit extensions or refer to conditions that the
selected program might not use. The scan does not implement module resolution
or expand wildcard exports. No package was patched or excluded to hide a
missing path.

## Path checks

The repaired script checks the nearest existing output ancestor and all
existing entries under its managed directories before it creates a directory.
It rejects output paths that overlap the read-only cache, symlinked output
ancestors and children, dangling links, and hard-linked output files. It also
checks controlled file destinations again before writing them.

Seventeen tests used disposable fake-cache paths under the input's `tmp`
directory. Every case failed before any filesystem change. The tests did not
use the real cached repository or run an install. The cases cover the output,
its ancestors, each managed directory, tool archives and binaries, source
archives, evidence files, dangling links, and a shared archive file.

A fresh frozen install with the repaired script also passed under the same
2 GiB limit. Its six source, dependency, config-root, package, hook, and
missing-path inventories match the original evidence byte-for-byte. The
original prepared trees and evidence were not changed.

The new proof is under
`/home/theo/Code/sandbox/ts-rust/target/project-inputs/hono/path-repair-proof`.
Its `evidence/path-guard-tests.json`, `evidence/preparation.json`, and
`evidence/original-comparison.json` record the repaired script hash shown above,
the rejection tests, and the fresh preparation result.

## Replay

Both preparations used separate empty dependency caches. The six inventories
listed in `evidence/replay-comparison.json` are byte-identical between the first
run and replay. The source archive and lockfile hashes also match. This proves
these copied inputs repeat on this host. It does not prove a complete compiler
module graph, Go artifacts, Rust parity, or performance.

Run the preparation from the ts-rust root with an existing pinned cache and a
new output directory:

```sh
node scripts/prepare-hono-inputs.mjs \
  "$HOME/.explore/repos/honojs__hono" \
  "$PWD/target/project-inputs/hono/reproduction"
```

The script needs network access for uncached downloads and a working user
systemd manager for the memory limit. It refuses an existing `source` directory.
It writes the exact install command, install log, source and dependency file
inventories, package metadata, hooks, missing literal paths, config roots, and
`preparation.json` under `<output>/evidence`. It never runs a compiler check or
Hono's build scripts.

`tools/ts_fixture/manifests/modern-projects-v1.tsv` is still not supplied by this
task. The full Rust and Go input graphs and exact oracle artifact hashes remain
pending.
