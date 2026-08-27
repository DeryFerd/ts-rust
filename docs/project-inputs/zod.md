# Zod prepared inputs

Recorded on August 26, 2026. This is dependency preparation, not compiler parity.
No project build, test suite, TypeScript typecheck, Rust build, or Go compiler run
was performed.

The preparation facts below describe the historical receipt from commit
`9cd67c92`. The later security repair changed the script and tested it in
disposable directories. It did not change the prepared input or the real source
cache. The guarded procedure below uses verified archive contents and produces
a different tool manifest. It has not regenerated this historical receipt.

## Prepared paths

Paths below are relative to the main ts-rust checkout.

| Item                            | Path                                                          |
| ------------------------------- | ------------------------------------------------------------- |
| Source and dependencies         | `target/project-inputs/zod/source`                            |
| Selected config                 | `target/project-inputs/zod/source/packages/zod/tsconfig.json` |
| Evidence receipt                | `target/project-inputs/zod/evidence/preparation.json`         |
| Package store                   | `target/project-inputs/zod/pnpm-store`                        |
| Node, Corepack, and pnpm copies | `target/project-inputs/zod/toolchain`                         |
| Cache and temporary files       | `target/project-inputs/zod/{cache,npm-cache,config,data,tmp}` |
| Reproduction script             | `scripts/prepare-zod-project-input.mjs`                       |

The prepared source is
`/home/theo/Code/sandbox/ts-rust/target/project-inputs/zod/source` on this machine.
The script uses the common Git directory to locate the main checkout when it
runs from a worktree. `ZOD_INPUT_OUT` can set an explicit output directory.

## Source pin

- Repository: `colinhacks/zod`.
- Commit: `43f729db4aa0cedff6d6b3261f33f8556b3c7102`.
- Git tree: `992c4000825b1e2e8b6a835b3f5471caebafa4ed`.
- Cache checkout: `/home/theo/.explore/repos/colinhacks__zod`.
- All 669 tracked entries match their Git blob IDs after installation.
- The archive retains source files, tests, instructions, licenses, and symlinks.
  It has no Git metadata. No cache checkout or upstream source file was changed.

The root `AGENTS.md`, package manifests, workspace settings, config chain, and
Git hooks were inspected before installation. The root license is MIT. Package
license files remain in the source copy and installed package contents.

## Config and declarations

The selected config is unchanged. It extends `.configs/tsconfig.base.json` and
includes `**/*.ts`. Its 321 root files include 189 test files. No tests or type
packages were excluded, and no replacement config or declaration shim was added.

| Option                    | Recorded value          |
| ------------------------- | ----------------------- |
| Target                    | ES2020                  |
| Libraries                 | ES2020 and DOM          |
| Module and resolution     | NodeNext                |
| Strict checking           | `true`                  |
| No emit                   | `true`                  |
| Exact optional properties | `true`                  |
| Skip library checking     | `true`, as set upstream |
| Custom conditions         | `@zod/source`           |
| Type packages             | `vitest`, `recheck`     |

The installed TypeScript 5.5.4 config reader selected the same root-list hash as
the inventory's TypeScript 6.0.3 reader. This is a config/root-list check, not a
typecheck or proof that the compilers agree.

Resolver probes with the original options found source files for `zod`,
`zod/v3`, `zod/v4`, `zod/mini`, and `zod/v4/core`. All resolved beneath
`packages/zod/src`. Type-reference probes found these shipped declarations:

| Package                | Declaration          | SHA-256                                                            |
| ---------------------- | -------------------- | ------------------------------------------------------------------ |
| `vitest@4.1.5`         | `vitest/index.d.cts` | `db8e26b83e6708b250200435440c326d84dd9f07114c72b33775569486bebd0b` |
| `recheck@4.6.0-beta.3` | `recheck/index.d.ts` | `3e1b56ee0607db56fcb000e0ca33532dc7015396c9deaaddf907683d06800348` |

The receipt contains their full paths within pnpm's virtual store. The default
built Zod entries `packages/zod/index.js` and `packages/zod/index.d.cts` are
absent. The selected source condition was retained rather than replacing those
missing build outputs.

## Install and hooks

The full eight-project workspace was installed with pnpm 10.12.1. No package
filter was used. pnpm reports the lockfile as current and skips resolution.
Its recorded module state includes regular, development, and optional
dependencies, with the isolated node linker.

The install uses these settings:

```text
--frozen-lockfile
--ignore-scripts
--ignore-pnpmfile
--package-import-method=copy
--network-concurrency=4
--child-concurrency=1
```

The package store, package manager cache, user config, and temporary files stay
under the output directory. Node 24.13.0 and Corepack 0.34.5 were copied from the
existing host tools. pnpm was downloaded into the isolated Corepack cache. No
global package manager was installed or changed.

The root `prepare` hook runs Husky. The docs package has a `fumadocs-mdx`
`postinstall`, and the tsc benchmark package has a `prepublish` build. The Git
hooks run version checks, comment checks, formatting, and tests. No pnpm hook
file was present. These hooks were not run.

The installed package manifests contain 73 packages with lifecycle scripts.
pnpm retains 11 pending-build entries, including repeats after the install
replay. The eight distinct entries are the root, `packages/docs`, `packages/tsc`,
`sharp@0.34.5`, `@biomejs/biome@1.9.4`, and esbuild versions 0.25.5, 0.25.8,
and 0.27.7. Nothing was rebuilt to clear that list.

## Resource and machine facts

Each install ran in a user systemd scope with a 2 GiB memory limit and no swap.
The final setup uses a 768 MiB Node heap and one package worker. In pnpm 10.12.1,
`PNPM_WORKERS` is an idle-CPU count, not the requested worker count. The script
sets it to the available CPU count. That was 32 here and leaves one worker.

The first attempt did not set that package-worker limit. The kernel ended its
2 GiB scope for an OOM condition. The source and lockfile still matched their
pins. The bounded retry completed, and a later frozen install replay reported
that dependencies were already current. The first attempt's progress log is
retained as `evidence/install-initial-terminated.log`.

| Item          | Recorded value                              |
| ------------- | ------------------------------------------- |
| System        | Linux x64                                   |
| Kernel        | `7.0.12-1-cachyos`                          |
| C library     | glibc 2.43                                  |
| CPU           | AMD RYZEN AI MAX+ PRO 395 with Radeon 8060S |
| Logical CPUs  | 32                                          |
| Node          | 24.13.0                                     |
| Corepack      | 0.34.5                                      |
| pnpm          | 10.12.1                                     |
| Config reader | TypeScript 5.5.4 from the root lockfile     |

These are preparation facts. They are not compiler timing or memory results.
The historical tool manifest hashes 1,167 copied tool entries, including the
package manager worker code. Node's executable SHA-256 is
`53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc`.
The TypeScript reader's SHA-256 is
`f7ff3e27aafe5dcc82d0307575e9a7dc5b053b141da123bec81c858537765b56`.

## Package content and links

The final tree has 1,061 physical dependency packages, with 48,052 package file
entries and 1,170,055,147 regular-file bytes. All contents were hashed, including
declarations and license files. The module state records 187 skipped optional
package entries for this install profile. Their names remain in the receipt,
and they were not removed from the lockfile.

All 3,343 dependency symlinks resolve inside the prepared source. None is broken.
Eleven are workspace links to `packages/zod`:

- The root `node_modules/zod` link.
- One link in each of `bench`, `integration`, `resolution`, `treeshake`, and `tsc`.
- Five peer links in `@ai-sdk/gateway`, `@ai-sdk/openai`,
  `@ai-sdk/provider-utils`, `ai`, and `drizzle-zod` virtual package directories.

Full paths and literal link targets are in `dependency-links.jsonl`. Other
installed Zod versions remain separate registry packages. They were not
replaced with the workspace package.

## Content hashes

SHA-256 values cover exact file bytes. Evidence paths are relative to
`target/project-inputs/zod/evidence`. Source metadata paths are relative to the
prepared source.

| Input or evidence             | SHA-256                                                            |
| ----------------------------- | ------------------------------------------------------------------ |
| Source tar archive            | `4f5e26542e189286be4f4256382467f78ae434144e3f0b87ba9edd4ce7114e43` |
| `source-files.jsonl`          | `be7bb6f7d3885d32b2d99f1a98ac4cac64d7784f79afb71f406d8f17b4bb636f` |
| Root `pnpm-lock.yaml`         | `03627f8232469285ad0ae0199f749bf5471f71e4d78f709cb74ad63bbf87bbc3` |
| Root `package.json`           | `b0cfd5f9fbc1d534d85be27673f96c676a4b5a1685d2b9a91d82859367df4d5e` |
| `packages/zod/package.json`   | `08f7eb795dd0069f45be7ed5bb3e50096d6897e8edee694499e9521f727aa3ef` |
| `pnpm-workspace.yaml`         | `850146353e93630000e16cd9eb3b9538e2791c33a8a5fcd89612bb00c42a00ba` |
| `.configs/tsconfig.base.json` | `226711c3bf0132b51dde119447fe52abd0afeea3c4ee39a7fe9bc6583267f28a` |
| `packages/zod/tsconfig.json`  | `f825769071e877be54d68eb5cc88581b052df312f2ec16ff2e516b54df663939` |
| `metadata-files.jsonl`        | `50c952c82683dd4be2cbc5f70594cff54fea5cd6f3b182b56b446f86af6b3bf7` |
| `packages.jsonl`              | `ed0a679e7920701ede02a69d4b3abd00bb591f483889a107b7411d9f0e20961b` |
| `package-files.jsonl`         | `e92c4c26728e9d9d102c7ec98276ad560f0ddcbabd51970de9c0f4360c7387f0` |
| `dependency-links.jsonl`      | `97e8b16cdedcb2d32496906762a5ae23d635458ef7e084fc0fabbf1b6538d652` |
| `tool-files.jsonl`            | `ff1ca8b9bb3c6ca1c7c8d8fdc836ed3ceea9fb0bf2afecaac46453ee5374b678` |
| `zod-root-files.txt`          | `0433cde05204a2323ca8f6626dd92c302b16d6cca7f511e13fb95f449573f54f` |
| `preparation.json`            | `539b3e0cba6f7e6345f78d3d7f3e0c6689bd13c9b9e41bee96a36e3aeade1315` |

JSONL manifests contain one JSON object per line with a final LF. Paths are
sorted by UTF-8 bytes. Each package content hash covers its sorted relative
file records, with file content hashes, executable flags, and literal symlink
targets. Dependency symlinks are not followed while hashing package contents.
The root list contains one repository-relative path per line with a final LF.

Two audit runs produced byte-identical `preparation.json` files, checked with
`cmp`. This proves stable auditing of this prepared tree. A second clean
installation into a separate directory has not been compared. Install logs,
scope paths, and generated pnpm metadata can differ between installations.

## Path and tool guards

The repaired script checks every existing output component before it creates
directories or writes files. It rejects symlinked output roots, ancestors,
managed directories, and managed files. It also rejects hardlinked files and
special files. Canonical cache paths use the native OS resolver. They prevent a
symlinked cache alias from hiding overlap with the output, including links with
later `..` components.

Source and dependency symlinks remain valid only if their relative targets and
resolved paths stay inside the source directory. The script checks the full
writable tree before pnpm runs. Config, evidence, logs, and archives use checked
temporary files and atomic replacement. Writes use descriptors opened with
`O_NOFOLLOW`.

The script checks each archive digest before parsing or extracting it. The
archive helper rejects unsafe paths, duplicate paths, hardlinks, special files,
escaping links, and files below link ancestors. Extraction uses a new private
directory. It never extracts over an existing tree. The source archive must
match the historical SHA-256 above, including when the archive is reused.

| Tool             | Pinned archive                   | Verified contents             |
| ---------------- | -------------------------------- | ----------------------------- |
| Node 24.13.0     | `node-v24.13.0-linux-x64.tar.gz` | `bin/node`                    |
| pnpm 10.12.1     | `pnpm-10.12.1.tgz`               | Complete package, 1,111 files |
| TypeScript 5.5.4 | `typescript-5.5.4.tgz`           | Complete package, 120 files   |
| YAML 2.8.3       | `yaml-2.8.3.tgz`                 | Complete package, 233 files   |

The Node archive SHA-256 is
`6223aad1a81f9d1e7b682c59d12e2de233f7b4c37475cd40d1c89c42b737ffa8`.
The npm archive SHA-512 values are in `toolPins` in the script. Archives are
stored under `toolchain/archives`. Every tool use compares the extracted file
set, file modes, and file contents with its pinned archive. Missing, added, or
changed files fail the check before execution. Version output is not an
integrity check. Existing tool trees that fail verification are not replaced.

Corepack no longer runs. The verified Node executable runs pnpm directly.
Audit parsing loads separate, verified TypeScript and YAML package copies.
It does not execute the reader copies from installed project dependencies.

The host Node, Git, curl, Python interpreter, and preparation script are trusted
bootstrap tools. These path checks do not claim to prevent concurrent filesystem
mutation. Keep exclusive control of the output while preparation runs.

## Reproduce

Use the main ts-rust checkout, a trusted host Node 24.13.0, Git, curl, Python
3.11 or later, and the unchanged cache checkout at the pinned commit. This
profile requires Linux x64 and a user systemd manager with cgroup v2. The script
refuses a dirty or moved cache. All three actions require a memory limit of at
most 2 GiB and no swap. Network access is needed when pinned tool or dependency
content is absent.

Use a new output directory to keep the historical prepared input unchanged.
Start each command with the trusted host Node, not a reused executable beneath
the output directory.

```sh
export ZOD_INPUT_OUT="$PWD/target/project-inputs/zod-verified"

systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2147483648 -p MemorySwapMax=0 \
  env NODE_OPTIONS=--max-old-space-size=768 TMPDIR="$ZOD_INPUT_OUT/tmp" \
  node "$PWD/scripts/prepare-zod-project-input.mjs" materialize

systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2147483648 -p MemorySwapMax=0 \
  env NODE_OPTIONS=--max-old-space-size=768 TMPDIR="$ZOD_INPUT_OUT/tmp" \
  node "$PWD/scripts/prepare-zod-project-input.mjs" install

systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2147483648 -p MemorySwapMax=0 \
  env NODE_OPTIONS=--max-old-space-size=768 TMPDIR="$ZOD_INPUT_OUT/tmp" \
  node "$PWD/scripts/prepare-zod-project-input.mjs" audit
```

The script does not run clean, build, release, or lifecycle commands. Keep
`@zod/source`, the original config, and both type packages for later compiler
runs. Do not switch to `tsconfig.build.json` to avoid test inputs.

## Guard tests

The native Node tests use disposable directories under the worktree's
`target/zod-guard-tests`. They do not use the real Zod cache or prepared input.
The offline cases check path redirection, hardlinks, unsafe archives, changed
executables that print the expected version, changed supporting files, and
missing or added tool files. External sentinel files must remain unchanged.

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2147483648 -p MemorySwapMax=0 \
  env NODE_OPTIONS=--max-old-space-size=768 \
  node --test scripts/prepare-zod-project-input.test.mjs
```

Set `ZOD_TEST_PUBLISHED_TOOLS=1` in the test environment to also download the four
pinned tool archives into disposable storage. This test verifies their complete
selected contents, runs Node and pnpm version commands, and loads the verified
TypeScript and YAML readers. It does not install Zod dependencies or run a
project build, test, or typecheck.

## Remaining evidence

The complete resolved module graph and built-in library inputs still need
verification with the pinned Go compiler and Rust checker. Config parsing and
the listed resolution probes are not that verification.

Go diagnostics, `.types`, and `.symbols` digests remain absent. Cold runs,
forced warm replay, Rust comparisons, and performance measurements remain
pending. The host's glibc version is recorded, but system libraries are not
archived with the copied Node binary. Skipped lifecycle hooks and published-entry builds
remain untested. This document does not make a complete project-ring manifest
or a passing parity claim.
