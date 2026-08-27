# React Hook Form input preparation

Recorded on August 26, 2026. The library and app dependencies are prepared.
This is input evidence, not a complete project manifest or a compiler parity
result. No Rust build or checker change was made.

## Source and paths

The source is `react-hook-form/react-hook-form` at
`bb3360f4db62489ed4ab4e09ccb4211a275da707`, version `7.86.0`.
Its Git tree is `12aaa0132efa2f6fe32824d81cf44bf477d74b0e`.
All 494 tracked files were copied with `git archive`. Every copied file still
matches the clean cache checkout. Source, configs, and lockfiles were not patched.

The preparation directory is:

```text
/home/theo/Code/sandbox/ts-rust/target/project-inputs/react-hook-form
```

All paths below are relative to that directory unless stated otherwise.

| Input | Path |
| --- | --- |
| Complete source copy | `source/` |
| Library config | `source/tsconfig.json` |
| App config | `source/app/tsconfig.json` |
| Library dependencies | `source/node_modules/` |
| App dependencies | `source/app/node_modules/` |
| Built library output | `source/dist/` |
| Package content store | `pnpm-store/v11/` |
| Local tools | `tools/` |
| Command records and hashes | `evidence/` |
| Command output | `logs/` |

The exploration cache remains clean at
`/home/theo/.explore/repos/react-hook-form__react-hook-form`.
No install or build ran there. The source copy retains the root MIT license
and all other tracked files. Dependency packages retain their own files and
license notices.

## Tools and reviewed commands

`CONTRIBUTING.md` requires pnpm 11 and Node 22. The pinned CI install action
selects pnpm `11.7.0` and Node major version `22`. This preparation uses the
exact Node release `22.22.0` on Linux x64. The host Node `24.13.0` only runs the
preparation script. Installs and the library build use the local Node 22 binary.

| Tool | Executable path |
| --- | --- |
| Node 22.22.0 | `tools/node-v22.22.0-linux-x64/bin/node` |
| pnpm 11.7.0 | `tools/pnpm/bin/pnpm.mjs` |
| pnpm for nested script calls | `tools/bin/pnpm` |
| Root TypeScript 6.0.3 | `source/node_modules/typescript/lib/typescript.js` |
| App TypeScript 5.7.2 | `source/app/node_modules/typescript/lib/typescript.js` |

Both package installs used:

```sh
pnpm install --frozen-lockfile --ignore-scripts --reporter=append-only \
  --store-dir /home/theo/Code/sandbox/ts-rust/target/project-inputs/react-hook-form/pnpm-store \
  --package-import-method=copy
```

The root install ran first. The normal root `pnpm run build` then produced
the package declarations and bundles. The app install ran after that build.
Each install, build, and executable-path check had a systemd scope with
`MemoryMax=2G` and `MemorySwapMax=0`. Child Node heaps used a 1.5 GiB cap.
`HOME`, package caches, tool caches, and temporary directories were redirected
into the preparation directory.

The root `prepare` hook invokes Husky. Its pre-commit hook invokes the typecheck
and lint-staged. Install scripts were disabled, and `HUSKY=0` remained set.
The root workspace also forbids automatic builds for `@swc/core`, `esbuild`,
and `unrs-resolver`. The app forbids the esbuild hook. Installed package
lifecycle commands are recorded in the package evidence files.

The reviewed library build runs its local `clean`, Rollup, and export checks.
`clean` removes only the prepared `source/dist` directory. Rollup builds CJS,
ESM, UMD, declarations, and source maps. Both ESM and CJS export checks passed.
No publish, version, git-push, browser-install, development-server, app-build,
or app-typecheck command ran.

The first build attempt used the system pnpm `11.3.0` for nested calls because
the local link pointed to the non-executable compatibility entry point. That
attempt is excluded. The link now points to the executable `pnpm.mjs`.
The root install and library build were repeated with pnpm `11.7.0`.
`logs/build-library-2.log` records the accepted build.
`logs/probe-tools-3.log` checks the nested pnpm path, version, and Node path.
The first attempt remains in the command history.

## Config roots and dependencies

The TypeScript 6.0.3 config reader reproduced both full upstream root lists.
No include, exclude, compiler option, or type package was changed.

| Config | Root files | TSX files | Resolution | Explicit types |
| --- | ---: | ---: | --- | --- |
| `tsconfig.json` | 109 | 6 | Bundler | Jest, Node, testing-library/jest-dom |
| `app/tsconfig.json` | 45 | 44 | Node | vite/client |

Both retain `strict: true` and `jsx: react`. The root retains `skipLibCheck:
true`. The app retains `skipLibCheck: false`. Root-list hashes match the modern
project inventory exactly. `evidence/root-files.txt` and
`evidence/app-root-files.txt` contain every selected path, sorted, with one
path and LF per line.

| Dependency tree | Installed package directories | Regular files | Symlinks |
| --- | ---: | ---: | ---: |
| Root | 676 | 19,867 | 2,138 |
| App | 151 | 9,165 | 417 |

These are installed package instances, including peer-version contexts.
They are not counts of unique package names. Every recorded symlink resolves
inside the preparation directory. The frozen lockfiles also describe optional
packages for other operating systems that were not installed on this host.

Root dependencies include React `19.2.7`, `@types/react` `19.2.17`,
`@types/node` `25.9.3`, and `@types/jest` `30.0.0`. The app independently uses
React `19.0.0` and `@types/react` `19.0.2`. These versions were not unified.
`evidence/compilers.json` records each compiler file hash and all installed
standard-library file hashes, 108 for TypeScript 6.0.3 and 96 for 5.7.2.

The app's `react-hook-form` link is:

```text
source/app/node_modules/react-hook-form
  -> .pnpm/react-hook-form@file+.._react@19.0.0/node_modules/react-hook-form
```

The local package's `package.json` matches the source package byte for byte.
Its 224 `dist` files also match the accepted library build byte for byte.
They include 109 `.d.ts` files and 109 declaration maps. The app consumes
`dist/index.d.ts` through the unchanged package export map. Its source also
imports `../../src/types` in `app/src/test.tsx` and `app/src/setError.tsx`.
The complete source copy preserves those paths.

## Hash evidence

All values below are SHA-256. Full per-file records are in `evidence/`.

| Input or evidence file | SHA-256 |
| --- | --- |
| `source.tar` | `a30d9ab79e2faf7fa60acbfff038ec8dc88de0cff5f45cc233d73f72357e0ce8` |
| `source/pnpm-lock.yaml` | `7acb3dc72842c76da85d5a9dd0e8c589c18250c2b2e46b0dbe4948798df0d14a` |
| `source/app/pnpm-lock.yaml` | `5c31f94a9ae847852866bafbac415bcc68273c678334c3b2fe9277800cce57ea` |
| Node archive | `9aa8e9d2298ab68c600bd6fb86a6c13bce11a4eca1ba9b39d79fa021755d7c37` |
| pnpm archive | `deafa7ec98a1218b6a047289b92fbe2395c1e22d3495bb711653013218ee15ee` |
| Root `typescript.js` | `569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39` |
| App `typescript.js` | `9e2becd9f76b5b1048ff907b824c61cc164efcfbe1e3b34681c20b9adc912d3a` |
| Root file list | `7963c7ea867f902a71da242554466828fc169034c75c66920cd6d2c41378bae0` |
| App root file list | `af71e8cab3b67cb538d918b5828317f1e16bc5bdfbb75e71585bf590c452c203` |
| `evidence/root-packages.json` | `8d7b60d9fe25d6e9c7b78a6589542e7385662e4ce54f5c8dcf6c467084e1bd54` |
| `evidence/root-links.json` | `2c1350acea83bab3407cd1dd2874450d633f3abb3551d7577735fdf6c3ad4a07` |
| `evidence/app-packages.json` | `48dda2945db929498e6edb14c6712f3f9d7da97944e53060383a9a2cdf2041a7` |
| `evidence/app-links.json` | `d51fb9262b1d3557e0889121a11633820afb4cfc1abee0ee1b431f1b053814d2` |
| Both `library-dist-files.jsonl` files | `5b9bf8ccbee560fc2044567db7f1b6dd871bd703579bebdb2edd7e786b6ea4d2` |
| Both library `dist/index.d.ts` files | `77a8e292d02cd1017e283ac0e26fd644caa498411ea2abb2e916ce04514bfb6f` |
| `evidence/commands.json` | `89e3cddae017524982f57475b2a64ae5ec62c97c47d4f4fbad390722ae092fca` |
| `evidence/summary.json` | `6cc9e8c675e88d2d2ab52099e7d2984777a0db213070c1021e69ed04c1f49c4a` |

`root-files.jsonl` and `app-files.jsonl` record package-tree file bytes and
relative symlink targets. They do not follow symlinks while hashing.
Each package's `contentSha256` hashes its sorted file records with paths
relative to that package. Link evidence separately records absolute resolved
paths. File modes and timestamps are not part of these content hashes.

## Replay and remaining work

Run from the ts-rust checkout or its worktree:

```sh
NODE_DISABLE_COMPILE_CACHE=1 node scripts/prepare-react-hook-form-inputs.mjs all
```

The script derives the main workspace from Git's common directory. It writes
only under `target/project-inputs/react-hook-form`, except for ephemeral
systemd scope state. It fails on changed source, lockfiles, tool archive
checksums, config root lists, missing pinned-tool commands, external dependency
links, or a local app package that differs from the library build.

Stages can run separately: `snapshot`, `tools`, `install-root`, `probe-tools`,
`build-library`, `install-app`, and `evidence`. Network stages need network
permission. Installs and builds require a working user systemd manager.

No dependency-preparation blocker remains for these two configs. The app build
and typecheck were not run. Disabled native install hooks and browser binaries
remain outside this preparation, so the result does not certify the test or
development environment.

Go project graph collection, Go library selection, diagnostics, types, symbols,
Rust comparisons, cold and warm replay, and performance measurements remain
pending. The installed TypeScript libraries are recorded inputs, not proof
that the pinned Go compiler will use identical library bytes. No complete
modern-project manifest or parity digest was created.

## Safety repair

Commit `2f9e1cff` repairs the path and tool-reuse checks. The inputs above were
prepared by `e530030f`. Their evidence still identifies that original script.
No preparation stage was rerun against the saved input during this repair.

The script now rejects invalid stage arguments before initialization. It
checks output ancestors, managed directories, and existing file destinations
with `lstat`, including dangling symlinks. Direct file writes use `O_NOFOLLOW`
and validate the open file before truncation. The Git archive goes to a checked
file descriptor. Archive extraction requires an empty destination. Install and
build commands check the managed paths before and after execution.

Valid package links must resolve inside the preparation directory. pnpm's
project links and internal hard links remain supported. A hard link with an
unaccounted name outside the input directory is rejected. The pinned command
links must exist before a tool command can run. The executable-path probe
checks the resolved pnpm path before requesting its version.

Tool reuse no longer trusts version output or an existing `tools.json` file.
The fixed archive hashes are checked first. The extracted directories must
then match these archive-derived catalogs before execution:

| Payload | Catalog entries | Catalog SHA-256 |
| --- | ---: | --- |
| Node 22.22.0 | 6,195 | `7d651642d670837f30481a8dcae4c64ea2f2844e260562287f9b86024f756a0b` |
| pnpm 11.7.0 | 554 | `6afe3ac41ccdec75532fd42b6644eb1143b1d4105a313a0c86e706f399e961a1` |

Tool catalogs include directory and file modes, file lengths and hashes, and
symlink text. The tests independently extracted both pinned archives into empty
disposable directories and reproduced these hashes. They then rejected a fake
pnpm CLI that reports `11.7.0`, a changed pnpm bundle, a changed Node binary, an
extra tool file, and a changed archive. The fake CLI's execution marker was not
created.

The final safety run passed **43 tests, with no failures or skips**. It also
covered output and ancestor symlinks, managed directory symlinks, existing and
dangling file symlinks, links introduced after an earlier check, external hard
links, missing command links, and valid contained package links. All mutations
were inside disposable fixtures. No install, build, or package-manager command
ran in these tests.

The run used `scripts/prepare-react-hook-form-inputs.test.mjs`, a 2 GiB systemd
scope, and a 1536 MiB Node heap. From the repair worktree, the command was:

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2G -p MemorySwapMax=0 \
  env RHF_TOOL_ARCHIVES=/home/theo/Code/sandbox/ts-rust/target/project-inputs/react-hook-form/tools \
  TMPDIR=/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave129/inputs-react-hook-form/target/safety-tests \
  NODE_OPTIONS=--max-old-space-size=1536 \
  node --test --test-concurrency=1 --test-reporter=tap \
  --test-reporter-destination=target/safety-tests/react-hook-form-safety.tap \
  scripts/prepare-react-hook-form-inputs.test.mjs
```

The report is in that worktree's `target/safety-tests/react-hook-form-safety.tap`.
Its SHA-256 is
`be74652ef1c79b5aec83bb07b2e4ec3f42c8419efd4d0975e287915c40707d7c`.
A read-only audit checked all 494 source records, 22,005 root dependency
records, 9,582 app dependency records, and both 224-file build catalogs against
the saved hashes. It also checked the tool catalogs and current path guards.
The saved summary remains
`6cc9e8c675e88d2d2ab52099e7d2984777a0db213070c1021e69ed04c1f49c4a`.
The source cache and prepared input were not changed.

This proof covers the safety repair. It does not add a fresh dependency install,
compiler graph comparison, or parity result.

## Bootstrap repair

Commit `dad3e789` closes the bootstrap command and inherited compile-cache gaps
found in the next review. Bootstrap commands now use `/usr/bin/git`,
`/usr/bin/tar`, `/usr/bin/systemd-run`, and `/usr/bin/which` directly.
Their environment has `PATH=/usr/bin:/bin`. A partial Node directory cannot
select an archive tool or decompressor. Extra entries in `tools/bin` are
rejected. Node tool commands receive the prepared tool directories on `PATH`
only after their archive contents and command links pass verification.

Every tool subprocess gets `NODE_COMPILE_CACHE` set to the checked
`cache/node-compile` directory under its output. Read-only Git queries remove
the inherited cache setting and disable Node compile caching.
The documented launcher also disables caching in the caller's Node process,
which starts before the preparation script can check its paths.

The expanded run passed **48 tests with no failures or skips**. New cases
confirmed that an untrusted inherited Git command was not selected, a fake
`tools/bin/tar` was rejected, and fake `tar`, `gzip`, `xz`, and `git` commands in
a partial Node directory were not executed. The extraction record named
`/usr/bin/tar` and retained the system-only bootstrap `PATH`.

The compile-cache test ran authenticated Node and pnpm version commands with
an outside cache setting. The outside directory stayed unchanged, and the
checked private cache received files. The runner started with caching disabled.
The test enabled it only for the authenticated tools inside the fixture.
No dependency install or project build ran.

The command ran from the repair worktree:

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryMax=2G -p MemorySwapMax=0 \
  env RHF_TOOL_ARCHIVES=/home/theo/Code/sandbox/ts-rust/target/project-inputs/react-hook-form/tools \
  TMPDIR=/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave129/inputs-react-hook-form/target/safety-tests \
  NODE_OPTIONS=--max-old-space-size=1536 NODE_DISABLE_COMPILE_CACHE=1 \
  node --test --test-concurrency=1 --test-reporter=tap \
  --test-reporter-destination=target/safety-tests/react-hook-form-bootstrap-safety.tap \
  scripts/prepare-react-hook-form-inputs.test.mjs
```

The new report is `target/safety-tests/react-hook-form-bootstrap-safety.tap`
in that worktree. Its SHA-256 is
`ae7396ebe926cf2a1a45084b5619e5c9cf78c3c7eb312e97c4d24d030f2c9d88`.
The earlier 43-test report was preserved.

A fresh read-only audit rebuilt the dependency and build catalogs from the
saved files. It checked the 494 source records, 22,005 root dependency records,
9,582 app dependency records, both 224-file build catalogs, tool contents,
command links, and path guards. Every recorded hash still matched. The saved
summary remains
`6cc9e8c675e88d2d2ab52099e7d2984777a0db213070c1021e69ed04c1f49c4a`.
The prepared input and source cache remain unchanged. These tests do not add
a fresh preparation run or compiler parity evidence.
