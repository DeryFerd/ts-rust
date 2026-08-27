# Effect project inputs

Recorded on August 26, 2026. Dependencies are prepared. The complete compiler
input graph and Go artifacts are still pending. This is not a passing ring,
a complete manifest, or a parity result.

## Prepared source

- Repository: `Effect-TS/effect`.
- Commit: `0d083ba26b2e1afec8d3e8d83db0d05683b6602b`.
- Package: `effect@4.0.0-rc.112`.
- Source: `/home/theo/Code/sandbox/ts-rust/target/project-inputs/effect/source`.
- Config: `packages/effect/tsconfig.json`.
- Evidence: `/home/theo/Code/sandbox/ts-rust/target/project-inputs/effect/evidence`.

The script copied the complete tracked tree with `git archive`. It checked
all 3,598 files against their pinned Git blob IDs and executable bits before
and after each install. The source contains 38,977,779 bytes. No tracked file
changed, and no file was added outside `node_modules`. The cached checkout
at `~/.explore/repos/Effect-TS__effect` remained clean at the same commit.

The exact config still extends `tsconfig.base.json` and includes `src`.
It retains `types: ["node"]`, strict mode, NodeNext, ES2022, exact optional
properties, erasable syntax, relative import extension rewriting,
`skipLibCheck`, incremental settings, and the Effect plugin configuration.
The script does not set `moduleResolution` or replace any option.

TypeScript 6.0.3 read the config only. It selected the same 457 roots as the
[original inventory](../typechecker-modern-project-inputs.md). Their sorted
path list has SHA-256
`ef2b0b9eed5911a73e1ed0c29a7945687869473b4ee7f6009de658600095ff3b`.
No TypeScript or Go project check ran.

## Install procedure

Run from a ts-rust checkout or worktree:

```sh
node scripts/prepare-effect-project-inputs.mjs
node scripts/prepare-effect-project-inputs.mjs --offline
```

The [preparation script](../../scripts/prepare-effect-project-inputs.mjs)
uses the main checkout's `target/project-inputs/effect` directory, including
when it runs in a linked worktree. It requires Node, npm, Git, tar, a working
systemd user manager, the pinned cached Effect checkout, and the cached
TypeScript 6.0.3 config reader. `EFFECT_REPO_CACHE` and `EFFECT_CONFIG_READER`
can name other existing copies. Neither override changes the output path.

The script bootstraps `pnpm@11.20.0` into `tools/pnpm` when needed. Bootstrap
scripts are disabled. Every install runs in its own systemd user scope with
`MemoryMax=2G` and `MemorySwapMax=0`. The frozen Effect install uses:

```text
--frozen-lockfile --ignore-scripts --ignore-pnpmfile
--no-side-effects-cache --package-import-method=copy
--network-concurrency=8 --child-concurrency=1 --reporter=append-only
```

The store and virtual store paths are explicit. HOME, npm configuration
paths, npm cache, XDG directories, pnpm home, Node compile cache, and temporary
directories are all under `target/project-inputs/effect`. The script clears
the inherited install environment. It sets `PNPM_MAX_WORKERS=2` and a 1 GiB
Node heap limit. The 2 GiB systemd cap applies to the complete install scope.

The first attempt, before the tarball worker limit was added, hit the 2 GiB
cap. The user journal recorded `oom-kill` for
`run-p487541-i21520458.scope`. Its log and command record are retained as
`install.log` and `commands-initial-oom.json`. The retry completed in 58.5
seconds using the existing partial store. That time is not a cold install
benchmark. Both offline replays then completed successfully.

### Path and tool checks

The script checks existing output ancestors and managed directories before
it creates directories. Source directories, input-cache paths, archive
paths, and evidence destinations must not be symlinks. Dependency links may
resolve only inside the source copy. The store permits only
`store/v11/projects/<id>` to link to the source directory. Its ID is the first
32 hexadecimal digits of SHA-256 of the absolute source path, and its canonical
target must equal that source path. All other store links remain rejected.
The four npm-created pnpm launcher
links must resolve to their exact expected files inside the local tool package.
Input-cache overrides must use real paths outside the managed output tree.

Evidence writes use file descriptors opened with `O_NOFOLLOW`. The script
checks that each destination is a regular file with one hard link before
it truncates the file. It checks the layout again before install commands.

Before any pnpm command, the installed package must match every file in the
pinned pnpm tar archive. Version output alone is not sufficient. The archive
must match both the fixed SHA-256 and SHA-512 values. The script can read it
from the isolated npm cache. If it is absent, an online run can fetch it with
`npm pack --ignore-scripts` into the managed tools directory. An offline run
fails if neither archive copy is available. Archive checks use a fresh private
directory under the managed temporary directory.

These checks were added after the recorded preparation. The original source,
installed packages, caches, and evidence were not changed to test this repair.
The recorded install results below are not a new install or compiler run.

### Disposable safety proof

```sh
node --test scripts/prove-effect-input-safety.mjs
```

The proof uses temporary workspaces, fake Git responses, and install-command
stubs. It copies the existing pinned pnpm archive into its fixtures. It never
downloads a package, runs an install or build, or changes the prepared input
tree. Set `EFFECT_TEST_PNPM_ARCHIVE` to another existing copy of that exact
archive if it is not present in the isolated npm cache.

All 35 tests passed. They cover symlinked ancestors, managed directories,
existing and dangling file links, a hard-linked evidence file, source-cache
aliases, reader files, external tool paths, changed pnpm files, and a changed
archive. The positive case accepts the full pinned package and expected
internal links, then stops at the install stub.
The store-link cases cover an existing entry and one created by a successful
install stub. Wrong entry names and different targets remain rejected.

A separate read-only audit confirmed that all 3,598 tracked source files in
both copies, 54,191 installed files, 3,186 links, saved evidence, and the cache
index remained unchanged. The existing 891 pnpm package files also matched
the pinned archive. These checks do not establish compiler parity.

## Hooks and retained files

The root `prepare` hook was not run:

```text
node scripts/setup-agents.mjs && effect-tsgo patch
```

No package lifecycle script, workspace build, compiler patch, or generator
ran. The declared lockfile patch for `@changesets/get-github-info@1.0.0` was
applied by pnpm during the frozen install. This package patch is separate
from the skipped compiler patch. Its input SHA-256 is
`a5b1907668397f36aab989954aa78993792f578b83e41a164ab7ecd573ac9166`.

All 20 generated barrels remain. `K8sTypes.ts`, `httpApiScalar.ts`, and
`httpApiSwagger.ts` remain byte-identical too. Their notices and the root
MIT license are retained. The Scalar and Swagger generators were not run.
`source-inputs.json` records the 23 generated files and key input hashes.
`packages.json` and `workspace.json` list lifecycle hooks found in package
metadata. Listing a hook does not mean it normally runs for a registry
install. All hooks were disabled here.

## Installed inputs

The final inventory has 41 workspace projects, 1,083 physical installed
packages, 54,191 regular installed files, and 3,186 symlinks. No link is
broken or resolves outside the Effect target directory. The installed
regular files contain 1,396,190,229 bytes after the second offline replay.
This count includes pnpm metadata and `.bin` launchers.

`packages/effect/node_modules/@types/node` resolves to `@types/node@26.2.0`.
Its `index.d.ts` exists. Its dependency link resolves to
`undici-types@8.3.0`, whose `index.d.ts` also exists. Their files and links are
in the inventory. This verifies their presence, not compiler selection.

The local Effect export map points to `src`, not generated `dist` files.
No explicit literal workspace declaration target checked by the script is
missing. No declaration build was run.

### Declaration gaps

The package metadata scan finds 12 absent literal targets. It does not run
module resolution or determine whether Effect imports those targets.

| Package | Version | Absent literal target | `.d.ts` for an extensionless target |
| --- | --- | --- | --- |
| `@babel/helper-compilation-targets` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `@babel/helper-skip-transparent-expression-wrappers` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `@babel/helper-string-parser` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `@babel/helper-validator-identifier` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `@babel/helper-validator-option` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `@babel/plugin-syntax-import-attributes` | `7.29.7` | `lib/index.d.ts` | Not applicable |
| `fast-safe-stringify` | `2.1.1` | `index` | Present |
| `mysql2` | `3.23.4` | `typings/mysql/index` | Present |
| `source-map` | `0.5.7` | `source-map` | Absent |
| `source-map` | `0.6.1` | `source-map` | Present |
| `ssh-remote-port-forward` | `1.0.4` | `dist/index` | Present |
| `yargs` | `17.7.3` | `browser.d.ts` | Not applicable |

Four extensionless entries have a same-name `.d.ts` file. They are not
proven missing compiler inputs. The eight other entries need review if
they occur in the actual graph. Do not generate or patch them from this
metadata scan alone.

Nine declaration wildcard targets and 17 installed package `typesVersions`
maps remain unexpanded. `wildcard-declarations.json` and `packages.json`
retain them. `missing-declarations.json` gives each absent literal target
and its full installed package path.

## Evidence and replay

`installed-files.jsonl` records each regular file's path, byte count,
SHA-256, and executable bit. It also records link text and resolved paths.
It scans physical files without following package links. The records are
serialized as one JSON object per line, with a final LF. Other evidence
files use two-space JSON indentation and a final LF.

| Evidence file | SHA-256 after the second offline replay |
| --- | --- |
| `source-after.json` | `71a1d5e221ee0f1bf0850c338cc1859486e95b66893a6a543da9f0853c224795` |
| `source-inputs.json` | `474dc45bf7a1db113778a91a5d97cf724ab1005ff462ff66e2093025f5591932` |
| `installed-files.jsonl` | `8564943794baaf49e387223e939b701fc441a8a0d4c888e117ba36d1f97307b7` |
| `packages.json` | `856e0ea89f49ef8ffa47072af4c3ec36cf9c1e6065867653202178b458decb12` |
| `links.json` | `94d34258337174395438dd9a124882e11ef37dc50c4c806a7809997a5b414c94` |
| `workspace.json` | `3f186453c5a251138dee2f02997a7f267cd10bfcc8e9104e0968b3afd17d1b6c` |
| `config.json` | `7a11b993ca9b1cb2ddd5b708955e85ba1eaf07349a3c9fb1b1978225eee2d1ce` |

Both replays kept source, package metadata, workspace metadata, config,
roots, and symlink records unchanged. The first offline replay rewrote 39
`.bin` launchers plus `node_modules/.modules.yaml` and
`node_modules/.pnpm-workspace-state-v1.json`. No other installed entry
changed. `offline-first-changes.json` records the before and after hashes.

The second replay changed only those two pnpm state files.
`replay-files-534526.json` records them. The installed-file inventory digest
therefore changed on both replays. No whole-directory determinism claim is
made. The script preserves all these entries in its inventory.

`summary.json` records counts and replay comparisons. Per-run command and
log files record the install flags and exit status. Evidence is local and
ignored by Git. The two committed files are this report and the preparation
script, not a dependency archive or manifest.

### Tool profile

The run used Linux x64, kernel `7.0.12-1-cachyos`, Node `v24.13.0`, npm
`11.6.2`, and pnpm `11.20.0`. The CPU reports
`AMD RYZEN AI MAX+ PRO 395 w/ Radeon 8060S`. `tools.json` records real paths,
runtime versions, the install environment, and pnpm's bootstrap lock entry.

| Tool file | SHA-256 |
| --- | --- |
| Node binary | `53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc` |
| npm `bin/npm-cli.js` | `8e5f6f3429f8cdbe693cdc29904e9d5a7b127a494bd15c804bd54c7403bfcbe7` |
| pnpm `bin/pnpm.mjs` | `ff3224d46b47fbb24a7e9fe15fededef7e00892d07d4e376b6762d4899906bfd` |
| pnpm `dist/pnpm.mjs` | `d8cac00e9c4f7f02f80dd173cfe9bf70c3a90830f4979842ea5b4753641186f7` |
| pnpm 11.20.0 archive | `34e198cb1e43237517ecedfd31f9ae26a6c0a3e5366ce58a2d05f4b21fb5f19a` |
| TypeScript config reader | `569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39` |

The Effect lockfile SHA-256 remains
`ba61b11c32ecab574cf5336d380bf7fe71a182ea01e198a117249c8d19d07423`.
The pnpm workspace file remains
`b779d0bda2a045e54ff3bb349227cf185c94c8d25eee05903e0e98ee92ee7fcc`.
The source snapshot includes every tracked package file, config, lockfile, patch,
license, and committed generator input.

## Remaining work

1. Resolve the complete module graph with the pinned, unpatched Go compiler
   at `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Use that compiler directly,
   never Effect's patched compiler or its `check` script.
2. Record the actual declaration inputs and compiler libraries. Confirm
   config options, roots, links, conditional exports, and `typesVersions`
   selection with Go and Rust. Review the absent targets only if loaded.
3. Produce and hash Go diagnostics, `.types`, and `.symbols`. Record cold
   execution and forced warm replay. No such artifacts exist in this work.
4. Run the Rust comparisons and resource measurements only after the input
   facts are complete. No Rust build or checker change was made here.

Do not create `modern-projects-v1.tsv` from this report or fill its pending
fields with placeholder hashes.
