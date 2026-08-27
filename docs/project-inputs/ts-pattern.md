# ts-pattern input preparation

Recorded on August 26, 2026. The dependency install completed. This preparation
ran no project build, semantic check, emit, Go oracle, or Rust comparison. This
document is not a project parity claim or a complete ring manifest.

## Prepared input

The first prepared input is available at:

```text
/home/theo/Code/sandbox/ts-rust/target/project-inputs/ts-pattern/source
```

Use its unchanged `tsconfig.json`. The directory contains all 101 tracked
upstream files and 654 installed dependency packages. No required lockfile
package is missing. npm omitted 23 optional packages on this Linux x64 host.
The full omitted list is in `evidence/packages.json` and `evidence/preparation.json`.

The output directory is `target/project-inputs/ts-pattern` under the main
ts-rust checkout. It also contains the copied tools, npm cache, temporary files,
source archive, install log, and hash catalogs. The cache checkout and global
toolchain were not changed.

## Pins and config

| Input | Pin |
| --- | --- |
| Repository | `gvergnaud/ts-pattern` |
| Commit | `c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0` |
| Package version | `5.9.0` |
| Config | `tsconfig.json` |
| Lockfile | `package-lock.json`, version 2 |
| Node | `v24.13.0` |
| npm | `11.6.2` |
| Installed TypeScript and config reader | `5.9.2` |
| Git | `2.54.0` |
| GNU tar | `1.35` |
| Host | Linux x64, kernel `7.0.12-1-cachyos`, glibc `2.43` |

The config still has `module: ESNext`, `target: ESNext`, Bundler resolution,
`strict: true`, `declaration: true`, `skipLibCheck: true`, and
`esModuleInterop: true`. Its output directory remains `dist/`. It includes
`src/` and excludes `tests/`, `dist/`, `examples/`, and `node_modules/` exactly
as upstream does. No extra exclusions or option overrides were added.

There is no explicit `types` list. Automatic ambient type packages were kept.
The root installed packages include `@types/jest@30.0.0` and
`@types/node@14.14.10`. Do not replace these with newer versions or omit dev
dependencies when replaying this input.

The locked TypeScript 5.9.2 config reader selected 18 roots. Their path hash
matches the earlier inventory made with TypeScript 6.0.3. The script requested
only the program file list. It did not request diagnostics or run checking or
emit. The reader loaded 367 files:

| File group | Count |
| --- | ---: |
| Project source | 18 |
| TypeScript 5.9.2 library declarations | 86 |
| Other dependency declarations | 263 |
| Total | 367 |

All files in this reader result were inside the prepared source directory.
This is a TypeScript reader result, not proof that Go loads the same graph.
The genuine oracle must use the pinned, unpatched Go compiler and record its
own library and module inputs.

## Install review

No `AGENTS.md` or contribution guide was found in the pinned ts-pattern tree.
The root package, README, config, lockfile, and declaration-generation script
were inspected. The root package has no `preinstall`, `install`, `postinstall`,
or `prepare` hook.

The lockfile marks install scripts for two dependencies:

| Package | Result |
| --- | --- |
| `fsevents@2.3.3` | Optional package, not installed on this host |
| `unrs-resolver@1.11.1` | Installed, but its `napi-postinstall unrs-resolver 1.11.1 check` hook was not run |

The install used `npm ci --ignore-scripts --no-audit --no-fund`, included dev,
optional, and peer dependencies, and kept the hoisted layout. Every resolved
lockfile URL uses the public npm registry. No Git or local-file dependency was
fetched. The installed package records retain any other lifecycle commands
for inspection, but none was run.

Node and the complete npm package were copied into `tools/` under the output
directory and checked against fixed content hashes. The install used those
copies. Its npm cache and temporary directory are local to the output. User
and global npm config were replaced with empty config inputs for the command.
The job ran in a systemd user scope with `MemoryMax=2147483648`, no swap, and a
1536 MiB Node heap limit.

`evidence/npm-ci.log` records exit success and 654 packages added. It also
records upstream deprecation warnings. No dependency update was made to
remove those warnings. Package integrity values remain in the upstream lock
and the installed-package evidence.

## Unavailable outputs

No generated file was identified in the 18 selected source roots. The project
was not built. These package export and bundle outputs remain absent:

```text
dist/index.d.ts
dist/index.d.cts
dist/types/index.d.ts
dist/types/index.d.cts
dist/index.js
dist/index.cjs
dist/index.umd.js
```

None is a selected config root or a file in the recorded reader result. They
are still unavailable for a separate package-consumer check. Upstream's build
runs microbundle and `scripts/generate-cts.sh`. That script also uses the BSD
`sed -i ''` form. It was not changed or run on this Linux host.

The optional package omissions include other platform bindings, WASM fallback
dependencies, and `fsevents`. Native tool operation was not tested after
disabling install hooks. Nested example and benchmark dependencies were not
installed. Those directories are not selected by the root config.

## Evidence

Paths below are relative to `target/project-inputs/ts-pattern` unless they name
an upstream source file. SHA-256 values cover the actual bytes used in the
first preparation.

| File or catalog | SHA-256 |
| --- | --- |
| `source.tar` | `fa93f30524ecbf5210281b9d57369aef3c8636c7cdf66951a60169b9964fc0cb` |
| `evidence/source-files.jsonl` | `33859391449e2f7f6ab1cfbf683b2d4f0ac03f4cc8e8a9d16a6efcc3d3260433` |
| `source/package-lock.json` | `53320f9e75f27f93be5161f5c968983597f0b41ca39a90c034afc5e8d20220c6` |
| `source/package.json` | `41f2ebe4021d50fb3ce870a18c7228304e855041d6c96b5c93e1919de9645ff5` |
| `source/tsconfig.json` | `b53aa621db1475ecd4316db408f54cb41bb43d9bc737561f00985de4f4ff3c05` |
| `evidence/roots.files` | `7ed182ee60381824081ffd18a0db0853bc62ea9ffd9a17b00e82987e5e6f0506` |
| `evidence/dependency-files.jsonl` | `38a9fbb4b2149359e46a0b62cfba67fd81e53d6c3b81f90392166a57ca4a11b4` |
| `evidence/typescript-reader-inputs.jsonl` | `656e8054388ed87542c2d2d48cfc9756aefe10fab546245eb97041d6e02f1a28` |
| Copied Node executable | `53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc` |
| Copied npm content catalog | `2317d7658fc5d46d52941ee78964ba579ed1736bb664c50175feabdd13a32231` |
| Installed `typescript/lib/typescript.js` | `e5f1f6b3e82228a89873cc7b941b2465185e839c0692860f83e3e63e53f94c2b` |

The source catalog records Git mode, Git blob ID, byte count, and SHA-256 for
every tracked file. Every copied blob was checked against the pinned Git
tree before and after installation. The dependency catalog has 12,694 entries.
Regular files record byte count and SHA-256. Symlinks record their link text.
Directories and timestamps do not enter those catalogs. Records use relative
paths and one JSON object followed by LF per line.

`evidence/preparation.json` records the complete preparation facts and script
hash. `evidence/install-result.json` records the exact command and exit code.
`evidence/packages.json` records each lock entry, installed version, lifecycle
commands, and optional omission. No Go artifact digest was filled with a
placeholder, and no ring manifest was created.

An independent install at `target/project-inputs/ts-pattern/replay-1/source`
used a new npm cache and produced the same source archive hash. These six
evidence files were byte-identical between the two preparations:

```text
source-files.jsonl
dependency-files.jsonl
roots.files
typescript-reader-inputs.jsonl
packages.json
lock-install-hooks.json
```

Both runs installed 654 packages, omitted the same 23 optional packages,
selected 18 roots, and loaded 367 reader inputs. The preparation profiles
retain their different absolute paths. This replay checks input preparation,
not compiler parity.

## Reproduce

Use `scripts/prepare-ts-pattern-input.mjs` from a ts-rust checkout. The script
requires the clean source-cache pin and the exact Node/npm versions and
content hashes listed above. It copies those tools instead of updating the
global installation. It starts its own 2 GiB scope. Public registry access
requires the usual execution approval.

The default output already exists. Use a new directory below the same input
area to repeat preparation without changing the first copy:

```sh
node scripts/prepare-ts-pattern-input.mjs \
  /home/theo/Code/sandbox/ts-rust/target/project-inputs/ts-pattern/replay-new
```

The script refuses output outside that input area and refuses to replace an
existing source or tool copy. It never changes ts-rust checker or runner code.
Go graph validation, exact oracle artifacts, Rust comparison, compiler
cold/warm replay, and performance measurements remain separate pending work.

## Output path repair

The two installs above used the script in `7eebbdb1`. Review then found that
lexical path checks did not reject symlinked ancestors or managed paths.
Evidence files and `empty.npmrc` could also follow links when opened for
writing. The prepared inputs themselves had no such paths and their recorded
bytes were valid.

The repaired script checks the nearest existing ancestor before its first
directory creation. It rejects symlinked ancestors, managed directory links,
broken links, shared files, wrong path kinds, and overlap with the read-only
source cache. It checks nested temporary, npm-cache, and evidence entries too.
Source and tool copies must remain absent before creation.

Every direct output file write now checks its destination. File descriptors
use `O_NOFOLLOW`, and the script checks the file kind and link count before
truncation. Archives, tool copies, log files, and package-manager output paths
are also checked before the operation that can write them. Optional Git index
writes are disabled during source inspection.

Disposable tests rejected 33 unsafe cases before any write. Two safe controls
reached a stubbed memory-scope command. These tests ran no install, build, or
generator and used no real cache paths.

Read-only verification after the repair checked both existing prepared copies,
all 101 source files and 12,694 dependency entries per copy, and all six replay
evidence files. The hashes above remain unchanged. No prepared input or
preparation profile was rewritten. The profiles correctly retain the original
preparation script hash rather than claiming that the repair performed those
installs.
