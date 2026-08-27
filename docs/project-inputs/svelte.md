# Svelte input preparation

Recorded on August 26, 2026. Dependencies and normal declaration wrappers are
prepared. This is not a compiler parity result or a passing project ring.

## Source and paths

- Repository: `sveltejs/svelte`.
- Commit: `4d5139552dac8593c5e020846fa7ce8e96ea97b7`.
- Tree: `a44d2a7d2c7f405d6f4291fe8467dd53604a0686`.
- Input directory: `/home/theo/Code/sandbox/ts-rust/target/project-inputs/svelte`.
- Prepared repository: `source/` inside the input directory.
- Logs and manifests: `evidence/` inside the input directory.
- Replay script: `scripts/prepare-svelte-input.mjs`.

The preparation read the cached repository's `AGENTS.md`, `CONTRIBUTING.md`,
package files, install hooks, generation code, and CI commands. It used a Git
archive of the exact commit. The cache stayed clean. All 9,148 tracked files
retain their original Git blob IDs and executable modes after installation
and generation. The root `LICENSE.md` and dependency license files remain in
the prepared copy.

All new package-manager files, package stores, caches, temporary files, and
generated output are inside the input directory. Existing Node and Corepack
binaries were used without changes. No global package install ran.

## Tools and limits

The host is Linux x64, kernel `7.0.12-1-cachyos`. Each prep command ran in a
systemd scope with `MemoryMax=2G` and `MemorySwapMax=0`. Node's heap limit was
1,536 MiB. The measured scope limits are in `evidence/input.json`.

| Tool | Version | SHA-256 |
| --- | --- | --- |
| Node binary | `24.13.0` | `53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc` |
| Corepack implementation | `0.34.5` | `b0cc9feb926d91df5d3e3fa2f0e18942b21e372d743335855c6232bb31df28b1` |
| pnpm implementation | `10.33.4` | `01de269448a00027a1b3daade2cba3c53fd436b2496ebb7be04fae3f6c6b6dae` |
| TypeScript `lib/typescript.js` | `5.5.4` | `f7ff3e27aafe5dcc82d0307575e9a7dc5b053b141da123bec81c858537765b56` |
| dts-buddy entry point | `0.5.5` | `053a3e9b7cf093203508f2d210827948a9c274d449a21d6d7135347ba42a432f` |

Corepack used the complete upstream `packageManager` value and retained the
same verified hash in its local `.corepack` record:

```text
pnpm@10.33.4+sha512.1c67b3b359b2d408119ba1ed289f34b8fc3c6873412bec6fd264fbdc82489e510fcbecb9ce9d22dae7f3b76269d8441046014bdca53b9979cd7a561ad631b800
```

The first Corepack download failed because Node selected unreachable IPv6
addresses. The successful run used `--dns-result-order=ipv4first`. No package
version, registry, lockfile, or source file was changed to resolve that failure.

## Configs

| Input | Exact upstream config | Root files | Files loaded by TypeScript 5.5.4 |
| --- | --- | ---: | ---: |
| Runtime | `packages/svelte/tsconfig.runtime.json` | 160 | 216 |
| Compiler and tests | `packages/svelte/tsconfig.json` | 3,233 | 3,538 |

Both configs retain `strict`, `allowJs`, and `checkJs`. Both use ESNext modules
and Bundler resolution. The runtime config still extends the compiler config
and uses its own ES2021 libraries and empty automatic `types` list. No config
option, path mapping, include, exclusion, or test root was changed.

The root lists match `docs/typechecker-modern-project-inputs.md`, including
the compiler test drivers and sample `_config.js` files. The loaded-file lists
come from TypeScript source loading, not from Go or Rust. They do not prove
matching module graphs or successful typechecking.

## Install and generation

The full three-project workspace was installed with the frozen lockfile,
development and optional dependencies included, and lifecycle scripts disabled.
The command used one child worker and eight network workers. Pnpm reported
424 installed package entries. It omitted 105 incompatible platform packages
under its normal platform rules. These are not compiler input exclusions.

Pnpm's pending build list is unchanged:

- `playgrounds/sandbox`, whose prepare hook writes a playground component.
- `esbuild@0.28.1`, whose postinstall hook runs `node install.js`.
- `esbuild@0.27.7`, whose postinstall hook runs `node install.js`.

`dependency-lifecycle-scripts.json` records 43 dependency manifests with
lifecycle scripts. Most contain package-development `prepare` scripts that
do not normally run for registry tarballs. The two esbuild packages have the
actual dependency install hooks. None of these scripts ran.

The only generation command was the pinned local
`node scripts/generate-types.js` from `packages/svelte`. It uses the installed
dts-buddy and TypeScript versions above. The replay script checks the source
generator and its reviewed implementation files before execution.

The generator ran twice and produced the same 13 outputs both times:

- Nine package-root wrappers: `action.d.ts`, `animate.d.ts`, `compiler.d.ts`,
  `easing.d.ts`, `index.d.ts`, `legacy.d.ts`, `motion.d.ts`, `store.d.ts`, and
  `transition.d.ts`. Each imports `./types/index.js` and has SHA-256
  `31181cc10bdc79c0e0a9a618de33d3e59f2626ed3f30a60537023906373802c5`.
- Two compatibility wrappers: `types/compiler/interfaces.d.ts` and
  `types/compiler/preprocess.d.ts`. Each imports `../index.js` and has SHA-256
  `e873776e929f9ceecb85f4f3fabefa870a9b954f08300c4acb61d12f8b8b67ac`.
- The already committed `types/index.d.ts`, unchanged at SHA-256
  `c5ebf1cf930d83e04791a7354e01ef488adfd8d098ea937946d170cbea94c48d`.
- `types/index.d.ts.map`, SHA-256
  `3099650dcf4a007122101d367024385a54dcb6b494e7b67754cf2cb39e0e7a35`.

These wrappers are normal package output for other module-resolution modes.
Neither selected Bundler config loaded a generated wrapper or the bundled
`types/index.d.ts` in this source-loading run. Their upstream source paths
remain the checked input. No message, version, browser-support, CommonJS
compiler bundle, or browser executable was generated. The full build and
runtime tests did not run.

## Evidence

`prepared-files.json` records 18,871 regular files and 1,093 symlinks, including
their content hashes or link targets. Every link resolves inside the prepared
copy. Seven links resolve to `packages/svelte`, including the root and
playground workspace links and five dependency peer links. The license manifest
records 386 retained license, notice, or copying files.

| Evidence | SHA-256 |
| --- | --- |
| `pnpm-lock.yaml` | `67218d513a065e0519a5c032e7b930c50d237af7fc445b3c6ba13b430aa58c59` |
| `source.tar` | `8f2ee17264d885029e1cce6e5d6243f67e02945f1f8ffb8987a626d9f55fff42` |
| `evidence/source-files.json` | `366f96bf46099b4cb4dad5599e2b8d4126f9b6e7e2520ff5f307fce46042f7b5` |
| `evidence/prepared-files.json` | `4a47289db4313d9584243f4ef28f1158a08af204c3b5446d0f0077e6b439e4b1` |
| `evidence/generation.json` | `9345d828dbf26b7ad703ccc73525dd7c4555ea097180ee7e9e990fdb35ddb8f2` |
| `evidence/workspace-links.json` | `8df2b4aa71b9efe437e960a946c8572660d63e315b738cb1fc4408254705f906` |
| `evidence/license-files.json` | `1b4bcea68337476e9f380462da18d8bc7cedb247132bec06650a4127c936b432` |
| `evidence/input.json` | `3fbd9eae52ba6421a593f56268b259d2d2fe21b048787f5d8a236b64d93d4ef9` |

The runtime root-list hash is
`27004d241717123c9e1b65303627443cc81dda1b7ea24d78ec2847ba0817f18b`.
The compiler/test root-list hash is
`abe26182af676fac1d42e3fe5e022b9ac0542b0dd9ee932d876415b9568b26ed`.

The whole prepared-file manifest includes pnpm metadata with absolute paths
and install timestamps. Its digest identifies this local snapshot. It is not
a claim that separate installs produce byte-identical package-manager metadata.

## Validation repairs

The repaired script has SHA-256
`af1630c5af779dea6e0c83f4a8d7f9e1870e282b2af7a51fdc610fc21c1d31f2`.
It checks canonical output ancestors, managed directories, and file destinations
before creating directories or writing files. The output cannot overlap the
read-only cache. A source-directory link to the cache is rejected for every
action, before source verification or an install can start.

Normal pnpm package links are allowed only when their real targets stay inside
the prepared source. The pnpm project marker must resolve to that source.
Managed roots, private-store directories, generated files, and evidence files
cannot redirect writes through symlinks. Shared hard-linked files are rejected.

The `record` action checks the generator identity and hashes all 13 current
outputs against `generation.json` before writing any evidence. It checks the
output hashes again before writing `input.json`. A missing wrapper, changed
source map, or incomplete output list cannot reuse an earlier `exactReplay`
claim.

Thirty rejection tests used disposable fake-cache directories. They covered
output ancestors, managed paths, all four actions with a redirected source,
unsafe package links, shared archives, and stale generated outputs. Each
command failed before a write. The tests did not use the real cache or run an
install. The test runner and results are under
`target/project-inputs/svelte/path-repair-proof`.

A successful `record` run on a disposable copy retained all ten source,
dependency, generation, root-list, loaded-file, workspace-link, license, and
lifecycle inventories byte-for-byte. It ran under the same 2 GiB limit with
Corepack network access disabled. `evidence/original-comparison.json` in the
proof directory records those checks. The original prepared input and evidence
were not changed. No install or generation command was rerun for this repair.

## Replay and remaining work

Run from a ts-rust worktree with this script. The install step needs registry
access. The other steps use local inputs. `SVELTE_REPO` can point to another
clean cache checkout at the same pin. Output stays under the main worktree's
`target/project-inputs/svelte` directory. `SVELTE_INPUT_DIR` can select a child
directory there for an isolated replay. It cannot select an outside path.

```sh
for step in copy install generate record
do
  systemd-run --user --scope --quiet \
    -p MemoryMax=2G -p MemorySwapMax=0 -- \
    node --max-old-space-size=1536 scripts/prepare-svelte-input.mjs "$step"
done
```

No dependency or declaration-generation blocker remains for the selected
input preparation. Runtime testing would still need its normal browser and
build setup. Before adding a completed project manifest, compare both configs
and complete module graphs in the pinned Go compiler and Rust. Then produce
and hash the Go diagnostics, types, and symbols, and run the required cold and
warm comparisons. No such artifacts or parity result exist from this task.
