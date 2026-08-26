# Modern project input inventory

Recorded on August 26, 2026. This is an input inventory, not a passing ring or
a complete manifest. All seven cached repositories were clean at the commits
below. No dependency install, project build, source patch, or compiler parity
run was done for this inventory.

The proposed core has five repositories and 224,500 non-generated TypeScript
code lines. This count excludes tests, declaration files, comments, and blank
lines. The configs still include every file selected by their upstream rules.
The ecosystem adds a NodeNext package consumer, React/TSX, and checked
JavaScript with JSDoc.

`tools/ts_fixture/manifests/modern-projects-v1.tsv` remains absent. Its required
Go artifact digests and complete dependency input facts are pending. Do not
turn the tables below into a ready manifest by filling those fields with
zeroes or placeholder hashes. Review this selection before freezing it.

## Repository pins

All repository URLs use `https://github.com/` followed by the owner and name
below. The replay script uses the existing `~/.explore/repos` cache.

| Entry | Repository | Commit | Package manager |
| --- | --- | --- | --- |
| Zod | `colinhacks/zod` | `43f729db4aa0cedff6d6b3261f33f8556b3c7102` | `pnpm@10.12.1` |
| ts-pattern | `gvergnaud/ts-pattern` | `c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0` | npm, version not pinned |
| TanStack Query | `TanStack/query` | `44645e9eb1dafba5f2f229adb328582075484f36` | `pnpm@11.9.0` |
| Hono | `honojs/hono` | `06880c4a2b04de9dd74217f26dd831209b9c01f1` | `bun@1.2.20` |
| Effect | `Effect-TS/effect` | `0d083ba26b2e1afec8d3e8d83db0d05683b6602b` | `pnpm@11.20.0` |
| React Hook Form | `react-hook-form/react-hook-form` | `bb3360f4db62489ed4ab4e09ccb4211a275da707` | `pnpm@11.7.0`, pinned in the CI install action |
| Svelte | `sveltejs/svelte` | `4d5139552dac8593c5e020846fa7ce8e96ea97b7` | `pnpm@10.33.4`, with a SHA-512 suffix in `package.json` |

Each repository has an MIT root license. The license file is `LICENSE`, except
for Svelte's `LICENSE.md`. Effect's
`packages/effect/src/unstable/cluster/K8sTypes.ts` has an Apache-2.0 notice for
generated Kubernetes declarations. Effect also commits bundled Scalar and
Swagger payloads. Their notices remain part of the pinned source and need to
be retained in any copied input archive. The root license is not a claim that
every embedded dependency has only that license.

The instruction review covered Zod's `AGENTS.md`, TanStack Query's `AGENTS.md`
and `CONTRIBUTING.md`, Hono's `docs/CONTRIBUTING.md`, React Hook Form's
`CONTRIBUTING.md`, Effect's `.agents/AGENTS.md`, and Svelte's `AGENTS.md` and
`CONTRIBUTING.md`. No `AGENTS.md` or contribution guide was found for ts-pattern.

## Lockfile digests

These SHA-256 digests cover the exact file bytes. They do not prove that the
resolved packages, workspace links, or generated declarations are available.
None of the seven cache roots had a `node_modules` directory.

| Repository | Lockfile | SHA-256 |
| --- | --- | --- |
| Zod | `pnpm-lock.yaml` | `03627f8232469285ad0ae0199f749bf5471f71e4d78f709cb74ad63bbf87bbc3` |
| ts-pattern | `package-lock.json`, lockfile version 2 | `53320f9e75f27f93be5161f5c968983597f0b41ca39a90c034afc5e8d20220c6` |
| TanStack Query | `pnpm-lock.yaml` | `dabc851b54103afd7fb67d00d07663d554c89393c2ffde5254ca539f84d81e71` |
| Hono | `bun.lock` | `910eec46012b95777558e1a8b568e63cf48c7167d12e7deaa60382d474fcdfff` |
| Effect | `pnpm-lock.yaml` | `ba61b11c32ecab574cf5336d380bf7fe71a182ea01e198a117249c8d19d07423` |
| React Hook Form | `pnpm-lock.yaml` | `7acb3dc72842c76da85d5a9dd0e8c589c18250c2b2e46b0dbe4948798df0d14a` |
| React Hook Form app | `app/pnpm-lock.yaml` | `5c31f94a9ae847852866bafbac415bcc68273c678334c3b2fe9277800cce57ea` |
| Svelte | `pnpm-lock.yaml` | `67218d513a065e0519a5c032e7b930c50d237af7fc445b3c6ba13b430aa58c59` |

## Config roots

Every listed config resolves to `strict: true`. Paths are relative to the
repository root. TypeScript 6.0.3's config reader selected the root files.
This reader was already cached. It was not installed or used to typecheck the
projects. Root lists are not full module graphs or Go oracle results.

| Ring | Entry | Exact config | Root files | Module / resolution |
| --- | --- | --- | ---: | --- |
| Core | Zod | `packages/zod/tsconfig.json` | 321 | NodeNext / NodeNext |
| Core | ts-pattern | `tsconfig.json` | 18 | ESNext / Bundler |
| Core | Query core | `packages/query-core/tsconfig.prod.json` | 23 | ESNext / Bundler |
| Core | Query persistence | `packages/query-persist-client-core/tsconfig.prod.json` | 4 | ESNext / Bundler |
| Core | Query sync storage | `packages/query-sync-storage-persister/tsconfig.prod.json` | 2 | ESNext / Bundler |
| Core | Query async storage | `packages/query-async-storage-persister/tsconfig.prod.json` | 3 | ESNext / Bundler |
| Core | Query broadcast | `packages/query-broadcast-client-experimental/tsconfig.prod.json` | 1 | ESNext / Bundler |
| Core | Hono | `tsconfig.build.json` | 188 | ES2020 / Bundler |
| Core | Effect | `packages/effect/tsconfig.json` | 457 | NodeNext / default |
| Ecosystem | Query NodeNext consumer | `integrations/react-nodenext/tsconfig.json` | 2 | NodeNext / NodeNext |
| Ecosystem | React Hook Form | `tsconfig.json` | 109 | ES2015 / Bundler |
| Ecosystem | React Hook Form app | `app/tsconfig.json` | 45 | ESNext / Node |
| Ecosystem | Svelte runtime | `packages/svelte/tsconfig.runtime.json` | 160 | ESNext / Bundler |
| Ecosystem | Svelte compiler and tests | `packages/svelte/tsconfig.json` | 3,233 | ESNext / Bundler |

The root-list SHA-256 values below use the serialization in the replay section.
These hashes cover paths, not dependency graphs or compiler artifacts.

| Config entry | Root-list SHA-256 |
| --- | --- |
| Zod | `0433cde05204a2323ca8f6626dd92c302b16d6cca7f511e13fb95f449573f54f` |
| ts-pattern | `7ed182ee60381824081ffd18a0db0853bc62ea9ffd9a17b00e82987e5e6f0506` |
| Query core | `0e4ba739fe52b0847accf3368ffabde25f9afdb6cb1b5a4a4ec681a70c6dbb06` |
| Query persistence | `0c0ad8ffff35c95e8c6bd29d860f9a3f51d17a0cf01dae90f5867b1263cbc140` |
| Query sync storage | `130383e8682ec769f6e036d47c998ffbd8c4ef3455ad61c63152dab89040ed4f` |
| Query async storage | `091e33d70eda7340fb5bdd7dc84cca09545aa6c38843c6ec5b4bde8861f7f64e` |
| Query broadcast | `8fd34f3b074d10b3e9f1aae8ac20d6534c39116b1593b6bfa626aa2d1ca8442a` |
| Hono | `4014df7bbea8c85b02685c887d1ac55ab00d96c7987775a02943e91e4360fb12` |
| Effect | `ef2b0b9eed5911a73e1ed0c29a7945687869473b4ee7f6009de658600095ff3b` |
| Query NodeNext consumer | `bd737bcff9461a3ce63b470c8897f3f473a3758cf6a802d8514df5265eeea541` |
| React Hook Form | `7963c7ea867f902a71da242554466828fc169034c75c66920cd6d2c41378bae0` |
| React Hook Form app | `af71e8cab3b67cb538d918b5828317f1e16bc5bdfbb75e71585bf590c452c203` |
| Svelte runtime | `27004d241717123c9e1b65303627443cc81dda1b7ea24d78ec2847ba0817f18b` |
| Svelte compiler and tests | `abe26182af676fac1d42e3fe5e022b9ac0542b0dd9ee932d876415b9568b26ed` |

- Zod extends `.configs/tsconfig.base.json`. Its package config includes
  `**/*.ts`, including 189 test files, and uses `@zod/source` plus the `vitest`
  and `recheck` type packages. Do not replace it with a source-only config.
- ts-pattern includes `src/` and excludes `tests/`, `dist/`, `examples/`, and
  `node_modules/` in its own config. The inventory adds no exclusions.
- Each Query production config extends its package `tsconfig.json`, which
  extends the root config. The production config includes `src` and excludes
  `src/__tests__`. It retains `@tanstack/custom-condition` and `types: [node]`.
  Project references from the package config are not inherited. Workspace
  imports still need resolution. The broadcast package imports
  `broadcast-channel`, which provides external declaration input to verify.
- Hono extends `tsconfig.base.json`. Its build config includes `src/**/*.ts`
  and `src/**/*.mts` and excludes upstream test patterns. Its roots include
  `src/adapter/deno/deno.d.ts`. Hono is one package here. The Query entries
  provide the proposed multi-package Bundler graph.
- Effect extends `tsconfig.base.json` and includes `src`. It retains
  `types: [node]`, `exactOptionalPropertyTypes`, `erasableSyntaxOnly`, and
  `rewriteRelativeImportExtensions`. Module resolution is not explicitly set.
  Its `prepare` script patches a compiler through `effect-tsgo`. A later
  oracle run must use the pinned unpatched Go compiler directly.
- The Query NodeNext config is independent of the root config. It has no
  source custom condition and consumes `@tanstack/react-query`. Its package
  expects dependency builds. The checked-in package export map points to
  `build/modern` declarations that are not available from a bare checkout.
- Both React Hook Form configs use `jsx: react`. The root config excludes
  upstream test directories and declares Jest, Node, and testing-library
  types. The app uses `vite/client`, its own lockfile, and `react-hook-form`
  through `file:..`. Some app files also import the library's source directly.
- Both Svelte configs use `allowJs: true` and `checkJs: true`. The runtime
  config extends the main config, includes `src`, and excludes compiler and
  test files. The main config includes source, scripts, test drivers, and
  sample `_config.js` files. It excludes upstream message templates,
  `scripts/_bundle.js`, and `src/compiler/optimizer/`. Runtime roots are a
  subset of main roots, so their counts must not be added twice.

## Measured size

Counts use cloc 2.08 with `--skip-uniqueness`. Each selected path counts once
within its repository entry, even if several configs include it. The core
threshold below uses only non-generated, non-test `.ts`, `.mts`, and `.cts`
code lines. Declaration files, TSX, JS, comments, and blank lines do not add
to the threshold.

| Core repository | Counted files | TypeScript code lines |
| --- | ---: | ---: |
| Zod | 132 | 29,471 |
| ts-pattern | 18 | 2,575 |
| TanStack Query | 33 | 6,547 |
| Hono | 187 | 19,198 |
| Effect | 434 | 166,709 |
| Total | 804 | 224,500 |

Without Effect, the four core candidates have only 57,791 source code lines.
Even adding Zod's 37,050 test code lines yields only 94,841. Those four entries
alone do not meet the 100,000-line gate under this measure.

React Hook Form contributes 104 `.ts` files with 6,132 code lines and 50 TSX
files with 4,953 code lines. The Query NodeNext consumer adds two `.ts` files
with 16 code lines. Svelte's deduplicated roots contain 367 non-test JavaScript
files with 41,444 code lines, one non-test `.ts` file with 573 code lines,
and 36 declaration files with 2,063 code lines. Its test roots add 33 `.ts`
files with 5,381 code lines and 2,787 JavaScript files with 55,016 code lines.
These ecosystem numbers do not increase the core total.

## Generated source

Generated files stay in the root lists and future compiler inputs. The
following files are excluded only from size measurement.

- Effect has 20 `index.ts` files marked
  `@barrel: Auto-generated exports.`. `packages/tools/utils/src/Codegen.ts`
  rewrites these exports. Excluding the whole file also excludes any hand
  written header, which makes the size count conservative.
- Effect's `packages/effect/src/unstable/cluster/K8sTypes.ts` says that it
  incorporates generated `kubernetes-types` declarations. Excluding it removes
  805 code lines that the first temporary inventory counted.
- Effect's `packages/effect/src/unstable/httpapi/internal/httpApiScalar.ts`
  and `httpApiSwagger.ts` are bundled payloads written by
  `scripts/package-scalar.mjs` and `scripts/package-swagger.mjs`. Those scripts
  fetch unpinned remote inputs. Do not rerun them to construct the oracle
  input. Use the committed bytes.
- Svelte has eight generated error and warning files under `src/compiler`
  and `src/internal/{client,server,shared}`. Their header names
  `scripts/process-messages/index.js`. `src/version.js` is generated during
  release. These nine files are excluded from size measurement. The runtime
  subset contains seven of them.
- Svelte's `types/index.d.ts` and compatibility declaration wrappers are
  generated by `scripts/generate-types.js`. They are outside the selected
  root lists. If imports load them later, they must stay in the full input
  graph and remain outside the non-generated size count.

No generated source was identified in the other selected roots. Marker
searches were checked against the source and generation scripts. Comments
about generated values do not make their containing source files generated.

## Missing evidence

The upstream compiler pin remains
`microsoft/typescript-go@dc37b5249ab60e2bbce936f71b883e6c8136167e` from
`UPSTREAM.md`. No per-project Go diagnostics, `.types`, or `.symbols` artifact
has been produced here. Every such digest is pending.

Before creating a complete manifest and running either ring:

1. Review and freeze this selection. Pin the npm version for ts-pattern and
   the full machine and toolchain profile.
2. Prepare dependencies from the pinned lockfiles without source patches.
   Record package content, workspace links, declaration output, and library
   inputs. Query's NodeNext consumer and the React Hook Form app need their
   normal local dependency output. Review install hooks first, especially
   Effect's compiler patch.
3. Verify the same config options, source files, libraries, and module graph
   in Rust and the pinned Go compiler. Config parsing by TypeScript 6.0.3 is
   not this proof. Core `.d.ts` consumption across the proposed Bundler graph
   also remains pending.
4. Produce and hash exact Go diagnostics, `.types`, and `.symbols`. Record
   cold execution and forced warm replay for two deterministic runs.
5. Run the Rust comparisons without unsupported results, skips, fallback,
   mismatches, or fatal results. Record release wall time and peak RSS against
   Go on the same machine. No performance result is claimed here.

## Reproduce the inventory

The script below reads cached source and writes only under `INVENTORY_OUT`.
It neither installs dependencies nor builds a project. It fails on dirty
checkouts, a changed commit, config errors, non-strict configs, or an untracked
root file. It uses TypeScript's config reader rather than a separate glob
implementation.

The first run and a replay of this document's script produced byte-identical
`inventory.json` files. Their SHA-256 is
`8efa4241dbd49de8e0788add7bf4f3bf5291387cf74adad71c04a6d29803b1f3`.
This validates the inventory procedure, not compiler parity.

The measured tool files have these SHA-256 digests:

- TypeScript 6.0.3 `lib/typescript.js`:
  `569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39`.
- cloc 2.08:
  `0a551a86c7785880bcaa0fdfe6107c064abfbebc7cc26b7eaeac423fe2c0d49e`.

Set `TYPESCRIPT_JS`, `CLOC`, and `REPO_CACHE` to existing local paths if they
differ. Run this from the ts-rust repository root. It prints the summary and
writes `inventory.json` plus sorted root lists in `/tmp`. Root-list SHA-256
uses one repository-relative UTF-8 path followed by LF per file, including
the final file. Generated files are present in these digests.

```sh
awk '/^```javascript$/{p=1; next} p && /^```$/{exit} p' \
  docs/typechecker-modern-project-inputs.md | node --input-type=module
```

```javascript
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { createRequire } from 'node:module';

const cache = process.env.REPO_CACHE ?? '/home/theo/.explore/repos';
const output = process.env.INVENTORY_OUT ?? '/tmp/wave127-modern-input-audit';
const tsPath = process.env.TYPESCRIPT_JS ?? '/home/theo/.bun/install/cache/typescript@6.0.3@@@1/lib/typescript.js';
const clocPath = process.env.CLOC ?? '/home/theo/.local/bin/cloc';
const ts = createRequire(import.meta.url)(tsPath);
const hash = (data) => createHash('sha256').update(data).digest('hex');
const projects = [
  { id: 'zod', directory: 'colinhacks__zod', sha: '43f729db4aa0cedff6d6b3261f33f8556b3c7102', locks: ['pnpm-lock.yaml'], configs: ['packages/zod/tsconfig.json'] },
  { id: 'ts-pattern', directory: 'gvergnaud__ts-pattern', sha: 'c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0', locks: ['package-lock.json'], configs: ['tsconfig.json'] },
  { id: 'query', directory: 'TanStack__query', sha: '44645e9eb1dafba5f2f229adb328582075484f36', locks: ['pnpm-lock.yaml'], configs: ['packages/query-core/tsconfig.prod.json', 'packages/query-persist-client-core/tsconfig.prod.json', 'packages/query-sync-storage-persister/tsconfig.prod.json', 'packages/query-async-storage-persister/tsconfig.prod.json', 'packages/query-broadcast-client-experimental/tsconfig.prod.json'] },
  { id: 'hono', directory: 'honojs__hono', sha: '06880c4a2b04de9dd74217f26dd831209b9c01f1', locks: ['bun.lock'], configs: ['tsconfig.build.json'] },
  { id: 'effect', directory: 'Effect-TS__effect', sha: '0d083ba26b2e1afec8d3e8d83db0d05683b6602b', locks: ['pnpm-lock.yaml'], configs: ['packages/effect/tsconfig.json'] },
  { id: 'query-nodenext', directory: 'TanStack__query', sha: '44645e9eb1dafba5f2f229adb328582075484f36', locks: ['pnpm-lock.yaml'], configs: ['integrations/react-nodenext/tsconfig.json'] },
  { id: 'react-hook-form', directory: 'react-hook-form__react-hook-form', sha: 'bb3360f4db62489ed4ab4e09ccb4211a275da707', locks: ['pnpm-lock.yaml', 'app/pnpm-lock.yaml'], configs: ['tsconfig.json', 'app/tsconfig.json'] },
  { id: 'svelte', directory: 'sveltejs__svelte', sha: '4d5139552dac8593c5e020846fa7ce8e96ea97b7', locks: ['pnpm-lock.yaml'], configs: ['packages/svelte/tsconfig.runtime.json', 'packages/svelte/tsconfig.json'] },
];

function run(command, args) {
  return execFileSync(command, args, { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 }).trim();
}

function sourceKind(filename) {
  if (/\.d\.[cm]?ts$/.test(filename)) return 'declaration';
  if (/\.tsx$/.test(filename)) return 'tsx';
  if (/\.[cm]?ts$/.test(filename)) return 'ts';
  if (/\.[cm]?jsx?$/.test(filename)) return 'js';
  throw new Error(`Unexpected source kind: ${filename}`);
}

function testFile(filename) {
  return /(^|\/)(__tests__|tests|test|__typetest__|__fixtures__|fixtures)(\/|$)|\.(test|spec|test-d)\.[cm]?[jt]sx?$/.test(filename);
}

function generated(id, filename, text) {
  if (id === 'effect') {
    return text.includes('@barrel: Auto-generated exports.')
      || filename === 'packages/effect/src/unstable/cluster/K8sTypes.ts'
      || /\/httpApi(Scalar|Swagger)\.ts$/.test(filename);
  }
  if (id === 'svelte') {
    return filename === 'packages/svelte/src/version.js'
      || text.startsWith('/* This file is generated by scripts/process-messages/index.js. Do not edit! */');
  }
  return false;
}

function countGroups(files, counts) {
  const result = {};
  for (const filename of files) {
    const key = `${sourceKind(filename)}_${testFile(filename) ? 'test' : 'source'}`;
    const group = result[key] ??= { files: 0, code: 0, comments: 0, blank: 0, physical: 0 };
    group.files++;
    for (const field of ['code', 'comments', 'blank', 'physical']) group[field] += counts[filename][field];
  }
  return result;
}

mkdirSync(output, { recursive: true });
const result = [];
for (const project of projects) {
  const root = path.join(cache, project.directory);
  const git = (...args) => run('git', ['-C', root, ...args]);
  if (git('rev-parse', 'HEAD') !== project.sha || git('status', '--porcelain=v1', '--untracked-files=all')) {
    throw new Error(`Unpinned or dirty checkout: ${project.id}`);
  }
  const tracked = new Set(git('ls-tree', '-r', '--name-only', '-z', project.sha).split('\0').filter(Boolean));
  const union = new Set();
  const configs = project.configs.map((config) => {
    const filename = path.join(root, config);
    const parsed = ts.getParsedCommandLineOfConfigFile(filename, {}, {
      ...ts.sys,
      onUnRecoverableConfigFileDiagnostic(diagnostic) { throw new Error(ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n')); },
    });
    if (!parsed || parsed.errors.length || parsed.options.strict !== true) {
      throw new Error(`Config did not parse as strict: ${project.id}/${config}: ${parsed?.errors.map((error) => ts.flattenDiagnosticMessageText(error.messageText, '\n')).join('\n')}`);
    }
    const files = parsed.fileNames.map((file) => path.relative(root, file)).sort();
    if (files.some((file) => !tracked.has(file))) throw new Error(`Untracked config root: ${project.id}/${config}`);
    for (const file of files) union.add(file);
    const list = files.join('\n') + '\n';
    writeFileSync(path.join(output, `${project.id}-${config.replaceAll('/', '_')}.files`), list);
    const chain = [...(parsed.options.configFile.extendedSourceFiles ?? []), filename];
    return {
      config,
      chain: chain.map((file) => ({ path: path.relative(root, file), sha256: hash(readFileSync(file)) })),
      rootFiles: files.length,
      rootListSha256: hash(list),
      strict: parsed.options.strict,
      module: ts.ModuleKind[parsed.options.module],
      moduleResolution: parsed.options.moduleResolution === undefined ? 'default' : ts.ModuleResolutionKind[parsed.options.moduleResolution],
      allowJs: parsed.options.allowJs ?? false,
      checkJs: parsed.options.checkJs ?? false,
      types: parsed.options.types ?? null,
      customConditions: parsed.options.customConditions ?? [],
      jsx: parsed.options.jsx === undefined ? null : ts.JsxEmit[parsed.options.jsx],
      references: (parsed.projectReferences ?? []).map((reference) => path.relative(root, reference.path)),
      files,
    };
  });
  const files = [...union].sort();
  const generatedFiles = files.filter((file) => generated(project.id, file, readFileSync(path.join(root, file), 'utf8')));
  const nonGenerated = files.filter((file) => !generatedFiles.includes(file));
  const list = path.join(output, `${project.id}.absolute.files`);
  writeFileSync(list, nonGenerated.map((file) => path.join(root, file)).join('\n') + '\n');
  const measured = JSON.parse(run(clocPath, ['--quiet', '--json', '--by-file', '--skip-uniqueness', `--list-file=${list}`]));
  const counts = {};
  for (const file of nonGenerated) {
    const entry = measured[path.join(root, file)];
    if (!entry) throw new Error(`File not measured: ${project.id}/${file}`);
    const text = readFileSync(path.join(root, file), 'utf8');
    counts[file] = { code: entry.code, comments: entry.comment, blank: entry.blank, physical: text.split('\n').length - Number(text.endsWith('\n')) };
  }
  for (const config of configs) {
    config.groups = countGroups(config.files.filter((file) => !generatedFiles.includes(file)), counts);
    config.generatedFiles = config.files.filter((file) => generatedFiles.includes(file));
    delete config.files;
  }
  result.push({
    ...project,
    locks: project.locks.map((file) => ({ path: file, sha256: hash(readFileSync(path.join(root, file))) })),
    configs,
    groups: countGroups(nonGenerated, counts),
    generatedFiles,
    unionRootListSha256: hash(files.join('\n') + '\n'),
  });
}
const report = {
  typescript: { version: ts.version, sha256: hash(readFileSync(tsPath)) },
  cloc: { version: run(clocPath, ['--version']), sha256: hash(readFileSync(clocPath)) },
  projects: result,
};
writeFileSync(path.join(output, 'inventory.json'), JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(result.map(({ id, groups, configs }) => ({ id, groups, configs: configs.map(({ config, rootFiles, rootListSha256 }) => ({ config, rootFiles, rootListSha256 })) })), null, 2));
```
