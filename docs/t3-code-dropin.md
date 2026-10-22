# tsc-rs as the `typescript` package in T3 Code

T3 Code typechecked with tsc-rs but still installed `typescript` 7.0.2 and `@effect/tsgo` 0.51.1 for
VS Code, and its `prepare` ran `effect-tsgo patch`, which rewrites
`@typescript/typescript-<platform>/lib/tsc`. Under pnpm's global virtual store that file is shared
by every project on the machine. `@tsc-rs/typescript` replaces both packages. Checked on
2026-10-21 against T3 Code main 9179178fd (state notes `e2e-dev21-2026-10-21` and
`final-bench-2026-10-21`).

## The package

`@tsc-rs/typescript` ([npm/typescript-readme.md](../npm/typescript-readme.md)) is Go's `typescript`
package (bin `tsc`, `lib/tsc.js`, Go's `lib/getExePath.js`, `lib/version.cjs`, `dist`, `schemas`,
`vendor`, the same `exports`) with the tsc-rs binary. Its optional dependencies install the
`@tsc-rs/<os>-<arch>` platform packages under the names `@typescript/typescript-<os>-<arch>`. Go's
`getExePath.js` and the VS Code TypeScript 7 extension (`resolveTsdkPathToExe`) both resolve that
name from the package dir, so an install as `"typescript": "npm:@tsc-rs/typescript@<v>"` finds the
binary in the CLI and in VS Code (`js/ts.tsdk.path: node_modules/typescript/lib`, started with
`--lsp --stdio`, version from `package.json`). `require("typescript").version` is the TypeScript
version that `tsc` reports (7.1.0-dev).

## The T3 Code change

- `pnpm-workspace.yaml`: catalog `typescript: npm:@tsc-rs/typescript@<v>`; remove the
  `@effect/tsgo` catalog entry; `allowBuilds` `"@tsc-rs/typescript": true` in place of `tsc-rs`
  (its postinstall makes `tsc` start without Node and writes only its own `bin/tsc`);
  `peerDependencyRules.allowAny` adds `typescript`; `minimumReleaseAgeExclude` drops `tsc-rs`
  (`"@tsc-rs/*"` stays).
- Root `package.json`: `prepare` is `vp config --no-agent` (no `effect-tsgo patch`); remove the
  `@effect/tsgo` and `tsc-rs` devDependencies.
- Typecheck scripts and the vite-plus typecheck tasks: `tsc-rs --noEmit` becomes `tsc --noEmit`.
- Docs (`docs/operations/development.md`, AGENTS.md): `typescript` is the tsc-rs drop-in.
- `.pnpmfile.cjs`: a `readPackage` hook sets vite-plus-core's `typescript` peer range to `*`.
  Without it, pnpm gave the vite-plus that `@effect/vitest` imports apps/marketing's
  `typescript@6.0.3`, and every test job failed with two vitest copies (T3 Code CI on #23023).
- `.vscode/settings.json`: no change.

The npm version (0.8.x) does not satisfy `typescript` peer ranges. pnpm then resolves those peers
(msw, one vite-plus-core copy) to apps/marketing's own `typescript@6.0.3`, and npm stops with
ERESOLVE unless `"overrides": { "typescript": "$typescript" }`. T3 Code aliases `vite` the same way.

Result with a locally packed 0.8.0-dev.21: `vp i` (also with `enableGlobalVirtualStore`: no
lifecycle script writes outside its own package), `vp run typecheck` 32 of 32, `npx tsc --noEmit -p
apps/server` runs the tsc-rs binary with the same output as tsc-rs 0.7.0, knip and lint pass, and
VS Code 1.139.1 with the TypeScript 7 extension starts the tsc-rs server and shows the same 62 Effect
diagnostics as the CLI. A workspace tsdk needs the extension's one-time "Allow", as before.

## Effect editor features

tsc-rs `--lsp` gives the same answers as effect-tsgo 0.51.1 for the Effect diagnostics (CLI output
byte-equal on apps/server and apps/web), quick fixes (the rule fixes and the disable comments),
refactors (all 21, kind `refactor.rewrite.effect.<name>`, listed in `initialize`), completions
(the `Effect.` snippets), hover (the Effect type parameter block, `yield*`, the Layer graph links),
the document symbol tree (Layers, Services, Errors, Schemas), inlay hints and the auto-import style
(`namespaceImportPackages`). The differences come from the TypeScript version (7.0.2 against
7.1.0-dev), not from Effect.

What T3 Code loses: only the parts of the `@effect/tsgo` package outside the language server. The
`effect-tsgo diagnostics`, `setup` and `config` commands, its tsconfig `schema.json` (completion of
the plugin options in tsconfig.json) and its oxlint presets. T3 Code uses none of them.

## Incremental runs

With `incremental: true`, an edit of an exported type made an incremental run slower than a cold
one (apps/server, an edit of `config.ts` with about 200 importers: 1.45x cold on 0.7.0). Go's
`getFilesAffectedBy` emits the d.ts of each importer, one at a time, to see whether the change
spreads, and tsc-rs ported that. Under `noEmit`, Go rechecks the whole closure anyway. tsc-rs now
skips that d.ts walk in large `noEmit` programs, and skips the changed file's own d.ts emit when it
has at most 32 importers, none of them affects the global scope, and the pending emit stays Go's
(`crates/ts_goport/PORTING.md`, `skips_dts_walk`; `GOPORT_DTS_WALK_FALLBACK=0` restores Go's
walk). The output is the same. The build info stores file versions where Go stores d.ts hashes.

T3 Code setup, 5 runs, incremental/cold, 0.7.0 to now:

| Edit | Project | 0.7.0 | now |
|---|---|---|---|
| contracts field | packages/contracts | 2.87 | 0.86 |
| contracts field | apps/server, apps/web, client-runtime, shared | 0.79 to 1.02 | 0.76 to 1.00 |
| contracts ThreadId brand | packages/contracts | 3.84 | 0.97 |
| contracts ThreadId brand | apps/server, apps/web, client-runtime, shared | 0.98 to 1.05 | 0.98 to 1.02 |
| server config.ts | apps/server | 1.45 | 0.82 |

Other projects reach `@t3tools/contracts` through `node_modules`, as external files, so a contracts
edit does not walk their files. Known: an edit of a file that affects the global scope (apps/web
`HostedBrowserWebview.tsx`) is about 2x a cold run, on 0.7.0 and now. Go runs that d.ts step on a
work group and tsc-rs runs it on one thread.

Repro: `scripts/goport/t3-incremental-bench.sh -t -n 5 -c contracts-field <t3code> <tsc>...`.
Package checks: `scripts/goport/npm-alias-test.sh`.
