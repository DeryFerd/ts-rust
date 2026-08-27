# Query Core module target

Status: module-target repair verified, full project checking remains unsupported.

## Reproduction

Clean `3947c8ba` reproduced `M00.EXTERNAL_MODULE_TARGET` for
`assert@1.5.1/node_modules/assert/assert.js`. This was not a stale result from
the sealed `400b2072` run.

Both Rust runs used the unchanged prepared
`target/project-inputs/query/source/packages/query-core/tsconfig.prod.json`.
The config SHA-256 is
`767c2ce4e408ca17d2b915c34119e115fa65dce53d1d9b58bbff1511548a3487`.
No compiler options, source files, or dependencies were changed for either run.

## Pinned Go route

The read-only probe used Go 1.26.5 and unmodified upstream commit
`dc37b5249ab60e2bbce936f71b883e6c8136167e`.

Go loaded 186 files and produced no diagnostics, including declaration
diagnostics. It retained `allowJs=true`, `checkJs=true`, `noEmit=false`,
`skipLibCheck=true`, and the default JavaScript dependency depth of zero.

Go resolved the installed `assert.js` file but did not load it. The checker
selected the ambient `assert` symbol from `@types/node/assert.d.ts` for all
three requests. That declaration file's emit mode was `ESNext`. Its default
resolution mode was `None`. The requests used `CommonJS` once and `ESNext`
twice. Ambient selection preceded filesystem-target validation.

A separate synthetic probe confirmed that Go can resolve JavaScript with
`allowJs=false`. It excludes the file from the graph and reports TS7016 for
an untyped named import. That probe did not change the prepared Query project.

## Repair

Runtime commit: `154c696bcc43060c89a4d493df04f8f1f0d4e0af`.

The compiler keeps successful resolutions separate from source admission.
It applies `allowJs`, `noResolve`, and JavaScript dependency depth. A later
shallower route reuses resolved edges to admit descendants. Explicit roots
keep depth zero. Exact global ambient declarations take precedence over
filesystem targets. Forced-module augmentations do not become global targets.

Known omissions without a supported declaration remain explicitly unsupported
as `M00.OMITTED_MODULE_TARGET`. Unproven missing targets remain fatal. No target
is replaced with an invented type. A small fixture adapter retains the new
typed error fields. Package observations, scripts, class checking, and source
bodies are unchanged. The approved `429bb01a` worktree is unchanged.

The clean-commit project run now reaches `E00.SOURCE_SYNTAX` in
`packages/query-core/src/timeoutManager.ts`, on `Arrow` node 90 in file 20.
That source-body boundary remains for its owner.

Production checks and 296 selected compiler tests passed. These include
ambient precedence, depth limits, shallower-route replay, explicit JavaScript
roots, omitted-target classification, and missing-target invariant checks.
Strict Clippy and formatting passed. The later test-only lint annotation keeps
the same fixture and assertions. It does not change runtime behavior.

## Evidence

Files below are in `target/project-evidence/query-core-module-target-wave132`.

| File | SHA-256 |
| --- | --- |
| `baseline-3947c8ba.json` | `c8c9eb77a7a0334088c27303d27e1d0d5e577936f604dc0ec2a8a9070d62dddc` |
| `after-154c696b.json` | `9d0fff0286653bb3558deed9ce30d49545f0724cab3668cdd3a62cea9f5a3241` |
| `input-before.json` | `c81ef4fbf7e328f5ebad36fc07bc5b05a845134fd6852d4530833424d78525de` |
| `input-after-final.json` | `c81ef4fbf7e328f5ebad36fc07bc5b05a845134fd6852d4530833424d78525de` |
| `go-route-current.json` | `10899d40e217658d339989b12f91b42888eb50adeeca08e9eb7463d4c9c0759c` |
| `go-probe/main.go` | `8113ac66a6ee947fca53c041efe4d227c22a0ed44f9280106229279c25a792dd` |
| `go-probe-current.bin` | `8c43ad0470abeb433dedfcfec61e1533345021cdf83ca82534fcac9059cf1792` |

The verifier checked 134,010 file payloads and 10,348 links before and after.
Those checks are prepared-byte evidence, not a compiler file-read trace.
The Rust reports retain clean runtime source and executable identities. They
do not include a supplied build record. The Go probe records routes and
diagnostics, not full type and symbol artifacts. No performance or full parity
claim follows from these results.
