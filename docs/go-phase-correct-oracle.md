# Phase-correct Go oracle results

Date: 2026-08-26.

The new schema 3 producer separates source-only diagnostic re-entry from
artifact queries. Both real projects still return `invariant_error` and
process exit code 1. No pointer check or artifact check was relaxed.
Fresh diagnostic production remains unavailable. These results do not
establish compiler parity.

## Producer

The implementation is in `tools/ts_fixture/go_project_oracle/phase_correct/`.
It starts from `7b912dc5954135d68331568e79a66198f99b6910` and leaves the
original producer and its reports unchanged.

- `e99962e2bb38ad6112375ca0be1885d8bcb226c4` adds the separate producer.
- `ca253b615bda422a5cfd36bc5ab30489f7c033b7` preserves the pinned renderer's
  failed-test reporting check. Both project builds use this clean commit.

Each process creates two independent Programs. The source-only Program
finishes its initial diagnostics, source reset, and normal diagnostic
re-entry before the query Program is created. It makes no artifact queries.
The query Program records initial source diagnostics, then diagnostic
snapshots before types, after types, and after symbols. It records the
source reset and re-entry before the second artifact walk.

Both artifact walks use `hadErrorBaseline` from the query Program's initial
source snapshot. Later query-added diagnostics do not change that flag.
Each snapshot has its own diagnostic records, error-artifact state, input
order, and sequence boundaries. Query differences are labeled retained
snapshot differences, not fresh diagnostic production.

Program and checker tokens bind actual process-local object identities.
Every direct baseline type or symbol query records its checker, queried
node, rendered node, file, byte range, kind, and query sequence token.
The recorder streams and hashes the trace. It does not publish pointer
addresses or treat tokens as object identities across processes.

The original source-completion reset is unchanged. No diagnostic collection
or broad checker cache is cleared. Retained diagnostic equality remains
separate from `fresh_diagnostics.equal`, which stays null. A stable control
returns `incomplete_evidence`. Pointer, visit, renderer, source-only
diagnostic, and artifact failures still prevent success.

## Inputs

| Input | Hono | ts-pattern |
| --- | ---: | ---: |
| Config roots | 188 | 18 |
| Go loaded sources | 352 | 111 |
| Artifact files | 287 | 18 |
| Prepared source files checked | 486 | 101 |
| Dependency files checked | 33,249 | 12,649 |
| Dependency links checked | 70 | 45 |
| Earlier evidence files checked | 126 | 96 |

Hono uses source commit `06880c4a2b04de9dd74217f26dd831209b9c01f1` and the
unchanged `target/project-inputs/hono/source/tsconfig.build.json`.
ts-pattern uses source commit `c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0` and
the unchanged `target/project-inputs/ts-pattern/source/tsconfig.json`.
The latter config's SHA-256 remains
`b53aa621db1475ecd4316db408f54cb41bb43d9bc737561f00985de4f4ff3c05`.

The existing input verifiers passed before and after the runs. Their reports
are byte-identical. Source files, configs, dependencies, links, and missing
generated outputs stayed unchanged. No package install or project build ran.
The upstream checkout remained clean. No project `dist` directory appeared.
Scoped `GIT_CEILING_DIRECTORIES` values kept these archive inputs from being
attributed to the ts-rust repository.

ts-pattern's preparation reader still records 367 inputs, while this Go
Program loads 111 sources. These separate observations were not normalized
to match. TS5011 remains visible. No `rootDir` option was added.

The original result hashes remain:

- Hono: `1edde625f35801c8be68fc85630ec7d6431b6deb5938f1fe0d8b171c12a5e53d`.
- ts-pattern: `f00030538b754618531226b48dc5534a1c5f7900f5dcdb79de41cff4e08844b7`.

## Diagnostic phases

Both fresh processes for each project produce these counts.

| Program and snapshot | Hono | ts-pattern |
| --- | ---: | ---: |
| Source-only, initial | 0 | 1 |
| Source-only, before reset | 0 | 1 |
| Source-only, after re-entry | 0 | 1 |
| Query, initial | 0 | 1 |
| Query, first before types | 0 | 1 |
| Query, first after types | 5 | 1 |
| Query, first after symbols | 5 | 1 |
| Query, before reset | 5 | 1 |
| Query, after re-entry | 5 | 1 |
| Query, second before types | 5 | 1 |
| Query, second after types | 5 | 1 |
| Query, second after symbols | 5 | 1 |

The five Hono records exactly match the earlier warm diagnostic records.
They are absent from both source-only re-entry and the query Program's
initial source snapshot. They first appear after the first type-artifact
walk. They remain separate from the initial source-check result.
The single ts-pattern record is TS5011 in every snapshot.

## Strict checks

| Check | Hono | ts-pattern |
| --- | --- | --- |
| Frozen renderer flags | false, false | true, true |
| Source-only retained re-entry diagnostics | Equal | Equal |
| Query Program retained reset/re-entry diagnostics | Equal | Equal |
| Type artifact bytes between walks | Different | Equal |
| Symbol artifact bytes between walks | Equal | Equal |
| AST visits between walks | Equal | Equal |
| Changed direct type-query identities | 221 | 44 |
| Changed rendered-type identities | 221 | 44 |
| Changed symbol identities | 0 | 0 |
| Fresh diagnostic production | Unavailable | Unavailable |
| Outcome in both processes | `invariant_error` | `invariant_error` |
| Process exit code | 1 | 1 |

The first type and symbol artifacts for both projects are byte-identical to
their original cold artifacts. Hono's fixed flag removes the 118
`error`/`any` display differences in the original cold/warm comparison.
The new two-walk type comparison still has 91 changed lines. On 69 of these
lines, every change is removal of `ArrayBufferLike` from a printed `Buffer`
type argument. The other 22 lines remain separate recorded differences.
All raw bytes and pointer failures remain in the evidence. These display
differences are not accepted or normalized away.
The classification script does not change artifacts or equality checks.

ts-pattern demonstrates the strict pointer rule directly: equal type and
symbol artifacts do not bypass its 44 changed type identities.

## Trace checks

Each process has two Program tokens and two checker tokens. The source-only
Program has zero artifact queries. Diagnostic snapshots name exact start
and end operation tokens, with no artifact query between those boundaries.
Every query token is consecutive and belongs to the query Program's checker.
Recorded query totals match the pinned walker's observation counts.

| Trace per process | Hono | ts-pattern |
| --- | ---: | ---: |
| Events | 330,058 | 18,962 |
| Direct artifact queries | 329,648 | 18,890 |
| Bytes | 188,763,657 | 10,624,593 |

Hono trace SHA-256:
`9f0580f24723e830066d2b8b0adaa8725d805ca233bfc5e94fcdce95e778cafe`.

ts-pattern trace SHA-256:
`983e5773e244d9ccc58bbdbb2aabc7e28a60a8a5702a9e547772657e2ecf728b`.

Both traces are byte-identical across the corresponding fresh processes.
Reports match after excluding only `runtime` and `run_id`. Every present
artifact's bytes, length, and hash were verified. No-content errors remain
absent artifacts, not empty-file digests. Program roots, loaded source
records, artifact order, and compiler options match the original inputs.
The original graph's missing-evidence fields are still present.
Repeatable available evidence is not full replay or graph parity.

## Controls and resources

The three focused controls passed at `e99962e2` and on the final Hono binary
built from `ca253b61`:

- The five-diagnostic reduction keeps source-only snapshots empty and both
  renderer flags false. It also checks independent Programs and exact tokens.
- The TS2322 control keeps both renderer flags true and remains incomplete.
- The object-literal control keeps equal printed artifacts but fails strict
  type identity.

The final control run returned exit code 0 in 0.23 seconds, with peak RSS
of 120,040 KiB. Its result records the same executable and build-manifest
hashes as the real Hono runs.

| Process | Elapsed seconds | Peak RSS KiB |
| --- | ---: | ---: |
| Hono build | 135.28 | 2,500,532 |
| Hono process-a | 12.26 | 3,467,948 |
| Hono process-b | 12.33 | 2,999,968 |
| ts-pattern build | 133.61 | 2,418,760 |
| ts-pattern process-a | 0.69 | 489,264 |
| ts-pattern process-b | 0.72 | 409,196 |

Each launcher used the shared Git-derived build lock, a verified 16 GiB
cgroup, no swap, one Go worker, and a 12 GiB Go memory target. The builds
used copied module inputs, isolated caches, `-mod=readonly`,
`GOTOOLCHAIN=local`, `GOPROXY=off`, `GOSUMDB=off`, and `GOWORK=off`.
The pinned SDK is Go 1.26.5 for linux/amd64. Its executable SHA-256 is
`8da5fd321795754b994c64e3eb8a5a14ff47bd285559a7e876f3c79abafc67f9`.
The pinned upstream commit is
`dc37b5249ab60e2bbce936f71b883e6c8136167e`.

## Evidence paths

All runtime evidence is outside this source worktree:

- `target/project-evidence/hono-go/phase-correct/result.json`.
- `target/project-evidence/ts-pattern-go/phase-correct/result.json`.
- `target/project-evidence/hono-go/phase-correct/type-differences.json`.
- `target/worktrees/wave131-phase-oracle/controls-1/`.
- `target/worktrees/wave131-phase-oracle/final-controls/result.json`.

Each project directory has before/after input reports and an inventory of
the preserved earlier evidence. Its `attempt-1/` directory has the build
manifest, exact overlays, executable hash, process arguments, resource
reports, and `process-a/` and `process-b/` artifacts and reports.

The Hono result SHA-256 is
`8e0a68384733527f5402371965c1be91b36f0940f910f7fa2ef5c5c7a86a81de`.
The ts-pattern result SHA-256 is
`81e4ab17b37bbe734ce6e94a11665fee3486d1c935f5a31e6d958a1b2fde7b8e`.
The final control result SHA-256 is
`83b44ec3614c19a8d6da1119a406d58c811a4cc4a29ac8a9351285078f8e6381`.

The evidence verifier and raw-line comparison script are under
`target/worktrees/wave131-phase-oracle/`. Each generated result records the
script hash. The producer README gives the launcher contract. Reruns must
use new output directories and isolated module caches. They must not replace
these results or the original schema 2 evidence.
