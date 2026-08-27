# Wave 131 input script integration

## Scope

The six-project base is `400b2072bf72f07a662ee2e79f77dd7ae7ed56f0`.
That branch is `agent/wave131-project-input-scripts-integration`.
The Query follow-up uses reviewed base
`d44d1c49fdd3c92b41e2a21113be7fe30c5fde84` on
`agent/wave132-query-script-integration`.

Each project group applies only its approved scripts, tests, and documentation.
The approved files match their source tips exactly, including file modes and
pins. No compiler source or unrelated lint changes are included.

These are grouped patch integrations, not merges of the source branches.
Each commit body records the full source commit IDs. All source chains start
at `b1acb9e5846ba45be5c1ee537b32e585bb8ad1a7`, which is already an ancestor of
both bases. No prerequisite commits were missing. No merge conflicts occurred.

## Commit order

| Project | Integration commit | Approved source chain |
| --- | --- | --- |
| Hono | `f3211ecd419eab54857d8deea56be27165efac1f` | `dc48de6a`, `30edb03a` |
| Svelte | `0b4056a42fb03015e0c5198ccfeec21f916c3400` | `865f3914`, `08528ce2` |
| ts-pattern | `5e645e04636f991173c0c95fb088d0e754c9ad41` | `7eebbdb1`, `e1fe4418` |
| Effect | `6aa5cf85332d5102088d288a7641f83b7f50b053` | `f9825a74`, `ef5308a0`, `4d1bce25`, `c216ab8f` |
| React Hook Form | `d1ac1f5b150685780c0644c908f5d3e298c35f04` | `e530030f`, `2f9e1cff`, `11290719`, `dad3e789`, `60b2a431` |
| Zod | `697351da61191230e69ab0b86089dea34bace488` | `9cd67c92`, `c0fbcb8c`, `a1c00e5f` |
| Query | This follow-up commit after `d44d1c49` | `8cb4b413`, `617efced`, `57b8e3f1` |

Query's source tip `57b8e3f1` has final bounded approval. The follow-up copies
only its two scripts and `docs/project-inputs/query.md`, with exact source
bytes, modes, and pins. It does not include the unrelated `8d413624` heritage
changes. This follow-up did not edit the primary `4705d079` worktree.

## Six-project checks

These results are carried forward from reviewed `d44d1c49`. They were not
rerun for the Query follow-up. The six projects' files remain unchanged.

| Check | Result |
| --- | --- |
| JavaScript syntax | All 10 integrated scripts and test runners passed |
| Python archive helper syntax | Passed without generating bytecode files |
| Hono, Svelte, and ts-pattern CLI guards | 24 passed |
| Effect safety tests | 35 passed |
| React Hook Form safety tests | 48 passed |
| Zod offline safety tests | 70 passed, 1 optional download test skipped |

The new `scripts/prepare-input-paths.test.mjs` uses disposable workspaces, fake
Git responses, and blocked preparation commands. Its negative cases compare
the complete fixture tree before and after rejection. Its controls reach only
a blocked Git or memory-scope command.

All six-project test fixtures were under that integration worktree's `target`
directory. The first sandbox runs hit Node subprocess `EPERM` errors.
Complete test reruns passed in 2 GiB user scopes. Their logs are under
`target/offline-scratch/logs`:

- `syntax-js-retry.log` and `syntax-python.log`
- `input-paths-retry.tap`
- `effect-retry.tap`
- `react-hook-form-retry.tap`
- `zod-retry.tap`

The Effect and React Hook Form tests read existing pinned archives and copy
them into disposable fixtures. The original archive hashes still match their
pins after the tests. The Zod download test stayed disabled.

## Query checks

| Check | Result |
| --- | --- |
| Approved file bytes and modes | Exact match with `57b8e3f1` |
| Query JavaScript syntax | Both imported scripts passed in 2 GiB user scopes |
| Query offline security tests | 18 passed, 0 skipped, in 100.67 seconds |

The Query tests use local pinned archives and disposable Git repositories.
They reject the four reviewed install-root redirects before installer dispatch.
Their clean and valid-layout controls reach only a test interceptor. That
interceptor stops every install or build call before execution. The tests also
cover tool payload integrity, managed write paths, pnpm metadata, internal
links, and a relocated copy of the current installed layout.

The Query run uses a 2 GiB user scope. Its scratch files and logs stay under
`target/query-offline-scratch` in the Query integration worktree. Cargo TMPDIR
and shared build locks do not change. The test harness checks real prepared
metadata, all 706 generated outputs, both archives, source Git state, and cache
Git state before and after the run. Those snapshots matched. Disposable
fixtures were removed after the run. The logs are:

- `target/query-offline-scratch/logs/query-prepare-syntax.log`
- `target/query-offline-scratch/logs/query-tests-syntax.log`
- `target/query-offline-scratch/logs/query-offline.log`

The approved generated-manifest SHA-256 is
`5c93347a1fea93f5cede5cdd1b7911e175b49438ab358e9cb8dda46c8194b81b`.
The declaration-manifest SHA-256 is
`6d950270cecc6f8e867eda0e09a38177486c55c2fd5674f46ae559505b07312e`.
These remain input evidence, not compiler parity results.

This integration did not run package downloads, dependency installs, project
builds, project typechecks, or Go and Rust parity comparisons. It did not
change real prepared inputs, source caches, or the main branch. These results
cover script syntax and disposable guard tests only.
