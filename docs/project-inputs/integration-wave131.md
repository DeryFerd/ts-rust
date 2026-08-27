# Wave 131 input script integration

## Scope

The base is `400b2072bf72f07a662ee2e79f77dd7ae7ed56f0`.
The branch is `agent/wave131-project-input-scripts-integration`.

Each project group applies only its approved scripts, tests, and documentation.
The approved files match their source tips exactly, including file modes and
pins. No compiler source or unrelated lint changes are included.

These are grouped patch integrations, not merges of the source branches.
Each commit body records the full source commit IDs. All source chains start
at `b1acb9e5846ba45be5c1ee537b32e585bb8ad1a7`, which is already an ancestor of
the base. No prerequisite commits were missing. No merge conflicts occurred.

## Commit order

| Project | Integration commit | Approved source chain |
| --- | --- | --- |
| Hono | `f3211ecd419eab54857d8deea56be27165efac1f` | `dc48de6a`, `30edb03a` |
| Svelte | `0b4056a42fb03015e0c5198ccfeec21f916c3400` | `865f3914`, `08528ce2` |
| ts-pattern | `5e645e04636f991173c0c95fb088d0e754c9ad41` | `7eebbdb1`, `e1fe4418` |
| Effect | `6aa5cf85332d5102088d288a7641f83b7f50b053` | `f9825a74`, `ef5308a0`, `4d1bce25`, `c216ab8f` |
| React Hook Form | `d1ac1f5b150685780c0644c908f5d3e298c35f04` | `e530030f`, `2f9e1cff`, `11290719`, `dad3e789`, `60b2a431` |
| Zod | `697351da61191230e69ab0b86089dea34bace488` | `9cd67c92`, `c0fbcb8c`, `a1c00e5f` |

Query is not included. Its `8cb4b413`, `617efced` chain is complete but still
awaits final approval. The results below do not cover Query.

## Checks

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

All test fixtures were under this worktree's `target` directory. The first
sandbox runs hit Node subprocess `EPERM` errors. Complete test reruns passed
in 2 GiB user scopes. Their logs are under `target/offline-scratch/logs`:

- `syntax-js-retry.log` and `syntax-python.log`
- `input-paths-retry.tap`
- `effect-retry.tap`
- `react-hook-form-retry.tap`
- `zod-retry.tap`

The Effect and React Hook Form tests read existing pinned archives and copy
them into disposable fixtures. The original archive hashes still match their
pins after the tests. The Zod download test stayed disabled.

This integration did not run package downloads, dependency installs, project
builds, project typechecks, or Go and Rust parity comparisons. It did not
change real prepared inputs, source caches, or the main branch. These results
cover script syntax and disposable guard tests only.
