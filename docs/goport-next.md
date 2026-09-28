# goport work queue

Root keeps this queue. In goal mode, when a workflow ends, root starts the top item that is ready in the same turn, so at least 3 workflows run at all times. Remove an item when its workflow starts. Add new items at the place that fits their priority.

Each item: one line of goal, the files or worktree it owns, and what it waits for.

## Ready

- **int12 (after R125 is accepted).** Merge into main: goport-lsmem2 `6797d48f0`, goport-lswarm `cf8e4c465`, goport-synmem `729b1f823`, goport-lsmem3 (when verified), goport-emitj `b9c9556b9`, goport-perf10 `ee91415e8`, goport-perf11 (when verified). Verify at pin 52168999f3dc, then R126 (roster carry-forward if roster_fp.py is equal). Owns: worktree goport-int12.

- **Split the `ts_goport` crate.** It is one crate of 605k lines in 677 files, so every build compiles all of it on few threads, and the build cache cannot reuse any part. Start with parts that have few dependencies back into the rest: the generated `lsp/lsproto/lsp_generated/` code (about 50k lines), then `ast` and `scanner`. Measure the release build time before and after. Owns: `crates/ts_goport/Cargo.toml`, a new `crates/ts_goport_*` crate per part, workspace `Cargo.toml`. Waits for: a quiet window with no open lane in the moved files. Every open lane must rebase after it merges.
- **Archive old rule extensions in `current.json`.** `acceptanceRuleChanges` holds 26 copies of two rules, one per batch (38 KB of 86 KB). The check reads only the entry for the current batch. Move the entries of closed batches to history with `scripts/state record note`, and keep the batch records as the archive. Owns: `docs/typechecker-state/*` (root only).

## Waiting

- **Bump B wave 2 and 3.** program-core, server, ls-autoimport, contentmapper and the late PRs of the wave 1 lanes (upstream/bumpB/plan-int11.md). Waits for: int12 in main, and wave 1 checks (workflow bumpB-wave1-check).
- **Free language server program shells and file versions per edit** (lsmem2 diagnosis steps 2 and 3: about 1 to 3 MiB per edit, the long-session growth limit). Owns: program/ls_program.rs, program/go_frontend.rs, project/*, core.rs. Waits for: int12, and coordination with bump B's server lane.
- **Multiprog M8 to M11 (parallel tsc -b).** tsc -b is 1.55x to 1.87x of Go. Waits for: the bump B lanes that own its files (plan-int11.md section 3), and the perf11 tsc -b profile.
- **S6-003 watcher ids** (Go timing dependent) and **workspace/symbol first call** (language server). Waits for: bump B server lane.

