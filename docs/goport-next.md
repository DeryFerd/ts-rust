# goport work queue

Root keeps this queue. In goal mode, when a workflow ends, root starts the top item that is ready in the same turn, so at least 3 workflows run at all times. Remove an item when its workflow starts. Add new items at the place that fits their priority.

Each item: one line of goal, the files or worktree it owns, and what it waits for.

## Ready

- **int12 part 2.** Add goport-lsmem3, goport-reqclean and goport-perf11 to goport-int12 when each is verified, then R126 (roster carry-forward if roster_fp.py is equal to R125). Waits for: int12 part 1 (workflow int12-part1) and those three branches.
- **Default pin switch.** UPSTREAM.json current, ~/.local/bin/tsgo-oracle and the default Go checkout still point at dc37b5249; R125 accepted 52168999f3dc. Switch when no running work compares at the old pin (perf11 does), on zbook and every host. Owns: UPSTREAM.json, scripts/upstream/pin.py.

- **Split the `ts_goport` crate.** It is one crate of 605k lines in 677 files, so every build compiles all of it on few threads, and the build cache cannot reuse any part. Start with parts that have few dependencies back into the rest: the generated `lsp/lsproto/lsp_generated/` code (about 50k lines), then `ast` and `scanner`. Measure the release build time before and after. Owns: `crates/ts_goport/Cargo.toml`, a new `crates/ts_goport_*` crate per part, workspace `Cargo.toml`. Waits for: a quiet window with no open lane in the moved files. Every open lane must rebase after it merges.
- **Archive old rule extensions in `current.json`.** `acceptanceRuleChanges` holds 26 copies of two rules, one per batch (38 KB of 86 KB). The check reads only the entry for the current batch. Move the entries of closed batches to history with `scripts/state record note`, and keep the batch records as the archive. Owns: `docs/typechecker-state/*` (root only).

## Waiting

- **Bump B wave 2 and 3.** program-core, server, ls-autoimport, contentmapper and the late PRs of the wave 1 lanes (upstream/bumpB/plan-int11.md). Waits for: int12 in main, and wave 1 checks (workflow bumpB-wave1-check).
- **Free language server program shells and file versions per edit** (lsmem2 diagnosis steps 2 and 3: about 1 to 3 MiB per edit, the long-session growth limit). Owns: program/ls_program.rs, program/go_frontend.rs, project/*, core.rs. Waits for: int12, and coordination with bump B's server lane.
- **Multiprog M8 to M11 (parallel tsc -b).** tsc -b is 1.55x to 1.87x of Go. Waits for: the bump B lanes that own its files (plan-int11.md section 3), and the perf11 tsc -b profile.
- **S6-003 watcher ids** (Go timing dependent) and **workspace/symbol first call** (language server). Waits for: bump B server lane.
- **Free dispatch-thread synthetic nodes in idle time.** lsmem3 (b1489a5a6) frees them during the next edit: +3.6 to +4.3 ms per edit in the Hono new-expression state (lsmem3/verify.md). Drop them after the answers, in idle work. Owns: ast/synthetic.rs, the owner scope in lsp/server.rs. Waits for: int12 part 2.
