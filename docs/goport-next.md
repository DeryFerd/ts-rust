# goport work queue

Root keeps this queue. In goal mode, when a workflow ends, root starts the top item that is ready in the same turn, so at least 3 workflows run at all times. Remove an item when its workflow starts. Add new items at the place that fits their priority.

Each item: one line of goal, the files or worktree it owns, and what it waits for.

## Ready

- **int12 part 2.** Add goport-lsmem3, goport-reqclean and goport-perf11 to goport-int12 when each is verified, then R126 (roster carry-forward if roster_fp.py is equal to R125). Waits for: int12 part 1 (workflow int12-part1) and those three branches.
- **Default pin switch.** UPSTREAM.json current, ~/.local/bin/tsgo-oracle and the default Go checkout still point at dc37b5249; R125 accepted 52168999f3dc. Switch when no running work compares at the old pin (perf11 does), on zbook and every host. Owns: UPSTREAM.json, scripts/upstream/pin.py.

- **Split the `ts_goport` crate.** It is one crate of 605k lines in 677 files, so every build compiles all of it on few threads, and the build cache cannot reuse any part. Start with parts that have few dependencies back into the rest: the generated `lsp/lsproto/lsp_generated/` code (about 50k lines), then `ast` and `scanner`. Measure the release build time before and after. Owns: `crates/ts_goport/Cargo.toml`, a new `crates/ts_goport_*` crate per part, workspace `Cargo.toml`. Waits for: a quiet window with no open lane in the moved files. Every open lane must rebase after it merges.

## Waiting

- **Bump B wave 2 and 3.** program-core, server, ls-autoimport, contentmapper and the late PRs of the wave 1 lanes (upstream/bumpB/plan-int11.md). Waits for: int12 in main, and wave 1 checks (workflow bumpB-wave1-check). Plan: `target/continuation-r97-goport/upstream/bumpB/plan-wave2.md` (merge goport-bumpB into a new goport-bumpB2 from int12, 3 conflict hunks). API battery `ext` (52 traces) is recorded at pin 16c25522e123 (`upstream/bumpB/api-battery/record.md`); on wave 1 it shows `getConfigSourceFile` failing ("unported Go code: SourceFile.ParseOptions" on the root config, "file N is not published" on an extended config) for the config/api lanes, and the encoder version byte for wave 3.
- **Free language server program shells and file versions per edit** (lsmem2 diagnosis steps 2 and 3: about 1 to 3 MiB per edit, the long-session growth limit). Owns: program/ls_program.rs, program/go_frontend.rs, project/*, core.rs. Waits for: int12, and coordination with bump B's server lane.
- **Multiprog M8 to M11 (parallel tsc -b).** tsc -b is 1.55x to 1.87x of Go. Waits for: the bump B lanes that own its files (plan-int11.md section 3), and the perf11 tsc -b profile.
- **S6-003 watcher ids** (Go timing dependent) and **workspace/symbol first call** (language server). Waits for: bump B server lane.
- **Free dispatch-thread synthetic nodes in idle time.** lsmem3 (b1489a5a6) frees them during the next edit: +3.6 to +4.3 ms per edit in the Hono new-expression state (lsmem3/verify.md). Drop them after the answers, in idle work. Owns: ast/synthetic.rs, the owner scope in lsp/server.rs. Waits for: int12 part 2.
- **Gate editor stage: known FAILs end with lsmem2 and lsmem3 in main.** Until int12 (with goport-lsmem2 and goport-lsmem3) is accepted, an editor FAIL counts as known only if the same session fails on the R125 bins and is not worse. A new failing session, or a known one that got worse, is a regression. After int12 is in main, every editor FAIL is a regression, except `long` growth, which waits for the language server program-shell item above; when that lands, `long` is a regression too.
- **Re-audit, 2026-09-30.** Run `scripts/audit/metrics.py --since 2026-09-28T08:10:00Z` and compare with the targets in `recommendations.md` item 6. For each missed target, find the cause in the transcripts and fix the tool, the brief or the rule; add one line per finding to `recommendations.md`. Waits for: 2026-09-30.

