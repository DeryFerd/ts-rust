# goport work queue

Root keeps this queue. In goal mode, when a workflow ends, root starts the top item that is ready in the same turn, so at least 3 workflows run at all times. Remove an item when its workflow starts. Add new items at the place that fits their priority.

Each item: one line of goal, the files or worktree it owns, and what it waits for.

## Ready

- **Split the `ts_goport` crate.** It is one crate of 605k lines in 677 files, so every build compiles all of it on few threads, and the build cache cannot reuse any part. Start with parts that have few dependencies back into the rest: the generated `lsp/lsproto/lsp_generated/` code (about 50k lines), then `ast` and `scanner`. Measure the release build time before and after. Owns: `crates/ts_goport/Cargo.toml`, a new `crates/ts_goport_*` crate per part, workspace `Cargo.toml`. Waits for: a quiet window with no open lane in the moved files. Every open lane must rebase after it merges.
- **Archive old rule extensions in `current.json`.** `acceptanceRuleChanges` holds 26 copies of two rules, one per batch (38 KB of 86 KB). The check reads only the entry for the current batch. Move the entries of closed batches to history with `scripts/state record note`, and keep the batch records as the archive. Owns: `docs/typechecker-state/*` (root only).

## Waiting
