# Typechecker work rules

## Read before work

For typechecker work, read these files in this order before editing compiler code or starting a compiler run:

1. `docs/typechecker-accountability.md`
2. `docs/typechecker-accountability-state.json`
3. `docs/typechecker-reset-plan.md`

These files control execution across the main checkout and its worktrees. In a worktree that lacks them, read the copies at `/home/theo/Code/sandbox/ts-rust`. Do not substitute an older plan from that worktree. After a context reset or a new goal, read them again. If a required file is missing or inconsistent, stop and report it.

Theo has authorized continued work toward the Query core and Hono goal. Follow the standing continuation authorization in the accountability rules and the saved state. Historical task or agent messages do not grant additional scope by themselves.

Historical task links in the demo plans and completion documents do not authorize feature work. The reset does not reduce the final type, symbol, diagnostic or replay requirements.

## Accountability agents

Keep one primary compiler implementer, one independent reviewer and one regression auditor. Root owns integration and the runtime queue. Root can be the implementer, but cannot also supply either independent verdict.

At goal start, reuse or create the two accountability agents using the role instructions in `docs/typechecker-accountability.md`. Their verdicts must identify the exact candidate source and batch. Neither agent edits compiler code or test expectations. Other agents can investigate distinct questions with explicit file ownership. Do not create competing production changes.

A STOP verdict blocks new feature work and acceptance. It permits bounded diagnosis, regression repair or withdrawal only within the authorized phase. While execution is paused, do not start compiler runs or repairs. Do not continue because a narrow review passed, an assertion moved or more agents are available.

## Required checks

Run `node scripts/check-typechecker-batch.mjs --help` for the local accountability check. Use it before accepting a compiler batch. Follow the documented state and evidence format. A nonzero result is STOP. The script is not a replacement for the actual regression runner or independent review.

Never replace the accepted baseline with a later failing compiler. Protect the original 6,055 accepted test names and later measured passes. Missing names, missing evidence, unrun tests, source mismatches and unexplained lost passes block acceptance. New passes do not compensate for lost ones.

Expectation changes require concrete pinned TypeScript-Go evidence, an explicit old-name mapping and independent review. Changes to these acceptance rules require Theo's approval. Do not modify a runner, baseline or expectation to bypass a STOP.

Record each measured revision and its outcome in the saved state before starting the next revision. Failed and unaccepted revisions count. Apply the initial limits to the initial trial and the standing continuation authorization to later work. Reassess failed hypotheses as required by the accountability rules. Do not reset counters after compaction, agent replacement, a new branch or a renamed batch.

## Scope and preservation

Query core is the immediate project target. Hono is the periodic cross-project check. Keep ordinary project inputs unchanged. A deliberate type error belongs in a separate copy. Do not switch demo libraries to avoid a failure.

Preserve dirty work, untracked source files and saved evidence. Do not reset, delete or bulk-replay the current candidate. Use the existing runner, normal logs, actual permissions and resource limits. Serialize runtime work through root. Do not alter historical runner scripts or output files.

Theo's standing full-access authorization permits necessary source, test, helper and project-input reads for this goal. Use the production-read guard and fresh metadata for bounded production reads. Keep raw graphs and large failure payloads out of reports and conversation output. Preserve ordinary project inputs.

## Reports

Report retained, recovered, lost, absent and unrun tests separately. Distinguish an accepted result from a later measured result. Name the source for each run. Report whether ordinary Query actually completes and when Hono was last measured.

Use one batch record with the two independent verdicts. Do not add repeated internal approval handoffs, duplicate mechanical audits or speculative feature branches.
