# Typechecker accountability

These rules were installed on September 5, 2026, at Theo's request. The machine-readable status is in [typechecker-state](typechecker-state/current.json): a small `current.json` and an append-only `history.jsonl`. Use `scripts/state` to read and write it.

The [reset plan](typechecker-reset-plan.md) explains the failure and recovery choices. These rules control execution if an older plan conflicts with them. They do not change the full port requirements.

## Standing continuation authorization

After the initial recovery phase closed, Theo instructed:

> You have my permission to do whatever you need to do. I have you on full access for a reason. Keep going

This authorizes continued work toward the Query core and Hono goal without a new permission request at each revision limit. The initial four-revision record remains complete and unchanged. Use `recovery-continuation` for later work and keep the cumulative revision numbers and all earlier results. The initial per-hypothesis and cumulative approval stops do not apply to this authorized continuation.

Keep experiments focused. After two measured attempts without useful recovery or Query progress, reassess the cause and dependency path with the independent reviewer. Reassessment is required. Another user approval is not required for work within this goal.

Necessary repository source, tests, helpers and project inputs may be read for this work. Use bounded production reads and fresh metadata. Keep raw type graphs and large failure payloads out of reports and conversation output. Keep ordinary project inputs unchanged.

Use as many independent analysis agents as the work needs, up to the available 40. Give each one separate file ownership. Keep one compiler writer and the root runtime queue while shared checker state remains under repair.

Read-only research helpers are always allowed and need no build or demo gate. A goal that asks for parallel work starts a workflow within 30 minutes. For a build that fails in many files, root builds once and gives each fix agent one file and its error list. Fix agents do not run Cargo. A later wave waits until the earlier wave it depends on is integrated and builds. [AGENTS.md](../AGENTS.md) has the details.

This authorization does not waive protected tests, corpus preservation, pinned Go evidence, exact source identity, independent verdicts or complete Query/Hono diagnostics, types, symbols and replay. STOP still blocks acceptance and unrelated feature work. It permits continued diagnosis and regression repair under this authorization.

## Start or resume

1. Read this file, the saved state and the reset plan. Do this after a context reset as well as at goal start.
2. Check the user's current instruction. A historical active goal is not permission to ignore the pause. Theo's new goal can authorize the recovery block, but does not waive the acceptance rules.
3. Verify the candidate source and required evidence still exist. Do not rebuild a missing accepted baseline from the current compiler.
4. Reuse or create the regression auditor and independent reviewer. Give them this file and the saved state. Record their current agent names. Agent names can change across sessions. Their roles and limits cannot.
5. Select one primary implementer and record file ownership before any parallel work. Root owns the runtime queue and integration state. Keep the other compiler drafts frozen.
6. Record the recovery hypothesis, exact tests it must recover, current source and cumulative revision number before editing. Record any applicable block budget.

The paused state can be activated only by Theo's next instruction to start the work. Record that instruction in the state. Do not claim that the goal has started merely because the accountability files exist.

## Regression auditor role

Use this assignment when creating or resuming the agent:

> You are the independent regression auditor. You do not edit compiler code, test expectations, baseline records or the primary implementer's patch. Read the accountability rules and state. Compare exact names and outcomes against the original 6,055 accepted tests, all 6,330 passes in the earlier full run and later measured passes. Verify that required runs closed normally and match the exact candidate source. Keep historical, partial and current results separate. Identify every lost pass, missing name and unrun requirement. Check any expectation change against its concrete pinned Go evidence and old-name mapping. Return one source-bound PASS or STOP verdict with the blocking facts. New passes cannot compensate for lost ones. Do not approve a focused run as full acceptance.

The auditor uses existing result parsers and logs. It does not inspect private test bodies or raw failure payloads to infer a cause. Cause investigation is a separate assigned task with its own access limits.

The historical source references are fixed:

- Accepted commit: `5c7c7bd20cb45ebc8f2171eed8478fa2797e8343`, 6,055 accepted passes.
- Code-equivalent checkpoint: `8f4943ac6dffa6785165e18a07a5b369a6811da7`. The measured run belongs to the first commit.
- Later passing-name reference: fingerprint `162fccf9061a30bac011c98f3086538a7ba64b5ca87e99ca6c78b69990b175be`, 6,330 passes. It also had 446 failures and is not an accepted compiler.

Every later passing name stays in the preservation ledger. Restarting from the accepted commit does not erase later measured behavior.

## Independent reviewer role

Use this assignment when creating or resuming the agent:

> You are the independent reviewer and progress reviewer. You do not edit the compiler patch or its expectations. Read the accountability rules, reset plan and state. Review the complete operation against pinned Go, including its real callers, context, cache publication, recursion, diagnostics, negative cases and repeat behavior. Check the actual ordinary Query result, Hono freshness, scope and cumulative revision count. A narrow static review or a later stopping point is not a completed feature. Return one source-bound PASS or STOP verdict. Stop new feature work when the operation remains incomplete, new regressions appear, the revision limit is reached, or the work changes targets without a decision. Do not reset the counter for new tests, traces, branches or agent replacements.

This is the existing independent code-review role with explicit authority to stop the work. It is not an additional approval committee. The reviewer checks the complete operation and the measured outcome, not each preparation step.

## What STOP means

A STOP from either accountability agent blocks new feature work and acceptance. Root cannot override it with a summary, a different agent's opinion or a passing new test.

Within an active, authorized recovery phase, STOP permits diagnosis, repair of the regression or withdrawal of the current batch. It does not permit another feature or a larger experiment. During the current pause, only setup, documentation and read-only investigation are authorized.

To close a STOP, record the specific corrected evidence and obtain a new verdict on that exact source from the role that raised it. If the facts are disputed, report both positions to Theo. Do not replace the reviewer to obtain approval.

Only Theo can approve a change to the acceptance rules. Any exception must record his instruction, its scope, exact affected names, Go evidence and replacement mapping. The local check must not have a general ignore-regressions switch.

## Initial recovery revision limits

These limits govern the completed initial recovery trial. The standing continuation authorization above governs later work. Do not rewrite the initial history or use the continuation to waive a failed result.

- One recovery hypothesis permits at most two measured revisions.
- The initial recovery phase permits at most four measured revisions across at most two demonstrated causes.
- Failed and unaccepted revisions count. Record a candidate before running its checks. A repeat run of identical source does not become a new semantic revision, and does not reset a counter.
- After two measured implementation batches without useful ordinary Query progress, stop feature work and reassess the dependency path. During regression recovery, apply the cumulative recovery limit and report Query separately.
- A later assertion, changed error label, new passing control, trace, different agent or renamed batch does not reset these limits.
- At the cumulative limit, either required results pass or have individually approved Go-backed expectation updates, or implementation stops with the recovery comparison and remaining losses. A recorded cause or port gap does not clear a STOP. Do not renew the same experiment automatically.

Reaching a limit does not prove that restarting from green is cheaper. Use the recorded dependency comparison. If the evidence is insufficient, stop and ask Theo for direction.

## One batch record

Root maintains one saved state and one record per batch. Write it through `scripts/state record`. `record revision` appends a revision row, `record note` archives a named record, `record passing-result` appends an auditor result and `record current` changes `current.json`. Each write adds a line to `history.jsonl`. The last line for a revision number is its current row. Update the state before starting a revision and after its measured result. Do not rely on conversation memory or subagent messages alone.

Before replacing `state.batch`, save its record at `docs/typechecker-batches/<batch-id>.json` (`scripts/state batch --with-history`) and add that path to `batchRecords`. `record current` refuses a new batch until both exist. Keep the complete initial-phase `recoveryHistory` in the next batch. The auditor compares it with the prior saved records. Do not delete old revisions or start the history again at one.

The record must identify the source, hypothesis, changed scope, exact expected recoveries, commands, completed runs, result paths and hashes, ordinary Query outcome, latest Hono result, both independent verdicts and the next permitted action. Each verdict names its agent, batch and exact source. A verdict from another source is stale.

Keep test comparisons separate for the original accepted roster, later measured passes and new coverage. Keep corpus diagnostics, types, symbols and replay evidence separate from unit-test totals. Full acceptance needs the required corpus checks as well as regression checks. Missing evidence is STOP.

Do not store raw type graphs, private test bodies or large failure payloads in this file. Link the existing evidence. If an ignored evidence file is missing in a future checkout, stop and recover it from preserved records. Do not invent its contents.

## Automated check

The local entry point is `node scripts/check-typechecker-batch.mjs --help`. The script reads saved evidence and state. It must reject malformed or missing evidence, mixed source identities, lost or missing passing names, stale verdicts and STOP verdicts. Tooling tests use synthetic records and do not run the compiler.

Run the real check from the main repository root:

```sh
node scripts/check-typechecker-batch.mjs docs/typechecker-state
```

Run the tooling tests with all named results visible:

```sh
node --test --test-isolation=none --test-reporter=spec scripts/check-typechecker-batch.test.mjs scripts/state.test.mjs
```

The first version automatically compares the fixed 6,055 accepted names and the later 6,330 passing names. The regression auditor must also compare passing names added after that reference. Their starting evidence is in `additionalPassingResultsForAuditor`. Append later measured results there. The script does not itself prove this extra comparison, corpus parity, Go equivalence or Query completion. The independent verdicts must address those requirements. A script PASS alone is not compiler acceptance.

This is a required pre-acceptance check, not a replacement Cargo runner. It does not prevent someone from calling Cargo or Git directly, and it cannot prove that a human-authored review is true. Root must honor the rules for actions outside the check. Keep existing resource limits and actual tool permissions.

The current invocation must return STOP because no recovery batch is authorized or accepted. A successful setup test must not clear the real state.

The original check supports `phase: "initial-recovery"`. The authorized continuation requires an explicit reviewed extension for `phase: "recovery-continuation"`. Keep the complete history and require the saved continuation authorization. Do not add an ignore-regressions path or use an unrecorded phase change to bypass the initial limit.

The script checks limits in the supplied history. For a state directory it also stops when `history.jsonl` no longer starts with its committed copy. It cannot detect a rewrite that was committed. The auditor must verify carry-forward against `batchRecords`. This limitation is not permission to reset a counter.

## Approved rule changes

Theo approved two scoped rule changes on 2026-09-25 for batch
`recovery-continuation-go-checker-port-1`. They are saved in
`acceptanceRuleChanges` in `current.json`. The check script applies them only to
that batch id.

- **Opt-in crate rule.** An additive opt-in crate (`ts_goport`) can be accepted
  when there is no new loss in the protected tests and it has its own Go parity
  evidence. The inherited losses in the pinned R96 full result (290 original
  accepted names and 15 later-pass names, all in `ts_checker`) are reported but
  do not block. The inherited counts must match exactly, and the script pins the
  R96 hash and both counts as constants. The 290 include 14 names that were
  already ABSENT at R96. All other protected names must be present and run, and
  no protected PASS may be newly lost.
- **Unbound history rows.** Revisions 97, 98 and 99 were measured before their
  source was saved. They keep a null source and a null result, and get no credit.

On 2026-09-25 Theo also said: "Going forward, answer every question yourself."
Under that delegation, root extended both rules to batch
`recovery-continuation-go-checker-port-2`, and then to batch
`recovery-continuation-go-checker-port-3`, and then to batch
`recovery-continuation-go-checker-port-4`, and then to batch
`recovery-continuation-go-checker-port-5`, and then to batch
`recovery-continuation-go-checker-port-6`, and then to batch
`recovery-continuation-go-checker-port-7`, each time with the same pins and
scope. Each extension is a separate entry in `acceptanceRuleChanges`. The
records name root as the extender. This is not a new direct approval by Theo,
and it does not widen the rules.

Any other rule change still needs Theo's approval.

## Project target and reporting

Query core remains first. The milestone is complete ordinary diagnostics matching pinned Go, plus a deliberate type error reported correctly in a separate copy. Full type, symbol and replay parity remain requirements.

Hono remains the cross-project check. Run it after a recovered shared operation, at the Query milestone and once per full work day on the latest accepted compiler during continued work. Do not claim the current compiler passes Hono from an older run.

Every progress report states accepted passes retained or lost, exact diagnostic changes, whether ordinary Query completes and the source/date of the latest Hono check. New test coverage is separate. Unavailable diagnostics are not zero diagnostics.

## Setup ownership

Root owns these instructions, the saved state and the reset plan. During setup, `audit_accepted_roster` owns the small accountability check and its tooling tests. `reset_process_audit` reviews setup without editing it. This setup assignment does not authorize either agent to resume compiler work.
