# Typechecker accountability

These rules were installed on September 5, 2026, at Theo's request. They apply when the next goal starts. Compiler execution is currently paused. The machine-readable status is [typechecker-accountability-state.json](typechecker-accountability-state.json).

The [reset plan](typechecker-reset-plan.md) explains the failure and recovery choices. These rules control execution if an older plan conflicts with them. They do not change the full port requirements.

## Start or resume

1. Read this file, the saved state and the reset plan. Do this after a context reset as well as at goal start.
2. Check the user's current instruction. A historical active goal is not permission to ignore the pause. Theo's new goal can authorize the recovery block, but does not waive the acceptance rules.
3. Verify the candidate source and required evidence still exist. Do not rebuild a missing accepted baseline from the current compiler.
4. Reuse or create the regression auditor and independent reviewer. Give them this file and the saved state. Record their current agent names. Agent names can change across sessions. Their roles and limits cannot.
5. Select one primary implementer and record file ownership before any parallel work. Root owns the runtime queue and integration state. Keep the other compiler drafts frozen.
6. Record the recovery hypothesis, exact tests it must recover, current source and remaining revision budget before editing.

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

## Revision limits

- One recovery hypothesis permits at most two measured revisions.
- The initial recovery phase permits at most four measured revisions across at most two demonstrated causes.
- Failed and unaccepted revisions count. Record a candidate before running its checks. A repeat run of identical source does not become a new semantic revision, and does not reset a counter.
- After two measured implementation batches without useful ordinary Query progress, stop feature work and reassess the dependency path. During regression recovery, apply the cumulative recovery limit and report Query separately.
- A later assertion, changed error label, new passing control, trace, different agent or renamed batch does not reset these limits.
- At the cumulative limit, either required results pass or have individually approved Go-backed expectation updates, or implementation stops with the recovery comparison and remaining losses. A recorded cause or port gap does not clear a STOP. Do not renew the same experiment automatically.

Reaching a limit does not prove that restarting from green is cheaper. Use the recorded dependency comparison. If the evidence is insufficient, stop and ask Theo for direction.

## One batch record

Root maintains one state file and one record per batch. Update the state before starting a revision and after its measured result. Do not rely on conversation memory or subagent messages alone.

Before replacing `state.batch`, save its record at `docs/typechecker-batches/<batch-id>.json` and add that path to `batchRecords`. Keep the complete initial-phase `recoveryHistory` in the next batch. The auditor compares it with the prior saved records. Do not delete old revisions or start the history again at one.

The record must identify the source, hypothesis, changed scope, exact expected recoveries, commands, completed runs, result paths and hashes, ordinary Query outcome, latest Hono result, both independent verdicts and the next permitted action. Each verdict names its agent, batch and exact source. A verdict from another source is stale.

Keep test comparisons separate for the original accepted roster, later measured passes and new coverage. Keep corpus diagnostics, types, symbols and replay evidence separate from unit-test totals. Full acceptance needs the required corpus checks as well as regression checks. Missing evidence is STOP.

Do not store raw type graphs, private test bodies or large failure payloads in this file. Link the existing evidence. If an ignored evidence file is missing in a future checkout, stop and recover it from preserved records. Do not invent its contents.

## Automated check

The local entry point is `node scripts/check-typechecker-batch.mjs --help`. The script reads saved evidence and state. It must reject malformed or missing evidence, mixed source identities, lost or missing passing names, stale verdicts and STOP verdicts. Tooling tests use synthetic records and do not run the compiler.

Run the real check from the main repository root:

```sh
node scripts/check-typechecker-batch.mjs docs/typechecker-accountability-state.json
```

Run the tooling tests with all 14 named results visible:

```sh
node --test --test-isolation=none --test-reporter=spec scripts/check-typechecker-batch.test.mjs
```

The first version automatically compares the fixed 6,055 accepted names and the later 6,330 passing names. The regression auditor must also compare passing names added after that reference. Their starting evidence is in `additionalPassingResultsForAuditor`. Append later measured results there. The script does not itself prove this extra comparison, corpus parity, Go equivalence or Query completion. The independent verdicts must address those requirements. A script PASS alone is not compiler acceptance.

This is a required pre-acceptance check, not a replacement Cargo runner. It does not prevent someone from calling Cargo or Git directly, and it cannot prove that a human-authored review is true. Root must honor the rules for actions outside the check. Keep existing resource limits and actual tool permissions.

The current invocation must return STOP because no recovery batch is authorized or accepted. A successful setup test must not clear the real state.

The first version of the check supports only `phase: "initial-recovery"`. Keep its complete revision history. Before using it for a later phase, review an explicit extension of the check. Do not rename the phase, reset its history or increase a state value to bypass the recovery limit.

The script checks limits in the supplied history. It cannot detect that someone discarded earlier state or rewrote its history. The auditor must verify carry-forward against `batchRecords`. This limitation is not permission to reset a counter.

## Project target and reporting

Query core remains first. The milestone is complete ordinary diagnostics matching pinned Go, plus a deliberate type error reported correctly in a separate copy. Full type, symbol and replay parity remain requirements.

Hono remains the cross-project check. Run it after a recovered shared operation, at the Query milestone and once per full work day on the latest accepted compiler during continued work. Do not claim the current compiler passes Hono from an older run.

Every progress report states accepted passes retained or lost, exact diagnostic changes, whether ordinary Query completes and the source/date of the latest Hono check. New test coverage is separate. Unavailable diagnostics are not zero diagnostics.

## Setup ownership

Root owns these instructions, the saved state and the reset plan. During setup, `audit_accepted_roster` owns the small accountability check and its tooling tests. `reset_process_audit` reviews setup without editing it. This setup assignment does not authorize either agent to resume compiler work.
