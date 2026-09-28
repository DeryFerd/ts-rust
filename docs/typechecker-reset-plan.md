# Reset the typechecker port

Date: September 5, 2026.

Status: the initial recovery trial is complete. Theo has authorized continued work under the standing authorization in the [accountability rules](typechecker-accountability.md). The [current state](typechecker-state/current.json) records the complete history. This plan does not discard existing work or accept the current compiler.

The four-revision trial and seven-role limit below describe the initial plan. The standing continuation authorization supersedes those execution limits for later work. Protected results, source preservation, ordinary project inputs and complete project requirements remain in force.

2026-09-28: Theo retired the legacy cargo roster ("i approve any rule changes that allow removing the legacy code", state note `legacy-removal-rule-approval-2026-09-28`). The protected results are now goport's own tests per name and the gate items, compared with the last accepted revision ([protected set](typechecker-accountability.md#protected-set)). The 6,055-name tables, the green reference commit and the first work block below are history of the legacy checker. They do not govern new batches. Where the later sections say accepted tests, accepted selection or corpus results, use the goport protected set.

## Decision

I let the integration compiler accumulate regressions while Query stayed incomplete. I counted the failures, but did not use them to stop the work. That is my execution failure.

The next objective is verified integration, with Query core as the first project target. Do not add more feature patches to the current failing compiler.

Use commit `5c7c7bd20cb45ebc8f2171eed8478fa2797e8343` as the fixed acceptance reference. Preserve the current compiler as a separate candidate. First establish whether a small number of shared defects can restore its accepted behavior. If that does not hold, rebuild the integration compiler from the green reference and reuse only complete, tested operations.

A restart is an option, not a proved shortcut. The current HEAD has 810 commits after the common ancestor. Throwing those changes away could repeat useful work. Keeping all of them without restoring correctness has already failed.

## What the evidence says

These are saved, completed results. No compiler or test ran during this reset audit.

| Source | Measured result | Original accepted tests |
| --- | --- | --- |
| Accepted commit `5c7c7bd2` | 6,055 PASS, 0 FAIL | All 6,055 present and passing |
| Earlier full candidate, fingerprint `162fccf9` | 6,330 PASS, 446 FAIL | 5,757 PASS, 284 FAIL, 14 ABSENT |
| Last full candidate, fingerprint `53de487d` | 6,284 PASS, 498 FAIL | 5,716 PASS, 325 FAIL, 14 ABSENT |
| Current candidate, fingerprint `a6c6cb92` | Focused run only: 96 PASS, 25 FAIL | Selected 75: 58 PASS, 17 FAIL |

The last full run lost 49 previously passing tests and recovered no old failure. Of those losses, 41 belong to the original accepted tests. The current focused run rechecked 14 of the 49, and all 14 still fail. It did not check the other 35. All 49 remain unresolved. Do not present the historical full result as a full run of the current source.

The two latest recoveries are new controls. They recover neither an original accepted test nor one of the 49 losses.

Query's latest ordinary result exactly matches the preceding result. It stops at `INV.SOURCE.DECLARED_TYPE`. Complete diagnostics, types, symbols and replay results are unavailable. An unavailable diagnostic result is not zero errors.

Hono has no verified result for the current compiler. Its last saved ordinary check stopped at `R01.RELATION` after about 320 seconds. Isolated file counts do not establish complete project checking.

Sources: [baseline audit](../target/query-core-reset-baseline-audit.md), [execution audit](../target/query-core-reset-process-audit.md), [latest focused result](../target/query-core-selected-indexed-repair-4-focused-result.md), [Hono record](../target/query-core-next-hono-cross-check.md).

### What the accepted baseline does and does not prove

The 6,055 tests cover 120 harnesses: checker library and public tests, compiler library tests, fixture tests and an original class fixture. The saved source and logs still exist. The checkout at `target/agent-worktrees/wave202/core-class-call-integration` is clean at the measured commit.

This was a green regression selection, not all workspace tests or full TypeScript support. Its separate corpus run had 423 exact diagnostic variants out of 511 executed and 60 exact semantic variants out of 95. Some old fatal results and symbol mismatches remained. Preserve its exact results without calling the whole corpus green.

The report titled "Current accepted baseline" describes a failed later candidate. Treat it as a historical comparison checkpoint. Its title must not determine acceptance.

## What went wrong

### An incomplete state became visible to normal callers

The deferred mapped-type constructor published a new Deferred state under the normal alias cache key. Existing cache readers expected completed operands. Some member readers could reach the old worker without completing those operands.

The first live batch lost 12 old passes. I continued adding display, member, value, context and replay changes to that same candidate. The new state therefore required an expanding set of repairs before ordinary callers could use it.

This explains the integration failure pattern. It does not prove the cause of every lost test. [Execution audit](../target/query-core-reset-process-audit.md#what-went-wrong)

### The short loop used the wrong comparison

Retaining the preceding candidate's 94 passes did not restore the accepted compiler. Narrow reviews proved individual changes were reasonable, not that the whole operation worked.

The focused selection covered only 14 of the later 49 losses. Compiling the library test executable did not execute its thousands of tests. The full behavior check came after several changes to shared state.

The two-batch stop rule also failed in practice. I treated another trace or a later failing assertion as enough reason to continue the same experiment. Query did not improve.

### The Rust design adds failure paths that need a separate justification

The pinned Go checker resolves these operations lazily in shared checker state. For example, an already resolved indexed type node returns its cached type. Mapped property resolution uses normal resolution state and publishes the selected result.

The current Rust path also plans reads, retains source proofs, replays them, and transports requests for more work through error values. These extra steps create more ways to reject a valid request.

One concrete audit found three live signature checks that omit available source context. A shared boolean validator then converts a cache error to `false`, and an outer caller reports a general signature error. This loses the reason for failure. It is a proved API problem, but not yet the proved cause of Query's stop or the 20 similarly named failures.

The architecture needs review at the complete operation level. Adding one more accepted state to one validator is not a substitute. [Pinned Go operation](../target/query-core-go-selected-indexed-operation.md), [signature context audit](../target/query-core-mapped-signature-demand-transport.md)

### Work outgrew integration

The current checkout has 46 dirty files. Source paths contain 11,154 added lines and 1,395 deleted lines. These counts include tests located inside source files. At least nine behavior areas overlap in the reports. They are not independent changes ready to merge.

The 50 saved Query patches include drafts, traces, superseded changes and already committed work. They are not a restart script. Repeated internal approvals, hashes and reports also consumed effort without changing the integration decision. [Change audit](../target/query-core-reset-change-audit.md)

The records do not measure total coordination time. I cannot claim that more agents improved the rate of accepted progress.

## What to take from the Bun port

Bun kept its initial Rust port close to the existing implementation and reused the existing tests. It separated porting from later redesign. It also used independent review and changed its process when agents started making workarounds to satisfy compilation. Those lessons fit this project better than copying its worker count. [Bun's port report](https://bun.com/blog/bun-in-rust)

For ts-rust, port Go's algorithms and state transitions first. Use Rust types and stable IDs to represent them safely. Require a concrete reason for a different evaluation order, cache rule or recovery path. Do not make a new planning and proof system a prerequisite for each TypeScript feature.

This is not permission to delete ownership checks or accept malformed caches. Full diagnostic, type and symbol parity with pinned Go remain requirements.

## First approved work block: choose a recovery path

This block has one purpose: determine whether to repair the current compiler or recover integration from the green reference. It is not another Query feature batch.

### 1. Preserve and reproduce

- Save the current tracked changes, all ten untracked files, base commit and source fingerprint. Save the relevant ignored logs, patches, result ledgers and runners separately. Verify the saved source matches the candidate. Do not reset the original checkout.
- Reproduce the exact accepted selection at `5c7c7bd2`, using fresh logs and a separate build target. Reuse the existing runner and resource limits. Do not run the historical wrapper unchanged because its output paths belong to the saved evidence.
- Run the same acceptance comparison on frozen `a6c6cb92`. It has no current full result. This establishes which old failures remain before a recovery patch.
- Measure unchanged Query on the green reference through its existing project runner. Establish whether the older compiler stops earlier and what later work is required. Keep the already recorded current Query result for comparison.

If the accepted source cannot reproduce its saved result, resolve the source, input or environment difference before feature work. Missing and unrun test names are failures of the acceptance check, not passes.

### 2. Classify failures before choosing repairs

Use one ledger keyed by exact test name. Include the original 6,055 accepted names, all 6,330 names that passed the earlier full run, and subsequent newly passing tests. Keep accepted results and later measured passes in separate columns. Eight of the 49 recent losses are outside the original accepted roster. A restart must not remove these later results from the accounting.

Separate:

- Incorrect diagnostics, types, symbols, recovery or repeat behavior.
- An old unsupported-behavior expectation that new, correct support invalidates.
- Internal state assertions that need comparison with Go's actual operation.
- Missing or renamed tests without an explicit replacement mapping.

Error names alone do not establish a shared cause. For the leading proposed cause, require an existing failing public case, the responsible source path, the relevant Go operation and a testable explanation of the state error. Keep unproved groups marked unknown.

An expectation change requires a concrete pinned Go comparison. It gets a focused review and an explicit old-name mapping. No blanket approval for cache tests, unsupported tests or renamed tests.

### 3. Test one recovery hypothesis

Choose one shared regression with a demonstrated cause. Prefer a cause also on Query's measured path, but do not assume that connection. The writer must explain the entire operation before patching it.

Permit one repair with at most two measured revisions. Name the exact accepted tests it must recover before editing. No new feature routing, test deletion or expectation weakening. Run affected positive and negative controls, the affected accepted tests and unchanged Query. If the focused checks establish the claimed recovery, run the full accepted selection and corpus comparisons even if Query remains incomplete. A focused result cannot establish that there are no new losses elsewhere.

In parallel, an audit agent estimates the dependencies needed to implement the same operation on the green source. This is read-only work, not a competing implementation.

### 4. Make a recorded choice

| Evidence | Decision |
| --- | --- |
| A complete repair restores an identified group of accepted tests, adds no new losses, and the remaining groups have bounded repair explanations | Continue regression recovery within the cumulative limit below. Do not add Query features or accept the compiler until required results pass or have individually approved Go-backed expectation updates. |
| Two measured revisions restore no accepted behavior, or require another chain of exceptions for incomplete state | End this repair hypothesis. Choose green-source recovery only if the dependency comparison supports that decision. One failed hypothesis does not prove the whole compiler is cheaper to rebuild. |
| Results remain insufficient to justify either route | Report the missing evidence and stop the experiment. Do not silently extend its budget or start more feature branches. |

This comparison is why I do not claim a full restart is already proved fastest. The green source fixes the correctness reference. The bounded experiment determines the implementation path.

Do not make this block an audit of all 810 commits. Use the existing failure ledger, investigate one leading cause, and estimate only that operation's dependencies. If this investigation cannot demonstrate a cause, report that limit before any repair starts.

The initial recovery phase has a cumulative limit of four measured revisions across at most two demonstrated causes. Failed and unaccepted revisions count. At that limit, either required results pass or have individually approved Go-backed expectation updates, or implementation stops with the recovery comparison and remaining losses. A recorded cause or port gap does not clear a STOP. Do not renew the same experiment automatically. A small recovery cannot fund an unlimited series of repairs.

## Implementation after the recovery decision

### Port one complete operation

For each operation, the writer records one short description:

- The real source caller and corresponding pinned Go functions.
- Inputs, lexical owner, mapper and shared checker state.
- Cold, resolving, resolved and error states where applicable.
- Member publication, selected value evaluation and cache publication order.
- Recursive entry, diagnostic recovery and repeated-call behavior.
- Every normal caller that can observe the new state.

For mapped and indexed types, the unit is the connected operation: construct the instance, obtain names, resolve the selected value, report a missing property, recover, and repeat correctly. Unrelated property values must not become required merely to pass validation. Generic deferral and recursive cases need their Go behavior preserved.

Prefer direct shared-state operations where Go uses them. If a reader can request more work, use an explicit result that distinguishes that request from invalid state. Do not flatten the distinction to a boolean. Preserve the caller's context and instantiation session.

First prove the smallest complete operation. Do not approve a checker-wide rewrite from this audit alone.

### Use one repeatable loop

1. Build implementation and test code in the existing profile.
2. Execute focused positive, negative, recursive and repeated-call cases. Compare the semantic cases with pinned Go.
3. Run unchanged ordinary Query on the same source. Keep configs, roots, libraries and inputs fixed.
4. Run the goport tests (`scripts/goport/goport-tests.sh`) before another semantic batch that changes shared planning, caches, mapped state or request transport.
5. Before accepting a batch, run the whole goport protected set and compare it with the last accepted revision, per test name (`compare-tests.py`), per gate item (`gate-compare.py`), per LSP and API oracle request (`oracle-compare.py`) and per np-suite test. Every run of the source counts. Run formatting and lint checks required by the repository.
6. Commit an accepted batch before starting the next operation. Keep one integration owner and one integration branch.

Reuse existing logs and result parsers. Each batch needs one record: source identity, commands, normal completion, exact comparison and review result. One owner performs each mechanical check. Retain actual tool permissions, read restrictions and resource limits. Remove duplicate internal permission handoffs.

Any new unexplained lost pass stops the batch. Repair or withdraw that batch before adding work. A new passing test cannot compensate for a lost one. Each accepted revision's results become the base for the next, so every earlier pass stays protected. Any behavior not yet restored remains an explicit port gap, not an accepted removal.

After two measured implementation batches without a useful change in ordinary Query, stop feature work and reassess the dependency path. Failed and unaccepted batches count. During regression recovery, use the stricter cumulative limit above and report Query separately. A new error label or a later assertion does not count as project completion or restart either counter.

### Check the cache contract explicitly

Separate user-visible repeatability, required type and symbol identity, bounded resource growth, and corruption detection. An exact internal cache-entry count is not automatically a TypeScript semantic rule. It can still protect a real identity or growth invariant.

Compare disputed behavior with Go and the documented Rust requirement before changing an assertion. Do not skip cache validation merely because Go has an early cached return. Decide which checks belong at publication, which remain necessary on reads, and which are optional debugging checks through the bounded operation trial.

## Query and Hono milestones

The immediate milestone is unchanged:

1. Unchanged Query core completes ordinary project checking. Its complete diagnostic result matches pinned Go, including locations and messages.
2. A separate copy with a deliberate type error produces the expected Go-matching diagnostic. The original input remains unchanged.
3. All goport protected results remain accounted for and passing, except individually proved expectation updates and checked name maps.

Do not replace this with isolated-file counts or an empty partial diagnostic snapshot.

Hono stays the cross-project check. Run it after a recovered shared operation and at the Query milestone. If Query work spans a full work day, run Hono on the latest accepted compiler once that day. Do not interrupt each small edit for a five-minute Hono run, and do not leave its status unmeasured for several days.

After Query diagnostics pass, close Query type and symbol mismatches. Then use the same process for Hono diagnostics and semantic parity. Keep all measured project results in the regression set.

For the rest of the port, use missing Go behavior and conformance failures to order complete operations. Likely areas include generic inference, assignability, conditional and mapped types, overloads, contextual typing and control-flow narrowing. That is a list to measure, not a claim that every area is currently missing. Add module, configuration and standard-library work when it blocks ordinary project checking. Do not switch to new demo libraries to avoid a hard failure.

## Parallel work and file ownership

Use at most seven active roles during recovery. Start fewer when there are fewer independent questions.

| Role | Ownership |
| --- | --- |
| Root | Integration decisions, runtime queue and one result ledger. No concurrent compiler edits. |
| Primary implementer | All production changes for the selected operation and its focused test changes. |
| Independent reviewer | Read-only review of the complete operation, tests and measured results. |
| Go comparison agent | One assigned operation report. No Rust edits. |
| Regression audit agent | Exact test comparison using the existing parser. No expectation changes. |
| Caller-state audit agent | One assigned context, cache or error-path question. Report only. |
| Recovery-cost audit agent | Dependency estimate for reusing the operation on green source. Report only. |

Give each audit a distinct output file and a decision it must support. Stop completed audits. Add agents for genuinely separate failure causes, not overlapping reports or speculative production patches.

Forty workers can help later with independent Go operation maps, conformance groups and reproductions. Forty compiler writers do not help while shared checker state and integration remain broken. Expand production parallelism only after green integration establishes independent file and API ownership. A measured gain in accepted behavior, not agent count, determines whether to keep the extra workers.

## Status reporting and stop conditions

Every batch report must answer:

- Which goport test passes were retained, recovered, lost, absent or unrun, and which gate items regressed?
- Did ordinary Query complete? What exact diagnostic difference changed?
- When was Hono last run, and on which source?
- Does the complete operation pass, including negative and repeated-call cases?
- What is the next decision, and what evidence will end the current experiment?

Report new coverage separately. Mark unrun results as unrun. Do not call a static review, successful build or later stopping point a completed feature.

I am confident that this plan stops the current failure pattern. I am not yet confident which recovery source is cheaper, which patch will complete Query, or how long full parity will take. The first work block is designed to answer the recovery question without another open-ended implementation run.

Compiler implementation remains stopped until Theo sets the goal. Read the accountability rules and current state before resuming.
