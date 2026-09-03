# Typechecker demo status

Updated 2026-09-03. Neither Query nor Hono has passed a full Rust type check.

The [execution reset](typechecker-demo-plan.md#execution-reset) now controls
the work. Root is the sole implementer, with one reviewer. Query core is first.
All other production drafts are frozen. Hono remains a periodic cross-project
check. All earlier worker runs have closed. Root owns the integration branch
`query-core-integration` and its build target.

## Latest checkpoint

The [shared member-resolution task](query-core-member-resolution.md) now has
a [small Go-checked baseline](../target/query-core-merged-members-baseline-5-result.md).
It is committed on the integration branch as `37179715d`. The two complete
Rust tests compile, then reject the merged generic `Emitter` base. Go accepts
the positive input and reports exactly TS2322 for the separate negative input.
No production code changed in this block. Query and regression results below
are still the last complete measurements. The reviewer and root identified
the required common operation across defaults, bases and selected members.
The next block implements that operation, not another admission guard.

The [base-resolution repair](../target/query-core-base-resolution-repair-1-result.md)
is committed on the integration branch as `031420b74`. The complete diagnostic
selection now finishes without a process crash. A bounded native backtrace
identified repeated generic target and base resolution in
`conditionalTypeSimplification.ts`. The repair follows Go's separation of
target identity, base publication and later heritage constraint checks.
The full schema tests still fail. This is not conditional-type acceptance.

All 6,325 passes from the previous integration test run remain. Against the
accepted compiler, counts are unchanged: 5,789 of 6,055 passes retained,
253 failures and 13 absent exact names. Every loss remains a promotion blocker.
One debug-order assertion now passes, which is not a proved semantic gain.

The [complete corpus comparison](../target/query-core-base-resolution-repair-1-corpus-result.md)
retains 400 of 423 previously exact diagnostic records. There are 23 changed
exact records and 12 fatal records. One changed record keeps an exact status
but has a different diagnostic path. These results remain blocked. The previous
integration run aborted, so this comparison cannot attribute all losses to the
new repair. All 95 type/symbol variant rows match baseline 2. Accepted retention
stays at 57 of 60 diagnostic records, 52 of 55 type metadata rows and 58 of 62
symbol metadata rows. Metadata equality does not independently prove rendered
payload parity.

[Unchanged Query](../target/query-core-base-resolution-query-1-result.md)
still completes 2 of 23 isolated roots. Ordinary checking does not complete.
All 244 checking records, outcomes, diagnostics and graph data are unchanged.
The earlier caller observation still identifies full global-annotation
preflight as the rejecting path. The base needs merged generic class/interface
handling, not only an interface-heritage guard change.

All runtime checks are closed. The preserved six-file reference-flow draft
remains uncommitted. No expectation changed, and nothing was promoted to the
accepted compiler. One implementer and one reviewer remain the work model.

Next, implement the [shared declared-value and inherited-member operation](query-core-member-resolution.md)
with its real source context, base substitutions and state. Do not add the
isolated conditional admission follow-up. Keep every regression open until it
is repaired or has concrete pinned-Go evidence for a changed contract.

## Previous implementation checkpoint

The integration branch is at `de557d99c`. The merged global variable-and-namespace
repair is committed, following a test-helper rename in `6f7319419`. The separate
six-file reference-flow draft remains uncommitted. Nothing is promoted to the
accepted compiler. Root remains the sole implementer, with one read-only reviewer.

The [new test run](../target/query-core-variable-namespaces-3-result.md) passes
all three variable-and-namespace cases. They check script merging, global
augmentation, local shadowing, exact types and owners, deliberate diagnostics,
cold queries and replay. The [pinned Go comparison](../target/query-core-variable-namespaces-go-1/result.md)
confirms all three positive cases and the exact negative diagnostics.

The library has 5,065 passes and 372 failures. The 12 public targets have 40
passes and six failures. Every one of the first run's 5,087 passes remains, and
the two new namespace failures now pass. Against the earlier reference-flow
run, one library test fails only because identical HashMap entries print in a
different order. The reviewer checked both complete state dumps. No expectation
changed. The three earlier unsupported-expectation losses remain unresolved.
Four public property-truthiness failures still need a pre-draft comparison.
Two type-only namespace tests now compile, but stop at an unsupported callable
expression. Their target has no result in the compared earlier selections.

[Unchanged Query](../target/query-core-variable-namespaces-query-1-result.md)
still completes only 2 of 23 isolated roots. The ownership error is gone.
Ordinary checking now stops at the optional `send` method in Node's `process.d.ts`.
All diagnostic snapshots and the full input graph are unchanged. This is no
complete-root or diagnostic gain. The results cover the combined working tree,
not the namespace commit in isolation. All measured file bytes remain unchanged
after the two commits, and all runtime checks have closed.

The next check follows the shared inherited-interface path. Rust's global-read
helper rejects lazy lookup for interfaces with heritage, and `Process` extends
`EventEmitter`. Go separates member-table resolution from the types of named
methods. Confirm the actual caller before changing it. Complete that lookup
path instead of adding an isolated `send` rule. Complete named and nested write
state also remains unfinished.

The last full integration selection at `f38238f76` had 5,068 library passes with
369 failures and 687 public passes with 24 failures. Against the accepted checker
selection, 248 old passes failed and 12 names were absent. That full selection,
the compiler tests and the original corpus must run again before this draft can
be promoted. Older results are not fresh passes for the draft.

## Earlier checks

Against the last accepted compiler, the
[complete checker baseline](../target/query-core-accepted-checker-baseline-1-result.md)
retains 5,252 of 6,055 selected passes, loses 252, and leaves 551 missing or
unrun. All 110 accepted public checker targets now ran. The gaps are 12 absent
names and 539 unrun compiler and fixture tests. Comparisons with recent failing
candidates below do not replace this accepted baseline.

Two failures are now explained by a concrete Go comparison and corrected in
`2bf54614a`. Those tests demanded complete member caches from an identity-only
query. The corrected tests pass with all earlier behavior checks intact.
The first production batch, committed as `6652447c7`, restores two more old
behavior tests. [Regression check 2](../target/query-core-interface-regression-2-result.md)
retains every pass from the frozen checker baseline. Current accepted-name
checker totals are 5,256 passes, 248 failures and 12 absent names.

The [complete accepted test comparison](../target/query-core-accepted-complete-baseline-1-result.md)
now covers every accepted harness. Of 6,055 old passes, 5,792 remain passing,
250 fail and 13 exact names are absent. All 285 old compiler tests pass.
Fixture checks add two old failures and one absent name. Causes and rename
equivalence remain unproved where the records say so. Nothing is promoted.

[Unchanged Query after this repair](../target/query-core-interface-demand-query-1-result.md)
has no gain or loss. All 244 non-runtime records match Query 44, including
the full input graph, every outcome and every diagnostic. Ordinary checking
still stops at the class in `timeoutManager.ts`. This is one production batch
without a Query improvement after the reset.

Two bounded observations now identify the next operation. The
[class observation](../target/query-core-class-annotation-observation-1-result.md)
did not reproduce the earlier type-literal cache failure. Its preserved union
change reached a later unsupported variable read. The
[variable observation](../target/query-core-variable-symbol-observation-1-result.md)
identified the ordinary variable reader and a merged global variable with no
instantiation state. All 24 outcomes and diagnostics match the first observation.
Neither observation gained a complete root. The ambient global-value draft then
passed [all 39 focused tests](../target/query-core-ambient-global-values-1-result.md).
Its [unchanged Query run](../target/query-core-ambient-global-values-query-1-result.md)
clears the variable rejection but stops at the enclosing binary expression.
All diagnostics remain unchanged. Root 0 reaches a different unsupported DOM
type. No complete root or project check was gained.

The first regression build found a missing field in a library test helper before
tests ran. The extra field was removed. The [corrected full selection](../target/query-core-ambient-global-values-regression-2-result.md)
compiled and ran all 6,148 cases. It lost exactly three library passes and retained
every public result. That rejected draft had 5,065 library passes with 372 failures,
and 687 public passes with 24 failures. Against the accepted checker selection,
5,253 passes remain, 251 fail and 12 names are absent. Earlier compiler and fixture
results are not fresh results for this draft.

The new global route incorrectly forced lazy member checking for all ambient
globals. It also changed the existing poisoned-variable error. Both are repaired.
[Regression check 3](../target/query-core-ambient-global-values-regression-3-result.md)
recovers all three lost passes. Every earlier integration result is retained.
Current counts are 5,068 library passes with 369 failures and 687 public passes
with 24 failures. Accepted checker counts return to 5,256 pass, 248 fail and 12
absent names. All 39 focused tests pass. [Fresh unchanged Query](../target/query-core-ambient-global-values-query-2-result.md)
still completes only 2 of 23 isolated roots. Ordinary checking stops at the same
binary condition, with no diagnostic gain. Restoring full member demand returns
root 0 to its earlier unsupported DOM reference. No complete root is lost.

The [remaining failure groups](../target/query-core-ambient-global-values-regression-3-failure-groups.json)
include 57 operation rejections, 15 incorrect or missing results, 26 cache or state
assertions, 27 old unsupported-boundary expectations and 25 other error-contract
mismatches. Another 98 remain unknown. These groups are observations, not cause
explanations or approved expectation changes. Nothing is promoted. All runtime
checks have closed. After two batches without a complete Query gain, the next
work must connect condition checking and class branch flow as one operation.

## Measured results

Full-project progress is stalled. Focused tests still recover cases, but neither
project has gained a complete isolated root in the latest comparisons.

| Check | Latest result | Change |
| --- | --- | --- |
| Query, base-resolution repair | 2 of 23 isolated roots complete | All 244 checking records unchanged. Ordinary checking remains unsupported |
| Full diagnostic corpus | 511 variants completed. 400 of 423 old exact records retained | Process crash fixed. 23 old exact records changed and 12 fatal records block promotion |
| Current accepted test selection | 5,789 old passes retained, 253 fail, 13 absent | All 6,325 previous integration passes retained. No accepted loss cleared |
| Query, merged variable-and-namespace repair | 2 of 23 isolated roots complete | Ownership error cleared. Ordinary checking stops at a method signature in process.d.ts. All diagnostics unchanged |
| Variable-and-namespace tests | Library 5,065 pass, 372 fail. Public 40 pass, 6 fail | All three new cases pass. All 5,087 first-run passes retained. Existing failures still block promotion |
| Query, reference-flow draft | 2 of 23 isolated roots complete | Ordinary checking fails with SymbolNotOwned. All diagnostic records remain unchanged |
| Reference-flow draft tests | Library 5,066 pass, 371 fail. Selected public cases 12 pass, 4 fail | Three new cases pass. Three previous library passes fail. One previous failure passes. Nothing promoted |
| Query, interface repair | 2 of 23 isolated roots complete | Every outcome and diagnostic matches census 44. Ordinary checking still stops |
| Query, current bounded observations | 2 of 23 isolated roots complete | Ordinary checking reaches a merged global-variable rejection. No diagnostic gain |
| Query, repaired ambient global values | 2 of 23 isolated roots complete | Variable rejection cleared. Ordinary checking still stops at its enclosing binary expression. No diagnostic gain |
| Ambient global-value regression check 3 | Library 5,068 pass, 369 fail. Public 687 pass, 24 fail | All three new losses repaired. Every previous integration outcome retained. All 39 focused tests pass |
| Query, separate method candidate 43 | 2 of 23 isolated roots complete | Five roots now fail internal type-literal checks. Candidate remains excluded |
| Hono, census 26 | 33 of 188 isolated roots complete | Every outcome and diagnostic matches census 25 |
| Accepted checker baseline 1 | Library 5,067 pass, 370 fail. Public 669 pass, 27 fail | All 111 harnesses completed. 252 accepted passes lost, 12 names absent |
| Interface regression check 2 | Library 5,068 pass, 369 fail. Public 673 pass, 24 fail | No baseline pass lost. Two behavior repairs, two test-contract corrections and one new passing case |
| Complete accepted selection | 5,792 old passes retained, 250 fail, 13 absent | All 120 accepted harnesses checked. Original corpus selections remain unrun |
| Return-context repair, six public targets | 19 pass, 0 fail | All three lost public passes restored |
| Checker library, return-context repair | 5,064 pass, 373 fail | Both lost library passes restored. Every outcome matches run 54 |
| Shared candidate, integration 2 | Library 5,067 pass, 370 fail. Public 239 pass, 35 fail | Three library recoveries. No old pass lost against runs 54 or 56 |

An isolated root is one original entry file checked on its own. These counts
are not full-project passes or percentages of TypeScript support.

The shared candidate's Query 44 run has finished. It still has two complete
roots and 21 unsupported roots. All 23 diagnostic records, the ordinary result
and the full graph match Query 41. One root reaches a different unsupported
operation. The other 22 complete outcomes match. No complete root was gained.

[Query 41](../target/wave202-query-combined-census-41-result.md) restores
`subscribable.ts`, lost in Query 38. The six `.bind(this)` call invariants are
gone. The other five affected roots return to their earlier unsupported errors.
All 23 raw diagnostic records match Query 36, and 22 full root outcomes match.
The remaining `utils.ts` outcome differs but is still unsupported. Ordinary
checking still stops in `timeoutManager.ts`. This is a regression recovery,
not a new complete root against the earlier best result.

[Query 37](../target/wave202-query-combined-census-37-result.md) gets five roots
past the shared heritage error and stops at a later method in `timeoutManager.ts`.
[Query 40](../target/wave202-query-combined-census-40-result.md) checks the real
`replaceAt<T>` body, then stops at the following class. Both repairs branch from
the earlier combined candidate. Their changes still need combined verification
with the Query 41 repair.

[Hono 26](../target/wave202-hono-combined-census-26-result.md) keeps the same
33 complete roots. Ordinary checking still fails in `http-exception.ts`.
The `basic-auth` call failure is in `Promise.all`. Its special call path
rejects valid merged library declarations. That repair is separate from the
ordinary-check property-context repair.

[The return-context repair](../target/wave202-query-return-context-repair-1-result.md)
restores all five passes lost in Tests 56. All 5,437 library outcomes match
Tests 54 exactly. All 19 selected public tests pass, including the new control
that requires return-context inference when arguments supply no type candidate.
Against the older accepted set of 4,839 library names, 4,598 pass, 231 fail,
and 10 exact names are absent. The remaining library failures and original
corpus regressions still prevent acceptance of this candidate.

The [original corpus checks](../target/wave202-measured-core-corpus-1-result.md)
also reject the earlier combined candidate `b4fe2618`. Its diagnostic selection aborts with a stack
overflow and produces no final scorecard. The semantic selection stays at
60 exact matches out of 95 executed variants, but loses three previously exact
cases and gains three others. It also has two supported mismatches.

## Preserved work at the reset

This is the state before the reset. These branches and drafts are preserved,
not released for further implementation or integration. Only checks already
started may finish.

1. Run both projects on one combined candidate. Commit `eb996907` contains the
   Query 41 repair, indexed writes, merged-interface cache validation and TS6504
   path handling. Its [complete test gate](../target/wave202-project-integration-2-tests-1-result.md)
   ran all 5,437 library cases and 274 public cases in 94 targets. Three library
   cases recovered, with no old pass lost against runs 54 or 56. Query 44 has
   finished without a complete-root gain. Hono 26 follows on the same frozen
   source and build target. No candidate is accepted.
2. Repair Query's class and method path. [Query 43](../target/wave202-query-combined-census-43-result.md)
   has no complete-root gain. Its separate method candidate has five internal
   type-literal errors and a later unsupported variable operation. Its test gate
   also loses two inherited-constructor passes. The constructor reader accepts
   inherited plans but only selects written constructors. That repair is active.
   The new replay test separately compares operational counters and unordered
   debug output. Its correction must preserve actual semantic state and results.
3. Keep Hono's ordinary check moving. [Hono ordinary 6](../target/wave202-hono-ordinary-6-result.md)
   still fails cached-type validation in `http-exception.ts`. The reviewed
   constructor repair now retains the source query through annotation demand,
   candidate validation and argument checks. Its full library and nine public
   targets must run before the next ordinary Hono check.
4. Complete shared async and Promise behavior. The
   [callable syntax repair](../target/wave202-callable-syntax-authenticity-5-result.md)
   passes all four new controls and recovers four old ownership checks, with no
   old pass loss. It is ready for a later combined candidate. Parameterized async
   arrow support is still being implemented. The
   [Promise.all tests](../target/wave202-hono-merged-promise-call-2-result.md)
   both still fail. The next repair must use canonical generic inference and
   mapped tuple results. Returning an array for the inline tuple is incorrect.
   [Optional catch calls](../target/wave202-optional-call-3-result.md) also remain
   incomplete after the cold callback proof repair.
5. Preserve working native cases while these features change. The
   [second conditional-schema repair](../target/wave202-conditional-simplification-stack-2-result.md)
   restores all six library regressions and no longer overflows the stack.
   Its original fixture and both full public tests still fail. The next fix
   reuses existing alias-conditional validation in method members. Separate
   repairs address lazy Exclude branches and static class self construction.
   The TS6504 fix retains its measured gain of 61 exact semantic variants
   instead of 60. None of these results proves a full-project pass.

The next useful results are successful ordinary project checks, additional
complete roots, and preserved native diagnostics. More commits or focused test
passes do not replace those results. Parallel patches and review have outpaced
integration. The project-check cycle needs to stay short, while a separate
regression track protects previously working behavior.

## Demo requirement

Query is the first full-project target. A useful demo must finish the unchanged
project with matching native diagnostics, no unsupported operation and no
internal error. It must also preserve the negative tests that require errors.
Hono has the same requirement. A later first error or an isolated-root count
does not meet it.

The immediate measure is the result from the shared build, not the number of
active workers. The current runner permits three concurrent Cargo jobs. Source
work can run in parallel, but another source worker cannot remove that test
limit. Query 41 spent 1m 50s building and 18.931s checking. Query 43 spent
2m 19s building and 25.390s checking. Reusing one build target and combining
library and public tests reduce repeated setup. No build-speed improvement is
claimed until it is measured.

## Earlier checkpoints

[Replacement Query 34](../target/wave202-query-combined-census-34-result.md)
ran after Query 35. It tests the class repair and has 21 unsupported roots
with no invariant failures. Five roots now get past their prior `removable.ts`
failure and stop at a heritage clause in `timeoutManager.ts`. The constructor
failure in `mutationObserver.ts` also clears, exposing an import-alias limit.
All 244 records and project inputs match Query 33. The census took 18.684
seconds after a 1m53s build. No additional root completes.

[Query 35](../target/wave202-query-combined-census-35-result.md) checks the
callback repair against Query 32. It still has 20 unsupported roots and one
invariant failure. Only `hydration.ts` changes, from an unsupported function
body to the optional call `thenResult?.catch?.(noop)`. The other 22 outcomes
and all recorded project inputs match. The census took 18.370 seconds after
a 1m54s build. This source does not include the separate class-condition fix.

[Query 32](../target/wave202-query-combined-census-32-result.md) completed all
23 roots and 244 records with unchanged project inputs. It has 20 unsupported
roots and one invariant failure. Five roots now stop at the `Math` reference
in `removable.ts`. `mutationObserver.ts` reaches a constructor guard that
rejects its legal trailing comma. No complete root was gained or lost.
The ordinary `timeoutManager.ts` failure is unchanged. The census took 20.009
seconds after a 2m05s build.

[Query 33](../target/wave202-query-combined-census-33-result.md) then tested
the class-global repair. It still completes only two roots. The five shared
`removable.ts` failures changed from unsupported reads to class invariants.
The other 18 outcomes and the ordinary failure are unchanged. All recorded
inputs match. A follow-up condition repair clears the focused test's
`UnknownCondition` failure, but reaches `InvalidCallEffect` instead. The next
project run stays held until that control passes.

[Hono 24](../target/wave202-hono-combined-census-24-result.md) completed all
188 roots with unchanged recorded inputs. It has 152 unsupported roots,
two internal errors and one original skip. The same 33 roots complete.
The ordinary check still fails in `http-exception.ts`. A separate observation
identifies the reported symbol as the merged global `Response`. Ordinary5
below measures the later ownership repair. The complete census took
716.068 seconds after a 1m58s build.

[Hono ordinary 5](../target/wave202-hono-ordinary-5-result.md) clears the
symbol-ownership failure with a reviewed five-line change. It reuses the
existing proof for all declarations of a merged global. The next failure is
`R01.RELATION`, requiring resolved structured members in `http-exception.ts`.
The check took 310.482 seconds after a 1m56s build. It still returns no graph
or replay, and does not establish a completed file or project.

[Tests 53](../target/wave202-query-hono-combined-tests-53-result.md) ran all
208 cases in 77 targets. The 185 old cases have 166 passes and 19 failures.
The unchanged conditional-call diagnostic case recovered. The 23 new cases
have 11 passes and 12 failures. Two callback cases hit a provenance publication
debug assertion. Both later recover in the unchanged
[callback-owner1 tests](../target/wave202-callback-owner-1-result.md).
That run passes five unchanged cases and three new captured-write cases.
One helper-corrected case still fails during arrow parameter checking.

[Library 6](../target/wave202-query-hono-checker-lib-6-result.md) failed to
compile its test harness. A test-only `SourceFlowPlan` initializer lacks the
new `class_expression_conditions` field. All 5,437 baseline cases are unrun.
Normal-library compilation did not catch this test-only error.

[Library 7](../target/wave202-query-hono-checker-lib-7-result.md) ran all
5,437 cases after the one-line initializer repair. It has seven lost passes
and three recoveries against run 5. One loss is a real sort-callback routing
regression. Another is only map ordering in a debug snapshot. The remaining
five involve changed support, member state, or an unsupported-error category
and need further checks. All seven were failures at that checkpoint. No test
expectation changed, and the source batch was not accepted.

[Sort run 1](../target/wave202-sort-call-route-1-result.md) runs all 5,437
library cases on the sort repair. It recovers the unchanged sort-callback case
and a class-method array-target query. The debug-order case also passes, but
the sort repair does not fix its unstable output order. No old pass is lost.
One new callback diagnostic control passes. The new positive/custom-method
control fails on a method signature before its later assertions. It remains
unchanged and is not counted as a pass.

The [constructor repair](../target/wave202-constructor-trailing-comma-1-result.md)
passes both new tests. [Generic defaults, run 3](../target/wave202-function-parameter-default-3-result.md)
passes four of five tests. Two new controls now pass in full and both old
numeric controls retain their passes. The remaining new case fails a
contextual literal identity check. Its expected result matches the pinned Go
checker. These focused gains are not complete-project gains.

## Earlier repair checkpoints

[Class-condition3](../target/wave202-class-condition-3-result.md) passes all
five unchanged tests. One case recovers and no pass is lost. The last repair
uses the existing optional-read helper for `label?: string`, while leaving
field storage and assignment rules unchanged. The complete test now passes
its original branch-type, TS2345, ownership and replay assertions.

[Both merged-global property controls](../target/wave202-merged-global-property-2-result.md)
now pass on commit `c8597243`. The eight-line repair reuses the existing
global-owner check instead of rejecting
a second global value declaration early. The fixed tests check both interface
members, the value's prototype, the incompatible-assignment diagnostic and
repeat queries. Hono still fails in a separate property-read query without
the source context needed to request interface heritage information. These
controls do not prove a Hono project pass.

The [shared-expression change](../target/wave202-shared-value-expression-1-result.md)
is committed and passes compilation for the library and all three selected
public test targets. Those tests have not run on this change.
It removes duplicate call-argument syntax checks, shares class child traversal,
and uses binder ownership for direct callbacks. The existing expression
planner and evaluator remain in use. Context, flow and Array.sort routing
must remain correct in the combined tests.

The class, callback, global and debug-output fixes are combined on the measured
sort branch at `f253d469`. Review confirms that all donor changes and public
tests are preserved. This combined candidate has not run its tests. The
shared-expression change is now being added after its compiler check passed.
Diagnostic code and unfinished optional-call or generic-return work stay
outside this candidate.

The [debug-output repair](../target/wave202-symbol-table-debug-1-result.md)
passes its new public test and the unchanged alias snapshot test. It sorts
symbol names only when printing debug output. It does not change type checking
or count as a project gain.

The [Hono observation](../target/wave202-hono-member-readiness-observation-1-result.md)
identifies the next failure as missing interface heritage information during
a property read without source-query context. The existing source-aware query
can request that information. The missing caller is not yet identified, so
there is no reviewed production fix or new Hono pass for this failure.

## Next project milestones

1. Resolve the `timeoutManager.ts` heritage failure now shared by five Query
   roots. Check the repair on the real project. A changed first error is not
   completion. The next useful result is a complete root with correct checking.
2. Resolve the members needed by Hono's next type comparison. Keep the exact
   declaration ownership and use the existing member-resolution path.
3. Run the combined candidate's focused tests and regression checks, then check
   the unchanged projects. Do not wait for the separate optional-call and
   generic-return repairs to finish before measuring the combined changes.

More workers have not increased the measured project completion rate in the
latest comparisons. Each project needs a short edit, test and project-check
cycle. Independent workers can fix the next measured blockers in parallel.
Neither project has evidence of being close to a full correct check yet.

## Earlier results

[Query 29](../target/wave202-query-combined-census-29-result.md) checked all
244 records and 23 original roots. The conditional-call repair changes the
shared failure in five roots. The next stop is `this.gcTime || 0` inside the
same call in `removable.ts`. The class-body walker does not visit logical
expressions. The other 18 root outcomes and the ordinary `timeoutManager.ts`
failure are unchanged. Original inputs, options and libraries match Query 28.
Compilation took 2m00s and the census took 16.890 seconds.

[Tests 49](../target/wave202-query-hono-combined-tests-49-result.md) ran all
185 cases in 70 targets. All 184 old outcomes match run 48. The new conditional
case reaches its diagnostic assertion, but Rust omits the failed union-member
detail beneath TS2345. The test remains unchanged. The fix must preserve that
native detail. Compilation took 2m08s. Both runs used the direct repair branch
at `70316a69fdd3471a96b389df02cf0475c2ea1543`, without another integration step.

[Query 28](../target/wave202-query-combined-census-28-result.md) completed all
244 records and 23 root attempts. Only `index.ts` and `subscribable.ts` complete.
The ordinary project check still rejects the class in `timeoutManager.ts`.
Five roots, `mutation.ts`, `mutationCache.ts`, `query.ts`, `queryCache.ts` and
`removable.ts`, now reach one unsupported call in `removable.ts` instead of
alias-resolution failures. Those are later failures, not recovered files.
The other 18 outcomes match Query 27. The census took 15.157 seconds.
The original project inputs, options and libraries stayed fixed.

[Tests 48](../target/wave202-query-hono-combined-tests-48-result.md) ran all
184 cases in 69 targets. Both original JWT cases recovered without test changes.
No old pass was lost. The new imported-callback test also passes. The 183
unchanged cases have 164 passes and 19 failures. Compilation took 2m05s.
Tests 48 and Query 28 use `c0153e05b95d37f72e33fc9e3698a05a9e584736`.

[Tests 46](../target/wave202-query-hono-combined-tests-46-result.md) compiled
all 66 targets and ran all 181 cases. The imported generic-class interface
annotation case recovered without a test change. No passing case was lost.
Two merged-symbol cases now pass after approved helper corrections and a
separate public `typeof` query repair. Keep these apart from unchanged gains.
Against Tests 45, 178 unchanged cases have 158 passes and 20 failures. The
three helper-affected cases all pass. The complete error blocks remain saved.

The symbol corrections follow the pinned Go implementation. Public queries
return the export owner. Internal lexical caches retain their local symbol.
These corrections do not erase the two measured failures in Tests 45.

[Tests 47](../target/wave202-query-hono-combined-tests-47-result.md) ran all
183 cases in 68 targets. All 181 earlier outcomes match Tests 46. The new global
augmentation ownership test passes. The new intersection-property test fails
an unused-branch cache assertion after source checking. The Rust and pinned Go
implementations both check the written branch during source checking, even when
the conditional result uses the other branch. A separate test-only correction
is committed but unrun. It is not included in run 48 or counted as a checker gain.
Compilation took 2m07s with four build jobs.

Tests 46 and Query 27 use `4a3796f4ecf12a10e048100520bca42b76b1a7b3`.
Tests 47 uses `a2b7b5fb9a3feea95353944b3164a81e447eb766`.
None of these results accepts the source batch. The last accepted primary source
remains `8f4943ac`, whose code matches the measured `5c7c7bd2` checkpoint.

## Why the demo has not advanced

A file can depend on several unsupported checker operations. Fixing its first
failure often exposes the next one. The Query cache files show this directly.
Focused tests prove individual cases, not full-project checking.

Parallel source work has also outpaced integration and project validation.
Worker count and commit count are not evidence that Query or Hono works.
The current priority is the errors returned by the unchanged real projects.
Root-only review and run approval also delayed useful checks. A small reviewed
source fix can now get its own frozen project-check copy while its new tests
are still being written. The integration and run pairs can now verify final
pins and start an approved check without another root review. They still must
preserve every old test and original project input. Broader tests and source
acceptance remain required.

Slow feedback added to this delay. Earlier Hono ordinary checks took about
24 minutes. Ordinary check 3 took about 2.5 minutes, and the latest check took
about 5.2 minutes. Source, diagnostics,
optimization, job count and target changed, so this difference does not isolate
a cause. Hono 24 now provides the newer full census shown above.

[Hono ordinary check 3](../target/wave202-hono-ordinary-3-result.md) clears
the `Buffer` ownership failure. It now returns `R01.RELATION`, an unsupported
object-type comparison, in `http-exception.ts`. The build took 1m57s and the
ordinary check took 154.069 seconds.
The failed check still returns no complete graph, input identity or replay.
This is a cleared first failure, not a complete file or project pass.

The [next Hono trace](../target/wave202-hono-structured-relation-observation-1-result.md)
names the failed cached object's owner as `globalThis`. The outer relation has
identical endpoints, but Rust walks their cached child types before returning.
Pinned Go returns for identical types before structural traversal. The new
eight-line repair stops that child walk for identical endpoints and retains
direct root validation. Ordinary check 4 measured it at `5c229304` in a frozen
copy while test writing continued separately.

[Hono ordinary check 4](../target/wave202-hono-ordinary-4-result.md) clears the prior
`R01.RELATION` stop. It next returns `INV.SOURCE.RELATION` in `http-exception.ts`
because a symbol is not store-owned. The later observation identifies `Response`,
but its exact rejecting check is not yet proved. The ordinary check took
311.957 seconds, compared with 154.069
seconds in check 3. It still returns no graph, complete diagnostics or replay.
No file or project pass follows from the changed error.

## Earlier work and checks

The current Query repairs address three measured stops:

- The ordinary check rejects a type alias in an `implements` clause. The source
  repair is committed as `20915d7f`, with three new controls in `9549fa9e`.
  It keeps alias identity separate from resolved object ownership and preserves
  the native invalid-base and missing-member diagnostics. These tests are unrun.
- Five roots stop on the logical argument in `removable.ts`. The repair pair
  is checking class-body traversal and retained flow for the complete call.
- Two roots stop on `#currentQuery = undefined!` in `queryObserver.ts`.
  The source repair and its follow-up are committed through `03003910`.
  They use the existing non-null evaluator and class assignment checks.
  Review caught an overly broad rejection of template literals and string
  mappings. The follow-up preserves those known non-nullable types and proved
  `keyof` types. General `NonNullable<T>` evaluation remains unfinished.

The union-member diagnostic fix is committed as `0c836cca`. It reuses the
existing diagnostic builder. The conditional-call test remains unchanged.
The branch for Tests 50 and Query 30 passed integration review at `5bb26fd0`.
It has these Query fixes and the Hono identity repair. All 185 old focused cases
are unchanged. Four new test files add 13 cases, for 198 cases in 74 targets.
Both attempts then failed Rust compilation with E0015 in `source_flow.rs`.
All 198 tests and all 23 Query roots were unrun. Root committed the one-line
const-compatible panic fix as `6ddc80a7`. Added tests are not recovered tests.

Four more pairs completed repairs for independent Query failures: forward closure references
in `retryer.ts`, a generic DOM reference, callback parameters in local
initializers and returns, and generic interface references in `types.ts`.
Each pair has its own worktree and separate source and test owners. They check
existing changes before adding code. These are not measured recoveries.

The empty-interface investigation found that current source already repairs
Hono 22's recorded `ContextVariableMap` failure. The old failure came from its
JWT augmentation, and both unchanged JWT controls now pass. No duplicate fix
or test was added. The new full Hono census must measure its current root result.

Tests 51 and Query 31 also failed Rust compilation. Four API errors prevented
all 208 tests and all 23 Query roots from running. Hono 24 and library run 6
did not launch on that broken source.

Root fixed the two affected source files and ran a fast normal-library compiler
check before another project build. That [check passed in 32.13 seconds](../target/wave202-query-hono-compile-check-52-result.md).
The checked source is committed as `722260115`. Tests, inputs and options are
unchanged. This is a Rust compilation result, not a TypeScript recovery.

Tests 52 then compiled the checker but failed to compile one new test. Root
fixed its `NodeId` API use in a separate source copy. Tests 53 compiled all
77 targets and ran all 208 cases. Its results are above. A later test-only
correction uses the actual parser property-node variant. That correction
passed a compiler check but does not count as a checker recovery.

Query 32 and Hono 24 are complete on the same production source and unchanged
recorded inputs. Neither gained a complete root. The separate observation
identified `Response`; its symbol and both type caches were present at the
observation point. This does not identify the exact earlier rejecting guard.
Library 6 is closed after its test-harness compile failure. Library 7 now has
the full results above. Hono ordinary 5 clears the ownership failure but stops
at the next comparison.

The next repairs target the measured class-global read, constructor trailing
comma and generic default-parameter failures. The default-parameter source
and tests reached four passes and one failure in run 3. The constructor
trailing-comma repair passed both new controls. Neither has established a new
complete project root. The callback-owner repair is committed and its focused
checks are running separately, with the known helper correction counted apart.

The workflow now requires a fast compiler check before a donor enters a
project batch. Repeated commands no longer need another preparation reviewer
or a chain of approval reports. Each runtime owner checks the source and
command changes once, then runs the released check and retains its results.

The Buffer change follows the pinned Go rule that a global augmentation can
retain its module parent. A separate public test checks the real global table
and retained ownership. This change does not add every augmentation value query.

Run 48 measured two more reviewed production fixes:

- Query callback checks now decline imported aliases before demanding their
  target values. The two affected checks only support local variables and
  parameters. Normal import checking remains unchanged. A new focused callback
  test includes a real type error and repeated checks, and passes. Five real
  Query roots now reach the later shared call failure.
- Hono's cached interface query now uses the existing validated alias resolver.
  The two JWT cases previously completed their initial checks, then failed on
  repeated checking. This one-call-site fix preserves their original tests.
  Both tests now pass.

Run 49 and Query census 29 used separate build targets in parallel. Both are
closed. Source acceptance remains separate from these feedback checks.

The [Set trace](../target/wave202-set-array-target-observation-1-result.md)
reports no supplied array targets at the failed cached `ReadonlyArray` check.
All three selected tests still fail. The caller that loses those targets is
under review. A separate generic-function alias repair also recovered no cases.
Neither result is a passing feature or a project gain.

The test and project feedback runs now use four Cargo build jobs with the
same optimization level, assertions, overflow checks and memory limits.
A [compile-only comparison](../target/wave202-opt1-four-job-feedback-1-result.md)
built all 66 targets in 121.0 seconds, compared with 194.9 seconds with two jobs.
No tests ran in that comparison. It was one sequential comparison, with
filesystem cache warmth and other worker load uncontrolled.

Query 27 tried sequential reuse of the completed test target. The checker
still rebuilt. Shared dependency features and artifact identities differed,
even though the checker's own feature list and profile matched. Compilation
took 3m03s. No cache or compiler flags were forced to hide that rebuild.

For each batch, preserve existing passing cases and native error checks, then
rerun the unchanged projects. Before acceptance, run the broader tests and the
unchanged original corpus, remove temporary observations, and verify the final
source again.

Neither full-project demo is ready. A partial demo must name the real files
that complete and show intentional type errors being reported.

## Earlier snapshot, runs 39 and 22

This section is retained history. Current results and work above supersede it.

Query has one new complete isolated root. The latest Hono census timed out.
Neither project is ready for a full typechecking demo.

| Check | Latest result | Change |
| --- | --- | --- |
| Query core, census 22 | 2 of 23 isolated roots complete | `subscribable.ts` is newly complete, no loss |
| Hono, census 22 | 33 of 188 isolated roots complete | No gain or loss |
| Focused tests, run 39 | 144 pass, 27 fail | One old test recovered since run 37, no old pass lost, four new tests fail |
| Checker library, run 3 | 5,069 pass, 368 fail | Two passes lost since run 2, no recovered failure |

Query 22 uses `96d3fa91cb239624d8a80e1d486776f76f22bdb6`.
Hono 22 uses the earlier `bbfd62521499c8cf7375c1be95076fe1a6576483`.
Focused run 39 and library run 3 use `f7e41298b0bfc543264a53bfa02a8c0579e2bee1`.
Those measured processes and their exact services are closed.
Project source, roots, dependencies, options and libraries stayed fixed.
Isolated roots are not full-project passes or a percentage of compiler support.

[Query 22](../target/wave202-query-combined-census-22-result.md) completes
`subscribable.ts` for the first time. Seven other roots now reach class checks.
The ordinary check still rejects the class declaration in `timeoutManager.ts`.
The complete 23-root census took 92.656 seconds. No complete root was lost.

[Hono 22](../target/wave202-hono-combined-census-22-result.md) still stops
at the `ContentfulStatusCode` reference in `http-exception.ts`. It has
148 unsupported roots, six internal errors and one original policy skip.
Only two first stops changed. No complete root was lost.

[Tests 39](../target/wave202-query-hono-combined-tests-39-result.md)
compiled all 60 targets and ran all 171 tests. One old generic-alias error test
recovered since run 37. No old pass was lost. Run 37 had recovered five unchanged
tests since run 36, covering `bind`, augmentation conflicts and buffer errors.

The 167 tests already present in run 37 now have 144 passes and 23 failures.
All four new DOM overload and generic-callback tests fail. The historical eight
cases in corrected test files still have five passes and three failures. Those
test corrections do not count as unchanged checker gains. Generic defaults,
imported JWT context, returned class callbacks and cache replay still fail.

Checker-library run 3 ran the same 5,437 tests as run 2. It passed 5,069 and
failed 368, with no ignored or filtered tests. All 366 old failures remain, and
two old passes now fail. Their complete snapshots differ only in map display
order. Both maps keep the same keys and values. Production review confirms
that both fields use unordered HashMaps with unsorted Debug output. The cause
of the order change and the snapshot contract still need checking. No lost
type information is visible in those two failures.

A [comparison with the accepted checkpoint](../target/wave202-query-hono-library2-accepted-name-comparison.md)
also found that 225 of run 2's failures had the same names passing before.
That comparison did not inspect test bodies. It is not proof of 225 unchanged
tests or 225 compiler regressions, but it identifies more work to check.

### Current work

[Hono 23](../target/wave202-hono-combined-census-23-result.md) took 1,444.768
seconds to return `SymbolNotOwned` in `http-exception.ts`. The census then hit
the unchanged 30-minute limit. Only four root attempts finished. All four match
the old unsupported results. The other 184 roots have no new outcome. Hono 22
finished its whole census in about 10 minutes. This is a measured slowdown.

Focused run 38 failed compilation on a wrong `TypeFlags` import in a new test.
All 171 tests are unrun. The process and service are closed. The import repair
does not change test inputs or assertions. Run 39 and library run 3 are now
closed. Their results are recorded above.

Run 40 also failed compilation before any tests ran. Two call-signature uses
had not been updated after the receiver-predicate change made a symbol optional.
All 179 tests remain unrun. The two-use repair passed review and is committed.
Run 41 is released on the repaired source at
`6e7ceab343667c503a623638a82c17565b972e3f`. It keeps all 64 targets and 179 tests.
No result is available yet.

Each source repair has one writer, one reviewer and an isolated worktree.
One separate pair combined the ready changes and reviewed the complete result.
Runtime owners now check that source. Root releases the runs and checks their
results. Thirteen reviewed fixes are combined. The repaired build must pass
before their 64 targets and 179 tests can run.

The next candidate adds async callback identity, Node timer bases, generic
defaults, JWT annotations, receiver predicates and array destructuring inside
returned async functions. The earlier `Omit`, Promise and DOM work is measured
in run 39. It does not yet pass all its controls.

The seven new Query class failures share an imported generic base-class guard.
That fix is committed and reviewed. The constructor callback fix for private
manager fields is also committed and reviewed. Both are in the next integration
batch with six new Query class tests. Fixing these guards does not establish
that all seven roots pass.

Query is the next demo target. Run its original census after the combined test
build passes. For Hono, first measure the repeated planning work and record the
exact ownership-error origin. The saved logs do not yet prove either cause.
One pair is adding those bounded observations in a separate worktree. Another
pair checks zero-argument class-call conditions in Query's focus and online
managers, including `if (!this.hasListeners())`.

No repair batch is accepted on primary. The unchanged corpus, broader tests
and removal of temporary error traces still apply.

## Earlier checkpoint, tests 34 and project censuses 20 and 21

The following section is retained history. Its pending work is superseded above.

Project progress remains slow. Hono gained one completed root in the latest
run. Query is unchanged. Neither is ready for a full-project demo.

| Project | Completed isolated roots | Unsupported | Internal errors | Original policy skip |
| --- | ---: | ---: | ---: | ---: |
| Query core | 1 of 23 | 22 | 0 | 0 |
| Hono | 33 of 188 | 148 | 6 | 1 |

Both project runs use `3bbbcbd838eeece2ca5ea23d52fa32f4557e009e`.
An isolated root is one original project entry file checked on its own. These
counts do not prove a full project pass or matching diagnostics. Both runs kept
the original roots, loaded files, options and libraries. Both had zero load
diagnostics.

[Query census 20](../target/wave202-query-combined-census-20-result.md)
matches every outcome from census 19. The ordinary check rejects the merged
`clearTimeout` function symbol. No root completed for the first time.

[Hono census 21](../target/wave202-hono-combined-census-21-result.md)
adds `src/utils/jwt/utf8.ts` and keeps all 32 previous completions. Its ordinary
check gets past the DOM parameter failure, then reports an internal
`InvalidTypeReference` error in `http-exception.ts`. This is a new internal
error, not a project pass. The other 186 root outcomes are unchanged.
All original root attempts finished. Both processes and their exact services
are closed.

### What the tests prove

[Combined tests 34](../target/wave202-query-hono-combined-tests-34-result.md)
compiled all 57 targets and ran all 165 tests. It passed 131 and failed 34.
Four unchanged tests recovered since tests 33. They cover timer callback
types and three imported generic-parameter cases. No previous pass was lost.

Compared with [tests 31](../target/wave202-query-hono-combined-tests-31-result.md),
the 163 byte-unchanged tests have 130 passes and 33 failures. Six tests
recovered across these runs. The other two recoveries cover class-call
argument and return errors, property narrowing, both branches and negation.

The two separately corrected Promise tests have one pass and one failure.
The positive case passes. The negative case still reports `LiteralTypeCapacity`.
The test correction is not an unchanged-test gain.

Earlier runs gained passing Set, Bind and buffer checks. Returned class
arrows, generic defaults, local Set inference and several import queries
still fail.
Attempts 27 and 32 failed compilation and ran no tests. The alias helper error
from attempt 32 is fixed in the compiled attempt 33.

### Why progress slowed

Function instantiation, imported types and cache validation are shared blockers.
Some earlier changes broke working paths and required repairs. Other fixes
cleared an early check but exposed another missing operation in the same file.

For example, the focused returned-class tests now get past the pending function
return. They next fail at `this.listeners.add(listener)`, before call resolution.
The complete Query run still finishes no additional roots.

Code reviews and commits have outpaced successful combined runs. Completed
project roots and unchanged test passes remain the progress measures.

### Next checkpoint

Tests 35 failed compilation on `6255e1364668f5aabc843b862cd4062fe1ab289f`.
All 165 tests are unrun. An imported-variable query passes `NodeRef` where the
existing API requires `SourceFileRef`. The original pair is fixing that call.
Both the failed process and its exact service are closed.

This batch has reviewed fixes for the actual `clearTimeout` overload group,
Node interfaces whose methods return `this`, cold Array types, generic
defaults, Promise callbacks, async return aliases, class writes and generic
inheritance. Two temporary traces record the next unresolved failures.
Source review is not a measured test pass.

Query 21 and Hono 22 did not run on the failed candidate. The next combined
run must compile before another project run starts.
Separate pairs handle the new Hono type-reference error, the next `Awaited`
and `bind` failures, generic alias evaluation and DOM index types. Each pair
has one writer and one reviewer. Ready fixes do not wait for unrelated work.

One separate test-only commit corrects two expected literal-order strings in
the generic-default tests. Pinned Go confirms the order. Original TypeScript,
diagnostic codes and other assertions stay fixed. The three affected cases
will be reported separately from the 162 unchanged cases in the next run.

The next useful result is an unchanged failing test that passes, followed by
an affected project root that completes. More reviews, commits or changed
first errors do not meet that checkpoint. Project inputs, library files,
compiler options and existing tests remain fixed.

No checker repair batch is accepted on primary. Acceptance still requires
the unchanged corpus comparison, broader checks and removal of temporary
traces. A demo must finish the ordinary project check with the original
config and libraries, then match the pinned Go checker's diagnostics.

## Earlier Query and Hono checkpoint

The section below is retained history. Its pending work and counts are
superseded by the latest checkpoint above.

Query core and Hono are the primary targets again. New Pathe-only work,
runner redesign and the UFO dependency task are paused.

The latest complete Query census used `df057324`. Hono used `a6f71911`.
These measure the repair branch, not an accepted primary-branch merge.

| Project | Completed isolated roots | Unsupported | Internal errors | Original policy skip |
| --- | ---: | ---: | ---: | ---: |
| Query core | 1 of 23 | 21 | 1 | 0 |
| Hono | 30 of 188 | 151 | 6 | 1 |

Neither ordinary project check completes. These are not passing-file or
diagnostic-parity counts. Both runs attempted every original root and ended
normally. Their root lists, loaded graphs and empty load diagnostics match
the earlier runs.

There is no new completed root since the earlier September 2 checkpoint.
No earlier completion was lost. Hono has one more internal error: its repaired
constructor now reaches a missing optional-chain flow condition. The same
condition error occurs in Query's `CancelledError` constructor.

Query took 37.900 seconds after compilation. Hono took 342.526 seconds.
The [current results](../target/wave202-query-hono-current-results.md) link
the complete raw reports and logs.

The newer ordinary Hono run at `d6a5182d` still fails. It reports
`InvalidCachedTypeAlias` in `http-exception.ts` before final diagnostics or
replay. This run does not replace the complete census above. The same error
category appears in the new imported-class tests. Their common cause is not
yet proved.

### Focused test progress

The latest [combined run](../target/wave202-query-hono-combined-tests-5.cargo.log)
at `d6a5182d` ran all 44 selected tests. It passed 33 and failed 11.
The preceding run passed 27 of 39. Four existing failures now pass, and the
five added tests contribute two passes and three failures. No earlier pass
was lost. Two of those four changed results are test-contract corrections,
not new checker support.

Before this batch, six genuine checker failures had been fixed on an unchanged
30-test set, increasing passes from 18 to 24. The latest batch adds passing
checks for two generic-call cases and two optional-constructor flow cases.

| Test group | Passed | Failed |
| --- | ---: | ---: |
| Existing constructor and optional-argument controls | 15 | 0 |
| Optional arguments to super | 2 | 0 |
| Own class method assignments | 2 | 0 |
| Constructor field initializers | 2 | 1 |
| Contextual object-property parameters | 1 | 3 |
| Captured array writes | 3 | 0 |
| Generic constructor parameters | 0 | 3 |
| Generic optional call parameters | 2 | 1 |
| Generic signature commas and defaults | 4 | 0 |
| Optional constructor flow | 2 | 0 |
| Imported generic class types | 0 | 3 |

The comma repair also passed all 366 parser tests in its separate
[parser check](../target/wave202-hono-generic-trailing-comma-tests-2-result.md).
These counts are not the full Rust or upstream TypeScript suite.

The earlier third batch did not run tests. Two calls to a nonexistent test
API prevented compilation. Its test-only correction preserves every input
and expected result. Two captured-array failures also exposed a test
contract error: signatures can keep lazy return types until queried. The
pinned Go source confirms this. A reviewed test-only correction calls the
canonical return-type query before checking the same result. Both corrected
tests now pass. This is not a new checker feature or a project gain.

### Current implementation priorities

1. Fix Hono's current type-alias cache error. The optional-chain flow repair
   passes both focused tests, but the project still fails in `HTTPException`.
   Determine whether the imported-class tests expose the same cache defect.
2. Finish Query's shared `Subscribable` class. Eight roots now pass the old
   field and method-assignment stops, then reject
   `this.subscribe.bind(this)`. Workers are porting real callable-library
   lookup and generic receiver inference. Query uses strict bind checking.
3. Fix Query's ordinary function call. Its next stop rejects a merged callable
   symbol. Preserve its real function declarations and namespace members.
4. Finish Hono's imported generic class types, generic call signatures and
   mutable object destructuring. All three class-import tests still fail.
   Two of three generic-call tests pass. The indexed object-rest repair is
   committed and reviewed, but has not run.
5. Fix the remaining focused constructor and contextual-parameter failures.
   Keep cold queries, lazy returns, real diagnostics and warm replay correct.

Each feature has a source owner and a test or review owner in a separate
worktree. Root owns the combined build and project measurements. The current
batch is not accepted on the primary branch. Remaining repairs need runtime
verification and the unchanged corpus checks. All current test and project
measurements above have finished. Separate focused runs are now released for
the committed method-bind and mutable object-rest repairs. They do not yet
have runtime results.

Each repair must preserve the original projects, options and dependencies.
Run focused type and diagnostic tests, then rerun the affected project.
Count complete project checks and diagnostic parity as the outcome.
Do not count source reviews, logging changes or compiler builds as fixes.

## Earlier Pathe checkpoint

The sections below are retained history. Their priorities and pending build
status do not describe the current Query and Hono work above.

## Current result

The latest combined run passed 425 of 500 selected tests. All tests ran.
The checker passed 163 of its 238 selected tests. Binder, parser and fixture
tests account for the other 262 passes. This is a focused repair batch, not
the full Rust or TypeScript test suite.

On the unchanged set of 496 earlier tests, four failures now pass and no
passing test regressed. Both new parameterized-function tests pass. Both new
Array property tests fail before checker construction. A reviewed diagnosis
finds the wrong AST variant in their test helper. Its one-line correction
keeps every TypeScript input and assertion unchanged. Later assertions remain
unmeasured. The
[independent result review](../target/wave202-pathe-demo-tests-11-result-review.md)
and the separate resource check are closed.

Pathe is not demo-ready. Its latest project run attempted all nine original
roots and completed none. Every root and the ordinary project attempt stopped
with an unsupported operation. No internal checker error occurred in this run.
The evidence reader passed. The independent result review and separate
resource check are closed for this project run.

The newer compiler build failed with Rust error E0308. A function-body parent
check compares a `SourceNodeParent` with a `NodeRef`. The one-line repair is
committed and reviewed. It wraps the node in `SourceNodeParent::Parent` and
retains the identity check. A new build has not verified this repair yet.
The duplicate 510-test build is on hold. It was not submitted.

| Measurement | Result |
| --- | --- |
| [Combined tests 11](../target/wave202-pathe-demo-tests-11-result.md), `2f8ae108` | All 500 ran. 425 pass, 75 fail. Four earlier failures fixed, no earlier pass lost. Main and resource reviews are closed. |
| [Ordinary compiler build 11](../target/wave202-pathe-demo-bin-11-main-result.md), `84f3a17a` | Build failed with E0308 after 37.648 seconds. No tests or project checks ran. The resource audit ran. Its evidence review is pending. |
| [Ordinary compiler build 10](../target/wave202-pathe-demo-bin-10-main-result.md), `c9258a43` | Build passed in 74.660 seconds. Main and separate resource reviews are closed. A build is not a project pass. |
| [Pathe census 10](../target/wave202-pathe-demo-census-10-result.md), `c9258a43` | Zero of nine roots complete. All nine and the ordinary attempt are unsupported. The oracle stage took 22.584 seconds. Main and resource reviews are closed. |
| [Previous combined tests 10](../target/wave202-pathe-demo-tests-10-result.md), `c9258a43` | 419 of 496 passed. Main and separate resource reviews are closed. This is the comparison set for Tests11. |

The project run used the older compiler. It does not measure the four fixes
in the newer test run. The failed newer build provides no new typechecking
result. Its [saved evidence review](../target/wave202-pathe-demo-bin-11-main-result-review.md)
confirms the compiler failure, not a passing build.

The current project evidence retains the same nine roots, all 277 loaded-file
identities and all 13 explicit options. The
[const-enum difference](../target/wave202-pathe-option-parity-diagnosis.md)
is stored-versus-effective reporting. Both checker getters derive true.
Complete effective-option and final module-resolution parity remain unproved.
Empty partial diagnostics are not a pass.

## Demo targets

| Project | Why it is selected | Current limit |
| --- | --- | --- |
| Pathe | First target. Five source files and four test files, 4,843 lines in total. Dependencies and a successful pinned Go reference are available. Each Rust root has a recorded attempt. | Zero complete roots. Prioritize the actual root failures and measure each combined repair. |
| UFO | Second candidate. Seven selected source files, 1,571 lines. Its smaller source set makes it worth measuring. | Dependency installation still needs approval. No paired Rust and Go baseline exists, so it is not a verified near-pass. |

Keep the projects unchanged. Do not remove tests, replace dependencies, change
compiler options or supply permissive stub types to produce a demo.

The [offline candidate check](../target/wave202-offline-demo-readiness.md)
found missing dependencies in the cached tiny-invariant and Mitt checkouts.
There is also a separate installed tiny-invariant project. Its
[earlier Rust measurement](../target/wave202-tiny-invariant-rust-measurement-1-result.md)
completed zero of five roots. Rust loaded 30 files versus 168 in its
TypeScript 5.3.3 reference and reported a removed config option. No Go
executable ran. This is a useful compatibility case, not a verified faster
route to a complete demo. Neither Pathe nor UFO is a proved near-pass yet.

## Next work

1. Use the actual Pathe stopping points to order repairs. The latest run
   still stops in arrows, function bodies, a binary expression, an import and
   cold alias resolution. Check which pending changes address those exact
   paths. Do not infer a cause from the outer error label.
2. Verify the committed parent-node repair in the next build. Keep the failed
   source and its evidence unchanged.
3. Assemble the next combined source. The reviewed `d6133d80` batch has 526
   selected test names. It includes computed-property writes, nullish
   diagnostic text, optional top-level reads and two test-helper repairs.
   It also retains the earlier typed-arrow, loop-local, function-expression,
   namespace and callable-intersection changes. No tests have run on this
   source. The next reviewed plan combines five complete changes: the parent
   repair, counted-loop repair, throw-parameter helper, import error records
   and parameter-default error records. It retains all 526 tests and adds
   eight loop controls, for a planned selection of 534 tests. Integration
   is in progress. No result from that batch is available yet.
4. Build that source, run its retained tests, then check unchanged Pathe.
   Import and parameter-default error records will help locate failures
   that currently lose their inner cause. These records are not semantic
   fixes. A separate diagnosis also finds an unsupported owner path for
   nested conditional returns. That repair and three focused tests are
   written and under review. Template branches remain a separate limit.
5. After dependency approval, measure unchanged UFO with the pinned Go and
   Rust compilers. Use its actual first failures to confirm or reject it as
   the second demo target.

The four newly repaired older tests cover callable loop composition, iterable
identity, loop scope and immediate function-call error preservation. Their
exact names are in the Tests11 result. Tests10 previously fixed eleven older
tests, including generic call-signature and Array iteration cases.

Two saved diagnoses guide the remaining new failures.
The [counted-loop diagnosis](../target/wave202-pathe-tests10-counted-for-diagnosis.md)
shows that an outer BinaryExpression error can also describe a Logical or
Element plan. The newer saved run identifies flow-preflight cycle errors in
three remaining counted-loop cases. The repair accepts a repeated path only
when that exact path contains a valid loop label. It retains errors for
malformed flow graphs. The committed repair and its eight new controls have
not run yet.

The [computed-member diagnosis](../target/wave202-pathe-tests10-computed-members-diagnosis.md)
finds an incomplete positive cache fixture and identifier-only assignment
planning. Computed writes also need unique-symbol key support and readonly
checks for ordinary assignment. Construct signatures are already admitted.
The exact failing Set guard remains unproved. Removing a rejection would
not complete this support.

## Parallel work and test delay

Source workers use separate worktrees with one writer per owned file.
Diagnosis, implementation, source review and saved-result review run in
parallel. At most three Cargo lanes run, with the existing resource limits.
Keep every old test and every new repair test in each combined selection.

The latest batch fixes four old tests. The previous batch fixed eleven.
These counts do not prove a higher fixes-per-hour rate or that worker count
caused the gain. Complete project checks remain at zero.

The [validation-workflow proposal](../target/wave202-pathe-validation-workflow-plan.md)
targets a measured delay. In earlier saved runs, source capture preceded
compilation by 9 to 18 minutes. Individual builds took about 1 to 5 minutes.
Result completion preceded the separate resource check by 32 to 37 minutes.
Those gaps include review and approval work. They are not all idle time.

The proposal uses one fixed reviewed program and an immutable input record
instead of copying and reviewing large programs for each run. It must keep
all input, output and resource checks. The three-file implementation has
passed independent source review. Its first offline self-check ran once:
245 checks passed, four failed and one lacked the required historical input.
These are runner checks, not typechecker tests. The failures cover saved
command parsing, one negative-test setup and two quote/newline controls.
The result review is closed and confirms the failures. A repair plan is in
progress. No compiler pilot has run, no current gate changed and no time
saving has been measured yet.

For the next source batch, one combined source-and-stage review replaces two
separate review steps. Build, test and project-run preparation also proceeds
in parallel. These changes reduce handoffs. Their time saving is not measured.

## Demo pass conditions

- The unchanged project completes ordinary typechecking with its original
  options, roots, dependencies and library declarations.
- Rust and the reference compiler check the same intended project and produce
  matching complete diagnostics.
- A separate project copy with a deliberate type error reports the expected
  error and source location. The original project stays unchanged.
- The required retained tests pass, and a repeat run gives the same result.

Temporary failure traces must be removed before final acceptance. The primary
branch has not received these unaccepted source batches. There is no reliable
completion date yet. The next useful milestone is a complete Pathe root,
followed by the complete ordinary project check.

## Earlier checkpoint at 5f7ad5e3

The remaining sections are retained history from before the results above.
Their pending states and proposed runs are not the current status.

The demo is not ready. The combined source `21df31a3` failed Rust
compilation at three alias API calls. All 464 selected tests remain unrun.
The one-function repair is committed and reviewed at `5f7ad5e3`. It retains
the contextual methods, template substitutions, computed calls and generic
constructor contexts. The next build and 464-test run will use that source.
Then check unchanged Pathe and use its actual failures to choose the next fixes.

Pathe is the first demo target. The latest census checked the same original
inputs in 21.862 seconds. All 277 loaded files parse without errors, but none
of the nine roots completes typechecking: eight stop as unsupported and one
hits an internal checker error. The [census 3 result](../target/wave202-pathe-first-error-census-3-result.md)
and [independent review](../target/wave202-pathe-first-error-census-3-result-review.md)
include the completed resource check. Source and evidence stayed unchanged.
This diagnostic build does not include the newer combined repairs.

The focused local-write tests improved to six passes out of seven. The latest
diagnostic run preserves that count and locates the normalizer's
`UnknownCondition` at `normalized[2] === "/"`. The normalizer has a static
dependency path to seven of nine Pathe roots. This supports fixing it first,
but does not predict seven passing roots. These separate runs do not establish
a combined compiler pass.

| Check | Actual result |
| --- | --- |
| [Combined demo tests 4](../target/wave202-pathe-demo-tests-4-result.md), `21df31a3` | Binder and parser harnesses compiled. Checker and fixture compilation failed at three alias API calls. No list or run phase started. All 464 tests are unrun. |
| [Normalizer condition trace focus 4](../target/wave202-pathe-normalizer-condition-trace-focus-4-result.md), `9727de9e` | Compile and list passed. Six tests passed and one failed. The failure-only trace identifies a binary expression at byte range `[345, 366)` in the unchanged normalizer. |
| [Combined repairs 3](../target/wave202-pathe-combined-repairs-3-result.md), `9c1a7cbf` | Binder and parser harnesses compiled. Checker and fixture compilation failed with four distinct Rust errors. No list or run phase started. All 454 tests are unrun. |
| [Local-write flow trace focus 3](../target/wave202-pathe-local-write-flow-trace-focus-3-result.md), `d02e8cb9` | Compile and list passed. All seven unchanged tests ran. Six passed and one failed. One trace reports `UnknownCondition`. |
| [Generic constructor focus](../target/wave202-pathe-generic-constructors-focus-1-result.md), `5373bc05` | Compilation failed after 38.598 seconds with two Rust enum API errors. All five tests remain unrun. |
| [Rust API preflight](../target/wave202-pathe-checker-compile-preflight-1-result.md), `38b8e0f1` | Failed after 32.463 seconds with exit 101. Four Rust errors across three of 19 targets. The other 16 emitted check metadata. No tests ran. |
| [Diagnostic CLI build](../target/wave202-pathe-first-error-trace-bin-1-result.md), `68067fca` | Passed in 77.775 seconds. Census 3 then used this unchanged binary without a rebuild. |

The latest [combined result review](../target/wave202-pathe-demo-tests-4-result-review.md)
and [cleanup review](../target/wave202-pathe-demo-tests-4-cleanup-result-review.md)
are closed. The errors call alias metadata methods on an alias ID. The
[repair](../target/wave202-pathe-demo-alias-api-repair-handoff.md) resolves that
ID through the existing store lookup and keeps both validators unchanged.
Its [source review](../target/wave202-pathe-demo-alias-api-repair-review.md)
is closed. The repair has not been compiled or tested. The ordinary CLI build
at the failed source was held before execution, so it does not repeat that
known compile failure.

The [combined result review](../target/wave202-pathe-combined-repairs-3-result-review.md)
and [cleanup review](../target/wave202-pathe-combined-repairs-3-cleanup-result-review.md)
are closed. The four diagnostics report missing
`SignatureLinks` and `SourceNodeParent` names, an unknown closure parameter
type in `source.rs`, and an `Option<EscapedNameRef>` versus `Option<&str>`
comparison in `source_callables.rs`. Fixture compilation repeats the same
checker errors. These are four error sites, not eight separate defects.
The [three-edit API repair](../target/wave202-pathe-compiler-api-repair-handoff.md)
and its [review](../target/wave202-pathe-compiler-api-repair-review.md) are
closed at `bebfdd9b` and included in the new combined source. Compilation is
still required to prove that the repairs work.

The [combined CLI build 4](../target/wave202-pathe-combined-core-bin-4-outcome.md)
never launched. Approval timed out before process creation. It was not retried
because the test build had already failed on the same source. It produced no
executable or project result.

Both branch-join type identity failures now pass. The original 519-byte
`normalizeWindowsPath` function still stops at `Function(Callable)`. Focus 3
emitted one typed flow-invariant trace, but did not identify the failed source
expression or the internal guard. Numeric debug IDs are not source locations.
The [diagnosis](../target/wave202-pathe-normalizer-flow-trace-3-diagnosis.md)
and [review](../target/wave202-pathe-normalizer-flow-trace-3-diagnosis-review.md)
are closed. The fixture uses real ES5 and ES2015 core declarations, not Pathe's full
library set or all its options. The [earlier four-pass, three-fail result](../target/wave202-pathe-conditional-local-writes-focus-1-result.md)
and its [review](../target/wave202-pathe-conditional-local-writes-focus-1-result-review.md)
remain unchanged. Focus 3's [result review](../target/wave202-pathe-local-write-flow-trace-focus-3-result-review.md)
and [cleanup review](../target/wave202-pathe-local-write-flow-trace-focus-3-cleanup-closure-review.md)
are closed. Diagnostic-only commit `9727de9e` adds a failure-only trace for the
condition kind and source range. Its seven-test run finished with six passes
and one failure. The reported byte range `[345, 366)` is
`normalized[2] === "/"` in the original 519-byte file. This uses the reported
source range, not a numeric debug ID. The [result review](../target/wave202-pathe-normalizer-condition-trace-focus-4-result-review.md)
is closed. Cleanup is pending. That trace must not enter the production
compiler. The normalizer and project still fail.

The constructor run found two API errors in `constructor_values.rs`, lines
512 and 515: code treated `PropertyObjectState` as an `Option`. The two-line
[repair](../target/wave202-pathe-constructor-api-fix-handoff.md) and
[source review](../target/wave202-pathe-constructor-api-fix-review.md) are closed
at `9c1a7cbf`. Combined repairs 3 did not report those two errors, but failed
at its four sites listed above. The five constructor tests remain unrun.
The [local-write result review](../target/wave202-pathe-local-write-trace-focus-2-result-review.md)
and [constructor result review](../target/wave202-pathe-generic-constructors-focus-1-result-review.md)
are closed. The [local-write cleanup](../target/wave202-pathe-local-write-trace-focus-2-cleanup-closure-review.md)
and [constructor cleanup](../target/wave202-pathe-generic-constructors-focus-1-cleanup-closure-review.md)
are also closed. Neither audit changed the test results.

The preflight checked 18 public test targets and the ordinary checker library.
It did not link or run tests, or check the private unit-test library. Its
[review](../target/wave202-pathe-checker-compile-preflight-1-result-review.md)
confirms four reported API errors, not the absence of later errors. The
[three-file repair](../target/wave202-pathe-public-api-repairs-handoff.md) has
[source approval](../target/wave202-pathe-public-api-repairs-review.md) and is
committed at `4dce5ef9` and included in the combined source. Its rerun is pending.
The earlier 408-test attempts remain failed compile results with every
selected test unrun. Their
[rerun result](../target/wave202-pathe-focused-repairs-2-result.md) and
[review](../target/wave202-pathe-focused-repairs-2-result-review.md) stay unchanged.

The [combined source handoff](../target/wave202-pathe-demo-generic-context-join-handoff.md)
and [review](../target/wave202-pathe-demo-generic-context-join-review.md) close
`21df31a3`, with 899 files and all prior tests preserved. It joins the complete
API and computed-call changes with the template, method and generic-context
changes. The one-file alias API repair at `5f7ad5e3` is its direct descendant.
It preserves all 899 files and all tests. This is source review, not a test pass.

The earlier combined source checkpoint `2cc8d38d` is signed and independently reviewed, with
894 files. It includes all five local-write, parameter-write, object-binding,
computed-key and callback donors, both public API repairs, and the complete
branch-join, generic-constructor and stored-arrow repairs. The
[source handoff](../target/wave202-pathe-next-three-source-join-handoff.md) and
[review](../target/wave202-pathe-next-three-source-join-review.md) are closed.
The [API integration review](../target/wave202-pathe-five-source-api-join-review.md)
preserves all four test API fixes. Its follow-up enum repair is `9c1a7cbf`,
the source used by the failed combined compile. No combined test has run.

| Work | Pathe code it addresses | Source state |
| --- | --- | --- |
| Conditional writes to initialized locals | `normalizeWindowsPath`, also used by computed keys | Six tests pass, one fails on the diagnostic branch. Repair `4ff5fd50` is included in `2cc8d38d`. |
| Compound writes to parameters | `path += "/"` in `normalize` | `424f3d8b`, five tests unrun |
| Object destructuring in callable bodies | `const { children } = parent` in `_pushToLeaves` | `17b225b1`, two tests unrun |
| Generic library constructors | Real `SetConstructor` declarations and iterator inference | Included in `2cc8d38d`. The separate five-test run failed to compile. |
| Contextual callback parameters and bodies | Local `Register` and nested `Assert` callbacks | Included in `2cc8d38d`. Six tests unrun. |
| Computed keys and their stored type evidence | Literal keys and contextual property order | Included in `2cc8d38d`. Tests unrun. |
| Template substitutions | Conditional expressions inside a loop's template literal | Included in `21df31a3`. Three tests unrun. |
| Contextual methods and generic constructor contexts | The real `Proxy` constructor and its handler | Included in `21df31a3`. Three method and two constructor-context tests unrun. |
| Nested calls in computed keys | Real `String.raw` and imported normalizer calls | Included in `21df31a3`. Two tests unrun. |

The [combined selection](../target/wave202-pathe-combined-repairs-3-template-review.md)
retains all 408 earlier cases, 39 feature cases and seven constructor and
stored-arrow cases, for 454 total. Compilation stopped before any ran.
No failed test was removed. The next [464-test selection](../target/wave202-pathe-demo-next-selection-plan.md)
adds ten tests and retains every old registration. Its
[independent review](../target/wave202-pathe-demo-next-selection-review.md)
confirms 36 groups. All 464 remain unrun at the new source.

Census 3 exposed a conditional expression rejected inside the lexical loop
body. The [source diagnosis](../target/wave202-pathe-for-of-conditional-initializer-diagnosis.md)
locates its ternary inside a template substitution: the conditional planner
does not accept a `TemplateSpan` parent. The separate
[template join](../target/wave202-pathe-template-join-handoff.md) is now closed
at `b102fdcc`, with [independent review](../target/wave202-pathe-template-join-review.md).
The [contextual method change](../target/wave202-pathe-contextual-method-prefix-handoff.md)
is also closed at `4ee8330f`, with [independent review](../target/wave202-pathe-contextual-method-prefix-review.md).
Each adds three tests. Neither change was in the earlier combined repairs 3 compile.
Both are now included in `21df31a3`, and all six new tests remain unrun.
The [generic-context donor](../target/wave202-pathe-generic-constructor-contexts-handoff.md)
and [computed-call donor](../target/wave202-pathe-computed-call-arguments-handoff.md)
are also included. Their source reviews do not prove a complete Proxy or
`String.raw` pass. The next combined run must test their interaction.

No callable trace appeared in census 3, so the callback invariant remains
unexplained. Diagnostic-only source stays out of the production port.

Resource checks are separate from these results. Both the
[preflight cleanup](../target/wave202-pathe-checker-compile-preflight-1-closure-review.md)
and [first local-write cleanup](../target/wave202-pathe-conditional-local-writes-focus-1-cleanup-closure-review.md)
are complete and independently reviewed. They did not change any test result.
[Diagnostic-build cleanup](../target/wave202-pathe-first-error-trace-bin-1-cleanup-result-review.md)
is also closed, as is census 3's separate resource check. None changes the
measured test or project outcomes. The [earlier census comparison](../target/wave202-pathe-census2-progress-comparison.md),
[census 2 result](../target/wave202-pathe-root-census-2-result.md) and
[review](../target/wave202-pathe-root-census-2-result-review.md) retain the parser
improvement from 35 diagnostics to zero and five changed first stops. Census 3
adds failure detail, not completed roots or a test of the newer combined fixes.

The demo is complete only when the original whole-project check finishes and
matches the reference diagnostics, including the four test roots. Focused
invalid programs must still report real type errors. UFO remains the second
small target, but its dependency install still needs network approval. Hono
and TanStack Query remain broader checks, not near-complete demo claims.

The [offline second-project check](../target/wave202-offline-second-demo-candidate.md)
found no ready replacement for UFO. Mitt lacks its test dependencies and generated
package declarations. Sourcemap-codec lacks its Node declarations and dependencies.
Neither has a new measured Rust result. Keep Pathe first and choose the second
project from an actual baseline, not its source size.

## Targets

Use Pathe for the first small complete demo, UFO for the second, and Hono for
the larger integration target. Pathe's original typecheck includes nine roots,
with all four test files.
It already uses TypeScript-Go and has a supported modern module configuration.
Its unchanged source, tools and installed dependencies are verified. The port's
pinned ordinary Go compiler checked all nine roots with zero diagnostics and
277 loaded files. That result and cleanup have independent review. The Rust
project-checking tool is built and its cleanup is closed. The first Rust Pathe
run stopped at `E00.SOURCE_SYNTAX`, an unsupported arrow in `src/_glob.ts`.
It returned no complete Rust graph or diagnostics. The main process exited 0,
but the project check is incomplete. Independent result review and separate
post-close verification are closed.

The later file-by-file run attempted all nine roots. None completed source
checking. Eight stopped at unsupported operations and one at an internal
checker error. It supplied typed locations for all eight unsupported cases.
The loader also reported 35 parser diagnostics in Node's `http2.d.ts`.
All 277 loaded files match the saved Go file list and bytes. This is not full
module-resolution or diagnostic parity.
The [census result](../target/wave202-pathe-root-census-1-result.md) and
[independent review](../target/wave202-pathe-root-census-1-result-review.md)
retain every failure and the closed resource checks.

The census reader failed because it sorted JSON keys that the Rust serializer
preserves in order. Separate saved-data checks reproduce both emitted digests.
The original failed result stays unchanged. A separate offline readback timed
out while hashing the executable, before census validation. It created no new
result. This reporting defect is separate from the nine checker failures.
The corrected reader now passes all 66 saved-data controls. It keeps parser
diagnostics, partial checker results and full-project results separate. The
[reader checks](../target/wave202-pathe-root-census-2-reader-controls-result.md)
and [review](../target/wave202-pathe-root-census-2-reader-controls-result-review.md)
are closed. The corrected reader passed the later live census described above.
Pathe is not one fix away from a demonstrated pass. Its original build and
project-pinned compiler check also remain separate requirements.

Seven Pathe changes are combined at `b4ece9d3`. They cover
keyword tuple labels, string-default parameter inference, ordinary property
operands, shared throw statements, function-expression bodies and destructuring
loops, plus typed callable-error locations. The first combined build failed on
two Rust compile errors. Its failed result and cleanup are closed. Both errors
are fixed in reviewed commit `7c6cda70`. The
[compile repair](../target/wave202-pathe-demo-compile-repair-handoff.md) and
[review](../target/wave202-pathe-demo-compile-repair-review.md) preserve all tests.
The repaired build passed in 79.302 seconds. Its ordinary executable, all source
files and all 94 emitted files have closed resource and independent reviews.
The [new build result](../target/wave202-pathe-next-bin-2-result.md) and
[review](../target/wave202-pathe-next-bin-2-result-review.md) are complete.
The unchanged nine-root Pathe census is now complete. It removed the 35 parser
diagnostics but did not complete a root's typecheck.

The corrected six-feature compiler at `a89c891b` builds successfully. The build
took 77.385 seconds, with no Rust errors. Separate cleanup and independent review
are complete. The ordinary project-checking executable is available. Its
[build result](../target/wave202-demo-next-source-bin-2-result.md) and
[review](../target/wave202-demo-next-source-bin-2-result-review.md)
do not claim a passing TypeScript project.

Its focused check compiled and ran all 79 selected tests: 52 passed and 27 failed.
All seven Boolean-negation tests passed. The failures include generic interface
calls, nullish assignment flow, interface heritage, wrapper types and diagnostic
details. The
[complete test log](../target/wave202-demo-next-source-focused-2.cargo.log)
retains every result. Separate cleanup and final result review are closed.

Thirteen repair commits are combined at `dd5e09f9` in a separate source branch.
The [source handoff](../target/wave202-pathe-focused-union-order-handoff.md) and
[independent review](../target/wave202-pathe-focused-union-order-review.md)
are closed. The check retains 408 tests across the binder, checker, parser and
project-error reporting. Its first attempt stopped at an E0308 in a new public
test. Three package builds succeeded, but no test ran. The
[failed gate](../target/wave202-pathe-focused-repairs-1-closure.md) and
[review](../target/wave202-pathe-focused-repairs-1-result-review.md) are closed.
The [one-line fix](../target/wave202-pathe-focused-repairs-compile-fix-handoff.md)
and [review](../target/wave202-pathe-focused-repairs-compile-fix-review.md) are
closed at `38b8e0f1`. It uses the registered `SourceFileRef` without changing
the fixture, assertions or selected tests. Its rerun stopped at the incorrect
import described above. No tests ran.
This includes the optional-property repair. It keeps canonical declared-union
order instead of incorrectly requiring numeric type-ID order. The original
failing test stays unchanged. The diagnostic-only source is excluded.

Computed-key review found a separate bug: missing index evidence can reach an
incorrect `any` result. The repair and focused test are reviewed and committed
at `220334d0`, but have not run. Integration review found another conflict:
contextual widening rejects a valid computed property's real name. That
compatibility repair is now committed with the combined computed-key changes
at `ef87fb20`. Its tests remain unrun. Pathe also needs argument-bearing computed keys
with real `String.raw` tags. The existing computed-key subset does not support
that full expression. The next composition test must use the actual imported
helper and bundled libraries, without replacement declarations. That control
is committed at `f4b568f5`. It retains the exact helper and 93 real library files.
It is an unrun test, not implemented support for the full expression.

The first build failed on two Rust E0308 errors because two calls omitted `Some`
around an optional session. That failed attempt and its cleanup remain in the
[build result](../target/wave202-demo-next-source-bin-1-result.md) and
[review](../target/wave202-demo-next-source-bin-1-result-review.md).
The first 248-test parser command also stopped before compilation because
`cargo test` rejects `--keep-going`. The corrected command passed all 248 tests,
including the three new keyword-tuple-label tests. No test was ignored or filtered.
Separate cleanup and final result review are closed. The later unchanged-input
Pathe census now separately confirms that its 35 loaded-file diagnostics are gone.

The latest core check passed 6,557 of 6,559 tests. All 19 earlier failures now
pass, but two old passes regressed. The latest alias check passed 5,103 of 5,108
tests. All 40 earlier alias regressions recovered. Five alias failures remain.
These are separate candidate builds, not one accepted combined compiler.

Keep TanStack Query core as a cross-project check. Hono and Query have prepared
dependencies, fixed original configurations and complete first-failure records.
Neither is proved close to a full pass. UFO is the second small candidate. Its
seven source roots and 14 separate test files need their original checks,
including Vitest type tests. Its source and tools are verified. Its system-only
isolation probe passed with closed cleanup and independent review. The dependency
install awaits user approval for host-network package requests. No install
process was created and no package tool ran.

| Project | Original source roots | Completed source checks | Unsupported | Other results | Load syntax diagnostics |
| --- | ---: | ---: | ---: | --- | ---: |
| Hono | 188 | 29 | 155 | 3 internal errors, 1 original-policy declaration skip | 0 |
| TanStack Query core | 23 | 1 | 22 | None | 0 |

These are complete first-failure measurements on `6d7a5f06`, not pass rates. A completed
source check does not include a complete diagnostic comparison. Both ordinary
project controls failed. Every original source root has an outcome. One binary
checked both projects. Both commands and separate cleanup are closed. The raw
streams, counts, root lists and loaded graphs are verified. Independent review
and the complete 58-file output seal are closed.

The full loaded graphs and root lists are unchanged from the earlier run.
Hono's 55 syntax diagnostics and Query's 25 syntax diagnostics are now gone.
Hono's JSX constants and request constants now complete. All 27 previous Hono
completions remain, including its HTTP status source. Two internal errors now
reach typed unsupported results. Fourteen Hono outcomes changed, including one
printed internal symbol number that is not progress. Query's utils source now
reaches a parameter check instead of the earlier overload-owner refusal.
Its other 23 outcomes, including the ordinary project result, are unchanged.

The saved [Hono stream](../target/wave202-demo-shared-project-census-7-hono.jsonl)
and [Query stream](../target/wave202-demo-shared-project-census-7-query.jsonl)
retain every outcome, complete typed error and loaded diagnostic. The
[complete report](../target/wave202-demo-shared-project-census-7-result.md)
records the source, build, unchanged inputs and closed cleanup. Its
[independent review](../target/wave202-demo-shared-project-census-7-result-review.md)
is closed. The previous complete measurement remains in the
[C5 report](../target/wave202-demo-shared-project-census-5-result.md).

The [Hono result](../target/wave202-demo-hono-first-failure-census-1-result.md)
and [Query result](../target/wave202-demo-query-first-failure-census-1-result.md)
are the older baseline, with independent reviews and closed cleanup. Their
original inputs stay fixed.
Query means its production core package, not React Query or the whole monorepo.

Tiny-invariant's first Rust measurement is now complete. All five original roots
and the ordinary check stop at unsupported operations. Its original Node10
module-resolution option also produces TS5108. The project-pinned TypeScript
5.3.3 reference reports no diagnostics, but the loaded graphs differ: 168 files
in the reference and 30 in Rust. Node and Jest declarations are among the
reference-only files. This is not a same-input diagnostic comparison or a pass.
The [complete result](../target/wave202-tiny-invariant-rust-measurement-1-result.md)
and [independent review](../target/wave202-tiny-invariant-rust-measurement-1-result-review.md)
retain all six failures, graph differences and closed cleanup. The original
config stays unchanged. Tiny-invariant is no longer the first clean-demo target.

## What works and what is not verified

An earlier core check passed 6,422 Rust tests on `57e743da`.
The selected original corpus has 423 exact diagnostic results in 511 executions
and 62 exact semantic results in 95 executions. These are limited test sets,
not complete TypeScript compatibility.

The latest core/parser check on `c70de1f9` ran all 6,559 tests in 163 harnesses.
It passed 6,557 and failed two. All 275 required controls passed. No test was
ignored, filtered or left unrun. Formatting, Clippy and the fixture build passed.
All 19 failures from the earlier 6,550-test run now pass. Nine new controls also
pass, but two previously passing contextual object-property arrow tests fail.
The related source work remains on hold. The
[complete core/parser result](../target/wave202-core-parser-combined-full-5-quality-report.md)
and [independent review](../target/wave202-core-parser-combined-full-5-quality-runtime-review.md)
retain the full comparison. Runtime, separate cleanup and review are closed.
The gate is failed. The primary branch still uses the previously accepted source.

The five parser repairs are committed at `b1746a95`, with 28 new tests.
The shared project run now confirms that all 55 Hono syntax diagnostics and
all 25 Query syntax diagnostics disappear with unchanged input graphs.
The focused parser check passed all 363 tests across 27 harnesses. All 335 old
tests and all 28 new controls passed. Independent review and cleanup are closed.
The [parser result](../target/wave202-hono-parser-syntax-focused-1-runtime.md)
records the complete selection.

The library batch at `0508192a` adds 94 tests. Its first check stopped on 38
Rust compile errors across 11 files. No tests ran. The repairs are committed
and combined with the exported interface-method owner fix at `555cac5e`.
Its next check ran all 5,258 library tests. It passed 5,099 and failed 159.
All three new exported-method controls passed. The public-test build then
stopped on two incorrect test API accesses, leaving 1,248 public and compiler
tests unexecuted. The [library result](../target/wave202-demo-hono-library-queries-focused-2-runtime.md)
has independent review and closed cleanup. Those two API accesses are now
fixed in the shared source. That correction has not been compiled yet.

The class batch at `0530aa6c` compiled. Its complete library stage passed 5,178
of 5,241 tests, with 63 failures. The public stage timed out at 900 seconds.
All 931 public rows remain incomplete. The full check failed. These results
retain the original tests and assertions. The
[class result](../target/wave202-class-two-repair-focused-2-runtime.md)
records the timeout and complete library outcomes.

The alias batch at `26337753` completed all 5,099 tests. It passed 5,082 and
failed 17. Four old failures now pass, and no old passing test regressed.
Independent review and cleanup are closed. The
[alias result](../target/wave202-alias-wrapper-numeric-method-focused-1-runtime.md)
retains every failure. The next repair batch stopped at a test import error
before listing any of its 5,104 tests. That one-line import fix is committed
and independently reviewed at `bc967441`. Its fresh retry completed all 5,104
tests with 5,094 passes and 10 failures. Eight old failures now pass. Nine old
failures remain, and one new control fails. No old passing test regressed.
Separate cleanup is closed. The
[new alias result](../target/wave202-alias-five-repair-focused-3-runtime.md)
has independent review. This batch is not accepted yet. Three test setup
repairs and the generic partial-property repair are now combined and reviewed
at `d5f0d448`. Its fresh diagnostic check completed all 5,105 tests, with 5,099
passes and six failures. All 50 required controls passed. Four old failures now
pass, the new property control passes, and no old passing test regressed. I
checked all outcomes against their raw log spans and verified all 22 saved
payload hashes. Separate cleanup is closed. The
[latest alias result](../target/wave202-alias-repair-focused-4-runtime.md)
and [independent review](../target/wave202-alias-repair-focused-4-runtime-review.md)
retain all six failures. This is still a failed gate.
The written conditional-argument proof repair is source-reviewed and committed
at `2c443dcf`. The unique-symbol property repair is source-reviewed and committed
at `c79055e9`. Their source integration is committed and independently reviewed
at `f9b477c4`. Its next check failed compilation on three calls to an absent
`EscapedName::is_late_bound` method. All 5,107 tests remain unrun. Separate cleanup
and saved-result review are closed. The three exact `.as_ref()` corrections are
committed and independently reviewed at `979dfe7b`. Its fresh check ran all
5,107 tests: 5,060 passed and 47 failed. All four public tests passed. Required
controls split 51 passes and one failure. Forty old passes regressed, all six
old failures remain, and one of the two new controls fails. Separate cleanup
passed. The [saved-result review](../target/wave202-alias-repair-focused-6-runtime-review.md)
is closed. The complete
[failure blocks](../target/wave202-alias-repair-focused-6-failure-blocks.md)
remain available. The [conditional regression plan](../target/wave202-alias-focused-6-conditional-regressions-plan.md)
and its review found a new collector using the wrong planning-membership set.
The first stop is proved in two old tests and the new control. The one-file
membership repair is committed at `7ad6a0b9`, with one new control and a closed
[commit review](../target/wave202-alias-written-plan-membership-repair-commit-review.md).
It preserves the old callable checks and all existing test inputs and assertions.
The fresh check ran all 5,108 tests: 5,103 passed and five failed. All 53 required
controls passed. It recovered 42 of the previous 47 failures, including all 40
old-pass regressions, and retained all 5,060 previous passes. The
[latest alias result](../target/wave202-alias-repair-focused-7-runtime.md)
and [independent review](../target/wave202-alias-repair-focused-7-result-review.md)
are closed, including separate cleanup. The gate remains failed. This is not a
project result or approval to promote the source.
The [failed build](../target/wave202-alias-repair-focused-5-runtime.md) remains
separate from the older 5,099 passing and six failing test outcomes.

The first shared project compiler is committed and independently verified at
`b71b4158`. It combines the repaired library, class work, core, parser and
project reporter. It also adds conditional expression operands, annotated
local callbacks, object-method captured writes and imported interface heritage.
All 859 source files match the reviewed commit. Its source inventory has
7,293 tests in 235 harnesses, including the two test API corrections above.
These tests have not run on that combined source. Its first project build
failed on an access to a nonexistent AST field. Neither project ran. The
[failed build result](../target/wave202-demo-shared-project-census-2-result.md)
has an independent review and closed cleanup. The exact one-line correction
is committed and independently reviewed at `3b293b28`. All tests stay unchanged.
Its retry compiled the checker library, then failed on three incomplete error
matches in the compiler driver. Neither project ran. The
[latest build result](../target/wave202-demo-shared-project-census-3-result.md)
has independent review and closed cleanup. The one-file driver repair is
committed and independently reviewed at `069ebad6`. It keeps internal errors
separate from unsupported language features and adds two classification tests.
The next run built that repair in 78 seconds. The same binary checked Hono
in 336 seconds and Query in 38 seconds. That earlier run had 26 Hono source
completions and one Query completion. The 7,295 selected tests did not run in
that project measurement.

Separate repair pairs committed fixes for three causes linked to 35 measured
library failures: conditional alias publication, warm union preparation and
property-kind checks. The last group includes one test setup correction.
These are source fixes, not 35 new passing tests. Later assertions still need
execution.
The separate namespace query selection repair is also committed and reviewed
at `b879db17`. Its first failing operation is shared by 20 measured tests.
Those tests have not run on the repair. The four fixes are now combined and
source-reviewed at `035a0751`, with 7,296 selected names and 559 required controls.
The earlier C5 project measurement used that source. Its build took
74 seconds, Hono took 335 seconds and Query took 40 seconds. That measurement
did not run the unit tests.

Separate import fixes are committed at `0a6254d8` and `7074c8c3`. The exact
source-file setup correction for 14 tests is committed at `3356aa21`.
All three have independent source review. Their source integration is committed
and reviewed at `60ab0675`. It contains 7,300 test names. Preparation and peer
review are complete for a diagnostic check of all 5,368 checker-library tests.
The programs remain disabled. The selection includes 356 required controls.
The other 1,932 tests and 230 required controls are outside that focused check.
These source counts are not passing-test results.

The next project compiler batch is committed and independently source-reviewed
at `a3ef2928`. It combines constructor-owner, merged-interface-call, readonly-array
and exported-overload repairs. Its build failed after 37 seconds with one Rust
E0599 error. A namespace check calls `is_empty` on an AST `SymbolTable` that is
a unit struct. Neither Hono nor Query ran. The main and separate cleanup are
closed. The [saved build result](../target/wave202-demo-shared-project-census-6-result.md)
and [independent review](../target/wave202-demo-shared-project-census-6-result-review.md)
retain the failure. All 24 saved output hashes and modes are verified.
That failed build produced no project outcomes.

The exact one-line correction is committed and independently verified at
`6d7a5f06`. It keeps all real binder and owner checks. The latest project run
built that source in 73 seconds and checked both unchanged projects. Its results
are in the table above. The batch's 7,318 test names remain source metadata,
not test results. The shared function/arrow local-variable repair at `76811b77`
is now combined with typed fields and the compile correction at `d1762098`.
Both source intervals have independent review. Its 7,346 selected tests have
not run. The Rust library-and-tests check at `b2b33bad` failed with two more
test-code API errors. Seven of nine required artifacts compiled. No test body
ran, and separate cleanup passed. Both exact corrections are committed and
independently verified at `589725e1`. They change only a test import and one
private validator call. The TypeScript inputs and assertions stay unchanged.

## Next work

1. Fix the four combined-build diagnostics and rerun compilation. Build the
   project-checking executable, then check unchanged Pathe and fix its next
   typed stops. Run the retained tests and verify the separate template and
   method changes. Keep the normalizer and callback failures visible until
   their causes are found. Keep diagnostic-only source out of production.
2. Run Pathe's original build and project-pinned typecheck separately. Compare
   its loaded files before and after the build. Obtain approval for UFO's install
   and verify its dependencies, then check its seven source roots and separate
   14-file test contract.
3. Combine and verify the committed Hono and Query repairs, including the
   P1/P2 source integration at `81fec0a2`. Its source review is complete, but it
   has no runtime result. Run full test verification separately from the first
   demo.
4. Fix the five remaining alias failures within the released work. Keep held
   source and the two held core regressions unchanged. Preserve every old result
   before accepting a batch.
5. Use the reporter's now-passing focused tests to proceed to a full project
   diagnostic comparison. Show a deliberate type error in a separate copy with
   its correct code, message and location.

The next demo must show a complete ordinary project check, not just cold-root
coverage. Missing diagnostics, unchecked declarations and unsupported operations
must remain visible. The source-only repair count is not the demo's pass count.

The latest measured Pathe first stops are from census 3 on the diagnostic
source, not the newer combined source:

| Original files | First stop | Next action |
| --- | --- | --- |
| `src/_glob.ts` | A later arrow block | Locate the underlying failure. Census 3 did not explain it. |
| `src/_internal.ts` | Function body | Keep the normalizer's callable failure separate from the branch-join repair. |
| `src/_path.ts` | Function-expression initializer | Measure again after the combined body repairs. |
| `src/index.ts` | New expression | Measure the integrated stored-arrow guard and check Proxy's handler separately. |
| `src/utils.ts` | New expression | Clear the combined compile errors and run the five constructor tests. |
| `test/glob.spec.ts` | Arrow parameter | Test the integrated contextual callback donor. |
| `test/index.spec.ts` | Computed object key containing a call | Check real `String.raw` and imported-helper composition. |
| `test/node-glob.spec.ts` | `for...of` statement, with an inner conditional failure | Test the committed `TemplateSpan` owner fix and measure again. |
| `test/utils.spec.ts` | Internal callable error with a typed arrow location | Locate its cause. Census 3 emitted no callable trace. |

These are first stops, not a complete list of remaining failures. The six-feature
integration and its 79 focused tests remain separate from the next demo binary
build. The full checker suite must not delay a useful diagnostic measurement.
Source review does not turn any of these repairs into a passing test result.

The diagnosis coordinator read all 16 project reports. Of 181 assigned failure
rows, 160 have a located source cause, 18 remain unresolved and three overlap
work that is on hold. Eight implementation pairs now have separate worktrees.
They target 34 distinct first failures. That is not a forecast of 34 completed
files, because later failures can appear after each repair.

All eight feature commits now have independent source review and verified
commit contents. They add 55 controls. Those controls have not run. The generic
constructor batch's separate Rust error, a question mark applied to a bool,
is corrected and independently verified at `fcaf8610`. Rust compile checks for
all eight batches are prepared or in final preparation review. The first actual
generic-class check stopped on four Rust API errors in an inherited public test
file. Its normal library compiled, but its required test targets were not reached.
No TypeScript test ran. The shared test-only correction at `36a3e127` is now
applied and independently verified on all nine isolated bases.
The next import-annotation and generic-class Rust checks both failed on another
shared test API mismatch. Their required feature targets compiled, but the whole
checks failed. Both raw errors and separate cleanups are retained.

The second correction at `b2b33bad` changes one snapshot argument to the existing
registered source-file API. It preserves every TS input, option and assertion.
The same exact one-line patch is now committed and independently verified on
P1 through P7. P8 does not contain that test and remains unchanged. The
[application report](../target/wave202-shared-source-file-ref-test-api-applications.md)
and [independent review](../target/wave202-shared-source-file-ref-test-api-applications-review.md)
record all seven complete source identities. The corrected P1 and P2 checks
now compile successfully, including all enabled checker tests and all four and
five required artifacts. A separate [recovery audit](../target/wave202-p1-p2-build-recovery.md)
verified unchanged inputs and no remaining owned processes, services or locks.
The original cleanup commands remain unrun and their saved packets remain
incomplete. That history is not replaced by the later closure check.
No test body ran. The new isolated P1/P2 source integration is complete at
`81fec0a2`. Its [source review](../target/wave202-demo-p1-p2-integration-review.md)
confirms both signed checkpoints and all 20 retained donor controls. It has no
runtime result. P3 through P6 requests are source-reviewed. P8's first request
stopped at an environment check before Cargo or target creation. Its new request
binds the actual recorded environment without changing it. P7 remains on hold.
Source review is not proof that a batch compiles or checks a project.

| Repair pair | Feature commit | Work in the commit |
| --- | --- | --- |
| Import annotations | `1bfd3f96` | Preserve real imported type owners and annotation children. |
| Generic class fields | `3960ebe7` | Check `new Set<TListener>()` through real declared generic constructor signatures. |
| Constructor annotations | `d2129b2c` | Publish single-constructor parameter types through the existing query path. |
| Local class exports | `9be223b9` | Follow the original class and named export owners. |
| Type reexports | `07fc299c` | Follow the full named and star reexport chain. |
| Arrow context | `0dc85701` | Use real imported function-type aliases for parameter context. |
| Typed async arrows | `99e04df7` | Check written parameter and `Promise<T>` return types. |
| Equality conditions | `ce649181` | Check both operands through the shared statement engine. |

The imported-arrow barrel cases still need the explicit reexport connection
and imported class-owner work. These feature commits do not complete their roots.

Nine further bounded Hono and Query repairs have independent source approval.
They cover empty derived classes, optional method parameters, typed arrow object
parameters, predicate arrows, contextual overloads, contextual arrow bodies,
shared `for...of`, named library constraints and defaulted implementation parameters.
The first four were combined at `3023dea1`, with 27 added control groups. They
are now combined with the diagnostic reporter and latest API corrections at
`0b8e389d`. The [source handoff](../target/wave202-demo-first-four-reporter-integration-handoff.md)
and [independent review](../target/wave202-demo-first-four-reporter-integration-review.md)
verify that combination. Its ordinary project-tool build completed in 73.796
seconds, including queue time. It recorded 52 compiler-artifact events and 94
unique output files. The [build result](../target/wave202-project-tool-0b8e389d-build-1-result.md)
and [independent review](../target/wave202-project-tool-0b8e389d-build-1-result-review.md)
confirm the executable, unchanged source and closed separate cleanup. No test or
project ran in that build. Full test verification remains unrun.
These controls have no passing result on the combined source. Separate pairs
completed the contextual join at `84d261d4` and the remaining three-feature join
at `660ab8d6`. Their [contextual review](../target/wave202-c7-contextual-integration-review.md)
and [three-feature review](../target/wave202-c7-remaining-three-integration-review.md)
are closed. Both are source-only results, with no compiler or test execution.
Each repair can expose a later unsupported operation in its original project file.

Six new source/test pairs have committed repairs in separate worktrees for 11
distinct measured first failures. They cover `!`, `in`, `string & {}`, inherited
interface properties, generic interface call parameters and `??=`. The nullish
assignment commit is `24ce2343`, with a closed
[source/test review](../target/wave202-demo-nullish-assignment-review.md).
These six repairs are integrated at `ad7c6f90`. Their
[source review](../target/wave202-demo-six-feature-integration-review.md) is closed.
The first binary build failed on the two session-argument errors described above.
The corrected build at `a89c891b` passed. Its 79-test check then passed 52 and
failed 27. The batch adds 41 tests, but that source count is not a pass count.
The failures are now under separate investigation. The
[repair tasks](../target/wave202-next-project-repair-candidates.md) record exact
errors, file ownership and positive and negative tests. Eleven first failures
do not predict 11 passing roots. Three exact expectation changes are approved
for these six features. The generic call-owned type-parameter case keeps its
105-byte TypeScript input and changes unsupported to owner and replay success.
The primitive scalar-to-empty-object relation keeps its original call and input
and changes one expected `Err` to `Ok(true)`. The incompatible inherited
interface-property override keeps its 144-byte TypeScript input and changes
unsupported to TS2430. These approvals do not permit changes to other tests.

The shared try/catch/throw implementation is committed and independently closed
at `0ddc0f07`. Typed synchronous returned arrows are committed at `381a3191`
after source/test review. Neither has run. Callable alias heritage is independently
closed at `6146022d`. Duplicate script-global recovery is closed at `907b67dc`,
also without a runtime result. These source changes must not increase the
measured project counts until the combined project check executes.

The diagnostic-payload implementation is committed at `d96b2801` and combined
with the newer source at `362ad62f`. Source and test review are closed. It keeps
complete ordinary diagnostics and marks cold or failed snapshots as partial.
It retains the first checker failure without extra type queries. The failed
post-source collector limit remains explicit.

Its first focused check compiled and listed all 297 compiler tests, then the
evidence reader confused two distinct Cargo outputs. That attempt left all
310 selected tests unrun.
Separate cleanup and the [failed-result review](../target/wave202-census-diagnostic-payloads-focused-1-result-review.md)
are closed. The fresh check passed all 310 tests: 297 compiler tests, three
public diagnostic tests and 10 project-report tests. None failed or was skipped.
The [result account](../target/wave202-census-diagnostic-payloads-focused-2-result-account.md)
records all outcomes and a separate audit of source, artifacts and actual
process, service and lock closure. The original terminal tool receipt is
missing and the original post-close step remains unrun. Those limits and the
earlier failed result stay explicit. This is not a full project diagnostic
comparison or a result for the newer combined compiler.

The generic-constructor work has a second source/test pair with separate file
ownership. The imported-arrow work also depends on the import and reexport
repairs. These dependencies remain explicit. The
[ownership and priority report](../target/wave202-census-4-failure-priorities.md)
records the measured failures, separate later limits and original assignment.

The new [early Rust compile protocol](../target/wave202-early-rust-compile-plan.md)
uses the existing three-job limit. It checks Rust APIs before broad integration,
including test code when needed. A compile result is not a passing TypeScript
test or project result.

The [small-project audit](../target/wave202-small-modern-demo-selection.md)
records the exact cached revisions and original build contracts. Pathe has five
source files and four tests. UFO's source config has seven roots, but its 14
separate test files and Vitest type tests need their own complete check. UFO also
has an original `@ts-nocheck` file, which must not count as checked code.
Mitt and sourcemap-codec select the same removed Node10 option as tiny-invariant.
Their configs stay unchanged. No smaller root list or omitted ambient package
counts as a complete project check.

Pathe's [input acquisition](../target/wave202-pathe-input-acquisition-1.md) and
[independent review](../target/wave202-pathe-input-acquisition-1-review.md) are
closed. Its first system-only isolation probe failed on incompatible `findmnt`
flags. Cleanup and complete input checks passed. No package tool ran in that
attempt. The later locked dependency install exited 0. Its
[saved result](../target/project-inputs/wave202-pathe-inputs-1/evidence/package-isolation-2-install/result)
records command, cleanup and input statuses of 0, with `closed=1`. The complete
[installed-input review](../target/wave202-pathe-package-isolation-2-install-review.md)
is now closed. It verified all 124 applicable installed packages, file contents,
command shims, links and unchanged original inputs. Native payloads are present,
but their runtime behavior and the original build remain untested.
The [ordinary Go CLI plan](../target/wave202-pathe-go-cli-preparation.md) uses one
offline build of the exact pinned compiler. The existing instrumented test binary
will not replace the ordinary reference command. That ordinary build passed,
and its [independent review](../target/wave202-pathe-go-cli-build-1-result-review.md)
verified the compiler artifact, unchanged inputs and closed cleanup. No project
reference check ran in that build. The later
[ordinary Go reference](../target/wave202-pathe-reference-check-1-result.md)
and [independent review](../target/wave202-pathe-reference-check-1-result-review.md)
are closed. All nine roots checked with zero diagnostics. The 277 loaded files
include nine roots, 175 dependency files and 93 bundled libraries. The original
options and diagnostic directives remain unchanged. This is the port's pinned
Go reference, not Pathe's project-pinned compiler or a Rust result. It does not
prove full structured-diagnostic or module-resolution parity.

The first [Rust Pathe report](../target/wave202-demo-project-check-1-pathe.json)
records construction as unsupported, code `E00.SOURCE_SYNTAX`. Its error names
an arrow in `src/_glob.ts`, but supplies no typed source range. The original
project config was used. Graph, diagnostics, type artifacts, symbol artifacts
and replay are unavailable. Missing diagnostics are not zero diagnostics.
The [terminal receipt](../target/wave202-demo-project-check-1-terminal-receipt.json)
records one actual execution after an approval timeout, with main exit 0.
That exit does not mean the project passed. The
[complete result](../target/wave202-demo-project-check-1-result.md) and
[independent review](../target/wave202-demo-project-check-1-result-review.md)
are closed. Separate post-close verification exited 0 and confirmed unchanged
inputs, executable and saved evidence. The compiler limitation remains open.
The earlier build and Go reference closures remain separate facts.

UFO's [input plan](../target/wave202-ufo-input-preparation-plan.md) and review are
closed. Its [acquisition report](../target/wave202-ufo-input-acquisition-1.md)
records all 39 original files and both verified tool archives in a separate
directory. [Independent acquisition review](../target/wave202-ufo-input-acquisition-1-review.md)
is closed. The exact pnpm 10 [install controls](../target/wave202-ufo-pnpm-controls.md)
have [independent approval](../target/wave202-ufo-pnpm-controls-review.md).
The [system-only probe](../target/wave202-ufo-package-isolation-1-probe-result.md)
and [independent review](../target/wave202-ufo-package-isolation-1-probe-review.md)
are closed. The probe exited 0 with unchanged inputs and verified isolation.
No package tool ran in that probe. The install's first permission request timed
out. The identical retry was denied pending informed approval for host-network
package requests. Neither request created an install process. User approval is
pending. UFO keeps its own Node, pnpm, build and type-test requirements.

Source workers have separate worktrees and test partners. Shared merge work
has explicit file ownership and one Git coordinator. At most three Cargo
checks run at once. Completed tests, exact diagnostics and whole-project
results measure progress, not worker count.

No configuration weakening, smaller root list, missing dependency, suppressed
diagnostic or replacement `any` counts as progress. A full-project demo and
acceptance of the complete compiler remain separate claims.

The [longer plan and earlier results](typechecker-demo-plan.md) retain the work
history. I do not have evidence for a reliable full-project completion date yet.
