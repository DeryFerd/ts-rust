# First complete project demos

Current execution rules are in [accountability](typechecker-accountability.md),
[saved state](typechecker-state/current.json) and the
[September 5 reset plan](typechecker-reset-plan.md). The execution instructions
below are historical. Full port requirements remain in force.

Updated 2026-09-03. The full port goal remains active.

Read the [current demo status](typechecker-demo-status.md) first. It has the
latest complete Hono and Query measurements, build failures and next work.
The detailed results below retain earlier checkpoints and their evidence.

## Execution reset

Query core is the immediate target. Hono is a periodic cross-project check.
Do not add more demo libraries or feature branches.

Root is the sole implementer and owns the integration index. The agent
`query_timer_context_peer` is the sole reviewer. Other agents may answer
specific read-only questions, but must not create production or test changes.
All existing branches, commits and dirty drafts stay preserved. Runtime owners
may close checks that started before this reset, with no follow-on stages.

Use the existing `query-core-integration` branch in
`target/worktrees/query-hono-project-integration-2`. Reuse the current build
target, `target/worktrees/next-core-build-1`. Root owns both. The candidate is not
accepted, and no pending feature branch joins automatically.
The last integration checkpoint is `5a1882c5d`. Both complete, Go-checked
merged-member tests now pass, but the regression selection loses 54 previous
checker passes. The checkpoint is rejected for promotion. Repair those losses
before more Query feature work. A separate reference-flow draft still changes
six files in that worktree. It is not committed or promoted. Query still does
not complete. The accepted compiler remains unchanged.

The [next shared member-resolution task](query-core-member-resolution.md)
records the exact Go order, reusable Rust identity code, default/base/member
gaps, caller changes and current regression repair order. Continue there.
Do not repeat a broad source audit or add another isolated admission rule.

### Regression baseline

Compare with the last accepted compiler, measured at
`5c7c7bd20cb45ebc8f2171eed8478fa2797e8343` and promoted as equivalent source
at `8f4943ac6dffa6785165e18a07a5b369a6811da7`. Recent failing candidates are
not substitutes for this baseline.

The [accepted gate](../target/wave202-core-class-call-integration-2-receipt.md)
passed all 6,055 selected tests in 120 harnesses. The new
[complete checker selection](../target/query-core-accepted-checker-baseline-1-result.md)
ran all 110 accepted public targets with the checker library on unchanged
`eb996907`. Exact name comparison gives:

| Accepted selection | Retained passes | Failures | Missing or not run |
| --- | ---: | ---: | ---: |
| Checker library, 4,839 tests | 4,601 | 228 | 10 |
| Public checker tests, 677 tests | 651 | 24 | 2 |
| Compiler library, 285 tests | 0 | 0 | 285 |
| Fixture library, 188 tests | 0 | 0 | 188 |
| Fixture binary tests, 4 tests | 0 | 0 | 4 |
| Fixture integration tests, 61 tests | 0 | 0 | 61 |
| Complete original class fixture, 1 test | 0 | 0 | 1 |
| Total | 5,252 | 252 | 551 |

These 252 failures require an explanation or a repair. The 551 missing or unrun
tests are coverage gaps, not passes. New passing tests cannot offset either
group. Record each old test by harness and full name, with its current outcome,
cause, evidence and disposition. Keep unknown causes explicit. A changed
expectation needs a concrete pinned TypeScript-Go comparison before approval.

The [first contract correction](../target/query-core-interface-demand-1-result.md)
accounts for two of those failures. Go's interface identity query leaves
inherited members cold. Both tests now demand a real inherited property before
checking complete caches. All earlier behavior checks remain, and both complete
tests pass. This test-only change is committed as `2bf54614a`. It is not a
production repair or a Query improvement. The original baseline is unchanged.

The first production repair is committed on the integration branch as
`6652447c7`. It retains every frozen baseline pass and restores two old behavior
tests. Together with the two test corrections, accepted-name totals are now
5,256 checker passes, 248 failures and 12 absent names. The remaining compiler
and fixture tests have now run. The [complete comparison](../target/query-core-accepted-complete-baseline-1-result.md)
has 5,792 accepted passes retained, 250 failures and 13 absent names across all
120 accepted harnesses. [Query is unchanged](../target/query-core-interface-demand-query-1-result.md).
The next batch follows the measured merged global-variable failure below.

The [new complete test comparison](../target/query-core-integration-baseline-2-result.md)
on `de557d99c` plus the preserved reference-flow draft retains 5,789 accepted
passes, loses 253 and has 13 absent names. All 120 accepted groups ran. Only
the three previously recorded reference-flow losses change outcomes against
the last full checker and compiler/fixture selections. The exact loss list is
complete, but cause analysis and repair are not.

The [accepted original corpus](../target/wave202-core-class-call-corpus-2-receipt.md)
has 423 exact diagnostic records in 511 executed variants. Its separate
95-variant type/symbol selection has 60 exact top-level diagnostic records,
55 exact type comparisons and 62 exact symbol comparisons. Preserve each accepted diagnostic, type and symbol
payload, not just the total count. Run these same selections before promoting
a batch. Missing outputs, crashes and new mismatches block promotion.

The [base-resolution repair](../target/query-core-base-resolution-repair-1-result.md)
retains every one of baseline 2's 6,325 passing tests. Accepted-name counts stay
at 5,789 pass, 253 fail and 13 absent. No expectation changed. The complete
positive and negative schema tests still fail, so this is only a crash repair.

The [new complete corpus checks](../target/query-core-base-resolution-repair-1-corpus-result.md)
ran all 511 diagnostic variants and all 95 type/symbol variants without a
process crash. The diagnostic comparison retains 400 of 423 old exact records,
has 23 changed exact records and 12 fatal records. Every type/symbol variant
row matches baseline 2, including its old losses. None of these results permits
promotion. The previous diagnostic run aborted, so the new complete loss list
does not establish which batch caused each loss.

The [latest complete selection](../target/query-core-source-member-operation-regression-2-result.md)
at `5a1882c5d` plus the unchanged reference-flow draft retains 5,765 accepted
passes, loses 277 and has 13 absent names. It loses 54 passes from the previous
integration selection, including 24 accepted passes. Both new complete member
tests pass. Compiler and fixture outcomes are unchanged. Every new and old loss
remains a promotion blocker. No expectation changed. The corpus was not rerun
on this rejected batch, and its earlier losses remain open.

Repair the shared member-state validation and inherited callable paths first.
Do not add the separate conditional alias admission patch. Full conditional
method-return support also needs source-aware evaluation and replay.

### Work loop

1. Select one failing Query operation. Trace it through the pinned Go checker
   and the actual Rust callers. Identify the required context, state and
   publication order. If successive changes hit cache or ownership checks,
   examine the shared path before adding another exception.
2. Implement the complete operation on the integration branch. Keep original
   project inputs, compiler options, libraries and expected diagnostics fixed.
3. Compile implementation, library test helpers and public test code. Run
   focused positive and negative cases, then rerun unchanged Query on that build.
   Use the existing runner,
   normal logs, actual tool permissions and resource limits.
4. Have the single reviewer check the complete change and results. Do not add
   preparation reviewers, repeated approval messages or new feature owners.
5. Run the accepted regression selections before promotion. Account for every
   lost pass, absent test and changed native record. Do not accept a batch with
   unexplained regressions or unrun required tests.
6. Report retained and lost passes, exact diagnostic changes and whether
   ordinary Query checking completes. A later first failure is diagnostic
   evidence, not a completed feature.

After two batches without a meaningful Query result, stop adding patches and
reassess the dependency path. More workers are not the fallback. Run Hono after
a meaningful Query milestone or a shared-path change that needs a cross-project
check, rather than after every local edit.

### Earlier operation: merged ambient global values

The [current class observation](../target/query-core-class-annotation-observation-1-result.md)
did not reproduce the earlier type-literal cache failure on the integration
branch. Its bounded cache trace emitted no failure records. Applying the
preserved method-union change moved ordinary Query to an unsupported variable
read. The project still did not complete, and all diagnostics stayed unchanged.

The [variable observation](../target/query-core-variable-symbol-observation-1-result.md)
identified the rejecting function and symbol metadata. It is a variable
declaration in another file with a merged transient symbol. It has no
instantiation flag, target or mapper. An instantiated-parameter repair would
address the wrong operation. Both observations retained every prior outcome
and diagnostic except the two recorded changes in stopping point.

The shared source planner reaches cross-file variable handling only after a
CrossFileDeclaration result. This merged variable is rejected earlier as
NonVariableSymbol. The existing declared-value reader already checks saved
global declaration order, raw merge edges, global augmentation ownership,
selected annotation and cache provenance. Extend that operation as follows:

1. Resolve the identifier in its real lexical scope. Require the result to
   match the saved global binding. Local variables and imports must still hide
   a global with the same name.
2. Select the value declaration from saved declaration order, then check the
   mutable symbol against it. Keep raw declaration, export, local placeholder
   and global augmentation parent checks. Do not allow TRANSIENT by itself.
3. Query the selected declared value through the canonical query, with the
   host, globals, options, aliases and session. Keep normal type preparation,
   source context, selected member demand and value provenance.
4. Compile implementation and tests. Check duplicate declarations, global
   augmentation, class reads, local shadows, exact positive and negative
   results, query order and replay. Rerun unchanged Query and the accepted
   regression selections before accepting this batch.

The draft shares the existing script-origin global proof. It does not claim
support for globals introduced first by an augmentation. The selected Query
annotation form is not inferred from numeric IDs. Let the canonical query
identify the actual dependency. The method-union change remains unaccepted
until the combined batch passes its checks. No other class branches join.

### Reassessment: class conditions and branch flow

The first ambient global-value draft passed 39 focused tests, but gained no
complete Query root. Together with the interface repair, this is two batches
without a complete project gain. The corrected full regression selection closed
with three new lost library passes. Regression check 3 repairs all three and
retains every previous integration result. The fresh Query run still has two
complete isolated roots and an unsupported ordinary check. All diagnostics match
the integration baseline. This batch has closed. Do not add another syntax rule.
Implement the condition and branch-flow operation together as described below.

The latest ordinary failure is the enclosing binary expression. The static
class statement path accepts only a property compared with undefined in this
position. The class executor also needs a matching branch-flow snapshot. These
are separate requirements. Accepting a new expression form alone will fail
later or lose narrowing.

The next complete operation must carry the condition through planning, binder
branch edges, normal expression checking, branch-specific narrowing and call or
assignment invalidation. Reuse existing general condition checking where its
context is complete. Preserve class member and parameter identities. Test both
branches, global and class properties, negation, logical composition, exact
operand errors and replay. Do not label arbitrary conditions as Unchanged.
Keep the class body's declared ambient-global types separate from outer mutable
local narrowing. Retain its real binder container, read points, assignments,
calls and branch edges through both planning and execution.

The pinned Go checker checks the full condition normally in checkIfStatement.
Its flow query separately narrows the referenced type for the true or false
branch. This is the structure to port. The actual Query operand form remains
unread under the source restrictions. Confirm the rejecting predicate with a
bounded trace or a focused case before editing this path.

### Current reference-flow draft

The bounded condition observation identified a property access compared with a
string using !==. The draft now carries reference identity and checked condition
values through real binder branch edges. All three new public cases pass with
fixed types, symbols, errors and replay checks. Three previous library passes
now fail unsupported-result assertions. They remain blockers until the original
cases have concrete pinned-Go comparisons. No expectation has changed.

The merged variable-and-namespace repair is now committed as `de557d99c`.
It proves the namespace contributions and complete export merge, then retains
the selected variable annotation. The shared property reader follows the same
value-selection order. All three new public cases pass with exact diagnostics,
ownership, cold queries and replay. Pinned Go confirms their diagnostic results.
No existing expectation changed. These results cover the combined working tree.

[Unchanged Query](../target/query-core-variable-namespaces-query-1-result.md)
still has only two complete isolated roots and unchanged diagnostics. The old
ownership error is gone. Ordinary checking now rejects the optional `send`
method in Node's `process.d.ts`. This is evidence for the next shared-path check,
not a complete project gain.

The complete reference-flow operation also needs retained checked member-write
state. The existing shared assignment path checks the RHS but does not keep its
member value in the frame. Reuse the real member lookup, normal RHS checker and
assignment reduction. Keep the live class frame through receiver and RHS checks.
Exact writes must use their checked flow type. Prefix writes must reset nested
references. Unrelated writes must retain facts. Direct-this writes and the old
arrow path must keep their behavior.

Before promotion, rerun the full accepted selections and original corpus on the
final bytes. The new focused passes do not offset old failures or absent tests.

### Next shared operation: inherited interface member lookup

The [bounded observation](../target/query-core-inherited-interface-observation-1-result.md)
confirms the actual caller. Both affected attempts fail in
`preflight_type_from_type_node`, before selected-property lookup. All 244
non-runtime Query records remain unchanged. The observation was removed and
the original integration fingerprint was restored.

There are two heritage guards, in the interface-identity preflight and the
source lazy-member selector. The selected annotation is `NodeJS.Process`, which
extends `EventEmitter`. The latter is a merged generic interface and class with
a default parameter. The existing direct-interface planner and the separate
nongeneric ambient-class import proof do not complete that base operation.

Pinned Go keeps separate work for declaration identity, member tables and base
types, and the selected member's type. Its member-table resolver does not obtain
every named method's type. Port that behavior through the actual Rust callers
with their real query context and retained state. Keep base substitutions,
canonical member owners, call/construct/index signatures and warm-cache checks.
Complete declaration checking must still run when that phase is requested.

Use one shared operation for these distinct states: declared identity, known
own members, resolved bases and inherited members, and selected member type.
An own-member query may leave bases pending. It must not report an inherited
member as absent, complete a structural relation or set completion flags while
bases are pending. The merged class base must use its actual import route,
parameter identities, defaults and substitutions. Do not substitute a plain
class identity for the defaulted base type.

Do not only remove the heritage guard or add a special case for `send`. Test
own and inherited property reads through a merged generic class base, including
its default argument, without resolving unrelated named method types. Then
query a method explicitly and require its correct type. Include deliberate
errors, source-first and query-first checks, and replay. Compile all test code,
run the focused cases, rerun unchanged Query, then run the accepted selections
before promotion. Keep the existing one-implementer and one-reviewer setup.

### Immediate milestone

Complete ordinary Query core checking with diagnostics matching pinned Go.
Then introduce a deliberate type error in a separate copy and require the
correct diagnostic. Do not change the original project to obtain a pass.

Full type, symbol and replay parity remain requirements for the finished
compiler. This first milestone does not waive them.

## Earlier evidence

The sections below preserve historical results. They do not authorize work
under the reset above.

The latest complete core check passed all 6,422 tests in 136 harnesses on
`57e743da`. All eleven stages and all 228 required controls passed, including
all 729 public checker tests. Separate cleanup is complete. Independent
result review confirms every outcome. The [complete result](../target/wave202-core-corpus-3-repair-full-4-quality-report.md)
and [independent review](../target/wave202-core-corpus-3-repair-full-4-quality-runtime-review.md)
retain all test names and build evidence. This is a Rust test-suite result,
not a full-project pass or full TypeScript compatibility. The original corpus
comparison has also completed on this source. Diagnostics remain 423 exact
results in 511 executions. Exact semantic results improved from 60 to 62 in
95 executions, with 31 unsupported results and two supported mismatches.
There are no fatal or unknown outcomes. Every earlier exact result remains
unchanged. The [complete corpus result](../target/wave202-core-corpus-3-repair-corpus-4-preparation-runtime.md)
and [independent review](../target/wave202-core-corpus-3-repair-corpus-4-preparation-runtime-review.md)
are closed. The corpus is still red, so this source is not accepted.

The two remaining supported mismatches concern a namespace-qualified symbol
name and an extra `undefined` in a printed optional parameter. The optional
parameter fix is committed at `da6d8be7`, with seven new tests that have not
run. The namespace-symbol fix is under source review. Its review found a
missing-link replay case that still needs correction. The original expected
artifacts will not change. A first differing line does not prove that all
later lines are correct.

The complete Hono census is now closed on `db8eda9a`. It checked all 188
original roots in separate fresh checker contexts. It recorded 27 source-check
completions, 158 unsupported results, two internal errors and one skip under
the original declaration-file policy. No root was left unvisited. These are
not 27 diagnostic-free files. Complete checker diagnostics remain unavailable
for each isolated root. The ordinary-order control also failed.

The load phase separately recorded 55 syntax diagnostics in ten original
source and dependency files. Five parallel investigations traced them to
parser rules, including arrow lookahead, type-argument lookahead, computed
members, keyword-named members and conditional type starts. One parser writer
and separate test owners are implementing the fixes on the tested core source.
No repaired parser result is claimed yet. The [complete census](../target/wave202-demo-hono-first-failure-census-1-result.md),
[independent review](../target/wave202-demo-hono-first-failure-census-1-result-review.md)
and [all 188 root outcomes](../target/wave202-demo-hono-first-failure-census-1-root-ledger.md)
retain the original inputs, separate diagnostics and closed cleanup.
The source failures also show missing function-body, async, generic-class and
callable support. Hono is not one library fix away from full checking.
A matching census for Query core is in preparation to compare the remaining
work on its complete 23-root production project.

The earlier Hono run on `33ebb2f0` built in 70 seconds, then failed construction
after 5 seconds. It does not return a diagnostic set. The trace identifies the
Node `Response` variable inside `declare global` in `@types/node/globals.d.ts`.
The merged-interface planner rejects that contribution because its source file
is an external module. The later multiple-variable restriction is a separate
source finding, not a second observed failure.
Both runtime stages, separate cleanup and independent evidence review are
closed. The [latest project result](../target/wave202-demo-hono-isolated-probe-7-report.md)
and [review](../target/wave202-demo-hono-isolated-probe-7-runtime-review.md)
preserve the complete trace. The [library source comparison](../target/wave202-demo-hono-library-query-batch-handoff.md#probe-7-compatibility-with-the-fixed-b-planner)
shows that the current batch already covers both guards through the real
declaration-owner checks. It does not prove that the full `Response` query
or Hono passes. The batch is now committed at `0508192a` with complete source
and commit review. Its 94 added tests have not run. Build and test preparation
is next. The [source review](../target/wave202-demo-hono-library-query-batch-review.md)
keeps that distinction explicit.
The original Hono configuration, 188 roots and dependencies remain unchanged.

The latest alias repair run completed 5,094 tests, with 5,074 passes and 20
failures. All five targeted failures now pass. All 5,069 passes from the
previous run remain passed. The new relation control fails before its
assertions because a nongeneric alias that wraps a generic function alias is
still unsupported. Nineteen older failures remain. This is not a project pass
or an accepted compiler. The class integration separately completed 6,149
tests, with 6,014 passes and 135 failures. These selections overlap and must
not be added together.

The accepted original test subset has 423 exact diagnostic results in 511
executed variants and 60 exact semantic results in 95 variants. These are not
percentages of the complete TypeScript test suite or project compatibility.
The measured compiler source is `5c7c7bd20cb45ebc8f2171eed8478fa2797e8343`.
New source candidates remain in separate worktrees. They have not replaced
that accepted compiler on the primary branch.

Those acceptance sets mix TypeScript-submodule and Go-owned originals.
The TypeScript-only results are 283 exact diagnostics in 348 executions and
seven exact semantic results in ten executions. An older full case-attempt
census on `79d44b12` recorded 1,537 exact diagnostic results in 13,101
configuration rows, plus 25 cases without a complete result. It did not
compare type or symbol artifacts. Neither measurement proves current full
TypeScript compatibility. The [coverage audit](../target/wave202-original-typechecking-corpus-coverage-audit.md)
separates the complete scope, old census and current acceptance sets.

An earlier full core check passed at
`4f7397046c08de663fede5e5281884bbbc092092`. All 6,399 tests passed in 133
harnesses. All eleven stages passed, including formatting, strict Clippy,
4,886 checker units, parser and compiler tests, fixture tests, and both tool
builds. All 201 required test names ran. The complete original
`ambiguousCallsWhereReturnTypesAgree.ts` fixture passed diagnostics, types and
symbols. The [complete result](../target/wave202-next-full-core-gate-7-report.md)
does not replace the accepted original test subset. Its complete corpus
comparison finished with a regression. All 423 exact diagnostic records remain
unchanged. The semantic run has 60 exact results, 31 unsupported results and
four artifact mismatches in 95 variants, with no crashes. One previously exact
type artifact now prints `typeof foo` instead of the expected object shape in
`invocationErrorRecovery.ts`. That regression prevents acceptance. The three
old crash cases have changed outcomes, not three accepted passes. The
[full semantic result](../target/wave202-core-class-source-next-artifact-corpus-3/semantic.json)
retains each record. The later repair candidates below address this regression.

The combined four-repair core candidate is committed at `73f50f94`.
The previous candidate, `77d7f4c1`, passed formatting, then failed strict Clippy
before any test or corpus ran. The six-line style correction is reviewed.
The new full check completed all 6,418 tests in 136 harnesses, with 6,410
passes and eight failures. All 224 required names ran. The failures are five
checker tests, two fixture-library tests and one baseline CLI integration
test. All 729 public checker tests and 285 compiler tests passed. Separate
cleanup is complete. The original corpus did not run because the full check
failed. This candidate is not accepted.

The five-file repair batch at `5948cd84` keeps the original fixture diagnostics
and type/symbol expectations. Its complete check ran 6,422 tests in 136
harnesses. It passed 6,421 and failed one. All eight previous failures now
pass. All eleven stages completed, including all public, compiler and fixture
tests. All 228 required names ran, with 227 passes and one failure. The
[complete result](../target/wave202-core-corpus-3-repair-full-3-quality-report.md)
records the unchanged source and closed cleanup. The
[independent result review](../target/wave202-core-corpus-3-repair-full-3-quality-runtime-review.md)
is complete.

The sole failure is the new ambient-export display snapshot. Forced source
replay advances `next_relation_observation_token` by exactly one. Independent
diagnosis confirms that every other store field and the diagnostics stay
exact. The committed correction checks that specific counter change while
retaining all other byte comparisons. Its display and damage assertions
remain intact. The complete 6,422-test check now passes on `57e743da`. The
[diagnosis](../target/wave202-core-full3-symbol-display-failure-diagnosis.md)
and [review](../target/wave202-core-full3-symbol-display-failure-review.md)
record the scope. No production fix is proposed for this failure. The corrected
full check, separate cleanup and independent result review are complete. The
original corpus comparison has also closed. It preserves all earlier exact
results, but the two supported artifact mismatches above prevent acceptance.

The newer combined core/class source is
`aea8d39c730a2db79e4d2fae965f5b164d1240bf`. Its full checker run passed 5,981
of 6,041 tests in 171 harnesses. The library harness passed 5,113 and failed
28. Public tests passed 868 and failed 32. No test was ignored or filtered.
All runtime services closed and the source stayed unchanged. The
[complete result](../target/wave202-demo-core-class-focused-2-result.md) records
all 60 failures. The previous run had 114 failures. The closed logs show 54
recovered old failures and no newly failed names.

That source combines two shared replay repairs. One keeps saved generic call
signatures on the existing generic validation path. The other completes the
operand plan for warm numeric-intersection queries. The new replay control
and all three private numeric controls passed. All old test inputs remain
unchanged. The two public numeric controls still fail and have a separate
committed repair awaiting runtime checks.

All 16 tests in four JSDoc overload harnesses also passed in the newer run.
They had failed in the previous run with unchanged parser and test source.
The latest run records actual executable hashes and Cargo dependency metadata.
The historical cause remains unproved. Do not assign every recovered test to
the two source repairs. These runs overlap and must not be added together as
unique passing tests.

A later generic-class-body run exposed a build-cache problem. The intended
source has 5,162 library tests, but Cargo ran the previous candidate's 5,143
test inventory. All 22 new private controls were absent. The saved service
record confirms the correct working directory and command. The old executable
and dependency records remained in the shared target. That run does not verify
the new class-body code. The [full result](../target/wave202-demo-generic-class-bodies-focused-1-report.md)
keeps the failed validation and all original evidence.

Hono builds now use new, empty source-specific targets. Each build checks
the actual Cargo artifact records before the project run. We do not copy or
delete old build caches. Cargo uses relative source paths and modification
times for freshness. Those rules make cross-worktree cache reuse unsafe for
this workflow. The exact local cache decision remains an inference.
[Cargo's fingerprint documentation](https://doc.rust-lang.org/stable/nightly-rustc/cargo/core/compiler/fingerprint/index.html)
describes these rules. This finding does not prove that every older run is wrong.

The first isolated Hono build failed after 37 seconds with Rust E0063.
One qualified class-base initializer lacked its required `constructor_value`
field. The reporter was not built, so no Hono project stage ran. Both runtime
and separate cleanup checks closed. The one-line fix is committed and reviewed
at `9c26f3bbd72bf5cf19ba3c0f73046092131f557b`. All tests and original inputs
remain unchanged. The [repair receipt](../target/wave202-demo-hono-qualified-base-build-repair-commit.md)
keeps its exact source and review evidence.

The second isolated build passed in 69 seconds. Its Cargo records confirm a
fresh reporter, checker and compiler in the new empty target. The full original
Hono command then ran for 5 seconds and stopped with `INV.SOURCE.DECLARED_TYPE`
in `src/http-exception.ts`. The detail is `InvalidTypeReference`. No Program
graph, complete diagnostic set, type or symbol artifact, or replay result was
returned. Both runtime stages and the separate cleanup check closed. The
[complete result](../target/wave202-demo-hono-isolated-probe-2-report.md)
retains all raw output and executable evidence. The 188-root input and all
dependencies remain unchanged. This clears the build failure, not the project
check.

The third isolated run used a diagnostic observer on source `c47b6749`.
Its fresh build passed in 69 seconds. The original project again failed after
5 seconds. The trace identifies `ContentfulStatusCode` in the real
`HTTPException` constructor parameter, `status: ContentfulStatusCode = 500`.
That name comes from the unchanged type-only import of `./utils/http-status`.
Its import alias has no resolved target at the failure. The trace identifies
the reference and its state, not the exact rejecting guard. The existing
class-annotation path supports cold imports, so missing alias links alone do
not prove that an import resolver must run earlier. The
[complete result](../target/wave202-demo-hono-isolated-probe-3-report.md)
retains the trace and both closed runtime stages. No complete diagnostic set,
type or symbol artifact, or replay result was returned.

The fourth isolated run used source `5f913a18`. Its fresh build passed in
69 seconds, and the unchanged Hono project failed after 5 seconds. The trace
now identifies the class-import plan's validation path. Both runtime stages
and the separate cleanup closed. The [complete result](../target/wave202-demo-hono-isolated-probe-4-report.md)
retains all output. It still has no complete diagnostics or artifacts.

The parser creates the annotation, then the default initializer, then the
parameter. The validator instead selects only the node immediately before
the parameter. For the observed parameter 41 and annotation 39, that reader
can return node 40 or no node. It cannot return the actual annotation.
The [source audit](../target/wave202-demo-hono-probe-4-import-identity-audit.md)
and [independent predicate audit](../target/wave202-demo-hono-probe-4-validate-current-audit.md)
agree. The repair at `e7e58fd8` retains the actual parameter/property annotation
role and changes this one validator. It does not warm imports early, remove a
guard, or change Hono. Four private controls were added. Existing valid and
invalid default-value tests stay unchanged. The fresh focused run listed all
5,174 tests. It completed 5,172, with 5,138 passes and 34 failures. The public
constructor-default test passed with all four excluded status codes unchanged.
The run reached its 900-second limit during the second public test. The third
never started. One new private test has a proved holder-count setup error.
The other 33 failures have no same-base before result. The
[closed runtime review](../target/wave202-demo-class-annotation-roles-focused-1-runtime-review.md)
keeps the incomplete result and separate cleanup evidence. The
[commit review](../target/wave202-demo-class-annotation-roles-commit-review.md)
records the exact source. The diagnostic Hono source, `f5b684b5`, combines
that whole repair with the unchanged error observer. Its full project run
returned a different error family, `InvalidInterfaceDeclaration`, while still
checking `http-exception.ts`. The [closed project result](../target/wave202-demo-hono-isolated-probe-5-report.md)
and [independent review](../target/wave202-demo-hono-isolated-probe-5-runtime-review.md)
retain the complete failed result. No graph, diagnostics, artifacts or replay
was returned. Observer-only source `b97f733f` now identifies the real DOM
`Response` declaration. It does not repair the error.
A repaired first failure will not establish that the rest of Hono passes.

The saved Cargo records show optimization level zero. A separate manifest-only
candidate, `7ca0e571`, sets development and test optimization to level one.
It keeps debug assertions and overflow checks enabled. Every checker and test
source byte remains exact relative to `e7e58fd8`, including its known failure.
Its complete run passed 5,140 tests and failed 34, with all 5,174 tests run.
All three public Hono controls passed. All 5,172 prior completed outcomes
remain unchanged, including the exact failure text after thread-ID removal.
The test run took 121 seconds after a 728-second clean build and listing.
Library execution took 21.29 seconds, previously 157.04. The previous clean
build took 148 seconds. This is faster test execution, not a proved overall
development speedup. The [complete receipt](../target/wave202-demo-checker-opt1-focused-1-runtime.md)
and [independent review](../target/wave202-demo-checker-opt1-focused-1-runtime-review.md)
retain both costs. The gate still fails. The holder-count correction is
separately committed at `dd6ed6d8` and has not run.

The Query contextual-arrow candidate ran all 5,114 selected checker and public
tests. It passed 5,064 and failed 50. Five failures are in the new controls.
Their diagnosis found three test-helper failures and two missing calls to
existing checker code. The other 45 failures now have source diagnoses.
Several share a generic-call validation error during repeated checking. This
is a measured integration result, not fifty separate missing language features.
The [full failure report](../target/wave202-demo-contextual-arrow-focused-2-report.md)
retains every failed test. No result from this run is added to another run.

## Selected projects

| Target | Complete upstream scope | Why use it | Last project-stage result |
| --- | --- | --- | --- |
| Hono | `tsconfig.build.json`, 188 roots | Strict library build with ES2022 target. Dependencies are prepared. Saved Go cold diagnostics are empty. | Complete census: 27 source completions, 158 unsupported, two internal errors, one original-policy skip. Ordinary check still fails. |
| TanStack Query core | `packages/query-core/tsconfig.prod.json`, 23 roots | Strict ESNext/Bundler package. Dependencies and declaration outputs are prepared. Saved Go cold and warm diagnostics are empty. | Unsupported arrow in `timeoutManager.ts`. |

Roots are not the complete dependency graph. The saved Go runs load 186 files
for Query core and 352 for Hono. The Query target does not include React Query
or the entire TanStack repository. The Hono target does not include every Hono
test, example, or project reference.

The first two project checks ran once on clean compiler `db4988b261625c67d770f9d6290b9684d6395680`.
Its project reporter was already built. This is a diagnostic candidate with
known component-test failures, not the accepted compiler source.

Neither check returned a Program graph or reached the canonical checker
callback. Cold diagnostics, type and symbol artifacts, and replay are
unavailable. Both processes returned zero because they wrote an unsupported
report. Neither project passed. Source, dependencies, configs, libraries, and
compiler bytes stayed unchanged. Both runtime services are stopped.

The [Query result](../target/wave202-demo-query-current-probe-1-closure.md)
supersedes the old generic-setter trace for this compiler. The
[Hono result](../target/wave202-demo-hono-current-probe-1-report.md) identifies
the class but not its inner rejecting guard. A separate source audit proves
missing constructor-valued heritage and ordinary annotated constructor
defaults. Those repairs have separate source commits. The heritage test run now
reaches both test harnesses. It passed 4,889 of 4,897 tests. All four new private
heritage controls passed, but four old checker controls and all four public
controls failed. The repair is committed at
`2ea6843ab6a5169dfe7344528d90f6e2aa22fc99`. It fixes inherited member ownership,
keeps the actual caller for property diagnostic details, and corrects proved
test setup errors. Its next run stopped on a wrong Rust import path before
either test harness started. All 4,904 tests were unrun. The import-only fix
is committed at `01ac9bb590bfbf03f2f2def53a38974804960b49`. The corrected
focused run completed all 4,904 tests, with 4,900 passes and four failures.
The library passed 4,899 of 4,900. The public harness passed its complete Hono
negative control. Its three positive controls stop in a test helper. The full
diagnosis found two test-only assumptions that need correction: scalar
annotations need not have node-cache rows, and one damaged base-table entry
has a different exact error. The corrections are committed at `c3136bbe`.
Their later assertions still need to run. Optional named fields
and imported conditional class annotations are also committed and reviewed,
but not runtime-verified.
One first project failure does not tell us how many remain.

The separate exported-class constructor repair has now passed both new private
controls and all three unchanged public constructor-default tests. This clears
the two previously failing local exported-constructor tests. Its complete
library run passed 5,115 of 5,143 tests. The remaining 28 library failures stay
visible. This result is not a Hono project pass.

The eight reviewed Hono dependencies are combined at `27347713`. The complete
source integration is reviewed. Its isolated build failed as recorded above.
The corrected candidate `9c26f3bb` built and reached the type-reference failure
recorded above. Further source
audits found named method return annotations, property truthiness flow and
ambient `Response` construction restrictions in the original `getResponse`
method. Five independent pairs have prepared those changes in one new tree.
The complete combined source is committed and reviewed at `1aebb12b`.
It still needs runtime checks.
The next parallel batch addresses the shared DOM/Node owner, alias heritage,
globalThis, conditional, import, defaulted-union and condition queries.
Another batch combines the committed generic class bodies, construction,
methods and executable imports. Each batch has one writer per source file
and one owner for Git changes. Separate workers now implement annotated
array/object field initializers and named/indexed alias bounds. The latter
covers the real `Env`, `Schema` and `Input` bound declarations. Generic methods
on generic classes and imported generic class heritage have reviewed plans.
These are source findings, not the next measured project error.

The class-only batch is committed and independently reviewed at `4cab980e`.
Its first build failed because a relation helper reads a field that is not on
the current session type. No test ran in that attempt. The narrow
correction is committed and reviewed at `3e5383d1`. It passes the session's
existing optional global Array targets. Its fresh run completed all 6,149 tests
in 178 harnesses, with 6,014 passes and 135 failures. All 72 additions ran,
with 27 passes and 45 failures. The [complete result](../target/wave202-demo-generic-project-integration-focused-2-runtime.md)
and [independent review](../target/wave202-demo-generic-project-integration-focused-2-runtime-review.md)
are closed. Seven workers completed separate failure reports. The coordinator
is checking their combined census.
The current shared class-reference repair targets a reader that accepts an
applied class reference, then incorrectly requires an interface payload.
Twelve writers completed a 24-file refactor of its read-only validation paths.
All component source reviews are closed. The combined review is in progress.
Each writer owns separate files. Current entry points keep
their existing behavior. This first phase passes one validation context through
the existing readers. It does not yet admit applied class references.
That second phase still needs a correct rule for recursive validation.
The [closed result](../target/wave202-demo-generic-project-integration-focused-1-runtime.md)
retains the full compiler error. The two later generic-class plans use the
actual `4cab980e` APIs and share file ownership. Their implementation is not
part of this gate.

The first named-bounds build on `3f32cc52` stopped on one test-helper type
mismatch before any of its 5,176 tests ran. Its one-site correction is now
committed and independently reviewed at `0e1b34e6`. Its next run completed all
5,176 tests, with 5,108 passes and 68 failures. All nine new controls failed.
Eight first stops come from a retained reader that rejects the parser's valid
property kind. The ninth comes from an exported-alias owner check. Both reader
repairs are committed and reviewed at `d8fa9fe3`. All original controls stay
unchanged. Of the other 59 failures, 21 match prior source and failure paths.
The other 38 now have complete current-source diagnoses. Twenty-three share
the exported-alias owner check, ten hit a class-only range check on JSDoc
annotations, and three hit the initialized-parameter annotation check. Two
remaining rows concern test setup or the expected error contract. The JSDoc
repair is committed at `3d8b9a80`. Its complete source is being combined with
the annotation-role and holder-count repairs. The combined source review
passed. Commit closure and the 5,187-test check remain separate steps.
None of these repairs has a new runtime result. The
[complete census](../target/wave202-named-bounds-failure-census.md) keeps these
groups separate. No pass gain is predicted.

The first class-field check stopped with six Rust compile errors. No test ran.
The errors came from one missing import and four reads of a private field.
The five-site correction is committed and independently reviewed at
`88a2b6b4`. It uses the existing immutable getter and changes no test or
TypeScript input. The [commit receipt](../target/wave202-demo-class-field-initializers-compile-repair-commit-receipt.md)
records the closed failed build and exact correction. The same 5,195-test
selection still needs a fresh run.

The second class-field build exposed five library-test compile errors and
ran no tests. The four-site test-only correction is committed and reviewed
at `b5be9d54`. It uses the current slice API and clones the full owned payloads
in snapshots. All original inputs and substantive assertions stay unchanged.
The next gate kept all 5,195 tests and 52 required controls. Its name audit
also corrected 12 inventory module paths without renaming any source test.

That third class-field run is now complete and independently checked. It
passed 5,121 tests and failed 74, with no ignored or unrun tests. All 52
required controls ran, with 13 passes and 39 failures. The build and artifact
checks passed. All three new public field tests stopped in their shared
setup helper before the later field assertions. The helper assumes that the
real ES5 Array owner has only interface flags. Its actual merged owner also
has a variable declaration. One new private replay control failed as well.
The [complete result](../target/wave202-demo-class-field-initializers-focused-3-result-receipt.md)
retains every failure. The completed twelve-group census covers all 74 exactly
once. It records 39 proved production first stops, 16 setup errors, seven
expectation conflicts and 12 unresolved causes. These are first stops, not
predicted recovered tests. The two field-control setup corrections are
committed and reviewed at `1f418c8a`. They have no new runtime result. These
failures include earlier class defects. They are not 74 proved regressions
caused by field support.

The Query source audit identifies missing contextual typing for the first
two-parameter object-property arrow. Its declared `TimeoutProvider` property
must supply both parameter types before the normal body check. The repair
uses that general rule. It does not change the timer code or assume its return.
The repair is committed with four private and five public tests. Its first
complete test run is recorded above. The follow-up remains paused and is not
included in the current Hono work.

A wider source audit covers all 23 Query roots. It finds more missing behavior,
including generic class bodies, optional calls, generic function-type aliases,
and branching callback bodies. Query is not one or two fixes from a proved
complete pass. Separate workers now implement the shared source features.
Generic class methods, generic class bodies, optional calls, branching arrow
bodies and generic function-type aliases are committed and source-reviewed.
Their runtime checks are not complete. The generic-class-body run above is
invalid. The first two generic function-alias runs stopped on missing Rust
imports. Both import-only corrections are committed. The third run executed
all 5,080 selected tests and failed 70, including all 17 new controls. A pair
proved two first-stop defects: copied signatures use a declaration-owned
parameter publisher, and alias-owned union references lack their owner proof.
The exact three-file repair is committed at `4232597a`. Its fresh fourth run
executed all 5,084 tests, with 5,028 passes and 56 failures. Fourteen of the
17 old feature failures now pass, and all four new controls pass. No old pass
was lost. Three feature failures remain. All 53 other failures are unchanged.
The [complete result](../target/wave202-demo-generic-function-type-aliases-focused-4-runtime.md)
and [independent review](../target/wave202-demo-generic-function-type-aliases-focused-4-runtime-review.md)
confirm the actual test executables and every outcome. All old inputs and
assertions remain intact. Aliases remain outside the current class-only
integration. This is local feature progress, not a Query project pass.
All 53 other failures now have indexed failure reports. Twenty-one share the
generic-call replay path, and eight share exported function-alias ownership.
Those two repairs are committed and reviewed at `ea201924` and `27ee97f1`.
The direct alias-context repair is committed and reviewed at `7427a715`.
Those three complete repairs and the four test-setup corrections are now
combined in clean commit `8912d642`. Final independent source closure is in
place. Its complete run passed 5,069 tests and failed 24. All 34 required
controls ran, with 29 passes and five failures. Thirty-six of the old 56
failures now pass, and no old pass was lost. All nine added tests ran, with
five passes and four failures. The new replay control, both exported-owner
controls and all four approved setup tests pass. The four new context failures
and the remaining public context test have a separate source diagnosis.
The [complete result](../target/wave202-demo-alias-four-repair-integration-focused-1-runtime.md)
and [independent review](../target/wave202-demo-alias-four-repair-integration-focused-1-runtime-review.md)
retain all 24 failures. The candidate is not accepted. The setup corrections
preserve the original TypeScript, options, semantic assertions and query order.
The five context failures now have a six-line relation repair committed and
reviewed at `915ddea3`. It admits validated function-alias instances to the
existing relation path. It does not force assignability. Its complete run
passed 5,074 of 5,094 tests. All five targeted failures and all 34 older
required controls now pass. No old passing test regressed. The
[complete result](../target/wave202-alias-context-relations-focused-1-runtime.md)
and [independent review](../target/wave202-alias-context-relations-focused-1-runtime-review.md)
are closed. The new relation control does not reach its assertions. Its
original alias-wrapper query is unsupported. That source form needs a real
repair, not a test route that avoids it. That bounded wrapper repair is now
committed at `d0bbe0c9` and independently reviewed. It has not run.
Two complete numeric and method backports are committed at
`3b8640ca` and independently reviewed, but not tested on this receiver yet.
The remaining 19 older failures have a separate completed census.
Executable class imports are committed and reviewed at `c295104c`, with eight
new private and eight new public tests. Generic construction is committed and
reviewed at `d2a6a8a3`, with 16 new private and four new public tests. Neither
feature is proved complete. Both are now included in the full class integration
run recorded above.
These audit findings do not predict the next runtime failure.

Pinned project commits:

- Query: `44645e9eb1dafba5f2f229adb328582075484f36`.
- Hono: `06880c4a2b04de9dd74217f26dd831209b9c01f1`.
- Reference typescript-go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

The saved Go reports fail forced replay checks. Query retains zero diagnostics
but changes type text or identity. Hono gains five diagnostics after artifact
queries. Establish fresh ordinary diagnostic results separately. Do not use
these reports to claim stable replay or complete artifact parity.

## Work order

The immediate demo sequence is:

1. Fix and test the parser rules behind Hono's 55 loaded syntax diagnostics.
   Keep the complete original input as the acceptance check.
2. Test the committed library batch that addresses the observed `Response`
   declaration guard. Run the complete Query-core census in parallel so its
   remaining work is measured before choosing the first finished demo.
3. Use the completed Hono census to group failures by their first shared
   checker operation.
   Give independent groups to separate writer and reviewer pairs. Combine
   the current class, alias and library patches only after their own tests.
4. Run the complete ordinary Hono check after each integrated repair. Continue
   with Query core on the recorded compiler once its shared fixes are ready.

For each project:

1. Preserve the source, configuration, root list, libraries, dependencies and
   generated declarations. Record construction failures as failures.
2. Use the actual failing source to define each repair. Assign independent
   failures to separate writers. Assign a peer to check the Go algorithm and
   focused tests. Root combines shared checker changes.
3. Recheck the complete selected project after each integrated blocker repair.
   A small reproducer helps diagnose a failure. It does not replace this check.
4. Once construction and checking finish, compare every diagnostic against a
   fresh Go run on the same input. Match diagnostic codes, locations, messages,
   and related information. Account for all roots and reachable dependencies.
5. Produce a repeatable CLI demo. Check the original project, then a separate
   copy with a deliberate type error. Both compilers must reject that error at
   the correct location. Keep the original prepared input unchanged.
6. Complete type and symbol comparison and resolve the replay limitation as
   separate steps toward the full port goal.

Use a compiled diagnostic candidate to find the next whole-project blocker
while unrelated artifact or replay repairs continue. Record its known test
failures and do not promote it as accepted. This keeps project measurement
moving without changing the original inputs or the full completion criteria.
The demo still needs a complete ordinary diagnostic check and the separate
deliberate-error check. An unsupported report is never a successful demo.

A separate diagnostic reporter is committed at `db8eda9a` to measure failures
hidden behind the first project stop. Its first gate stopped on an incomplete
artifact identity key before any test body ran. The corrected gate keeps both
real `unicode-ident` output identities. It has now passed all 313 tests,
including all 16 new controls, in a fresh target. Complete artifact checks,
separate cleanup and independent review also passed. The [result](../target/wave202-project-first-failure-census-focused-2-runtime.md)
and [review](../target/wave202-project-first-failure-census-focused-2-runtime-review.md)
preserve all outcomes. The old failed result remains unchanged. This reporter
test pass does not mean that Hono passes. The original-project census is now
complete and independently reviewed. Its fresh build took 70 seconds and
the census took 334 seconds. All 188 roots returned an outcome before either
deadline. The ordinary invariant and all 55 load diagnostics remain separate.
Main execution returned 2. Separate cleanup returned 0 and all 36 saved
output hashes were verified. No complete Hono check or replay pass follows.

The reporter loads the complete original Program, runs the ordinary-order
control first, and checks each root in a fresh checker context. It records
every root, incomplete attempt and failure. These isolated-root results will
guide parallel repairs. They will not count as a normal complete-project pass.

The existing development entry point is `tsgo --check-canonical PROJECT`.
It fails if construction is unsupported or canonical checking did not run.
A project reporter can exit successfully after writing an unsupported result.
Its process exit code is not proof that typechecking succeeded.

## Parallel work and progress reports

Use one integration owner and two project owners. Other workers can implement
independent source, class, inference, relation, or library failures needed by
these projects. Give each writer a fixed worktree and file list before edits.
Keep review and reference checks in parallel with implementation. Keep the
existing build limits. Forty agent slots do not authorize forty Cargo builds.
The target is up to 40 useful parallel workers. A worker count is not a
speedup measurement. New builds must not reuse another source worktree's
target directory. Keep one owner for each target and at most three compiler
services at once.

Judge progress by whole-project checks and resolved old failures, not lines
ported, new test counts, or the number of active agents. Each project report
must name the compiler commit, input pins, actual first failure, completed
checking stages, and any diagnostic differences. Report separately whether a
patch is written, reviewed, integrated, tested, or proved on the whole project.

## Deferred demo candidates

React Hook Form remains a useful later target. Its current `T['length']` repair
is not yet tested, and its recursive path types and JSX are not proved end to
end. Its app also has diagnostics with the pinned Go version.

ts-pattern is a useful strict type-system test, but its unchanged configuration
has a recorded TS5011 diagnostic. A new audit also checked sourcemap-codec,
UFO, pathe and RailwaySDK. Sourcemap-codec has a strict four-file build config,
but its dependencies are not prepared and its typed-array field initializer
hits a current class-planning guard. The others have dependency or configuration
limits. None is a measured short path to a complete strict project pass. The
[smaller-project assessment](../target/wave202-demo-small-project-alternatives.md)
records the exact limits. No project input was changed for that assessment.

Two additional source audits checked tiny-invariant and Mitt. Tiny-invariant's
unchanged strict config has five roots, including its tests. It needs mixed
early-exit function bodies, annotated async arrows and its full dependency
graph. Mitt has three roots and needs generic callback aliases, generic object
methods, dependency types and generated declarations. Neither has run through
the Rust checker or proved a shorter route to a complete demo. Their small
implementation files are not substitutes for their full configurations.

The local [project assessment](../target/wave202-demo-prepared-project-assessment.md)
contains the exact input and result hashes. This plan changes scheduling. It
does not lower the [full port completion criteria](typechecker-completion-goal.md).
