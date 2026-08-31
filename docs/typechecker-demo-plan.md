# First complete project demos

Updated 2026-08-31. The full port goal remains active.

## Decision

Make Hono the next complete-project demo target. Keep TanStack Query core as
the second target. Three unchanged Hono class-annotation tests now pass,
including rejected status codes and renamed imports. The full Hono run still
stops on an unavailable interface declaration in `http-exception.ts`.
The latest trace identifies the merged DOM and Node `Response` declarations.
The library batch already addresses the observed declaration guard. It still
needs a complete runtime check on the combined source.
Query still needs more source-language features before its next complete check.
This changes the work order, not the acceptance criteria.
Use their existing production typecheck configurations, not a new app
or a reduced source list. These are selected targets, not projects proved close
to passing. No complete real-world project has passed in Rust yet.

New checker work should address a measured failure in one of these projects,
a shared dependency of that failure, or a regression that prevents integration.
Finish the current bounded patches. Do not start more unrelated feature
batches while the demo path remains unmeasured.

## Current evidence

The latest complete core check passed all 6,422 tests in 136 harnesses on
`57e743da`. All eleven stages and all 228 required controls passed, including
all 729 public checker tests. Separate cleanup is complete. Independent
result review confirms every outcome. The [complete result](../target/wave202-core-corpus-3-repair-full-4-quality-report.md)
and [independent review](../target/wave202-core-corpus-3-repair-full-4-quality-runtime-review.md)
retain all test names and build evidence. This is a Rust test-suite result,
not a full-project pass or full TypeScript compatibility. The original corpus
comparison is now running on this same source. It has no result yet.

The latest Hono run on `33ebb2f0` built in 70 seconds, then failed construction
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
or Hono passes. The batch's final source review is still in progress.
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
original corpus comparison is running under its separately reviewed packet.

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
| Hono | `tsconfig.build.json`, 188 roots | Strict library build with ES2022 target. Dependencies are prepared. Saved Go cold diagnostics are empty. | Three public class-annotation tests pass. Full project still stops on an unavailable interface declaration. |
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
Source work is paused because its validation paths extend beyond the proposed
file list. The scope review must close before edits resume.
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
in progress. Two complete numeric and method backports are committed at
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

1. Run the validated root-failure reporter on the unchanged Hono project.
   Keep its ordinary control separate from isolated-root results. The complete
   313-test prerequisite and independent result review have passed.
2. Finish and test the library batch that addresses the observed `Response`
   declaration guard. Do not claim success from its source coverage alone.
3. Group measured Hono failures by their first shared checker operation.
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
test pass does not mean that Hono passes. Its original-project census is being
prepared with all 188 roots and a fixed time limit.

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
