# First complete project demos

Updated 2026-08-31. The full port goal remains active.

## Decision

Make Hono the next complete-project demo target. Keep TanStack Query core as
the second target. The latest Hono trace exposed an exact annotation-role bug.
Its narrow repair is committed and under test, separate from the larger class batches.
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

The latest Hono run still stops during construction. It builds correctly, but
does not return a diagnostic set. Two source audits prove that its imported
constructor annotation fails a node-adjacency assumption when the parameter
has a default value. The immediate task is to retain the actual annotation
field. That repair is committed at `e7e58fd8`. Its fresh test run includes
the unchanged valid and invalid default-value controls. The next project run
will use the same original Hono configuration and dependencies.

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

The full core check is green at
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
retains each record. A separate pair is repairing the display rule.

The combined four-repair core candidate is committed at `73f50f94`.
The previous candidate, `77d7f4c1`, passed formatting, then failed strict Clippy
before any test or corpus ran. The six-line style correction is reviewed.
The new full check completed all 6,418 tests in 136 harnesses, with 6,410
passes and eight failures. All 224 required names ran. The failures are five
checker tests, two fixture-library tests and one baseline CLI integration
test. All 729 public checker tests and 285 compiler tests passed. Separate
cleanup is complete. The original corpus did not run because the full check
failed. This candidate is not accepted.

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
invalid default-value tests stay unchanged. The fresh focused run selects all
5,174 tests and ten required controls. It has no result yet. The
[commit review](../target/wave202-demo-class-annotation-roles-commit-review.md)
records the exact source. The next diagnostic Hono source combines that whole
repair with the unchanged error observer.
A repaired first failure will not establish that the rest of Hono passes.

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
| Hono | `tsconfig.build.json`, 188 roots | Strict library build with ES2022 target. Dependencies are prepared. Saved Go cold diagnostics are empty. | Imported constructor annotation fails a proved source-role check. Repair committed and under test. |
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
the current session type. All 6,149 selected tests, including 72 additions,
remain unrun. Separate cleanup and evidence review are complete. The narrow
correction will pass the session's existing optional global Array targets.
The [closed result](../target/wave202-demo-generic-project-integration-focused-1-runtime.md)
retains the full compiler error. The two later generic-class plans use the
actual `4cab980e` APIs and share file ownership. Their implementation is not
part of this gate.

The first named-bounds build on `3f32cc52` stopped on one test-helper type
mismatch before any of its 5,176 tests ran. Its one-site correction is now
committed and independently reviewed at `0e1b34e6`. A new focused packet
keeps the full selection and all nine required controls. Neither candidate
has a passing runtime result yet.

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
retains every failure. Twelve read-only groups now cover all 74 failures
exactly once. These failures include earlier class defects. They are not
74 proved regressions caused by field support.

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
Their combined source and test plan is being checked before integration.
These are repairs for first failing operations, not new passing test results.
Four separate test-setup corrections are also approved. They preserve the
original TypeScript, options, semantic assertions and query order.
Executable class imports are committed and reviewed at `c295104c`, with eight
new private and eight new public tests. Generic construction is committed and
reviewed at `d2a6a8a3`, with 16 new private and four new public tests. Neither
feature has a valid runtime result yet.
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

1. Run both original configurations on one recorded current compiler build.
   Verify source, config, root lists, libraries, dependencies, and generated
   declarations first. Record construction failures as failures.
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
The team has reached 40 active subagents. This is a worker count,
not a speedup measurement. New builds must not reuse another source worktree's
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
