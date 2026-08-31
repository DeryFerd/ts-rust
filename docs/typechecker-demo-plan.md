# First complete project demos

Updated 2026-08-30. The full port goal remains active.

## Decision

Make Hono the next complete-project demo target. Keep TanStack Query core as
the second target. Hono's immediate class repairs are committed and reviewed.
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

The accepted original test subset has 423 exact diagnostic results in 511
executed variants and 60 exact semantic results in 95 variants. These are not
percentages of the complete TypeScript test suite or project compatibility.
The measured compiler source is `5c7c7bd20cb45ebc8f2171eed8478fa2797e8343`.
New source candidates remain in separate worktrees. They have not replaced
that accepted compiler on the primary branch.

The full core check is green at
`4f7397046c08de663fede5e5281884bbbc092092`. All 6,399 tests passed in 133
harnesses. All eleven stages passed, including formatting, strict Clippy,
4,886 checker units, parser and compiler tests, fixture tests, and both tool
builds. All 201 required test names ran. The complete original
`ambiguousCallsWhereReturnTypesAgree.ts` fixture passed diagnostics, types and
symbols. The [complete result](../target/wave202-next-full-core-gate-7-report.md)
does not replace the accepted original test subset. Its complete corpus
comparison is being prepared separately.

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

The Query contextual-arrow candidate ran all 5,114 selected checker and public
tests. It passed 5,064 and failed 50. Five failures are in the new controls.
Their diagnosis found three test-helper failures and two missing calls to
existing checker code. The other 45 failures now have source diagnoses.
Several share a generic-call validation error during repeated checking. This
is a measured integration result, not fifty separate missing language features.
The [full failure report](../target/wave202-demo-contextual-arrow-focused-2-report.md)
retains every failed test. No result from this run is added to another run.

## Selected projects

| Target | Complete upstream scope | Why use it | Fresh Rust construction result |
| --- | --- | --- | --- |
| Hono | `tsconfig.build.json`, 188 roots | Strict library build with ES2022 target. Dependencies are prepared. Saved Go cold diagnostics are empty. | Unsupported class in `http-exception.ts`. |
| TanStack Query core | `packages/query-core/tsconfig.prod.json`, 23 roots | Strict ESNext/Bundler package. Dependencies and declaration outputs are prepared. Saved Go cold and warm diagnostics are empty. | Unsupported arrow in `timeoutManager.ts`. |

Roots are not the complete dependency graph. The saved Go runs load 186 files
for Query core and 352 for Hono. The Query target does not include React Query
or the entire TanStack repository. The Hono target does not include every Hono
test, example, or project reference.

Both fresh checks ran once on clean compiler `db4988b261625c67d770f9d6290b9684d6395680`.
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
negative control. Its three positive controls stop in a test helper. Those
failures still need diagnosis and are not passes. Optional named fields
and imported conditional class annotations are also committed and reviewed,
but not runtime-verified.
One first project failure does not tell us how many remain.

The Query source audit identifies missing contextual typing for the first
two-parameter object-property arrow. Its declared `TimeoutProvider` property
must supply both parameter types before the normal body check. The repair
uses that general rule. It does not change the timer code or assume its return.
The repair is committed with four private and five public tests. Its first
complete test run is recorded above. The follow-up patch preserves the actual
arrow return, source property identities, parameter order and body diagnostics.

A wider source audit covers all 23 Query roots. It finds more missing behavior,
including generic class bodies, optional calls, generic function-type aliases,
and branching callback bodies. Query is not one or two fixes from a proved
complete pass. Separate workers now implement the shared source features.
Generic class methods, generic class bodies, optional calls, branching arrow
bodies and generic function-type aliases are committed and source-reviewed.
Their runtime checks remain pending. Executable class
imports now have a separate implementation team. Generic construction has a
reviewed design and waits for the class-body provider. These audit findings do
not predict the next runtime failure.

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
