# First complete project demos

Updated 2026-08-30. The full port goal remains active.

## Decision

Make TanStack Query core the first complete-project demo target. Make Hono the
second. Use their existing production typecheck configurations, not a new app
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

Newer branches have useful results but are not accepted whole-project builds.
The latest interface run passed 5,177 of 5,202 test executions. It cleared 28
old failures and retained 25 failures, including one regression. One of those
28 improvements includes an approved test setup correction. The JSDoc run
passed all 88 selected public tests, but seven checker tests still failed.
These runs overlap and must not be added together as unique passing tests.

A separate full core check passed 6,393 of 6,395 tests in 133 harnesses at
`713a5211c21dd1dfd654cb612a23f5b585fca048`. Formatting, strict Clippy and both
binary builds passed. The failures are an invalid literal-cache test setup
and a missing union-type route for class method parameters. Both fixes are
combined at `88fae170a9f422b2fb109abf4e8fb9553c60a0e0`. The next full run expects
6,399 tests, including four new private controls. It has not run yet. This
result does not replace the accepted original test subset.

Combined core/interface source `3571142fc7fb7f6e3e23346370e668c2b90b4939`
passes the complete workspace all-target compile check. One unused-method
warning remains. This result does not prove that tests or projects pass.

## Selected projects

| Target | Complete upstream scope | Why use it | Fresh Rust construction result |
| --- | --- | --- | --- |
| TanStack Query core | `packages/query-core/tsconfig.prod.json`, 23 roots | Strict ESNext/Bundler package. Dependencies and declaration outputs are prepared. Saved Go cold and warm diagnostics are empty. | Unsupported arrow in `timeoutManager.ts`. |
| Hono | `tsconfig.build.json`, 188 roots | Strict library build with ES2022 target. Dependencies are prepared. Saved Go cold diagnostics are empty. | Unsupported class in `http-exception.ts`. |

Roots are not the complete dependency graph. The saved Go runs load 186 files
for Query core and 352 for Hono. The first target does not include React Query
or the entire TanStack repository. The second does not include every Hono
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
defaults. Those repairs are committed but not yet runtime-verified. The first
heritage test run failed to compile its tests. That test API repair is now
committed. One first failure does not tell us how many remain.

The Query source audit identifies missing contextual typing for the first
two-parameter object-property arrow. Its declared `TimeoutProvider` property
must supply both parameter types before the normal body check. The repair
uses that general rule. It does not change the timer code or assume its return.
The repair is committed with four private and five public tests. It is being
combined with the newer checker before its first test run.

A wider source audit covers all 23 Query roots. It finds more missing behavior,
including generic class bodies, optional calls, generic function-type aliases,
and branching callback bodies. Query is not one or two fixes from a proved
complete pass. Separate workers now implement the shared source features.
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
UFO, pathes and RailwaySDK. Sourcemap-codec has a strict four-file build config,
but its dependencies are not prepared and its typed-array field initializer
hits a current class-planning guard. The others have dependency or configuration
limits. None is a measured short path to a complete strict project pass. The
[smaller-project assessment](../target/wave202-demo-small-project-alternatives.md)
records the exact limits. No project input was changed for that assessment.

The local [project assessment](../target/wave202-demo-prepared-project-assessment.md)
contains the exact input and result hashes. This plan changes scheduling. It
does not lower the [full port completion criteria](typechecker-completion-goal.md).
