# Typechecker demo status

Updated 2026-08-31. No complete real-world project has passed in Rust yet.

## Targets

Use Hono and TanStack Query core as the two main project targets. Both have
prepared dependencies, fixed original configurations and complete first-failure
measurements. Neither is proved close to a full pass. Hono stays the first
integration target. Query tests whether the same fixes work in another codebase.

| Project | Original source roots | Completed source checks | Unsupported | Other results | Load syntax diagnostics |
| --- | ---: | ---: | ---: | --- | ---: |
| Hono | 188 | 27 | 158 | 2 internal errors, 1 original-policy declaration skip | 55 |
| TanStack Query core | 23 | 1 | 22 | None | 25 |

These are first-failure measurements on `db8eda9a`, not pass rates. A completed
source check does not include a complete diagnostic comparison. Both ordinary
project controls failed. Every original source root has an outcome.

The [Hono result](../target/wave202-demo-hono-first-failure-census-1-result.md)
and [Query result](../target/wave202-demo-query-first-failure-census-1-result.md)
have independent reviews and closed cleanup. Their original inputs stay fixed.
Query means its production core package, not React Query or the whole monorepo.

## What works and what is not verified

The latest complete core check passed 6,422 Rust tests on `57e743da`.
The selected original corpus has 423 exact diagnostic results in 511 executions
and 62 exact semantic results in 95 executions. These are limited test sets,
not complete TypeScript compatibility. Two supported artifact mismatches still
prevent acceptance. Their fixes are combined at `e6ced336` and have not run.
The primary branch still uses the previously accepted compiler source.

The five parser repairs are committed at `b1746a95`, with 28 new tests.
Static diagnosis links them to all 55 Hono syntax diagnostics and all 25 Query
syntax diagnostics. This does not prove those diagnostics disappear in a run.
The full parser check is being prepared. Its correct inventory is 363 tests,
including six old included tests missed in the first source-only count.

The library batch at `0508192a` adds 94 tests. Its first check stopped on 38
Rust compile errors across 11 files. No tests ran. Six independent repair
groups now own those files. The errors include production API mismatches and
test setup errors. They are not TypeScript diagnostics.

The class batch also stopped before tests, on two symbol-name ownership errors
in a test. The exact two-line correction is committed at `0530aa6c`. Its next
check keeps all 6,172 selected tests and their original assertions.

The exported interface-method owner fix is committed at `8a5b1345`. It targets
Hono's LambdaContext declaration and adds three focused controls. It has not run.

More source work is complete, but the latest batches have no new passing test
results yet. Compilation and integration are the immediate delay to the demo.

## Next work

1. Compile and test the parser, class and repaired library batches. Keep every
   existing test and report all failures.
2. Combine their complete histories with the core repairs and existing project
   reporter. The class/library join has real code and test-contract conflicts.
   It needs review. Do not replace one branch's implementation with the other.
3. Run both unchanged projects on that combined source. Do not wait for every
   later feature patch to finish before measuring the next project failures.
4. Prioritize the next actual failure and any shared dependency. Repeat until
   the ordinary project check returns complete diagnostics that match Go.
5. Show the clean result, then add one deliberate type error in a separate copy
   and show the correct diagnostic and location.

Seven source tasks are active alongside the compile repairs:

- Imported interface heritage with real import and generic-default ownership.
- Exported function overloads with a separately checked implementation.
- Exported abstract class declarations.
- Binary and nullish expressions in ternary conditions and Boolean branches.
- Callback types from an annotated local variable.
- Annotated local variables without initializers, with assignment checks.
- Captured local writes from object methods, using the actual binder flow.

Each source task has its own worktree and a test partner. Each compile repair
has explicit file ownership and a reviewer. At most three Cargo checks run at
once. Worker count is not a progress measure. Completed tests, exact diagnostics
and whole-project results are the measures.

No configuration weakening, smaller root list, missing dependency, suppressed
diagnostic or replacement `any` counts as progress. A full-project demo and
acceptance of the complete compiler remain separate claims.

The [longer plan and earlier results](typechecker-demo-plan.md) retain the work
history. I do not have evidence for a reliable full-project completion date yet.
