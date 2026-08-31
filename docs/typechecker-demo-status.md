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
prevent acceptance. Their fixes are combined with the parser at `706299ac`.
Its first full check stopped at a parser function-length lint. The correction
at `3b45a90d` passed formatting in the second check, then stopped on three
Clippy findings. All 6,550 tests remain unrun on that source. The
[latest core/parser result](../target/wave202-core-parser-combined-full-2-quality-report.md)
retains every compiler error and the nine unattempted stages. The three small
lint fixes are committed and independently reviewed at `4a09da42`. A fresh
check of the same 6,550 tests is being prepared. The artifact fixes still need
execution. The primary branch uses the previously accepted compiler source.

The five parser repairs are committed at `b1746a95`, with 28 new tests.
Static diagnosis links them to all 55 Hono syntax diagnostics and all 25 Query
syntax diagnostics. This does not prove those diagnostics disappear in a run.
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
has independent review. This batch is not accepted yet.

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
The next run will build that repair once and check both original projects.

Separate repair pairs committed fixes for three causes linked to 35 measured
library failures: conditional alias publication, warm union preparation and
property-kind checks. The last group includes one test setup correction.
These are source fixes, not 35 new passing tests. Later assertions still need
execution. These fixes stay outside the immediate project retry.
The separate namespace query selection repair is also committed and reviewed
at `b879db17`. Its first failing operation is shared by 20 measured tests.
Those tests have not run on the repair. It also stays outside this retry.

## Next work

1. Build `069ebad6` once and measure both unchanged projects with that same
   binary. Keep this source fixed. Do not wait for later feature patches or
   unrelated test repairs.
2. Run the repaired core/parser tests in parallel with the project measurement.
   Review the complete alias result and repair its remaining failures.
3. Fix the measured library and class failures in separate worktrees. Combine
   those repairs after the first project measurement.
4. Prioritize the next actual project failure and any shared dependency. Repeat until
   the ordinary project check returns complete diagnostics that match Go.
5. Show the clean result, then add one deliberate type error in a separate copy
   and show the correct diagnostic and location.

Additional committed source changes cover optional merged-interface calls,
readonly array const assertions, typed class-field initializers, nested global
constructor owners, exported overloads and uninitialized locals. Shared
function/arrow statement checking and generic class-method return diagnostics
are also committed and source-reviewed. These later changes
stay outside the first fixed project candidate so they do not delay measurement.

Source workers have separate worktrees and test partners. Shared merge work
has explicit file ownership and one Git coordinator. At most three Cargo
checks run at once. Completed tests, exact diagnostics and whole-project
results measure progress, not worker count.

No configuration weakening, smaller root list, missing dependency, suppressed
diagnostic or replacement `any` counts as progress. A full-project demo and
acceptance of the complete compiler remain separate claims.

The [longer plan and earlier results](typechecker-demo-plan.md) retain the work
history. I do not have evidence for a reliable full-project completion date yet.
