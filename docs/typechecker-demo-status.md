# Typechecker demo status

Updated 2026-08-31. No complete real-world project has passed in Rust yet.

## Targets

Use Hono and TanStack Query core as the two main project targets. Both have
prepared dependencies, fixed original configurations and complete first-failure
measurements. Neither is proved close to a full pass. Hono stays the first
integration target. Query tests whether the same fixes work in another codebase.

| Project | Original source roots | Completed source checks | Unsupported | Other results | Load syntax diagnostics |
| --- | ---: | ---: | ---: | --- | ---: |
| Hono | 188 | 27 | 155 | 5 internal errors, 1 original-policy declaration skip | 0 |
| TanStack Query core | 23 | 1 | 22 | None | 0 |

These are complete first-failure measurements on `035a0751`, not pass rates. A completed
source check does not include a complete diagnostic comparison. Both ordinary
project controls failed. Every original source root has an outcome. One binary
checked both projects. Both commands and separate cleanup are closed. The raw
streams, counts, final reports and all 58 saved output hashes are verified.

The full loaded graphs and root lists are unchanged from the earlier run.
Hono's 55 syntax diagnostics and Query's 25 syntax diagnostics are now gone.
Hono's HTTP status source completes again. This repairs the one-file regression
in the previous measurement. It does not improve on that file's older result.
All other Hono source outcomes are unchanged apart from one printed internal
symbol number. Every Query outcome is unchanged.

The saved [Hono stream](../target/wave202-demo-shared-project-census-5-hono.jsonl)
and [Query stream](../target/wave202-demo-shared-project-census-5-query.jsonl)
retain every outcome, complete typed error and loaded diagnostic. The
[complete report](../target/wave202-demo-shared-project-census-5-result.md)
and [independent review](../target/wave202-demo-shared-project-census-5-result-review.md)
record the source, build, unchanged inputs and closed cleanup.

The [Hono result](../target/wave202-demo-hono-first-failure-census-1-result.md)
and [Query result](../target/wave202-demo-query-first-failure-census-1-result.md)
are the older baseline, with independent reviews and closed cleanup. Their
original inputs stay fixed.
Query means its production core package, not React Query or the whole monorepo.

## What works and what is not verified

An earlier core check passed 6,422 Rust tests on `57e743da`.
The selected original corpus has 423 exact diagnostic results in 511 executions
and 62 exact semantic results in 95 executions. These are limited test sets,
not complete TypeScript compatibility. The latest core/parser check on
`4a09da42` completed all 6,550 tests in 162 harnesses. It passed 6,531 and failed
19. Formatting and Clippy passed. All 363 parser tests passed. The failures
include 15 previously passing tests and four new controls. The
[complete core/parser result](../target/wave202-core-parser-combined-full-3-quality-report.md)
and [independent review](../target/wave202-core-parser-combined-full-3-quality-runtime-review.md)
retain every failure. Both runtime and separate cleanup are closed.

Eighteen failures share a namespace export-owner check. The repair is committed
and reviewed at `99597a7b`. The remaining failure needs scalar method-value
lookup through the existing wrapper-type provider. Its source and tests have
paired approval, including a correction for caller-limit cache recovery.
Neither repair has a runtime result yet. The primary branch still uses the
previously accepted compiler source. No core candidate is accepted from this
failed check.

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
at `d5f0d448`. A fresh 5,105-test diagnostic check is being prepared. Two other
pairs are fixing written conditional-argument proof and unique-symbol property
publication. Those source changes have not run.

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
The latest project measurement in the table used that source. Its build took
74 seconds, Hono took 335 seconds and Query took 40 seconds. That measurement
did not run the unit tests.

Separate import fixes are committed at `0a6254d8` and `7074c8c3`. The exact
source-file setup correction for 14 tests is committed at `3356aa21`.
All three have independent source review. Their source integration is committed
and reviewed at `60ab0675`. It contains 7,300 test names. A diagnostic check of
all 5,368 checker-library tests is being prepared. Its selection includes 356
required controls. The other 1,932 tests and 230 required controls are outside
that focused check. These source counts are not passing-test results.

## Next work

1. Run the shared checker-library and alias diagnostic checks on their fixed
   source batches. Keep every old result in the comparison.
2. Combine the reviewed project repairs for constructor owners, merged
   interface calls, readonly arrays and exported overloads. Add the typed-field
   and shared function/arrow local-variable work after their source reviews.
3. Repeat both unchanged project checks with one fixed binary. Use the next
   actual failure in each source file to choose the following repairs.
4. Complete the eight project repair pairs below and the two core repairs.
   Require tests before accepting their source.
5. Compare complete project diagnostics with TypeScript-Go. Then show one
   deliberate type error in a separate copy with its correct location.

The diagnosis coordinator read all 16 project reports. Of 181 assigned failure
rows, 160 have a located source cause, 18 remain unresolved and three overlap
work that is on hold. Eight implementation pairs now have separate worktrees.
They target 34 distinct first failures. That is not a forecast of 34 completed
files, because later failures can appear after each repair.

| Repair pair | Immediate work |
| --- | --- |
| Import annotations | Preserve real imported type owners and annotation children. |
| Generic class fields | Check `new Set<TListener>()` through real declared generic constructor signatures. |
| Constructor annotations | Publish single-constructor parameter types through the existing query path. |
| Local class exports | Follow the original class and named export owners. |
| Type reexports | Follow the full named and star reexport chain. |
| Arrow context | Use real imported function-type aliases for parameter context. |
| Typed async arrows | Check written parameter and `Promise<T>` return types. |
| Equality conditions | Check both operands through the shared statement engine. |

The generic-constructor work has a second source/test pair with separate file
ownership. The imported-arrow work also depends on the import and reexport
repairs. These dependencies remain explicit. The
[ownership and priority report](../target/wave202-census-4-failure-priorities.md)
records the measured failures, separate later limits and original assignment.

Small libraries remain possible earlier demo targets, but none is proved
close to a full check. The cached tiny-invariant, Mitt, UFO, Pathe and
sourcemap-codec inputs lack dependencies. Current-source audits also retain
known compiler limits. Mitt additionally needs its original generated package
declarations. A valid measurement must prepare those inputs first and keep
the full original configuration, including any tests and ambient types.

Source workers have separate worktrees and test partners. Shared merge work
has explicit file ownership and one Git coordinator. At most three Cargo
checks run at once. Completed tests, exact diagnostics and whole-project
results measure progress, not worker count.

No configuration weakening, smaller root list, missing dependency, suppressed
diagnostic or replacement `any` counts as progress. A full-project demo and
acceptance of the complete compiler remain separate claims.

The [longer plan and earlier results](typechecker-demo-plan.md) retain the work
history. I do not have evidence for a reliable full-project completion date yet.
