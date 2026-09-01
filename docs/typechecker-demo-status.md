# Typechecker demo status

Updated 2026-08-31. No complete real-world project has passed in Rust yet.

## Targets

Use Pathe for the first small complete demo and Hono for the main integration
target. Pathe's original typecheck includes nine roots, with all four test files.
It already uses TypeScript-Go and has a supported modern module configuration.
Its tools and locked dependencies are being prepared. It has no Rust result yet.

Keep TanStack Query core as a cross-project check. Hono and Query have prepared
dependencies, fixed original configurations and complete first-failure records.
Neither is proved close to a full pass. UFO is the second small candidate, but
its separate type-test contract must also run before a complete demo claim.

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
paired approval and are committed at `4192503d`, including a correction for
caller-limit cache recovery.
Both are now combined and source-reviewed at `267cfa91`. Its next check passed
formatting, then Clippy stopped on Rust error E0609 in a new scalar-method test.
The helper uses `question_token`, but the AST field is `postfix_token`.
All 6,559 selected tests remain unrun. Separate cleanup and independent review
are closed. The [failed check](../target/wave202-core-parser-combined-full-4-quality-report.md)
retains the complete error. The exact field-name correction is committed and
independently verified at `c70de1f9`. The next check's preparation is reviewed.
New active copies are being prepared for the same 6,559-test selection.
The primary branch still uses the previously accepted compiler source.

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
committed and independently reviewed at `979dfe7b`. A fresh check is in preparation.
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
not run. A finite Rust compile request is prepared for that source.

## Next work

1. Prepare and measure all nine Pathe roots with the original config, dependencies
   and generated declarations. Record both its pinned reference and the port's
   pinned Go reference. Do not call it close before measuring its failures.
2. Apply the shared Rust test API correction, then compile and test the project
   repairs before combining them. Keep all original tests and failures.
3. Finish the measured Hono repairs and combine the shared statement work.
   Rerun Hono and Query with their complete unchanged graphs.
4. Run the repaired core and alias checks. Preserve every old result in the
   comparison and finish the remaining failures before accepting those batches.
5. Retain complete ordinary project diagnostics in the census reporter. Compare
   the full project result with the reference, then show a deliberate type error
   in a separate copy with its correct code, message and location.

The next demo must show a complete ordinary project check, not just cold-root
coverage. Missing diagnostics, unchecked declarations and unsupported operations
must remain visible. The source-only repair count is not the demo's pass count.

The diagnosis coordinator read all 16 project reports. Of 181 assigned failure
rows, 160 have a located source cause, 18 remain unresolved and three overlap
work that is on hold. Eight implementation pairs now have separate worktrees.
They target 34 distinct first failures. That is not a forecast of 34 completed
files, because later failures can appear after each repair.

All eight feature commits now have independent source review and verified
commit contents. They add 55 controls. None has a runtime result. The generic
constructor batch's separate Rust error, a question mark applied to a bool,
is corrected and independently verified at `fcaf8610`. Rust compile checks for
all eight batches are prepared or in final preparation review. The first actual
generic-class check stopped on four Rust API errors in an inherited public test
file. Its normal library compiled, but its required test targets were not reached.
No TypeScript test ran. The same failing test file exists in all eight batches
and the statement/field integration. The shared test-only correction is committed
and independently reviewed at `36a3e127`. The same exact one-file patch is being
applied to all nine isolated bases. It changes no TS input or assertion.
The import-annotation request timed out before execution. The constructor-annotation
request was not submitted. Both are on hold until the shared correction is ready.
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

Three further Hono repairs have complete source review and signed commits:
empty derived classes at `a2f0ea80`, optional named method parameters at
`c3444fc0`, and typed arrow object parameters at `7aad3ef5`. They have no runtime
result yet. Predicate arrows, contextual overloads, contextual arrow bodies and
shared `for...of` statements have separate implementation and test owners.

The shared try/catch/throw implementation is committed and independently closed
at `0ddc0f07`. Typed synchronous returned arrows are committed at `381a3191`
after source/test review. Neither has run. Callable alias heritage remains under
review. Duplicate script-global recovery is independently closed at `907b67dc`,
also without a runtime result. These source changes must not increase the
measured project counts until the combined project check executes.

The diagnostic-payload implementation has a source/test pair. It will preserve
complete ordinary diagnostics and mark cold or failed snapshots as partial.
It must keep the first checker failure and must not run extra type queries just
to fill the report. Its failed post-source collector limit remains explicit.

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

Source workers have separate worktrees and test partners. Shared merge work
has explicit file ownership and one Git coordinator. At most three Cargo
checks run at once. Completed tests, exact diagnostics and whole-project
results measure progress, not worker count.

No configuration weakening, smaller root list, missing dependency, suppressed
diagnostic or replacement `any` counts as progress. A full-project demo and
acceptance of the complete compiler remain separate claims.

The [longer plan and earlier results](typechecker-demo-plan.md) retain the work
history. I do not have evidence for a reliable full-project completion date yet.
