# Typechecker demo status

Updated 2026-09-01. No complete real-world project has passed in Rust yet.

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
Pathe is not one fix away from a demonstrated pass. Its original build and
project-pinned compiler check also remain separate requirements.

The Pathe fixes now have committed source and independent review. They cover
keyword tuple labels, string-default parameter inference, ordinary property
operands, shared throw statements, function-expression bodies and destructuring
loops. The typed callable-error location mapping is also committed. Integration
is in progress. The computed-key donor still needs a complete source review.
None of these changes has a new Pathe project result yet.

The corrected six-feature compiler at `a89c891b` builds successfully. The build
took 77.385 seconds, with no Rust errors. Separate cleanup and independent review
are complete. The ordinary project-checking executable is available. Its
[build result](../target/wave202-demo-next-source-bin-2-result.md) and
[review](../target/wave202-demo-next-source-bin-2-result-review.md)
do not claim a passing TypeScript project.

Its focused check compiled and ran all 79 selected tests: 52 passed and 27 failed.
All seven Boolean-negation tests passed. The failures include generic interface
calls, nullish assignment flow, interface heritage, wrapper types and diagnostic
details. Seven separate investigations are tracing these failures. The
[complete test log](../target/wave202-demo-next-source-focused-2.cargo.log)
retains every result. Separate cleanup and final result review are pending.

The first build failed on two Rust E0308 errors because two calls omitted `Some`
around an optional session. That failed attempt and its cleanup remain in the
[build result](../target/wave202-demo-next-source-bin-1-result.md) and
[review](../target/wave202-demo-next-source-bin-1-result-review.md).
The first 248-test parser command also stopped before compilation because
`cargo test` rejects `--keep-going`. The corrected command passed all 248 tests,
including the three new keyword-tuple-label tests. No test was ignored or filtered.
That parser run still needs separate cleanup and final result review. A passing
parser test does not prove that Pathe's 35 loaded-file diagnostics are gone.

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

1. Combine and test the committed Pathe fixes. Trace the 27 focused failures in
   parallel, with one owner per cause. Complete the computed-key source review.
   Repeat all nine Pathe roots with the original config and dependencies. Use
   the typed reporter mapping to locate the remaining internal error. Fix the
   newly measured stops before adding unrelated language features.
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

The current Pathe first stops are:

| Original files | First stop | Next action |
| --- | --- | --- |
| `src/_glob.ts`, `test/glob.spec.ts` | Arrow bodies containing `throw` | Shared throw integration and project-shaped tests committed. Run them. |
| `src/_internal.ts`, `src/utils.ts` | Untyped parameters with string defaults | Inference repair committed. Run its five new controls. |
| `src/_path.ts` | Function-expression body with a parameter | Shared-body repair and eight new tests committed. Integrate and run them. |
| `src/index.ts` | Ordinary property used in a binary expression | Operand repair and three public tests committed. Run them. |
| `test/index.spec.ts` | Computed object key containing a call | Verify the existing computed-key donor, then integrate it. |
| `test/node-glob.spec.ts` | Source-file destructuring `for...of` | Source-file and callable-loop repairs committed with eight new tests. Integrate and run them. |
| `test/utils.spec.ts` | Internal callable error, location unavailable | Typed location mapping committed. Measure the actual error next. |
| Installed Node `http2.d.ts` | Parser rejects keyword tuple labels | All 248 selected parser tests passed. Recheck the original loaded file. |

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
