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
The focused parser check passed all 363 tests across 27 harnesses. All 335 old
tests and all 28 new controls passed. Independent review and cleanup are closed.
The [parser result](../target/wave202-hono-parser-syntax-focused-1-runtime.md)
records the complete selection.

The library batch at `0508192a` adds 94 tests. Its first check stopped on 38
Rust compile errors across 11 files. No tests ran. The repairs are committed
and combined with the exported interface-method owner fix at `555cac5e`.
Its next check selects 6,506 tests. That repaired source has not run yet.

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
retains every failure. This batch is not accepted yet.

The shared feature merge is committed at `f2e9d14d`. It adds conditional
expression operands, annotated local callbacks, object-method captured writes
and imported interface heritage to the repaired library. Its source inventory
retains all 6,506 old tests and adds 16 controls. These tests have not run on
that combined source. Class, core/parser and reporter integration remain.

## Next work

1. Finish the fixed shared source integration. Four file groups and their
   reviewers now resolve the class/library join in parallel.
2. Run the repaired library and core/parser checks. Diagnose the completed
   class and alias failures in parallel. Keep every test and report all failures.
3. Build the combined compiler once and measure both unchanged projects with
   that same binary. Prepare the project checks while source integration runs.
   Do not wait for every later feature patch or unrelated test repair.
4. Prioritize the next actual failure and any shared dependency. Repeat until
   the ordinary project check returns complete diagnostics that match Go.
5. Show the clean result, then add one deliberate type error in a separate copy
   and show the correct diagnostic and location.

The next feature batch covers optional merged-interface calls, readonly array
const assertions, typed class-field initializers, nested global constructor
owners and shared function/arrow statement checking. Exported overloads and
uninitialized locals also have committed source changes. These later changes
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
