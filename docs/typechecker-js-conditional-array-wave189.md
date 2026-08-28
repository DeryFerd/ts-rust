# JavaScript conditional array

Base: `8142bff97efccf69bb83c4b51ffe4d3ba515fb77`.
Conditional-array change: `aeb10041993828e1f47a37c258616e1836483c6b`.
Constructed-interface method routing and tested HEAD:
`6df78b16bb8cac4c489eafba1580c732d783429f`.
Worktree: `target/agent-worktrees/wave189/js-conditional-array`.
Branch: `agent/wave189-js-conditional-array`.

The complete unchanged `jsSpeculativeParsingError.ts` now has an exact
diagnostic artifact match under the required 8 MiB main stack and 300s
timeout. The extra `.types` observation test remains blocked by an existing
artifact-query boundary. This report does not claim that all nine tests pass.

## Complete original

Case: `testdata/tests/cases/compiler/jsSpeculativeParsingError.ts`.
Variant: `v1:d389f9a26c155656b4637e5731afb1cd`.
Options: strict=true, allowJs=true, checkJs=true, noEmit=true.
The virtual file remains t.js. The full source retains the real
`new Date().getHours() < 12`, both original string branches, the parentheses,
array, and comment. No replacement declarations or library omissions were used.

Session `51379` completed with exit zero. The scorecard records one selected
case and one executed variant, `checkerMode=canonical`,
`comparisonScope=full_artifact`, and `fullArtifactComparison=true`.
Its status is `exact_match`, with zero diagnostics, skipped selected variants,
unsupported details, or fatal invariants. The expected errors baseline is
absent, and the complete actual diagnostic artifact is empty.

The runner records `main_stack_kib=8192`. It owns the diagnostics lock and
places timeout 300s after lock acquisition. No outer lock was added. Source,
binary, and the clean pinned Go checkout were checked before and after.

Scorecard:
`/tmp/ts-rust-wave189-js-conditional-array-original-1/original.json`.
SHA-256: `06f831eec13fcbd9920ae9f8e3d25e270cf2afca076a783435c1de07cda1d9c5`.
Runner receipt: `/tmp/ts-rust-wave189-js-conditional-array-original-1.log`.
SHA-256: `73b7ea7b8b58b9c67d6dd7c3afc0c548f9b53cb0ffd95e9e8c811a331d77ec58`.

## Production scope

`SourcePlanner::plan_conditional` now accepts an unasserted array-element
owner. Contextual preparation retains the conditional for the existing
nested-expression checker. Execution checks the actual condition and both
branches, preserves their raw literal union, and widens only the mutable
array-element result. No alternate branch checker or any fallback was added.

The first full-source run then exposed a cold real Date receiver. A temporary
trace identified local type 86 as Date, with no resolved members. The Date
constructor had succeeded. The selected-method gate admitted only scalar
and array receivers, so the Date method fell through to a read-only path.

The seven-line follow-up admits a nongeneric interface returned by an actual
`new` expression to `check_source_selected_method_property`. Its existing
`SourceIterationProperties::property` provider resolves the selected method
from source and resolves its real return annotation. There is no Date or
getHours name exception. Constructor, global, library, and provider code is
unchanged. The dependency was recorded before expansion. All tracing was
removed from the candidate.

## Focused results

| Run | Session | Result |
| --- | --- | --- |
| Gate 1 at `aeb10041` | `89637` | Seven existing controls passed. Both full-Date fixtures stopped at cold Date type 86. |
| Diagnostic-only trace | `35741` | Confirmed the actual cold Date record. The original input was unchanged. |
| Gate 2 at `6df78b16` | `95223` | Eight of nine passed. Full source checking completed with empty errors. The additional types observation stopped at an artifact-query boundary. |
| Private binary build | `85927` | Exit zero, 3.04s. |
| Complete original | `51379` | Exit zero and exact whole diagnostic artifact match at 8 MiB. |

Gate 2 compiled in 1m45s. All seven existing controls passed in 0.03s, with
zero ignored and 4,130 filtered tests. The full-Date control for missing names
reported TS2304 from both conditional branches. The original retained all
its input and options. No existing test body or expectation was changed.

## Artifact boundary

The added types observation requests every type in the original's artifact
walk. It fails with `ARTIFACT.MISSING_TYPE` for StringLiteral node 15.
This is not a source-checking failure or a failure of the original errors
artifact. The scalar conditional checker creates the literal types but
deliberately leaves scalar child type-node links absent. The existing
conditional replay control explicitly requires that contract.

No child links were forced into the source checker, no artifact query was
changed, and no assertion was weakened to hide this boundary. Reading those
checked literals through artifact_queries.rs would be a separate readback
change outside the assigned checker scope. The parent scope question is in
`/tmp/ts-rust-wave189-js-conditional-array-artifact-boundary.md`.
Do not describe the extra types test or the full nine-test gate as passing.

## Preserved evidence

Go pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
Original source SHA-256:
`a8a91aaa7679836beb58adde59287b27a920f3ae907c87aecf0de2d6e952d6ff`.
The captured full input is in
`/tmp/ts-rust-wave189-js-conditional-array-artifacts-2/original.ts`.
Its `original.errors.txt` is empty. The artifact error remains in
`types-error.txt` in the same directory.

Private binary:
`target/agent-builds/wave189-js-conditional-array/debug/ts_fixture_baseline`.
SHA-256 before and after the original run:
`f82b44c7f15be7ef37f9123aa9a371a9d830dcf387921dff8f044891aa9d7989`.

Preserved logs share `/tmp/ts-rust-wave189-js-conditional-array-`:

| Log | SHA-256 |
| --- | --- |
| `gate-1.log` | `4bbc6ec21239882caf0d99e8b92794862c7ed1fc06da58209d3082805eab0d22` |
| `trace-1.log` | `96bb9085d81dd5186a070913028acdba046a87750a1e0eaf413e0341daece4ab` |
| `gate-2.log` | `5d665b43b0f7ed1c4dc92be9b73453765b3c9f62d2ba0df8f2fdb923d3794811` |
| `build-1.log` | `c8a5cfd914f908abf19fc767cf7c43db1a5b396690b6c0f4a3e49c904a608c9b` |

Every Cargo run used the root absolute capped runner, absolute manifest,
locked/offline mode, 16 GiB memory, the shared build lock, and the new physical
target. No artifacts were copied and TMPDIR was unchanged. The original run
used a 16 GiB scope with the prescribed 8 MiB main stack. Earlier worktrees
and evidence are unchanged. No full workspace suite was run.
