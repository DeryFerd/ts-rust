# JavaScript conditional array

Base: `8142bff97efccf69bb83c4b51ffe4d3ba515fb77`.
Conditional-array change: `aeb10041993828e1f47a37c258616e1836483c6b`.
Constructed-interface method routing:
`6df78b16bb8cac4c489eafba1580c732d783429f`.
Read-only conditional literal query and tested HEAD:
`661483175b9f19ec1c0c1e6df4de942dd9fcd16d`.
Worktree: `target/agent-worktrees/wave189/js-conditional-array`.
Branch: `agent/wave189-js-conditional-array`.

The complete unchanged `jsSpeculativeParsingError.ts` now matches both its
full diagnostic artifact and its entire pinned `.types` baseline. All nine
original focused tests and three new read-only query tests pass. The original
diagnostic rerun used the required 8 MiB main stack and 300s timeout.

## Complete original

Case: `testdata/tests/cases/compiler/jsSpeculativeParsingError.ts`.
Variant: `v1:d389f9a26c155656b4637e5731afb1cd`.
Options: strict=true, allowJs=true, checkJs=true, noEmit=true.
The virtual file remains t.js. The full source retains the real
`new Date().getHours() < 12`, both original string branches, the parentheses,
array, and comment. No replacement declarations or library omissions were used.

Session `91556` completed with exit zero. The scorecard records one selected
case and one executed variant, `checkerMode=canonical`,
`comparisonScope=full_artifact`, and `fullArtifactComparison=true`.
Its status is `exact_match`, with zero diagnostics, skipped selected variants,
unsupported details, or fatal invariants. The expected errors baseline is
absent, and the complete actual diagnostic artifact is empty.

The runner records `main_stack_kib=8192`. It owns the diagnostics lock and
places timeout 300s after lock acquisition. No outer lock was added. Source,
binary, and the clean pinned Go checkout were checked before and after.

Scorecard:
`/tmp/ts-rust-wave189-js-conditional-array-original-2/original.json`.
SHA-256: `73ccfe482f603e829298f36593ff5018d3fdb580ac49df442b3aaca45c7f5d29`.
Runner receipt: `/tmp/ts-rust-wave189-js-conditional-array-original-2.log`.
SHA-256: `20cdd09ae518d834562b6147f42378dcea3441b18ec98363f01924fae7ec3a42`.

The earlier original run at `6df78b16` also passed. Its scorecard remains in
`original-1/original.json` with SHA-256
`06f831eec13fcbd9920ae9f8e3d25e270cf2afca076a783435c1de07cda1d9c5`.

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

The separate artifact follow-up adds
`checked_conditional_literal_artifact_type(&self, ...)`. It accepts only
direct literal children of a validated conditional, after source checking
and with an existing parent result. It reads the existing literal cache and
uses the read-only `fresh_type_of_literal_type` pair validator. Null uses the
existing intrinsic identity. Missing parent results and conflicting child
cache data return typed errors. The helper does not allocate checker types,
check source, publish child links, or reconstruct other expressions.

## Focused results

| Run | Session | Result |
| --- | --- | --- |
| Gate 1 at `aeb10041` | `89637` | Seven existing controls passed. Both full-Date fixtures stopped at cold Date type 86. |
| Diagnostic-only trace | `35741` | Confirmed the actual cold Date record. The original input was unchanged. |
| Gate 2 at `6df78b16` | `95223` | Eight of nine passed. Full source checking completed with empty errors. The additional types observation stopped at an artifact-query boundary. |
| Private binary build 1 | `85927` | Exit zero, 3.04s. |
| Complete original 1 | `51379` | Exit zero and exact whole diagnostic artifact match at 8 MiB. |
| Gate 3 at `66148317` | `97911` | All original nine tests and three new query tests passed. The entire `.types` file matches pinned Go byte for byte. |
| Private binary build 2 | `66377` | Exit zero, 2.84s. |
| Complete original 2 | `91556` | Exit zero and exact whole diagnostic artifact match at 8 MiB. |

Gate 2 compiled in 1m45s. All seven existing controls passed in 0.03s, with
zero ignored and 4,130 filtered tests. The full-Date control for missing names
reported TS2304 from both conditional branches. The original retained all
its input and options. No existing test body or expectation was changed.

Gate 3 compiled in 1m50s. Its ten checker tests passed in 0.04s and its two
fixture tests passed in 2.74s, with zero ignored tests. `source.rs`,
`contextual.rs`, and both original fixture tests remain unchanged from gate 2.

## Read-only literal queries

At `6df78b16`, the types observation stopped at `ARTIFACT.MISSING_TYPE` for
StringLiteral node 15. Scalar conditional checking creates literal types
but leaves scalar child type-node links absent. The existing conditional
replay control requires that contract. The parent approved a separate
read-only artifact query fix. Its helper ownership was recorded before edits.

The new tests cover repeated reads of checked string, template, number,
bigint, boolean, and null literals. They run with strict null checks both
on and off and require absent child links. They also reject an unchecked
owner even when the literal pair already exists. Repeated failures retain
state when the parent result is missing or the child type, outer type
parameters, or symbol cache conflicts. Type, symbol, signature, mapper,
link, and diagnostic counts remain unchanged during checked reads.

The complete actual `.types` file is in
`/tmp/ts-rust-wave189-js-conditional-array-artifacts-3/original.types`.
`cmp` against the pinned Go baseline exited zero. Both files are 762 bytes
with SHA-256
`8e2a58fe6a70db75219ad59c21811aa0477ef53c99edf00a9aca3cd6b1761df0`.
No original assertion was changed or removed.

## Preserved evidence

Go pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
Original source SHA-256:
`a8a91aaa7679836beb58adde59287b27a920f3ae907c87aecf0de2d6e952d6ff`.
The captured full input is in
`/tmp/ts-rust-wave189-js-conditional-array-artifacts-3/original.ts`.
It is byte-identical to the pinned original. Its `original.errors.txt` is
empty. The earlier failed artifact and its error remain in `artifacts-2`.

Private binary:
`target/agent-builds/wave189-js-conditional-array/debug/ts_fixture_baseline`.
SHA-256 before and after the new original run:
`3a34b9420ce310d17b03d06dae307365aee0a69d0915ca06847c0f6c1208d197`.

Preserved logs share `/tmp/ts-rust-wave189-js-conditional-array-`:

| Log | SHA-256 |
| --- | --- |
| `gate-1.log` | `4bbc6ec21239882caf0d99e8b92794862c7ed1fc06da58209d3082805eab0d22` |
| `trace-1.log` | `96bb9085d81dd5186a070913028acdba046a87750a1e0eaf413e0341daece4ab` |
| `gate-2.log` | `5d665b43b0f7ed1c4dc92be9b73453765b3c9f62d2ba0df8f2fdb923d3794811` |
| `build-1.log` | `c8a5cfd914f908abf19fc767cf7c43db1a5b396690b6c0f4a3e49c904a608c9b` |
| `gate-3.log` | `89953ea6e8131399fe95462ceddd01f130e68ebcfbb9ca49813d8500034f2c15` |
| `build-2.log` | `f171feaf851659a2c93fd99cc3f06dce7d5e31daa1a203a8225cd3d5a6abbdfa` |

Every Cargo run used the root absolute capped runner, absolute manifest,
locked/offline mode, 16 GiB memory, the shared build lock, and the new physical
target. No artifacts were copied and TMPDIR was unchanged. The original run
used a 16 GiB scope with the prescribed 8 MiB main stack. Every session is
collected. Earlier worktrees and evidence are unchanged. No full workspace
suite or artifact audit was run.
