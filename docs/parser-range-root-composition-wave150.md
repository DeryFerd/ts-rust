# Parser range and assertion root composition

Status: combined root checks passed all 4,676 tests and strict parser Clippy.
No primary promotion is claimed.

Root base: `4327f7f345c90d59d6057a3f53c4d1c0e81eed9c`.
Checked parser source: `3bfa6cc60bd0f5a2fbd5514fa82267796ab9764d`.
Range-only source: `1a3a1c7a204f8b272863d3d1c2c8819c3793a5c5`.
Combined source: `2143d0bb604b03f95bc4f1436ceef211e895f413`.
Worktree: `target/agent-worktrees/wave150/parser-range-root-composition`.
Branch: `agent/wave150-parser-range-root-composition`.

## Dependency and equivalence checks

The shared ancestor is `d0339659f3112ff5d6f786942db309dd33097382`.
The root base's parser crate is byte-identical to that ancestor. The parser
source has Git blob `9a7c23308a5f4ff304706435a71878565163bc56` in both trees.
There were no root parser changes to discard during the range import.

`git cherry` found no patch-equivalent commit from the checked parser stack on
this root. The final parser-only delta through `8035fe5b` was imported instead
of merging source-branch parent history. The original and imported deltas have
the same stable patch ID, `d2d564fe24746831f2644670901f2f2f446b256f`.

That delta contains the final source and tests from these checked components:

| Source commit | Required behavior or control |
| --- | --- |
| `abca9c55` | Contextual type-alias names |
| `b1ac6f34` | Export-type dispatch |
| `47b4a178` | Const generic arrows and template-aware lookahead |
| `6ff0fa23` | Generic arrow recovery bodies |
| `5ab88f4e` | Bounded return-type lookahead |
| `1b6ccac6` | Type-parameter declaration names |
| `53c40cbe` | Type grammar await/yield context |
| `91baa6eb` | Original predicate-context probes |
| `7709aa5a` | Value context for predicate names |
| `e8adfa13` | Predicate arrow recovery |
| `79479308` | Parenthesized generic function returns |
| `fb727dc3` | Predicate recovery review controls |
| `d5f06ef6` | Test dispatch compilation repair |
| `881662cb` | Missing angle-token recovery |
| `a37a0c2c` | Missing arrow-node positions |
| `8035fe5b` | Missing return-type ranges and original invariant tests |

The historical intermediate commits were not added as parents. Report-only
history was not imported with this aggregate delta. All existing parser tests
match the final checked files, including the original inputs and assertions.

## Minimal import map

| Source | Composition commit | Imported files |
| --- | --- | --- |
| Parser delta through `8035fe5b` | `ce22c86de373e85368bb866619f9d585f67dfd54` | Parser crate and exact original invariant probe |
| Probe from `57e8fd65` | `4b3c1a94d3c7a02940e9b6dc0bfce8d00a662867` | Only `parser-missing-return-final-review.rs` |
| `3bfa6cc6` | `1a3a1c7a204f8b272863d3d1c2c8819c3793a5c5` | Exact nested-signature correction, test target, and its source report |

All three imports completed without conflicts. Each composition commit has one
parent. The correction retains stable patch ID
`e3c26f48ba3af559b4fec1d80150087ca0a5f57c`.

Before the assertion import, the complete parser crate and both probe files
were byte-identical to `3bfa6cc6`. The probes retain SHA-256
`2153a53cfc6820e1aa2bac5a35233dc61a0052b10d0c0b1fa35dbcf0f15ad9aa`
and `178b1ca57a808cd981020e2ca05b00de6e66ec4300c79424f8dca7f67d42c3a6`.
The range-only parser source has SHA-256
`ea44589e9fcb6404185c6590c27d1d42421a77ddd017401fbd08370b70270a73`.

No checker or compiler source changed. Their executions below use the actual
root code from `4327f7f3`, not the older source branch's consumers.

## Separate parser work

The JSDoc dot-generic leaf is `e421874875600aa2122545b2d5951a899545bf7f`, based
on `1366aa8fb6d449a56b017f5e5166d951ad1a138f`. Its report records 4,009 passing
Rust tests and one unchanged whitespace-probe failure. The heritage composition
owns its combination with the whitespace repair. No part of that leaf or its
parent history was imported here.

The exact parser overlap is:

- The leaf adds `jsdoc_type_context` to `Parser`, initializes it to false, and
  scopes it in a new `parse_jsdoc_type` helper. Retain this composition's
  `arrow_return_type_context` field and initialization alongside it.
- Both dot loops stop before `<` after consuming the dot in JSDoc context.
  In `parse_type_reference`, insert that check before the call to
  `parse_type_reference_name`. Do not restore the leaf's older name parser or
  its token-based start position. Those would discard missing-name range fixes.
- Add the scoped helper without replacing `parse_type` or `parse_type_worker`.
  Their await/yield and predicate context handling belongs to this composition.
- `generic_arrow_lookahead_parser` copies the current parser contexts into a
  bounded probe. The combination must check whether `jsdoc_type_context` also
  needs propagation. No combined-context result is claimed here.
- The leaf adds `parse_jsdoc_type_expression` and changes the checker comment
  parser to call it. This root does not have the leaf's
  `parse_javascript_jsdoc_function_type` or function-overload source data.
  Those source entry points and the typedef/property preflight calls require
  the heritage dependency check before importing their deltas.

A read-only `git apply --check` of the leaf's parser delta fails at its `Parser`
context hunk against this root. No patch was applied. This is a merge dependency,
not a root test failure.

The five range-only checks below do not include assertion precedence. Their
fixed source includes only the prior newline guard in
`parse_postfix_expression_worker`. Root supplied the checked assertion leaves
after those commands were queued. Their separate import is described below.

The exact parser delta is saved in
`target/review/parser-function-deltas.patch`. Any later exchange must use clean,
tested function deltas and preserve these imports. The independent review of
`3bfa6cc6` by `constraint_base_plan` remains separate from this composition.

## Assertion import

Root authorized importing `87627479` and
`ad0c1c0388bcdd1be4093d4dfe7f9a83f8c667be` once all five range-only commands
were collected. Their source report is `1efd53d6`, at
`target/agent-worktrees/wave150/assertion-precedence/docs/reviews/assertion-precedence-wave150.md`.
That report records 249 parser passes, including all 108 bundled libraries,
and strict Clippy. Those are leaf results, not combined results.

A read-only apply check accepted the complete probe commit. The production
delta had one overlapping hunk in `parse_postfix_expression_worker`. The leaf
removed the unguarded `AsKeyword | SatisfiesKeyword` arm. This composition had
the same arm with a preceding-line-break guard. The resolution removed
the complete old arm, including that guard, because the new assertion branch in
`parse_binary_expression` has the same guard. This conflict was reported before
changing source.

The other production changes add assertion handling and operand precedence in
`parse_binary_expression`, add the two relational entries in `binary_precedence`,
and add stopped-assertion comma recovery in `parse_variable_statement_tail`.
The existing contextual binding recovery remains intact. No range helper,
parser name, JSDoc entry point, or checker function needs replacement.

The probe imported cleanly. The repair had exactly the reported conflict. Both
commits use `-x`, and no broad ancestry or source report history was imported.

| Original | Import |
| --- | --- |
| `87627479` | `a9101367958b499413722eab27c248fc9e3a5423` |
| `ad0c1c03` | `2143d0bb604b03f95bc4f1436ceef211e895f413` |

The original and imported probes share stable patch ID
`4615c047edeba046d9b70a5c6e774b4a5d75623c`. The repair also removes the five
lines of the old newline guard, so its raw patch ID is not the leaf's patch ID.
No other conflict resolution was needed.

All assertion tests, both fixtures, and their Git attribute are byte-identical
to `ad0c1c03`. The original fixture retains CRLF bytes and SHA-256
`9a7b99d7a6c42ed91c6eedad965f690c73ba4b4cd54db67f8118deef908b79b6`.
The controls retain SHA-256
`acefde9262b0f14d67ef969f252526c77e93fb42d663f66fc51bd58542588ecb`.
All old parser tests and review probes remain unchanged. The combined parser
source has SHA-256
`3f568e39c51d80ca74b08054aa9656dbb8d9b7ebe7bfd57a1c59f7e0179e0eb6`.

The exact function delta is `target/review/assertion-function-deltas.patch`.
Changed-file rustfmt and `git diff --check` pass. The combined worktree was
clean before its checks started. All 324 old parser controls and the five
assertion tests ran and passed. The pre-run record is
`target/review/combined-sources.sha256`, with 13 source and fixture hashes.

## Range-only root checks

| Check | Session | Result |
| --- | --- | --- |
| Complete root parser suite | `49051` | 324 passed, exit 0 |
| Root checker and compiler unit suites | `66664` | 3,939 and 258 passed, exit 0 |
| Public checker consumers, 13 targets | `84893` | 106 passed, exit 0 |
| Public compiler consumers, nine targets | `98857` | 44 passed, exit 0 |
| Strict all-target parser Clippy | `10874` | No warnings, exit 0 |

All five sessions exited and were collected before assertion integration.
The total is 4,671 passing tests. The 43 result records have no failed, ignored,
measured, or filtered tests. One record is the empty parser doc-test suite.
The parser total is 245 unit tests and 79 integration tests.

The checker units took 45.10 seconds, and the compiler units took 39.42 seconds.
Their build took 1m 01s. The public checker and compiler builds took 40.85 and
56.46 seconds. Parser tests and strict Clippy built in 4.71 and 4.10 seconds.
Public consumer builds reported 18 dead-code warnings in unchanged checker
source. The unit build also reported one unchanged test-only warning for
`allows_string_fallback`.
Strict Clippy here covers only the parser.

The checker public selection covers diagnostic ranges, generic signatures and
calls, generic alias annotations, inferred returns, parameter initializers,
constructor annotations and parameters, exported types, imports, reexports,
JSDoc, and JSX.

The compiler public selection covers generic calls and interface members,
ambient generic and ordinary functions, source imports, arrow expandos,
artifact queries, export-equals artifacts, and JavaScript sources. These include
exact source ranges and cross-file related diagnostics.

The root base's saved namespace/export composition result remains separate. It
reported 4,415 passes and 53 exact semantic-smoke rows. This report does not
reuse that result as proof that the parser composition passes.

## Combined root checks

All commands below used fixed combined source `2143d0bb`, the same selections,
and only this physical worktree's existing target. Rust source and tests stayed
fixed until all five commands were collected.

| Check | Session | Result |
| --- | --- | --- |
| Complete root parser suite | `54769` | 329 passed, exit 0 |
| Root checker and compiler unit suites | `55595` | 3,939 and 258 passed, exit 0 |
| Public checker consumers, 13 targets | `70065` | 106 passed, exit 0 |
| Public compiler consumers, nine targets | `92657` | 44 passed, exit 0 |
| Strict all-target parser Clippy | `44496` | No warnings, exit 0 |

All five sessions exited and were collected. The combined total is 4,676
passing tests. The 44 result records have no failed, ignored, measured, or
filtered tests. One record is the empty parser doc-test suite. The parser
total is 245 unit tests and 84 integration tests.

The complete test-label comparison preserves all 4,671 range-only tests,
including the four expected-panic controls. The only additions are the five
assertion tests. The original fixture tests still check all 48 assertion trees,
parent links, expression ranges, and the eight pinned TS1005 diagnostics.
No existing range control, assertion, or fixture byte was weakened or removed.

The parser build took 6.18 seconds. The checker and compiler unit build took
1m 37s, followed by 44.93 and 39.91 seconds of tests. The public checker and
compiler builds took 36.64 and 6.85 seconds. Strict parser Clippy took 2.82
seconds. Consumer warning messages match the range-only runs. This Clippy
result does not cover the checker or compiler.

The two assertion fixtures were replayed here with the unchanged pinned Go
executable while Rust waited. The original fixture produced exactly eight
TS1005 diagnostics, and the controls produced exactly five. Both commands
exited with expected status 1 and were collected. Their complete logs match
the leaf's saved logs byte for byte.

| Assertion replay file under `target/review` | SHA-256 |
| --- | --- |
| `assertion-go-original.log` | `bdc818dfd1e34bcf49ac978c4be501ebdc6ee477bd9a48b2bc9a7e7645161833` |
| `assertion-go-controls.log` | `9c5af5f534f3869480f4950b7d7644941a8015ae0280b1df596b522319dc7062` |

The executable remains `/home/theo/.local/bin/tsgo-oracle`, with SHA-256
`204f15c767025fc9238b748399be7d1293f6d0f8ea9ddec8eab65995ecf4bb39`.
These two runs did not build or change Go code, fixtures, or old evidence.
Both fixtures ran again after the combined Rust checks. The final logs,
`assertion-go-original-final.log` and `assertion-go-controls-final.log`, have
the same hashes and the same eight and five diagnostics. Both expected exit-1
commands were collected.

## Execution and evidence

This physical worktree started with no Cargo target at
`target/worktrees/wave150-parser-range-root-composition`. No workspace artifact,
fingerprint, reflink, or hardlink was copied from another worktree. All runs use
only this worktree's new target.

Every Cargo command uses the root capped runner, an absolute manifest,
`--locked --offline`, 16 GiB memory, 16 MiB Rust and process stacks, the common
lock, and unchanged TMPDIR. Rust source stayed fixed within each run group.
The range-only pre-run record is `target/review/root-sources.sha256`. No queued
or running command was cancelled for queue wait, and the lock was not bypassed.

All 55 sealed evidence files verified before the root gates. The seal manifest
remains `c7529d4a277f580a9042676817fd4bab2cf1aadd06196f6fd290e228abf986a6`.
After all five range-only gates, all nine source hashes and all 55 sealed files
verified again. At that checkpoint, the complete parser crate and both original
probes were byte-identical to `3bfa6cc6`. The import range passes
`git diff --check`.

All five read-only Go helpers ran again on their original inputs. The 54 output
rows match the pre-run files byte for byte, in groups of 30, 8, 6, 8, and 2.
No old input, output, helper, or executable was regenerated. The pinned checkout
remains clean at `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

The checked summary is `target/review/range-check-summary.json`. The range-only
logs have these SHA-256 values:

| Log under `target/review` | SHA-256 |
| --- | --- |
| `root-parser.log` | `5a6dcb23cb540bba989f5153807df9c37b0a25745e768994b6afa80825a36ef0` |
| `root-consumer-units.log` | `fddbd56fcc64a8d81ec461138020965f219cfd928526d9ad07f18e8d6084c934` |
| `root-checker-public.log` | `0d28bd833104327f8089787a1b71162a89d5633ff611833140e21650832a915d` |
| `root-compiler-public.log` | `98a59935187ef5ce17cdaa60fd96fb85d47c7f2f2127ed097d0e5dff6f9b51aa` |
| `root-parser-clippy.log` | `0b25bc529f0d600f49f088eaa67b185bd6923597a1afe406e80f7d19fd0396f3` |

After all five combined checks, all 13 recorded source and fixture hashes
matched. All 55 sealed files verified again, and the manifest hash stayed
unchanged. Production parser code outside the four assertion functions remains
unchanged from the range-only candidate. The assertion tests and fixtures still
match `ad0c1c03` exactly.
Checker and compiler trees still match root base `4327f7f3`.

All five range replay helpers ran again after the combined checks. Their 54
final rows match both earlier replay sets byte for byte. The output names use
the `-combined-final.jsonl` suffix. The Go checkout remains clean at its pin,
and both Go executable hashes remain unchanged. No previous input or evidence
was rewritten.

The checked final summary is `target/review/combined-check-summary.json`.
It verifies result counts, the complete old test-label inventory, the five
added test labels, unchanged warning messages, all Go outputs, source hashes,
and the 55-file seal. No verification command owned by this composition remains
running or queued.

| Combined log under `target/review` | SHA-256 |
| --- | --- |
| `combined-parser.log` | `bd2b4de22f311656f0ab9e90524fc795079ea4dc13d860dbea2ac42d1d681b1d` |
| `combined-consumer-units.log` | `12a22af7ead8011e3d37e7a6ea681c0a006bcff71ef8eed6b05ea86ebe0183fc` |
| `combined-checker-public.log` | `33c1d568a41afd187bfc9a3f8c85e10dc5a987540070778f8ab88c5648151af5` |
| `combined-compiler-public.log` | `6f8154d70c71dae9098b31befa309d67da425bc8e9b2232ed423a02a6199c808` |
| `combined-parser-clippy.log` | `c1f70f24ce1aa7529fc43ce24afa68f64ace43b33dfcccbe8aceafe79645761f` |

## Limits

No primary promotion, full project parity, performance result, or upstream
roll-forward is claimed. The combined result does not include the heritage or
JSDoc composition and does not replace the separate parser reviews. The 54 Go
range replays compare fresh Go results with saved Go results. They do not claim
complete Rust/Go AST or malformed-input diagnostic parity.
