# Assertion signature display

Tested source: `5a58a5dcef37fe35dcf5cf975db2eb65017bb7b1`.
Base: `4327f7f345c90d59d6057a3f53c4d1c0e81eed9c`.
Branch: `agent/wave150-assertion-signature-display`.

The original `assertionWithNoArgument.ts` fixture now matches its complete
pinned diagnostic, type, and symbol artifacts. All 4,423 selected tests pass.
The separate inferred predicate in `isolatedDeclarationsTypePredicate.ts`
still needs a checked source publisher. That fixture is not counted as exact.

## Source map

| Commit | Change |
| --- | --- |
| `96a2ccd945d922ce6874dbb35fbf3eff653ef6ca` | Typed signature display and focused controls |
| `be3546c8b4e83537c3292f1c5b6dcaca24ded054` | Test-only correction for distinct export and local symbol IDs |
| `5a58a5dcef37fe35dcf5cf975db2eb65017bb7b1` | Test-only classification of an unsupported assertion arrow |

Production code is unchanged after `96a2ccd9`. The two later commits change
only `crates/ts_compiler/tests/canonical_assertion_signature_artifacts.rs`.
No broader branch was imported.

## Repair

`ValidatedSingleCallSignatureDisplay` now retains its checked signature ID.
`display_signature_return` reads that signature's existing `TypePredicate`.
It prints the predicate kind, parameter name, and narrowed type instead of
printing the boolean or void call-result type. It does not create predicates
or inspect source text for a replacement string.

`ValidatedSingleCallParameterDisplay` keeps a checked annotation type separate
from the parameter value type. Only location-aware display selects that
annotation for an optional parameter. Context-free display keeps the semantic
value type, including implicit undefined. Written undefined remains present.
Required parameters and parameters initialized before required parameters keep
their previous output.

The source-callable and function-type providers supply annotation identities
only after their existing source checks pass. Contextual, JSDoc, and mapped
callback projections do not invent annotation overrides. Mapped callbacks
retain their actual mapped signature ID.

Source checking, predicate publication, store records, ordinary callable-set
proofs, namespace display, and intersection construction are unchanged. The
existing single-call display path consumes the new fields. Other signature
display paths are not expanded by this change.

## Pinned fixture results

The runner used the clean Go reference checkout at
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. It compared complete reference
artifacts, not selected lines or headers. Both original fixture files and
their reference artifacts remain unchanged.

| Fixture | Final result | Type rows | Symbol rows |
| --- | --- | ---: | ---: |
| `assertionWithNoArgument.ts` | Exact diagnostics, types, and symbols | 7 | 8 |
| `isolatedDeclarationsTypePredicate.ts` | Type mismatch, exact diagnostics and symbols | 12 | 13 |

The assertion key remains `v1:645ee287fcb218f94607a1aa1dbd6af7`, from the
reported run-2 attempt00001 row. Session `91508` reproduced the original
mismatch on the clean base. It printed
`(value?: string | undefined) => void` instead of
`(value?: string) => asserts value`. Session `83737` exited 0 on the final
source. The parameter read type is still `string | undefined`, both calls
still return void, and there are no diagnostics.

The second key is `v1:2544762e8f79db2840eb2a2f41b40cfc`. Session `56558`
exited 1. Its first type difference is still the inferred `isString` signature:
`(value: unknown) => boolean` instead of `(value: unknown) => value is string`.
The complete TS9007 diagnostic, its related TS9031 message, and the symbol
artifact match. No inferred-predicate support is claimed.

Both fixtures were also measured on `96a2ccd9` and `be3546c8`. Their full
variant records, summaries, and semantic-artifact records are deeply equal
across the test-only corrections. Only provenance and invocation paths differ.
No historical corpus result was rewritten or transferred to this source.

## Tests and retained attempts

Session `2829` exited 0. All 22 selected binaries ran with no failed, ignored,
or filtered tests.

| Group | Passed |
| --- | ---: |
| Checker units | 3,940 |
| Compiler units | 258 |
| Fixture units | 164 |
| Public controls | 61 |
| Total | 4,423 |

The qualified binary/test-name comparison retains all 4,415 previous root
tests. It has no missing names. The eight additions are one checker invariant
test, four new public tests, and the three existing optional-method tests
newly included in the selection.

The invariant test rejects five changed predicate records without formatter
writes. The public controls cover eleven supported sources, preserving exact
display, call results, per-location symbols, declarations, and warm replay.
A separate control retains the original unsupported arrow input and verifies
that its typed source error occurs before artifact queries.

Both earlier failed attempts remain in the evidence directory:

- Session `92183`, source `96a2ccd9`, passed 4,419 tests. Three new public
  tests incorrectly required exported declarations and local references to
  share one symbol ID. The correction checks each location's own binding,
  name, and declarations across replay. Production code did not change.
- Session `44165`, source `be3546c8`, passed 4,421 tests. The predicate matrix
  stopped before display on `export const check = (value?: string): asserts
  value => {};`. This base rejects that empty-block arrow with
  `UnsupportedSourceSyntax::Arrow`. Its exact input now has a separate typed
  boundary test. No source support was added or removed.

All prior root test names passed in both attempts. Formatting and
`git diff --check` pass. The final source stayed clean and fixed until every
owned command was collected.

## Execution and evidence

Every Cargo command used the root capped runner, an absolute manifest, locked
offline dependencies, 16 GiB memory, 16 MiB Rust and process stacks, the common
lock, and unchanged `TMPDIR`.

The worktree is
`/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave150/assertion-signature-display`.
Its Cargo target is `target/cargo` below that directory. That target started
empty. No artifacts or fingerprints were copied, reflinked, or hardlinked
from another worktree. Reuse stayed within this physical worktree. No run is
affected by the cross-worktree artifact rule.

Evidence paths below are relative to `target/assertion-display-evidence` in
this worktree:

| File | SHA-256 |
| --- | --- |
| `root-before.json` | `7fa2f9f1260642921430aa360a7d57be933cea369301188cd847afb2dabacb52` |
| `candidate-tests-1.log` | `4f342a3890b6dc8e3ce6630e3ef50b0bb18f644fa1c48a824e281e6180fbffd0` |
| `candidate-tests-2.log` | `e70c35c3b8204ed7ba2d1c8d4007c51e4d18015ed40d28096ac2398cbd3eb0d1` |
| `candidate-tests-3.log` | `5d582752a28cd3a0b728dd2d91a366b3a65db57a5f94dac71d577db97697f097` |
| `assertion-after-3.log` | `6d5d645daedf6005e9a10a0af36d4b4691e5c26dc19cca3607a475fbe828f7a3` |
| `assertion-after-3.json` | `d2c6c720031529031135d4389122378adea96477bfb1f959d642c2ffd48ab122` |
| `isolated-predicate-after-3.log` | `40b6ad20972dfde819bf321a5ca86bfc08e949029910b82e6faabd144c38e4af` |
| `isolated-predicate-after-3.json` | `2cab7184f9f1f08beae20d15fe016eef541659284179640b72115b2b030847ae` |
| `test-retention.json` | `ff734a72a9e41eedb036e2b6c6a943251c233ce8226fdb6ceec6c0c7786b3033` |
| `candidate-after-passed.tsv` | `7a1967752bcf4c5db300159ca483852b0684a22aecaf95c2b8136590549a8f90` |

The fixture input SHA-256 values are
`1f1b0d17245fbc437fc02495574ce10a5f1641e3d6ef2868278617d8a1d08a39`
for `assertionWithNoArgument.ts` and
`6f1fed37286281703244f9061a3649d776c2aba4aa860313e16299ad3fb166dd`
for `isolatedDeclarationsTypePredicate.ts`.

The retained root comparison is
`/home/theo/Code/sandbox/ts-rust/target/wave148-namespace-export-combined-tests.log`,
SHA-256 `4a489e74b8c1b610e2e6573e423bf0983356bcd2bc055b1fd565f59a2d8c1891`.

## Inferred predicate handoff

The canonical `isString` signature has a checked boolean return but no
predicate record. The existing test
`source_type_predicate_returns_publish_boolean_and_preserve_warm_identity`
also verifies that absence. The explicit `isExplicitString` predicate already
has typed metadata and uses the repaired display path.

`source.rs::publish_checked_source_callable_return` checks and widens a return
expression. `source_callable_inferred_return_type` handles async wrapping.
They pass only a return `TypeId` to
`source_callables.rs::publish_inferred_source_callable_return` and
`store.rs::set_source_callable_inferred_return_type`.
`valid_stored_callable_type_predicate` rejects a predicate without a return
annotation. These shared functions were not changed here.

The source owner must publish a checked inferred-predicate record with the
declaration, signature, parameter symbol and index, parameter input type,
condition, and narrowed type. Warm validation must match that record before
accepting a predicate without an annotation. Graph validation must retain the
narrowed type dependency. Raw signature or parameter writes must not forge
that proof by changing caches together.

Pinned `checker.go::getTypePredicateFromBody` and
`checkIfExpressionRefinesAnyParameter` require a normal function with one
return and no implicit return path, a boolean condition, and an unassigned
identifier parameter that is neither boolean nor rest.
`checkIfExpressionRefinesParameter` requires a narrower true-branch type and
a false branch that reduces to never within that type.

Keep the boolean call-result type and inferred return provenance. Do not
synthesize an annotation or suppress TS9007/TS9031. The formatter should read
the checked predicate record, not infer it from a name, body string, or fixture.

No full corpus, semantic smoke, or broader parity run was made here. No
ordinary method-proof hold is cleared by this report. The full port goal
remains active.
