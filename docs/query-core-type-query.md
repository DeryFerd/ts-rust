# Query core type-query work

Updated 2026-09-04. Implementation has started. The operation is not complete.
Use query-core-integration. Root owns production code, tests and the index.
One reviewer checks the complete change. Other workers investigate bounded
questions and write separate reports. Do not start another feature branch.

## Measured failure

The latest unchanged Query run reports GenericAliasConstraintUnsupported for
ReturnType's formal in lib.es5.d.ts, bytes 75173..75204. The old blanket
FunctionType syntax rejection is gone. Plain required/scalar ReturnType and
pending global overload inference now pass separate controls. The outer Query
error does not expose its exact inner relation or formatting failure.
The run still has 244 records and 24 attempts. Only the ordinary attempt and
isolated root 20 change their stopping point. Two of 23 isolated roots complete.
Ordinary checking remains incomplete. No diagnostic changes.
See the [exact comparison](../target/query-core-return-type-query-2-comparison.json)
and [result](../target/query-core-return-type-query-2-result.md).
The focused checks, Query run, accepted regression selection, and pinned Go
controls are closed. Their complete source fingerprint is
5cb542a9343878233682e102a12bee84d12c867afa9135f5b8bfc225554a89a9.

The prior ordinary Query stop was TypeQuery, file 20, node 82, bytes 1196..1213.
The bounded observation found an Identifier query with no type arguments.
Its resolved symbol has four declarations, no parent, no export-symbol link
and no cached value type. Its flags are TRANSIENT | FUNCTION | VALUE_MODULE.
plan_value_type_query rejects the declaration list because it requires exactly
one declaration. It never asks for the value type.

The held operand name and declaration bodies remain unread. Four declarations
do not prove four signatures. The new type query reaches the authenticated
global owner path. Its later constraint failure does not prove that signature
demand is complete. See the [prior observation](../target/query-core-type-query-observation-1-result.md).

All temporary traces from that observation were removed before implementation.

## Implemented checkpoint

These commits are on the existing query-core-integration branch:

- 567e3a460 retains an authenticated Pending merged callable identity. Plain
  typeof does not query annotations. Later overload publication reuses its TypeId.
- 90efbaf82 shares overload annotation and publication work. Full-source checking
  keeps its old resets and implementation diagnostics. The live adapter borrows
  the actual query and session. Optional unions retain that session.
- df6b23c93 adds a qualified return-query reproducer. It is still failing.
- 78655c224 checks ordinary function-valued alias constraints, including captured
  formals. It accepts declared scalar-any rest types and keeps source errors
  through the shared overload worker. It also adds live conditional demand.
- 91b954d1e adds public constraint and ReturnType controls without changing old
  expectations.
- 2ef992da1 keeps valid function headers lazy and resolves selected returns
  through the existing source proof. It fixes plain ReturnType and pending
  global overload inference, including cold/warm identity and replay.

The [latest focused run](../target/query-core-return-type-constraints-4-result.md)
has 28 tests, 23 passes and five failures. It recovers two cases and retains
all 21 prior passes. The earlier publication assertion panic is
fixed with the common rest-parameter predicate, with assertions still enabled.
The [85-case regression selection](../target/query-core-return-type-regression-2-comparison.json)
retains all 83 Full3 passes and the same two accepted-baseline failures. No names
are missing. This selection does not replace the full accepted regression gate.
The checker unit tests and 13 selected public harnesses also
[compile successfully](../target/query-core-return-type-test-build-1-result.md).
This compilation did not execute the private unit tests.

[Pinned Go controls](../target/query-core-return-type-go-controls-1/result.md)
confirm the new TS2344 text and position. Separate assignment witnesses confirm
the string and number ReturnType results, last-overload selection, and exclusion
of the implementation signature. They reject an any fallback. Rust's plain
FunctionType ReturnType control now passes. Both exported-overload controls
still fail before full checking. Go CLI diagnostics do not measure internal
cache identity or warm replay.

The paragraphs below record the earlier overload checkpoint and its baseline.

Source review passed for both production changes and the new test. The focused
identity and worker selections retained all ten baseline passes and added two
passing typeof controls. Their one earlier failure remains. The qualified-query
selection has 12 passes and two failures. It retains every earlier pass. Its
new failure is UnsupportedSyntax on the inner qualified TypeQuery. The test
keeps that annotation uncached before source demand. No old expectation changed.
See the [worker comparison](../target/query-core-pending-overload-worker-1-comparison.json)
and [qualified-query comparison](../target/query-core-pending-overload-recursion-2-comparison.json).

The six-file reference-flow draft remains separate and unstaged. Unrelated
formatter changes were removed. The committed checkpoint with that preserved
draft has fingerprint
d5bd6dfdcd647f1384792a7db5da79eaab06148c07856f5d480098952ffec5ce.
The [final focused check](../target/query-core-pending-overload-checkpoint-1-comparison.json)
on these exact bytes retains all 12 passes and the same two failures.
No earlier pass was lost in this selection.
This is not a compiler promotion. The accepted regression and corpus gates
remain required. Hono has not been rerun for this partial change.

## Immediate dependency path

Finish one callable operation. Do not replace each rejection with a new exception.

1. Add real `ReturnType<typeof parseInt>` to the existing public pending-global
   augmentation fixture. Keep its declarations and order unchanged. The passing
   unconstrained Last control tests later inference, not the earlier argument
   constraint. Retain the inner relation error in this public control. Do not
   read or alter held Query inputs to create a passing reduction.
2. Complete overload relations through shared operations. Pending source overloads
   need live signature demand and retry. Valid multi-overload sets need ordered
   signature projection and the real namespace export properties. Keep property
   origins, selected value demand, caller Array authority, and recovery state.
   The existing top-signature rule can then handle the scalar-any constraint.
   Do not admit overloads as propertyless objects. The
   [current path audit](../target/query-core-return-type-query-2-constraint-path.md)
   identifies these source gaps but does not assign a hidden Query failure cause.
   Preserve the completed lazy-header and selected-return operation.
3. Add direct-global qualified value lookup beside the existing import lookup.
   Use the complete merged owner and export proof. Keep import restrictions in
   the import path. Resolve only the selected member's annotation and preserve
   its declaration, parent and cache proof. Do not force the owner's signatures
   for `typeof parseInt.label`. The current selector accepts import namespaces
   only, so the new control fails before it reaches recursive member readiness.
4. Retain the implemented group-level active-demand set and live publication
   guard. Restore the active state on failure. Existing query-depth and return
   guards do not protect a pending group that has no SignatureId yet. The
   [recovery audit](../target/query-core-overload-demand-recovery-fix.md) confirms
   that the outer source-conditional entrypoints inspect fresh limits even when
   demand returns an error. Do not add a general error whitelist.
5. Connect ordinary calls before argument context, early effects, generic calls,
   conditional inference and source-aware display. Preserve declaration errors
   through call resolution. Do not flatten them to an unrelated unsupported result.

The [complete ReturnType audit](../target/query-core-pending-overload-alias-constraint.md)
maps planning, rest syntax, constraint instantiation, relation and inference.
Parallel reports also cover [call demand](../target/query-core-pending-overload-call-api.md),
[conditional demand](../target/query-core-pending-overload-conditional-api.md),
[qualified lookup](../target/query-core-pending-overload-qualified-query.md),
[recursive state](../target/query-core-pending-overload-recursion.md) and
[display](../target/query-core-pending-overload-display-api.md).
Root remains the sole code and test writer. One reviewer checks integration.

## Retained regressions and build cost

The two failures in the 85-case selection remain blocking. The
[instantiation-limit audit](../target/query-core-instantiation-limit-regression-path.md)
finds a real operation loss: source-aware generic parameter demand rejects an
ordinary recovered array mapping. Repair cold demand, cache validation, and warm
replay together. Keep constructor rejection and source-derived return proofs.
The [ambient publication audit](../target/query-core-ambient-publication-regression-path.md)
finds an error-contract mismatch before execution. Its later state assertions
have not run. Do not remove those assertions or waive the failure.

The [build audit](../target/query-core-test-query-build-reuse.md) explains the
second checker compilation. Query enables serde_core/result through serde.
The focused tests do not. Those dependency graphs produce separate checker
artifacts despite equal checker settings and source bytes. Reordering the same
commands does not remove this cost. Keep both cached variants. Any future
feature-graph alignment needs a separate measured change, not a hidden change
to the current regression command.

## Complete the value operation

Pinned Go first creates and caches one anonymous value object for the complete
merged function/module symbol. Plain typeof can return that identity before
resolving its signatures. When a later request needs structure, Go installs
the namespace members before creating the overload signatures. This order
allows a signature to refer to a member through a qualified typeof query.
Each signature retains its own source declaration and parameters. Return types
remain deferred until needed. Full declaration checks remain a separate step.

Rust has an authenticated merged-global owner proof and an overload provider.
SourceOverloadState now accepts Cold, authenticated Pending and Resolved.
Resolved still requires the complete signature and parameter publication,
reverse maps and namespace member table. Pending is not a completed callable.

Do not solve this by selecting one declaration, trusting the flags, or forcing
the full source checker from inside typeof. Use the existing owner proof and
extend the shared value operation to represent each valid stage explicitly.

1. Authenticate the whole owner with
   store::source_global_function_namespace_declarations. Retain the exact
   declaration sequence, binder ownership, value declaration and namespace
   exports. Use the existing overload row plans. Confirm whether the actual
   Query symbol passes this proof before attributing later failures to it.
2. Add a proved unresolved callable identity. Store enough source ownership
   evidence to distinguish it from a missing or damaged cache. Keep one TypeId
   when later requests resolve the members and signatures. Reuse existing
   pending callable support where its contract fits. Do not create a second
   incompatible callable representation.
3. Resolve namespace members before recursive signature demand. Retain active
   resolution state and a failure path that unwinds it. An active request is
   not proof that arbitrary pending data is valid. Keep separate checks for
   identity, member readiness, signature readiness and annotation readiness.
4. Connect signature and return demand to the existing row planners and source
   annotation queries. Keep the live query context and instantiation session.
   The current materialize_source_overloads driver resets the session before
   annotations and creates fresh queries. It cannot be called unchanged from
   a nested typeof request. Optional-parameter preparation also needs the
   caller-aware type preparation path.
5. Make ordinary source checking finish the same identity. Preserve overload
   selection order, implementation compatibility, namespace diagnostics and
   provider source-check state. Plain value demand must not mark a provider
   file checked or suppress its later diagnostics.
6. Route typeof through that shared value request. Keep lexical name identity
   separate from the effective value owner. Validate warm query/name caches
   against the current source proof. Do not accept a cold value with damaged
   signature, annotation or reverse-map state.

Inspect all consumers of the overload state before introducing a new state.
That includes source and expression checking, call resolution, property lookup,
relations, formatting and warm-cache validation. A pending value must reach a
real demand operation in each consumer, not become an empty callable object.

Share the annotation and publication worker between full-source and nested
demand. Full-source calls keep their current query boundaries, resets and
diagnostic order. Nested calls borrow the actual CanonicalTypeQuery. A copied
SourceTypeQueryContext does not contain all pending-parameter, class and
return state. Keep the source implementation-compatibility diagnostic loop
outside value-only demand. The [session audit](../target/query-core-type-query-overload-session.md)
identifies the two optional-union preparation calls that also need the live
session. A reset flag alone is not sufficient.

General inferred-variable typeof, forward references, flow narrowing and
fresh-literal normalization are separate known gaps. The observed Query error
does not reach those branches. Keep them in the remaining port plan. Do not
combine them with this batch unless the actual callable operation requires it.

## Focused controls

Use the existing public fixtures in source_merged_callable_symbols and
source_global_augmented_callable_symbols. They already check merged owner
identity, real signatures, namespace members, invalid calls and replay. Add
separate direct typeof controls. Do not change their existing inputs or checks.
These harnesses were not selected by full-3. The
[focused baseline](../target/query-core-type-query-overload-baseline-1-result.md)
now measures their four tests, and all four pass. With the seven ambient
overload tests, the selection has ten passes and one existing failure. All
seven outcomes that overlap full-3 are unchanged. None tests direct typeof.

The new controls must cover:

- A cold plain typeof query, then source checking, in both orders. Keep the
  same merged TypeId. Verify which signature and annotation caches stay cold.
- Direct call and namespace-member demand after that query. Check all source
  signatures and selected return types, not just successful completion.
- A signature that refers back to a namespace member with qualified typeof.
  Verify the resolution order and stable repeated requests.
- Invalid calls after cold typeof demand. Retain the exact existing diagnostic
  codes, locations, related declarations and recovery signatures.
- Generic and rest-parameter overloads with the real formal owners and caller
  Array authority. Keep source context and work budgets across nested demand.
- Damaged owner, member, signature and cache proofs. Rejection must not turn
  into a valid pending state or a second value identity.

Derive new expectations from Go pin dc37b5249ab60e2bbce936f71b883e6c8136167e.
Source comparisons are not measured Go outputs. Run the exact new TypeScript
controls through Go before accepting diagnostic assertions. Label lazy-cache
and identity expectations as pinned-source evidence unless a dedicated Go
query measures them. An ordinary diagnostic run does not measure those caches.

## Verification and stop rules

Compile implementation and test code. Run the focused positive and negative
controls. Rerun unchanged Query with the existing runner and normal logs.
Compare exact diagnostics and whether ordinary checking completes. A later
stopping point is useful evidence, not completion of this operation.

Then compare against the exact [full-3 result](../target/query-core-member-regression-full-3-comparison.json)
and [command manifest](../target/query-core-member-regression-full-3-command.json):
6,319 passes and 418 failures across 6,737 tests. Its source checkpoint is
38dd636991687cf26f28ba60e0247e4003a06152 with the preserved draft. Its complete
source fingerprint is
8f6d68eee8668cde06f0f508434bac80b0c0c34f4ae7e6835968063a939b1542.
All prior passes must remain. The accepted roster still has 263 failures and
13 absent names. Eleven of the 54 recent losses remain. No expectation change
or promotion is approved by this plan. Run the previously accepted corpus
selections before promotion. Hono remains a periodic cross-project check.

After two batches without useful Query progress, recheck the shared demand
path. Do not add workers or another cache exception as the default response.
The project milestone remains complete Query diagnostics matching Go, plus
the correct deliberate type error in a separate copy.

## Evidence

- [Go type-query operation](../target/query-core-type-query-go-operation.md).
- [Go controls and merged callable state](../target/query-core-type-query-go-controls.md).
- [Rust cache and overload paths](../target/query-core-type-query-cache-state.md).
- [Existing value demand](../target/query-core-type-query-value-demand.md).
- [Public test roster](../target/query-core-type-query-public-roster.md).
- [Source-check scheduling](../target/query-core-type-query-source-schedule.md).
- [Pending overload state](../target/query-core-type-query-lazy-overload-state.md).
- [Overload query and session boundaries](../target/query-core-type-query-overload-session.md).
