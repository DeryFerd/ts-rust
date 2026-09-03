# Query core type-query work

Updated 2026-09-03. This is the next implementation plan, not a completed fix.
Use query-core-integration. Root owns production code, tests and the index.
One reviewer checks the complete change. Other workers investigate bounded
questions and write separate reports. Do not start another feature branch.

## Measured failure

Ordinary Query checking stops at TypeQuery, file 20, node 82, bytes 1196..1213.
The bounded observation found an Identifier query with no type arguments.
Its resolved symbol has four declarations, no parent, no export-symbol link
and no cached value type. Its flags are TRANSIENT | FUNCTION | VALUE_MODULE.
plan_value_type_query rejects the declaration list because it requires exactly
one declaration. It never asks for the value type.

The held operand name and declaration bodies remain unread. Four declarations
do not prove four signatures. The actual global merge proof and declaration
split still need confirmation. See the [run result](../target/query-core-type-query-observation-1-result.md).

The run has the same 244 checking records as the clean checkpoint. Two of 23
isolated roots complete. Ordinary checking does not complete. No diagnostic
changed. All temporary traces were removed and the clean fingerprint restored.

## Complete the value operation

Pinned Go first creates and caches one anonymous value object for the complete
merged function/module symbol. Plain typeof can return that identity before
resolving its signatures. When a later request needs structure, Go installs
the namespace members before creating the overload signatures. This order
allows a signature to refer to a member through a qualified typeof query.
Each signature retains its own source declaration and parameters. Return types
remain deferred until needed. Full declaration checks remain a separate step.

Rust has an authenticated merged-global owner proof and an overload provider.
It does not yet have the same lazy overload-value state. SourceOverloadState
accepts only Cold or Resolved. Resolved requires the complete signature and
parameter publication, reverse maps and namespace member table. A partially
published value is currently a cache error.

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
