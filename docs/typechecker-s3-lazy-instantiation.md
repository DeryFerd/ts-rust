# S3 execution contract: lazy generic-call instantiation

- Status: audited; implementation queued behind S2
- Audit date: 2026-07-16
- Integration branch at audit: `2691cbe`
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Rejected draft branch: `agent/w0-s3b-session` through `f11eb00`

This document freezes the next S3 implementation boundary. It supplements
[`typechecker-completion-goal.md`](typechecker-completion-goal.md) and the live
[`typechecker-wave0-status.md`](typechecker-wave0-status.md) ledger.

## Decision

Port typescript-go's lazy, store-backed instantiated-signature model. Do not
extend Rust's current eager generic-call projection or cherry-pick
`a27ee8c`/`f11eb00` wholesale.

The checked call path must:

1. reject type/value arity before creating a checked instantiation;
2. check explicit constraints before creating a checked instantiation;
3. create or reuse a globally cached mapper-backed signature shell;
4. leave every instantiated parameter type unresolved;
5. leave the signature return unresolved;
6. demand parameters left-to-right during applicability and stop at the first
   mismatch;
7. create an uncached recovery shell after failure; and
8. demand only the selected checked or recovery return during source-call
   finalization.

This preserves observable upstream behavior. TS2554, TS2558, and TS2344 do not
instantiate checked parameters or returns. TS2345 resolves only the checked
parameter prefix that applicability demanded, leaves the checked suffix and
return unresolved, and resolves the recovery return. A successful call resolves
used parameters before resolving its return.

## Upstream anchors

| Concern | Pinned typescript-go anchor |
|---|---|
| Counter ownership and reset | `checker.go` checker fields, `checkSourceElement`, `checkDeferredNode`, `checkExpressionEx` |
| Call resolution and overload choice | `checkCallExpression`, `getResolvedSignature`, `resolveCallExpression`, `resolveCall`, `chooseOverload` |
| Arity, constraints, applicability | `hasCorrectTypeArgumentArity`, `checkTypeArguments`, `isSignatureApplicable` |
| Failure recovery | `getCandidateForOverloadFailure`, `pickLongestCandidateSignature`, `inferSignatureInstantiationForOverloadFailure` |
| Lazy checked signature | `getSignatureInstantiationWithoutFillingInTypeArguments`, `instantiateSignatureEx` |
| Lazy parameter type | `instantiateSymbol`, `getTypeOfInstantiatedSymbol`, `relater.go::getTypeAtPosition` |
| Lazy return | `getReturnTypeOfSignature` |
| Core accounting | `instantiateTypeWithAlias`, `pushActiveMapper`, `clearActiveMapperCaches` |

## Counter and reset contract

One checker-owned instantiation session spans source checking. Its query count
resets at every source-element, deferred-node, and expression entry. It does not
reset inside call resolution, overload retries, inference, parameter demand,
return demand, or signature creation.

Expression resets are not lexically restored. A nested callee or argument
expression resets the shared count, and the outer call continues from the last
nested expression's ending count. Total instantiation count is checker-lifetime
telemetry and never resets. Depth and active-mapper frames are dynamic recursion
state and are not query-reset fields.

The core ordering is exact:

1. identity/cannot-contain-type-variables early return;
2. depth/count guard;
3. locate or push the active mapper;
4. consult its cache;
5. return a hit without incrementing;
6. on a miss, increment total count, query count, and depth;
7. instantiate;
8. cache and pop the mapper frame; and
9. decrement depth.

The limit guard precedes the cache lookup. At the count limit, an otherwise
valid active-mapper cache hit still reports TS2589. A recovering session records
the limit event and returns the canonical error type at the recursive boundary,
so outer wrappers remain intact. Recovery must happen inside the core
instantiation routine, not by catching a top-level error.

## Rust contract

### Instantiation leaf

`semantic/instantiate.rs` owns the production-capable session:

- fail-fast and recovering limit policies;
- exact count, depth, total, and active-mapper behavior;
- a monotonic limit-event marker;
- query-count reset without resetting total/depth/frames;
- active-mapper cache clearing after each inferred type; and
- session-aware single and vector instantiation entry points.

The recovering constructor validates that the error type belongs to the store.
A limit hit does not increment query or total counts.

### Generic-call leaf

`semantic/generic_calls.rs` owns:

- cached checked signature shells with exact target/mapper identities;
- transient instantiated parameter symbols whose resolved type starts `None`;
- left-to-right parameter demand;
- deferred return demand;
- uncached recovery shells;
- warm validation that accepts monotonic `None -> Some` filling;
- inference/default/constraint use of the shared session;
- active-mapper cache clearing at the pinned inference boundary; and
- removal or conversion of the eager identity-generic fallback.

An already resolved parameter or return is reused without re-instantiation so a
warm validation does not change accounting. A wrong or foreign cached value
fails atomically.

### Concrete generic-call replacement map

The current eager implementation is concentrated enough to remain one leaf.
Its two implementation commits should make these replacements:

1. Add one checked-signature shell get/create path and allocation-free warm
   validator. `prepare_generic_call_vector_signature` and
   `publish_prepared_generic_call_vector_signature` must publish transient
   parameter links with `resolved_type: None` and signatures with
   `resolved_return_type: None`. Both existing materializers must use this one
   publisher instead of building duplicate eager graphs.
2. Reorder `project_validated_generic_call_vector` to perform arity, explicit
   constraints, checked-shell publication, left-to-right applicability, and
   uncached recovery in that order. Replace `instantiate_generic_call_shape`
   and `generic_call_projection` with individual parameter/return demand and
   recovery-shell helpers. Thread the same `InstantiationSession` through
   defaults, inference, constraints, and demand, clearing active mapper caches
   immediately after each inferred type is finalized.

`check_generic_call_arguments` must demand one parameter slot before each
relation and stop at the first mismatch. Source finalization then demands only
the selected checked or recovery return. The existing identity-call fallback
keeps its source-only inference proof but must route its type argument through
the same shell, demand, recovery, and return primitives; it must not remain a
second eager semantic model.

The existing store already supplies the required mapper, symbol, signature,
value-link, cached-signature, reservation, and setter APIs. After S2 lands,
ordinary `set_value_symbol_links` and `set_signature_resolved_return_type`
writes also invalidate relations that observed a lazy `None` slot. No new
semantic record or mandatory `store.rs` adapter is expected.

Warm validation of an already resolved union return must remain allocation
free. Prefer a local exact mapper-result verifier over the currently installed
intrinsic, literal, type-parameter, Array, and anonymous-union domain. If that
becomes unreasonably duplicative, the only acceptable extra substrate is a
read-only union-cache identity lookup; warm validation must never intern a type
or repair a poisoned cache.

### Root-owned adapters

Root serializes the high-fanout changes:

- `production.rs`: checker-owned recovering session;
- `source.rs`: source-element and expression resets plus session threading;
- `source_calls.rs`: retry reuse, selected-return finalization, and TS2589;
- `type_nodes.rs`: mapper-backed signature return demand; and
- any unavoidable `store.rs` adapter after S2 lands.

Every retry in one source call shares the same session. The normal store setters
publish lazy parameter and return types so S2 relation-cache invalidation sees
their `None -> Some` transitions.

## TS2589 recovery

Source-call checking records a session event mark before resolution and emits
TS2589 if a later limit event occurred. The diagnostic uses the call node,
message code 2589, no range override, and no related information. The error type
continues through relation, selected-return publication, and call links; a limit
is not reclassified as unsupported or fatal.

Nested calls claim their own events because their call check completes before
the outer call takes its mark.

## Acceptance matrix

### Core session

- identity early return succeeds at an exhausted count;
- an active-mapper hit below the limit does not increment;
- the same hit at the limit triggers the guard before lookup;
- depth/count recovery retains outer array wrappers;
- reset clears query count only;
- active-mapper cache clearing preserves counters and frames; and
- a foreign recovery error type fails closed.

### Generic calls

- arity failure creates no checked shell and demands no checked type;
- explicit constraints precede checked shell creation;
- a mismatch at parameter zero leaves every suffix parameter unresolved;
- success resolves parameters during applicability and return afterward;
- TS2345 leaves the checked suffix/return unresolved and resolves only the
  recovery return;
- a later warm call fills only missing checked slots;
- retries cannot reset or evade the count limit;
- checked shells are cached before applicability;
- recovery shells are never cached; and
- poisoned parameter/return caches fail without partial publication.

### Public production path

Add `source_instantiation_limits.rs` after the two leaves and root adapters
compose. Its deep generic appears only in a later parameter:

- too few arguments yields TS2554 without TS2589;
- a first-argument mismatch yields TS2345 without demanding the deep suffix;
- a matching prefix that demands the deep parameter yields TS2589;
- the call result still recovers to its concrete return type;
- selected-signature and call-type links publish;
- a warm recheck adds no diagnostics or allocations; and
- a later call reuses the checked shell and fills an unresolved suffix.

Add one S2/S3 composition regression: warm a relation over a lazy instantiated
parameter/signature, fill the parameter or return through the normal store
setter, prove the relation invalidates and recomputes, and prove equal/rejected
writes remain clean.

## Four-slot execution

After S2 integrates:

| Slot | Ownership |
|---|---|
| Root | `production.rs`, `source.rs`, `source_calls.rs`, `type_nodes.rs`, serial Cargo/integration |
| Leaf A | `instantiate.rs` only |
| Leaf B | `generic_calls.rs` only |
| Reviewer/tests | adversarial review first; then the new public test target without production-file edits |

The leaves agree on the session API before either implementation begins. There
is no file conflict between them. S2 is a semantic prerequisite and conflicts
with any S3 attempt to edit `store.rs`, so S3 rebases only after S2 lands.

## Commit order

1. Land S2 observed-dependency invalidation.
2. Rebase the S3 worktrees onto the new root.
3. Land the `instantiate.rs` session/recovery core.
4. Land checked-shell and lazy parameter demand in `generic_calls.rs`.
5. Land recovery, identity, and inference parity in `generic_calls.rs`.
6. Land root context/source/return-demand integration and TS2589.
7. Land public production and S2/S3 composition tests.
8. Run the fixed checker smoke manifest and update the execution ledger.
