# Query core member resolution

Updated 2026-09-03. This is the next implementation task, not a completed fix.
Root is the only implementer. One reviewer checks the change. Use the existing
`query-core-integration` branch. Do not start another feature branch.

## Result required

Complete the shared class/interface member operation. It must retain member
symbols before it reads named member types. It must resolve inherited members
with the actual type arguments, `this` type and source query context.

The [new test baseline](../target/query-core-merged-members-baseline-5-result.md)
is committed as `37179715d`. Both tests compile and fail at the actual `Emitter`
base reference. Pinned Go passes the positive fixture and reports exactly
TS2322 for the separate negative fixture. The assertions after Rust's failure
have not executed. The fixture does not yet cover Query's import/alias route.

Query's last unchanged run still completes only 2 of 23 isolated roots.
Ordinary project checking does not complete. There is no new Query gain.

The first [implementation checkpoint](../target/query-core-merged-members-implementation-3-result.md),
`af2597745`, compiles but is not accepted. Both complete tests still fail.
The [new Query run](../target/query-core-merged-members-query-1-result.md) has
the same 244 checking records as the previous run. Do not add more base
admission rules before changing the shared member-value state below.

## What the source comparison established

The Go checkout is pinned to `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
The following functions are in `internal/checker/checker.go` at that pin.

| Go operation | Behavior needed in Rust |
| --- | --- |
| `getDeclaredTypeOfClassOrInterface` | Publish one canonical identity. A merged class/interface keeps class identity and shared formals. |
| `getTypeFromClassOrInterfaceReference` | Fill omitted defaults from the actual formal declarations, then create the reference. |
| `resolveDeclaredMembers` | Retain named member symbols. Resolve call, construct and index signatures, not every named method type. |
| `getBaseTypes` | Process class heritage first, then every interface contribution of the same owner. |
| `resolveObjectTypeMembers` | Publish own members before recursive inherited lookup. Apply argument and `this` mappings. Mark the table complete only after its bases complete. |
| `getPropertyOfTypeEx` | Select the property symbol from that table. Demand its type through the normal caller. |

Rust already has the merged identity operation. `declared.rs::preflight_class_plan`
collects the actual class and interface formals. Its declared-type dispatcher
chooses class identity first. Reuse this implementation.

The missing work is downstream. Current default planning excludes merged class
owners. Interface heritage has no general class-instance base path. Both the
selected interface method planner and selected class method planner exclude
the merged generic owner. Changing only the global-read guard cannot fix these
callers.

## Implementation

### 1. Share the owner and member-name plan

Use the canonical merged symbol, all ordered declarations and the existing
declared identity. Keep instance members separate from class static exports.
Retain actual formal symbols, member symbols, names and declaration ownership.
Do not create an interface-shaped replacement for a class owner.

Reuse the source and cache checks in `object_members.rs`:

- `plan_source_member_names`
- `validate_source_member_name_cache`
- `validate_cold_source_member_symbol`
- `cold_source_interface_local_member_edges`

Refactor these checks around a shared class/interface owner plan. They must
cover class and interface contributions without evaluating unread named member
annotations. Keep validation of cached annotation and signature edges. An
unread member is not permission to trust a stale published cache.

Match the meaning of Go's declared-member state. A resolved member-name table
does not mean every named member type is known. Change callers and validators
that currently make that assumption together. Do not add another package-specific
header or a second definition of completed members.

Use explicit pending and resolved values in `instantiated_members::DeclaredProperty`.
Pending requires a proved completed name table and clean unresolved value links.
Keep identity, declaration, parent and table checks for both states. Keep all
existing value checks for resolved members. Compute proxy policy from the
owner/reference mapping, not from cache warmth. A resolved source must not make
an existing proxy suddenly invalid. Reject a resolved proxy or recovery record
while its source is pending. At demand, resolve and validate that one source
member through the live query, then use the existing proxy mapper.

### 2. Resolve defaults and bases from that owner

Generalize `preflight_merged_interface_defaults` and the direct reference
target planner to the shared owner. Select each default from the actual
canonical formal's declarations. Preserve source order and constraints.
Reuse `resolve_direct_generic_reference_defaults`, with the real argument
mapper for merged class owners as well as ordinary classes.

Extend the base operation to combine the selected class declaration's base
and every merged interface base. Evaluate the written references through the
normal source type query. Preserve import and alias proofs. Do not require a
base to be a nongeneric global interface/value pair.

Reuse the active `ResolvedBaseTypes` resolution frame, ordered base publication
and later heritage constraint checks from the recent crash repair. A pending
base is not an empty base. A failed request must unwind its active frame.

The checkpoint still needs four class-base corrections. Separate `extends`
from `implements`. Authenticate actual class base references. Retain the
existing class base-constructor state separately from interface contributions.
Use the local formal count for written argument arity, while retaining the full
outer/local vector for identity checks. These are not completed by widening
the interface executor's class flag check.

### 3. Build the member table and demand one member

Keep own names first. Add inherited names in base order without replacing an
own member. Create mapped member symbols with their real target and mapper.
Keep their value types lazy. Resolve call, construct and index signatures at
the same stage as Go.

Dispatch selected declarations to the existing syntax-specific property and
method planners. A merged method can have several declarations. Preserve all
of them and their order. Do not select only the class declaration or rewrite
its owner flags to pass the interface planner.

Carry `SourceTypeQueryContext` and the caller's instantiation session. This
includes aliases, globals, active requests and completed source proofs.
Globals and checker options alone are insufficient. Reuse the source-aware
property, signature and type instantiation APIs. A conditional return type
must not lose its source when inherited or instantiated.

### 4. Connect all relevant callers

Use this same operation for the global declared-value read, property lookup,
method lookup and inherited-member relation demand. Start with:

- `source.rs::check_source_plan`, the cross-file global-read loop
- `CanonicalTypeQuery::plan_declared_value_type`
- `object_members::resolve_object_property_by_key_with_source`
- `CanonicalTypeQuery::get_property_of_source_interface`
- The source-aware property and signature demand in `instantiated_members.rs`

Remove the duplicated no-heritage admission checks only when these callers
can complete the operation. Keep full source-declaration checking separate.
When a declaration file is actually checked, unread declarations still need
their normal diagnostics. Lazy consumer lookup must not silently skip that
phase.

## Verification and promotion

First run `source_merged_class_interface_members`. Both complete tests must
pass. They check the defaulted reference, merged owner, inherited types, class
property, method result and proxy identity, unused method state, negative
diagnostic and replay. Keep their Go-checked TypeScript inputs unchanged.

Then rerun unchanged Query with the existing runner and logs. Report exact
diagnostic changes and whether ordinary checking completes. The small fixture
does not replace this check, especially for imports and aliases.

Before promotion, run the accepted regression selections and compare every
old passing name and diagnostic record. The current 253 failures, 13 absent
names and changed corpus records remain open blockers. New passes do not offset
them. Do not change an accepted expectation without concrete pinned-Go evidence.

The immediate project milestone remains complete Query diagnostics matching
Go, plus the correct deliberate type error in a separate Query copy. Hono is
a periodic cross-project check. Full type, symbol and replay parity remain
requirements for the finished compiler.
