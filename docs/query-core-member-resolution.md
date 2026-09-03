# Query core member resolution

Updated 2026-09-03. Four lost tests recovered. Integration remains rejected.
Root is the only implementer. One reviewer checks code changes. Use the existing
`query-core-integration` branch. Do not start another feature branch.

## Result required

Complete the shared class/interface member operation. It must retain member
symbols before it reads named member types. It must resolve inherited members
with the actual type arguments, `this` type and source query context.

The [complete tests](../target/query-core-source-member-operation-2-result.md)
now pass at checkpoint `5a1882c5d`, built on the earlier owner and Pending/Resolved
changes. Both source-first and query-first cases retain actual inherited types,
default arguments, class properties, method identity and stable replay. The
negative case reports the exact TS2322 diagnostic. The unused generic method
remains unresolved. Pinned Go agrees on both unchanged TypeScript inputs.
The fixture does not cover all of Query's import and alias paths.

The [latest full regression selection](../target/query-core-member-regression-full-1-result.md)
has 6,278 passes and 457 failures across 6,735 tests. It retains all 6,274
previous passes and recovers four losses. Fifty of the 54 recent lost passes
remain. Against the accepted compiler, 5,769 of 6,055 pass, 273 fail and 13
exact names are absent. The batch is rejected. No expectation change is approved.
The three-file repair is saved as signed checkpoint `ae2f42ac2`. The separate
reference-flow draft remains unchanged and unstaged.

[Unchanged Query](../target/query-core-member-regression-query-2-result.md)
still completes only 2 of 23 isolated roots. Ordinary checking no longer stops
at the unread Node `send` method. It fails at a void annotation instead. No
additional root completes and diagnostics remain unchanged. This is not a demo.

## Current dependency path

The local export-owner mismatch is repaired. The shared proof derives
`EXPORT_VALUE` from the actual declarations that share the local symbol. It
does not infer the local marker from the final merged owner's flags. File and
namespace exports use the same proof. Nonambient const-enum-only modules retain
the binder's value-export meaning.

The source member operation now connects ambient global reads, nongeneric
inherited lookup and applied generic bases. It retains names before demanding
one member value. That exposed failures in existing consumers and validators.
Repair these failures before advancing Query's next stopping point.

1. Separate full and name-only member plans. A full request must upgrade an
   earlier name-only plan. A later lazy request must not downgrade a full plan.
   Preserve caller mode when planning concrete generic bases. Select strict
   completed generic reuse during planning, before optional-union and receiver
   preparation. Compute expected member types from source, not stored values.
2. Complete the remaining shared source demand. Direct completed heritage must
   use the source-aware property provider. Empty intermediate interfaces need
   an empty member plan. Proved nongeneric source bases must retain identity
   through the instantiation classifier. Carry written-base owner proofs into
   reference planning and preserve legal repeated bases. The
   [parallel audit](../target/query-core-member-regression-parallel-audit.md)
   records the concrete paths and limits on each finding.
3. Recheck all 50 remaining recent losses and both complete member tests. Then run
   the full accepted selections. Every earlier accepted loss also stays open.
4. Rerun unchanged Query. Its current void failure needs bounded metadata for
   the rejecting reader, ownership role, plan membership and cache fields. The
   keyword planner, executor and cache readers already support void. Do not
   add another syntax admission rule.

The latest patch restores source heritage validation before identity reuse,
fills ordinary Pending values without replacing names or proxies, and connects
inherited source-aware property demand. It also extends the checked Array edge
walk. Cached annotation edges on Pending members still need to stay in that
walk. Shape validation alone does not prove caller Array authority.

The negative DOM test's exact private corruption is not visible in the log.
It still fails. Do not change its expectation. No private test body or held
Query source body was read.

The rest of the same operation remains open:

- Resolve class methods through their existing source method proof. Do not send
  a `MethodDeclaration` through a validator limited to `MethodSignature`.
- Complete computed names through their real key publisher. The new name planner
  currently reports them as unsupported.
- Complete the class base-constructor state and argument counts described below.
- Keep full source declaration checks separate from lazy consumer lookup. The
  current routes remain separate, but changed cache expectations need concrete
  pinned-Go evidence before any test change.

Eighteen read-only investigations ran in parallel. Keep one production writer
and one code reviewer. Give extra workers bounded source and evidence checks.
Do not promote the checkpoint while any regression is unresolved.

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

The checkpoint adds merged-owner defaults and the measured class/interface
instance-base path. General runtime class bases and selected class methods
remain unfinished. The shared member operation also has the regression gaps
listed above. Changing only the global-read guard does not finish these callers.

Full Go source checking resolves ordinary property values. Plain bodyless method
checking does not always resolve the named method's callable cache. Rust still
uses its older eager method-value policy in full publication. Separate method
annotation checking from selected method value demand before claiming cache
parity. Pinned Go also retains repeated noncircular bases in written order.

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
old passing name and diagnostic record. The current 273 failures, 13 absent
names and changed corpus records remain open blockers. New passes do not offset
them. Do not change an accepted expectation without concrete pinned-Go evidence.

The immediate project milestone remains complete Query diagnostics matching
Go, plus the correct deliberate type error in a separate Query copy. Hono is
a periodic cross-project check. Full type, symbol and replay parity remain
requirements for the finished compiler.
