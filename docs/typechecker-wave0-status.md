# Typechecker Wave 0 integration status

- Status: active
- Started: 2026-07-16
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Wave branch baseline: `cdbf749`
- Integration branch: `july-ultra`
- Current root adapters: `690f13e`, `2ef996a`

This is the live execution record for Wave 0 of
[`typechecker-completion-goal.md`](typechecker-completion-goal.md). The port
map remains authoritative for cluster state.

## Active lanes

| Lane | Branch/worktree | Current task | State |
|---|---|---|---|
| Root/integration | `july-ultra`; repository root | typed failure envelope, declaration-target admission, serial verification | `690f13e` and `2ef996a` committed; reviews pending |
| M0 | `agent/w0-m0-scorecard`; `../ts-rust-worktrees/w0-m0-scorecard` | retained-fatal scorecard, provenance, registry, fixed manifest | implementing |
| S2a | `agent/w0-s2a-members`; `../ts-rust-worktrees/w0-s2a-members` | direct nongeneric interface heritage and inherited members | contract frozen; implementing |
| S3 | `agent/w0-s3-instantiation`; `../ts-rust-worktrees/w0-s3-instantiation` | composite mapper and exact instantiation session | contract frozen; implementing |

Only S2a and S3 are semantic writers. M0 consumes the root-owned typed failure
envelope and does not edit checker/compiler query internals.

The S1a compiler prerequisite is now present: a plain `.d.ts` external module
may be the resolved target of a plain TypeScript ESM/Bundler source while the
importing source gate remains unchanged. Declaration files are still bound and
retained, `skipLibCheck` still suppresses their source check, and declaration-
target value/type consumption remains an explicit S1b checker leaf.

## Frozen S2-S3 boundary

The existing `ObjectTypeData`, `TypeReferenceData`, `StructuredTypeData`,
`InterfaceTypeData`, `Signature`, `IndexInfo`, and symbol-link records are the
single canonical graph. No parallel member or reference cache may be added.

S3 owns a read-only reference-shell descriptor with:

- destination and declared-source identities;
- `Identity` or exact ordered source/target mapping;
- pinned padding of a missing final `this` argument with the destination
  reference; and
- cold/resolved/malformed validation without an identity fallback.

S2 resolves the source's declared cache, then gives only that cache to S3 as
one batch: raw member table, ordered properties, call signatures, construct
signatures, and index infos. Identity reuses the raw table, including reserved
entries. Instantiation creates named value members plus separate signature and
index vectors. S3 never traverses bases and never publishes destination
structured members.

S2 resolves and instantiates each base separately, merges in declaration
order, retains own-before-inherited property order, appends call then construct
signatures, de-duplicates inherited index keys, and performs the sole final
structured publication. Instantiated symbols/signatures remain lazy through
two-phase target-type/return queries; index-info value types instantiate
eagerly and reuse the original index identity when unchanged.

The first parallel stacks deliberately do not yet compose: S2a proves a direct
nongeneric inherited-property vertical while S3 proves composite mapping and
the query-scoped instantiation session. Their next stacks meet at a generic
`Box<T>` member vertical.

## Hub leases

| Hub | Wave | Owner | Base | Allowed symbols | Expiry |
|---|---|---|---|---|---|
| `semantic/relater.rs` | W0.1 | `agent/w0-s2a-members` | `cdbf749` | `RelationUnavailable` additions; `ResolvedObjectMembers`; `structured_type_related_to`; `properties_related_to`; `call_signatures_related_to`; `resolved_object_members`; new index-relation helpers | reviewed S2a integration commit |

Root and every other worker treat the leased surface as read-only until the
lease expires. `type_nodes.rs`, `source.rs`, `store.rs`, `type_records.rs`,
`production.rs`, `formatter.rs`, and `ts_compiler/src/lib.rs` remain root-owned.

## Required integration evidence

- M0 completes all selected variants after a fatal result, records the typed
  capability or invariant code, writes its scorecard, and exits nonzero.
- The scorecard embeds upstream/Rust SHA, dirty state, manifest digest, exact
  invocation, and stable variant keys.
- S2a proves inherited property order, missing-property diagnostics, inherited
  reads, cold/warm identity, poison/foreign rejection, and cycle safety through
  a public production path.
- S3 proves Composite-versus-Merged behavior, no-op identity, cache-before-
  counter ordering, depth/count boundaries, active-mapper recursion, and
  query-local reset.
- Every stack receives a Go-semantic review and a separate Rust-invariant
  review before serial integration.
- Root runs focused tests, `cargo check --tests`, strict Clippy, rustdoc, and
  the fixed scorecard after integration.
