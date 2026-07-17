# Typechecker Wave 0 integration status

- Status: active
- Started: 2026-07-16
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Wave branch baseline: `cdbf749`
- Integration branch: `july-ultra`
- Current integration head: `174eebf`

This is the live execution record for Wave 0 of
[`typechecker-completion-goal.md`](typechecker-completion-goal.md). The port
map remains authoritative for cluster state.

## Active lanes

| Lane | Branch/worktree | Current task | State |
|---|---|---|---|
| Root/integration | `july-ultra`; repository root | contract adapters, review, serial verification | M0, S1b, S3 kernel, arrow capability recovery, and the fixed smoke lane integrated; root is the sole Cargo/build owner |
| M0 | `july-ultra`; repository root | deterministic checker scoring | schema-5 provenance, retained fatal outcomes, exact fixed-manifest execution, and selected-case preparation integrated through `174eebf` |
| S2a | `agent/w0-s2a-members`; `../ts-rust-worktrees/w0-s2a-members` | exact single-base interface heritage | implementation complete; repeated adversarial review found relation-cache invalidation bugs, so an observed-dependency redesign is in progress before integration |
| S3 | `agent/w0-s3-instantiation`; `../ts-rust-worktrees/w0-s3-instantiation` | composite mapper and instantiation-session kernel | integrated through `4701c60`; checker check, strict Clippy, and rustdoc green |
| S3b | `agent/w0-s3b-session`; `../ts-rust-worktrees/w0-s3b-session` | lazy generic-call demand and source-owned instantiation accounting | `a27ee8c`/`f11eb00` are rejected as-is; a fresh read-only Go/Rust audit is specifying the replacement slice |
| S1b | `agent/w0-s1b-declarations`; `../ts-rust-worktrees/w0-s1b-declarations` | direct named `.d.ts` value/type consumption | integrated through `c23594d`; both program orders, warm reuse, skipLibCheck, and fail-closed boundaries pass |

S2a is the only active semantic writer. S3b is a read-only audit until its
ownership and lazy-demand contract is frozen. Root keeps integration, shared
dispatch adapters, Cargo, and corpus scoring serialized while spare capacity
rotates through independent Go-semantic and Rust-invariant review.

## Fixed smoke evidence

`checker-smoke-v1.json` freezes 96 unique variant keys across eight semantic
families. Two clean executions at `174eebf` produced the same scorecard digest,
`12dd493b4e782771446eb922579def8d`, with no fatal invariants. The fixed-shard
digest is `60dbd52bce2c3f9f94971819ad0d9cda`; the complete pinned-oracle manifest
digest is `667bc371832bee995194e09bc5b6e968`.

The current frontier is four exact variants, 90 typed capability boundaries,
and two supported mismatches. The run discovers 12,750 upstream configurations,
selects 95 cases and 96 variants, and completes in about 88 seconds on the
recorded machine. This is a deterministic merge gate, not a coverage claim.

The S1a compiler prerequisite is now present: a plain `.d.ts` external module
may be the resolved target of a plain TypeScript ESM/Bundler source while the
importing source gate remains unchanged. Declaration files are still bound and
retained, `skipLibCheck` still suppresses their source check, and declaration-
target value/type consumption now admits direct exported declaration constants,
nongeneric aliases, and nongeneric interfaces. Declaration bind and checker
diagnostics remain suppressed under `skipLibCheck` while the retained symbols
and imported types stay available.

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
| `semantic/relater.rs` | W0.1 | `agent/w0-s2a-members` | `cdbf749` | heritage admission/relation helpers plus successful-relation dependency collection | reviewed S2a integration commit |
| `semantic/store.rs` | W0.1 repair | `agent/w0-s2a-members` | `e867a88` | relation-observed identity sets and changed-write invalidation only; no unrelated store API work | reviewed S2a integration commit |

Root and every other worker treat the leased surface as read-only until the
lease expires. `type_nodes.rs`, `source.rs`, `type_records.rs`, `production.rs`,
`formatter.rs`, and `ts_compiler/src/lib.rs` remain root-owned. The temporary
`store.rs` repair lease exists only because a successful relation cache must
retain the exact identities whose later mutation invalidates that cache.

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
