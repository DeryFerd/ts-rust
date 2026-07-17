# Typechecker Wave 0 integration status

- Status: active
- Started: 2026-07-16
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Wave branch baseline: `cdbf749`
- Integration branch: `july-ultra`
- Current integrated semantic stack: through `6c3bf97`

This is the live execution record for Wave 0 of
[`typechecker-completion-goal.md`](typechecker-completion-goal.md). The port
map remains authoritative for cluster state.

## Active lanes

| Lane | Branch/worktree | Current task | State |
|---|---|---|---|
| Root/integration | `july-ultra`; repository root | contract adapters, review, serial verification | M0, S1b named reexports, S2a including readonly directionality, and the recovering/lazy S3 generic-call path are integrated; root is the sole Cargo/build and fixed-shard owner |
| M0 | `july-ultra`; repository root | deterministic checker scoring | schema-5 provenance, retained fatal outcomes, exact fixed-manifest execution, and selected-case preparation integrated through `174eebf` |
| S2a | `july-ultra`; repository root | exact single-base interface heritage and relation-cache observation | integrated through `14ae6ce`; two exact-tip reviews found no P0/P1 issue, all five public heritage tests pass, and the fixed shard advances one interface fixture without an exact loss |
| S2 readonly follow-up | `july-ultra`; repository root | readonly property retention and strict-subtype directionality | integrated through `d4719b3`; two independent reviews found no P0/P1 issue, the public production target passes, focused strict Clippy is green, and the fixed shard is semantically unchanged |
| S3 session/generic calls | `july-ultra`; repository root | lazy checked shells, shared query sessions, exact demand/recovery, and TS2589 | integrated through `010d93a`; the library check and focused `source_generic_calls`/`source_instantiation_limits` targets pass, and independent review found no remaining P0/P1 issue |
| S1b | `july-ultra`; repository root | named ESM imports and two-hop renamed/type-only reexports | integrated through `6c3bf97`; 17 focused import/reexport public tests pass, sparse immediate-link timing matches pinned `resolveAlias`, warm alias/type-only/value poison is rejected, and independent review approved the slice |
| W1 S5 | isolated worker worktree | dependency-independent nongeneric `keyof`/property-key algebra leaf | active from `6c3bf97`; worker owns new leaf modules and bounded indexed-access changes while root retains type-node/options/formatter adapters |
| W1 S6 | isolated worker worktree | direct explicit generic class/interface reference shells | active from `6c3bf97`; worker owns the reference leaf and bounded instantiation/declared helpers while root retains type-node/store/source adapters |
| W1 review/oracle | independent reviewer lane | pinned S5/S6 expected behavior, cache timing, and adversarial fixtures | active; no production writes or Cargo ownership |

The current four-slot topology is the intended steady state: root integrates
and builds, two isolated semantic workers own non-overlapping leaves, and one
reviewer/oracle lane audits both Go behavior and Rust cache invariants. Shared
store, source-dispatch, compiler, and formatter adapters remain serialized at
root.

## Fixed smoke evidence

`checker-smoke-v1.json` freezes 96 unique variant keys across eight semantic
families. Two clean executions at `174eebf` produced the same raw scorecard
digest, `12dd493b4e782771446eb922579def8d`, with no fatal invariants. The
fixed-shard digest is `60dbd52bce2c3f9f94971819ad0d9cda`; the complete
pinned-oracle manifest digest is `667bc371832bee995194e09bc5b6e968`.

The S2a integration run at `14ae6ce` has raw digest
`efa3ce8f2047b2fa7e8e12a320dd3b73`. After removing only Rust commit/dirty and
invocation provenance, its sole semantic delta from `174eebf` is that
`anyIsAssignableToObject.ts` advances from the interface declaration boundary
to its first unsupported property declaration. The S3 session-core run at
`75abbf5` has raw digest `f895b87f26f22da71aafa385709eba09` and is byte-for-
byte identical to the normalized S2a scorecard (`9c64e6157ea7b7b8b6f0f0332a61d034`).

The readonly-property follow-up through `d4719b3` has raw digest
`0a63690ed0c698f2e0463e7aa521c241`. After deleting only Rust commit/dirty and
invocation provenance, it is byte-identical to the `75abbf5` session-core run.
The public target proves source-retained readonly state across interfaces,
type literals, direct heritage, formatting, bidirectional assignability, and
warm rechecks; internal relation evidence proves the pinned strict-subtype
ordering and changed-versus-equal cache invalidation behavior.

The integrated lazy-generic/session stack through `010d93a` has raw fixed-shard
digest `dce743a4b3ed9fa6ddc09822a8f5e16e`. The complete named-reexport stack
through `6c3bf97` has raw digest `25d72d4210b7a8f7ab46f1478a7855fc`.
After removing only Rust commit/dirty and invocation provenance, both hash to
`353dddd39af6749db775683da54d7c9a`, exactly matching the normalized readonly
baseline. Both runs retain four exact variants, 90 typed capability boundaries,
two supported mismatches, and zero fatal invariants.

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
| `semantic/relater.rs` | W0.1 | `agent/w0-s2a-members` | `cdbf749` | heritage admission/relation helpers plus successful-relation dependency collection | expired at reviewed integration `14ae6ce` |
| `semantic/store.rs` | W0.1 repair | `agent/w0-s2a-members` | `e867a88` | relation-observed identity sets and changed-write invalidation only; no unrelated store API work | expired at reviewed integration `14ae6ce` |
| `semantic/generic_calls.rs` | W0.2 | `agent/s3-generic-calls` | `75abbf5` | frozen lazy checked-shell/demand/recovery rewrite only | pending reviewed S3 generic-call integration |
| `semantic/relater.rs` | W0.2 | `agent/s2-readonly-properties` | `75abbf5` | readonly property strict-subtype branch and its focused tests only | expired at reviewed integration `d4719b3` |

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
- S2a proves inherited property order, missing-property diagnostics and related
  information, inherited reads, cold/warm identity, exact observed-dependency
  invalidation, poison/foreign rejection, cycle safety, retained readonly
  syntax, and pinned readonly strict-subtype directionality. A future public
  strict-subtype query adapter and forced replay remain test-hardening debt,
  not missing leaf semantics.
- S3 proves Composite-versus-Merged behavior, no-op identity, cache-before-
  counter ordering, depth/count boundaries, active-mapper recursion, and
  query-local reset.
- Every stack receives a Go-semantic review and a separate Rust-invariant
  review before serial integration.
- Root runs focused public tests, production-library check, strict focused
  Clippy, rustdoc, and the fixed scorecard after integration. On the current
  1 GiB machine, checker-wide `cargo check --tests` and all-target Clippy enter
  the giant unit-test crate and are killed by the cgroup; the focused public
  binaries are therefore the executable behavior gate, while all-target
  compilation remains a tracked infrastructure limit rather than a claimed
  success.
