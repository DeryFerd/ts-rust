# Typechecker integration status

- Status: active
- Started: 2026-07-16
- Updated: 2026-08-22
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Wave branch baseline: `cdbf749`
- Integration branch: `july-ultra`
- Latest measured integration checkpoint: `d97e5de` with uncommitted fixes

This file records progress after the initial Wave 0 of
[`typechecker-completion-goal.md`](typechecker-completion-goal.md). The port
map remains authoritative for cluster state.

## Current checkpoint

The latest focused package runs pass these unit-test suites:

| Package | Passing unit tests |
|---|---:|
| `ts_parser` | 189 |
| `ts_binder` | 174 |
| `ts_checker` | 1,226 |
| `ts_compiler` | 159 |
| `ts_printer` | 564 |

The parser also reads all 108 bundled declaration libraries without
diagnostics. The checked-in fixture manifests contain 96 smoke variants and
512 milestone variants.

Run the focused suites with:

```sh
for package in ts_parser ts_binder ts_checker ts_compiler ts_printer; do
  ./scripts/run-cargo-capped.sh test -p "$package" --lib
done
./scripts/run-cargo-capped.sh test -p ts_parser --test bundled_libs
```

The latest recorded smoke scorecard is
`/tmp/ts-rust-type-node-zero-fatal-scorecard.json`. Its provenance records
commit `d97e5de` with a dirty worktree. The 96 selected variants contain 95
executed variants and one upstream skip. Of the executed variants, 14 match
exactly and 81 stop at typed unsupported boundaries. No fatal invariant occurs.

Regenerate the fixed smoke scorecard with:

```sh
TS_GO_REPO=/path/to/typescript-go \
  ./scripts/run-cargo-capped.sh run -p ts_fixture --bin ts_fixture_baseline -- \
  --diagnostics \
  --canonical-checker \
  --variant-manifest tools/ts_fixture/manifests/checker-smoke-v1.json \
  --scorecard-json /tmp/ts-rust-type-node-zero-fatal-scorecard.json
```

Production `get_type_at_location` and `get_symbol_at_location` queries now
provide `.types` and `.symbols` fixture artifacts. Mapped, conditional, and
template types, JSX, JavaScript, and JSDoc each have implemented checker code
and focused tests. Their complete upstream coverage remains unverified.

A complete 512-variant run, complete upstream corpus parity, and the final
workspace verification are not established by this checkpoint.

## Earlier lane history

| Lane | Branch/worktree | Current task | State |
|---|---|---|---|
| Root/integration | `july-ultra`; repository root | contract adapters, review, serial verification | integrated checkpoint `d97e5de`; root owns Cargo, shared checker contracts, commits, and fixture scoring |
| M0 | `july-ultra`; repository root | deterministic checker scoring | schema-5 provenance, retained fatal outcomes, 96-variant smoke selection, 512-variant milestone selection, and semantic fixture artifacts are present |
| S2a | `july-ultra`; repository root | exact single-base interface heritage and relation-cache observation | integrated through `14ae6ce`; two exact-tip reviews found no P0/P1 issue, all five public heritage tests pass, and the fixed shard advances one interface fixture without an exact loss |
| S2 readonly follow-up | `july-ultra`; repository root | readonly property retention and strict-subtype directionality | integrated through `d4719b3`; two independent reviews found no P0/P1 issue, the public production target passes, focused strict Clippy is green, and the fixed shard is semantically unchanged |
| S3 session/generic calls | `july-ultra`; repository root | lazy checked shells, shared query sessions, exact demand/recovery, and TS2589 | integrated through `010d93a`; the library check and focused `source_generic_calls`/`source_instantiation_limits` targets pass, and independent review found no remaining P0/P1 issue |
| S1b | `july-ultra`; repository root | named ESM imports and two-hop renamed/type-only reexports | integrated through `6c3bf97`; 17 focused import/reexport public tests pass, sparse immediate-link timing matches pinned `resolveAlias`, warm alias/type-only/value poison is rejected, and independent review approved the slice |
| W1 S5 | `july-ultra`; repository root | nongeneric `keyof`/property-key algebra | integrated through `c5c3cf9` plus cache hardening `7d97c9a`; direct and parenthesized property/index literals, nongeneric interfaces, exact `propertiesTypes` timing, eager Index origins, symbolic display, interface index publication, and cold/warm source identity pass independent review |
| W1 S6 | `july-ultra`; repository root | direct explicit generic class/interface reference shells | integrated through `8132af9` with compiler classification `a478f13`; local full-arity class/interface references reuse target caches mapper-free/session-free, publish exact node/symbol links, and recover with pinned TS2314/TS2315 diagnostics |
| W1 S2b | `july-ultra`; repository root | exact two-way union property synthesis and declared source reads | integrated through `26346f5` plus cleanup `6974fb4`; direct reads over two declared type-literal unions reuse exact synthetic members, emit pinned TS2339/TS2551 details and spelling suggestions, preserve first-missing provenance, reject apparent-Object/comparator-dependent cases before publication, and pass independent review |
| W1 S4b | `july-ultra`; repository root | direct scalar conditional initializers | integrated through `afb36f8`; boolean and ordinary scalar truthiness, branch-order joins, fixed/bootstrap and freshly allocated union identities, whole-source preflight, poison rejection, and forced warm replay pass the focused production gate and independent oracle review |
| W1 S11a | `july-ultra`; repository root | primitive class declarations through source/compiler | integrated through `b909237` with classifier repair `1ad5689`; local named nongeneric/no-heritage classes install exact instance/static member graphs and a default construct signature at lexical source positions, whole-file preflight rejects unsafe or poisoned later classes before earlier publication, exported/anonymous classes remain typed boundaries, and independent review found no remaining P0/P1 issue |
| W1 S11a heritage | `july-ultra`; repository root | one exact direct local nongeneric base class plus class relations | integrated through `673bd70`; pinned owner/base instance/value provenance, own-first instance/static composition, distinct resolved member tables, derived default construction, exact class relation admission, and warm poison/cache-masking gates pass public tests and independent review |
| W1 S11b default construction | `july-ultra`; repository root | direct zero-argument `new Model()` | integrated through `67d072d`; source execution consumes the canonical class construct signature, publishes exact constructor/symbol/signature/result links through a whole-plan validate/reserve/ensure phase, and retains arguments, type arguments, missing parentheses, aliases, forward classes, abstract/explicit constructors, heritage, and optional chaining as typed boundaries |
| W1 A16 | `july-ultra`; repository root | first direct nongeneric intersection kernel, source bridge, relations, and display | integrated through `01f8ea7` with compiler classification/gates in `1bbe265`; ordered identity, flattening/deduplication, required primitive/literal property synthesis, discriminant-never reduction, exact relation ordering, source consumption, display, and cold/warm/poison behavior passed focused gates and independent P0/P1 review |
| W1 A16 optional/composite follow-up | `july-ultra`; repository root | optional properties and recursive source-owned property-object types | integrated through `3b1b713` with compiler coverage in `365da82`; pinned optional/readonly merge rules, recursively validated local composite property objects, optional-discriminant reduction, warm replay, and fail-closed boundaries passed focused gates and independent P0/P1 review |
| W1 ambient functions | `july-ultra`; repository root | exact singleton nongeneric `declare function` declarations | integrated through `74ea3ca`; script/external-module hoisting, canonical callable/signature identity, optional parameters, TS2345, whole-source atomicity, warm replay, and typed generic/overload/export/`.d.ts` boundaries passed checker/compiler gates and independent P0/P1 review |
| W1 ambient generic follow-up | `july-ultra`; repository root | exact singleton generic ambient functions and strict top-level direct call statements | integrated through `693d0be`; generic constraints/defaults, inference/explicit arguments, exact TS2558/TS2344/TS2345 ranges, hoisting, whole-plan atomicity, and warm replay passed focused/adjacent/compiler/strict-Clippy gates and independent P0/P1 review |
| W1 ambient overload follow-up | `july-ultra`; repository root | exact local nongeneric ambient overload families | integrated through `290afc9`; ordered arbitrary-length signature groups, literal-first selection, complete reverse provenance, cross-provider preflight, warm poison rejection, and fail-closed recovery passed six public checker tests, two compiler tests, strict Clippy, and independent P0/P1 review |
| W1 class-source heritage | `july-ultra`; repository root | class heritage, constructors, and initialization | class constructor and initialization work is integrated through `96c9a02`; broader class coverage remains incomplete |
| W1 generic interface members | `july-ultra`; repository root | concrete generic-interface member instantiation | generic member instantiation and source checking are integrated through `5788e18` and `3e47a08` |
| W1 review/oracle | rotating read-only lanes | pinned behavior, cache timing, and adversarial fixtures | historical lane assignments ended; current fixture results appear in the checkpoint above |

The earlier S5/S6 sub-wave used four agents. The current session permits more
agents, provided that each implementation lane owns different files. Root
continues to serialize Cargo commands, commits, shared checker contracts, and
fixture scoring.

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

The integrated S5/S6 stack through `7d97c9a` has raw fixed-shard digest
`4b87094f4e8a53b8e63689086aebcba2`. Removing Rust and invocation provenance
with the established sorted normalization again produces
`353dddd39af6749db775683da54d7c9a`, byte-identical to the `6c3bf97` semantic
scorecard. The shard still reports four exact variants, 90 typed capability
boundaries, two supported mismatches, and zero fatal invariants.

The integrated S2b/S4b/S11a-shell stack through `d443d1b` has raw fixed-shard
digest `514c967f1737901d80dbdd5af119cfb0`. Removing the Rust provenance object and
invocation provenance produces `353dddd39af6749db775683da54d7c9a` again. The
96 variants remain four exact, 90 typed capability boundaries, two supported
mismatches, and zero fatal invariants. At that checkpoint, the focused public
checker surface was 81 tests across 29 independently runnable targets.

The declared-union read and primitive-class source stack through `1ad5689` has
raw fixed-shard digest `b9bd4de812f8b438af1baa9c7aae15d9`. The first run
at `b909237` exposed one honest integration bug: an anonymous decorated class
was classified as `INV.SOURCE.CLASS`. `1ad5689` moves the missing-name check
ahead of semantic class planning, adds checker/compiler regressions, and the
rerun returns to zero fatal invariants. The headline remains four exact
variants, 90 typed capability boundaries, and two supported mismatches. Its
provenance-normalized digest is `c3dd4beaec5aae1377c60e50e7871d6f`:
15 fixed-shard frontier records changed from `d443d1b`, all retaining the same
typed capability code and comparison status. One fixture,
`checkInheritedProperty.ts`, now advances past its first class declaration to
the next unsupported `declare` modifier; the other 14 expose a more specific
class-family boundary. There are no exact losses. The focused public checker
surface is now 94 tests across 31 independently runnable targets.

The direct-class-heritage and default-construction stack through `67d072d` has
raw fixed-shard digest `1212729ae8f5ba7979ca16ea928dccb1`. Removing only
Rust commit/dirty and invocation provenance produces
`c3dd4beaec5aae1377c60e50e7871d6f`, byte-identical to `1ad5689`: the shard
remains four exact variants, 90 typed capability boundaries, two supported
mismatches, and zero fatal invariants, with no frontier-record change. Five
public direct-heritage tests and three public default-construction tests raise
the focused checker surface to 102 tests across 33 independently runnable
targets. Both leaves passed focused strict Clippy and independent P0/P1 review.

The ambient-variable, direct-intersection, and singleton-ambient-function stack
through `74ea3ca` has raw fixed-shard digest
`5f0cb46a0a4222d821a08e1df2190b33`. Removing only Rust commit/dirty and
invocation provenance produces `95cbefd8e0b7555007cad37877c4db03`.
The shard remains four exact variants, 90 typed capability boundaries, two
supported mismatches, and zero fatal invariants. Relative to the ambient-
variable checkpoint, exactly five frontier records change and every change is
forward-only: `freshObjectLiteralSubtype.ts` and
`exactOptionalPropertyTypesArgumentError.ts` advance through the admitted
nongeneric ambient declaration; `inferenceWithNeverSource1.ts` and
`typeArgumentArityErrorSkipsTrivia.ts` reach the intentional generic callable
boundary; and `ambiguousOverloadResolution.ts` reaches the intentional merged-
overload boundary. There are no status changes or exact losses. The focused
public checker surface is now 111 tests across 36 independently runnable
targets. Both new semantic leaves passed strict focused Clippy, compiler gates,
and independent P0/P1 review.

The optional/composite-intersection and generic-ambient-function stack through
`693d0be` has raw fixed-shard digest
`16a26f90058c7b7090a3f0462f10daf6`. Removing only Rust commit/dirty and
invocation provenance produces `beab382c4f923f0d393b4abd0a61d4bb`.
The shard advances `typeArgumentArityErrorSkipsTrivia.ts` from the generic
ambient callable boundary to an exact two-diagnostic TS2558 match, leaving five
exact variants, 89 typed capability boundaries, two supported mismatches, and
zero fatal invariants. Exactly two other records change:
`moduleKeywordSkipLibCheck.ts` and
`exactOptionalPropertyTypesArgumentError.ts` move only from the old assignment-
fallback spelling to the new direct-call boundary; neither changes status or
capability class. No other record changes, and the intersection extension
changes no fixed-shard record. The focused public checker surface is now 121
tests across 38 independently runnable targets. The combined integration gate
ran 77 checker tests, eight compiler tests, the checker library check,
and strict focused Clippy.

The local ambient-overload stack through `290afc9` has raw fixed-shard digest
`9aaab16ed4d80a594c2686c2494d907b`. Removing only Rust commit/dirty and
invocation provenance produces `616f256f9ec771ae7eefa3324e52faa7`.
The shard remains five exact variants, 89 typed capability boundaries, two
supported mismatches, and zero fatal invariants. Exactly one record changes:
`ambiguousOverloadResolution.ts` advances from the merged-function boundary
to the next honest boundary, the direct heritage on `class B`. No status,
diagnostic, or exact-match record regresses. The focused public checker surface
is now 127 tests across 39 independently runnable targets; the semantic module
count is 66 and the retained semantic unit-test count is 1,026.

At the historical `290afc9` checkpoint, the frontier was five exact variants,
89 typed capability boundaries, two supported mismatches, and zero fatal
invariants. The current checkpoint above supersedes those results. The runner
discovers 12,750 upstream cases, but the fixed smoke selection is not a claim
of complete corpus coverage.

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
- Root runs focused public tests, the production-library check, strict Clippy,
  rustdoc, and the fixed scorecard after integration. The capped Cargo runner
  now allows up to 8 GiB by default when sufficient memory is available. Set
  `TS_CARGO_MEMORY_LIMIT_KIB` to adjust the limit. Cargo commands remain
  serialized across agent worktrees.
