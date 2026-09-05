# Goal: complete typescript-go core typechecking in Rust

Current execution rules are in [accountability](typechecker-accountability.md),
[saved state](typechecker-accountability-state.json) and the
[September 5 reset plan](typechecker-reset-plan.md). The active status and
scheduling below are historical. They do not override the current pause or
authorize more feature branches. Full port requirements remain in force.

- Status: active; execution approved
- Plan date: 2026-07-16
- Integration branch: `july-ultra`
- Planning baseline: `ded5eaa`
- Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`
- Primary outcome: accurate checking of real-world modern TypeScript projects

## Executive decision

The remaining port is highly parallelizable, but it is not embarrassingly
parallel. Approximately 65-75% of the engineering is a post-contract
parallelization target once work is divided by semantic leaf rather than by
failing fixture. Before the member/instantiation, location-query, and source
dispatch contracts land, current executable concurrency is closer to two
semantic writer lanes plus measurement and review. The eventual remaining
25-35% is deliberately serialized because it changes shared type identity,
lazy cache publication, relation behavior, source dispatch, or compiler
classification.

The default topology is therefore:

- one integration owner for shared checker contracts, Cargo, corpus scoring,
  and merge order;
- multiple leaf owners working in isolated worktrees on non-overlapping
  semantic modules;
- independent typescript-go and Rust-invariant reviewers; and
- a fixer/oracle lane that turns review and corpus output into bounded queues.

The current session supports more than four agents. Keep one integration owner
and give each implementation agent exclusive ownership of specific files. Use
additional agents for upstream audits, focused reviews, fixture analysis, and
independent compiler subsystems. Serialize Cargo commands, commits, and edits
to shared checker contracts. Increase the number of implementation lanes only
when their ownership does not overlap.

The implementation strategy is a faithful port of coherent typescript-go
algorithms. Preserve recognizable upstream structure and behavior first;
refactor toward more idiomatic Rust only after parity. Do not create fixture
special cases, silent `any`/`unknown` fallbacks, placeholder successes, or a
mixed old/new semantic graph.

## Goal statement

For the frozen upstream epoch, `ts-rust` will:

1. Build one program-wide canonical graph of nodes, symbols, types, signatures,
   mappers, aliases, and flow nodes.
2. Check ordinary `.ts` and `.d.ts` programs with the same type identities,
   relations, inference, overload selection, control-flow narrowing, and
   diagnostics as typescript-go.
3. Support the module, class, generic, utility-type, and control-flow patterns
   used by modern strict TypeScript projects.
4. Produce exact `.errors.txt`, `.types`, and `.symbols` artifacts for the
   claimed support ring.
5. Expand through TSX, NodeNext/package semantics, JavaScript/JSDoc, and the
   complete compiler/conformance corpus without introducing a second checker
   architecture.
6. Complete one controlled upstream roll-forward after frozen-epoch parity.

Typechecking is the critical path. General JavaScript emit, complete declaration
emit, transforms, watch/build mode, fourslash, and language-service parity are
outside this goal except where a checker query or artifact is required to prove
semantic correctness.

“Frozen-epoch parity” below means every pinned configuration is discovered and
accounted for, and every checker-relevant variant has exact `.errors`, `.types`,
and `.symbols` artifacts. Emit-only artifacts remain visible as explicitly
out-of-scope; JavaScript or declaration emit equality is not a completion gate
for this goal. A configuration may not be labeled semantically exact merely
because its only expected artifact is out of scope.

## Why this plan follows the Bun rewrite model

Jarred Sumner's [Bun Rust rewrite account](https://bun.com/blog/bun-in-rust)
provides the right operating model for a large AI-assisted port:

- use the original language-independent test suite as the behavioral oracle;
- port mechanically with minimal simultaneous architectural change;
- write down source-to-target conventions before multiplying workers;
- isolate work in a small number of worktrees;
- use a separate implementer, adversarial reviewer, and fixer loop;
- turn compiler errors and test failures into explicit work queues;
- prevent workers from racing through shared Git or build state;
- reject stubs and workarounds whose purpose is only to make the build green;
  and
- verify that tests are truly executing and are not skipped before claiming
  parity.

This repository needs one adaptation. Bun could mechanically translate a broad
file surface and repair it later. TypeScript's checker is a highly connected
lazy graph, so independently translated files are not useful unless they share
exact identity, publication, and recursion contracts. Our unit of parallelism
is therefore an upstream semantic cluster behind an opaque Rust leaf API, not
an arbitrary source file.

The tuple, indexed-access, and `typeof` flow work validated this model. Separate
workers produced bounded leaves and reviews while root integrated shared
dispatch. Adversarial review found three `typeof` bugs that compiled and passed
the original production test: loss of broad-object identity at a join, the same
loss for a leading local, and incorrect `void` narrowing. All were repaired
before the slice was declared complete.

## Where the port is now

### Working foundation

The hard substrate is present and useful:

- program-branded node, file, flow, symbol, type, signature, mapper, and link
  identities;
- canonical binder declaration graphs, name resolution, aliases, and a broad
  CFG construction prefix;
- the complete `TypeData` representation and all checker LinkStores;
- intrinsic and global bootstrap, literal and union caches, and canonical
  global Array/Object/Function identities;
- declared type parameters, classes/interfaces as identities, aliases, direct
  generics, arrays, property objects, function types, unions, tuples, and a
  concrete indexed-access leaf;
- primitive, literal, property-object, function, array, and bounded structured
  relations;
- bounded instantiation, constraints, generic inference, contextual typing,
  calls, overload sets, source expressions, imports, and diagnostics;
- transactional source checking for a useful but narrow set of variables,
  functions, assignments, calls, properties, operators, enums, and ESM
  imports; and
- invocation-local truthiness and strict `typeof` flow with two-arm joins.

Recent integrated verticals include canonical tuple annotations, concrete
inline indexed access, property objects in unions, all eight strict `typeof`
tags, reversed comparisons, object/function classification, `void` projection,
and base/local join identity restoration.

### Execution checkpoint: 2026-08-27

The current saved semantic smoke records clean Rust commit `8357dac3` and
51 exact results in 95 executed variants. The remaining results are 43
unsupported and one artifact mismatch, with no fatal invariants. See the
[checkpoint table](#quantitative-posture) for artifact counts and evidence.

The retained 397/511 milestone is diagnostic-only and records clean `74fd417a`,
not `8357dac3`. Full verification of `8357dac3`, a semantic milestone at that
commit, complete upstream corpus parity, and a modern-project parity ring
remain unproved. The full port goal remains active.

### Earlier wave 131 checkpoint: 2026-08-27

Wave 131 passes all 6,239 workspace tests. Strict workspace Clippy passes after
one test-only lint fix. The fixed semantic report has 48 exact results in 95
executed variants, one more than wave 128. The diagnostic-only milestone
retains all 397 exact results in 511 executed variants. Neither report lost an
exact result or produced a fatal invariant.

JSDoc callback alias identity, mode-aware module targets, dependency-ordered
source checking, retained config and resolver inputs, and exact project error
rendering are integrated. Approved input-preparation scripts for all seven
projects are also included. The remaining semantic outcomes are 46 unsupported
variants and one artifact mismatch. No modern-project parity ring is claimed.

See [`typechecker-wave131-status.md`](typechecker-wave131-status.md) for runtime
checkpoint `74fd417a`, test-only follow-up `4705d079`, script evidence, and the
remaining work. The full port goal remains active.

### Earlier wave 128 checkpoint: 2026-08-26

Wave 128 passes all 6,173 workspace tests. Strict workspace Clippy passes after
the lint-only follow-up. The fixed semantic report has 47 exact results in 95
executed variants, seven more than wave 127. The diagnostic-only milestone
retains all 397 exact results in 511 executed variants. Neither report lost an
exact result or produced a fatal invariant.

Canonical library ordering, lazy module values, enum declaration queries,
owned project graph observations, and source replay are integrated. The
remaining semantic outcomes are 46 unsupported variants and two artifact
mismatches. Prepared project inputs and Go probes remain separate evidence,
not a passing project ring.

See [`typechecker-wave128-status.md`](typechecker-wave128-status.md) for runtime
checkpoint `df2ba7bc`, lint follow-up `f07dc2f1`, and the verification details.
The full port goal remains active.

### Earlier wave 127 checkpoint: 2026-08-26

Wave 127 passes all 6,105 workspace tests and strict workspace Clippy. The fixed
semantic report has 40 exact results in 95 executed variants, three more than
wave 126. The diagnostics-only milestone retains 397 exact results in 511
executed variants. Neither report lost an exact result or produced a fatal
invariant. The remaining semantic outcomes are 50 unsupported variants and five
artifact mismatches.

The opt-in canonical project CLI and the reviewed modern-project input
inventory are integrated. The inventory contains five core repositories with
224,500 non-generated TypeScript code lines. Dependency graphs, exact Go
artifacts, forced replay, and performance evidence remain incomplete.

See [`typechecker-wave127-status.md`](typechecker-wave127-status.md) for the
runtime checkpoint `ed33229a`, lint-only follow-up `4a6f52fe`, evidence, and held
iterator and project-runner work. The full port goal remains active.

### Earlier wave 126 checkpoint: 2026-08-26

Code checkpoint `c440602d` passes all 6,001 workspace tests and strict Clippy
for all targets. The semantic smoke report has 37 exact results in 95 executed
variants, five more than wave 125. The diagnostics-only milestone has 397
exact results in 511 executed variants, two more than wave 125. Neither report
lost an exact match or produced a fatal invariant.

Semantic smoke still has 50 unsupported variants and eight artifact
mismatches. Two previously blocked queries now expose existing display gaps.
Full upstream semantic parity and the modern-project rings remain incomplete.

See [`typechecker-wave126-status.md`](typechecker-wave126-status.md) for the
verified code, evidence, separate branches, and build rules.

### Earlier wave 125 checkpoint: 2026-08-26

Code checkpoint `5e2f9e37` passes the full repository verification script.
The semantic smoke report has 32 exact results in 95 executed variants, eight
more than the previous batch, with no exact losses or fatal invariants. The
diagnostics-only milestone retains 395 exact results in 511 executed variants.
Neither result establishes complete upstream semantic parity.

See [`typechecker-wave125-status.md`](typechecker-wave125-status.md) for the
evidence, prepared branches, and required per-worktree build directories.
The older figures below remain as execution history.

### Earlier checkpoint: 2026-08-22

At this historical checkpoint, focused package runs passed 189 parser unit
tests, 174 binder unit tests, 1,226 checker unit tests, 159 compiler unit tests,
and 564 printer unit tests. The parser also accepted all 108 bundled declaration
libraries without diagnostics.

Both fixed checker manifests are present. The smoke manifest contains 96
variants, and the milestone manifest contains 512 variants. The August 22 smoke
scorecard recorded commit `d97e5de` with uncommitted fixes. Of its 96 selected
variants, 95 execute and one is skipped by upstream. The executed variants
produce 14 exact matches, 81 typed unsupported outcomes, and no fatal
invariants.

Production location queries and fixture walkers generate `.types` and
`.symbols` artifacts. Mapped, conditional, and template types, JSX, JavaScript,
and JSDoc now have production checker implementations and focused tests.
Complete support for those features remains in progress.

That historical scorecard is
`/tmp/ts-rust-type-node-zero-fatal-scorecard.json`. A completed run of the
512-variant milestone, complete upstream corpus parity, and the final workspace
verification were unverified at that checkpoint.

### Earlier implementation checkpoints

At the July 17 checkpoint, the fixed 96-variant smoke lane produced five exact
variants, 89 typed capability boundaries, two supported mismatches, and zero
fatal invariants. S2a's exact one-base interface heritage and relation-cache
invalidation are integrated through `14ae6ce`. All five public heritage
scenarios pass, and the fixed shard advances one interface fixture to its next
unsupported property boundary. The recovering S3 instantiation session is
integrated through `75abbf5`. Its fixed shard is semantically byte-identical to
the S2a run after removing only commit and invocation provenance. The bounded
readonly-property follow-up is integrated through `d4719b3`: source properties
retain exact readonly state, direct heritage preserves it, strict subtype is
ordered readonly-to-mutable exactly as upstream, ordinary assignability remains
symmetric, and changed observed bits invalidate warmed relations. Its public
target and focused strict Clippy pass, and its fixed shard is semantically
byte-identical to `75abbf5`.

The recovering lazy-generic vertical is now integrated through `010d93a`,
including query-owned sessions in source calls, assignment diagnostics, and
import preparation; atomic mapper-shell preflight; nested generic arrays; and a
public TS2589/limit oracle. Named ESM reexports are integrated through
`6c3bf97`: two-hop renamed value/function barrels, transitive type-only markers,
separate immediate/final alias identities, pinned lazy immediate-cache timing,
and fail-closed warm-chain validation all pass focused public tests and
independent review. Both stacks are semantically byte-identical to the frozen
96-variant baseline after removing only commit/invocation provenance.

The first Wave 1 S5/S6 sub-wave is integrated through `7d97c9a`. Nongeneric
`keyof` now resolves direct and parenthesized property/index literals plus
nongeneric interfaces with exact `propertiesTypes` timing, eager `IndexType`
origins, symbolic display, and fail-closed warm validation. Direct full-arity
local generic class/interface references now reuse the target-owned
instantiation cache without creating mappers or consuming instantiation
sessions, with pinned TS2314/TS2315 recovery. The focused public targets and
the adjacent indexed-access, index-signature, heritage, tuple, generic-call,
import, and reexport targets pass. The fixed 96-variant shard remains four
exact, 90 typed capability boundaries, two supported mismatches, and zero
fatal invariants; its established provenance-normalized digest remains
`353dddd39af6749db775683da54d7c9a`.

The next Wave 1 cut is integrated through `d443d1b`. Exact two-way union
property synthesis now has a declared type-literal production adapter with
source declaration/owner provenance, partial-member caching, a freshly
allocated `string | bigint` public gate, and allocation-free warm validation.
Direct nongeneric interface references can now participate in canonical union
type nodes, while the member leaf still rejects interfaces and mixed modes
before writes. Direct scalar conditional initializers are whole-source
preflighted and replay exactly, and the first nongeneric/no-heritage class
instance/value shells are installed with canonical no-base state. Independent
review found no P0/P1 issue in the union and conditional cuts. The frozen
96-variant shard remains four exact, 90 typed capability boundaries, two
supported mismatches, and zero fatal invariants; its provenance-normalized
digest is still `353dddd39af6749db775683da54d7c9a`.

The following source-facing cut is integrated through `1ad5689`. Direct
property reads over exact two-member declared type-literal unions now execute
through the ordinary source dispatcher with pinned synthetic-member identity,
TS2339/TS2551 diagnostics, first-missing constituent detail, spelling
suggestions, warm replay, and fail-closed apparent-Object/comparator handling.
Nongeneric/no-heritage classes with primitive annotated fields now execute at
their lexical source positions, publish exact instance/static member graphs
and the canonical default construct signature, and are admitted through the
compiler adapter. Whole-file planning validates every later class before an
earlier class can publish; exported, anonymous, unsafe-initialization, and
unsupported member families remain typed capability boundaries. Independent
review found no remaining P0/P1 issue. A fixed-shard run caught one anonymous
class invariant classification after initial integration; `1ad5689` repairs it
and the full rerun has four exact variants, 90 typed capability boundaries, two
supported mismatches, and zero fatal invariants. The normalized digest changes
to `c3dd4beaec5aae1377c60e50e7871d6f` solely because 15 frontier details move
within the same capability/status classes; there are no exact losses.

The next class composition cut is integrated through `67d072d`. One exact
direct non-alias source-owned nongeneric base class now contributes pinned
base instance/value identities, own-first inherited instance/static surfaces,
distinct resolved member tables, a derived-return default construct signature,
and fail-closed class-only structural relations. Direct top-level
`new Model()` for a preceding admitted no-base class now consumes that same
canonical construct graph and publishes exact constructor symbol/static type,
selected signature, result type, and variable/property identities through a
whole-plan validate/reserve/ensure transaction. Arguments, type arguments,
missing parentheses, aliases, forward classes, abstract or explicit
constructors, heritage construction, optional chaining, and broader class
families remain typed boundaries. Both leaves passed focused public gates,
strict Clippy, and independent review with no remaining P0/P1 issue. The fixed
96-variant shard is semantically byte-identical to `1ad5689` after provenance
normalization: four exact, 90 typed capability boundaries, two supported
mismatches, and zero fatal invariants.

The next type-algebra/source-declaration cut is integrated through `74ea3ca`.
Direct nongeneric intersections now preserve ordered raw identity, flatten and
deduplicate nested constituents, synthesize required primitive/literal property
surfaces, reduce conflicting discriminants to `never`, format symbolically, and
participate in pinned identity/assignability/comparability ordering with excess-
property and weak-target checks before decomposition. Exact direct nonexported
singleton `declare function` declarations in ordinary `.ts` now reuse the
canonical source-callable graph, hoist before lexical calls, retain one owner/
type/signature identity, accept the existing supported annotated parameter
surface, and never enter body or inferred-return execution. Both leaves are
fail-closed at optional/composite intersection properties and generic/merged/
exported/declaration-file ambient functions respectively. Checker/compiler
gates, strict focused Clippy, and independent reviews found no P0/P1 blocker.
The fixed shard remains four exact, 90 typed capability boundaries, two
supported mismatches, and zero fatal invariants; exactly five ambient-function
frontiers advance without a status or exact loss.

The follow-up cut is integrated through `693d0be`. Direct intersections now
merge optional and readonly state with pinned all-contributor rules, retain
borrowed unique-property provenance, admit recursively validated local
nongeneric property-object graphs, and keep conflicting optional discriminants
as optional `never` properties instead of reducing the whole intersection.
Generic singleton ambient functions now reuse the ordered generic-signature
engine for constraints, defaults, inference, explicit type arguments, and exact
TS2558/TS2344/TS2345 diagnostics. A strict top-level direct-identifier call
statement leaf lets those declarations execute in the same source forms as the
pinned fixtures while preserving whole-source preflight and warm replay. Both
leaves passed independent P0/P1 review, 77 combined checker tests, eight
compiler tests, library checking, and strict focused Clippy. The fixed shard
has raw digest `16a26f90058c7b7090a3f0462f10daf6` and provenance-
normalized digest `beab382c4f923f0d393b4abd0a61d4bb`. Its only status
change advances `typeArgumentArityErrorSkipsTrivia.ts` to an exact match; only
`moduleKeywordSkipLibCheck.ts` and
`exactOptionalPropertyTypesArgumentError.ts` otherwise change, both from the
old assignment-fallback spelling to the direct-call boundary. The result is
five exact variants, 89 typed capability boundaries, two supported mismatches,
and zero fatal invariants.

The four-slot topology has rotated into local ambient overload families plus a
direct class-heritage source adapter and a property-only generic-interface
member kernel, with an adversarial review slot and root retaining shared store,
compiler, formatter, build, and scoring ownership. The class-field and
uninitialized-variable leaves remain serialized behind the heritage adapter
because the pinned overload fixture encounters those boundaries in that order.
The live commit/worktree ledger is
[`typechecker-wave0-status.md`](typechecker-wave0-status.md).

The ambient-overload cut is integrated through `290afc9`. Arbitrary-length
local nongeneric `declare function` groups retain source order, one canonical
callable object, exact owner/declaration/signature reverse maps, optional/minimum
arity, literal-specialized candidate ordering, and the existing subtype-then-
assignable resolver. Whole-source preflight now covers singleton functions,
direct arrows, and contextual-arrow target closures before any overload group
publishes. Two independent cache findings—callable-union dirtiness and retained
signature literal flags—plus a cross-provider atomicity finding were repaired
before integration. Six public checker tests, two compiler tests, the library
check, strict focused Clippy, and independent P0/P1 review pass. The fixed shard
has raw digest `9aaab16ed4d80a594c2686c2494d907b` and provenance-normalized
digest `616f256f9ec771ae7eefa3324e52faa7`; its sole semantic delta is
`ambiguousOverloadResolution.ts` advancing from the merged-function boundary
to direct class heritage, with the headline unchanged at five exact, 89 typed
capability boundaries, two supported mismatches, and zero fatal invariants.

### Quantitative posture

The semantic smoke records clean Rust source
`8357dac34c37b4a4f24b210a4ddafb76310bfaec` and clean upstream source
`dc37b5249ab60e2bbce936f71b883e6c8136167e`.

| Evidence | Recorded result | Scope |
|---|---|---|
| Smoke selection | 96 selected, 95 executed, one upstream skip | Fixed `checker-smoke-v1` selection |
| Smoke outcomes | 51 exact, 43 unsupported, one artifact mismatch, zero fatal | Not full-corpus parity |
| Unsupported outcomes | 28 checker capabilities, 15 harness/configuration errors | Neither category counts as success |
| Smoke `.types` | 89 expected, 46 exact, one mismatch, 15 unsupported, 27 not reached | Production semantic artifact comparison |
| Smoke `.symbols` | 89 expected, 54 exact, seven mismatches, one unsupported, 27 not reached | Secondary mismatches also remain failures |
| Retained diagnostic-only milestone | 512 selected, 511 executed, one upstream skip, 397 exact, 114 unsupported, zero fatal | Clean `74fd417a`, not `8357dac3`. No type or symbol comparison |
| Wave 137 check log | Dev check finished with 18 library warnings and one library-test warning | No source SHA in the log. Not full-test or strict-lint proof |
| Full `8357dac3` verification | Unproved | Full tests, strict Clippy, rustdoc, and a semantic milestone need checkpoint-bound records |
| Port-map clusters | 46 | Unchanged: 11 verified, 30 porting, and five blocked |

Saved runtime evidence paths are relative to the main workspace:

- Semantic smoke: `target/wave137-combined-semantic-smoke.json`.
  SHA-256: `927cf97cb834c87da2fb2b3290f7438eea9de87da3a7e8f7b81e739782499d7a`.
- Diagnostic-only milestone: `target/wave131-combined-milestone.json`, Rust SHA
  `74fd417aab1365618db7d7d668e01a7d82294215`.
  SHA-256: `dbe23396ff1571c9b00e02532da64e4e5b64fd6e59449fa69f43726372cb2054`.
- Check log: `target/wave137-combined-check.log`.

The implementation is no longer bottlenecked on basic representation. It is
bottlenecked on semantic breadth behind intentionally fail-closed gates.

### Current measurement is a frontier, not coverage

The semantic smoke in the checkpoint table discovers 12,750 upstream cases.
Discovery does not prove execution of every option configuration. Only exact
variants count as success. Advancing an unsupported variant to a later
unsupported boundary is not an exact win.

The retained milestone compares diagnostic artifacts only. Its invocation has
no `--semantic-artifacts`, and `semanticArtifacts` is null. Its `full_artifact`
label does not establish `.types` or `.symbols` parity. A semantic milestone
at `8357dac3` and complete upstream corpus parity remain unverified.
Historical first-50 and 500-case runs predate this checkpoint and are not its
failure totals.

The historical first blockers were dominated by:

| First blocker family | Variants in the old 500-case run |
|---|---:|
| JS/JSX/TSX/JSON source kind | 105 |
| Class declarations | 79 |
| Function declarations/bodies | 69 |
| Variable inference and bindings | 55 |
| Other source syntax | 46 |
| Namespaces/modules | 32 |
| Interfaces | 29 |
| Import-equals | 28 |
| Declaration-file admission | 24 |
| Imports/exports | 19 |
| Enums | 19 |
| Module-mode facts | 19 |

These counts understate relations, instantiation, inference, and advanced
types because the runner exposes only the first boundary in each variant.

### Largest semantic gaps

1. General member resolution and structural relations across interfaces,
   signatures, indexes, heritage, instantiated objects, and classes.
2. Reusable mapper/instantiation support for object references, properties,
   signatures, tuples, and index infos.
3. General generic references, constraints/defaults, recursion, and imported
   declarations.
4. Ordinary CFG/source execution beyond the bounded final-if shapes.
5. `keyof`, intersections, general indexed access, and option-sensitive index
   behavior.
6. Structured inference, contextual callbacks, rest/spread arity, constructors,
   and complete overload recovery.
7. Conditional/infer/substitution and mapped/reverse-mapped types, followed by
   template/string-mapping and variance/intrinsic closure.
8. Classes as executable source values with inheritance, constructors,
   accessibility, and member checking.
9. Modern module surfaces: declaration targets, default/namespace imports,
   barrels/reexports, cycles, import-equals/export-equals, then NodeNext.
10. TSX and JavaScript/JSDoc after their semantic prerequisites exist.

## Parallel architecture

### Root-owned integration surfaces

These files and records are serialized within an integration wave:

| Surface | Reason |
|---|---|
| `semantic/type_nodes.rs` | Type-family dispatch, whole-query planning, allocation budgets, and cache publication |
| `semantic/source.rs` | Whole-source preflight, statement/expression dispatch, diagnostics, and atomic commit |
| `semantic/relater.rs` | Relation recursion, cache keys, mode-specific behavior, and structured reduction |
| `semantic/store.rs`, `links.rs`, `production.rs` | Program identity, lazy state, public query boundaries, and publication invariants |
| `semantic/formatter.rs` | Exact display routing shared by diagnostics and artifacts |
| `ts_compiler/src/lib.rs` | Capability-versus-invariant classification and program option/fact projection |

Root owns each shared contract and integration commit. Root may grant one
worker an explicit, single-wave lease for one hub such as `relater.rs`; while
that lease is active, root and every other worker treat the file as read-only.
The lease names the allowed functions and ends when the reviewed stack is
integrated. A leaf worker that needs a new shared field or dispatch contract
stops and proposes the narrow interface instead of independently widening the
hub. Thus S2's relation work is a lease, not contradictory ownership of a
root-owned surface.

### Leaf module contract

Every new type/source family should follow the established leaf pattern:

1. `plan`: inspect exact AST/binder provenance and produce an opaque plan with
   no semantic writes.
2. `prepare`: validate all cold/warm identities and reserve exact allocation
   budgets before publication.
3. `execute` or `finish`: compute through existing child-query APIs and publish
   the complete family atomically.
4. `validate`: prove warm cache identity, graph closure, store ownership, and
   option compatibility.
5. public production test: exercise the actual binder/context/program path,
   not a parallel test-only constructor.

Leaf owners should prefer new modules such as `keyof_types.rs`,
`reference_types.rs`, `conditional_types.rs`, or `classes.rs`. Root registers
their opaque APIs in the shared dispatchers.

### Worker ownership tuple

Each task owns exactly:

- a named upstream function cluster;
- one Rust leaf module set;
- the semantic records it may read or publish; and
- a dedicated public test target or bounded extension to one.

Fixture names are validation inputs, never ownership boundaries. Two workers
must not both own `relater.rs`, `type_nodes.rs`, or `source.rs` in the same
wave.

## Measurement and attribution lane

Measurement work runs continuously beside semantic work and does not become a
reason to postpone the checker.

### M0.1: stable frontier scorecard

Extend scorecard records with:

- upstream SHA, Rust SHA, dirty state, manifest digest, and exact invocation;
- a stable variant key from case path, canonical options, and expected
  baseline;
- separate harness/config, checker-capability, supported mismatch, and fatal
  invariant outcomes;
- a stable capability code linked to the port map, for example
  `A13.CONDITIONAL_TYPE` or `E02.CLASS_DECLARATION`; and
- a `frontierBlocker` field instead of pretending the first failure measures
  total feature coverage.

The runner should finish a shard while retaining fatal outcomes, then exit
nonzero. A fatal invariant is never reclassified as unsupported merely to make
the run complete.

Check in `docs/typechecker-capabilities.tsv` with `code`, `port_map_id`,
`description`, `owner_slice`, `introduced_version`, `status`, and
`replacement`. Every capability code maps to exactly one primary port-map row,
has a stable description and outcome class, and is never silently renamed or
reused. Retired codes remain with a replacement. Fatal invariants use a
separate `INV.*` namespace and can never be reclassified as capabilities. CI
validates uniqueness, registry completeness for typed unsupported results, and
scorecard references. Registry/schema changes are reviewed like public API
changes and recorded in scorecard provenance.

### M0.2: balanced fixed shards

Keep the alphabetic first-50 for historical comparison, but replace it as the
primary gate with checked-in manifests, never a sample chosen dynamically at
run time:

- `tools/ts_fixture/manifests/checker-smoke-v1.json`: 96 exact variant keys,
  twelve from each of modules and
  declarations, objects and relations, generics/calls/inference, flow/source
  syntax, classes, advanced types, TSX, and JavaScript/JSDoc/modern options;
- `tools/ts_fixture/manifests/checker-milestone-v1.json`: a 512-variant
  balanced superset used at wave gates;
  and
- the complete pinned manifest at frozen-epoch closure.

Each family quota includes clean and error-producing programs, and the whole
manifest includes single/multi-file, `.ts`/`.d.ts`, and relevant module-option
variants. Each manifest stores canonical variant keys and a digest. Replacing
a key requires an explicit reviewed manifest change; newly supported cases do
not rotate out harder cases. The manifests cover:

- clean and error-producing programs;
- single- and multi-file programs;
- `.ts` and `.d.ts`;
- Bundler/ESM and NodeNext module shapes;
- functions, generics, objects, classes, advanced types, and control flow;
- TSX; and
- JavaScript/JSDoc.

The same keys run before and after each merge.

### M0.3: semantic artifacts and location queries

H02 is three deliverables, not a formatter-only task:

1. An independent harness scaffold accounts for configured `.types` and
   `.symbols` artifacts, walks the exact upstream node set/order, and records an
   explicit unsupported capability when the production query is unavailable.
2. A root-owned query trunk adds `get_type_at_location` and
   `get_symbol_at_location`, declaration provenance, symbol display, and the
   minimal type-node builder/printer needed by the artifact walker. Formatter
   and node-builder coverage expands in every semantic wave.
3. Exact artifact closure grows with the supported semantic rows; no early H02
   scaffold is called complete merely because it can traverse a file.

Diagnostic-clean programs can otherwise appear exact while inferring the
wrong types or binding the wrong symbols. Artifact generation must use the
production checker query surface and exact upstream ordering; it must not
reconstruct semantic meaning from rendered diagnostics.

### Per-merge attribution

Integrate one coherent slice at a time and diff the same shard after every
cherry-pick. Record:

- exact retained and lost;
- unsupported to exact;
- frontier capability A to frontier capability B;
- mismatch to exact;
- newly supported mismatch;
- fatal invariant; and
- `.types`/`.symbols` exact deltas once H02 lands.

If two interdependent slices unlock a fixture only together, credit the wave,
not whichever commit happened to merge second.

## Semantic dependency DAG

```text
Continuous: M0 scorecards + H02a artifact walker/accounting
                              |
Root contract freeze --------+----------------------------------------------
  | module facts             | member/instantiation       | source query
  v                          v                            v
S1a declaration targets   S2a declared members <----> S3 instantiation
  |                          |                    \          |
S1b ESM aliases/exports      v                     +------> S6 references,
  |                       S2b union/intersection/            aliases, `this`
  +--> S1c namespaces        apparent members                    |
  +--> N1 NodeNext facts            +-------------+--------------+
                                                   |
                                          S5 property-key algebra

S4a CFG ---- S4b general source/expression ---- S4c discriminant/chain flow
                    |                                  |
                    +------> S7 calls <----> S8 inference
                                 |
S2a + S3 + S6 --> S11a class shells --> S11b executable classes

S3 + S5 + S6 + S8 --> S9 conditional core
S2b + S3 + S5 + S8 -> S10 mapped core
S1b + S2a + S7 + S8 -> S12a basic function-component TSX
S9 + S10 + S11b + S12a -> S12b managed/class JSX

Follow-ons: advanced classes/flow, generators, JavaScript/JSDoc, remaining
modern syntax/options, complete corpus closure.
```

S2 and S3 deliberately run concurrently behind a fixed interface: S3 creates
lazy instantiated shells; S2 resolves their members. S7 and S8 may run
concurrently only after they agree on a narrow inference request/result API.
S9 and S10 can run concurrently after S8 because mapped construction does not
require conditional evaluation for its first complete core. S11a moves class
admission ahead of advanced types. S12a covers intrinsic and function
components without waiting for classes or conditional/mapped types; S12b adds
their managed behavior later.

A **leaf gate** uses only already integrated contracts and must pass before the
leaf is merged. A **composition gate** is root-owned and runs after all named
dependencies are integrated. Generic `T[K]`, imported generic members, class
construction, managed JSX, and complete semantic artifacts are composition
claims, not impossible requirements on an in-flight leaf.

## Semantic slices

### S1: declaration modules, aliases, and package facts

S1 is staged because the current compiler manifest rejects declaration-file
targets before checker leaves can run.

**S1a, root compiler prerequisite:** admit resolved `.d.ts` targets into the
canonical program manifest with exact source kind, declaration status,
resolution mode, and ownership. `skipLibCheck` suppresses declaration checking
diagnostics; it does not skip binding or lazy semantic consumption. Leaf gate:
a `.ts` importer and a bound `.d.ts` target share one canonical context without
source-checking the declaration body.

**S1b, ESM aliases/exports:** default and namespace imports, named/star
reexports, two-level barrels, type-only propagation, and alias cycles. Leaf
gate: exact export-table and alias identity in both file orders, cold execution,
forced warm replay, and atomic failure. Its composition gate consumes imported
values/types through S2/S6 without reconstructing identity.

**S1c, bounded namespaces/merges:** internal and repeated namespaces,
external-module namespace objects, qualified type/value lookup, and merging
with aliases, interfaces, and ordinary values. Namespace+class/function
merging waits for S11; general augmentation remains a module follow-on.

**N1, NodeNext fact lane:** after S1a, compiler-only workers can retain package
boundaries, `.mts`/`.cts`/`.d.mts`/`.d.cts` modes, condition selection, and
resolution-mode provenance without waiting for advanced types. Checker
consumption composes later through S1b. `import =`/`export =` is a separate
CommonJS-mode sub-slice and is not smuggled through the plain-ESM gate.

Upstream anchors: alias resolution and exports in `checker.go` and
`exports.go`, plus program/module facts. Rust ownership:
`module_resolution.rs`, `alias_provider.rs`, `source_imports.rs`, and a
root-owned `ts_compiler` manifest/fact adapter; root owns `source.rs` dispatch.

### S2: structured members and relation completion

**S2a, declared/reference member core:** one canonical structured result for
properties, call/construct signatures, and index infos; type literals and
direct interfaces; direct heritage; optional/readonly semantics; string/number
index compatibility; fixed signatures; and the consumer side of an
instantiated shell. Its leaf gate uses non-generic direct types and proves
cold/warm publication, relation behavior, and malformed/foreign-cache
rejection. S2a and S3 share a frozen request/result contract.

**S2b, union/intersection/apparent member algebra:** reduction/apparent
projection before lookup, union/intersection property synthesis, Object and
Function augmentation, namespace-object queries, inherited/synthetic cache
identity, and their structural-relation branches. Its leaf gate uses
preconstructed types; source property access over unions, intersections,
namespaces, and instantiated references is a composition gate with S1/S3/S5/S6.

Upstream anchors: `getPropertiesOfType` through
`resolveStructuredTypeMembers`/`resolveObjectTypeMembers`, plus
`structuredTypeRelatedTo`, `propertiesRelatedTo`, `signaturesRelatedTo`, and
`indexSignaturesRelatedTo`. Rust ownership: new `member_resolution.rs`,
`object_members.rs`, `callable_sets.rs`, and the sole Wave 0 lease for
`relater.rs`.

### S3: mapper and instantiation kernel

Scope:

- composite mapper semantics;
- object/reference instantiation shells;
- signature, symbol, property, tuple, reference-argument, and index-info
  instantiation;
- identity-preserving no-op instantiation;
- exact recursion depth and count budgets.

Conditional, mapped, and inference-owned special cases remain typed handoffs
to S9, S10, and S8.

Upstream anchors: `mapper.go`, `instantiateSignature`,
`instantiateTypeWorker`, and `getObjectTypeInstantiation`. Rust ownership:
`mapper.rs`, `instantiate.rs`, and `signatures.rs`; root owns shared store APIs.

Leaf gate: mapper composition, shell/cache/mapped-record identity,
tuple/reference/signature/index-record substitution, exact budgets,
foreign-store rejection, poison repair, and warm validation without demanding
S2's unresolved general member traversal. Nested generic members and inherited
generic bases are composition gates with S2a/S6.

### S4: CFG plus general source/expression dispatch

**S4a, CFG/statement core:** nested blocks and returns, assignment/reassignment
flow, `if`, loops, classic `for`, `switch`, literal/null equality, fixed points,
labels, joins, and reachability. Leaf gate: binder-proven primitive/local flow
with exact diagnostics, invocation-local retry state, and forced warm replay.

**S4b, general source/expression dispatcher:** recursive expression queries;
unary, update, and conditional expressions; optional property/element/call
syntax and `??` typing; destructuring/binding patterns; object/array spread;
function expressions and broader arrow bodies; general returns,
throw/break/continue, `for..of`, ordinary `try`/`catch` and
`useUnknownInCatchVariables`; `as const`, `satisfies`, and non-null assertions;
broader variable inference; and assignment targets. Each family gets an
isolated production vertical and a typed handoff when member/call/flow
semantics are unavailable. S7 owns call/new/async-callable algorithms, not
this dispatcher.

**S4c, discriminant/nullish flow:** equality and property-discriminant
narrowing, discriminant switches, `in`, optional-chain containment, nullish
flow, type-predicate and assertion-function signatures/narrowing after S7, and
alias-preserving joins after S2b/S5. This runs in Wave 2 rather than waiting for
ecosystem closure.

Defer complex `finally` flow, closure capture, and full definite assignment to
advanced flow follow-ons.

Upstream anchors: `getTypeAtFlowNode`, assignment/condition/branch/loop/switch
paths, `narrowTypeByEquality`, expression dispatch, and ordinary statement
checkers. Rust ownership: `source_flow.rs`, `source_statements.rs`, preferably
new `source_control_flow.rs` and `source_expressions.rs`; root owns the
`source.rs` contract and dispatch adapter.

### S5: property-key algebra

Scope:

- property-first intersection construction and reduction;
- `keyof` over interfaces, literals, arrays, and index signatures;
- general indexed access over resolved objects, unions, and intersections;
- exact named/string/number precedence;
- `noUncheckedIndexedAccess` option plumbing.

Generic forms become executable after S6; they are not part of S5's
independent leaf gate.

Upstream anchors: `getTypeFromIntersectionTypeNode`, `getIntersectionType`,
`getIndexType`, `getIndexedAccessTypeOrUndefined`, and
`getPropertyTypeForIndexType`. Rust ownership: new `intersection_types.rs` and
`keyof_types.rs`, plus `indexed_access_types.rs`; root owns type-node,
formatter, option, and compiler adapters.

Leaf gate: non-generic resolved-object `keyof`/index/intersection behavior,
mixed properties/indexes, union indexing, the option matrix, cold/warm
identity, and adversarial member-cache tests. Generic `T[K]`, imported
recursive generics, and tuple indexing are a Wave 1 composition gate with
S2/S3/S6/A10.

### S6: general generic references, aliases, and `this`

Scope:

- direct and qualified type references;
- generic classes/interfaces and type aliases with supported
  object/reference/union/intersection bodies;
- defaults, constraints, outer type parameters, and exact cache keys;
- recursive references such as `Node<T>`;
- polymorphic `this` creation and substitution;
- imported generic declaration targets through S1.

Defer conditional and mapped alias bodies to S9/S10.

Upstream anchors: `getTypeFromTypeReference`, `getTypeReferenceType`,
`fillMissingTypeArguments`, and declared class/interface construction. Rust
ownership: preferably new `reference_types.rs`, `declared.rs`, and S3's
instantiation API; root owns `type_nodes.rs` registration.

Leaf gate: local declarations, alias bodies, defaults, constraints, recursion,
outer parameters, `this` substitution, warm replay, and exact arity
diagnostics. Imported/qualified targets compose with S1; instantiated members
compose with S2/S3; generic `keyof`/`T[K]` composes with S5.

### S7: callable shapes, overloads, spreads, and construction

Scope:

- optional/rest parameters and tuple-rest normalization;
- `const` type-parameter declaration/signature preservation;
- ordered overload declarations;
- construct signatures and constructor-type nodes;
- spread arguments and `new`;
- subtype-then-assignable overload choice;
- exact failure-recovery signatures and diagnostics;
- async functions/arrows/methods and return validation;
- `await`, Promise/thenable unwrapping, Promise-like diagnostics, and
  `for await` composition with S4b.

S8 supplies the inference interface; S7 must remain independently testable
with explicit or fixed type arguments.

Upstream anchors: `resolveCall`, `chooseOverload`, `hasCorrectArity`,
`getSignatureApplicabilityError`, and signature instantiation. Rust ownership:
`functions.rs`, `source_callables.rs`, `callable_sets.rs`, `calls.rs`,
`source_calls.rs`, and preferably new `overload_resolution.rs`.

Leaf gate: ordered literal overloads, optional/rest calls, tuple spread,
construct signatures, `new`, recovery, awaited/thenable calculation, and exact
call/async diagnostics. Source `await`, async callable bodies, and `for await`
are the Wave 2 composition gate with S4b. Generators/`yield` remain an explicit
Wave 4 follow-on.

### S8: structured inference and contextual callbacks

Scope:

- canonical inference contexts, priorities, candidate collection, fixing, and
  deterministic ordering;
- inference through arrays, tuples, object properties, parameters, and
  returns;
- contextual arrows/functions;
- repeated covariant and contravariant candidates;
- `const` type-parameter candidate preservation and tuple/object literal
  inference;
- a narrow engine API consumed by S7.

Defer conditional `infer` consumption to S9 and reverse-mapped inference to
S10.

Upstream anchors: `inference.go` and `inferTypeArguments`. Rust ownership:
`inference.rs`, `generic_calls.rs`, `contextual.rs`, and a dedicated
`source_arrows.rs`; root owns the S7 bridge.

Gate: structured identity, `map`-style callbacks, object/array candidates,
defaults/constraints, contravariance, const-parameter literal preservation,
and repeatable candidate order. A10's const-generic source-call closure is a
Wave 2 composition gate with S7.

### S9: conditional and `infer` types

Scope:

- conditional roots and caches;
- distributive and non-distributive evaluation;
- `infer` parameters and substitution types;
- default/distributive constraints;
- the exact tail-recursion limit of 1,000.

Upstream anchors: `getTypeFromConditionalTypeNode`, `getConditionalType`, and
`getConditionalTypeInstantiation`. Rust ownership: new
`conditional_types.rs` with bounded S3/constraint APIs; root owns dispatch and
formatter routing.

Gate: `Exclude`, `Extract`, `ReturnType`, nested distribution, constrained
inference, tail recursion, circular behavior, cold/warm identity, and poison
rejection.

### S10: mapped and reverse-mapped types

Scope:

- optional/readonly modifier addition and removal;
- homomorphic mapping over objects, arrays, tuples, and unions;
- supported key remapping;
- lazy member materialization;
- reverse-mapped inference through S8;
- `Partial`, `Required`, `Readonly`, and `Pick` in the mapped core.

`Omit`, conditional key-remap integration, and utility closure are Wave 3
composition work after S9; they are not part of the concurrently developed S10
leaf gate.

Upstream anchors: `resolveMappedTypeMembers`, `getTypeFromMappedTypeNode`,
mapped instantiation, and reverse-mapped inference. Rust ownership: new
`mapped_types.rs` consuming S2/S3/S8 APIs; root owns shared routing.

Leaf gate: mapped-core object/tuple/array homomorphism, modifier matrices,
supported key remap, reverse-inference records, and stable lazy member caches.

### S11: classes in two project-facing stages

**S11a, class shells/members:** start after S2a/S3/S6. Port declaration
identity and value/instance split, static/instance annotated properties and
method signatures, simple `extends`, generic base instantiation, and class
expressions once S4b admits them. Leaf gate: exact member tables/base identities,
static/instance separation, cold execution, and forced warm replay. Its
composition gate lets class types participate in relations and module exports.

**S11b, executable classes:** after S7 and S4b, add constructors/`new`, method
and constructor bodies, `implements`, public/protected/private accessibility,
override checking, and fixed initialization checks. This closes the common
class-heavy project gate while S9/S10 are developed in parallel.

Defer decorators, ECMAScript private identifiers, static blocks, mixins, and
advanced initialization analysis to a follow-on.

Upstream anchors: `checkClassLikeDeclaration`,
`getDeclaredTypeOfClassOrInterface`, `resolveBaseTypesOfClass`, and member/
constructor checkers. Rust ownership: new `classes.rs` consuming
S2/S3/S4/S6/S7; root owns source and compiler dispatch.

### S12: TSX in basic and managed stages

**S12a, basic TSX/function components:** TSX program admission, intrinsic
tags, fixed function components, attributes/children/basic spreads, JSX
namespace lookup, and classic/automatic runtime resolution after S1b/S2a/S7.
Generic function components compose after S8. This gate deliberately does not
wait for classes, conditional types, or mapped types.

**S12b, managed/class JSX:** after S9/S10/S11b, add class components,
`LibraryManagedAttributes`, and conditional/mapped prop transformations.

Upstream anchors: `jsx.go` call resolution, attribute construction, props
extraction, and namespace lookup. Rust ownership: new `jsx.rs`; root owns TSX
program admission. The S12a gate is a local React-like declaration fixture
with intrinsic/fixed components and bad-prop diagnostics. Generic components,
automatic runtime imports, managed attributes, and class components are named
composition gates at their respective stages.

## Integration waves

### Wave 0: contracts, measurement, and independent foundations

Land M0 before integrating the first semantic stack and land H02a before the
Wave 0 exit. In parallel, freeze the S2/S3 contract and implement S2a and S3.
Root supplies S1a compiler facts; S1b and the first S4a vertical start as
capacity frees. At four slots, S1 is queued behind S2/S3 rather than becoming a
third unchecked writer.

Exit gate:

- the checked-in 96-variant scorecard and capability registry exist;
- fatal outcomes are retained, later variants still execute, and the run exits
  nonzero;
- `.ts` consumes a simple exported declaration from `.d.ts`;
- direct members and instantiated shells prove a compatible identity contract;
- one ordinary primitive/local CFG vertical passes; and
- no exact artifact regresses or unsupported case becomes a silent mismatch.

### Wave 1: references, member algebra, and source breadth

Run S1c and N1 fact infrastructure, S2b, S5's non-generic core, S6, S4b, and
H02b as dependencies and slots allow. Start S11a once S2a/S3/S6 are green.
With four slots this is four reviewed sub-waves—S5/S6, S2b/S4b, S1c/N1, then
S11a/composition—not eight simultaneous writers.

Composition gate: imported recursive generic objects expose instantiated
members; namespace/barrel consumers work; `keyof`, `T[K]`, indexed access, and
intersections compose; common destructuring/spread/optional-expression source
shapes execute; class declarations cease being a front-door blocker; and the
location/symbol query trunk returns stable production identities.

### Wave 2: calls, inference, narrowing, classes, and basic TSX

Freeze the inference request/result interface, then run S7 and S8. Run S4c,
finish S11a and add S11b, stage S12a fixed components before its generic
composition, connect NodeNext facts to the checker, and add H02c adapters for
each integrated family.

Composition gate: generic callbacks, overloads/rest/spread/`new`,
const-generic calls, async functions/`await`/`for await`, discriminated unions
and optional chains, predicate/assertion functions, `try`/`catch`,
const/satisfies/non-null assertions, executable ordinary classes, basic
function-component TSX, and bounded Bundler/NodeNext projects are exact in
errors/types/symbols.

### Wave 3: advanced type closure

Run S9 conditional core, S10 mapped core, A14 template/string-mapping types,
and the `NoInfer`/required-intrinsic subset of A15 as capacity permits. After
the cores land, serialize conditional key-remap/`Omit`, reverse-mapped
inference, standard utility-type integration, and S12b managed/class JSX.

Exit gate: the pinned modern-project core ring passes, standard-library
utilities, template keys, string mappings, `NoInfer`, and checker intrinsics
compose through the actual pinned default-library declarations with
classes/callbacks/JSX, and the milestone scorecard has no exact losses,
supported mismatches, or fatal invariants.

### Wave 4: ecosystem closure

Finish A15 variance closure, module augmentation and full NodeNext/package
semantics, plus decorators, private fields, static initialization, generators,
complex `finally`, closure flow, and definite assignment. Close the pinned
NodeNext and TSX project rings.

Exit gate: representative Bundler, NodeNext, and React-like projects and their
declaration dependencies are exact in diagnostics, types, and symbols.

### Wave 5: full frozen-epoch closure

Cluster the complete compiler/conformance corpus by stable frontier code. Work
root algorithms in parallel, never fixture names. Close JavaScript/JSDoc,
remaining syntax/options, diagnostic elaboration, and semantic display, then
pass the complete ecosystem project ring.

Exit gate: zero Rust-only unsupported variants, zero unapproved mismatches,
zero fatal invariants, and exact complete artifacts for the frozen epoch.

## Staffing and scaling

| Active slots | Recommended topology | Useful concurrency |
|---:|---|---:|
| 4 | root/integrator; two leaf implementers; one rotating reviewer/oracle/fixer | about 2.5-3 lanes |
| 8 | root; four leaf implementers; Go reviewer; Rust-invariant reviewer; fixer/oracle | about 6-7 lanes |
| 12 | root; seven leaf owners; two reviewers; one fixer; one oracle worker | about 9-10 lanes |
| 16+ | keep roughly seven semantic writers; add corpus shards, fuzz/property testing, diagnostics, module/project gates, and more review | integration-limited |

Before S2/S3/S6/S7/S8 contracts freeze, allow at most two simultaneous writers
on shared type/signature/relation state. After they freeze, seven semantic leaf
owners are plausible. Additional workers remain valuable for independent
review and corpus attribution; converting every slot into a writer would lower
throughput by overloading integration.

The executable four-slot schedule is:

| Phase | Root | Worker A | Worker B | Worker C |
|---|---|---|---|---|
| W0.0 | Freeze S2/S3 and typed compiler/query envelopes | S2 inventory/API proof; review M0 | S3 inventory/API proof; review M0 | Implement fixed-manifest/retained-fatal harness |
| W0.1 | Rust-review and serially integrate leaves | Implement S2a | Implement S3 | Go review/oracle |
| W0.2 | Root-only S1a/query adapters and integration | Implement S1b | Implement first S4a vertical | H02a between Go reviews |
| W1.0 | Review and serial integration | Implement dependency-independent S5 core | Implement S6 | Go review/oracle; advance H02b |
| W1.1 | Root member/source adapters | Implement S2b | Implement S4b | Go review/oracle; advance H02b |
| W1.2 | Root module/compiler adapters | Implement S1c | Implement N1 fact snapshots | Go review/oracle; advance H02b |
| W1.3 | Composition adapters and scoring | Implement S11a | Own cross-slice composition tests/fixes | Go review/oracle; close H02b gate |

M0 lands before the first semantic stack is integrated, although S2/S3 may be
implemented while it is being reviewed. Reviews may be sequential: every
semantic stack receives a fresh Go-semantic review and a different
Rust-invariant review. Root may supply the Rust review only when root authored
none of that stack. A root-authored adapter is reviewed by Worker C and the
non-owning semantic worker; joint root/Worker-C M0 work is reviewed by Workers
A and B. There are never more than two unreviewed stacks.

A hub lease is recorded as `hub, wave, owner, base_sha, allowed_symbols,
expiry_commit`. Only one lease exists per hub and a worker holds at most one.
M0 consumes a root-provided typed capability envelope; H02 consumes a
root-provided artifact-query interface. Neither lane edits compiler,
production, or formatter internals independently.

### Complete port-map assignment

Every port-map row has one primary lane below. Other slices may consume it but
do not become co-owners.

| Primary rows | Wave/lane | Owner | Shared lease/adapter | Completion gate |
|---|---|---|---|---|
| H00 H01 A00 A01 B00 B01 B02 B03 T00 T01 T02 | verified foundation | root regression | none | all later gates retain foundation invariants |
| H02 T07 C00 C01 | M0/continuous | oracle + root query | root compiler/production/formatter adapters | retained scorecards and per-wave exact artifacts |
| B04 T04 M00 | S1, W0-W4 | module owner | root compiler/source adapter | declaration ESM, namespaces, then package/CommonJS closure |
| R00 R01 R02 | S2, W0-W1 | member/relation owner | exclusive `relater.rs` lease | declared then synthetic/apparent members exact |
| T03 R03 | S3, W0 | instantiation owner | root store API | shells, mappers, and composite instantiation exact |
| B05 E00 E01 F00 | S4, W0-W4 | source/flow owner | root `source.rs` adapter | general statement/expression routing and narrowing exact; S7 supplies call/new algorithms |
| A11 A16 | S5, W1 | property-algebra owner | root type-node/formatter adapters | intersections, `keyof`, indexed access, option matrix exact |
| T05 T06 R04 | S6, W1 | reference owner | root type-node adapter | local/imported recursive references, aliases, constraints exact |
| R06 A10 | S7, W2 | call owner | root source/type adapters | overload/rest/spread/construct, tuple-call, and S8-composed const-generic behavior exact |
| R05 | S8, W2 | inference owner | frozen S7/S8 interface | structured/contextual inference exact |
| A13 | S9, W3 | conditional owner | root type-node/formatter adapters | conditional/infer core and utility composition exact |
| A12 | S10, W3 | mapped owner | root type-node/formatter adapters | mapped/reverse-mapped core and utility composition exact |
| E02 | S11, W1-W4 | class owner | root source/compiler adapter | shells, executable classes, then advanced class closure |
| M01 M04 | S12, W2-W3 | JSX owner | root TSX admission adapter | basic function JSX, then managed/class JSX exact |
| A14 A15 | W3-W4 advanced core/follow-on | advanced-type owners | root type/formatter adapters | template/string/NoInfer/intrinsic core, then variance closure exact |
| M03 | W4 follow-on | modern-syntax owner | root source/compiler adapters | modern option/syntax shards exact |
| G00 M02 | W5 closure | diagnostics + JS owners | root source/formatter adapters | exact diagnostics and JS/JSDoc project ring |
| C02 | post-parity | root | production cutover | controlled roll-forward retains frozen parity |

## Implement-review-fix loop

Every slice follows the same loop:

1. **Inventory:** record exact upstream functions, dependencies, data records,
   options, diagnostics, and recursion budgets.
2. **Implement:** port the coherent cluster in its worktree without Cargo or
   unrelated shared-hub edits.
3. **Go review:** a fresh-context reviewer compares branches, evaluation order,
   nil behavior, flags, caches, diagnostics, and limits against the pinned Go
   source.
4. **Rust review:** a separate reviewer assumes the patch is wrong and checks
   ownership, store provenance, cold/warm state, atomicity, recursion,
   deterministic order, and adversarial cache behavior.
5. **Fix:** the author or a dedicated fixer resolves both reports. Reviewers do
   not approve their own implementation.
6. **Integrate:** root cherry-picks one coherent stack, resolves the narrow hub
   adapters, runs gates, scores the fixed shard, updates the map, and commits.

When a review finds a systemic mistake, update the worker contract or template
so later slices do not repeat it. That feedback-loop repair is more valuable
than fixing only the observed fixture.

## Acceptance gates

### Per leaf

Required evidence:

- exact upstream function inventory and one port-map owner;
- public production-path test;
- cold execution and forced warm replay, not merely a second call that exits on
  `type_checked`;
- atomic retry after an unsupported boundary when the leaf stages or publishes
  semantic state;
- missing/wrong/foreign cache identity tests when the leaf owns a semantic
  cache;
- relevant strict-option matrix;
- cross-file test whenever identity can leave a file;
- no hidden fallback, stub, fixture-name branch, or unexplained broad type;
- production-library check plus compilation and execution of every affected
  public integration target through the capped runner;
- focused public integration tests;
- strict checker Clippy and rustdoc warnings denied; and
- fixed scorecard shard with zero exact losses, zero new supported mismatches,
  and zero fatal invariants.

### Per integration wave

- serial score after each coherent cherry-pick;
- all affected public checker/compiler targets;
- checked-in 96-variant smoke manifest;
- checked-in 512-variant milestone manifest at the wave gate;
- exact prior artifacts retained;
- capability frontiers may advance but never silently disappear;
- port map and this plan synchronized to the integrated commit; and
- no more than two unreviewed semantic stacks waiting per reviewer.

### Practical verification commands

The root integration lane owns slow builds and runs them serially:

```sh
scripts/run-cargo-capped.sh check -p ts_checker --lib
scripts/run-cargo-capped.sh check -p ts_checker --test <public-target>
scripts/run-cargo-capped.sh test -p ts_checker --test <public-target> -- --nocapture

scripts/run-cargo-capped.sh clippy -p ts_checker \
  --lib --test <public-target> --no-deps -- \
  -D warnings \
  -A clippy::too_many_lines \
  -A clippy::nonminimal_bool \
  -A clippy::match_same_arms \
  -A clippy::large_enum_variant

scripts/run-cargo-capped.sh clippy -p ts_compiler --all-targets --no-deps -- \
  -D warnings

RUSTDOCFLAGS='-D warnings' \
  scripts/run-cargo-capped.sh doc -p ts_checker --no-deps
```

The capped runner defaults to an aggregate memory limit of up to 8 GiB when
the host has enough available memory. Set `TS_CARGO_MEMORY_LIMIT_KIB` to adjust
the limit. The complete checker unit-test binary now runs within the updated
memory envelope. Keep Cargo commands serialized across agent worktrees, and
run focused public integration tests for each changed behavior.

### Objective modern-project manifest

Before Wave 1 closes, check in
`tools/ts_fixture/manifests/modern-projects-v1.tsv`. Each row pins repository
URL and commit, license, lockfile digest, package manager, exact tsconfig paths,
project ring, non-generated TypeScript line count, and the pinned
typescript-go artifact digests. Selection happens once under review, not at
claim time. The initial candidate pool should include a type-heavy library
such as Zod or ts-pattern, a callback/inference-heavy library such as TanStack
Query, a multi-package Bundler/ESM library such as Hono, and a React/TSX project
such as React Hook Form; final entries and revisions are fixed by the manifest.

The **core ring** contains at least four strict `.ts` projects totaling at
least 100,000 non-generated lines and covers utility-heavy generics, classes,
callback inference, and a multi-package Bundler/ESM graph consuming `.d.ts`.
The **ecosystem ring** adds at least one NodeNext project, one TSX project, and
one mixed JavaScript/JSDoc project.

A ring passes only from clean pinned checkouts with:

- no source patches, project-specific exclusions, skips, or checker fallback;
- identical files, libraries, options, and module graphs in Rust and the pinned
  Go oracle;
- exact diagnostics, `.types`, and `.symbols`;
- identical cold execution and forced warm replay across two deterministic
  runs;
- zero unsupported, mismatch, or fatal results; and
- release-mode wall time no worse than 10x typescript-go and peak RSS no worse
  than `max(2x typescript-go, 4 GiB)` on the recorded machine profile.

Wave 3 may claim the core ring, Wave 4 adds the NodeNext and TSX entries, and
Wave 5 claims the complete ecosystem ring. These are ceilings for viability,
not a claim that performance optimization is finished.

## Milestone claims

### Modern TypeScript core

Claim this only when the pinned modern-project core ring proves:

- `.ts` and consumed `.d.ts` across multi-file Bundler/ESM graphs;
- ordinary interfaces, generic objects/functions, utility types, arrays,
  tuples, intersections, indexed access, conditionals, and mapped types;
- overloads, callbacks, rest/spread, constructors, and classes;
- ordinary assignments, branches, loops, switches, and narrowing;
- strict options needed by the suite; and
- exact diagnostics plus `.types` and `.symbols`.

### Modern ecosystem

Add NodeNext/package facts, TSX/function components, advanced class/flow
behavior, and standard-library closure. Representative real projects must run
through the same canonical path without a project-specific skip or fallback.

### Frozen-epoch parity

All pinned compiler/conformance configurations are accounted for as executed,
upstream-skipped, or emit-only/out-of-scope. Every checker-relevant variant has
exact errors/types/symbols, and the port map has no unverified row in the core
semantic dependency closure.

### Maintainability

Port one later upstream semantic batch using the retained function/module map,
then prove both the new epoch and all frozen-epoch regression artifacts. This
is required evidence that the Rust architecture remains recognizable and
maintainable.

## Risks and controls

| Risk | Control |
|---|---|
| Parallel workers race on shared state | Exclusive module/record ownership; root-only hub adapters; isolated worktrees |
| Compilation is mistaken for correctness | Two independent adversarial reviews and production-path artifacts |
| Corpus count rewards front-door admissions | Stable frontier codes plus exact errors/types/symbols and balanced shards |
| New capabilities poison warm caches | Mandatory forced replay, poison, foreign-ID, and atomic-retry tests |
| Calls/inference/relations diverge into incompatible mini-engines | Freeze narrow shared APIs and one relation owner per wave |
| Classes or TSX begin before prerequisites | Enforce the DAG and allow syntax planning only behind fixed semantic plans |
| Standard library remains special-cased | Make library declarations consumers of S1/S2/S3/S6/S9/S10 |
| Too many workers overload integration | Cap semantic writers around seven; put excess capacity into review, oracle, and fuzzing |
| Upstream drift causes endless churn | Frozen epoch, drift ledger, one required roll-forward after parity |

## Immediate execution queue

1. Connect the existing exact direct local base-class transaction to whole-
   source checking, preserving whole-file preflight and leaving derived `new`
   expressions outside the leaf unless their existing constructor contract can
   be reused without widening it.
2. Project `strictPropertyInitialization` into the canonical checker and admit
   annotated uninitialized instance fields only when the option disables that
   diagnostic; then add direct annotated uninitialized `var` declarations under
   the pinned loose-flow rules.
3. Integrate the reviewed property-only generic-interface member kernel by
   publishing the binder's property-only declared table, then admit its exact
   transient instantiated properties in the relater and source/context query.
4. Rerun the fixed shard after each source frontier, record every status and
   frontier delta, and choose the next dependency-closed source/callable leaf.
5. Keep root as the sole shared-adapter, Cargo, compiler-gate, and scorecard
   owner while semantic workers and independent reviewers rotate around it.

This is the shortest credible path to useful modern-project checking and then
full typescript-go parity. It multiplies independent semantic work without
pretending that the checker graph, relation engine, or publication transaction
can be merged safely by independent writers at the same time.
