# Goal: typescript-go core typechecking parity in Rust

- Status: active
- Audit date: 2026-07-14
- Local branch: `july-ultra`
- Audited upstream pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`

## Executive decision

The shortest credible path to broad TypeScript compatibility is to replace the
current simplified semantic foundation with a faithful Rust port of
typescript-go's binder and checker algorithms. We should stop using isolated
fixture fixes as the primary development loop.

This is not a recommendation to discard the working repository or mechanically
translate every Go package at once. The scanner, parser, AST generation,
compiler shell, module resolver, bundled libraries, diagnostics catalog, CLI,
and existing tests are useful assets. The replacement should happen behind one
whole-checker boundary so that old and new semantic types never mix. Within
that boundary, coherent upstream clusters should be ported mechanically and
reviewed against the Go source before doing idiomatic Rust refactors.

The critical path is:

1. Make the Go fixture corpus an exact, measurable oracle.
2. Establish stable program-wide node, symbol, flow, type, and signature
   identities.
3. Port binder/name-resolution/control-flow construction.
4. Port the canonical type kernel, declared types, and lazy semantic links.
5. Add the minimum source/expression traversal and port base relations,
   instantiation, inference, contextual typing, and overload resolution as a
   coupled vertical slice.
6. Extend that slice through advanced types, then complete source checking,
   classes, flow evaluation, and strict option behavior in dependency order.
7. Prove the result on modern multi-file projects, then close the entire
   upstream compiler/conformance corpus.
8. Cut over atomically, remove the legacy semantic bridge, and demonstrate one
   controlled upstream roll-forward.

This goal prioritizes typechecking. JavaScript emit, complete declaration emit,
source maps, watch/build mode, fourslash, and language-service parity remain
follow-on goals except where a checker API or artifact is required to validate
semantic parity.

## Execution progress

Work began on 2026-07-14 after this goal was approved. The integration branch
records small, dependency-closed commits; `docs/typechecker-port-map.tsv`
remains the cluster-level source of truth.

- Cargo invocations are serialized across linked worktrees.
- Upstream corpus discovery is fail-closed and records all 12,750 discovered
  cases, including the pinned runner's 45 explicit skips.
- Diagnostic scorecards distinguish header-only evidence from exact parity.
- Complete non-pretty `.errors.txt` rendering is implemented on a review branch,
  but remains unmerged until exact option-matrix expansion cannot manufacture
  clean variants.
- Canonical `TypeFlags`, `ObjectFlags`, signature flags, tuple/index flags, and
  relation ternary values are pinned to the audited upstream commit.
- Program-wide node identity is independently reviewed and verified on the
  integration branch. Complete symbol masks and the typed flow substrate are
  integrated as well; the combined stack passes 209 focused tests and adds no
  Clippy regression.
- Canonical semantic IDs plus signature, predicate, index, and tuple records
  are the active type-system lane. Program-owned symbols and binder CFG
  construction are the next dependency-closed binder lane.

No percentage in this section is a whole-corpus parity claim. A score is
publishable only when its variant manifest and complete artifact comparison are
both exact.

This document is the checker-specific execution goal.
`docs/PORTING.md` remains the broad compiler dependency spine, and its
syntax-only/no-check gate remains a regression test, but it is no longer the
typechecking critical path. Earlier fixture-oriented recovery plans remain
historical context rather than the semantic architecture target.

## The outcome

At the end of this goal, for one recorded typescript-go commit, `ts-rust` will:

- load the same program graph as typescript-go for supported modern compiler
  configurations;
- produce the same complete diagnostics, including code, category, file,
  span, message chains, related information, and deterministic ordering;
- produce the same `.types` and `.symbols` baselines;
- implement the same symbol identity, type identity, relation, inference,
  overload, and control-flow semantics rather than approximating their output;
- check ordinary standard-library declarations through the same binder/checker
  path as user declarations;
- pass a pinned suite of representative modern TypeScript projects;
- contain no per-feature fallback to the legacy checker, silent `any`/`unknown`
  escape hatch, hidden skip, or accepted Rust-only baseline difference;
- survive recursive and adversarial programs within the same explicit semantic
  budgets as the Go checker; and
- remain maintainable enough to port a later batch of upstream checker changes
  by following recognizable Go function and module structure.

"Parity" in this document means typescript-go parity, not JavaScript
TypeScript parity. The Go port intentionally differs from the JavaScript
implementation in some areas, and its checked-in actual baselines and
`CHANGES.md` are the authority.

## Where the port is today

### What is already valuable

The repository is well beyond a parser-only prototype. The local checker has
about 26,800 lines of production implementation and supports useful subsets of
primitives, literals, objects, functions, overloads, generics, constraints,
classes, tuples, unions/intersections, mapped and conditional types, template
literal types, utility types, narrowing, modules, and JSDoc.

Targeted results from this audit were:

| Surface | Result | What it establishes |
|---|---:|---|
| `ts_binder` native tests | 20/20 | The current local binder behaviors are stable. |
| `ts_checker` native tests | 149/149 | The current structural checker is internally consistent. |
| Curated semantic-oracle files | 27/27 exact | The selected strict, single-file cases match the pinned Go CLI. |
| `ts_compiler` native tests | 119/125 | Most compiler behavior works; six declaration/provenance/emit cases expose remaining integration faults. |
| `ts_cli` native tests | 39/39 | The current command-line vertical slice is healthy. |
| `ts_fixture` native tests | 65/65 | The fixture parser's own expected behavior is stable. |

The six compiler failures are concentrated in declaration/reference
deduplication, cross-file alias provenance, inferred declaration emit, ambient
literal declaration serialization, source-map ordering, and declaration import
elision. They do not negate the working checker, but the provenance failures
are consistent with the cross-file identity problem described below.

The 27-file semantic corpus should remain a fast regression ring. It is not a
coverage measure: every case is a single `.ts` file run with `--strict`, every
case intentionally emits diagnostics, and it covers no clean-file false
positives, TSX, JavaScript/JSDoc, project configuration, multi-file cycle,
package resolution, or real program graph.

### Why progress is plateauing

The remaining gap is architectural rather than a list of missing syntax cases.

1. **Cross-file types lose identity.** `ProgramChecker` checks files, converts
   exported/global types to a duplicate `TypeDescriptor` representation, then
   reconstructs them for dependent files. Recursive aliases, cycles, generic
   targets, declaration provenance, augmentation, relation caches, and nominal
   private/protected identity cannot be represented faithfully this way.

2. **The type model is too flat.** The local `TypeKind` has 25 variants and
   omits important first-class upstream concepts such as object/reference
   flags, fresh literals, unique symbols, signatures with predicates and
   `this`, complete tuple element flags, type mappers, deferred conditional and
   mapped types, substitutions, indexed-access types, string mappings, and
   variance metadata.

3. **The binder does not build TypeScript's flow graph.** Generated AST nodes
   have flow IDs, but the binder does not populate a graph. The checker clones
   and joins mutable maps while walking syntax. That cannot accurately model
   loops, exception paths, labels, closure flow, reachability, definite
   assignment, and the full narrowing algorithm.

4. **Relations and inference are approximations.** Assignability is one
   handwritten structural path without upstream relation modes and caches.
   Inference keeps a simplified candidate, overload resolution commonly takes
   the first applicable signature, and contextual typing often chooses one
   signature early. These algorithms are tightly coupled in TypeScript and are
   responsible for a large fraction of useful typechecking behavior.

5. **Libraries are special-cased.** Default-library declarations are described
   selectively and some globals degrade to shallow `any` rather than entering
   the same canonical semantic graph as source declarations.

6. **Option coverage is narrow.** The checker-facing option record has roughly
   a dozen fields and omits semantic switches used by modern projects,
   including `noUncheckedIndexedAccess`, `strictFunctionTypes`,
   `strictBindCallApply`, `noImplicitThis`, `noImplicitOverride`, and
   `noPropertyAccessFromIndexSignature`.

7. **Fallbacks conceal missing semantics.** The implementation contains few
   obvious `todo!` markers; instead, omissions appear as eager reduction,
   first-signature selection, broad scope lookup, or `any`/`unknown`. That makes
   green bespoke tests easy to add without converging on upstream behavior.

### The current upstream score is not trustworthy

The ordinary verification script does not run semantic upstream comparisons.
When `TS_GO_REPO` is absent, the `upstream_cases` test returns successfully
without testing the corpus. When it is present, that test proves fixture
parsing, not checker parity.

The diagnostic runner also selects the wrong expected-output layout:

- it looks for `testdata/tests/baselines/reference`, which does not exist;
- it falls through to the JavaScript TypeScript submodule baselines;
- the actual Go outputs live under
  `testdata/baselines/reference/{compiler,conformance}` for Go-owned tests and
  `testdata/baselines/reference/submodule/{compiler,conformance}` for the
  TypeScript submodule;
- it compares only the diagnostic header before the first blank line;
- it does not produce `.types` or `.symbols`;
- it admits suites with different harness semantics, such as fourslash and
  projects; and
- it does not reproduce the Go runner's option matrices, baseline overlays, or
  explicit skip list.

The pinned submodule contains 6,537 compiler and 5,907 conformance `.ts`/`.tsx`
source cases before the Go runner's 45 explicit skips and before option
expansion. Its Go-produced submodule references include 7,023 error, 12,155
type, and 12,155 symbol baseline files. These are orders of magnitude broader
than the curated suite.

As a directional check, this audit sampled 59 expanded variants across widely
separated compiler and conformance paths. Four were cases the Go runner skips;
22 of the remaining 55 matched the actual pinned Go diagnostic baselines
exactly. The resulting 40% is not a statistically valid whole-project estimate,
but it is sufficient to reject the idea that the 27/27 curated result reflects
broad parity. We should publish no overall percentage until the harness has a
canonical manifest and denominator.

## Lessons adopted from Bun's Rust rewrite

Jarred Sumner's [Bun rewrite account](https://bun.com/blog/bun-in-rust)
describes a successful strategy that is unusually relevant here:

- make the port mechanical and minimize behavioral changes;
- use the same language-independent tests as the original implementation;
- preserve architecture, function names, and recognizable control flow during
  the port, accepting temporarily unidiomatic Rust;
- inventory the work before scaling it out;
- use independent reviewers to find code that compiles but is semantically
  wrong;
- forbid stubs whose purpose is merely to make the build green; and
- refactor only after parity.

We should adopt those rules, with one adaptation. Bun could cut over a bounded
component all at once. Here, the checker is embedded in an already working
compiler and the upstream semantic foundation is roughly 60,000 checker lines
plus binder/AST/compiler contracts. Our equivalent of an all-at-once rewrite
is an **atomic semantic boundary**:

- construct the new core in coherent modules;
- allow tests to invoke either whole checker during development;
- never call the legacy checker for an unsupported node or mix legacy/new type
  IDs inside one program; and
- switch the default checker atomically only after the new core passes the full
  supported compiler/conformance gate.

This preserves a usable branch without creating a permanent bridge architecture.

## Source of truth and upstream policy

The audit is tied to typescript-go
[`dc37b52`](https://github.com/microsoft/typescript-go/commit/dc37b5249ab60e2bbce936f71b883e6c8136167e)
from 2026-06-19. At audit time, upstream `main` was 98 commits ahead, with a
net 742 additions and 303 deletions across the AST, binder, checker, and
compiler paths.

The port should not chase a moving `main` while its semantic substrate is being
replaced. The epoch policy is:

1. Build the exact scorecard against the current recorded pin.
2. Once the scorecard is trustworthy, update once to a chosen current upstream
   commit, regenerate pinned inputs, record all intentional differences, and
   freeze that commit for the semantic port. Repinning at that point is
   recommended because the current target is already behind before major work
   begins.
3. Do not merge routine upstream semantic changes during milestones 1-7.
4. Keep a drift ledger that maps later upstream commits to the Rust module and
   port-map rows they affect.
5. After full frozen-epoch parity, roll forward in one bounded batch and rerun
   the complete scorecard. That is part of the definition of done because it
   tests maintainability, not just correctness at one snapshot.

Ordinary Cargo builds must continue to require neither Go nor Node. Go is an
external differential oracle and fixture-maintenance dependency, never a
runtime dependency.

## Target semantic architecture

The new architecture should preserve Rust's arena/ID strengths while matching
the information and lazy behavior of the Go checker.

```text
Program / CheckerHost
        |
        v
Program-owned SemanticStore
  +-- source files and NodeRef(FileId, NodeId)
  +-- symbols, symbol tables, aliases, SymbolLinks
  +-- binder FlowNodes and antecedents
  +-- types, signatures, mappers, NodeLinks
  +-- relation/inference/instantiation caches and budgets
        |
        +--> binder + shared name resolver
        +--> checker queries and source checking
        +--> exact diagnostics / .types / .symbols
        +--> temporary consumer adapter for declaration emit and services
```

The precise crate boundary can evolve, but the ownership invariants cannot.

| Upstream concept | Rust representation | Invariant |
|---|---|---|
| AST node pointer | `NodeRef { file: FileId, node: NodeId }` or equivalent | A node is unambiguous across the whole program. |
| Symbol pointer and merges | Program-owned `SymbolId`, tables, declarations, and flags | Imports and merged declarations refer to the same semantic symbol, not a copied type description. |
| `FlowNode` graph | Program/binder-owned `FlowId` arena | Checker flow queries follow antecedents created by binding. |
| `Type` interfaces | Canonical `TypeId` arena plus a complete tagged payload | Identity, recursion, aliases, freshness, targets, and deferred forms survive across files. |
| `Signature`, `IndexInfo`, predicates | Dedicated ID arenas/records | Complete call/construct rules and lazy links are retained. |
| `NodeLinks` / `SymbolLinks` | Dense or sparse ID-keyed side tables | Lazy results and recursion state have one owner and stable cache keys. |
| Type mappers | Explicit mapper records/IDs | Instantiation and inference compose without cloning or stringifying recursive graphs. |
| Checker host callbacks | Narrow program-view trait with normalized checker options | `ts_checker` does not depend back on printer or the entire compiler crate. |
| Type display | Semantic formatter inside `ts_checker` | Diagnostics do not introduce a `ts_checker` -> `ts_printer` dependency cycle. |

Additional architectural decisions:

- Start with one serial binder, one checker, and one semantic store per
  `Program`. Parsing may remain parallel because it produces immutable
  file-local arenas; binding and checking should be serial until stable
  allocation, merge ordering, flow attachment, cache ownership, and
  determinism are proven. Restore binder/checker parallelism only after parity.
- Bind bundled libraries as ordinary source declarations and cache their
  immutable parse/bind inputs. Do not use `TypeDescriptor` as a semantic
  shortcut for libraries or dependencies.
- Keep descriptors only as temporary output views for existing consumers. They
  must not be relation inputs, cache keys, or the cross-file representation.
- Keep mutually recursive checker algorithms in the same crate, organized into
  recognizable modules such as `types`, `links`, `mapper`, `relater`,
  `inference`, `flow`, `jsx`, `grammar`, and source checking.
- Preserve upstream enum/flag ordering where it is observable, including type
  ordering used by unions. If Rust uses a different physical representation,
  encode the upstream canonical comparator explicitly.
- Carry upstream safety limits from the beginning: flow recursion, relation
  depth, instantiation depth/count, conditional tail recursion, union
  cross-product size, and base-constraint depth. These are correctness and
  robustness behavior, not optional performance polish.
- Continue generating AST kinds/schema, diagnostics, bundled libraries, Unicode
  data, and exported flag tables from pinned inputs. Do not hand-port generated
  catalogs.

## Porting rules

These rules apply until frozen-epoch parity:

1. Preserve upstream function names, algorithm comments, decision ordering,
   and source provenance where practical. Prefer boring, comparable Rust over
   an early abstraction.
2. Translate a coherent dependency cluster, not one failing fixture. Every
   cluster has named upstream files/functions, dependencies, tests, and an exit
   gate in the port map.
3. Do not add `todo!`, `unimplemented!`, dummy success, diagnostic suppression,
   `any`/`unknown` fallback, first-candidate shortcut, or legacy-checker call to
   make a ported path compile.
4. Do not delete, ignore, weaken, or accept a test baseline to land a port. The
   only baseline updates allowed are mechanically explained by a recorded
   upstream epoch change.
5. Port observable evaluation order, nil/optional behavior, integer/span
   conversions, cache state, recursion guards, and diagnostic elaboration—not
   only the happy-path result.
6. Keep Rust safe. Use stable IDs, arenas, side tables, explicit worklists, and
   scoped borrows rather than introducing `unsafe` or pervasive interior
   mutability to imitate Go pointers.
7. Keep debug and release behavior semantically identical. Correctness must not
   depend on assertions with side effects.
8. Delay ergonomic renames, abstraction, deduplication, and performance
   rewrites until the relevant full-corpus cluster is exact.

## The parity scorecard

### Canonical manifest

Milestone 0 creates a checked-in, machine-readable manifest for the frozen
epoch. It must reproduce the Go compiler runner's:

- compiler and conformance discovery;
- virtual source units and root-file selection;
- directive parsing and option/config matrix expansion;
- default and explicit library selection;
- hardcoded skips and unsupported legacy configurations;
- submodule accepted/triaged overlay routing;
- expected artifact names; and
- platform-sensitive exclusions.

An unavailable oracle or corpus is a failure, never a passing no-op.

Each run reports, with denominators:

- source cases discovered;
- expanded variants;
- upstream-skipped variants;
- temporarily Rust-unsupported variants;
- variants executed;
- exact passes for complete `.errors.txt`;
- exact passes for `.types`;
- exact passes for `.symbols`;
- expected-clean false positives;
- expected-error false negatives;
- code-set matches that still have span/text/order differences;
- panics, stack overflows, timeouts, and harness failures; and
- results grouped by suite subtree and important compiler-option axis.

Rust-unsupported variants are always visible and count against completion. An
upstream skip is reported separately and does not count as either a Rust pass
or failure.

### Exactness

The primary diagnostic gate is the complete Go `.errors.txt` artifact. A
structured diagnostic diff should additionally isolate code, category, file,
start, length, message chain, related information, and ordering so failures can
be clustered productively. Matching only process exit status, a message header,
or a diagnostic-code multiset is useful triage information but is not a pass.

`.types` and `.symbols` are first-class gates from the beginning. They expose
wrong inference, symbol identity, aliasing, display, and union ordering even
when a fixture has no diagnostic difference. Before the new checker has enough
source traversal to generate complete fixture artifacts, early milestones use
direct semantic-query and graph snapshots on deliberately dependency-closed
programs; unsupported full artifacts remain visible in the scorecard rather
than being counted as passes.

### Test rings

| Ring | Contents | When it runs |
|---|---|---|
| 0: invariants | Arena identity, flags, symbol merging, mapper composition, relation cache/budget, flow graph, and formatter unit tests | Every edit |
| 1: smoke | Existing 27 files plus clean, multi-file, cyclic, TSX, JS/JSDoc, default-lib, Bundler, and NodeNext probes | Every cluster |
| 2: feature shards | Deterministic compiler/conformance buckets tagged by semantic dependency | Before cluster integration |
| 3: full corpus | Every supported frozen-epoch compiler/conformance variant and artifact | At each milestone gate and before cutover |
| 4: projects | Pinned modern project graphs and adversarial stress cases | At useful-checker and release gates |

The fast ring protects iteration speed; only the complete rings establish
parity.

## Milestone plan

Each milestone ends with an objective gate. A milestone is not complete because
its code compiles or because a few newly added examples pass.

### Milestone 0: establish truth and freeze an epoch

Deliverables:

- A maintenance-time manifest exporter driven by the pinned Go harness, so the
  canonical case/config/skip inventory is generated from the oracle rather
  than independently reinterpreted in Rust.
- Correct `ts_fixture` routing for the manifest's Go-owned and submodule
  compiler/conformance cases.
- Faithful execution of the manifest's virtual files, options, libraries,
  expected artifact paths, and accepted/triaged overlay behavior.
- Complete diagnostic, `.types`, and `.symbols` artifact comparison.
- A deterministic manifest and JSON scorecard with explicit denominators.
- Failure if `TS_GO_REPO`, the submodule, the oracle, or expected artifacts are
  unavailable for a requested upstream run.
- A small balanced smoke suite containing both clean and erroneous programs,
  plus multi-file, cycle, TSX, JSDoc, lib, Bundler, and NodeNext cases.
- A port inventory such as `docs/typechecker-port-map.tsv`, with one row per
  upstream function cluster, dependency, Rust destination, owner, state,
  reviewers, and validating fixture buckets.
- One intentional upstream repin, regenerated inputs, recorded behavior
  changes, and a frozen goal commit.

This milestone is deliberately scoped to compiler/conformance semantics. Do
not build a general fourslash, watch, or project-service harness here. It has a
thin unblock gate: as soon as a balanced manifest sample is generated, routed
to Go actual baselines, and fails closed when unavailable, the milestone-1
identity spike may proceed in parallel with full manifest/artifact work.

Gate:

- Two consecutive full discoveries produce the same manifest and denominators.
- The runner can explain every case as executed, upstream-skipped, or explicitly
  Rust-unsupported.
- The checked-in manifest can be regenerated from the pinned Go harness without
  hand-maintained discovery drift.
- A manual sample agrees with the Go runner's selected configs and artifacts.
- The 27 current oracle cases remain exact, and absence of the oracle fails.
- The scorecard records the honest frozen-epoch starting point.

### Milestone 1: program identity, binder, name resolution, and CFG

Deliverables:

- `FileId` plus cross-file node identity.
- A program-owned semantic symbol arena and exact symbol flag/exclusion masks.
- Locals, exports, members, aliases, parent/container links, declaration
  merging, module/global augmentation, strict-mode state, CommonJS state, and
  comment directives.
- One shared lexical/name/reference resolution implementation used by binder
  and checker callbacks; remove the broad "scan every scope" recovery path in
  the new core.
- Binder-created flow nodes, antecedents, branch labels, loop labels,
  assignment/call/condition nodes, exception edges, and container flow state.
- `NodeLinks` and `SymbolLinks` storage with stable IDs and recursion state.

Mandatory architecture probes:

1. a recursive generic exported through a cyclic re-export graph;
2. declaration merging plus module/global augmentation across files;
3. a loop with `break`, `continue`, exception flow, and closure capture; and
4. same-spelling private members from distinct declarations that retain
   distinct symbol/declaration identities; their nominal assignability result
   is gated in milestone 3.

Gate:

- Binder/name-resolution snapshots for the assigned no-lib and module buckets
  match the Go graph, including merge identity and flow antecedents.
- No node or symbol is reconstructed through `TypeDescriptor` in the new core.
- The mandatory probes have stable graph invariants and exact `.symbols` where
  the public baseline exposes them.
- Ring 0/1 stays green in debug and release configurations.

### Milestone 2: canonical type kernel and declared types

Deliverables:

- Faithful `TypeFlags`, `ObjectFlags`, literal/fresh types, unique symbols,
  object/interface/reference/tuple/union/intersection/type-parameter forms,
  deferred indexed/mapped/conditional/substitution/template/string-mapping
  forms, and aliases.
- Complete signatures, parameters, `this`, predicates, minimum argument counts,
  index information, tuple element flags, generic targets, constraints,
  defaults, and variance storage.
- Type/signature/index/mapper arenas; lazy node/symbol/type links; intrinsic and
  global type bootstrap; interning; canonical ordering; recursion guards; and
  cache keys.
- Type mapper composition and instantiation primitives.
- Global/module symbol initialization, declared types of symbols, aliases,
  classes, interfaces, enums, type parameters, object members, and
  `getTypeFromTypeNode` equivalents.
- Standard libraries bound and checked as normal declarations.
- The minimal exact semantic type formatter required by diagnostics and
  `.types` baselines.

Gate:

- Direct declared-type, identity, alias, and formatter snapshots match Go for
  deliberately dependency-closed no-lib programs and a representative
  library-backed program. Complete fixture `.types`/`.symbols` remain a later
  gate until the required source traversal exists.
- Recursive aliases and recursive generic graphs terminate without flattening
  or loss of identity.
- Union/intersection construction is deterministic and passes upstream ordering
  invariants.
- No semantic operation in the new core consumes a string or descriptor as a
  substitute for a type graph.

### Milestone 3: relations, instantiation, inference, and calls

This is the highest-leverage pass-rate milestone and must be implemented as one
vertical slice rather than separate approximations.

Deliverables:

- Identity, subtype, strict-subtype, assignability, and comparability relations.
- Apparent types, constraints, freshness/excess properties,
  private/protected-origin checks, variance, signature relations, discriminants,
  and error elaboration.
- Stable relation caches, recursion stacks, variance markers, and upstream
  overflow/complexity budgets.
- Type instantiation, mapper composition, constraint substitution, and lazy
  resolution.
- The minimum source/expression traversal needed to execute this slice through
  variables, functions, returns, literals, object/array literals,
  property/element access, and call/new expressions. Unsupported expression
  families stay explicit; they do not fall back to a legacy or approximate
  result.
- Inference candidate sets, priorities, fixing/deferred inference, return-type
  inference, contextual inference, and generic defaults.
- Contextual typing for functions, objects, arrays, unions, and overload sets.
- Call/construct signature collection, arity/applicability checks, overload
  ranking, generic calls/constructors, assertions, `satisfies`, and exact
  diagnostic selection.

Gate:

- Dependency-closed feature shards for base structural relations, functions,
  generics, constraints, contextual typing, calls, constructors, overloads,
  accessibility, and excess properties are exact for complete `.errors`,
  `.types`, and `.symbols` artifacts.
- Same-spelling private/protected members from different declarations have the
  exact upstream nominal relation result.
- Adversarial recursive relations terminate at the same semantic budget rather
  than panicking or overflowing the Rust stack.
- No first-signature or one-candidate shortcut remains on a ported path.

### Milestone 4: advanced types and standard-library closure

Representing advanced forms in milestone 2 prevents redesign; this milestone
ports their full construction, reduction, and relation behavior.

Deliverables, in dependency order:

1. tuple optional/rest/variadic behavior and const type parameters;
2. `keyof`, indexed access, index signatures, and
   `noUncheckedIndexedAccess` interaction;
3. mapped and reverse-mapped types;
4. conditional, `infer`, distributive, and substitution types;
5. template literal and string-mapping types;
6. variance calculation, `NoInfer`, intrinsic helpers, and utility types; and
7. global types required by current libraries, including iterator/disposable,
   decorators, import attributes, and `Awaited` families.

Each item includes its branches in relations, inference, contextual typing,
instantiation, type display, and diagnostics. Advanced forms must not be
constructed correctly and then compared by a simplified fallback relation.

Gate:

- The advanced-type and declaration-heavy library shards are exact across all
  three artifacts.
- The checker loads the configured library set without duplicate globals,
  shallow `any` descriptions, or special-case semantic imports.
- Instantiation, conditional-tail, union-cross-product, and base-constraint
  limits match upstream behavior on stress fixtures.

### Milestone 5: source checking, classes, and flow evaluation

Deliverables:

- Complete source/statement dispatch for variables, functions, returns,
  modules, enums, classes, interfaces, control statements, and grammar checks.
- Expression checking for literals, objects/arrays, property/element access,
  operators, calls/new, optional chains, await/yield, tagged templates,
  meta-properties, regular expressions, and contextual expressions.
- Class heritage, `this`/`super`, abstract members, `implements`,
  private/protected/public identity and accessibility, override checks,
  parameter properties, static/instance sides, and initialization.
- Flow evaluation over binder-created antecedents: assignment narrowing,
  discriminants, aliased conditions, predicates, loops/fixed points,
  reachability, definite assignment, closures, exceptions, and
  `try`/`catch`/`finally`.
- Strict option families, especially exact optional properties, unchecked
  indexed access, function variance, bind/call/apply, implicit `this`,
  properties from index signatures, unused checks, and catch variables.
- Diagnostic suppression and expectation directives, with correct unused
  `@ts-expect-error` reporting.

Gate:

- Flow, class, expression, strictness, and control-statement feature shards are
  exact across all three artifacts.
- Clean-file shards have no false positives.
- Loop, closure, exception, predicate, and definite-assignment stress cases are
  exact and terminate deterministically.

### Milestone 6: modern program integration and first useful checker

Deliverables:

- Canonical semantic identity through relative imports, re-exports, cyclic
  graphs, aliases, global/module augmentations, and project-reference inputs.
- Bundler and NodeNext/Node20 resolution semantics as consumed by the checker,
  including package exports/imports, conditions, type-only imports, verbatim
  module syntax, JSON/import attributes, extension rewriting, and unchecked
  side-effect imports.
- Full JSX tag, props, children, intrinsic/component, managed-attribute, and
  generic component checking.
- Standard decorators, `using`/`await using`, `import defer`, top-level await,
  private fields, ES2025, and other modern syntax already parsed by the repo.
- A pinned project suite containing at least:
  - a strict declaration-heavy TypeScript library;
  - a React/TSX application under Bundler resolution;
  - a NodeNext package with conditional exports and type-only boundaries;
  - a multi-package/project-reference graph with cycles and augmentations;
  - a strict project using advanced generics and current standard libraries;
  - a modern JavaScript/JSDoc/CommonJS package; and
  - clean as well as intentionally failing variants.

Project comparison includes loaded source/library graph, resolved modules,
compiler exit status, and complete diagnostics—not only whether both compilers
exit successfully.

Gate:

- Every pinned modern project is exact against the frozen Go compiler.
- No project uses the legacy semantic core or per-feature fallback.
- The new checker is ready for explicit opt-in and shadow comparison on normal
  CLI use, but the production default remains unchanged until the full corpus
  gate and atomic cutover.

### Milestone 7: full supported corpus closure

Deliverables:

- Complete grammar and semantic diagnostic selection, chains, related spans,
  suppression, and ordering.
- Remaining checker APIs needed for `.types`, `.symbols`, declaration
  serialization, emit resolver, and language-service consumers.
- Current Corsa-supported JavaScript, JSDoc, CommonJS, JSX, and module behavior.
  Do not restore legacy behavior intentionally removed in upstream `CHANGES.md`.
- Failure clustering by root algorithm rather than fixture-by-fixture patches.
- Closure of every Rust-unsupported compiler/conformance row in the manifest.
- Readiness for the atomic default-checker cutover; production selection is not
  changed inside a partial feature cluster.

Legacy module/target configurations that the Go compiler runner itself skips,
such as some Node10/Classic, AMD/UMD/System, `outFile`, and ES5 combinations,
are not on the modern-project critical path. They remain visible as upstream
skips and can be addressed in a later compatibility goal if upstream enables
them.

Gate:

- Every upstream-supported frozen-epoch compiler/conformance variant has exact
  complete `.errors`, `.types`, and `.symbols` artifacts.
- There are zero Rust-only unsupported variants, crashes, unexplained timeouts,
  and accepted Rust-only differences.
- All local rings and consumer tests pass.

### Milestone 8: cutover, cleanup, performance, and roll-forward

Deliverables:

- Switch the production default to the new checker atomically, then remove the
  legacy checker selection and `TypeDescriptor` semantic bridge.
- Retain only explicit output adapters required by declaration emit or services,
  with canonical IDs remaining the source of truth.
- Split remaining oversized modules along the already proven upstream clusters;
  then perform narrowly reviewed idiomatic Rust refactors.
- Re-enable safe parallel binding/checker pooling only with measured ownership,
  determinism, and no cross-checker type mixing.
- Benchmark representative modern projects for wall time, peak RSS, cache size,
  stack depth, and pathological inputs. Correct double checking, repeated
  library parse/bind work, descriptor cloning, quadratic union deduplication,
  and uncached relation paths.
- Port the accumulated upstream drift batch, update generated inputs, and rerun
  every scorecard ring.

Gate:

- Frozen-epoch parity remains exact after cleanup and optimization.
- The selected roll-forward epoch's complete core semantic delta and all
  previously passing frozen-epoch artifacts are exact. A drift audit with
  unported core changes does not satisfy this gate.
- Workspace format, targeted tests, full workspace tests, and clippy pass in
  debug and relevant release paths.
- No old semantic implementation is reachable in production.

## Execution model

### Work inventory

Before broad implementation, build the port map from upstream packages and
functions rather than from local failing fixtures. At minimum it should cover:

- binder, symbol flags, name resolver, reference resolver, and flow creation;
- checker host/state, semantic links, type representation, and mappers;
- declared/type-node resolution and global initialization;
- relater, inference, instantiation, overloads, and expression checking;
- flow evaluation, grammar checks, JSX, exports, and utilities;
- type formatting and the emit/service-facing query surface; and
- relevant compiler/options/module/AST contracts and generated inputs.

Each row has exactly one state: `unmapped`, `blocked`, `porting`, `review-1`,
`review-2`, `fixing`, or `verified`. "Implemented" without both review and an
artifact gate is not a terminal state.

### Four-lane collaboration

With four active work slots, use dependency-aware waves rather than allowing
four agents to patch the monolithic checker simultaneously:

1. **Oracle/integration lane:** harness, manifest, scorecard, exact formatter
   support, failure clustering, and integration runs.
2. **Binder/identity lane:** AST identities, symbols, name resolution, links,
   and CFG construction.
3. **Type-system lane:** type kernel, mappers, relations, instantiation,
   inference, and advanced types.
4. **Review/fixer lane:** independent semantic comparison with Go, Rust
   ownership/budget review, compiler integration, and fixes.

The lanes change roles as dependencies clear. They should use separate
worktrees or non-overlapping modules and integrate small coherent commits.
Cargo-heavy verification should use the repository's capped runner and one
integration lane to avoid memory contention.

### Review loop for every cluster

1. The implementer records the exact Go functions, dependencies, and fixture
   bucket, then ports the cluster without semantic shortcuts.
2. Reviewer 1 compares Rust and Go side by side for missing branches,
   evaluation order, nil behavior, flags, caches, diagnostics, and budgets.
3. Reviewer 2 reviews stable identity, borrowing, arena ownership, recursion,
   determinism, and tests independently.
4. A fixer resolves both reviews; reviewers do not merely approve their own
   implementation.
5. Ring 0/1 and the cluster's Ring 2 shard run before integration.
6. The integration lane runs the full scorecard gate and records the delta by
   artifact and root-cause cluster.

Compiler errors are useful work queues; they are never license to add dummy
returns. A cluster that cannot be completed should remain visibly blocked in
the port map rather than being represented as a compiling stub.

## Risk register

| Risk | Early signal | Mitigation |
|---|---|---|
| Wrong oracle or denominator | Green run with missing corpus; Rust matches JS but not Go | Milestone 0 manifest, Go actual-baseline routing, fail closed, explicit overlay/skip accounting |
| Semantic identity is lost at a boundary | Cycles, aliases, augmentations, or private members differ | Program-owned IDs; no descriptor/string relation inputs; mandatory identity probes |
| Feature patches recreate the current plateau | Growing special cases and fixture-name conditionals | Work from upstream function clusters; two-source reviews; no per-feature fallback |
| Relations/inference are split into incompatible approximations | Calls pass but generic/contextual variants fail unpredictably | Treat relation, mapper, inference, contextual typing, and overload selection as one milestone slice |
| Go recursion works but Rust overflows or hangs | Stack overflow, exponential unions, non-deterministic timeout | Port explicit upstream budgets early; use iterative worklists where representation-neutral |
| Checker creates crate cycles | `ts_checker` reaches into printer/compiler/module internals | Narrow `CheckerHost`; normalized options; semantic formatter stays in checker |
| Upstream drift invalidates months of work | Frequent generated/baseline churn | One frozen epoch, drift ledger, one required roll-forward after parity |
| The old checker leaks into new results | Suspiciously green unsupported features | Whole-checker selection only; provenance assertions in test builds; delete legacy path at cutover |
| Standard libraries dominate runtime/memory | Repeated parsing/binding and shallow library types | Cache immutable lib inputs; check libs normally; optimize only after identity is correct |
| Exact output work is postponed | Code-set matches but `.types`, spans, or messages diverge broadly | Full artifacts from milestone 0; formatter and elaboration ported alongside each cluster |
| Modern demos pass while the corpus remains weak | Handpicked projects green, feature shards red | Modern-project gate is milestone 6; full corpus closure remains a separate mandatory gate |

## Definition of done

This goal is complete only when all of the following are true:

- A recorded upstream epoch and reproducible manifest define the oracle.
- Every compiler/conformance configuration supported by that Go runner is
  executed or reported as an upstream skip; Rust has no private skip list.
- Complete `.errors.txt`, `.types`, and `.symbols` outputs are exact for every
  executed variant.
- Expected-clean files, expected-error files, diagnostic chains, related
  information, union ordering, and symbol/type display are all covered.
- The modern project suite matches source graph, resolution, and diagnostics.
- Program-wide symbols, flow nodes, types, signatures, mappers, and semantic
  links have canonical stable identity.
- Default libraries use the ordinary semantic path.
- The new checker contains no legacy fallback, placeholder semantic success,
  or unexplained `any`/`unknown` escape hatch.
- Recursive/adversarial programs respect explicit budgets without panic,
  overflow, nondeterminism, or unexplained timeout.
- All local tests, full workspace tests, formatting, and clippy pass; the six
  compiler failures observed in this audit are resolved or deliberately moved
  to a separately approved non-typechecker goal.
- One controlled upstream roll-forward has exact core semantic results and has
  demonstrated that the port can be maintained without re-deriving its
  architecture.
- The port map has no unverified row in the core checker/binder/name/flow/type
  dependency closure.

## First implementation tranche after approval

The first build tranche should be deliberately small and proof-oriented:

1. Generate a balanced compiler/conformance manifest sample from the pinned Go
   harness and repair its Go actual-baseline routing.
2. Make missing-oracle runs fail and emit a sample scorecard.
3. Once that thin oracle slice is verified, work in parallel:
   - expand the Go-derived manifest and complete diagnostic plus skeleton
     `.types`/`.symbols` artifact accounting; and
   - implement the program identity spike (`FileId`/node refs, canonical
     symbols, semantic side tables) and the four mandatory milestone-1 probes.
4. Record the honest frozen-pin baseline and cluster the largest failures.
5. Create the upstream function/cluster port map.
6. Review the identity spike against the Go architecture before scaling binder
   work.

That tranche answers the two highest-risk questions early: whether progress can
be measured honestly, and whether the Rust ownership model can preserve the
semantic identities on which the rest of TypeScript depends. If both pass,
the remaining work is large but straightforwardly decomposable.

## After this goal

Once the semantic core is exact and stable, the broader port should continue
along the existing dependency spine:

1. complete declaration emit and emit-resolver/node-builder behavior;
2. complete transforms, JavaScript emit, source maps, and output modes;
3. incremental/build mode, project references, and watch mode;
4. language-service, project-service, fourslash, LSP, and native API parity; and
5. performance/concurrency work across the complete compiler pipeline.

Those phases will be much safer once they consume a canonical checker rather
than compensating for a lossy semantic model.
