# Goal: typescript-go core typechecking parity in Rust

- Status: active
- Audit date: 2026-07-15
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
- Program diagnostics preserve their exact catalog category through the
  compiler boundary and the fixture runner consumes it in complete non-pretty
  `.errors.txt` artifacts.
- Exact diagnostic comparison is integrated with column-zero directive parsing,
  pinned option matrices and skip rules, exact configured baseline identity,
  and fail-closed guards for unmodeled roots, projects, options, related
  information, and pretty output. In a pinned first-50 run it reported 26 exact
  artifacts, three explicit unsupported variants, and 21 honest checker gaps.
- Canonical `TypeFlags`, `ObjectFlags`, signature flags, tuple/index flags, and
  relation ternary values are pinned to the audited upstream commit.
- Program-wide node and flow references are branded by both `NodeArenaId` and
  `FileId`, so equal dense IDs from rebuilt Programs fail closed. Complete
  symbol masks, the typed flow substrate, and the first exact binder-created
  CFG slices are integrated as well. Sequential flow, branches, returns,
  mutations, calls, unreachable traversal, detached function containers,
  while/do/classic-for/for-in/for-of loops, and labeled or unlabeled jumps are
  active. Switch/case flow now includes exact clause ranges, empty-clause
  grouping, fallthrough, default/no-default joins, nested break restoration,
  and source-order clause traversal. Try/finally, optional/logical chains,
  destructuring, direct-call boundaries, and static blocks remain explicit
  incomplete boundaries rather than guessed graphs.
- Canonical semantic IDs plus signature, predicate, index, and tuple records
  are integrated behind a store-branded aggregate. AST scope growth is
  monotonic, raw payload allocation is crate-private, and independent review
  proved that equal local IDs from another store cannot enter any public
  record slot.
- The complete canonical type-payload graph is integrated. Every upstream
  `TypeData` family has an explicit store-owned record instead of a descriptor,
  with exact byte-backed names, immutable unique-symbol identity, atomic
  interface/tuple `this` initialization, validated instantiation caches, and
  exact union-discriminant cache states. Two semantic review rounds and 36
  focused graph tests closed the reachable invalid states found during audit.
- The program-symbol ownership boundary is integrated: `ts_binder` owns the
  exact symbol/table substrate and `ts_checker::SemanticStore` consumes and
  embeds that owner under one immutable semantic brand. The graph landed as
  eight reviewable commits through `b6c058e` and passes 86 binder tests, 196
  checker tests, the all-target workspace check, and strict targeted Clippy.
- Generated AST child traversal now covers all 192 `NodeData` payload variants
  and all 420 declared child slots in pinned order. This removes hand-maintained
  structural traversal as a source of silent binder/checker omissions, while
  keeping binder-specific flow order as a distinct contract.
- The first sparse-link slice is integrated as `c1863d0..f82e28d`. It covers
  nine common upstream stores plus all ten live type-resolution property probes,
  exact field-specific sentinel domains, and an opaque store-branded LIFO
  boundary. The dependency-closed mapper kernel is integrated as `ceb51a0` with
  exact simple, array, array-to-single, merge, prepend, and append semantics;
  callback-, instantiation-, and inference-owned mapper variants remain
  explicit later dependencies. The combined semantic stack passes 219 checker
  tests, strict targeted Clippy, and the all-target workspace check after two
  independent reviews. The canonical B01 traversal is integrated as
  `a7d9159..a6a63bb`: one flow-driven recursive walk now owns exact enter/exit
  state, container order, and full ordinary-child discovery even across
  unsupported flow boundaries. It preflights root identity, kind/data pairs,
  and every parent backlink before store mutation; preserves nil locals; and
  prevents its symbol owner from reaching the checker until B02 declarations
  complete. The merged stack passes 99 binder and 219 checker tests plus strict
  binder Clippy and the all-target workspace check.
- The dependency-closed `NewChecker` bootstrap is integrated as
  `9e50ec6..01c5a92`. It creates the exact checker transient symbols,
  `globalThis` table cycle, intrinsic/literal/union/template/anonymous marker
  types, predicates, sentinel signatures, and index infos through `typeofType`,
  including strict-null/exact-optional identity splits and the populated
  literal, union, and template caches. Initialization is one-shot and rejects
  preexisting checker arenas, sparse links, resolution history, or transients
  while accepting the real prebound binder graph, including private-name
  global IDs. Eight focused bootstrap tests and all 227 checker tests pass; an
  independent review found no semantic issue. Callback-owned function mappers
  and Program/global-library initialization remain explicit later slices.
- The B02a canonical declaration primitive is integrated as
  `7959d30..bc4d0ab`. It ports the pinned declaration insert, compatible merge,
  replacement, conflict, diagnostic, value-declaration, and parent-link state
  machine; exact computed/default/private/ambient/assigned names; and atomic
  exported local/export symbol pairing. JavaScript-only assigned names remain
  behind an explicit file-kind boundary rather than guessed from syntax. The
  merged stack passes 113 binder tests, all 227 checker tests, strict binder
  Clippy, and the all-target workspace check. Independent review found no
  P0-P2 issue. Full source facts, declaration-family dispatch, and table
  routing are the active B02b slice, so checker extraction remains closed.
- T01b is integrated as `182e591`, expanding the canonical sparse checker
  state from 9 to 23 of the pinned checker's 26 typed LinkStores. The 14 new
  records cover assertion, array/switch/JSX, mapped/deferred/module/late/export,
  members/exports, spread, variance, reverse-mapped, and assignment caches with
  exact defaults, nil-versus-allocated-empty states, byte-backed name keys, and
  atomic provenance validation for every ID-bearing slot. Bootstrap pristine
  checks include every landed store, all 229 checker tests pass, and targeted
  Clippy is clean with only the recorded baseline allowances after moving one
  enlarged test collection off the stack in `670a20e`. An independent final
  audit found no P0-P2 semantic issue. Enum-member, containing-symbol, and
  source-file links remain explicit richer follow-ups.
- B02b's source contract is integrated as `d58d523`: canonical binding now
  retains a caller-derived byte-backed source symbol name plus explicit
  JavaScript, declaration-file, external-module, and CommonJS facts. It never
  infers those Program/parser facts from a filename or AST shape.
- Canonical class-constructor parsing is integrated as `85dab99`, with binder
  cleanup in `1be603c`. Real constructors now use the generated
  `ConstructorDeclaration` payload while generators, computed/private names,
  and optional/generic quoted `constructor` methods remain ordinary methods.
- B02b ordinary non-JavaScript declaration dispatch is integrated as
  `dddd6db..ca759ef`. It linearly replays B01's captured order for global and
  external TS/TSX/d.ts files, preserving lazy locals/members/exports, exact
  declaration flags and exclusions, class prototypes and parameter
  properties, destructuring, anonymous/signature symbols, and exported
  local/export pairs. Unsupported module, namespace, import/export alias, and
  assignment families reject the whole file before writes and remain stable
  on retry. Independent pinned-source review is clean after its constructor
  repair and accessor-recovery correction; 117 binder and 236 checker tests
  pass. The file remains honestly in `Traversal`, and checker extraction stays
  gated while B02c ports those module/alias families.
- R00a's relation-state substrate is integrated as `9bd331d`: exact flag/result
  widths, five distinct lazy relation caches, nil-versus-allocated map state,
  directional enum keys over canonical global symbol IDs, the signed
  `(16_000_000 - size) / 8` budget, and bootstrap pristine-state accounting.
  Its independent audit found no P0-P2 issue. Relation-key generation,
  recursion identities, simple relations, and structural relation algorithms
  remain intentionally absent rather than approximated.
- The later declaration/name-resolution wave supersedes the active-slice
  descriptions above. B02 is now verified through `d1d6182`: non-JavaScript
  TypeScript declaration dispatch includes modules and namespaces, import and
  export aliases, modern import phases and recovery, TypeScript expando
  assignments, and exact ambient export context. Independent reviews plus the
  integration gate pass 143 binder tests, 25 focused import tests, strict
  parser Clippy, and the all-target workspace check. B03's ordinary lexical
  and module resolver landed as `b7e6e1b`, with the complete optional-location,
  file-independent global, and checker-created synthetic-scope repair in
  `676d9a0`. Independent review found and verified the bounded `a6bc09d`
  follow-up for recovered constructor bodies and synthetic-parent provenance.
  B03 is now verified with 152 binder tests and strict binder Clippy green.
- All 26 sparse checker LinkStores are represented through `ae84673`, with the
  exact enum evaluator value domain repaired in `ba9eaf1`. The final boundary
  repair landed as `7c95a62` and `4cc18ba`: isolated entity names now use the
  exact sealed JS parser path, sentinel IDs have one canonical state, source
  facts enforce every specialized call domain including `instanceof`, and
  flag negation/setters admit only defined bits. Two independent audit rounds
  are clean across fields, lazy state, evaluator values, SourceFileRef and AST
  provenance, and pristine accounting. T01 is verified with 253 checker tests,
  two focused isolated-parser tests, and no change to the known 175/179 parser
  recovery baseline.
- R00b is integrated as `4be3a12` and has completed an independent clean
  audit. Exact simple/generic relation-key bytes, XXH3-128 encoding,
  depth-four parameter recursion, constraint fail-closed behavior, recursion
  identity precedence, and compatibility with the five lazy relation caches
  all match the pinned Go implementation. General simple and structural
  relation algorithms remain the next R00/R01 work rather than being implied
  by the completed key substrate.
- Binder-owned `NodeFlagsContainsThis` side facts are integrated as `2f14c19`.
  The exact bit-7 capture/propagation state machine is retained outside the
  immutable AST and all 157 binder tests pass. This closes the direct-`this`
  input needed by interface declared types without guessing from syntax during
  checker construction.
- T05A's declared type-parameter and class identity slice is verified through
  `53c869e` and the independent cache-integrity repair `bc65b06`. It preserves
  outermost-to-innermost plus local type-parameter order, class/interface merge
  precedence, early recursive shell publication, the owning-class synthetic
  `this` parameter, exact self-instantiation identity, exported-symbol routing,
  and fail-closed cache validation. Twenty focused tests and all 279 checker
  tests pass, and the final independent audit found no P0-P2 issue. Alias,
  enum, reverse-mapped, and JSDoc declared types remain explicit later T05
  slices. Program-wide merged-symbol identity is closed by the later T04B1
  consumer work described below.
- T05B's dependency-closed interface declared types are verified through
  `e83f0df`, with merged-symbol consumer canonicalization in `aafbdbe` and the
  cached direct-identifier heritage extension in `af20ef6`. Generic and
  direct-`this` interfaces publish the exact recursive reference shell and
  synthetic `this`; definitely `this`-less interfaces use the plain interface
  identity; merged outer and local parameters preserve pinned ordering and
  symbol identity; invalid non-entity heritage is ignored; and every raw merged
  class/interface symbol shares the canonical transient's exact declared
  `TypeId` and cache entry. A private post-global capability now permits the
  narrow `isThislessInterface` path to resolve a direct identifier whose base
  identity is already cached, preserving thisless bases, propagating synthetic
  `this`, and treating missing or non-interface bases like the pin. Public or
  pre-global hosts fail atomically, as do uncached recursive, qualified, and
  alias-dependent heritage paths. Thirty-six declared-type tests and the
  expanded 339-test checker suite pass. Independent pinned-source audits found
  no remaining P0-P2 issue. The recursive direct-identifier follow-up is now
  integrated through `9ff7991` and `5b30edb`: uncached interface graphs publish
  root-first shells, terminate self and mutual cycles, preserve the pin's
  order-sensitive active-shell behavior, propagate real and synthetic `this`,
  and leave base-type caches untouched. Pure class bases force a derived
  interface reference without allocating the class identity. The independent
  review found no P0/P1 defect, and all 44 focused declared-type tests pass.
  Qualified/alias heritage plus alias, enum, reverse-mapped, and JSDoc declared
  families stay explicit follow-up work rather than being approximated.
- T04B0's production construction boundary is verified through `21e69fb`,
  `0005257`, and `a426cd9`. It consumes declaration-complete binder ownership,
  validates exact file/arena/root/source-fact correspondence and exact bound
  root closure, preserves explicit Program order, registers source roots, and
  bootstraps intrinsics without exposing partial state. A generated monotonic
  `NodeArenaRevision` makes every post-bind AST mutation observable; production
  construction, declared-type hosts, and canonical name-resolution hosts all
  reject stale snapshots before semantic writes or host callbacks. The repair
  and consumer audit are clean, 160 binder and 299 checker tests pass, and the
  all-target workspace check is green. T04B1's dependency-closed global merge
  phase is integrated through `42cf18f`, `aafbdbe`, `f87d457`, and `513e7e4`.
  It ports exact symbol clone/merge/table semantics, validated one-hop
  merged-symbol redirects, explicit Program-order script globals, deferred
  ambient-module and wildcard queues, UMD globals, global-scope augmentations,
  and the `undefined`/`globalThis` initialization branches. Declared
  class/interface consumers and the production name resolver canonicalize
  through those redirects, and only a completed checker context can construct
  the resolver host. Three local bundled-library fixtures are byte-identical to
  the pin and exercise the same production path. The merge substrate's
  independent audit found no P0-P2 issue. The eager global-library follow-up is
  integrated in `af20ef6`: intrinsic value links, IArguments, Array, Object,
  Function, strict CallableFunction/NewableFunction selection, String, Number,
  Boolean, RegExp, Array<any>, the unique auto-array marker, ReadonlyArray,
  ReadonlyArray<any>, and ThisType now initialize in pinned order. One-argument
  generic references reuse the target cache and propagate flags; no-lib and
  malformed-library inputs retain pinned fallbacks, resolved-member state,
  diagnostic order, declaration locations, and eager-name library arguments.
  A private global-merge completion brand prevents heritage name resolution
  from escaping before its phase. The independent eager-global audit found and
  closed that phase hole plus the auto-array resolved-members mismatch, then
  reported no remaining P0-P2 issue. The prior milestone passed 162 binder
  tests, 339 checker tests, the checker compile-fail doctest, strict targeted
  Clippy, and the all-target workspace check. Compiler-option normalization now
  retains explicit `strictBindCallApply` provenance and exact inheritance
  through `653017f`; `strictBuiltinIteratorReturn` has the same normalized
  strict inheritance, explicit-option provenance, canonical-context retention,
  and CLI routing through `1fdb98b` and `837ff93`. Binder output retains whether
  each module augmentation was declared in an ambient context through
  `aaeb11f`. The canonical merge diagnostic host is integrated through
  `55b7213` and `680ec4b`, preserving each pinned branch's unconditional Add
  versus Lookup ownership, related-information equality, and raw issuance
  order. AST-adjusted diagnostic locations, JavaScript suppression, checker
  symbol spelling, and final compiler sorting remain owned by later Program
  diagnostics. The declaration-provider-independent alias kernel is integrated
  through `653272f`, `270c984`, and `c4c316a`: immediate and transitive caches,
  missing-target negative caching, pure and assignment indirection, merged
  targets, type-only propagation, TS2303 unwind events, retry semantics, and
  transactional resolution-stack rollback all passed two independent reviews.
  Fourteen focused alias tests and all 376 merged checker tests pass. T04
  remains in progress: the production alias-declaration target provider and its
  name-resolution/merge wiring, late ambient-module merging, non-global
  augmentation execution, full Program diagnostic elaboration, callback
  mappers, lazy global families, and complete compiler-to-canonical option
  plumbing are explicit later slices.
- The alias path now extends through combined symbol meanings, immutable
  module-resolution facts, and a production plain-TypeScript ESM target host.
  `c7c1355` ports the pinned `getSymbolFlags`/`getSymbolFlagsEx` loop;
  `69bad00` retains and validates an exact, node-keyed module-resolution
  manifest; and `e2510d0` plus the independently reviewed boundary repair
  `2215e61` resolve namespace imports, named imports, and named re-exports to
  raw immediate targets. Direct-default namespace wrappers, default/local/star
  and export-equals paths, CommonJS, JavaScript, missing manifest states, and
  synthetic-module interop fail with typed retryable boundaries. Type-only
  markers publish at the pinned syntactic point even when later target lookup
  fails. Production-context orchestration and alias-aware lexical lookup remain
  the next T04 consumer slices.
- R00/R01 now have a usable exact base relation path. `d1f782f` and `c002752`
  port the pinned fast/simple identity, subtype, strict-subtype, assignability,
  comparability, literal, primitive, enum, nullable, unknown-like-union, and
  cache-read branches. `fb420e2` adds uncached assignability for fully resolved
  ordinary interface/type-literal property objects, including directional
  relation keys, `Maybe` recursion, expansion and complexity budgets,
  transactional cache publication, weak-target common-property checks,
  optional-property semantics inside the supported nullability boundary, and
  validated global `Object` fallback. Signatures, indexes, nominal members,
  strict optional unions, generic structures, and other structural families
  still fail typed rather than becoming false relations. The independent audit
  found no P0-P2 issue, and all 29 focused relater tests pass on the merged tree.
- T05/T06 now resolve useful declared aliases and source type nodes through
  `8c2dc7d`, `22801bd`, `5938420`, `aed8638`, and `42fef2b`. The context-owned query
  session supports intrinsic keyword and parenthesized nodes, non-generic
  direct identifier references, recursive generic and non-generic type aliases
  inside the installed boundary, and exact string/template, number, bigint,
  boolean, null, and unary-minus literal type nodes. Literal queries preserve
  upstream regular/fresh pairs, cross-node interning, operand-before-result
  allocation, `+0`/`-0` cache identity, signed bigint behavior, null's link
  bypass, checked batch capacity, and atomic retry. The literal audit found no
  P0-P2 issue under the parser/binder/revision-validated production contract.
  Direct generic aliases now substitute dependency-closed primitive, literal,
  union, and type-parameter arguments through nested aliases and earlier or
  outer-lexical defaults. Their provided-arity/owner cache keys match the
  pinned encoding, warm caches are validated without mutation, and TS2314,
  TS2707, and TS2315 preserve nested-argument-first order. Structured generic
  bodies, constraints, intersections, object/function types, qualified/import
  aliases, and circular-default TS2716 remain explicit follow-up work.
- T04's production query boundary now has one retained alias/source registry
  through `7b0712a`, `17b12f2`, and `85e5005`. It owns the validated Program
  snapshots, module-resolution manifest, alias target facade, and store-branded
  source-file tokens. `2c93541` makes declared-type and name-resolver hosts
  borrow that registry in O(1), including nested type references, recursive
  heritage, and global-library initialization; repeated queries no longer
  rebuild Program-wide maps or rescan sources.
- T07's semantic formatter is integrated through `9d61038`, `763361f`,
  `96fb33a`, and `daf9a9d`. Primitive, nullish, unique-symbol boundary,
  complete string/number/bigint literals, and canonical primitive unions now
  display inside `ts_checker`. The independently reviewed union slice preserves
  named aliases, denormalized origins, boolean collapse, nullable tail order,
  the pinned approximate-length/elision algorithm, exact ordinary versus
  `noErrorTruncation` byte budgets, and typed malformed/cycle failures without
  formatter writes. Symbol-aware objects, functions, generic aliases, and
  qualified names remain explicit follow-up work.
- T06 and R01 now share a canonical primitive-union kernel. `af6096e`,
  `745fad1`, and `841dfd2` port parsed union type nodes, flattening,
  deduplication, literal reduction, nullable precedence, named origins, exact
  cache identities, recursive alias cycles, transactional preparation, and a
  dirty-only validation barrier whose lazy relation/member memo flags stay
  O(1). Independently reviewed `ca22d61` ports the pinned SOME/EACH branch
  order for identity, subtype, strict subtype, assignability, and comparability,
  plus nullable correspondence, literal-to-primitive shortcuts, named-union
  identity, cache thresholds, and transactional publication.
- The independently reviewed direct-generic slice is integrated as `42fef2b`
  with exhaustive capability/invariant classification in `38ba576`. Review
  found and repaired exact-key poisoning, cached forward-default validation,
  recursive-default stack overflow, a double merged-symbol redirect, and an
  immutable-validation attempt to allocate a global symbol ID. The final
  merged stack passes 560/560 checker tests; checker, parser, binder, and
  compiler scoped Clippy/rustdoc/doctest gates are green. Circular defaults
  intentionally remain a typed capability boundary instead of emitting
  pinned TS2716.
- E00's first production source-checking slice is integrated through `625c143`,
  `101fb48`, `0afc838`, and `42fef2b`. One context checks retained source files after a
  complete-tree provenance preflight, supporting unmodified type aliases,
  exact empty `export {}` module markers, and explicitly typed ordinary
  variables (optionally exported) whose initializers are primitive literals.
  Target types include named, anonymous, nullable, and literal unions plus
  dependency-closed direct generic aliases and defaults.
  Successful checks publish an idempotent source marker and exact TS2322 nodes,
  order, alias display, and strict-null behavior; failed plans publish neither
  marker nor diagnostics, and retry diagnostics stay privately partitioned by
  their owning source. Export syntax requires a retained external-module fact,
  preventing a caller from silently checking it in global Script scope.
  Unsupported statements and expressions remain typed boundaries with no
  legacy fallback. The combined stack passes all 560 checker library tests;
  its formatter and export-source reviews found no remaining P0-P2 issue, and
  rustdoc, the compile-fail doctest, and scoped all-target Clippy are green.
- C00's first whole-Program route is integrated through `32d22b7` and exposed
  to the fixture oracle through `439e652`. The explicit
  experimental constructor retains the ordinary Program graph and diagnostics
  but suppresses legacy binder/checker semantics, preflights every source fact,
  performs canonical traversal for all files before declaration replay, and
  creates one local `CanonicalCheckerContext` borrowing the Program's arenas.
  Only owned diagnostics cross that scope, and they are appended only after
  every eligible source succeeds; a later unsupported file therefore discards
  all earlier semantic work. Emit is explicitly refused. The initial admitted
  source-fact boundary is conservative: unambiguous `.ts` plus bundled library
  declarations; TSX, fixed `.mts`/`.cts` formats, `import.meta`, Node implied
  formats, and unskipped non-default declarations fail typed before canonical
  binding. The independent facts re-review found no remaining P0-P2 issue, and
  all eleven canonical Program tests pass on the merged branch. The diagnostics
  runner's explicit `--canonical-checker` mode never emits or falls back to the
  legacy checker. It records genuine capability gaps as unsupported coverage,
  aborts on provenance/cache/phase invariants, and writes schema-4 scorecards
  with an explicit `checkerMode` and nested related records. The actual pinned
  12,750-case oracle discovers and checks `simpleTestMultiFile.ts` byte-for-byte
  exactly, including both TS2322 paths, spans, messages, and order. Canonical
  Program conversion now
  validates and owns same-file and cross-file related records without adding
  them to the top-level diagnostic stream. Program-level diagnostic
  sorting/deduplication, full modern module facts, and canonical emit remain
  explicit follow-up work.
- The first broad canonical corpus tranche now completes instead of aborting on an
  AST invariant. `cb6cdaf` makes optional-parameter ranges contain their `?`,
  and `0a54a21` parses expression-position `undefined` as the pinned identifier
  while retaining keyword-type shape in type position. The first 500 selected
  cases execute 536 variants with zero fatal invariants, two exact matches,
  533 explicit unsupported results, and one supported-path mismatch: lossy
  lone-surrogate string identity. This ordering-biased tranche is dominated by
  JavaScript (84), classes (79), functions (69), untyped variables (46),
  modules (32), interfaces (29), import-equals (28), enums and TSX (19 each),
  and imports (15). It is a root-algorithm queue, not a parity percentage.
- The first property-object vertical slice is integrated through `5916c00`,
  `8e3e52e`, `20fe648`, `9aad5c7`, `680b444`, and the source/compiler seams
  `d33373c..7d74866`. Canonical queries now construct property-only type
  literals, simple no-heritage interfaces, and nested object literals with
  exact binder-owned raw members, checker-owned transient property clones,
  resolved member tables, owner identity, propagated object flags, recursive
  interface shells, and warm-cache validation. Assignability consumes that
  representation without descriptors; the formatter prints named interfaces,
  named object aliases, anonymous structures, optional/readonly members,
  nested objects, and pinned property elision. Source checking can therefore
  complete and issue deterministic TS2322 diagnostics for supported object
  assignments instead of stopping at a display boundary. The merged slice
  passes 609 checker library tests, 163 binder tests, strict scoped Clippy,
  rustdoc, and doctests. Contextual property widening and pinned object-literal
  elaboration (property-local incompatible, excess, and missing diagnostics)
  are the next active dependency cluster; unions, indexes, spreads, computed
  names, generic object bodies, and interface heritage remain typed boundaries.
- Contextual object-property typing is integrated as `b1f6922`, with the
  independently reviewed spelling-suggestion kernel in
  `e1d8388..fa75449`. Object initializers now preflight the complete
  host-validated target graph before publishing a source object; mutable
  property locations widen fresh literals to primitives unless a same-kind
  literal context preserves the regular literal, including canonical boolean
  unions and recursive interface contexts. The shared ordered property view
  validates owner, declaration, alias, member-table, and link provenance and
  is frozen for diagnostic elaboration. The spelling kernel retains the
  pinned Go byte-versus-rune gates, weighted distance, stable tie ordering,
  and Unicode 15 behavior; independent review found and pinned all 55 newer
  Rust Unicode 17 case pairs. The combined branch passes 628 checker library
  tests, strict all-target Clippy, rustdoc with warnings denied, and doctest.
  A bounded seven-case property-object corpus probe found two exact artifacts,
  three honest syntax boundaries, and two remaining supported-path mismatches;
  both mismatches are now isolated to generic TS2322 versus pinned
  property-local excess diagnostics. Exact object-literal diagnostic
  elaboration is therefore the active cluster, with simple assignment-statement
  dispatch being traced independently behind the same frozen contracts.
- The object-diagnostic and direct-assignment wave is integrated through
  `2ff2d4f`, `a65912f`, `3d636ec`, and `86ba585`. Failed property-object
  assignments now follow the pinned elaboration order for known-property
  mismatches, nested errors, excess/spelling diagnostics, and one/many missing
  properties, including exact primary spans, related-information order,
  suppression, TypeToString flags, and whole-batch diagnostic staging. TS6500
  suppression consumes the exact Program-owned default-library fact rather
  than a filename or same-file heuristic. Independent review also exposed and
  closed the legal base-types-warm/members-cold interface state and the global
  `interface Object` plus value-side `var Object` merge without a name-based
  bypass. Top-level direct assignments to unique, explicitly typed and
  initialized same-file `var` declarations now reuse the same contextual
  object and relation path; Script-global, hoisted, and exported symbol routing
  is provenance-checked, while aliases, block-scoped, inferred, merged, and
  cross-file targets remain typed boundaries. The merged checker passes
  655/655 library tests and strict checker/compiler Clippy. Pinned corpus
  artifacts for `contextualTyping16`, `contextualTyping17`,
  `contextualTyping2`, and `objectLitStructuralTypeMismatch` match exactly;
  the first two prove zero diagnostics and the sole TS2353 over `name` at
  `[46,50)` respectively. Arrays/assertions, calls, functions, and broader
  assignment targets are the next dependency clusters.
- The assertion and canonical-array substrate is integrated through `54101e4`,
  `561382e`, `7df90aa`, `141e802`, `324d1b8`, `331f156`, and `df0a890`.
  `T[]` now resolves
  through the Program-owned canonical `Array<T>` target with target-local
  instantiation identity, fail-closed global capability checks, poisoned warm
  cache rejection, and atomic retry. Property-only fresh object literals now
  have stable regular and widened derived identities, and Comparable admits
  validated declared, fresh, regular, and widened property objects without
  weakening fresh excess-property rules. Root type assertions check their
  operands without the asserted contextual type, publish the asserted result,
  enqueue the comparison for the deferred pass, and emit the exact TS2352
  diagnostic for non-overlapping types. Raw literal links remain fresh while
  enclosing mutable locations consume their regular/widened result types, and
  assignment expressions publish the right-hand result identity needed by
  `.types` baselines. Canonical array assertion operands now recursively widen
  to the stable ordinary Array identity, and non-overlapping array assertions
  emit exact cold/warm TS2352 diagnostics. `contextualTyping18` is exact;
  nested and const assertions, sibling-context union widening, spreads, holes,
  tuples, and direct readonly-array type-reference syntax remain explicit
  boundaries.
- Contextual ordinary array literals are integrated through `a872db5`,
  `cc7c4a0`, `a198e99`, `045cc36`, `81b1482`, `83d12ba`, `a3fd511`, and
  `88dcb9f`. Expression unions now admit
  primitives, literals, recursively canonical unions, and validated fresh
  property objects; subtype reduction preserves excess-property-distinct
  shapes. Checker-owned `Array<T>` references and array-literal clones have
  separate stable cache identities, same-target Array/ReadonlyArray relations
  are covariant, and global-aware display prints canonical suffix syntax.
  Contextual elements consume the target element type at mutable locations,
  retain literal AST identities while publishing widened effective types, and
  preserve the distinct strict empty-array `implicitNever` element. Positional
  no-spread elaboration uses retained element results, so `contextualTyping19`,
  `contextualTyping20`, and `contextualTyping21` match the pinned zero-error,
  TS2353, and TS2322 artifacts including exact spans and arguments. Recursive
  shorthand arrays are valid union constituents with authoritative global
  capability, including contextual literal unions and cold/warm alias query
  orders; loose nullish array elements retain their canonical widening
  identities. Malformed canonical-array caches remain invariants rather than
  being mislabeled as unsupported coverage. Recursive diagnostic elaboration
  retains the checked expression tree through object properties, so nested
  array failures point at the incompatible element without a spurious parent
  property record. The first global-aware apparent-type slice maps string-,
  number-, and boolean-like sources through authoritative library wrapper
  identities without leaking answers into context-free relation caches.
  Spreads and holes remain atomic typed boundaries; direct
  `Array<T>`/`ReadonlyArray<T>` syntax, declared-interface array elements in
  unions, mixed array/property-object subtype reduction, sibling-context union
  widening, tuples, const contexts, evolving arrays, and cross-target
  Array-to-ReadonlyArray relations remain explicit follow-ups. The combined
  checker passes 705/705 library tests, doctest, strict all-target checker and
  compiler Clippy, and rustdoc with warnings denied.
- The canonical array surface now extends through direct global
  `Array<T>`/`ReadonlyArray<T>` references, declared property-object elements,
  mixed array/property-object relation reduction, and dependency-closed cache
  validation in `41b5eb7`, `ab36630`, `5b382a9..21468be`, and `af2b51a`.
  Direct references share the authoritative target-local instantiation cache
  with shorthand arrays, preserve exact arity diagnostics, and reject local
  aliases that merely spell `Array`. Declared interface/type-literal elements
  participate in contextual arrays and unions without descriptor shortcuts.
  Cached capability validation closes through aliases, generic wrappers,
  unions, and declared property graphs, including exported and nested legal
  boundaries, while actual repeated merged properties remain an explicit
  unsupported family rather than a malformed cache. Array/object mixed
  reductions retain the pinned empty-object ordering and validate both source
  and target graphs before relation publication.
- Top-level initialized variable inference and exact straight-line current-flow
  types are integrated through `6821c5d`, `65487d4`, `889cd7a`, and the
  compiler invariant classification in `18987e5`. The source checker keeps the
  published declaration type separate from the source-ordered current-flow
  type used by identifier reads. Within the completely preflighted straight-line
  tree, annotated and inferred declarations, same-list reads, and direct
  assignments to already declared supported `var` symbols follow the pinned
  union-only assignment reduction, including `never`, `void`, fresh boolean
  literals, denormalized named-union origins, and the final invalid-reduction
  assignability safeguard. Non-union declarations retain their declared type;
  invalid assignments diagnose then reset flow to it. Self/forward reads,
  assignment before declaration, block-scoped assignment, chained/nested
  targets, cross-file flow, and control-flow joins still fail closed. The
  combined main tree passes 738/738 checker library tests plus doctest, strict
  all-target checker/compiler Clippy, and rustdoc with warnings denied after an
  independent Go-semantic audit.
- The annotated, non-generic `FunctionType` and signature kernel is integrated
  as `b815d77`. Dependency-closed function-type annotations now publish one
  canonical callable object, call signature, parameter value types, optional
  unions and minimum argument count before exposing the resolved cache. The
  implementation preserves lazy return-type resolution, function-indirected
  recursive aliases, circular return annotation recovery, exact pending-cache
  proofs, atomic parameter publication, and poisoned-cache retry behavior.
  Generic signatures, `this` and rest parameters, inferred annotations,
  constructors, overload families, and source-level
  `FunctionDeclaration`/`ArrowFunction` dispatch remain explicit boundaries.
  Independent Go evaluation-order and Rust identity/transaction audits both
  returned final GO verdicts. The integrated tree passes 744/744 checker
  library tests plus doctest, strict all-target checker and compiler Clippy,
  and rustdoc with warnings denied.
- The first callable consumer wave is integrated through `7de519e`,
  `7147520..f0434fa`, and `92410e1..74cc50a`. One normalized immutable
  `strictFunctionTypes` value now owns the relation-cache session; the
  production context exposes option-aware assignability. Exact annotated
  `FunctionType` values participate in non-generic signature relation,
  including minimum arity, strict variance, callback reversal, ignored target
  `void` returns, recursive `Maybe` state, lazy returns, and atomic cache
  publication. The semantic formatter prints those signatures in aliases,
  unions, arrays, and TS2322 displays while preserving optional semantic value
  types, precedence, truncation budgets, and typed capability boundaries for
  other callable shapes. Independent Go and Rust reviews closed cache,
  common-property, empty-object, reserved-member, rest-arity, duplicate
  signature, pending-state, and malformed-taxonomy defects before merge. The
  combined tree passes 766/766 checker tests plus doctest, strict all-target
  checker and compiler Clippy, and rustdoc with warnings denied.
- The source-callable integration boundary is frozen through `a1ba91a`,
  `b652b3a`, `579ec46`, and `6fd8fba`. Source assignment and current-flow
  relations now consume the retained `strictFunctionTypes` option and retry
  provider-owned lazy returns only when the relation or diagnostic formatter
  demands them. The retry path covers every union-flow constituent and stages
  circular-return diagnostics transactionally. A syntax-neutral callable
  dispatcher now owns cache classification, graph edges, relation projection,
  and display projection while the existing `FunctionType` implementation
  remains its only installed provider. Formatter traversal emits parameter
  types before demanding the outer return, including the complete nested
  inner-return, outer-return, successful-display retry sequence. Two
  independent semantic/invariant reviews found no P0/P1 defect after the
  union-flow repair. The combined tree passes 769/769 checker tests plus the
  doctest and strict all-target checker Clippy.
- The fresh canonical first-50 scorecard at
  `/tmp/ts-rust-canonical-first50-signatures-20260715.json` executes 50 variants
  with one exact full diagnostic artifact (`declarationEmitBigInt.ts`) and 49
  honest unsupported results, with no fatal checker invariant. The first
  unsupported syntax roots are concentrated in function declarations (9),
  classes (6), enums (4), modules (3), interfaces and arrows (2 each), plus
  five JavaScript and two TSX source gates. The attempted first-500 rerun hit
  the harness's 120-second cap before producing a scorecard, so the earlier
  completed 536-variant tranche remains the broad denominator. The unchanged
  one/49 result after `b815d77` is expected: neither the kernel nor its now
  integrated formatter/relation consumers are reachable from the dominant
  `FunctionDeclaration` and `ArrowFunction` source roots. The next parallel
  wave is therefore source callable construction, dispatch, and bounded body
  checking on top of the frozen signature contracts.
- The pinned source-callable oracle selects two separate gates. The first
  implementation gate is an annotated source function or fully annotated
  non-contextual arrow with required/optional identifier parameters, an
  explicit return annotation, exact source-function symbol ownership, lazy
  return resolution, formatter/relation participation, and one bounded return
  body. The first likely first-50 payoff after that substrate is
  `contextuallyTypedFunctionOptionalAndRest.ts`; exact parity additionally
  requires contextual arrow extraction, optional implicit-`any` TS7006, and
  empty-tuple rest normalization. `assertionWithNoArgument.ts` remains later
  because it also requires assertion predicates and real call checking.
- The first source-callable gate is now integrated through `96b4ebb`,
  `be06583`, `0e5ecf7`, and `72323b1`. Exact annotated top-level
  `FunctionDeclaration` values and direct non-contextual `const` arrows publish
  distinct binder-owned callable identities, immutable semantic parameter
  provenance, eager checked-return identities, strict/bivariant relations, and
  bounded concise/block return diagnostics. Arrow bodies are planned and
  checked after the source-order statement walk so parameter, self, and forward
  reads retain function-expression semantics. Independent Go/Rust reviews found
  no P0/P1 cache or retry defect; malformed arrow parser facts are rejected
  before publication. The combined gate is 788/788 checker tests plus doctest,
  strict checker/compiler Clippy, and rustdoc with warnings denied.
- `97d03fa` retains `noImplicitAny` in the canonical checker and projects it
  from compiler options. The fresh exact-artifact run at
  `/tmp/ts-rust-canonical-first50-source-functions-20260715.json` remains one
  exact match and 49 honest unsupported variants: all nine prior
  function-declaration roots advanced to narrower callable/body blockers, but
  none became a complete artifact, and the two arrow roots require contextual
  or destructured/untyped parameters. The next callable gate is therefore a
  reusable contextual-callable preparation layer with missing parameter/return
  types, TS7006, optional/rest semantics, and canonical empty-tuple
  normalization—not another syntax-only admission.
- Dependency-adjusted clustering of the completed 536-variant scorecard ranks
  three parallel verticals: shared value-expression/inference semantics,
  inferred/contextual callables, and enums. Enums are the best independent
  exact-match lane (19 first blockers, 17 no-diagnostic artifacts, and 12
  relatively standalone fixtures); classes and relative ESM remain strategically
  essential but consume the expression/callable kernels before they produce
  reliable complete artifacts.
- The first three-way feature wave is integrated through `a789acf..ca65708`,
  `1bf491c..fdde968`, and `87fcad1`. Root owned contextual-arrow source dispatch
  and the shared callable/tuple seams; one leaf worker owned canonical enum
  declared/value/member identity and relation admission; another leaf worker
  produced the syntax-neutral direct-call kernel; and a read-only reviewer
  attacked contextual-arrow and empty-tuple cache atomicity. That review found
  whole-file publication, optional-array capability, warm-retry, effective
  empty-rest, and tuple-provenance defects before merge. The resulting bounded
  contextual-arrow cut passes 23 focused tests, enum coverage passes 29 focused
  tests, and the combined checker library passed 812/812 tests before the call
  kernel was registered for source integration. `39f07f4` also makes the
  compiler adapter classify the new enum and empty-tuple error domains
  exhaustively instead of relying on a wildcard or fallback.
- The follow-on source-expression and generic-kernel wave is integrated through
  `cdba454`, `a1c04e1`, `a2c2d47`, `bbd3f8b`, and `584779d`. Ordinary direct
  identifier calls now execute exact fixed-arity and argument checks; top-level
  literal enums enter source execution; required own-property reads compose
  through arrays, objects, and calls; and dependency-closed constraint and
  instantiation kernels retain the pinned recursion/count limits rather than
  substituting identity types. Focused gates passed 48 property tests, 34 enum
  tests, nine constraint tests, and five instantiation tests. The checker unit
  binary passed 853 tests before the final nested-property repair; the expanded
  all-target Clippy build compiles all 854 unit tests, while the 1 GiB runner can
  no longer link that monolithic unit binary reliably. The pinned enum tranche
  at `/tmp/ts-rust-enum-50-584779d.json` executes 59 variants with seven exact
  full artifacts, 52 honest unsupported results, and no fatal invariant.
- Plain ESM program facts and the first exact cross-file value-import vertical
  are integrated through `76d7709`, `81fb514`, and `a2f71b7`. The compiler
  supplies a NodeRef-keyed Bundler/ESM resolution manifest that preserves
  repeated equal-text specifiers and explicit unresolved results. The checker
  accepts leading direct named value imports, resolves every binding through
  the immutable manifest, queries a target annotation only when the alias is
  read as a value, and never recursively source-checks an importer-first target.
  Target, alias, local-value, and identifier links share one final preflighted
  publication batch. Independent review caught and closed cross-batch partial
  publication, unused-import eager typing, consistent warm-cache target poison,
  and normal merged-alias classification defects before integration. Four
  public checker integration scenarios and one compiler-level ESNext/Bundler
  `string[]` scenario pass in importer-first, target-first, cold, and warm
  orders; strict checker/compiler Clippy and rustdoc with warnings denied are
  green.
- The fresh first-50 scorecard at
  `/tmp/ts-rust-canonical-first50-a2f71b7.json` advances from one to two exact
  full artifacts: `declarationEmitBigInt.ts` and
  `contextuallyTypedFunctionOptionalAndRest.ts`; the other 48 variants remain
  explicit unsupported boundaries with no code/span/message/order mismatch.
  The broad name-filtered import tranche at
  `/tmp/ts-rust-import-50-a2f71b7.json` has zero exact results across 54
  variants because its first blockers are predominantly CommonJS/Node10,
  NodeNext/package facts, declaration files, default/namespace/type-only or
  unresolved-import diagnostics—not the direct Bundler/ESM named-value slice.
  This is useful negative evidence: the next module payoff is type-space and
  exported-declaration closure, not widening the current gate by guessing.
- That type-space and generic-call seam is now integrated through
  `8ef637e..6253984`, `a97101d`, `2a40f0b`, and `3d66eaf`. Exact exported source
  type aliases and simple interfaces retain module/local/export ownership;
  annotated generic source functions retain one default-free identity
  signature; and inferred or explicit primitive identity calls execute through
  local and imported callable values. Imported declared alias/interface objects
  may cross the source-only inference boundary only after exact export and
  host-graph proof. The ordinary semantic inference API remains closed, warm
  call caches are revalidated, and importer-first checking never recursively
  checks the target source. Failed declared-object assignments now add the
  pinned TS2326/TS2322 chain only for independently proven terminal scalar
  property pairs; nested objects and callables deliberately retain the plain
  root TS2322 until recursive relation-chain reporting is ported.
- The ordered generic-call v2 slice is integrated through
  `0177d8f..805e1c3`. One exact stored source signature may now carry 1..N
  ordered type parameters, fixed required naked-parameter targets, trailing
  defaults, primitive or earlier-parameter constraints, repeated inference
  candidates, and a mapper-supported return. Direct and imported calls share
  globally cached checked signatures by their complete effective vector;
  every erroneous call instead retains a distinct uncached recovery signature,
  with TS2345 publishing its checked and recovery graphs in one reserved
  transaction. Partial/default failure returns preserve the pinned raw-vector
  behavior rather than recomputing from the checked signature. TS1009, TS1099,
  TS2558, TS2554/TS6210, TS2344, and TS2345 now have exact source ranges,
  messages, precedence, final compiler sorting, and cross-file related
  information. The public gates cover direct/imported checked-cache sharing,
  distinct recoveries, dependent constraints, literal candidate unions,
  partial/full default cache identity, raw default failure returns, and warm
  replay; two independent reviews found no P0/P1 defect.
- Exact named `import type` consumption is integrated through
  `002e17f..70c8096`, `38e0976`, and `4017b4d`. A capability is scoped to one
  direct top-level variable annotation root and may compose through exact
  parenthesized, array, and primitive/literal-union graphs with multiple
  imported leaves. Every complete root is read-only preflighted before source
  execution; warm union and both initialized/fallback array caches cannot retain
  authority; and local aliases, callable annotations, assertions, explicit call
  type arguments, and later assignments remain closed boundaries. Independent
  review found and closed later-root partial publication, warm outer-cache
  escape, wrapper-flag, nested owner, and truncated-diagnostic defects before
  merge. The combined gate passes 10/10 public source-import tests, 3/3 imported
  generic-call tests, 2/2 compiler Bundler/ESM tests, strict checker/compiler
  Clippy, and rustdoc with warnings denied. The monolithic checker unit binary
  still cannot reliably link inside the 1 GiB runner; all unit targets compile
  under the exact all-target Clippy gate and executable integration tests carry
  the public behavior checks.
- Fresh name-filtered scorecards provide honest negative evidence rather than a
  parity claim. `/tmp/ts-rust-generic-50-c22851e.json` reruns 50 variants after
  ordered source-call integration and still reports zero exact and 50 explicit
  unsupported results, with no code/span/message/order mismatch. The selected
  files are dominated by JavaScript, contextual generic callables, overloads,
  classes, mapped/conditional types, declaration emit, and unsupported source
  signatures, so none exercises the bounded annotated identifier-call cut as a
  complete artifact. The dominant blockers remain structured multi-parameter
  inference and candidates, contextual generic
  callables, overloads, classes, mapped/conditional types, and declaration
  emit—not the verified bounded ordered-call slice.
  `/tmp/ts-rust-import-50-4017b4d.json`
  executes 54 variants with zero exact and 54 explicit unsupported results,
  dominated by CommonJS/Node10, NodeNext/package facts, declaration files,
  default/namespace/reexport forms, and unresolved-import diagnostics. The next
  completed parallel implementation wave assigned one owner to single-signature
  generic calls v2 and a disjoint owner to primitive scalar operators. Logical
  operators, overload selection, element/index access, and flow joins remain
  separate later gates.
- The generic-calls-v2 owner kept the coupled substrate serial within one
  worktree: ordered source type-parameter metadata, full-vector inference and
  finalization, exact checked-signature caching, atomic recovery
  materialization, source diagnostics, and imported replay. The admitted shape
  is one exact stored signature with 1..N ordered type parameters,
  fixed required parameters whose inference targets are naked type parameters,
  a mapper-supported return template, repeated candidates, exact/partial
  explicit arguments, trailing defaults, and primitive or earlier-parameter
  constraints. Candidate combination, literal widening, declaration-order
  default/constraint instantiation, TS2558/TS2344/TS2345 recovery, exact mapper
  endpoint order, and last-write signature-cache publication are part of this
  gate. Structured `Array<T>` target inference is the immediate same-owner
  follow-up. Overload sets, callbacks/context-sensitive inference, optional/rest
  parameters, spreads, constructors, const parameters, and advanced type targets
  are not allowed to widen this slice.
- The parallel expression owner starts in a new `primitive_operators.rs` leaf
  and consumes only frozen bootstrap/relation/formatting APIs. Its first oracle
  matrix covers non-assignment primitive/literal `+`, arithmetic/exponentiation,
  relational, and equality binary expressions, with prefix `+`, `-`, `~`, and
  `!` only if they do not expand the shared contract. It must reproduce the
  upstream distinction between operand diagnostics TS2362/TS2363, whole-node
  TS2365, recovery result types, mixed number/bigint behavior, operand spans,
  issuance order, and final source-position sorting. `&&`, `||`, and `??` are
  explicitly deferred because their results require fact-sensitive falsy and
  non-nullish union projection; returning `boolean` would be a semantic cheat.
  Assignment operators, shifts/bitwise suggestion paths, updates, unions, type
  parameters, enums, objects, and flow narrowing also remain later gates.
- The next expression/callable wave is integrated through `df297a3`,
  `7f818a5`, `fea95fd`, `c7bffc5..0f31e7a`, `3e4cdb8`, and `37c9b99`.
  The parser and checker now preserve the pinned left-associative `??`/`||`
  recovery shape; source `&&`, `||`, and `??` execute their exact primitive
  result projection, identifier flow narrowing, contextual routing, and
  TS1345/TS2869/TS2871/TS2872/TS2873/TS5076 diagnostics. Ordered generic calls
  infer through canonical `Array<T>` and `ReadonlyArray<T>` parameter targets,
  while source callable metadata retains default and rest parameters and call
  checking observes effective rest arity. Exact element access now composes
  through source properties, strings, canonical arrays, primitive binary
  operands, and direct call arguments, including TS7015/TS2538/TS7053 and
  cold/warm publication. Source-declared index signatures, tuple/union access,
  optional chains, property/element flow references, method calls, overloads,
  and nested aggregate expression dispatch remain explicit follow-ups.
- The default/index/inferred-return closure is integrated through `c732b68`,
  `ca1c6a6`, `13d1774..e144f44`, and `ab67a9b..33105d8`. Supported source
  functions and arrows now execute default parameter initializers in the
  earlier-parameter scope, retain distinct optional call types and body types,
  and infer bounded empty, single-return, and concise-arrow returns before
  direct use. Inferred primitive, canonical array, and ordinary object results
  widen to stable identities; nested object/array results retain the exact
  array capability required by formatting and relation. Mutable arrow captures
  use the declared type rather than a declaration-point narrowing, inferred
  function diagnostics replay deterministically at the declaration slot, and
  forced warm replay recomputes the body so valid-looking poisoned return or
  expression caches cannot escape validation. One exact source-declared string
  or number index signature now feeds element access with declaration and
  readonly provenance; mixed, duplicate, interface, method, and paired index
  families remain fail-closed until their TS2411/TS2413 checks are ported.
  Independent review found and closed five inferred-return defects and one
  index-owner provenance defect before integration. The combined logical,
  generic-call, element, index, default-initializer, and inferred-return public
  tests pass together; checker test compilation, exact checker/compiler
  Clippy, and checker rustdoc with warnings denied are green. The monolithic
  checker unit binary is still intentionally not retried under the 1 GiB
  runner after repeated linker termination; its unit targets compile under the
  all-target gates and public integration binaries carry the vertical behavior.
- Required own-property calls are integrated through `e803a7b` and `0f2efd0`.
  The source planner admits `api.fn(arguments)` only when the exact enclosing
  call grants a retained callee-position capability to a direct
  identifier-property plan. Ordinary property reads cannot be laundered into a
  call, and the finished call cross-checks the property node, name node, parent
  call, and callee family before execution. One required own property with one
  exact non-generic callable now composes with the existing call kernel,
  publishing exact property symbol/type and call signature/return links. Too
  few arguments diagnose the property name and retain exact TS6210 related
  information; argument and extra-argument paths retain their existing pinned
  nodes/ranges. Optional, generic, overloaded, explicit-`this`, spread,
  element, parenthesized, nested-receiver, apparent, union, and `any` forms stay
  explicit boundaries. Forced warm/error replay and both property/call cache
  poison paths are covered. Focused property/call tests, three public vertical
  tests, checker test compilation, and exact checker Clippy pass; independent
  review found no P0-P2 issue.
- The binder-backed source-statement flow slice is integrated through
  `3045dd4..600ce07`. An explicitly annotated `FunctionDeclaration` may now
  execute sequential initialized identifier-named `let`/`const` locals and
  either a final direct or parenthesized identifier `if`/`else` whose arms
  return, or one fallthrough `if`/`else` whose locals-only arms rejoin before
  trailing locals and a final value return. The source leaf
  proves exact AST/binder scopes, symbol tables, flow containers, payloads,
  points, registered assignments, both condition edges, and the payload-less
  function `START` before semantic execution. Every invocation then owns a
  fresh flow frame, immutable snapshots, pending/resolved assignment state,
  and monotone memoization, so retries cannot reuse branch or local state.
  Truthiness narrowing, TS1345 and syntactic truthiness diagnostics, local and
  return TS2322 order/anchors, branch shadowing, multi-declarator ordering,
  parenthesized conditions, and cold/warm publication are covered. Hoisted
  function captures start all top-level variables—including `const`—at their
  declared types, matching the pinned checker rather than declaration-point
  narrowing; union types that merely contain `void` do not receive TS1345.
  Callable, named promise, exact structural-thenable, and other opaque object
  conditions remain fail-closed until TS2774/TS2801 and general apparent or
  inherited property lookup are ported. Missing `else`, non-final branches,
  inferred multi-return aggregation, joins, equality/`typeof` narrowing,
  loops, jumps, and broader statement families also remain explicit. Three
  independent reviews found no remaining P0/P1 defect; the residual hardening
  item is to encode the expected edge and assignment prefix per flow point
  instead of relying on global route coverage. The joined-body leaf now proves
  those exact prefixes independently, including ordered distinct two-arm
  `BRANCH_LABEL` antecedents. Join execution unions both immutable snapshots,
  preserves a matching declared named-union identity, and drops branch-local
  symbols that do not exist on both paths. The pinned zero-diagnostic `Choice`
  case and its three TS2322 branch/branch/trailing companion pass cold and warm
  with stable type, mapper, signature, diagnostic, and anchor order. Equality/
  `typeof`/discriminant narrowing, mutation statements, loops, jumps, and
  broader statement families remain explicit. The expanded 32-test expression,
  callable, generic, index, property-call, and statement-flow regression
  cluster plus checker test compilation and exact checker Clippy are green.
- The syntax-neutral ordered callable-set seam is integrated through
  `b4e01ce..9da7475`. Existing exact-single callable providers now adapt through
  one immutable projection without widening accepted source syntax. The shared
  validator preserves provider order, separates call and construct signatures,
  rejects duplicate IDs and poisoned parameter/return type caches, and checks
  minimum arity against fixed parameters after extracting a rest tail. The
  declared interface/type-literal call-member provider and overload resolver
  remain the next C1/C2 production consumers rather than being inferred from a
  structured signature cache alone.
- The first T1 tuple-construction seam is integrated through
  `1bc3fa1..b480547`. It ports the pinned target-key and instance-cache shape
  for required elements, trailing optional elements, a trailing rest element,
  labels, and readonly tuples. Fixed-length targets own exact numeric length
  literals or unions; variable-length targets use `number`; and a sole rest
  element collapses only through authoritative `Array`/`ReadonlyArray`
  targets. The existing mutable-empty-tuple adapter remains behaviorally
  closed while mutable `[]` and `readonly []` keep distinct target identities.
  Warm construction validates the recursive target, instance, literal, and
  union caches before reuse. Independent review found and closed both a
  poisoned length-union acceptance path and the zero-arity readonly cache
  conflation before handoff. Checker test compilation and exact checker Clippy
  are green. Tuple type-node consumption, general tuple display and relations,
  indexed access, variadic tuples, and rest/spread call applicability remain
  explicit T1/A10 follow-up work.
- The current pinned first-50 run at
  `/tmp/ts-rust-canonical-first50-9da7475.json`, rebuilt after the first
  post-join and callable-set slices, remains two exact artifacts and 48 honest unsupported
  variants, with zero code, span, message, order, or complete-artifact
  mismatches. This alphabetically biased smoke tranche is dominated by
  classes, broader function/body forms, module modes, JavaScript, TSX,
  declaration emit, and advanced type nodes; none is a complete artifact for
  the newly admitted final-`if` cut. The unchanged headline is therefore
  useful negative evidence rather than a regression: the next work must close
  post-branch joins and broader statements, overloads and contextual calls,
  classes, advanced types, then modules/projects—rather than add
  fixture-specific syntax admissions.

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
- use one implementer plus at least two independent reviewers and a separate
  fixer to find code that compiles but is semantically wrong;
- shard work across a small number of isolated worktrees, keep slow Cargo work
  out of leaf workers, and turn compiler/test failures into explicit queues
  only after the mechanical source inventory exists;
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
| AST node pointer | `NodeRef { arena: NodeArenaId, file: FileId, node: NodeId }` | A node is unambiguous across files and Program rebuilds. |
| Symbol pointer and merges | Program-owned `SemanticSymbolId`, `SymbolTableId`, declarations, and flags | Imports and merged declarations refer to the same semantic symbol, not a copied type description. |
| `FlowNode` graph | Program/binder-owned `FlowRef { arena, file, flow }` arena | Checker flow queries follow antecedents created by binding without accepting a rebuilt Program's equal local ID. |
| `Type` interfaces | Canonical `TypeId` arena plus a complete tagged payload | Identity, recursion, aliases, freshness, targets, and deferred forms survive across files. |
| `Signature`, `IndexInfo`, predicates | Dedicated ID arenas/records | Complete call/construct rules and lazy links are retained. |
| `NodeLinks` / `SymbolLinks` | Dense or sparse ID-keyed side tables | Lazy results and recursion state have one owner and stable cache keys. |
| Type mappers | Explicit mapper records/IDs | Instantiation and inference compose without cloning or stringifying recursive graphs. |
| Checker host callbacks | Narrow program-view trait with normalized checker options | `ts_checker` does not depend back on printer or the entire compiler crate. |
| Type display | Semantic formatter inside `ts_checker` | Diagnostics do not introduce a `ts_checker` -> `ts_printer` dependency cycle. |

Additional architectural decisions:

- The canonical symbol substrate lives in `ts_binder`, following the existing
  `ts_checker -> ts_binder` dependency. `ts_binder::SymbolStore` owns exact
  `Symbol` and `SymbolTable` records plus their store-branded IDs;
  `ts_checker::SemanticStore` embeds that store and remains the sole aggregate
  owner of the program semantic graph. Both layers use one `SemanticStoreId`.
  There is no separately branded binder graph and no legacy-symbol conversion
  map.
- Symbol member/export/local tables use store-owned `SymbolTableId`
  indirection. This preserves nil versus allocated-empty state, lets types and
  symbols share the same table identity, and avoids holding a mutable symbol
  borrow across recursive allocation or merge. Cross-crate checker operations
  mutate symbols through provenance-validating store methods; unchecked
  `&mut Symbol` is not a public API.
- Symbol-table keys use a byte-backed `EscapedName` newtype. Upstream reserves
  raw byte `0xFE`—which is deliberately invalid UTF-8—for internal names, so a
  Rust `String` or Unicode sentinel would either be unable to represent the
  key exactly or could collide with a legal source identifier. Source names
  retain their UTF-8 bytes; internal call/new/private/computed names retain the
  raw reserved prefix.
- Binder-created and checker-created transient symbols occupy the same symbol
  arena. Exact `CheckFlags`, declaration order, value-declaration precedence,
  parent/export-symbol links, shallow table cloning, and merge redirects are
  part of this substrate rather than later adapters.
- The ownership migration lands as one mechanical shared-contract change:
  move and re-export the semantic brand/symbol/table IDs, embed the concrete
  symbol store, and replace the provisional by-value type-member tables with
  `SymbolTableId`. After that contract freezes, canonical binder/CFG work,
  checker link records, and semantic artifact work may proceed independently.
- The canonical binder owns declaration and flow state in one traversal,
  matching upstream child order. The current separate flow builder remains a
  tested legacy transition path only until its graph helpers are consumed by
  that traversal; it is not a second canonical binder.
- Checker links follow upstream's 26 sparse, typed `LinkStore`s rather than a
  monolithic per-node or per-symbol record. `Get` allocates one stable
  zero-valued logical slot, while `Has` and `TryGet` never allocate; absent,
  allocated-empty, negative-cache, and recursion-sentinel states remain
  distinct. The first dependency-closed link slice covers common node links,
  resolved symbols/types/signatures, value and alias symbols, declared types,
  type aliases, and the shared type-resolution stack after T00 and B02 land.
- Link operations never retain a mutable record borrow across recursive
  checking. They read state, install any exact sentinel, release the borrow,
  recurse, then re-fetch and commit through provenance-validating aggregate
  methods. Specialized module, flow, mapped-type, JSX, accessibility,
  node-builder, and emit-resolver stores can then be ported independently.
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

The useful concurrency is phase-dependent. More workers do not help while
they are all changing the same identity, store, binder-state, or relation
contract; after those contracts freeze, the same workers can own disjoint
semantic families with little coordination.

| Execution wave | Safe parallel implementation clusters | Practical concurrency with four slots |
|---|---|---:|
| Foundation and oracle | Diagnostic oracle; AST/store identity; binder flow; semantic records | 2-3 implementers, with root integrating and one worker rotating into review |
| Canonical graph | Type payloads; lazy link records; program-owned binder symbols; exact artifact plumbing | 3 implementation lanes, provided each consumes the frozen store API |
| Binder/checker bootstrap | Name/reference resolution; mappers; intrinsic/global bootstrap and declared types; semantic formatter | 2-3 implementation lanes plus continuous review |
| Coupled algorithms | One owner for relation state and cache semantics; separate mapper/instantiation probes and source-dispatch scaffolding | 2 core implementation lanes; extra workers focus on tests, oracle shards, and review |
| Feature expansion | Expressions, flow evaluation, classes, modules, JSX, JSDoc, and advanced-type families behind stable dispatch | 3 implementation lanes with four slots; 6-10 independent clusters if more reviewed workers are available |
| Corpus closure | Root-cause failure clusters, modern-project gates, diagnostics, and integration regressions | Broadly parallel, bounded primarily by reviewer and integration throughput |

With four active slots, the default operating shape is root/integration plus
three workers. During a risky contract change, one worker implements, one
independently compares against Go, and one advances a non-overlapping oracle or
binder/type lane. During feature expansion, all three workers may implement
disjoint modules while root performs rolling review and integration. Do not
queue more than two unreviewed semantic clusters per available reviewer; an
unreviewed pile merely moves the bottleneck to integration and makes bad shared
assumptions expensive to unwind.

The 2026-07-15 object/assignment wave validated this shape empirically: one
worker owned diagnostic elaboration, one owned read-only assignment planning,
one alternated between pinned-Go oracle work and independent review, and root
owned source dispatch, compiler classification, and integration. When the
object lane exposed a separate global-`Object` cache contract, it became a
fourth bounded module slice only after the first worker released that
ownership. Cargo remained serialized while review, oracle analysis, and static
editing continued in parallel. The result was four coherent commits with no
P0/P1 review defect at integration, rather than four overlapping source-file
patches. With four slots this pattern yields roughly 2.5-3 useful worker lanes;
additional workers become valuable only after dispatch and shared cache
contracts are frozen, at which point 6-10 disjoint feature clusters are
plausible but reviewer/integration throughput becomes the limiting resource.

The subsequent array/flow/signature wave confirmed the same ceiling from the
opposite direction. One implementation lane completed array capability-graph
closure while another implemented current-flow types; a read-only Go reviewer
caught the union-only caller guard, non-union `never` behavior, `void` relation
edge, and fresh-literal mapping details before merge. Root serialized Cargo,
integrated the two slices, and kept the next FunctionType kernel in static
development. Two independent signature reviews then split Go evaluation-order
semantics from Rust retry/atomicity and found different shell-state defects
before that slice reached integration. With four slots, this is the stable
default: root/integration, one active core implementer, one next-wave
implementer or disjoint feature owner, and one rotating reviewer. A fifth and
sixth worker are best spent on a second review dimension and corpus/oracle
shards until source dispatch, signature records, and relation cache contracts
freeze; only then should they become additional core writers.

Work is assigned by an exclusive tuple of upstream functions, Rust destination
modules, and semantic records it may mutate. Fixture buckets are validation
inputs, never ownership boundaries. A worker that discovers a required change
to a shared contract stops at that boundary and returns a proposed interface
change to the integration lane instead of editing another worker's substrate.

### Scaling beyond four workers

Additional workers should widen the review, oracle, and feature queues before
they increase the number of writers touching shared checker state. The useful
topology changes when the semantic contracts freeze:

| Active slots | Before source/signature/relation contracts freeze | After those contracts freeze | Expected useful concurrency |
|---:|---|---|---:|
| 4 | root/integration; one core implementer; one disjoint implementer or next-wave scout; one rotating Go/Rust reviewer | root, two semantic writers, and one rotating reviewer; a reviewed slot may begin the next leaf | 2.5-3 while contracts move; about 3-3.25 after freeze |
| 8 | root; two core implementers; Go semantic reviewer; Rust invariant reviewer; dedicated fixer; oracle/corpus sharder; compiler/integration assistant | root; four or five feature owners; separate Go and Rust reviewers | about 6-7 lanes |
| 12+ | keep at most two writers on shared contracts; add upstream-inventory, oracle, fixture-clustering, fuzz/property-test, diagnostic, and compiler workers | roughly seven feature owners; root; two reviewers; oracle and fixer roles | about 9-10.5 lanes until integration saturates |

The revised post-freeze range is supported by the present module and change
shape, not by an assumption that a checker is embarrassingly parallel. The
checker has 52 top-level semantic modules and 40 are below 3,000 lines, so many
families can have bounded ownership. In the most recent 120 semantic commits,
however, `source.rs` changed in roughly one third, while `type_nodes.rs`,
`source_calls.rs`, `store.rs`, `mod.rs`, and `relater.rs` were the next most
frequent shared surfaces. Those dispatcher, record, and relation seams cap the
useful population at roughly seven simultaneous semantic writers. Additional
workers remain productive as Go-semantic reviewers, Rust cache/provenance
reviewers, fixers, oracle/corpus sharders, and compiler-integration owners.

For an eight-worker push, only two workers may write the shared type/signature,
link, relation, or source-dispatch substrate at once. The other roles are not
standby capacity: the Go reviewer produces branch and evaluation-order defects,
the Rust reviewer produces identity/transaction/cache defects, the oracle lane
turns fixture failures into root-cause queues, and the fixer keeps reviewed
patches from accumulating behind their original authors. Once a contract is
frozen, those same slots can rotate into functions, classes, enums,
modules/imports, expressions/operators, control flow, JSX/JS, or advanced-type
clusters that consume it without editing it.

The annotated non-generic signature contract subsequently passed both final
Go-semantic and Rust-invariant reviews and integrated as `b815d77`. Its first
consumer wave keeps option ownership at root: root first publishes one
immutable normalized `strictFunctionTypes` value, then separate workers may
project callable types through the semantic formatter and port non-generic
signature relation without sharing destination modules. Source-level function
declarations and arrows remain a later dispatch wave rather than being inferred
from the presence of callable records.

The completed consumer wave is a concrete warning against spending every slot
on implementation. The formatter and relation branches both passed their first
test runs, but independent reviews still found semantic defects: optional
parameter display, truncation accounting, pending-versus-malformed state,
valid reserved callable members, rest-tuple arity, duplicate inherited
signatures, weak common-property checks, empty-object shortcuts, option-blind
relation caches, and rollback/taxonomy gaps. Separate fixers closed those
findings, and the merged branch then passed 766 checker tests plus checker
Clippy, compiler Clippy, and rustdoc with warnings denied. With four slots, the
productive shape was therefore two disjoint writers, one rotating reviewer or
fixer, and root integration—not three unchecked semantic writers.

The next source-callable wave should freeze one syntax-neutral validated-callable
projection before it widens. Root owns that shared projection, source dispatch,
context facade, and compiler classification. Once frozen, separate workers can
own (1) non-generic annotated `FunctionDeclaration` values, (2) fully annotated
non-contextual arrow values, and (3) bounded body/return checking. Each owns its
source module and upstream function range; none may independently change type,
signature, symbol-link, or relation-cache records. With four slots, run two of
those feature owners plus a reviewer while root integrates. With eight, all
three can advance while Go review, Rust invariant review, a fixer, and an
oracle/corpus worker remain continuously staffed.

That source-callable wave is now complete, and the contextual/enum/call wave
confirmed the next ownership boundary. At four slots, root can integrate one
shared source-dispatch change while two workers build non-overlapping semantic
leaves and the fourth slot performs adversarial review or starts the next leaf.
The current wave assigns direct-call source integration to one worker,
top-level enum source planning to a second worker without granting it
`source.rs`, and dependency-closed instantiation/constraint work to a third;
root alone owns compiler classification, serialized Cargo, corpus runs, and
changes to shared dispatch. This is the stable 2.5-3-lane shape in practice.
At eight slots, add property/member access and inferred-callable completion
plus independent Go and Rust reviewers. At twelve slots, add fixed tuples and
cross-file reference/module work while retaining dedicated source and
type-node/relation seam owners. Generic inference/overload selection remains a
single coupled owner after direct calls, instantiation, and constraints land.

The plain-ESM wave then exercised the same topology across files. One worker
owned the compiler's immutable module-resolution manifest, a second owned the
read-only named-import leaf, two short-lived reviewers separately audited Go
alias semantics and Rust publication atomicity, and root alone changed shared
source dispatch. That review found four integration-class defects before the
feature merged: cross-batch partial publication, eager typing of unused
imports, trusting consistently poisoned warm alias caches, and treating a
valid merged alias as an internal invariant. The correction is structural,
not fixture-specific: every binding is resolved independently, only value-read
bindings are typed, and target/alias/local/identifier links enter one final
preflighted publication batch.

The next four-slot wave is therefore root/integration plus three disjoint
writers: (1) generic call inference, signature instantiation, and overload
selection under one coupled owner; (2) source-signature completion for generic
declarations and bounded parameter/return inference; and (3) type-space ESM
closure for named type-only imports and exported simple declarations. Root
retains `source.rs`, production/compiler wiring, shared record changes, Cargo,
and corpus scorecards. As each leaf finishes, its slot rotates into independent
review before integration. About 70-80% of implementation in this phase can
run concurrently; shared dispatch, cache/publication contracts, integration,
and artifact scoring remain deliberately serialized. With eight slots, add a
Go reviewer, a Rust invariant reviewer, a dedicated fixer, and an indexed/
element-access feature owner before adding another writer to generic calls.

Each worktree owns one small coherent commit series. Slow Cargo and corpus-wide
runs remain centralized and serialized; leaf workers perform static inspection,
pinned-Go comparison, targeted oracle work, and edits while the integration
lane builds. A wave may advance when every shared contract has one owner, every
implementation cluster has independent review capacity, and the integration
queue contains no more than two unreviewed semantic clusters per reviewer.

### Near-term parallel dependency DAG

The fastest path from the current bounded checker to ordinary modern projects
is not to finish one semantic family at a time. It is to freeze the remaining
composition seams, then advance the independent branches below in parallel:

```text
P0: inferred returns [done] + required property calls [done] + first statement/flow slice [done]
|
|-- F1 post-if joins [bounded slice done] and equality/typeof narrowing
|    `-- F2 loops, switch, reachability and jumps
|         `-- F3 try/finally, closure flow and definite assignment
|
|-- C1 callable-member and ordered overload-set construction
|    |-- C2 overload selection and contextual callbacks
|    |    |-- I1 structured generic inference
|    |    |-- K1/K2 classes
|    |    `-- J1/J2 JSX
|    `-- T1 tuple, rest and spread call semantics ---------^
|
|-- A11 declared index seed [bounded slice done]
|    `-- A1 keyof and indexed access
|         |-- X1 intersections
|         `-- A2 mapped types
|              `-- A3 conditional, infer and substitution types
|
`-- M0 immutable ESM manifest [bounded slice done]
     `-- M1 Bundler declaration/default/namespace/re-export closure
          `-- M2 NodeNext and package facts
               `-- P1 representative modern project graph
```

Before widening that graph, root/integration freezes and exclusively registers
four interfaces:

1. `SourceStatementPlan` and invocation-local `SourceFlowFrame`, with narrow
   callbacks into the existing expression planner/checker. Leaf statement and
   flow workers must not add private alternatives to source dispatch.
2. A recursive type-family host for child planning, child resolution, staged
   publication, and warm-cache validation. Advanced type workers own new leaf
   modules; root alone registers their syntax kinds in `type_nodes.rs`.
3. An ordered `CallableSetProjection` containing exact call and construct
   signature IDs. Callable-member construction can then feed production sets
   while overload selection is tested concurrently against synthetic sets.
4. One relation-family integration owner per wave. Type constructors may
   advance independently, but multiple workers do not add unrelated branches
   to `relater.rs` in the same wave.

`source.rs`, `type_nodes.rs`, `relater.rs`, `mod.rs`, shared store/link/signature
records, compiler fact projection, and final diagnostic integration therefore
remain root-owned merge surfaces. A leaf that needs a new shared field stops
and proposes the contract instead of widening its ownership.

#### Wave 1: composable declarations, calls, and straight-line bodies

Goal: check ordinary strict functional and library code through Bundler imports
and consumed declaration files.

| Lane | Primary upstream seam | Rust ownership |
|---|---|---|
| C1 callable sets | `getSignatureFromDeclaration`, `getSignaturesOfSymbol`, anonymous member resolution | new `anonymous_signatures.rs`/`source_overloads.rs`; bounded signature/object-member adapters |
| C2 overloads/context | `resolveCallExpression`, `resolveCall`, `chooseOverload`, applicability and contextual argument typing | new `overloads.rs`; `calls.rs`, `contextual.rs`, `inference.rs`, `source_calls.rs` |
| T1 tuple/rest/spread | tuple type construction, rest extraction, spread argument typing, correct arity | `tuple_types.rs`, new tuple/call-arity leaves |
| A1 indexed/keyof | indexed-access type resolution, property/index lookup and applicable index selection | new indexed/keyof leaf modules plus element/index tests |
| F1 joins/narrowing | branch-label flow, assignment flow, equality and `typeof` narrowing | `source_flow.rs` and `source_statements.rs`; no loops yet |
| M1 Bundler modules | import/export checking, external-module symbol and alias-target resolution | `source_imports.rs`, `alias_provider.rs`, compiler module facts |
| O1 oracle | exact `.errors`, `.types`, and `.symbols` root-cause scorecards | `tools/ts_fixture` only |

C1 and C2 may execute concurrently only after the ordered callable-set
projection freezes. T1 joins C2 when spread/rest applicability begins. A1, F1,
M1, and O1 are otherwise independent of that call seam.

#### Wave 2: ordinary application code

Goal: classes, structured inference, control statements, package declarations,
and basic TSX.

| Lane | Scope and ownership |
|---|---|
| K1 class graph | class/interface member resolution, bases, constructor/static/instance identities in a new class-type leaf |
| K2 class checking | class/property/method/constructor source plans in a new source-class leaf; consumes a frozen `ClassPlan` from K1 |
| I1 structured inference | broader inference priorities, fixing, signature and contextual candidates under one coupled inference owner |
| X1 intersections | construction, member resolution, instantiation and one explicitly owned relation seam |
| F2 loops/switch | flow loop labels, switch clauses, reachability, jumps, and source statement checking |
| M2 NodeNext | package/module format facts, conditional exports, and declaration targets |
| J1 JSX core | intrinsic tags, function components, props, children, and basic overload application |

K2 may plan syntax concurrently with K1 only after the `ClassPlan` contract is
fixed; it may not invent a second class/member representation.

#### Wave 3: ecosystem closure

Goal: the advanced type and flow families that dominate React, framework
declarations, and strict multi-package projects.

| Lane | Scope |
|---|---|
| A2 | mapped and reverse-mapped member resolution, instantiation, relation, and inference |
| A3 | conditional/infer/substitution types, distributivity, and tail-recursion budgets |
| A4 | template literal construction/pattern inference and intrinsic string mappings |
| K3 | accessibility, private/protected identity, override/abstract checks, `this`/`super`, and static initialization |
| F3 | try/finally completion, predicates/discriminants, closure flow, definite assignment, and exception reachability |
| J2 | managed attributes, generic/class components, and JSX namespace resolution |
| P1 | NodeNext/project references, augmentations, option closure, and exact modern-project scorecards |

At four slots, root keeps two semantic writers and one rotating reviewer active.
At eight, Wave 1 can sustain C1, C2, A1, F1, and M1 with root and separate Go
and Rust reviewers; T1 rotates in as a lane clears. At twelve, all six Wave 1
writers fit alongside root, two reviewers, an oracle worker, and a fixer. Waves
2 and 3 use the same topology: staff five writers at eight slots or roughly
seven at twelve, rather than allowing every worker to touch a shared
dispatcher.

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
