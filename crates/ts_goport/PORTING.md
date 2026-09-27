# ts_goport porting contract

This crate is a line-by-line port of pinned typescript-go
`dc37b5249ab60e2bbce936f71b883e6c8136167e`
(`~/.explore/repos/microsoft__typescript-go/internal`). About 70 agents port
separate Go ranges at the same time. Nobody can see the other files while
writing. The rules below make every file agree on names and types without
coordination. Follow them exactly. When a rule does not cover a case, choose
the most literal port and add a `// PORT:` comment that explains the choice.

## Ownership

- You own exactly one new file (two for the program unit). Write only that file.
- Do not edit `lib.rs`, `core.rs`, `prelude.rs`, `flags*.rs`, `diag.rs`,
  any `mod.rs`, `Cargo.toml`, or any other crate.
- Do not run `cargo`. Root runs builds and sends compile errors back later.
- Start every file with `use crate::prelude::*;`. Everything in the crate is
  glob-exported through the prelude.
- Port every Go function in your range, in Go order, with the Go logic intact.
  Keep Go comments that explain behavior. Do not simplify, merge, or "improve".
  Behavior must match Go exactly, including diagnostic order and type creation
  order (type ids decide union order).
- If you cannot port something (a missing dependency such as the node builder,
  printer, or node factory), call `unported!("goFunctionName")` at that point.
  Never return a guessed value.
- Skip Go code only for: tracing, `debug.Assert*` (port as `debug_assert!`),
  language-service-only exported APIs (`GetXxx` wrappers used only by
  `ls`/`services`), and concurrency (mutexes, `sync.Once` become plain code).

## Names

- Go `camelCase`/`PascalCase` function or method -> Rust `snake_case` with the
  same words. `getTypeOfSymbol` -> `get_type_of_symbol`,
  `IsTypeAny` -> `is_type_any`, `GetJSDocTags` -> `get_js_doc_tags`,
  `isESSymbolLikeType` -> `is_es_symbol_like_type`.
  Rule: insert `_` before each capital that follows a lowercase letter or
  digit, and before the last capital of an acronym run followed by a
  lowercase letter; then lowercase. (`getTypeOfJSXElement` ->
  `get_type_of_jsx_element`, `ESSymbol` -> `es_symbol`.)
  Rust keywords get a trailing underscore: `type_`, `match_`, `ref_`.
- Go struct fields -> `snake_case` by the same rule.
- Exported and unexported Go names with the same snake name only collide when
  both exist in one Go type; then suffix the exported one with `_exported`.
- Go consts of flag types: `ast.SymbolFlagsValue` -> `SymbolFlags::VALUE`,
  `TypeFlagsAny` -> `TypeFlags::ANY`, `ast.NodeFlagsAmbient` ->
  `NodeFlags::AMBIENT` (all from `crate::flags`, generated from Go, same
  numeric values). Operators: `a|b` works, `a&b != 0` -> `a.intersects(b)`,
  `a&b == b` -> `a.contains(b)`, `a&^b` -> `a.without(b)`, `a&b` -> `a & b`.
  Raw bits: `.0`.
- `ast.KindFoo` -> `SyntaxKind::Foo` (`ts_ast::SyntaxKind`). Only difference:
  Go `JSDoc...`/`JS...` kinds are spelled `JsDoc...`/`Js...`
  (`ast.KindJSDocTypeTag` -> `SyntaxKind::JsDocTypeTag`,
  `ast.KindJSImportDeclaration` -> `SyntaxKind::JsImportDeclaration`).
  Range markers: `ast.KindFirstTypeNode` -> `SyntaxKind::FIRST_TYPE_NODE`
  (compare with `>=`/`<=`; SyntaxKind is `Ord`).
- Diagnostics: `diagnostics.Type_0_is_not_assignable_to_type_1` ->
  `diag::Type_0_is_not_assignable_to_type_1` (exact Go name,
  `&'static ts_diagnostics::Message`).
- Go package-level functions in `checker` -> `impl Checker` methods when they
  touch type, symbol, signature, mapper or checker data, else free `pub fn`.
  Package-level functions in `ast`, `scanner`, `binder` that take a symbol
  get `symbols: &SymbolArena` as the first parameter; all other `ast`
  functions are free `pub fn`s with the Go snake name.
- Go methods on `*Checker` -> `impl Checker` methods (`&mut self`; `&self`
  only when Go clearly only reads). Go methods on other structs -> methods on
  the Rust struct.

## Types

| Go | Rust |
|---|---|
| `*ast.Node` and every alias (`*ast.Expression`, `*ast.TypeNode`, `*ast.SourceFile`, `*ast.IdentifierNode`, `*ast.Declaration`, ...) | `Node` (Copy handle, `Node::NIL` = nil) |
| `*ast.NodeList` | `NodeList` (Copy handle, `NodeList::NIL` = nil) |
| `*ast.ModifierList` | `ModifierList` (Copy handle) |
| `*ast.Symbol` | `SymbolId` (`SymbolId::NIL`) |
| `ast.SymbolTable` | `SymbolTable` (Copy handle; nil map = `SymbolTable::NIL`) |
| `*ast.FlowNode` | `FlowNodeId` |
| `*Type` | `TypeId` |
| `*Signature` | `SignatureId` |
| `*IndexInfo` | `IndexInfoId` |
| `*TypePredicate` | `TypePredicateId` |
| `*TypeMapper` | `MapperId` |
| `*InferenceContext` | `InferenceContextId` |
| `*InferenceInfo` | `usize` index into `inference_contexts[ctx].inferences` (pass the context id too) |
| `*diagnostics.Message` | `&'static Message` (`ts_diagnostics::Message`) |
| `*ast.Diagnostic` | `Diagnostic` (owned, `core::Diagnostic`) |
| `[]*T` param | `&[T]` ; `[]*T` field or return | `Vec<T>` |
| `string` param | `&str` ; field or return | `String` |
| `int` | `i32` ; `int64` | `i64` ; `uint32` | `u32` ; `jsnum.Number` | `ts_jsnum::Number` |
| `bool` | `bool` |
| `any` literal value (LiteralType.value) | `LiteralValue` enum defined in `checker/types.rs` |
| `core.Tristate` | `Tristate` (in `options.rs`) |
| `func(*Type) bool` param | `&mut dyn FnMut(&mut Checker, TypeId) -> bool` |
| `func(*Type) *Type` param | `&mut dyn FnMut(&mut Checker, TypeId) -> TypeId` |
| stored func fields | `Rc<dyn Fn(&mut Checker, ...) -> ...>` |
| other `*Struct` shared/mutated across calls | `Rc<RefCell<Struct>>` |
| `map[K]V` | `FxHashMap<K, V>`; use `IndexMap` when Go iterates and order matters for output |
| `collections.Set[T]` / `OrderedSet` | `FxHashSet<T>` / `IndexSet<T>` |
| `(T, bool)` / multiple returns | tuple |
| `...any` diagnostic args | `Vec<String>`, built with `args![a, b]` |

Handles are nil when zero. Go `x == nil` -> `x.is_nil()`, `x != nil` ->
`x.is_some()`. Do not use `Option<Handle>`. Pointer equality -> `==` on
handles.

Borrowing: arenas live in `Checker`. Copy what you need out of an arena entry
before calling another `&mut self` method. Clone `Vec`s you iterate while
calling `&mut self` methods. After a call, re-fetch links
(`self.value_symbol_links.get(s)`) instead of holding a reference across it.

## Checker data (owned by checker_p01 and types)

`checker/types.rs` defines (Go names, snake fields):
`Type { flags: TypeFlags, object_flags: ObjectFlags, id: TypeId, symbol: SymbolId, alias: Option<Rc<TypeAlias>>, data: TypeData }`,
`enum TypeData { Intrinsic(IntrinsicType), Literal(LiteralType), UniqueESSymbol(UniqueESSymbolType), TypeParameter(TypeParameter), Index(IndexType), IndexedAccess(IndexedAccessType), TemplateLiteral(TemplateLiteralType), StringMapping(StringMappingType), Substitution(SubstitutionType), Conditional(ConditionalType), Object(ObjectType), TypeReference(TypeReference), Interface(InterfaceType), Tuple(TupleType), InstantiationExpression(InstantiationExpressionType), Mapped(MappedType), ReverseMapped(ReverseMappedType), EvolvingArray(EvolvingArrayType), Union(UnionType), Intersection(IntersectionType) }`.
Go embedding becomes nesting: `TupleType { interface: InterfaceType, .. }`,
`InterfaceType { reference: TypeReference, .. }`, `TypeReference { object: ObjectType, .. }`,
`ObjectType { structured: StructuredType, .. }`, `StructuredType { constrained: ConstrainedType, .. }`,
`UnionType { union_or_intersection: UnionOrIntersectionType, .. }`, and so on
exactly as in Go. Every Go `AsX()` accessor on `*Type` is a method on `Type`:
`as_x(&self) -> &X` and `as_x_mut(&mut self) -> &mut X`, working for every
variant that embeds `X` (panic otherwise). Every other Go method on `*Type`
(`Target()`, `Types()`, `TargetTupleType()`, `Distributive()`, ...) is a
`Type` method with the snake name, returning handles by value and slices as
`&[T]`. Same for `Signature`, `IndexInfo`, `TypePredicate`, `TypeAlias`,
`ConditionalRoot`, and all `*Links` structs (all `Default`).

`checker/checker_p01.rs` defines `pub struct Checker` with every Go
`Checker` field (snake), and these arenas and accessors:
- `symbols: SymbolArena` (starts as a clone of `prog().bound_symbols`).
  Access: `self.symbols.sym(s)`, `self.symbols.sym_mut(s)`; shorthand
  methods `self.sym(s) -> &Symbol` and `self.sym_mut(s)`.
- `types: Vec<Type>` -> `self.ty(t) -> &Type`, `self.ty_mut(t) -> &mut Type`.
- `signatures: Vec<Signature>` -> `self.sig(s)`, `self.sig_mut(s)`.
- `index_infos: Vec<IndexInfo>` -> `self.index_info(i)`, `self.index_info_mut(i)`.
- `type_predicates: Vec<TypePredicate>` -> `self.pred(p)`, `self.pred_mut(p)`.
- `mappers: Vec<TypeMapper>` -> `self.mapper(m)`, `self.mapper_mut(m)`.
- `inference_contexts: Vec<InferenceContext>` -> `self.inference_context(c)`, `self.inference_context_mut(c)`.
Each arena has a dummy entry at index 0. New entries are pushed; ids are
`TypeId(len as u32)` etc. Go `c.newType`, `c.newSignature`,
`newIndexInfo`, `newTypePredicate`, mapper constructors push into these.
Go `t.id` equals the arena index, so Go's per-checker `TypeId` counter order
is kept. Link stores: `value_symbol_links: LinkStore<SymbolId, ValueSymbolLinks>`
etc. with the Go field names.

`checker/mapper.rs` defines `TypeMapper` (an enum over the Go mapper kinds)
and its constructors. Go `m.Map(t)` -> `self.mapper_map(m, t)`,
`m.Kind()` -> `self.mapper(m).kind()`, `m.MapsThisOnly()` ->
`self.mapper(m).maps_this_only()`.

## AST (owned by ast/node.rs, ast/fields.rs, ast/misc.rs, ast/utilities_*)

Go reads the AST without a context. So do we: `crate::core::prog()` returns
the current `&'static GoProgram` of the thread (see Threads). `Node`
methods reach the AST through it.
- `node.Kind` -> `n.kind() -> SyntaxKind`; `node.Flags` -> `n.flags() -> NodeFlags`
  (Go flags: parser flags plus binder-added flags); `node.Parent` ->
  `n.parent() -> Node`; `node.Pos()`/`End()`/`Loc` -> `n.pos() -> i32`,
  `n.end() -> i32`, `n.loc() -> TextRange` (Go `core.TextRange`, defined in
  node.rs with `pos()`/`end()`/`len()`).
- `ast.GetSourceFileOfNode(n)` -> `get_source_file_of_node(n) -> Node`.
  File data: `n.go_file() -> &'static GoFile` (any node);
  `file.AsSourceFile().X` for Go SourceFile fields -> `source_file_info(file).x`
  (parser/program fields, `program::SourceFileInfo`) or
  `file_bind_data(file).x` (binder fields, `core::FileBindData`). Text:
  `file.Text()` -> `source_file_text(file) -> &'static str`,
  `file.FileName()` -> `source_file_file_name(file) -> &'static str`.
- Binder data (Go fields set by the binder on nodes): `n.symbol()`,
  `n.local_symbol()`, `n.locals()`, `n.flow_node_data().flow_node`... use
  `n.bind() -> &'static NodeBindData` and its fields; Go `node.Symbol()` ->
  `n.symbol()`, `node.Locals()` -> `n.locals()`, `node.LocalSymbol()` ->
  `n.local_symbol()`, `node.FlowNodeData().FlowNode` -> `n.flow_node()`,
  `EndFlowNode`/`ReturnFlowNode` -> `n.end_flow_node()`/`n.return_flow_node()`.
  Flow data: `f.get_flow() -> &'static FlowNode`.
- Go field access through `As*()`: `node.AsBinaryExpression().OperatorToken`
  -> `n.operator_token()`. One accessor per Go field name, generated in
  `ast/fields.rs`, that works for every kind that has that field (panics on
  other kinds). Return types: node field -> `Node`; `*NodeList` ->
  `NodeList`; `*ModifierList` -> `ModifierList`; `string` -> `&'static str`;
  `Kind` -> `SyntaxKind`; flags -> their flag type; bool -> bool.
  Name clashes with Go `Node` methods of the same name (`Name()`, `Body()`,
  `Type()`, `Expression()`, `Initializer()`, `Text()`, `Arguments()`,
  `Parameters()`, `Members()`, `Statements()`, `TypeArguments()`,
  `TypeParameters()`, `Elements()`, `Properties()`, `ModuleSpecifier()`,
  `ImportClause()`, `Label()`, `QuestionToken()`, `PostfixToken()`, ...):
  the Go method wins (in node.rs; returns nil instead of panicking on kinds
  without it); fields.rs does not generate a clashing name. Go methods that
  return `[]*Node` (`Arguments()`, `Parameters()`, `Members()`,
  `Statements()`, `Elements()`, `Properties()`, `TypeArguments()`,
  `TypeParameters()`, `ModifierNodes()`, ...) return `NodeSlice` (Copy;
  `len()`, `is_empty()`, `get(i) -> Node`, `iter()`, `first()`, `last()`,
  `to_vec()`; empty when nil). `NodeList` has `.nodes() -> NodeSlice`,
  `pos()`, `end()`, `loc()`, `has_trailing_comma()`, `is_nil()`.
  `ModifierList` has `.nodes()`, `.modifier_flags()`, `is_nil()`.
- `NodeList`, `ModifierList` and `NodeSlice` are Copy structs defined in
  `ast/node.rs` (for example `{ file: u32, list: Option<&'static ts_ast::NodeList> }`).
- Node factory (`c.factory.NewX`) is unported for now: `unported!("NewX")`.
- Go `ast.IsX(node)` predicates -> `is_x(n)` free functions.
- New code reads node data through `by_data!`, `data_accessor!` or the
  binder `_in` pair. Do not add `ast_data_of` call sites: the multiprog D3
  to D5 port removes `ast_data_of`.
- New store columns are read through one file lookup helper, not
  `FROZEN.get()` directly, so the multiprog port can make that lookup
  tier 1 aware in one place.

## Program (owned by program.rs)

`core::GoProgram` and `core::GoFile` are fixed. **Pending Theo's approval
(A1, multi-program plan):** this model replaces one program per process.
The batch that adds it is not accepted until Theo approves.

- `GoProgram` is one program version (Go makes a new `Program` for each
  edit). It has an `id` (`core::next_program_id`), the file ids in Go order
  (`source_file_order`), options, binder symbols and its program state. It
  has no file list.
- `GoFile` is one file version. The file registry (`ast/store.rs`) owns it
  from `publish_file_stores` on; read it with `ast::go_file(id)`. Program
  versions share the file versions they have in common, as Go shares
  unchanged `SourceFile` objects.
- `program::release_program` frees the checker pool and the frontend of a
  version. The program shell and the file versions stay leaked for now.
- A `tsc -b` build (`goport_build`, `tsgo -b`) is a multi-program process,
  like Go: each project's program is a version made with `new_program` and
  `program::new_program_version`, and it is released when its task
  reports. The build host shares its parsed `.d.ts` and `.json` files
  between the programs. A file that one program parsed and left out (a
  deduplicated package) can be a program file of a later one, so the build
  host notes each parse that it keeps (`program::note_parsed_source_file`)
  and a publish gives it its complete `GoFile`. The publish asserts that
  every program file is a source file.

`program.rs` defines `SourceFileInfo`, `load`, `bind_all`, the Go
`Program` methods as free functions with Go snake names (`get_resolved_module(file, name, mode)` ->
`*module.ResolvedModule` port as `Option<ResolvedModule>` struct with Go
fields, `get_source_file_for_resolved_module(name) -> Node`, ...), the
checker pool, and diagnostic sorting. `options.rs` defines Go-shaped
`CompilerOptions`; read it from `prog().options`.

## Exit codes

`tsgo`, `goport`, `goport_emit` and `goport_build` compile and report
through the shared `execute::execute_tsc` (Go execute/tsc.go) and
`execute::tsc` modules, as Go `tsc` does. `tsgo` returns the Go status.
`goport` and `goport_emit` return the tsc status (Go
execute/tsc/emit.go:65): 0 success, 1 diagnostics with emit skipped, 2
diagnostics with emit not skipped. Under
noEmit, a program with no emittable file (no inputs, or only `.d.ts`
files) exits 2. `goport_build` returns the Go build status, which can also
be 3 or 4. Unported code, any other panic and a worker-thread failure
exit `execute::tsc::EXIT_UNPORTED` (70, `EX_SOFTWARE`). Go uses 0 to 5 (3
in cmd/tsgo/sys.go:66, 4 in build mode, 5 NotImplemented), so a harness
must treat a goport exit of 70 as a crash, never as a tsgo status.

A site where the pinned Go panics on the same input uses
`core::go_panic(message)`, not `panic!`. It is not a port gap: the guards
that keep a run going pass it on (`core::resume_go_panic`), and the bins
end the run as the Go runtime does. The output written so far stays,
stderr gets `panic: <message>` (then the port site in place of the
goroutine trace), and the exit code is 2 (`core::EXIT_GO_PANIC`).

## Threads

- `prog()` is the current program of the thread. A one-program process
  calls `core::set_prog` once, and every thread with no current program
  reads that program. `WorkerSeed` sets it on checker and bind threads. A
  multi-program process (watch, `tsc -b`, language server, tests)
  registers each version with `core::register_program_version` and makes
  one current for a scope with `core::enter_program`. There, `prog()`
  panics on a thread with no current program.
- Programs and the program state are read only after load, so they hold
  only thread-safe data (`Arc`, `OnceLock`, `Mutex`).
- Files bind in parallel, each into its own arena, and join the binder
  lineage in file order (`program::bind_all`). The ids equal a serial bind.
  A file version binds once (Go `BindOnce`): a later program version binds
  only its new file versions and adds them to the same lineage.
- Each program has its own checker pool. Each checker is made on its own
  worker thread and stays there (Go `checkerPool`: 4 checkers, file `i`
  goes to checker `i % 4`). The loading thread sends jobs and merges the
  results in file order. `program::release_program` joins the workers of
  the pool; the released program must not be current on the calling thread.
- Thread-local state (synthetic nodes, node and symbol ids, lazy JSDoc,
  caches) is per thread. A worker starts from a copy of the loading
  thread's state (`WorkerSeed`), so each checker's results depend only on
  its own files, not on thread timing.
- One thread can hold checkers of several programs (the language server's
  dispatch thread). Make a checker's program current while the checker runs
  (`core::enter_program`): the `program.rs` functions that checker code
  calls read `prog()`. The ids of the symbols that a checker adds are kept
  per checker arena (`SymbolArena::for_checker`, `ast::get_symbol_id`), and
  the module specifier caches per program (`modulespecifiers/host.rs`), so
  checkers of different programs do not share them.
- The Go frontend program is not thread-safe. Only the loading thread reads
  it (one frontend per program version); checker code reads the copies in
  `program::go_frontend::GoSharedState`.
- Emit (`emitter/`, `transformers/`, `printer/`, `bin/goport_emit.rs`)
  runs each file on its checker's thread with no checker borrowed
  (`program::run_on_checker_threads_for_files`); the emit resolver borrows
  the checker itself.
- Transformers return factory (synthetic) SourceFiles. `source_file_info`
  and the printer's identifier set map one to the parsed file with the same
  path (Go `copyFrom`). `get_ecma_line_starts` caches its line map by node,
  because all synthetic nodes share one file index. Read fields that the
  transforms set with `source_file_parser_fields`.

## Release builds

- Build release binaries with the workspace `goport` profile:
  `scripts/run-cargo-capped.sh build --profile goport -p ts_goport --bins`.
  It inherits `release` and adds `lto = "fat"` and `codegen-units = 1`.
  Other crates keep the default release settings. The binaries land in
  `<target>/goport/`, not `<target>/release/`.
- Allocator: glibc malloc is the default. `bin/goport.rs`
  `set_malloc_tunables` re-execs once with `GLIBC_TUNABLES` set; `tsgo` and
  `goport_build` have copies. `top_pad=67108864` makes each thread heap
  read-write in full when glibc makes it, so THP `always` maps it with
  2 MiB pages. Without it, glibc before 2.44 (cup2, alvin) grows the heaps
  in 4 KiB steps and every new page faults. On cup2 the settings cut
  `tsgo` wall time by 26% to 42% (perf9 round 1). `arena_max` and the
  parse and bind thread caps come from one budget (`program::ThreadBudget`),
  which each binary installs at start. `goport` and `tsgo`
  (`ThreadBudget::one_program`) have one arena for each thread that is
  alive while the checkers run: 6 in `goport`, 7 in `tsgo` (its signal
  thread). The parse mallocs most, so it runs at most 5 threads (4 workers
  and the loading thread), which fit these arenas; with 8 parse threads at
  16 cores the parse threads shared arena locks. A large program (128 or
  more root tasks, `program::note_program_load`: hono, zod, effect,
  elysia) adds up to 3 parse workers at 8 or more cores, and the budget
  has one spare arena for each (9 in `goport`, 10 in `tsgo`). The bind
  mallocs little: a large program binds on 8 threads, which share arenas.
  A program that is not large (query) binds on 4 threads when there are
  spare arenas, so its bind threads take the arenas of the ended parse
  workers and it makes no more arenas than with 6 or 7 (query at 16
  threads with 8 bind threads: 10 arenas, +4 MB). `goport_build` (about 20
  threads per program) and bins that install no budget keep
  `ThreadBudget::WIDE`: 8 parse and 8 bind threads, 16 arenas in
  `goport_build`. Each arena in use raises peak RSS. Keep query peak RSS
  under 1.15 times Go tsgo (119 MB, so 137 MB): at 16 cores `tsgo` has 129
  to 132 MB (7 parse threads with 10 arenas: 143 MB). jemalloc and
  mimalloc have the same speed as these settings on cup2 but more RSS
  (jemalloc query 143 to 153 MB), so the `jemalloc` feature stays off.
- PGO: `scripts/build-pgo.sh [out-dir]` does an instrumented build
  (`-Cprofile-generate`), trains on query, hono, zod, effect, elysia and
  about 200 corpus cases (plus `tsgo --noEmit` on the five projects and
  `goport_emit` on query and hono), merges with `llvm-profdata` and builds
  with `-Cprofile-use`. Output must stay byte-identical to the plain
  `goport` build; verify the PGO binary like any other. The gate does not
  run `tsgo`, so check it separately. The binaries (with `tsgo`) land in
  `<out-dir>/target-use/goport/`.
  Round 5 (1.95): 9% faster on query and 12 to 15% on hono, zod, effect and
  elysia, with the same peak RSS.
  Retrain when the allocator or hot code changes.
- PGO toolchain: the script sets `RUSTUP_TOOLCHAIN=1.95.0` unless it is
  already set. The system `llvm-profdata` is LLVM 22, which matches rustc
  1.95 (LLVM 22). rustc 1.93 (LLVM 21) cannot read the indexed format 13
  that LLVM 22 writes, and it only warns and builds without the profile.
  The script checks that `llvm-profdata` is not newer than rustc's LLVM and
  stops on a mismatch. For another toolchain, use
  `rustup component add llvm-tools` or set `LLVM_PROFDATA`.
- BOLT: `scripts/build-bolt.sh <bin-dir> [out-dir]` makes BOLT copies of
  `tsgo` and `goport`, normally of the PGO bins. It runs on zbook (perf
  LBR samples; perf cannot profile on cup2 or alvin): it records the five
  projects at 4 cores and 16 threads, then runs `perf2bolt`, `merge-fdata`
  and `llvm-bolt`. BOLT uses relocation mode (it also orders functions)
  when the bin has `.rela.text`; the PGO use build links with
  `--emit-relocs` for this. The script writes the BOLT bins only when their
  stdout, stderr and exit code equal the input bins on every run. BOLT
  rewrites machine code, so run the gate, the language-server batteries and
  the `tsgo` stdout check against Go tsgo on the BOLT bins. `build-pgo.sh`
  `PGO_LINK=nopie` or `static` links a non-PIE bin, like Go tsgo; BOLT
  refuses static bins. Round 3 on cup2 (PGO with `PGO_LINK=nopie`, then
  BOLT, against the plain `goport` build of the same source): query 15 to
  20% faster, hono 13 to 20%, zod 13 to 18%, effect 21 to 24%. BOLT alone
  (against the PGO bins) gave 0 to 9%.

## Style

- No `unsafe`. No new dependencies beyond these: `bumpalo` (the AST arena
  in `ast/store.rs`) and the optional `tikv-jemallocator` (feature
  `jemalloc`). Lints are relaxed crate-wide; still write clean Rust.
- Keep a `// Go: file.go:LINE funcName` comment above each ported function.
- Use `#[allow]` sparingly; do not add crate attributes.

## Language service

These rules add to the rules above for the language-service port: Go
`internal/{ls,lsp,project,format,astnav,api,fswatch,jsonrpc}`,
`cmd/tsgo`, and the small parts of other packages they need. The wave plan
is `target/continuation-r97-goport/ls-port/plan.md` in the main checkout.
Where this section and a rule above differ, this section wins for these
files.

The shared-shape sections of the area maps in the same directory are also
binding, except where this section says otherwise: `map-lsproto.md` section
3, `map-ls-completions.md` section 2, `map-ls-navigation.md` section 2,
`map-ls-edits.md` section 3, `map-project.md` section 4 and the U1 contract
in `map-watch-api.md`.

### Ownership

- A unit owns the files the plan lists for it. Some units own several new
  files. A few also own one existing file for one wave. Write nothing else.
- Root (the integrator) owns `lib.rs`, every `mod.rs`, the `mod` lines of
  the module-root file `program.rs`, `Cargo.toml` and `Cargo.lock`. Root
  also writes each package `prelude` (inside that package `mod.rs`).
- Nobody edits `src/prelude.rs` or `src/frontend/prelude.rs` for this
  port. Language-service packages are never glob-exported into them.
- Do not run cargo.
- The rule "skip language-service-only exported APIs" above no longer
  applies. `checker/exports.go` and `checker/services.go` are ported now.

### Modules, files and imports

- A Go package becomes the Rust module at the same path:
  `internal/ls/lsutil` -> `crate::ls::lsutil`, `internal/lsp/lsproto` ->
  `crate::lsp::lsproto`, `internal/project/dirty` ->
  `crate::project::dirty`, `cmd/tsgo` -> `crate::cmd::tsgo`.
- A Go file becomes one Rust file with the Go base name in snake case
  (`importTracker.go` -> `import_tracker.rs`, `box.go` -> `box_.rs`). A Go
  file split by line ranges uses `_p1`, `_p2`, ... in Go order.
- Small parts of other Go packages go in the files the plan names:
  `src/frontend/core_*.rs` (Go `internal/core`),
  `src/frontend/stringutil_ls.rs`, `src/frontend/scanner/scanner_ls.rs`,
  `src/ast/source_file_ls.rs`, `src/program/ls_program.rs`.
- Every file of a language-service package starts with exactly one glob
  import, its own package prelude, by absolute path. Examples:
  `use crate::ls::prelude::*;`, `use crate::ls::lsutil::prelude::*;`,
  `use crate::lsp::lsproto::prelude::*;` (also in generated files),
  `use crate::project::dirty::prelude::*;`. Add no other glob. Import
  anything else by explicit path.
- A package prelude re-exports the crate prelude (not in `lsproto`, see
  below), every item of the package's own files, the packages that the Go
  package imports as module names, and `Context`, `GoError`, `LspAny`.
  When two globs export the same name, root adds an explicit pick in the
  prelude. The package's own item wins, as in Go.
- Module names in the preludes: `lsproto`, `jsonrpc`, `lsutil`, `lsconv`,
  `change`, `autoimport`, `astnav`, `format`, `ls`, `project`, `dirty`,
  `logging`, `background`, `ata`, `fswatch`, `lspwatcher`, `api`, `lsp`,
  `gostd`, `locale`, `compiler` (`frontend::compiler`), `tsoptions`,
  `tspath`, `vfs`, `module`, `packagejson`, `modulespecifiers`,
  `sourcemap`, `json_ext`, `scanner_ls`, `ls_program`
  (`program::ls_program`).
- Call another Go package through its name, as Go does:
  `lsproto::Hover`, `lsutil::UserPreferences`,
  `astnav::get_token_at_position(file, pos)`,
  `format::format_document(ctx, file)`. Always write
  `lsutil::UserPreferences` in full; `modulespecifiers` has its own
  `UserPreferences`.
- A new file in an existing module keeps that module's header:
  `use crate::prelude::*;` (checker, printer, ast, sourcemap,
  modulespecifiers), `use crate::frontend::prelude::*;` (frontend), or
  `use super::*;` (children of `program`).
- `lsproto` files do not see the crate prelude. It exports `Diagnostic`,
  `FormattingOptions` and `Message`, and lsproto defines the same names.
  The lsproto prelude holds the JSON items, `json_ext`, `IndexMap`, `Cow`,
  `gostd`, `tspath` and `unported`. Inside lsproto, write
  `crate::jsonrpc::X` in full (lsproto has its own `jsonrpc` module).
- A Go package-private name that another Go file of the same package uses
  is `pub` in Rust. Never rename a Go name to avoid a clash; the prelude
  picks.

### Threads

One thread runs all language-service state: the LSP dispatch thread. It
loads programs and owns the session, projects, file systems
(`Rc<dyn Fs>`), programs, checkers and language services. It runs every
request. These types use `Rc` and `RefCell` and are not `Send`. Other
threads (stdin reader, stdout writer, progress reporter, parent watchdog,
fswatch backends and debouncers, timer wake-ups) touch only `Send` data.
Factory nodes and cached tokens are thread-local, which is correct
because every request runs on the dispatch thread.

### Go runtime (`crate::gostd`)

| Go | Rust |
|---|---|
| `ctx context.Context` param | `ctx: &Context` (`gostd::context::Context`, `Clone + Send + Sync`) |
| `context.Background`, `WithCancel`, `WithCancelCause`, `WithTimeout`, `WithDeadline`, `WithValue`, `AfterFunc`, `Cause` | `gostd::context::{background, with_cancel, with_cancel_cause, with_timeout, with_deadline, with_value, after_func, cause}` |
| `ctx.Err()`, `ctx.Done()` | `ctx.err() -> Option<GoError>`, `ctx.done() -> Option<Done>` (`None` is Go's nil channel) |
| context key and value | `pub static KEY: ContextKey<T> = ContextKey::new("goName");`, `with_value(&ctx, &KEY, v)`, `ctx.value(&KEY) -> Option<Arc<T>>` (`T: Send + Sync + 'static`) |
| `error` | `GoError` (`gostd::errors`, `Clone + Send + Sync`) |
| `(T, error)` / `error` result | `Result<T, GoError>` / `Result<(), GoError>`; an `error` param or field that can be nil is `Option<GoError>` |
| package var `errors.New("x")` | `pub static ERR_X: LazyLock<GoError> = LazyLock::new(\|\| errors::new("x"));` |
| `fmt.Errorf("..%w..", a, b)` | `errors::errorf(text, vec![a, b])`, text built with `format!` |
| typed error value (`lsproto.ErrorCode`, a struct) | `errors::from_value(v)` |
| `errors.Is`, `errors.As` / `AsType[T]`, `errors.Join` | `errors::is(&err, &target)`, `errors::as_type::<T>(&err)`, `errors::join(errs)` |
| `io.EOF`, `context.Canceled`, `context.DeadlineExceeded` | `errors::EOF`, `context::CANCELED`, `context::DEADLINE_EXCEEDED` |
| `err.Error()` | `err.error()` |
| `go f()` that touches dispatch-thread state | `gostd::local::go(Box::new(f))`: FIFO on the dispatch thread, run by `local::run_pending()` |
| `go f()` over `Send` data only | `std::thread::spawn` |
| `sync.WaitGroup`, `wg.Go`, `core.WorkGroup`, `errgroup` over dispatch-thread state | serial, in Go start order, like Go's single-threaded `WorkGroup`; keep the `ctx.err()` checks |
| `errgroup.WithContext` over `Send` loops | `gostd::errgroup` (real threads) |
| `chan T` with capacity n / unbuffered | `std::sync::mpsc::sync_channel(n)` / `sync_channel(0)`; `select` with `default` is `try_send` / `try_recv`; `select` on `ctx.Done()` is a `recv_timeout` loop that checks `ctx.err()` (PORT note) |
| `sync.Mutex`, `RWMutex`, `atomic.*` on dispatch-thread data | a plain field, `Cell` or `RefCell` (drop the lock) |
| the same on cross-thread data | `std::sync::{Mutex, RwLock, atomic}` |
| `sync.Once`, `OnceValue`, `OnceFunc` | `OnceCell`, `OnceLock`, `LazyLock`, or a `Cell<bool>` guard |
| `time.AfterFunc(d, f)` that touches dispatch-thread state | `gostd::local::after_func(d, Box::new(f)) -> LocalTimer` (`stop() -> bool`, `reset(d)`); `f` runs on the dispatch thread |
| `time.Timer`, `Ticker`, `AfterFunc` over `Send` data | `gostd::timer::{Timer, Ticker, after_func}` |
| `time.Now`, `time.Since`, `time.Duration` | `std::time::{Instant, SystemTime, Duration}` |
| `defer f()` | a guard, or an explicit call on every return path |
| `recover()` | `std::panic::catch_unwind(AssertUnwindSafe(..))`; `unported!` panics are recovered like Go panics |
| `panic(x)` | `panic!` with the Go text |
| `slices.SortFunc`, `sort.Slice` (not stable) | `gostd::slices::sort_func(&mut v, cmp)`, `gostd::slices::sort_slice(&mut v, less)` (Go pdqsort: equal elements end where Go puts them) |
| `slices.SortStableFunc`, `sort.SliceStable` | `v.sort_by(..)` (all stable sorts agree) |
| `slices.BinarySearchFunc` | `gostd::slices::binary_search_func(&v, target, cmp) -> (usize, bool)` |
| `strconv.Quote`, `%q` | `gostd::strconv::quote(s)` |
| `net/url` (`Parse`, `PathEscape`, `QueryEscape`, `PathUnescape`), `net/netip.ParseAddr` | `gostd::url::{parse, path_escape, query_escape, path_unescape}`, `gostd::netip` |
| `regexp` with `\p{..}` classes, `unicode` range tables | `gostd::regexp`, `gostd::unicode_tables` (go1.26.8, Unicode 15.0.0, generated) |
| x/text `collate`, `unicode/norm` (organize imports) | `gostd::collate`, `gostd::norm` (tables in `gostd/data/`, generated); `language.Compose`, `Parent`, `TypeForKey`, compact tags in `locale.rs` |
| `signal.NotifyContext(ctx, os.Interrupt, syscall.SIGTERM)` | `cmd::tsgo::main::notify_context` (`signal-hook`) |
| `panic(x)` that the pinned Go reaches on the same input and nothing recovers | `core::go_panic(text)`: the bins print `panic: <text>` and exit 2 |
| `%v`, `%+v`, `%T` in log text | `format!("{:?}", x)` with a PORT note (log text is not compared) |
| Go map iteration that reaches output | `IndexMap` in insertion order and `// PORT: Go map order is random`; the oracle compares that output without order |
| `collections.OrderedMap` | `IndexMap` (`Delete` is `shift_remove`) |
| `collections.SyncMap`, `SyncSet`, `Set`, `MultiMap` | `RefCell<FxHashMap>`, `FxHashSet`, `IndexMap<K, Vec<V>>` |
| `core.IfElse(c, a, b)` | `if c { a } else { b }`; evaluate both first only if an argument has a side effect (Go evaluates both) |
| `core.Filter`, `Map`, `Find`, `Some`, `Every`, `FlatMap`, `FirstOrNil`, ... | iterator code with the same order and the same nil-versus-empty result |
| `diagnostics.X.Localize(loc, args...)`, `locale.FromContext(ctx)` | `diagnostics_loc::message_localize(diag::X, &loc, &args![..])`, `locale::from_context(ctx)`; `Locale` is the Go `language.Tag` |
| `stringutil.Compare*`, `EquateStringCaseInsensitive`, `TruncateByRunes` | `crate::frontend::stringutil_ls` |
| `stringutil.IsLineBreak`, `IsWhiteSpace*`, `StripQuotes` | the existing `scanner_util` names |
| Go `string` indexes and positions | byte offsets (`as_bytes()`); decode runes with the `pub(crate)` `utf8_decode_rune_in_string` / `utf8_decode_last_rune_in_string` in `frontend/scanner/scanner_p1.rs`; never slice a `&str` inside a character |

Dispatch loop contract (lsp server and session): the server calls
`gostd::local::set_waker(f)` once. A due `LocalTimer` calls the waker from
its timer thread. The dispatch loop calls `local::run_pending()` after
each message and after each wake-up. Go `WaitForBackgroundTasks` runs
`local::run_pending()` until the queue is empty.

### Programs and checkers

- Go `*compiler.Program` in ls, project and api code is
  `&'static compiler::NewProgram` (leaked for the process like
  `GoProgram`; `Copy`; pointer equality is `std::ptr::eq`; a map key is
  `p as *const _ as usize`).
- Go `compiler.NewProgram(opts)` is `ls_program::new_program(opts,
  create_checker_pool)`; `p.UpdateProgram(..)` is
  `ls_program::update_program(p, ..)`. Go `ProgramOptions.CreateCheckerPool`
  is the extra `create_checker_pool` argument (PORT).
- Every program made by `ls_program::new_program` or
  `ls_program::update_program` is a program version of the process
  (`program::new_program_version`), as Go makes a new `Program` for each
  snapshot change. Versions share the file versions they have in common.
  The checkers of every version are made on the dispatch thread.
- Current program: checker code reads `prog()`. `ls_program::enter(p)`
  makes `p` current while its `ProgramGuard` lives; the last guard that is
  still alive wins, so guards can drop in any order. A language service
  holds a guard for its program, the `get_type_checker*` functions return
  a `Release` that holds one, and the `ls_program` diagnostics functions
  enter `p`. A caller that uses several language services in turn calls
  `ls.enter_program()` for each. A checker from a pool of its own gets its
  guard with `ProgramGuard::with_release`.
- Release: `ls_program::release_program(p)` is Go's program drop (the
  snapshot `programCounter.Deref`). It frees the checker pools of `p` and
  its program version now, or when the last guard of `p` drops. The
  `NewProgram`, the `GoProgram` shell and the file versions stay leaked
  (multi-program M2, M3).
- Go `*ast.SourceFile` is `Node` (the file root). An `Rc<ParsedSourceFile>`
  from a `NewProgram` method becomes `file.root`.
- Go `p.X(..)` on a program: call `NewProgram::x` when it exists; else
  `ls_program::x(p, ..)` when the plan lists it (checker and diagnostics
  methods); else the `program::x` free function (it reads the current
  program); else `unported!("Program.X")`.
- `c, done := p.GetTypeCheckerForFile(ctx, file); defer done()` becomes
  `let (checker, done) = ls_program::get_type_checker_for_file(p, ctx, file);`
  and `let c = &mut *checker.borrow_mut();`. Keep `done` (a `Release`
  guard) alive to the end of the scope; it releases once, on drop or on
  `done.call()`. Helper functions take `c: &mut Checker`, never the `Rc`.
  Never borrow the checker twice.
- Go `compiler.CheckerPool` is the trait `ls_program::CheckerPool`
  (`get_checker(&self, ctx: &Context, file: Node) -> (Rc<RefCell<Checker>>, Release)`,
  `file` may be `Node::NIL`). The project pool implements it. Go
  `checker.NewChecker(program)` is `ls_program::new_checker(program)`.
- Checker API names: `checker-api-tools/names_exports_services.tsv`
  (the new `checker/exports.rs` and `checker/services.rs`) and
  `checker-api-tools/ported_ls_names.tsv` (existing ports), both next to
  the maps. When Go calls an exported wrapper whose unexported twin also
  exists, the Rust name ends in `_exported`. Never call the twin in its
  place.
- Node builder `idToSymbol`: Go shares one map between the builder and its
  caller. Build with `new_node_builder_ex(c, ec, Some(FxHashMap::default()))`
  and read the filled map back from `nb.impl_.borrow().id_to_symbol`. For
  a printer, move the map into `Printer.id_to_symbol`. Add a PORT note.
- A file that the language server parses outside a program load (the
  parse cache, `getOrParseSourceFile` in sourcedefinition.go) is recorded
  with `program::note_parsed_source_file`, so the next publish gives it
  its parser fields. To read it before a program includes it, publish it
  with `program::publish_parsed_files` and bind it with
  `program::bind_file_outside_program` (Go `BindSourceFile`).
- The autoimport `aliasResolver` (a checker over node_modules files that no
  program holds) makes its own program version
  (`program::new_alias_resolver_program`). Before it makes the checker, it
  reads every file that a string module name in its files can resolve to
  (imports, exports, `require`, import types, JSDoc imports, relative names
  inside `declare module "x" {}`), so the checker arena holds them. It can
  read more files than Go; it never reads fewer. A file that this walk
  misses reaches `unported!("aliasResolver.GetSourceFile after NewChecker")`.

### Scanning

- ls, astnav and format code scan with the literal Go scanner
  `frontend::scanner::Scanner`, not `RsScanner`.
- Go `scanner.GetScannerForSourceFile(f, pos)` is
  `scanner_ls::get_scanner_for_source_file(f, pos)` and
  `scanner.GetECMAPositionOfLineAndByteOffset` is
  `scanner_ls::get_ecma_position_of_line_and_byte_offset`. Other Go
  `scanner.X` free functions (`SkipTrivia`, `GetTokenPosOfNode`,
  `TokenToString`, ...) are the existing `scanner_util` names.

### Protocol types (`lsproto`)

- `src/lsp/lsproto/lsp_generated/*.rs` is generated by
  `src/lsp/lsproto/_generate/generate.mts` (a port of Go's generator) from
  the pinned `metaModel.json`. Never edit the output by hand. Change the
  generator, then run `node --experimental-strip-types generate.mts`.
- Names and shapes follow `map-lsproto.md` section 3. Short form: type
  names keep the Go spelling (`HoverParams`, `URI`, `DocumentUri`); fields
  are snake case (`text_document`, `type_`); `*T` is `Option<T>`
  (`Option<Box<T>>` only on a type cycle); `*[]T` is `Option<Vec<T>>`;
  `[]T` and `[]*T` are `Vec<T>`; `map[K]V` is `IndexMap<K, V>`; LSPAny is
  `LspAny`; a string enum is `pub struct MarkupKind(pub Cow<'static, str>)`
  with consts such as `MarkupKind::PLAIN_TEXT`; an int enum is
  `pub struct CompletionItemKind(pub i32)` with consts; method consts are
  `Method::TEXT_DOCUMENT_HOVER`; `TextDocumentHoverInfo` is
  `TEXT_DOCUMENT_HOVER_INFO: RequestInfo<HoverParams, TextDocumentHoverResponse>`;
  a union is a struct of `Option` fields (all `None` is null); a literal is
  a unit struct; `*Response` aliases are `pub type`; `(v *X) resolve()` is
  `X::resolve(v: Option<&X>)`.
- Go `any` in `RequestMessage.Params` and `ResponseMessage.Result` is
  `Box<dyn AnyValue>`. Read it with `downcast_ref::<HoverParams>()`.
- Client capabilities in a context:
  `lsproto::with_client_capabilities(&ctx, caps) -> Context` and
  `lsproto::get_client_capabilities(&ctx) -> Arc<ResolvedClientCapabilities>`.
- `lsproto::ErrorCode` is also a `GoError` value
  (`errors::from_value(code)`), so `errors::as_type::<lsproto::ErrorCode>`
  finds it in a wrap chain.

### JSON

- All JSON uses `frontend/json.rs` (`MarshalerTo`, `UnmarshalerFrom`,
  `JsonDecoder`) and `frontend/json_ext.rs` (the Go JSON v2 default
  arshalers for integers, floats, `Option`, `Box`, `Vec`, `[u32; 2]`,
  `IndexMap`, `LspAny`, `JsonValue`, one-line field helpers, and
  `marshal_indent`). No serde.
- A hand-written Go struct with `json:"..."` tags (Go marshals it by
  reflection) gets a hand-written `MarshalerTo` and `UnmarshalerFrom` with
  the v2 default rules: fields in declaration order; `omitzero` skips the
  zero value; `omitempty` skips `null`, `""`, `[]` and `{}`; a non-omit
  `None` writes `null`; a non-omit nil slice or map writes `[]` or `{}`;
  input names match exactly and unknown names are skipped; `null` input
  sets the zero value.
- Go `json.Value` is `JsonValue(Vec<u8>)`. Go `map[string]any` is
  `IndexMap<String, LspAny>`.
- A `float64` field writes the ES6 number text (as v2). An integer field
  rejects `1.0` and `1e2` (as v2).
- `null`, `[]` and a missing key are different values. Maps write keys in
  insertion order. Go writes random order unless it sets
  `json.Deterministic(true)`; then sort the keys as Go does.

### `goport --lsp`

- `bin/goport.rs` sends `--lsp` and `--api` to `cmd::tsgo::run_main` before
  anything is written to stdout.
- A request that reaches `unported!` gets a `-32603` error response through
  the server's `recover`. At exit, goport returns the Go status (0 or 1)
  unless unported code ran; then it prints the unported report on stderr
  and exits 70 (`EXIT_UNPORTED`).

### Not ported (plan level)

- The kqueue, FSEvents and Windows file watchers. The in-process LSP
  watcher (`lsp/lspwatcher`) needs one of them, so on Linux it is never
  made (as in Go) and its callback delivery stays `unported!`. The Linux
  watchers (fanotify, inotify) are ported in `src/fswatch/unix.rs` with
  safe crates (`nix::sys::fanotify`, `name-to-handle-at`, `rustix`, `std`;
  D-W1). No `libc`, no `unsafe`.
- One dispatch thread (see "Threads"): the server answers requests in
  arrival order, where Go runs the async part of a request on a goroutine
  and answers in finish order. Timers and background tasks run at message
  boundaries. The checker is never canceled, so a canceled diagnostic
  request answers `-32800` after the full check. The results are Go's; only
  order and timing differ.
- Go runtime profiles (pprof) have no samples: the port writes Go's file
  names, errors and log lines and valid empty profiles. `runtime.GC` is a
  no-op. `runtime/metrics` reads as `KindBad`, so the Go runtime fields of
  performance telemetry are 0.
- API handles across checkers: a type, signature or checker-made symbol of
  one project sent with another project of the same snapshot stays
  `unported!` (a Rust id indexes one checker's arena).
- Windows named pipes (`--api --pipe` on Windows) return an error.
