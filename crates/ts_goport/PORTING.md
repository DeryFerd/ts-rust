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
the installed `&'static GoProgram`. `Node` methods reach the AST through it.
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

## Program (owned by program.rs)

`core::GoProgram` and `core::GoFile` are fixed. `program.rs` defines
`SourceFileInfo`, `load`, `bind_all`, the Go `Program` methods as free
functions with Go snake names (`get_resolved_module(file, name, mode)` ->
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
be 3 or 4. Unported code, any other panic, a worker-thread failure and a
failed build worker exit `execute::tsc::EXIT_UNPORTED` (70,
`EX_SOFTWARE`). Go uses 0 to 5 (3 in cmd/tsgo/sys.go:66, 4 in build mode,
5 NotImplemented), so a harness must treat a goport exit of 70 as a crash,
never as a tsgo status.

A site where the pinned Go panics on the same input uses
`core::go_panic(message)`, not `panic!`. It is not a port gap: the guards
that keep a run going pass it on (`core::resume_go_panic`), and the bins
end the run as the Go runtime does. The output written so far stays,
stderr gets `panic: <message>` (then the port site in place of the
goroutine trace), and the exit code is 2 (`core::EXIT_GO_PANIC`). A build
worker exits 2 with no result line, and the orchestrator then exits 2 too.

## Threads

- `prog()` and the program state are process-wide and read only after
  load, so they hold only thread-safe data (`Arc`, `OnceLock`, `Mutex`).
- Files bind in parallel, each into its own arena, and join the program
  arena in file order (`program::bind_all`). The ids equal a serial bind.
- Each checker is made on its own worker thread and stays there (Go
  `checkerPool`: 4 checkers, file `i` goes to checker `i % 4`). The loading
  thread sends jobs and merges the results in file order.
- Thread-local state (synthetic nodes, node and symbol ids, lazy JSDoc,
  caches) is per thread. A worker starts from a copy of the loading
  thread's state (`WorkerSeed`), so each checker's results depend only on
  its own files, not on thread timing.
- The Go frontend program is not thread-safe. Only the loading thread reads
  it; checker code reads the copies in `program::go_frontend::GoSharedState`.
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
  `set_malloc_tunables` re-execs once with `GLIBC_TUNABLES` set. The
  `jemalloc` feature is faster (about 10% on query, 5% on zod and effect)
  but puts query peak RSS about 15% over tsgo, so it is off. It can become
  the default if query peak RSS drops by about 20 MB elsewhere (for example
  fewer parse or bind threads). Then retest query RSS with `narenas:4`.
- PGO: `scripts/build-pgo.sh [out-dir]` does an instrumented build
  (`-Cprofile-generate`), trains on query, hono, zod, effect, elysia and
  about 200 corpus cases (plus `goport_emit` on query and hono), merges with
  `llvm-profdata` and builds with `-Cprofile-use`. Output must stay
  byte-identical to the plain `goport` build; verify the PGO binary like
  any other. The binaries land in `<out-dir>/target-use/goport/`.
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

## Style

- No `unsafe`. No new dependencies beyond these: `bumpalo` (the AST arena
  in `ast/store.rs`) and the optional `tikv-jemallocator` (feature
  `jemalloc`). Lints are relaxed crate-wide; still write clean Rust.
- Keep a `// Go: file.go:LINE funcName` comment above each ported function.
- Use `#[allow]` sparingly; do not add crate attributes.
