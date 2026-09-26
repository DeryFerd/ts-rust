//! Synthetic AST nodes: the nodes Go creates with `ast.NodeFactory`.
//!
//! Go factory nodes are ordinary `*ast.Node` values. Here a synthetic node is
//! a `Node` handle whose file index is `SYNTHETIC_NODE_FILE`. Its low 32 bits
//! index a thread-local slot list (like `SYNTHETIC_FLOW_FILE` for flow nodes).
//!
//! Each node slot holds a leaked `ts_ast::Node` (kind and `NodeData`), so every
//! accessor in `node.rs` and `fields.rs` that matches on `NodeData` works on
//! synthetic nodes without changes. Child ids inside that data are ids in the
//! synthetic id space:
//! - a synthetic child uses its own slot index;
//! - a parsed child (Go shares the pointer) uses an alias slot. `Node::new`
//!   resolves an alias slot to the parsed node, so identity is kept:
//!   `synthetic.name() == parsed_name` is true, like Go pointer equality;
//! - Go `nil` in a field that ts_ast stores as a required `NodeId` uses slot 0,
//!   which resolves to `Node::NIL`.
//!
//! Go mutates factory nodes after creation (`node.Parent = p`, `node.Loc = l`,
//! `node.Flags |= f`, `node.FlowNodeData().FlowNode = f`,
//! `node.AsX().Symbol = s`). Those fields live in the slot, not in the leaked
//! `ts_ast::Node`, and `node.rs` reads them through the hooks below.
//!
//! PORT: parsed nodes are immutable. The setters panic on a parsed node,
//! except on a node of a ported-parser file that the parser has not finished
//! (`ast/store.rs`). Go code that writes a field of a parsed node needs its
//! own port decision.

use crate::prelude::*;
use ts_ast::NodeData;

/// File index of synthetic nodes. `SYNTHETIC_FLOW_FILE` is `0xffff_ffff`.
pub const SYNTHETIC_NODE_FILE: usize = 0xffff_fffe;

/// Slot 0: Go `nil` stored in a ts_ast field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// One synthetic slot.
#[derive(Clone)]
enum Slot {
    /// Go `nil`. Only slot 0.
    Nil,
    /// A parsed node used as a child of a synthetic node.
    Alias(Node),
    /// A node the factory created.
    Node(SyntheticNode),
}

/// The mutable Go `NodeBase` fields of a factory node.
#[derive(Clone)]
struct SyntheticNode {
    node: &'static ts_ast::Node,
    parent: Node,
    flags: NodeFlags,
    loc: TextRange,
    /// Go `DeclarationData().Symbol`, `FlowNodeData().FlowNode`, ... Replaced
    /// (and the old value leaked) on each write, so `bind()` can return
    /// `&'static`. Writes are rare.
    bind: &'static NodeBindData,
    /// Go `SyntheticExpression.Type.(*Type)`. Nil for other kinds.
    synthetic_type: TypeId,
    /// The Go `ast.SourceFile` fields of a factory SourceFile. `None` for
    /// other kinds.
    source_file: Option<Box<SyntheticSourceFileData>>,
}

/// The Go `ast.SourceFile` fields (other than `Statements` and
/// `EndOfFileToken`, which are in the node data) of a SourceFile that the
/// factory made: `NewSourceFile` sets the first group, `copyFrom` and later
/// Go writes (`result.AsSourceFile().IsDeclarationFile = true`) set the rest.
// PORT: a parsed SourceFile keeps these fields in `SourceFileInfo`. ts_ast
// node data cannot hold them, so a factory SourceFile keeps them in its slot.
// Go `parseOptions` is kept as its file name and path; the external module
// indicator options are only read by the parser. `ContainsNonASCII` and
// `Identifiers` are not in `SourceFileInfo`, so `copyFrom` cannot copy them
// from a parsed file and they are not kept.
#[derive(Clone, Debug, Default)]
pub struct SyntheticSourceFileData {
    // Fields set by NewSourceFile
    pub file_name: &'static str,
    pub path: String,
    pub text: &'static str,

    // Fields set by copyFrom (Go "fields set by parser") and later writes
    pub language_variant: LanguageVariant,
    pub script_kind: ScriptKind,
    pub is_declaration_file: bool,
    pub uses_uri_style_node_core_modules: Tristate,
    pub imports: Vec<Node>,
    pub module_augmentations: Vec<Node>,
    pub ambient_module_names: Vec<String>,
    pub comment_directives: Vec<CommentDirective>,
    pub pragmas: Vec<Pragma>,
    pub referenced_files: Vec<FileReference>,
    pub type_reference_directives: Vec<FileReference>,
    pub lib_reference_directives: Vec<FileReference>,
    pub common_js_module_indicator: Node,
    pub external_module_indicator: Node,
}

#[derive(Clone)]
struct SyntheticArena {
    slots: Vec<Slot>,
    /// Alias slot of each parsed node, so one parsed node gets one slot.
    aliases: FxHashMap<Node, u32>,
}

impl SyntheticArena {
    fn new() -> Self {
        Self {
            slots: vec![Slot::Nil],
            aliases: FxHashMap::default(),
        }
    }
}

static EMPTY_BIND: NodeBindData = NodeBindData {
    symbol: SymbolId::NIL,
    local_symbol: SymbolId::NIL,
    locals: SymbolTable::NIL,
    next_container: Node::NIL,
    flow_node: FlowNodeId::NIL,
    end_flow_node: FlowNodeId::NIL,
    return_flow_node: FlowNodeId::NIL,
    added_flags: NodeFlags::NONE,
};

thread_local! {
    static ARENA: RefCell<SyntheticArena> = RefCell::new(SyntheticArena::new());
}

/// A copy of the synthetic nodes of one thread (see `synthetic_seed`).
#[derive(Clone)]
pub struct SyntheticSeed(SyntheticArena);

/// A copy of the synthetic nodes made on this thread so far. A checker
/// worker starts from the nodes of the loading thread
/// (`install_synthetic_seed`), so the nodes that the parser and the binder
/// made keep their handles on every thread.
// PORT: Go factory nodes are shared pointers. Each checker thread owns a
// copy of the nodes made before the checkers started, and the nodes it
// makes itself.
#[must_use]
pub fn synthetic_seed() -> SyntheticSeed {
    ARENA.with(|a| SyntheticSeed(a.borrow().clone()))
}

/// The number of synthetic slots on this thread. Work that must not make
/// synthetic nodes compares it before and after.
#[must_use]
pub fn synthetic_slot_count() -> usize {
    ARENA.with(|a| a.borrow().slots.len())
}

/// Makes `seed` the synthetic nodes of this thread.
pub fn install_synthetic_seed(seed: SyntheticSeed) {
    ARENA.with(|a| *a.borrow_mut() = seed.0);
}

/// The handle of slot `index`. Does not resolve aliases.
const fn handle(index: u32) -> Node {
    Node(((SYNTHETIC_NODE_FILE as u64) << 32) | (index as u64 + 1))
}

/// Slot index of a synthetic handle.
fn slot_index(n: Node) -> usize {
    ((n.0 & 0xffff_ffff) - 1) as usize
}

/// True when `n` is a node that the factory created.
#[must_use]
pub fn is_synthetic_node(n: Node) -> bool {
    n.is_some() && n.file_index() == SYNTHETIC_NODE_FILE
}

/// Hook for `Node::new(SYNTHETIC_NODE_FILE, id)`: the Go node that a child id
/// inside synthetic `NodeData` stands for.
#[must_use]
pub fn resolve_synthetic_id(id: ts_ast::NodeId) -> Node {
    ARENA.with(|a| match &a.borrow().slots[id.index()] {
        Slot::Nil => Node::NIL,
        Slot::Alias(target) => *target,
        Slot::Node(_) => handle(id.index() as u32),
    })
}

/// Reads the node slot of a synthetic handle.
fn with_node<R>(n: Node, f: impl FnOnce(&SyntheticNode) -> R) -> R {
    ARENA.with(|a| match &a.borrow().slots[slot_index(n)] {
        Slot::Node(s) => f(s),
        _ => panic!("synthetic handle does not name a node slot"),
    })
}

/// Writes the node slot of a synthetic handle. Panics on a parsed node.
fn with_node_mut<R>(n: Node, f: impl FnOnce(&mut SyntheticNode) -> R) -> R {
    assert!(
        is_synthetic_node(n),
        "cannot mutate a parsed node (kind {:?})",
        n.kind()
    );
    ARENA.with(|a| match &mut a.borrow_mut().slots[slot_index(n)] {
        Slot::Node(s) => f(s),
        _ => panic!("synthetic handle does not name a node slot"),
    })
}

// ──────────────────────────────────────────────────────────────────────
// Read hooks for node.rs / fields.rs
// ──────────────────────────────────────────────────────────────────────

/// Hook for `raw(n)`: the ts_ast node (kind and data) of a synthetic node.
#[must_use]
pub fn synthetic_ast_node(n: Node) -> &'static ts_ast::Node {
    with_node(n, |s| s.node)
}

/// The ts_ast node of any node, parsed or synthetic. Go dereferences the
/// pointer, so nil panics. `node.rs` reads node data through this (`raw`).
#[must_use]
pub fn ast_node_of(n: Node) -> &'static ts_ast::Node {
    assert!(n.is_some(), "nil node dereference");
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return synthetic_ast_node(n);
    }
    if let Some(node) = try_store_ast_node(n) {
        return node;
    }
    prog().files[n.file_index()]
        .legacy_source()
        .parse
        .arena
        .get(n.node_id())
        .expect("node is not in its file arena")
}

/// The ts_ast data of any node, parsed or synthetic.
#[must_use]
pub fn ast_data_of(n: Node) -> &'static NodeData {
    &ast_node_of(n).data
}

/// Hook for `Node::flags` on a synthetic node.
#[must_use]
pub fn synthetic_flags(n: Node) -> NodeFlags {
    with_node(n, |s| s.flags)
}

/// Hook for `Node::parent` on a synthetic node.
#[must_use]
pub fn synthetic_parent(n: Node) -> Node {
    with_node(n, |s| s.parent)
}

/// Hook for `Node::loc` on a synthetic node.
#[must_use]
pub fn synthetic_loc(n: Node) -> TextRange {
    with_node(n, |s| s.loc)
}

/// Hook for `Node::bind` on a synthetic node.
#[must_use]
pub fn synthetic_bind(n: Node) -> &'static NodeBindData {
    with_node(n, |s| s.bind)
}

/// Go `node.AsSyntheticExpression().Type.(*Type)`.
#[must_use]
pub fn synthetic_expression_type(n: Node) -> TypeId {
    debug_assert!(n.kind() == SyntaxKind::SyntheticExpression);
    with_node(n, |s| s.synthetic_type)
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes on factory nodes
// ──────────────────────────────────────────────────────────────────────

/// Go `node.Parent = parent`. Works on factory nodes and on nodes of a
/// ported-parser file that is not finished.
pub fn set_node_parent(n: Node, parent: Node) {
    if is_store_node(n) {
        return set_store_node_parent(n, parent);
    }
    with_node_mut(n, |s| s.parent = parent);
}

/// Go `node.Loc = loc`.
pub fn set_node_loc(n: Node, loc: TextRange) {
    if is_store_node(n) {
        return set_store_node_loc(n, loc);
    }
    with_node_mut(n, |s| s.loc = loc);
}

/// Go `node.Flags = flags`.
pub fn set_node_flags(n: Node, flags: NodeFlags) {
    if is_store_node(n) {
        return set_store_node_flags(n, flags);
    }
    with_node_mut(n, |s| s.flags = flags);
}

/// A Go write to a data field of a node (`node.AsX().Field = v`): `data` is
/// the node's data with that field changed. Works on factory nodes and on
/// nodes of a ported-parser file that is not finished.
// PORT: ts_ast data is leaked and shared, so the node gets a new leaked
// ts_ast node with the same kind; the old one leaks. Writes are rare.
pub fn replace_node_data(n: Node, data: NodeData) {
    if is_store_node(n) {
        return replace_store_node_data(n, data);
    }
    with_node_mut(n, |s| {
        let kind = s.node.kind;
        debug_assert!(
            data.matches_syntax_kind(kind),
            "{kind:?} does not fit its NodeData"
        );
        s.node = crate::ast::store::leak_in_ast_arena(ts_ast::Node {
            kind,
            flags: ts_ast::NodeFlags(0),
            range: undefined_ts_range(),
            parent: None,
            data,
        });
    });
}

/// Go `node.Kind = kind` on a factory node. The new kind must fit the node
/// data (Go only does this between kinds with one data struct, such as
/// `KindJSImportDeclaration` to `KindImportDeclaration`).
// PORT: the kind lives in the leaked ts_ast node, so the node gets a new
// leaked ts_ast node with the same data; the old one leaks.
pub fn set_node_kind(n: Node, kind: SyntaxKind) {
    with_node_mut(n, |s| {
        let data = s.node.data.clone();
        assert!(
            data.matches_syntax_kind(kind),
            "{kind:?} does not fit the data of {:?}",
            s.node.kind
        );
        s.node = crate::ast::store::leak_in_ast_arena(ts_ast::Node {
            kind,
            flags: ts_ast::NodeFlags(0),
            range: undefined_ts_range(),
            parent: None,
            data,
        });
    });
}

/// Go `node.AsMutable().SetModifiers(modifiers)`.
// Go: ast/ast.go:227 (n *MutableNode) SetModifiers
// PORT: Go dispatches to `setModifiers` on the data. The kinds with a
// `modifiers` field set it (ModifiersBase, NamedMemberBase,
// BinaryExpression); other kinds do nothing, like Go `NodeDefault`.
pub fn set_node_modifiers(n: Node, modifiers: ModifierList) {
    let mods = synthetic_modifiers_value(modifiers);
    let mut data = ast_data_of(n).clone();
    match &mut data {
        NodeData::ArrowFunction(d) => d.modifiers = mods,
        NodeData::BinaryExpression(d) => d.modifiers = mods,
        NodeData::ClassDeclaration(d) => d.modifiers = mods,
        NodeData::ClassExpression(d) => d.modifiers = mods,
        NodeData::ClassStaticBlockDeclaration(d) => d.modifiers = mods,
        NodeData::ConstructorDeclaration(d) => d.modifiers = mods,
        NodeData::ConstructorTypeNode(d) => d.modifiers = mods,
        NodeData::EnumDeclaration(d) => d.modifiers = mods,
        NodeData::EnumMember(d) => d.modifiers = mods,
        NodeData::ExportAssignment(d) => d.modifiers = mods,
        NodeData::ExportDeclaration(d) => d.modifiers = mods,
        NodeData::FunctionDeclaration(d) => d.modifiers = mods,
        NodeData::FunctionExpression(d) => d.modifiers = mods,
        NodeData::FunctionTypeNode(d) => d.modifiers = mods,
        NodeData::GetAccessorDeclaration(d) => d.modifiers = mods,
        NodeData::ImportDeclaration(d) => d.modifiers = mods,
        NodeData::ImportEqualsDeclaration(d) => d.modifiers = mods,
        NodeData::IndexSignatureDeclaration(d) => d.modifiers = mods,
        NodeData::InterfaceDeclaration(d) => d.modifiers = mods,
        NodeData::MethodDeclaration(d) => d.modifiers = mods,
        NodeData::MethodSignatureDeclaration(d) => d.modifiers = mods,
        NodeData::MissingDeclaration(d) => d.modifiers = mods,
        NodeData::ModuleDeclaration(d) => d.modifiers = mods,
        NodeData::NamespaceExportDeclaration(d) => d.modifiers = mods,
        NodeData::ParameterDeclaration(d) => d.modifiers = mods,
        NodeData::PropertyAssignment(d) => d.modifiers = mods,
        NodeData::PropertyDeclaration(d) => d.modifiers = mods,
        NodeData::PropertySignatureDeclaration(d) => d.modifiers = mods,
        NodeData::SetAccessorDeclaration(d) => d.modifiers = mods,
        NodeData::ShorthandPropertyAssignment(d) => d.modifiers = mods,
        NodeData::TypeAliasDeclaration(d) => d.modifiers = mods,
        NodeData::TypeParameterDeclaration(d) => d.modifiers = mods,
        NodeData::VariableStatement(d) => d.modifiers = mods,
        _ => return,
    }
    replace_node_data(n, data);
}

/// Changes the binder data of a factory node: Go
/// `node.FlowNodeData().FlowNode = f`, `node.AsX().Symbol = s`, ...
pub fn update_node_bind(n: Node, f: impl FnOnce(&mut NodeBindData)) {
    with_node_mut(n, |s| {
        let mut bind = *s.bind;
        f(&mut bind);
        s.bind = Box::leak(Box::new(bind));
    });
}

/// Go `node.FlowNodeData().FlowNode = flow`.
pub fn set_node_flow_node(n: Node, flow: FlowNodeId) {
    update_node_bind(n, |b| b.flow_node = flow);
}

/// Go `node.AsX().Symbol = symbol` (declaration data).
pub fn set_node_symbol(n: Node, symbol: SymbolId) {
    update_node_bind(n, |b| b.symbol = symbol);
}

/// Go `node.AsX().LocalSymbol = symbol`.
pub fn set_node_local_symbol(n: Node, symbol: SymbolId) {
    update_node_bind(n, |b| b.local_symbol = symbol);
}

/// Go `node.AsX().Locals = locals`.
pub fn set_node_locals(n: Node, locals: SymbolTable) {
    update_node_bind(n, |b| b.locals = locals);
}

// ──────────────────────────────────────────────────────────────────────
// Allocation (used by factory.rs)
// ──────────────────────────────────────────────────────────────────────

/// Go `newNode(kind, data, hooks)`: a new factory node with
/// `Loc = UndefinedTextRange()`, nil parent, no flags and no binder data.
pub fn alloc_synthetic_node(kind: SyntaxKind, data: NodeData) -> Node {
    debug_assert!(
        data.matches_syntax_kind(kind),
        "{kind:?} does not fit its NodeData"
    );
    let node: &'static ts_ast::Node = crate::ast::store::leak_in_ast_arena(ts_ast::Node {
        kind,
        flags: ts_ast::NodeFlags(0),
        range: undefined_ts_range(),
        parent: None,
        data,
    });
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let index = a.slots.len() as u32;
        a.slots.push(Slot::Node(SyntheticNode {
            node,
            parent: Node::NIL,
            flags: NodeFlags::NONE,
            loc: TextRange::undefined(),
            bind: &EMPTY_BIND,
            synthetic_type: TypeId::NIL,
            source_file: None,
        }));
        handle(index)
    })
}

/// Sets the Go `SyntheticExpression.Type` of a new node.
pub(crate) fn set_synthetic_expression_type(n: Node, t: TypeId) {
    with_node_mut(n, |s| s.synthetic_type = t);
}

// ──────────────────────────────────────────────────────────────────────
// Factory SourceFile fields
// ──────────────────────────────────────────────────────────────────────

/// Attaches the Go `ast.SourceFile` fields to a new factory SourceFile.
pub(crate) fn set_synthetic_source_file_data(n: Node, data: SyntheticSourceFileData) {
    debug_assert!(n.kind() == SyntaxKind::SourceFile);
    with_node_mut(n, |s| s.source_file = Some(Box::new(data)));
}

/// True when `n` is a SourceFile that the factory made.
#[must_use]
pub fn is_synthetic_source_file(n: Node) -> bool {
    is_synthetic_node(n) && with_node(n, |s| s.source_file.is_some())
}

/// Reads the Go `ast.SourceFile` fields of a factory SourceFile.
pub fn with_synthetic_source_file<R>(n: Node, f: impl FnOnce(&SyntheticSourceFileData) -> R) -> R {
    with_node(n, |s| {
        f(s.source_file
            .as_deref()
            .expect("node is not a factory SourceFile"))
    })
}

/// Go writes to the fields of a factory SourceFile
/// (`file.AsSourceFile().IsDeclarationFile = true`, ...). Panics on a
/// parsed SourceFile (see the module comment).
pub fn update_synthetic_source_file<R>(
    n: Node,
    f: impl FnOnce(&mut SyntheticSourceFileData) -> R,
) -> R {
    with_node_mut(n, |s| {
        f(s.source_file
            .as_deref_mut()
            .expect("node is not a factory SourceFile"))
    })
}

/// Go `file.Text()` of a factory SourceFile.
#[must_use]
pub fn synthetic_source_file_text(n: Node) -> &'static str {
    with_synthetic_source_file(n, |d| d.text)
}

/// Go `file.FileName()` of a factory SourceFile.
#[must_use]
pub fn synthetic_source_file_file_name(n: Node) -> &'static str {
    with_synthetic_source_file(n, |d| d.file_name)
}

/// Go `file.AsSourceFile().ReferencedFiles`, `TypeReferenceDirectives` and
/// `LibReferenceDirectives`, `IsDeclarationFile` of any SourceFile, parsed
/// or factory-made.
// PORT: `SourceFileInfo` is `&'static` for parsed files only, so readers that
// must also see a factory SourceFile use this copy.
#[must_use]
pub fn source_file_parser_fields(file: Node) -> SyntheticSourceFileData {
    if is_synthetic_node(file) {
        return with_synthetic_source_file(file, Clone::clone);
    }
    let info = source_file_info(file);
    SyntheticSourceFileData {
        file_name: source_file_file_name(file),
        path: info.path.clone(),
        text: source_file_text(file),
        language_variant: info.language_variant,
        script_kind: info.script_kind,
        is_declaration_file: info.is_declaration_file,
        uses_uri_style_node_core_modules: info.uses_uri_style_node_core_modules,
        imports: info.imports.clone(),
        module_augmentations: info.module_augmentations.clone(),
        ambient_module_names: info.ambient_module_names.clone(),
        comment_directives: info.comment_directives.clone(),
        pragmas: info.pragmas.clone(),
        referenced_files: info.referenced_files.clone(),
        type_reference_directives: info.type_reference_directives.clone(),
        lib_reference_directives: info.lib_reference_directives.clone(),
        common_js_module_indicator: info.common_js_module_indicator,
        external_module_indicator: info.external_module_indicator,
    }
}

// Go: ast/ast.go:2663 (node *SourceFile) copyFrom
/// Copies the parser fields of `other` (parsed or factory-made) to the
/// factory SourceFile `node`.
pub fn source_file_copy_from(node: Node, other: Node) {
    // Do not copy fields set by NewSourceFile (Text, FileName, Path, or Statements)
    let o = source_file_parser_fields(other);
    update_synthetic_source_file(node, |d| {
        d.language_variant = o.language_variant;
        d.script_kind = o.script_kind;
        d.is_declaration_file = o.is_declaration_file;
        d.uses_uri_style_node_core_modules = o.uses_uri_style_node_core_modules;
        d.imports = o.imports;
        d.module_augmentations = o.module_augmentations;
        d.ambient_module_names = o.ambient_module_names;
        d.comment_directives = o.comment_directives;
        d.pragmas = o.pragmas;
        d.referenced_files = o.referenced_files;
        d.type_reference_directives = o.type_reference_directives;
        d.lib_reference_directives = o.lib_reference_directives;
        d.common_js_module_indicator = o.common_js_module_indicator;
        d.external_module_indicator = o.external_module_indicator;
    });
    set_node_flags(node, node.flags() | other.flags());
}

/// The synthetic-space id that stands for `n` inside synthetic `NodeData`.
/// Nil maps to the nil slot. A parsed node gets (or reuses) an alias slot.
#[must_use]
pub fn synthetic_child_id(n: Node) -> ts_ast::NodeId {
    if n.is_nil() {
        return ts_ast::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return ts_ast::NodeId::new(slot_index(n) as u32);
    }
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(&index) = a.aliases.get(&n) {
            return ts_ast::NodeId::new(index);
        }
        let index = a.slots.len() as u32;
        a.slots.push(Slot::Alias(n));
        a.aliases.insert(n, index);
        ts_ast::NodeId::new(index)
    })
}

/// Like `synthetic_child_id`, for ts_ast fields that are `Option<NodeId>`.
#[must_use]
pub fn synthetic_opt_child_id(n: Node) -> Option<ts_ast::NodeId> {
    if n.is_nil() {
        None
    } else {
        Some(synthetic_child_id(n))
    }
}

/// Go `core.UndefinedTextRange()` in ts_ast form. `TextPos` is `u32`; the
/// `as i32` in `node.rs` `text_range_of` turns `u32::MAX` back into `-1`.
fn undefined_ts_range() -> ts_core::TextRange {
    ts_range(TextRange::undefined())
}

/// A Go `core.TextRange` in ts_ast form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> ts_core::TextRange {
    ts_core::TextRange {
        start: ts_core::TextPos::new(loc.pos() as u32),
        end: ts_core::TextPos::new(loc.end() as u32),
    }
}

/// The ts_ast list for a synthetic node's list field.
fn ts_list(nodes: &[Node], loc: TextRange, has_trailing_comma: bool) -> ts_ast::NodeList {
    ts_ast::NodeList {
        range: ts_range(loc),
        nodes: nodes.iter().map(|&n| synthetic_child_id(n)).collect(),
        has_trailing_comma,
    }
}

/// Go `f.NewNodeList(nodes)` with a given `Loc`.
// PORT: Go list `Loc` is mutable; here a synthetic list fixes its `Loc` at
// creation. Callers that set `list.Loc` later pass it here instead.
#[must_use]
pub fn new_synthetic_node_list(nodes: &[Node], loc: TextRange) -> NodeList {
    let list: &'static ts_ast::NodeList =
        crate::ast::store::leak_in_ast_arena(ts_list(nodes, loc, false));
    NodeList {
        file: SYNTHETIC_NODE_FILE as u32,
        list: Some(list),
    }
}

/// Go `f.NewModifierList(nodes)` with a given `Loc`. `modifier_flags()` in
/// node.rs recomputes `ModifiersToFlags(nodes)`, as the Go factory does.
#[must_use]
pub fn new_synthetic_modifier_list(nodes: &[Node], loc: TextRange) -> ModifierList {
    let list: &'static ts_ast::ModifierList =
        crate::ast::store::leak_in_ast_arena(ts_ast::ModifierList {
            list: ts_list(nodes, loc, false),
            flags: ts_ast::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
        });
    ModifierList {
        file: SYNTHETIC_NODE_FILE as u32,
        list: Some(list),
    }
}

/// A list value to store inside new synthetic `NodeData`. Go stores the
/// `*NodeList` pointer; a list that already is synthetic is copied as is, and
/// a parsed list is rebuilt over alias ids with its own `Loc`.
// PORT: ts_ast stores lists by value, so a synthetic node that takes a
// parsed (or another synthetic) list gets a copy. `NodeList` equality on the
// copy is false where Go compares equal pointers.
#[must_use]
pub fn synthetic_list_value(list: NodeList) -> Option<ts_ast::NodeList> {
    if list.is_nil() {
        return None;
    }
    let l = list.list?;
    if list.file as usize == SYNTHETIC_NODE_FILE {
        return Some(l.clone());
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(&nodes, list.loc(), l.has_trailing_comma))
}

/// Like `synthetic_list_value` for a list field that ts_ast requires. Go
/// `nil` becomes an empty list with an undefined `Loc`.
// PORT: Go keeps `nil`; `NodeList::is_nil` on that field is false here.
#[must_use]
pub fn synthetic_req_list_value(list: NodeList) -> ts_ast::NodeList {
    synthetic_list_value(list).unwrap_or_else(|| ts_list(&[], TextRange::undefined(), false))
}

/// A modifier list value to store inside new synthetic `NodeData`.
#[must_use]
pub fn synthetic_modifiers_value(modifiers: ModifierList) -> Option<ts_ast::ModifierList> {
    let m = modifiers.list?;
    if modifiers.file as usize == SYNTHETIC_NODE_FILE {
        return Some(m.clone());
    }
    let nodes = modifiers.nodes().to_vec();
    Some(ts_ast::ModifierList {
        list: ts_list(&nodes, modifiers.loc(), m.list.has_trailing_comma),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}
