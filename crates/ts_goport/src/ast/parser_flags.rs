//! Go parser node flags for a Rust-parsed source file.
//!
//! The Go parser ORs its context flags into every node when it finishes the
//! node (`finishNode`). The Rust parser does not track these contexts, so
//! this file replays them with one walk over the finished Rust tree. The
//! binder and checker read the result as `go_file.parser_flags[idx]`.
//!
//! Only legacy (ts_parser) arena nodes come here, so the `IdentifierData`
//! text reads below see the text. U1 (d) empties only the data text of node
//! store identifiers (`store::alloc_store_name_node`).

use crate::prelude::*;

use crate::flags::NodeFlags;
use ts_ast::{ModifierList, Node as AstNode, NodeArena, NodeData as D, NodeId as AstId, NodeList};

const Y: NodeFlags = NodeFlags::YIELD_CONTEXT;
const A: NodeFlags = NodeFlags::AWAIT_CONTEXT;
const DI: NodeFlags = NodeFlags::DISALLOW_IN_CONTEXT;
const DEC: NodeFlags = NodeFlags::DECORATOR_CONTEXT;
const DCT: NodeFlags = NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT;

/// How the parent reached a child. Type entries follow the Go type
/// precedence chain (parseType, parseUnionTypeOrHigher, and so on).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Entry {
    Normal,
    /// parseType
    Type,
    /// parseReturnType / parseTypeOrTypePredicate
    ReturnType,
    /// parseUnionTypeOrHigher
    Union,
    /// parseTypeOperatorOrHigher
    Operator,
    /// parsePostfixTypeOrHigher
    Postfix,
    /// parseParameterWorker. `outer_await` is the Await context of the
    /// enclosing signature, used for the parameter modifiers.
    Param {
        outer_await: bool,
    },
    /// The type parameter of an `infer T extends C` type.
    InferParam,
    /// A modifier of a `declare` declaration. Go ORs Ambient into the
    /// modifier node only, not into its children.
    AmbientModifier,
}

/// How a node hands context to its children, after the type chain is
/// resolved for that node.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Normal,
    FnType,
    CondType,
    Predicate,
    Union,
    Intersection,
    Operator,
    Infer,
    Postfix,
    InferParam,
    Param { outer_await: bool },
    AmbientModifier,
}

/// One pending node in the walk. `host` is the context of the nearest
/// ancestor that is not a JS reparse node.
#[derive(Clone, Copy)]
struct Item {
    id: AstId,
    ctx: NodeFlags,
    entry: Entry,
    host: NodeFlags,
}

// Go: parser/parser.go setContextFlags
fn set(f: NodeFlags, flag: NodeFlags, on: bool) -> NodeFlags {
    if on { f | flag } else { f.without(flag) }
}

// Go: none. Rust helper for child slot checks
fn in_list(list: &NodeList, id: AstId) -> bool {
    list.nodes.contains(&id)
}

// Go: none. Rust helper for child slot checks
fn in_opt_list(list: &Option<NodeList>, id: AstId) -> bool {
    list.as_ref().is_some_and(|l| in_list(l, id))
}

// Go: none. Rust helper for child slot checks
fn in_mods(mods: &Option<ModifierList>, id: AstId) -> bool {
    mods.as_ref().is_some_and(|m| in_list(&m.list, id))
}

// Go: none. Rust helper for child slot checks
fn is(slot: Option<AstId>, id: AstId) -> bool {
    slot == Some(id)
}

// Go: ast/utilities.go (ast.Node.Modifiers)
// PORT: a local accessor over the Rust NodeData variants that carry modifiers.
fn modifiers_of(data: &D) -> Option<&ModifierList> {
    let mods = match data {
        D::ArrowFunction(d) => &d.modifiers,
        D::ClassDeclaration(d) => &d.modifiers,
        D::ClassExpression(d) => &d.modifiers,
        D::ClassStaticBlockDeclaration(d) => &d.modifiers,
        D::ConstructorDeclaration(d) => &d.modifiers,
        D::ConstructorTypeNode(d) => &d.modifiers,
        D::EnumDeclaration(d) => &d.modifiers,
        D::EnumMember(d) => &d.modifiers,
        D::ExportAssignment(d) => &d.modifiers,
        D::ExportDeclaration(d) => &d.modifiers,
        D::FunctionDeclaration(d) => &d.modifiers,
        D::FunctionExpression(d) => &d.modifiers,
        D::FunctionTypeNode(d) => &d.modifiers,
        D::GetAccessorDeclaration(d) => &d.modifiers,
        D::ImportDeclaration(d) => &d.modifiers,
        D::ImportEqualsDeclaration(d) => &d.modifiers,
        D::IndexSignatureDeclaration(d) => &d.modifiers,
        D::InterfaceDeclaration(d) => &d.modifiers,
        D::MethodDeclaration(d) => &d.modifiers,
        D::MethodSignatureDeclaration(d) => &d.modifiers,
        D::MissingDeclaration(d) => &d.modifiers,
        D::ModuleDeclaration(d) => &d.modifiers,
        D::NamespaceExportDeclaration(d) => &d.modifiers,
        D::ParameterDeclaration(d) => &d.modifiers,
        D::PropertyAssignment(d) => &d.modifiers,
        D::PropertyDeclaration(d) => &d.modifiers,
        D::PropertySignatureDeclaration(d) => &d.modifiers,
        D::SetAccessorDeclaration(d) => &d.modifiers,
        D::ShorthandPropertyAssignment(d) => &d.modifiers,
        D::TypeAliasDeclaration(d) => &d.modifiers,
        D::TypeParameterDeclaration(d) => &d.modifiers,
        D::VariableStatement(d) => &d.modifiers,
        _ => return None,
    };
    mods.as_ref()
}

// Go: ast/utilities.go HasSyntacticModifier
// PORT: checks the modifier token kinds directly instead of ModifierFlags.
fn has_modifier(arena: &NodeArena, data: &D, kind: SyntaxKind) -> bool {
    modifiers_of(data).is_some_and(|m| {
        m.list
            .nodes
            .iter()
            .any(|&id| arena.get(id).is_some_and(|n| n.kind == kind))
    })
}

// Go: ast/utilities.go IsTypeNode
// PORT: keyed on the Rust NodeData variant. ExpressionWithTypeArguments
// counts as an expression here, because Go parses it as one.
fn is_type_data(data: &D) -> bool {
    matches!(
        data,
        D::ArrayTypeNode(_)
            | D::ConditionalTypeNode(_)
            | D::ConstructorTypeNode(_)
            | D::FunctionTypeNode(_)
            | D::ImportTypeNode(_)
            | D::IndexedAccessTypeNode(_)
            | D::InferTypeNode(_)
            | D::IntersectionTypeNode(_)
            | D::KeywordTypeNode(_)
            | D::LiteralTypeNode(_)
            | D::MappedTypeNode(_)
            | D::NamedTupleMember(_)
            | D::OptionalTypeNode(_)
            | D::ParenthesizedTypeNode(_)
            | D::RestTypeNode(_)
            | D::TemplateLiteralTypeNode(_)
            | D::ThisTypeNode(_)
            | D::TupleTypeNode(_)
            | D::TypeLiteralNode(_)
            | D::TypeOperatorNode(_)
            | D::TypePredicateNode(_)
            | D::TypeQueryNode(_)
            | D::TypeReferenceNode(_)
            | D::UnionTypeNode(_)
            | D::JsDocAllType(_)
            | D::JsDocNonNullableType(_)
            | D::JsDocNullableType(_)
            | D::JsDocOptionalType(_)
            | D::JsDocVariadicType(_)
    )
}

// Go: ast/utilities.go:755 IsJSDocKind
fn is_jsdoc_kind(kind: SyntaxKind) -> bool {
    let k = kind as u16;
    SyntaxKind::FIRST_JS_DOC_NODE as u16 <= k && k <= SyntaxKind::LAST_JS_DOC_NODE as u16
}

// Go: tspath/extension.go IsDeclarationFileName
// PORT: local copy. It takes the base name and checks the declaration
// extensions, then the `.d.<ext>.ts` form used for arbitrary extensions.
fn is_declaration_file_name(file_name: &str) -> bool {
    let base = file_name.rsplit(['/', '\\']).next().unwrap_or(file_name);
    let lower = base.to_ascii_lowercase();
    if lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts") {
        return true;
    }
    lower.ends_with(".ts") && lower.contains(".d.")
}

/// Skips whitespace and comments from `pos`, like the Go scanner's
/// SkipTrivia. Returns the start of the next token.
// Go: scanner/scanner.go SkipTrivia
fn skip_trivia(text: &[u8], mut pos: usize) -> usize {
    while pos < text.len() {
        let c = text[pos];
        if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' || c == 0x0b || c == 0x0c {
            pos += 1;
        } else if c == b'/' && text.get(pos + 1) == Some(&b'/') {
            while pos < text.len() && text[pos] != b'\n' && text[pos] != b'\r' {
                pos += 1;
            }
        } else if c == b'/' && text.get(pos + 1) == Some(&b'*') {
            pos = comment_end(text, pos);
        } else if c >= 0x80 && is_unicode_space(text, pos) {
            pos += utf8_len(c);
        } else {
            break;
        }
    }
    pos
}

/// End of the `/* ... */` comment that starts at `pos` (or the text end).
// Go: scanner/scanner.go Scan (MultiLineCommentTrivia case)
fn comment_end(text: &[u8], pos: usize) -> usize {
    let mut i = pos + 2;
    while i + 1 < text.len() {
        if text[i] == b'*' && text[i + 1] == b'/' {
            return i + 2;
        }
        i += 1;
    }
    text.len()
}

// Go: none. UTF-8 width for the byte scanner
fn utf8_len(first: u8) -> usize {
    match first {
        0xf0..=0xff => 4,
        0xe0..=0xef => 3,
        0xc0..=0xdf => 2,
        _ => 1,
    }
}

// Go: stringutil IsWhiteSpaceLike / IsLineBreak (non-ASCII part)
fn is_unicode_space(text: &[u8], pos: usize) -> bool {
    let end = (pos + utf8_len(text[pos])).min(text.len());
    let Ok(s) = std::str::from_utf8(&text[pos..end]) else {
        return false;
    };
    s.chars().next().is_some_and(|c| {
        matches!(
            c,
            '\u{00a0}' | '\u{1680}' | '\u{2000}'
                ..='\u{200b}'
                    | '\u{2028}'
                    | '\u{2029}'
                    | '\u{202f}'
                    | '\u{205f}'
                    | '\u{3000}'
                    | '\u{feff}'
                    | '\u{0085}'
        )
    })
}

/// Returns the Go `node.Flags` value for every node of `source`, indexed by
/// `NodeId::index()`. It keeps the flags the Rust parser already set (Let,
/// Const, Using, Reparsed, ThisNodeHasError) and adds the Go parser context
/// flags, OptionalChain, HasJSDoc, PossiblyContainsDeprecatedTag and the
/// SourceFile-only flags. The binder stores this as `GoFile::parser_flags`.
// Go: parser/parser.go:430 parseSourceFileWorker
pub fn compute_parser_flags(file_index: usize, source: &ts_compiler::SourceFile) -> Vec<NodeFlags> {
    // PORT: the Go parser does not need a program file index. The flags come
    // only from the tree, the text and the file name.
    let _ = file_index;
    let arena = &source.parse.arena;
    let root = source.parse.source_file;
    let script_kind = ts_path::script_kind_from_path(&source.file_name);
    let is_js = matches!(
        script_kind,
        ts_path::ScriptKind::Js | ts_path::ScriptKind::Jsx
    );
    let is_json = script_kind == ts_path::ScriptKind::Json;
    let is_declaration = is_declaration_file_name(&source.file_name);

    // Go: parser/parser.go:300 initializeState (contextFlags per script kind)
    let mut base = NodeFlags::NONE;
    if is_js {
        base |= NodeFlags::JAVA_SCRIPT_FILE;
    } else if is_json {
        base |= NodeFlags::JAVA_SCRIPT_FILE | NodeFlags::JSON_FILE;
    }
    if is_declaration {
        base |= NodeFlags::AMBIENT;
    }

    let mut w = Walker {
        arena,
        text: source.source_text.as_bytes(),
        js: is_js,
        out: arena.iter().map(|(_, n)| NodeFlags(n.flags.0)).collect(),
        seen: vec![false; arena.len()],
        await_statements: Vec::new(),
    };
    if !is_declaration && is_external_module(arena, root, &source.file_name, script_kind) {
        w.await_statements = w.top_level_await_statements(root);
    }
    w.walk(Item {
        id: root,
        ctx: base,
        entry: Entry::Normal,
        host: base,
    });
    w.walk_unreached(base);
    w.set_optional_chains();
    w.set_has_jsdoc();
    let source_flags = w.source_flags();
    if let Some(slot) = w.out.get_mut(root.index()) {
        *slot |= source_flags;
    }
    w.out
}

struct Walker<'a> {
    arena: &'a NodeArena,
    text: &'a [u8],
    js: bool,
    out: Vec<NodeFlags>,
    seen: Vec<bool>,
    /// Top-level statements that Go reparses in Await context.
    await_statements: Vec<AstId>,
}

impl Walker<'_> {
    // Go: none. Arena accessor
    fn node(&self, id: AstId) -> Option<&AstNode> {
        self.arena.get(id)
    }

    // Go: none. Arena accessor
    fn kind(&self, id: AstId) -> Option<SyntaxKind> {
        self.arena.get(id).map(|n| n.kind)
    }

    // Go: parser/parser.go finishNode (applies contextFlags to each node)
    fn walk(&mut self, start: Item) {
        let mut stack = vec![start];
        while let Some(item) = stack.pop() {
            self.visit(item, &mut stack);
        }
    }

    /// Nodes that the tree walk did not reach, for example JSDoc nodes that
    /// the Rust parser keeps outside the child lists. A JSDoc root takes the
    /// context of its host plus JSDoc, as in Go parseJSDocComment.
    // Go: parser/jsdoc.go:139 parseJSDocComment
    fn walk_unreached(&mut self, base: NodeFlags) {
        for index in 0..self.seen.len() {
            if self.seen[index] {
                continue;
            }
            let Ok(raw) = u32::try_from(index) else { break };
            // Climb to the highest ancestor that is not reached yet.
            let mut top = AstId::new(raw);
            while let Some(parent) = self.node(top).and_then(|n| n.parent) {
                if self.seen.get(parent.index()).copied().unwrap_or(true) {
                    break;
                }
                top = parent;
            }
            let parent_ctx = self
                .node(top)
                .and_then(|n| n.parent)
                .and_then(|p| self.out.get(p.index()).copied())
                .map_or(base, |f| f & NodeFlags::CONTEXT_FLAGS);
            let jsdoc = self.kind(top).is_some_and(is_jsdoc_kind);
            let ctx = if jsdoc {
                parent_ctx | NodeFlags::JS_DOC
            } else {
                parent_ctx
            };
            self.walk(Item {
                id: top,
                ctx,
                entry: Entry::Normal,
                host: ctx,
            });
            if !self.seen[index] {
                // A cycle or a bad parent link. Mark it so the loop ends.
                self.seen[index] = true;
            }
        }
    }

    // Go: parser/parser.go finishNode (Flags |= contextFlags)
    fn visit(&mut self, item: Item, stack: &mut Vec<Item>) {
        let index = item.id.index();
        let Some(node) = self.arena.get(item.id) else {
            return;
        };
        if self.seen.get(index).copied().unwrap_or(true) {
            return;
        }
        self.seen[index] = true;
        let rust = NodeFlags(node.flags.0);
        let reparsed = rust.intersects(NodeFlags::REPARSED);

        // Go: parser/parser.go:2220 parseModuleOrNamespaceDeclaration sets
        // `implicitExport.Flags = NodeFlagsReparsed` after finishNode.
        if reparsed
            && node.kind == SyntaxKind::ExportKeyword
            && self.is_nested_namespace_modifier(node)
        {
            self.out[index] = rust;
            return;
        }

        let mut ctx = item.ctx;
        let mut finish_reparsed = false;
        if reparsed && self.js {
            // Go: parser/reparser.go finishReparsedNode uses the host context.
            // PORT: the host is the nearest ancestor that is not a reparse
            // node. Other reparsed nodes are JSDoc clones (DeepCloneReparse).
            finish_reparsed = self.is_finish_reparsed_kind(node);
            ctx = item.host | NodeFlags::JS_DOC;
        }

        let ambient = item.entry == Entry::Normal && self.is_ambient_declaration(node);
        if ambient {
            ctx |= NodeFlags::AMBIENT;
        }

        let (child_base, mode) = resolve(node, ctx, item.entry);
        let node_ctx = if finish_reparsed {
            item.host
        } else if mode == Mode::AmbientModifier {
            child_base | NodeFlags::AMBIENT
        } else {
            child_base
        };
        let mut flags = rust | node_ctx;
        if self.js && node.kind == SyntaxKind::JsTypeAliasDeclaration {
            // Go: parser/reparser.go reparseJSDocTypedef calls withJSDoc on the alias.
            flags |= NodeFlags::HAS_JS_DOC;
        }
        self.out[index] = flags;

        let host = if reparsed { item.host } else { node_ctx };
        let ambient_outer = if ambient { Some(item.ctx) } else { None };
        node.for_each_child(|child| {
            let (ctx, entry) = self.child(node, item.id, mode, child_base, child, ambient_outer);
            stack.push(Item {
                id: child,
                ctx,
                entry,
                host,
            });
        });
    }

    /// The implicit `export` modifier on `B` in `namespace A.B {}`.
    // Go: parser/parser.go parseModuleOrNamespaceDeclaration (nested namespace export modifier)
    fn is_nested_namespace_modifier(&self, node: &AstNode) -> bool {
        let Some(module_id) = node.parent else {
            return false;
        };
        if self.kind(module_id) != Some(SyntaxKind::ModuleDeclaration) {
            return false;
        }
        let outer = self
            .node(module_id)
            .and_then(|m| m.parent)
            .and_then(|p| self.node(p));
        matches!(outer.map(|n| &n.data), Some(D::ModuleDeclaration(d)) if d.body == Some(module_id))
    }

    // Go: parser/reparser.go (the kinds created with finishReparsedNode)
    fn is_finish_reparsed_kind(&self, node: &AstNode) -> bool {
        use SyntaxKind as K;
        match node.kind {
            K::JsTypeAliasDeclaration
            | K::JsImportDeclaration
            | K::ModuleDeclaration
            | K::ModuleBlock
            | K::HeritageClause
            | K::Parameter
            | K::PropertySignature
            | K::TypeParameter
            | K::FunctionDeclaration
            | K::MethodDeclaration
            | K::Constructor
            | K::FunctionType
            | K::JsDoc
            | K::AbstractKeyword
            | K::AccessorKeyword
            | K::AsyncKeyword
            | K::ConstKeyword
            | K::DeclareKeyword
            | K::DefaultKeyword
            | K::ExportKeyword
            | K::InKeyword
            | K::OutKeyword
            | K::OverrideKeyword
            | K::PrivateKeyword
            | K::ProtectedKeyword
            | K::PublicKeyword
            | K::ReadonlyKeyword
            | K::StaticKeyword
            | K::QuestionToken
            | K::DotDotDotToken
            | K::AsExpression
            | K::SatisfiesExpression => true,
            K::Identifier => matches!(&node.data, D::Identifier(d) if d.text == "this"),
            _ => false,
        }
    }

    /// A declaration with a `declare` modifier. Go parses it inside
    /// Ambient context and ORs Ambient into each modifier.
    // Go: parser/parser.go parseDeclaration, parseClassElement (isAmbient)
    fn is_ambient_declaration(&self, node: &AstNode) -> bool {
        use SyntaxKind as K;
        let declaration = matches!(
            node.kind,
            K::VariableStatement
                | K::FunctionDeclaration
                | K::ClassDeclaration
                | K::InterfaceDeclaration
                | K::TypeAliasDeclaration
                | K::EnumDeclaration
                | K::ModuleDeclaration
                | K::ImportEqualsDeclaration
                | K::ImportDeclaration
                | K::ExportAssignment
                | K::ExportDeclaration
                | K::NamespaceExportDeclaration
                | K::MissingDeclaration
                | K::PropertyDeclaration
                | K::MethodDeclaration
        );
        declaration && has_modifier(self.arena, &node.data, SyntaxKind::DeclareKeyword)
    }
}

/// Follows the Go type precedence chain for one node. Returns the context
/// the node is finished with and the way it hands context to its children.
// Go: parser/parser.go parseType, parseUnionTypeOrHigher,
// parseTypeOperatorOrHigher, parsePostfixTypeOrHigher, parseTypeOrTypePredicate
fn resolve(node: &AstNode, ctx: NodeFlags, entry: Entry) -> (NodeFlags, Mode) {
    let data = &node.data;
    let mut f = ctx;
    let mut entry = entry;
    let type_entry = matches!(
        entry,
        Entry::Type | Entry::ReturnType | Entry::Union | Entry::Operator | Entry::Postfix
    );
    if type_entry && !is_type_data(data) {
        // PORT: a non-type node in a type slot (for example a JS clone of an
        // expression) keeps the slot context and the normal child rules.
        entry = Entry::Normal;
    }
    loop {
        match entry {
            Entry::Normal => {
                if is_type_data(data) {
                    entry = Entry::Type;
                } else {
                    return (f, Mode::Normal);
                }
            }
            Entry::Param { outer_await } => return (f, Mode::Param { outer_await }),
            Entry::InferParam => return (f, Mode::InferParam),
            Entry::AmbientModifier => return (f, Mode::AmbientModifier),
            Entry::ReturnType => {
                // Go: parseTypeOrTypePredicate. Only `x is T` skips parseType.
                if let D::TypePredicateNode(p) = data
                    && p.asserts_modifier.is_none()
                {
                    return (f, Mode::Predicate);
                }
                entry = Entry::Type;
            }
            Entry::Type => {
                // Go: parseType runs outside Yield and Await context.
                f = f.without(NodeFlags::TYPE_EXCLUDES_FLAGS);
                match data {
                    D::FunctionTypeNode(_) | D::ConstructorTypeNode(_) => return (f, Mode::FnType),
                    D::ConditionalTypeNode(_) => return (f, Mode::CondType),
                    _ => entry = Entry::Union,
                }
            }
            Entry::Union => match data {
                D::UnionTypeNode(_) => return (f, Mode::Union),
                D::IntersectionTypeNode(_) => return (f, Mode::Intersection),
                _ => entry = Entry::Operator,
            },
            Entry::Operator => match data {
                D::TypeOperatorNode(_) => return (f, Mode::Operator),
                D::InferTypeNode(_) => return (f, Mode::Infer),
                D::FunctionTypeNode(_) | D::ConstructorTypeNode(_) => return (f, Mode::FnType),
                _ => {
                    // Go: allowConditionalTypesAnd(parsePostfixTypeOrHigher)
                    f = f.without(DCT);
                    entry = Entry::Postfix;
                }
            },
            Entry::Postfix => return (f, Mode::Postfix),
        }
    }
}

/// Context for a parameter list: `parseParameters(flags)` sets Yield and
/// Await from the signature, and each parameter's modifiers use the outer
/// Await context.
// Go: parser/parser.go parseParametersWorker
fn params(outer: NodeFlags, yield_: bool, await_: bool) -> (NodeFlags, Entry) {
    (
        set(set(outer, Y, yield_), A, await_),
        Entry::Param {
            outer_await: outer.intersects(A),
        },
    )
}

/// Context for a function body block.
// Go: parser/parser.go:3500 parseFunctionBlock
fn body(outer: NodeFlags, yield_: bool, await_: bool) -> NodeFlags {
    set(set(outer, Y, yield_), A, await_).without(DEC)
}

impl Walker<'_> {
    fn default_child(&self, f: NodeFlags, c: AstId) -> (NodeFlags, Entry) {
        let is_type = self.node(c).is_some_and(|n| is_type_data(&n.data));
        (f, if is_type { Entry::Type } else { Entry::Normal })
    }

    /// The context and entry for child `c` of `node`, where `f` is the
    /// context the node hands down.
    // Go: parser/parser.go doInContext (context set for each child slot)
    fn child(
        &self,
        node: &AstNode,
        id: AstId,
        mode: Mode,
        f: NodeFlags,
        c: AstId,
        ambient_outer: Option<NodeFlags>,
    ) -> (NodeFlags, Entry) {
        if let Some(outer) = ambient_outer
            && modifiers_of(&node.data).is_some_and(|m| in_list(&m.list, c))
        {
            return (outer, Entry::AmbientModifier);
        }
        match (mode, &node.data) {
            (Mode::Union, _) => (f, Entry::Union),
            (Mode::Intersection | Mode::Operator, _) => (f, Entry::Operator),
            (Mode::Infer, _) => (f, Entry::InferParam),
            // Go: parseFunctionOrConstructorType
            (Mode::FnType, D::FunctionTypeNode(d)) => {
                self.fn_type_child(f, c, &d.parameters, d.type_)
            }
            (Mode::FnType, D::ConstructorTypeNode(d)) => {
                self.fn_type_child(f, c, &d.parameters, d.type_)
            }
            // Go: parseType (conditional type branch)
            (Mode::CondType, D::ConditionalTypeNode(d)) => {
                if c == d.check_type {
                    (f, Entry::Union)
                } else if c == d.extends_type {
                    (f | DCT, Entry::Type)
                } else {
                    (f.without(DCT), Entry::Type)
                }
            }
            (Mode::Predicate, D::TypePredicateNode(d)) => {
                if is(d.type_, c) {
                    (f, Entry::Type)
                } else {
                    (f, Entry::Normal)
                }
            }
            // Go: parseInferType / tryParseConstraintOfInferType
            (Mode::InferParam, D::TypeParameterDeclaration(d)) if is(d.constraint, c) => {
                (f | DCT, Entry::Type)
            }
            // Go: parsePostfixTypeOrHigher (element and object types)
            (Mode::Postfix, D::ArrayTypeNode(d)) if c == d.element_type => (f, Entry::Postfix),
            (Mode::Postfix, D::IndexedAccessTypeNode(d)) if c == d.object_type => {
                (f, Entry::Postfix)
            }
            (Mode::Postfix, _) => self.default_child(f, c),
            // Go: parseParameterWorker (modifiers in the outer Await context)
            (Mode::Param { outer_await }, D::ParameterDeclaration(d))
                if in_mods(&d.modifiers, c) =>
            {
                (set(f, A, outer_await), Entry::Normal)
            }
            _ => self.normal_child(node, id, f, c),
        }
    }

    fn fn_type_child(
        &self,
        f: NodeFlags,
        c: AstId,
        parameters: &NodeList,
        type_: Option<AstId>,
    ) -> (NodeFlags, Entry) {
        if in_list(parameters, c) {
            params(f, false, false)
        } else if is(type_, c) {
            (f.without(DCT), Entry::ReturnType)
        } else {
            self.default_child(f, c)
        }
    }

    /// A signature with plain parameters and a return type: accessors,
    /// constructors and type member signatures.
    // Go: parser/parser.go parseSignatureMember
    fn plain_signature_child(
        &self,
        f: NodeFlags,
        c: AstId,
        parameters: &NodeList,
        type_: Option<AstId>,
        body_: Option<AstId>,
    ) -> (NodeFlags, Entry) {
        if in_list(parameters, c) {
            params(f, false, false)
        } else if is(type_, c) {
            (f.without(DCT), Entry::ReturnType)
        } else if is(body_, c) {
            (body(f, false, false), Entry::Normal)
        } else {
            self.default_child(f, c)
        }
    }

    /// True when `list` is the initializer of a for, for-in or for-of
    /// statement.
    // Go: parser/parser.go parseForOrForInOrForOfStatement
    fn is_for_initializer(&self, list: AstId, parent: Option<AstId>) -> bool {
        match parent.and_then(|p| self.node(p)).map(|n| &n.data) {
            Some(D::ForStatement(d)) => d.initializer == Some(list),
            Some(D::ForInOrOfStatement(d)) => d.initializer == list,
            _ => false,
        }
    }

    /// `x => ...` without parentheses. Go finishes the parameter in the
    /// outer context (parseSimpleArrowFunctionExpression).
    // PORT: detected from the source text, since the Rust tree has no
    // parenthesis tokens.
    // Go: parser/parser.go parseSimpleArrowFunctionExpression
    fn is_simple_arrow(&self, node: &AstNode, d: &ts_ast::ArrowFunctionData) -> bool {
        if d.parameters.nodes.len() != 1 || d.type_parameters.is_some() || d.type_.is_some() {
            return false;
        }
        let Some(param) = self.node(d.parameters.nodes[0]) else {
            return false;
        };
        let mut from = node.range.start.get() as usize;
        if let Some(last) = d
            .modifiers
            .as_ref()
            .and_then(|m| m.list.nodes.last())
            .and_then(|&m| self.node(m))
        {
            from = from.max(last.range.end.get() as usize);
        }
        let to = param.range.start.get() as usize;
        let from = skip_trivia(self.text, from.min(self.text.len()));
        !(from < to && self.text.get(from) == Some(&b'('))
    }
}

impl Walker<'_> {
    /// Child context rules for ordinary (non-type-chain) nodes. Each arm
    /// names the Go parse function that changes the context for that slot.
    // Go: parser/parser.go doInContext call sites
    fn normal_child(
        &self,
        node: &AstNode,
        id: AstId,
        f: NodeFlags,
        c: AstId,
    ) -> (NodeFlags, Entry) {
        // Go: parseExpressionAllowIn clears DisallowIn; parseExpression
        // clears Decorator.
        let allow_in = (f.without(DI | DEC), Entry::Normal);
        let has = |kind| has_modifier(self.arena, &node.data, kind);
        match &node.data {
            // Go: parser/parser.go:500 parseToplevelStatement, :519 reparseTopLevelAwait
            D::SourceFile(d) if in_list(&d.statements, c) && self.await_statements.contains(&c) => {
                (f | A, Entry::Normal)
            }

            // Go: parseFunctionDeclaration
            D::FunctionDeclaration(d) => {
                let generator = d.asterisk_token.is_some();
                let async_ = has(SyntaxKind::AsyncKeyword);
                let g = if has(SyntaxKind::ExportKeyword) {
                    f | A
                } else {
                    f
                };
                if in_list(&d.parameters, c) {
                    params(g, generator, async_)
                } else if is(d.type_, c) {
                    (g.without(DCT), Entry::ReturnType)
                } else if is(d.body, c) {
                    (body(g, generator, async_), Entry::Normal)
                } else {
                    self.default_child(f, c)
                }
            }
            // Go: parseFunctionExpression
            D::FunctionExpression(d) => {
                let generator = d.asterisk_token.is_some();
                let async_ = has(SyntaxKind::AsyncKeyword);
                let g = f.without(DEC);
                if is(d.name, c) {
                    // Go: parseOptionalBindingIdentifier inside doInContext
                    // (Yield for generators, Await for async). It only adds.
                    let mut name = g;
                    if generator {
                        name |= Y;
                    }
                    if async_ {
                        name |= A;
                    }
                    (name, Entry::Normal)
                } else if in_list(&d.parameters, c) {
                    params(g, generator, async_)
                } else if is(d.type_, c) {
                    (g.without(DCT), Entry::ReturnType)
                } else if c == d.body {
                    (body(g, generator, async_), Entry::Normal)
                } else {
                    self.default_child(g, c)
                }
            }
            // Go: parseParenthesizedArrowFunctionExpression, parseSimpleArrowFunctionExpression,
            // parseArrowFunctionExpressionBody
            D::ArrowFunction(d) => {
                let async_ = has(SyntaxKind::AsyncKeyword);
                if in_list(&d.parameters, c) {
                    if self.is_simple_arrow(node, d) {
                        (f, Entry::Normal)
                    } else {
                        params(f, false, async_)
                    }
                } else if is(d.type_, c) {
                    (f.without(DCT), Entry::ReturnType)
                } else if c == d.body {
                    if self.kind(c) == Some(SyntaxKind::Block) {
                        (body(f, false, async_), Entry::Normal)
                    } else {
                        (set(set(f, A, async_), Y, false), Entry::Normal)
                    }
                } else {
                    self.default_child(f, c)
                }
            }
            // Go: parseMethodDeclaration
            D::MethodDeclaration(d) => {
                let generator = d.asterisk_token.is_some();
                let async_ = has(SyntaxKind::AsyncKeyword);
                if in_list(&d.parameters, c) {
                    params(f, generator, async_)
                } else if is(d.type_, c) {
                    (f.without(DCT), Entry::ReturnType)
                } else if is(d.body, c) {
                    (body(f, generator, async_), Entry::Normal)
                } else {
                    self.default_child(f, c)
                }
            }
            // Go: parseConstructorDeclaration, parseAccessorDeclaration
            D::ConstructorDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, d.body)
            }
            D::GetAccessorDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, d.body)
            }
            D::SetAccessorDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, d.body)
            }
            // Go: parseSignatureMember, parsePropertyOrMethodSignature
            D::MethodSignatureDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, None)
            }
            D::CallSignatureDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, None)
            }
            D::ConstructSignatureDeclaration(d) => {
                self.plain_signature_child(f, c, &d.parameters, d.type_, None)
            }
            // Go: parseIndexSignatureDeclaration (parseBracketedList of parseParameter)
            D::IndexSignatureDeclaration(d) if in_list(&d.parameters, c) => {
                (f, Entry::Param { outer_await: false })
            }

            // Go: parseClassDeclarationOrExpression (export sets Await for the heritage and members)
            D::ClassDeclaration(d) => {
                let g = if has(SyntaxKind::ExportKeyword) {
                    f | A
                } else {
                    f
                };
                if in_opt_list(&d.heritage_clauses, c) || in_list(&d.members, c) {
                    (g, Entry::Normal)
                } else {
                    self.default_child(f, c)
                }
            }
            D::ClassExpression(d) => {
                let g = if has(SyntaxKind::ExportKeyword) {
                    f | A
                } else {
                    f
                };
                if in_opt_list(&d.heritage_clauses, c) || in_list(&d.members, c) {
                    (g, Entry::Normal)
                } else {
                    self.default_child(f, c)
                }
            }
            // Go: parsePropertyDeclaration (initializer outside Yield, Await and DisallowIn)
            D::PropertyDeclaration(d) if is(d.initializer, c) => {
                (f.without(Y | A | DI), Entry::Normal)
            }
            // Go: parseClassStaticBlockBody
            D::ClassStaticBlockDeclaration(d) if c == d.body => {
                (set(set(f, Y, false), A, true), Entry::Normal)
            }

            // Go: parseVariableDeclarationList (DisallowIn = inForStatementInitializer)
            D::VariableDeclarationList(d) if in_list(&d.declarations, c) => {
                if self.is_for_initializer(id, node.parent) {
                    (f | DI, Entry::Normal)
                } else {
                    (f.without(DI), Entry::Normal)
                }
            }
            // Go: parseArrayBindingPattern, parseObjectBindingPattern (parseBindingElement allowIn)
            D::BindingPattern(d) if in_list(&d.elements, c) => (f.without(DI), Entry::Normal),

            // Go: parseForOrForInOrForOfStatement
            D::ForStatement(d) => {
                if is(d.initializer, c) {
                    if self.kind(c) == Some(SyntaxKind::VariableDeclarationList) {
                        (f, Entry::Normal)
                    } else {
                        ((f | DI).without(DEC), Entry::Normal)
                    }
                } else if is(d.condition, c) || is(d.incrementor, c) {
                    allow_in
                } else {
                    self.default_child(f, c)
                }
            }
            D::ForInOrOfStatement(d) => {
                if c == d.initializer {
                    if self.kind(c) == Some(SyntaxKind::VariableDeclarationList) {
                        (f, Entry::Normal)
                    } else {
                        ((f | DI).without(DEC), Entry::Normal)
                    }
                } else if c == d.expression {
                    if node.kind == SyntaxKind::ForOfStatement {
                        (f.without(DI), Entry::Normal)
                    } else {
                        allow_in
                    }
                } else {
                    self.default_child(f, c)
                }
            }

            // Go: statements that call parseExpressionAllowIn
            D::IfStatement(d) if c == d.expression => allow_in,
            D::DoStatement(d) if c == d.expression => allow_in,
            D::WhileStatement(d) if c == d.expression => allow_in,
            D::ReturnStatement(d) if is(d.expression, c) => allow_in,
            D::SwitchStatement(d) if c == d.expression => allow_in,
            D::ThrowStatement(d) if c == d.expression => allow_in,
            D::CaseOrDefaultClause(d) if c == d.expression => allow_in,
            // Go: parseWithStatement
            D::WithStatement(d) => {
                if c == d.expression {
                    allow_in
                } else if c == d.statement {
                    (f | NodeFlags::IN_WITH_STATEMENT, Entry::Normal)
                } else {
                    self.default_child(f, c)
                }
            }
            // Go: parseExpressionOrLabeledStatement (parseExpression)
            D::ExpressionStatement(d) if c == d.expression => (f.without(DEC), Entry::Normal),

            // Go: parseComputedPropertyName, parseParenthesizedExpression,
            // parseTemplateSpan, parseMemberExpressionRest (element access)
            D::ComputedPropertyName(d) if c == d.expression => allow_in,
            D::ParenthesizedExpression(d) if c == d.expression => allow_in,
            D::TemplateSpan(d) if c == d.expression => allow_in,
            D::ElementAccessExpression(d) if c == d.argument_expression => allow_in,
            // Go: parseArgumentExpression. parseArrayLiteralExpression keeps
            // the outer context for its elements.
            D::CallExpression(d) if in_list(&d.arguments, c) => allow_in,
            D::NewExpression(d) if in_opt_list(&d.arguments, c) => allow_in,
            // Go: parseConditionalExpressionRest
            D::ConditionalExpression(d) if c == d.when_true => (f.without(DI), Entry::Normal),

            // Go: parseEnumDeclaration, parseEnumMember
            D::EnumDeclaration(d) if in_list(&d.members, c) => (f.without(Y | A), Entry::Normal),
            D::EnumMember(d) if is(d.initializer, c) => (f.without(DI), Entry::Normal),
            // Go: parseObjectLiteralElement (allowInAnd for initializers)
            D::PropertyAssignment(d) if c == d.initializer => (f.without(DI), Entry::Normal),
            D::ShorthandPropertyAssignment(d) if is(d.object_assignment_initializer, c) => {
                (f.without(DI), Entry::Normal)
            }

            // Go: parseExportAssignment, parseExportDeclaration (Await context set after the modifiers)
            D::ExportAssignment(d) if !in_mods(&d.modifiers, c) => {
                let (_, entry) = self.default_child(f, c);
                (f | A, entry)
            }
            D::ExportDeclaration(d) if !in_mods(&d.modifiers, c) => (f | A, Entry::Normal),

            // Go: parseDecorator (doInContext(DecoratorContext, true))
            D::Decorator(d) if c == d.expression => (f | DEC, Entry::Normal),

            _ => self.default_child(f, c),
        }
    }
}

/// True when the file has an external module indicator.
// Go: ast/parseoptions.go:60 getExternalModuleIndicator
// PORT: compiler options are not available here. moduleDetection=force,
// the react-jsx tag rule and an ESM implied node format from package.json
// are not applied. The .mts/.cts/.mjs/.cjs rule of moduleDetection=auto is.
fn is_external_module(
    arena: &NodeArena,
    root: AstId,
    file_name: &str,
    script_kind: ts_path::ScriptKind,
) -> bool {
    if script_kind == ts_path::ScriptKind::Json {
        return false;
    }
    let Some(AstNode {
        data: D::SourceFile(sf),
        ..
    }) = arena.get(root)
    else {
        return false;
    };
    if sf
        .statements
        .nodes
        .iter()
        .any(|&s| is_an_external_module_indicator_node(arena, s))
    {
        return true;
    }
    if ts_ast::source_file_contains_import_meta(arena, root) {
        return true;
    }
    let lower = file_name.to_ascii_lowercase();
    [".mts", ".cts", ".mjs", ".cjs"]
        .iter()
        .any(|ext| lower.ends_with(ext))
}

// Go: ast/parseoptions.go:95 isAnExternalModuleIndicatorNode
fn is_an_external_module_indicator_node(arena: &NodeArena, id: AstId) -> bool {
    let Some(node) = arena.get(id) else {
        return false;
    };
    if has_modifier(arena, &node.data, SyntaxKind::ExportKeyword) {
        return true;
    }
    match &node.data {
        D::ImportEqualsDeclaration(d) => arena
            .get(d.module_reference)
            .is_some_and(|r| r.kind == SyntaxKind::ExternalModuleReference),
        _ => matches!(
            node.kind,
            SyntaxKind::ImportDeclaration
                | SyntaxKind::ExportAssignment
                | SyntaxKind::ExportDeclaration
        ),
    }
}

impl Walker<'_> {
    /// Top-level statements that Go reparses in Await context: the first
    /// pass (outside Await) created an `await` identifier in them.
    // Go: parser/parser.go:500 parseToplevelStatement
    fn top_level_await_statements(&self, root: AstId) -> Vec<AstId> {
        let Some(AstNode {
            data: D::SourceFile(sf),
            ..
        }) = self.node(root)
        else {
            return Vec::new();
        };
        sf.statements
            .nodes
            .iter()
            .copied()
            .filter(|&s| self.statement_has_await_identifier(s))
            .collect()
    }

    /// Replays `statementHasAwaitIdentifier` for one statement. Go sets it in
    /// newIdentifier for the text `await`, and restores it around binding
    /// names, property names, class names, function bodies, JSDoc and the
    /// module-level declarations that always parse in Await context.
    // Go: parser/parser.go:2970 newIdentifier
    // PORT: the Rust parser makes an AwaitExpression in some places where
    // the Go first pass makes an `await` identifier. Those are counted by
    // await_expression_was_identifier.
    fn statement_has_await_identifier(&self, statement: AstId) -> bool {
        let mut stack = vec![statement];
        while let Some(id) = stack.pop() {
            let Some(node) = self.node(id) else { continue };
            if node.flags.0 & NodeFlags::REPARSED.0 != 0 || is_jsdoc_kind(node.kind) {
                continue;
            }
            match &node.data {
                D::Identifier(d) if d.text == "await" => return true,
                D::AwaitExpression(d)
                    if self.await_expression_was_identifier(node, d.expression) =>
                {
                    return true;
                }
                D::EnumDeclaration(_)
                | D::ModuleDeclaration(_)
                | D::ImportDeclaration(_)
                | D::ImportEqualsDeclaration(_)
                | D::ExportDeclaration(_)
                | D::ExportAssignment(_)
                | D::NamespaceExportDeclaration(_)
                | D::ExternalModuleReference(_) => continue,
                // Go: parseClassDeclarationOrExpression restores the flag for ambient classes.
                D::ClassDeclaration(_) | D::ClassExpression(_)
                    if has_modifier(self.arena, &node.data, SyntaxKind::DeclareKeyword) =>
                {
                    continue;
                }
                _ => {}
            }
            node.for_each_child(|c| {
                if !self.await_restored_slot(node, c) {
                    stack.push(c);
                }
            });
        }
        false
    }

    /// Slots where Go saves and restores statementHasAwaitIdentifier.
    // Go: parser/parser.go parseBindingIdentifier, parsePropertyName, parseFunctionBlock
    fn await_restored_slot(&self, node: &AstNode, c: AstId) -> bool {
        let is_block = |id: AstId| self.kind(id) == Some(SyntaxKind::Block);
        match &node.data {
            // parseFunctionBlock, parseBindingIdentifier
            D::FunctionDeclaration(d) => is(d.body, c) || is(d.name, c),
            D::FunctionExpression(d) => d.body == c || is(d.name, c),
            D::ArrowFunction(d) => d.body == c && is_block(c),
            D::MethodDeclaration(d) => is(d.body, c) || d.name == c,
            D::ConstructorDeclaration(d) => is(d.body, c),
            D::GetAccessorDeclaration(d) => is(d.body, c) || d.name == c,
            D::SetAccessorDeclaration(d) => is(d.body, c) || d.name == c,
            // parseNameOfClassDeclarationOrExpression
            D::ClassDeclaration(d) => is(d.name, c),
            D::ClassExpression(d) => is(d.name, c),
            // parseBindingIdentifier
            D::VariableDeclaration(d) => d.name == c,
            D::ParameterDeclaration(d) => d.name == c,
            D::BindingElement(d) => is(d.name, c) || is(d.property_name, c),
            // parsePropertyName
            D::PropertyAssignment(d) => d.name == c,
            D::ShorthandPropertyAssignment(d) => d.name == c,
            D::PropertyDeclaration(d) => d.name == c,
            D::PropertySignatureDeclaration(d) => d.name == c,
            D::MethodSignatureDeclaration(d) => d.name == c,
            _ => false,
        }
    }

    /// True when Go's first pass (outside Await context) would parse this
    /// `await` as an identifier. Go only starts an AwaitExpression there
    /// when an identifier, keyword or literal follows on the same line.
    // Go: parser/parser.go isAwaitExpression, nextTokenIsIdentifierOrKeywordOrLiteralOnSameLine
    fn await_expression_was_identifier(&self, node: &AstNode, operand: AstId) -> bool {
        let text = self.text;
        let keyword_start = skip_trivia(text, (node.range.start.get() as usize).min(text.len()));
        let keyword_end = (keyword_start + "await".len()).min(text.len());
        let Some(op) = self.node(operand) else {
            return false;
        };
        let op_start = skip_trivia(
            text,
            (op.range.start.get() as usize)
                .min(text.len())
                .max(keyword_end),
        );
        if text[keyword_end..op_start]
            .iter()
            .any(|&b| b == b'\n' || b == b'\r')
        {
            return true;
        }
        let Some(&ch) = text.get(op_start) else {
            return true;
        };
        !(ch.is_ascii_alphanumeric()
            || matches!(ch, b'_' | b'$' | b'\\' | b'"' | b'\'')
            || ch >= 0x80)
    }

    /// Sets OptionalChain bottom-up along property access, element access,
    /// call and tagged template chains, including the non-null reparse.
    // Go: parser/parser.go:5399 parsePropertyAccessExpressionRest,
    // :5454 parseElementAccessExpressionRest, :5479 parseCallExpressionRest,
    // :5530 parseTaggedTemplateRest
    fn set_optional_chains(&mut self) {
        let count = self.arena.len();
        let mut state: Vec<Option<bool>> = vec![None; count];
        for start in 0..count {
            if state[start].is_some() {
                continue;
            }
            let Ok(raw) = u32::try_from(start) else { break };
            let mut spine = Vec::new();
            let mut cur = AstId::new(raw);
            while state[cur.index()].is_none() && spine.len() <= count {
                match self.chain_link(cur) {
                    Some((inner, _, _)) => {
                        spine.push(cur);
                        cur = inner;
                    }
                    None => {
                        state[cur.index()] = Some(self.has_rust_optional_chain(cur));
                        break;
                    }
                }
            }
            while let Some(id) = spine.pop() {
                let Some((inner, question_dot, reparse)) = self.chain_link(id) else {
                    continue;
                };
                if state[id.index()].is_some() {
                    continue;
                }
                let value = if self.kind(id) == Some(SyntaxKind::NonNullExpression) {
                    self.has_rust_optional_chain(id)
                } else {
                    question_dot
                        || self.has_rust_optional_chain(id)
                        || state[inner.index()] == Some(true)
                        || (reparse && self.reparse_optional_chain(inner, &mut state))
                };
                state[id.index()] = Some(value);
            }
        }
        for (index, value) in state.into_iter().enumerate() {
            if value == Some(true) {
                self.out[index] |= NodeFlags::OPTIONAL_CHAIN;
            }
        }
    }

    // Go: parser/parser.go parseCallExpressionRest
    fn has_rust_optional_chain(&self, id: AstId) -> bool {
        self.node(id)
            .is_some_and(|n| n.flags.0 & NodeFlags::OPTIONAL_CHAIN.0 != 0)
    }

    /// (inner expression, has `?.`, uses tryReparseOptionalChain)
    // Go: parser/parser.go parseMemberExpressionRest
    fn chain_link(&self, id: AstId) -> Option<(AstId, bool, bool)> {
        let node = self.node(id)?;
        match &node.data {
            D::PropertyAccessExpression(d) => {
                Some((d.expression, d.question_dot_token.is_some(), true))
            }
            D::ElementAccessExpression(d) => {
                Some((d.expression, d.question_dot_token.is_some(), true))
            }
            D::CallExpression(d) if node.kind == SyntaxKind::CallExpression => {
                Some((d.expression, d.question_dot_token.is_some(), true))
            }
            D::TaggedTemplateExpression(d) => Some((d.tag, d.question_dot_token.is_some(), false)),
            D::NonNullExpression(d) => Some((d.expression, false, false)),
            _ => None,
        }
    }

    // Go: parser/parser.go:5414 tryReparseOptionalChain
    fn reparse_optional_chain(&self, node: AstId, state: &mut [Option<bool>]) -> bool {
        if state[node.index()] == Some(true) {
            return true;
        }
        let is_non_null = |id: AstId| self.kind(id) == Some(SyntaxKind::NonNullExpression);
        if !is_non_null(node) {
            return false;
        }
        let inner = |id: AstId| self.chain_link(id).map(|(e, _, _)| e);
        let Some(mut expr) = inner(node) else {
            return false;
        };
        while is_non_null(expr) && state[expr.index()] != Some(true) {
            let Some(next) = inner(expr) else {
                return false;
            };
            expr = next;
        }
        if state[expr.index()] != Some(true) {
            return false;
        }
        let mut cur = node;
        while is_non_null(cur) {
            state[cur.index()] = Some(true);
            let Some(next) = inner(cur) else { break };
            cur = next;
        }
        true
    }
}

/// Node kinds that Go parses with `withJSDoc`, so they can get HasJSDoc.
// Go: parser/parser.go withJSDoc call sites
fn can_have_jsdoc(kind: SyntaxKind) -> bool {
    use SyntaxKind as K;
    matches!(
        kind,
        K::Block
            | K::BreakStatement
            | K::ContinueStatement
            | K::DebuggerStatement
            | K::DoStatement
            | K::EmptyStatement
            | K::ExpressionStatement
            | K::LabeledStatement
            | K::ForStatement
            | K::ForInStatement
            | K::ForOfStatement
            | K::IfStatement
            | K::ReturnStatement
            | K::SwitchStatement
            | K::ThrowStatement
            | K::TryStatement
            | K::WhileStatement
            | K::WithStatement
            | K::VariableStatement
            | K::CaseBlock
            | K::CaseClause
            | K::DefaultClause
            | K::ClassDeclaration
            | K::FunctionDeclaration
            | K::EnumDeclaration
            | K::InterfaceDeclaration
            | K::TypeAliasDeclaration
            | K::ModuleDeclaration
            | K::ImportDeclaration
            | K::ImportEqualsDeclaration
            | K::ExportDeclaration
            | K::ExportAssignment
            | K::NamespaceExportDeclaration
            | K::EnumMember
            | K::ExportSpecifier
            | K::FunctionExpression
            | K::ArrowFunction
            | K::FunctionType
            | K::ConstructorType
            | K::Parameter
            | K::ParenthesizedExpression
            | K::PropertyDeclaration
            | K::MethodDeclaration
            | K::Constructor
            | K::GetAccessor
            | K::SetAccessor
            | K::SemicolonClassElement
            | K::ClassStaticBlockDeclaration
            | K::IndexSignature
            | K::PropertySignature
            | K::MethodSignature
            | K::CallSignature
            | K::ConstructSignature
            | K::PropertyAssignment
            | K::ShorthandPropertyAssignment
            | K::SpreadAssignment
            | K::NamedTupleMember
            | K::VariableDeclaration
            | K::EndOfFile
    )
}

/// Result of scanning the trivia before one token.
#[derive(Default)]
struct LeadingJsDoc {
    has_jsdoc: bool,
    deprecated: bool,
}

/// Scans `text[lo..tok]` for JSDoc comments. A byte that is not trivia means
/// the range crosses a token, so the flags found before it are dropped.
// Go: scanner/scanner.go:620 Scan (PrecedingJSDocComment), parser/parser.go withJSDoc
fn scan_leading_jsdoc(text: &[u8], lo: usize, tok: usize) -> LeadingJsDoc {
    let mut found = LeadingJsDoc::default();
    let mut pos = lo;
    while pos < tok {
        let c = text[pos];
        if c.is_ascii_whitespace() || c == 0x0b {
            pos += 1;
        } else if c == b'/' && text.get(pos + 1) == Some(&b'/') {
            while pos < tok && text[pos] != b'\n' && text[pos] != b'\r' {
                pos += 1;
            }
        } else if c == b'/' && text.get(pos + 1) == Some(&b'*') {
            let end = comment_end(text, pos);
            // Go: isJSDocLikeText. `/**/` is not JSDoc.
            if text.get(pos + 2) == Some(&b'*') && text.get(pos + 3) != Some(&b'/') {
                found.has_jsdoc = true;
                found.deprecated |= has_deprecated_tag(&text[pos..end.min(text.len())]);
            }
            pos = end;
        } else if c >= 0x80 && is_unicode_space(text, pos) {
            pos += utf8_len(c);
        } else {
            found = LeadingJsDoc::default();
            pos += 1;
        }
    }
    found
}

/// True when a JSDoc comment has an `@deprecated` tag.
// Go: parser/jsdoc.go parseTag (case "deprecated": p.hasDeprecatedTag = true)
// PORT: this does not check that the tag starts a JSDoc line. It checks the
// tag name ends at whitespace, `}`, `*` or the text end.
fn has_deprecated_tag(comment: &[u8]) -> bool {
    const TAG: &[u8] = b"@deprecated";
    comment.windows(TAG.len()).enumerate().any(|(i, w)| {
        w == TAG
            && comment
                .get(i + TAG.len())
                .is_none_or(|&b| b.is_ascii_whitespace() || b == b'}' || b == b'*')
    })
}

impl Walker<'_> {
    /// Sets HasJSDoc and PossiblyContainsDeprecatedTag on nodes that have a
    /// JSDoc comment directly before their first token.
    // Go: parser/parser.go:4030 withJSDoc
    // PORT: the Rust tree does not keep the scanner's PrecedingJSDocComment
    // state, so this scans the text between the previous token boundary and
    // the node's first token.
    fn set_has_jsdoc(&mut self) {
        let text = self.text;
        let skip = NodeFlags::JS_DOC | NodeFlags::REPARSED;
        let token_start =
            |node: &AstNode| skip_trivia(text, (node.range.start.get() as usize).min(text.len()));
        let mut bounds: Vec<usize> = Vec::with_capacity(self.arena.len() * 2);
        for (id, node) in self.arena.iter() {
            // The zero-width EndOfFile token must not bound its own leading
            // trivia.
            if self.out[id.index()].intersects(skip)
                || node.kind == SyntaxKind::SourceFile
                || node.kind == SyntaxKind::EndOfFile
            {
                continue;
            }
            bounds.push((node.range.end.get() as usize).min(text.len()));
            bounds.push(token_start(node) + 1);
        }
        bounds.push(0);
        bounds.sort_unstable();
        bounds.dedup();
        let mut marks = Vec::new();
        for (id, node) in self.arena.iter() {
            if !can_have_jsdoc(node.kind) || self.out[id.index()].intersects(skip) {
                continue;
            }
            let tok = token_start(node);
            let lo = match bounds.partition_point(|&b| b <= tok) {
                0 => 0,
                n => bounds[n - 1],
            };
            let found = scan_leading_jsdoc(text, lo.min(tok), tok);
            if found.has_jsdoc {
                marks.push((id, found.deprecated));
            }
        }
        for (id, deprecated) in marks {
            let slot = &mut self.out[id.index()];
            *slot |= NodeFlags::HAS_JS_DOC;
            if deprecated {
                *slot |= NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
            }
        }
    }

    /// Flags Go puts on the SourceFile node from parser state:
    /// PossiblyContainsDynamicImport and PossiblyContainsImportMeta.
    // Go: parser/parser.go:430 parseSourceFileWorker (sourceFlags)
    // PORT: Go sets these while parsing. Here they come from the finished
    // tree. JSDoc nodes count only in JS files, where Go reparses them into
    // the tree.
    fn source_flags(&self) -> NodeFlags {
        let mut flags = NodeFlags(0);
        for (id, node) in self.arena.iter() {
            if !self.js && self.out[id.index()].intersects(NodeFlags::JS_DOC) {
                continue;
            }
            match &node.data {
                D::ImportTypeNode(_) => flags |= NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT,
                D::CallExpression(_) if ts_ast::is_import_call(self.arena, node) => {
                    flags |= NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT;
                }
                D::MetaProperty(d) if d.keyword_token == SyntaxKind::ImportKeyword => {
                    let is_defer = matches!(self.node(d.name), Some(AstNode { data: D::Identifier(n), .. }) if n.text == "defer");
                    if !is_defer {
                        flags |= NodeFlags::POSSIBLY_CONTAINS_IMPORT_META;
                    }
                }
                _ => {}
            }
        }
        flags
    }
}
