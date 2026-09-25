//! Port of `transformers/declarations/transform.go`.
//!
//! Ported so far: the transformer state, its constructor, `GetDiagnostics`,
//! the `@internal` checks, the root `visit` dispatch and the source file
//! setup. The statement and subtree transforms (`transformSourceFile`,
//! `visitDeclarationStatements`, `visitDeclarationSubtree` and the rest) are
//! not ported yet and reach `unported!`.

use super::diagnostics::{GetSymbolAccessibilityDiagnostic, SymbolAccessibilityDiagnostic};
use super::tracker::{new_symbol_tracker, SymbolTrackerImpl, SymbolTrackerSharedState};
use super::DeclarationEmitHost;
use crate::ast::visitor::{new_node_visitor, NodeVisitorHooks};
use crate::checker::nodebuilder_types::{InternalNodeBuilderFlags, NodeBuilderFlags};
use crate::prelude::*;
use crate::printer::{new_emit_context, CommentRange, EmitContext, EmitResolver, SymbolAccessibilityResult};

// Go: transformers/declarations/transform.go:23 ReferencedFilePair
#[derive(Clone)]
pub struct ReferencedFilePair {
    pub file: Node,
    pub r#ref: FileReference,
}

// Go: transformers/declarations/transform.go:46 thisPropertyAssignmentKey
#[derive(Clone, PartialEq, Eq, Hash)]
struct ThisPropertyAssignmentKey {
    name: String,
    node: Node,
    is_static: bool,
    is_private: bool,
}

// Go: transformers/declarations/transform.go:53 getThisPropertyAssignmentKey
#[allow(dead_code)] // Called by the transformer body, which is not ported yet.
fn get_this_property_assignment_key(name: Node, node: Node, is_static: bool) -> ThisPropertyAssignmentKey {
    let is_private = is_private_identifier(name);
    if name.is_some() && !is_dynamic_name(name) {
        let (name_text, ok) = try_get_text_of_property_name(name);
        if ok {
            return ThisPropertyAssignmentKey { name: name_text, node: Node::NIL, is_static, is_private };
        }
    }
    ThisPropertyAssignmentKey { name: String::new(), node, is_static, is_private }
}

// Go: transformers/declarations/transform.go:63 DeclarationTransformer
// PORT: Go embeds `transformers.Transformer` (emit context, factory and root
// visitor). The emit context is the `emit_context` field; the factory is
// `emit_context.factory`; the root visitor is built in
// `transform_source_file_root`. Go also builds six `*ast.NodeVisitor` fields in
// the constructor (bindingNameVisitor, expressionVisitor,
// cjsExportAssignmentVisitor, exportStrippingVisitor, thisPropertyVisitor,
// declareStrippingVisitor). Their callbacks are in the unported transformer
// body, so they are not fields yet. Go maps keyed by `ast.NodeId` are keyed by
// `Node`.
#[allow(dead_code)] // Most fields are read by the transformer body, which is not ported yet.
pub struct DeclarationTransformer {
    emit_context: Rc<EmitContext>,
    host: Rc<dyn DeclarationEmitHost>,
    compiler_options: &'static CompilerOptions,
    tracker: Rc<RefCell<SymbolTrackerImpl>>,
    state: Rc<RefCell<SymbolTrackerSharedState>>,
    resolver: Rc<dyn EmitResolver>,
    declaration_file_path: String,
    declaration_map_path: String,

    needs_declare: bool,
    needs_scope_fix_marker: bool,
    result_has_scope_marker: bool,
    enclosing_declaration: Node,
    result_has_external_module_indicator: bool,
    suppress_new_diagnostic_contexts: bool,
    witnessed_cjs_exports: FxHashSet<String>,
    late_statement_replacement_map: FxHashMap<Node, Node>,
    // store the result of transforming expando hosts so they can be inserted later if the host is actually referenced
    expando_hosts: FxHashMap<Node, Node>,
    // store any found expando _members_ after transforming them so *if* the host is referenced, they can be emitted alongside it
    expando_members: FxHashMap<Node, Vec<Node>>,
    seen_properties: FxHashSet<ThisPropertyAssignmentKey>,
    this_property_assignments_collected: Vec<Node>,
    raw_referenced_files: Vec<ReferencedFilePair>,
    raw_type_reference_directives: Vec<FileReference>,
    raw_lib_reference_directives: Vec<FileReference>,

    cjs_export_assignment: Node,
    cjs_export_members: Vec<Node>,
    // tracks the name node used for `export =` in CJS module.exports assignments
    cjs_export_assignment_name: Node,
    // true when serializing members of a class expression kept as a class declaration
    in_class_expression_declaration: bool,
}

// Go: transformers/declarations/transform.go:102 NewDeclarationTransformer
// TODO: Convert to transformers.TransformerFactory signature to allow more automatic composition with other transforms
// PORT: a nil Go `context` is `None` (Go `NewTransformer` then makes a new
// emit context). Go stores `reportExpandoFunctionErrors` as a closure on the
// state; it is `SymbolTrackerSharedState::report_expando_function_errors`.
pub fn new_declaration_transformer(
    host: Rc<dyn DeclarationEmitHost>,
    context: Option<Rc<EmitContext>>,
    compiler_options: &'static CompilerOptions,
    declaration_file_path: &str,
    declaration_map_path: &str,
) -> DeclarationTransformer {
    let resolver = host.get_emit_resolver();
    let state = Rc::new(RefCell::new(SymbolTrackerSharedState {
        late_marked_statements: Vec::new(),
        diagnostics: Vec::new(),
        get_symbol_accessibility_diagnostic: None,
        error_name_node: Node::NIL,
        isolated_declarations: compiler_options.isolated_declarations.is_true(),
        strip_internal: compiler_options.strip_internal.is_true(),
        current_source_file: Node::NIL,
        resolver: resolver.clone(),
    }));
    let tracker = Rc::new(RefCell::new(new_symbol_tracker(host.clone(), resolver.clone(), state.clone())));
    // TODO: Use new host GetOutputPathsFor method instead of passing in entrypoint paths (which will also better support bundled emit)
    // Go: transformers/transformer.go:14 Transformer.NewTransformer
    let emit_context = context.unwrap_or_else(new_emit_context);
    DeclarationTransformer {
        emit_context,
        host,
        compiler_options,
        tracker,
        state,
        resolver,
        declaration_file_path: declaration_file_path.to_string(),
        declaration_map_path: declaration_map_path.to_string(),
        needs_declare: false,
        needs_scope_fix_marker: false,
        result_has_scope_marker: false,
        enclosing_declaration: Node::NIL,
        result_has_external_module_indicator: false,
        suppress_new_diagnostic_contexts: false,
        witnessed_cjs_exports: FxHashSet::default(),
        late_statement_replacement_map: FxHashMap::default(),
        expando_hosts: FxHashMap::default(),
        expando_members: FxHashMap::default(),
        seen_properties: FxHashSet::default(),
        this_property_assignments_collected: Vec::new(),
        raw_referenced_files: Vec::new(),
        raw_type_reference_directives: Vec::new(),
        raw_lib_reference_directives: Vec::new(),
        cjs_export_assignment: Node::NIL,
        cjs_export_members: Vec::new(),
        cjs_export_assignment_name: Node::NIL,
        in_class_expression_declaration: false,
    }
}

/// Go `declarationEmitNodeBuilderFlags`.
// Go: transformers/declarations/transform.go:214 declarationEmitNodeBuilderFlags
#[allow(dead_code)]
pub(crate) const DECLARATION_EMIT_NODE_BUILDER_FLAGS: NodeBuilderFlags = NodeBuilderFlags::MULTILINE_OBJECT_LITERALS
    .union(NodeBuilderFlags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL)
    .union(NodeBuilderFlags::USE_TYPE_OF_FUNCTION)
    .union(NodeBuilderFlags::USE_STRUCTURAL_FALLBACK)
    .union(NodeBuilderFlags::ALLOW_EMPTY_TUPLE)
    .union(NodeBuilderFlags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
    .union(NodeBuilderFlags::NO_TRUNCATION);

/// Go `declarationEmitInternalNodeBuilderFlags`.
// Go: transformers/declarations/transform.go:222 declarationEmitInternalNodeBuilderFlags
#[allow(dead_code)]
pub(crate) const DECLARATION_EMIT_INTERNAL_NODE_BUILDER_FLAGS: InternalNodeBuilderFlags =
    InternalNodeBuilderFlags::ALLOW_UNRESOLVED_NAMES;

impl DeclarationTransformer {
    // Go: transformers/transformer.go:39 Transformer.TransformSourceFile
    // PORT: Go visits with the root visitor that `NewTransformer` made through
    // `EmitContext.NewNodeVisitor`. That is unported. The root visit only calls
    // `tx.visit` on the source file, so this uses a plain `ast` visitor with
    // the transformer as its context. The emit context hooks only change
    // `VisitEachChild`, which the root visit does not call.
    pub fn transform_source_file_root(&mut self, file: Node) -> Node {
        let mut visitor = new_node_visitor(
            |node, v: &mut crate::ast::visitor::NodeVisitor<'_, &mut DeclarationTransformer>| v.ctx.visit(node),
            None,
            NodeVisitorHooks::default(),
            self,
        );
        visitor.visit_source_file(file)
    }

    // Go: transformers/declarations/transform.go:141 DeclarationTransformer.GetDiagnostics
    pub fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.state.borrow().diagnostics.clone()
    }

    // Go: transformers/declarations/transform.go:145 DeclarationTransformer.shouldStripInternal
    #[allow(dead_code)] // Called by the transformer body, which is not ported yet.
    fn should_strip_internal(&self, node: Node) -> bool {
        let (strip_internal, current_source_file) = {
            let state = self.state.borrow();
            (state.strip_internal, state.current_source_file)
        };
        strip_internal && node.is_some() && self.is_internal_declaration(node, current_source_file)
    }

    // Go: transformers/declarations/transform.go:149 DeclarationTransformer.isInternalDeclaration
    fn is_internal_declaration(&self, node: Node, source_file: Node) -> bool {
        if node.is_nil() {
            return false;
        }
        let parse_tree_node = self.emit_context.most_original(node);
        if !is_parse_tree_node(parse_tree_node) {
            return false;
        }
        if parse_tree_node.kind() == SyntaxKind::Parameter {
            let params = parse_tree_node.parent().parameters();
            let param_idx = params.iter().position(|p| p == parse_tree_node);
            let mut previous_sibling = Node::NIL;
            if let Some(idx) = param_idx {
                if idx > 0 {
                    previous_sibling = params.get(idx - 1);
                }
            }

            let text = source_file_text(source_file);
            let mut comment_ranges: Vec<CommentRange> = Vec::new();

            if previous_sibling.is_some() {
                // to handle
                // ... parameters, /** @internal */
                // public param: string
                let trailing_pos = skip_trivia_ex(
                    text,
                    previous_sibling.end() + 1,
                    Some(&SkipTriviaOptions { stop_at_comments: true, ..Default::default() }),
                );
                comment_ranges.extend(get_trailing_comment_ranges(text, trailing_pos));
                comment_ranges.extend(get_leading_comment_ranges(text, node.pos()));
            } else {
                let trailing_pos =
                    skip_trivia_ex(text, node.pos(), Some(&SkipTriviaOptions { stop_at_comments: true, ..Default::default() }));
                comment_ranges.extend(get_trailing_comment_ranges(text, trailing_pos));
            }

            if let Some(last) = comment_ranges.last() {
                return has_internal_annotation(last, source_file);
            }
            return false;
        }

        for comment_range in self.get_leading_comment_ranges_of_node(parse_tree_node, source_file) {
            if has_internal_annotation(&comment_range, source_file) {
                return true;
            }
        }
        false
    }

    // Go: transformers/declarations/transform.go:202 DeclarationTransformer.getLeadingCommentRangesOfNode
    fn get_leading_comment_ranges_of_node(&self, node: Node, source_file: Node) -> Vec<CommentRange> {
        if node.is_nil() || node.kind() == SyntaxKind::JsxText {
            return Vec::new();
        }
        get_leading_comment_ranges(source_file_text(source_file), node.pos())
    }

    // Go: transformers/declarations/transform.go:225 DeclarationTransformer.visit
    // functions as both `visitDeclarationStatements` and `transformRoot`, utilitzing SyntaxList nodes
    pub fn visit(&mut self, node: Node) -> Node {
        if node.is_nil() {
            return Node::NIL;
        }
        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            // statements we keep but do something to
            SyntaxKind::FunctionDeclaration
            | SyntaxKind::ModuleDeclaration
            | SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::JsTypeAliasDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::VariableStatement
            | SyntaxKind::ImportDeclaration
            | SyntaxKind::JsImportDeclaration
            | SyntaxKind::ExportDeclaration
            | SyntaxKind::ExportAssignment => self.visit_declaration_statements(node),
            // statements we elide
            SyntaxKind::BreakStatement
            | SyntaxKind::ContinueStatement
            | SyntaxKind::DebuggerStatement
            | SyntaxKind::DoStatement
            | SyntaxKind::EmptyStatement
            | SyntaxKind::ForInStatement
            | SyntaxKind::ForOfStatement
            | SyntaxKind::ForStatement
            | SyntaxKind::IfStatement
            | SyntaxKind::LabeledStatement
            | SyntaxKind::ReturnStatement
            | SyntaxKind::SwitchStatement
            | SyntaxKind::ThrowStatement
            | SyntaxKind::TryStatement
            | SyntaxKind::WhileStatement
            | SyntaxKind::WithStatement
            | SyntaxKind::NotEmittedStatement
            | SyntaxKind::Block
            | SyntaxKind::MissingDeclaration
            | SyntaxKind::ExpressionStatement => Node::NIL,
            // parts of things, things we just visit children of
            _ => self.visit_declaration_subtree(node),
        }
    }

    // Go: transformers/declarations/transform.go:279 DeclarationTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        self.cjs_export_assignment_name = Node::NIL;
        if source_file_info(node).is_declaration_file {
            return node;
        }

        self.needs_declare = true;
        self.needs_scope_fix_marker = false;
        self.result_has_scope_marker = false;
        self.enclosing_declaration = node;
        self.state.borrow_mut().get_symbol_accessibility_diagnostic = Some(throw_diagnostic());
        self.result_has_external_module_indicator = false;
        self.suppress_new_diagnostic_contexts = false;
        self.state.borrow_mut().late_marked_statements = Vec::new();
        self.late_statement_replacement_map = FxHashMap::default();
        self.expando_hosts = FxHashMap::default();
        self.expando_members = FxHashMap::default();
        self.raw_referenced_files = Vec::new();
        self.raw_type_reference_directives = Vec::new();
        self.raw_lib_reference_directives = Vec::new();
        self.witnessed_cjs_exports.clear();
        self.state.borrow_mut().current_source_file = node;
        self.collect_file_references(node);
        self.resolver.precalculate_declaration_emit_visibility(node);
        let updated = self.transform_source_file(node);
        self.state.borrow_mut().current_source_file = Node::NIL;
        updated
    }

    // Go: transformers/declarations/transform.go:308 DeclarationTransformer.collectFileReferences
    fn collect_file_references(&mut self, source_file: Node) {
        let info = source_file_info(source_file);
        self.raw_referenced_files.extend(
            info.referenced_files.iter().map(|r| ReferencedFilePair { file: source_file, r#ref: r.clone() }),
        );
        self.raw_type_reference_directives.extend(info.type_reference_directives.iter().cloned());
        self.raw_lib_reference_directives.extend(info.lib_reference_directives.iter().cloned());
    }

    // Go: transformers/declarations/transform.go:339 DeclarationTransformer.transformSourceFile
    fn transform_source_file(&mut self, _node: Node) -> Node {
        unported!("DeclarationTransformer.transformSourceFile")
    }

    // Go: transformers/declarations/transform.go:1126 DeclarationTransformer.visitDeclarationStatements
    fn visit_declaration_statements(&mut self, _node: Node) -> Node {
        unported!("DeclarationTransformer.visitDeclarationStatements")
    }

    // Go: transformers/declarations/transform.go:571 DeclarationTransformer.visitDeclarationSubtree
    fn visit_declaration_subtree(&mut self, _node: Node) -> Node {
        unported!("DeclarationTransformer.visitDeclarationSubtree")
    }
}

// Go: transformers/declarations/transform.go:209 hasInternalAnnotation
fn has_internal_annotation(comment_range: &CommentRange, source_file: Node) -> bool {
    let comment = &source_file_text(source_file)[comment_range.pos() as usize..comment_range.end() as usize];
    comment.contains("@internal")
}

// Go: transformers/declarations/transform.go:275 throwDiagnostic
fn throw_diagnostic() -> GetSymbolAccessibilityDiagnostic {
    Rc::new(|_result: &SymbolAccessibilityResult| -> Option<SymbolAccessibilityDiagnostic> {
        panic!("Diagnostic emitted without context")
    })
}

// Go: scanner/scanner.go:2813 GetLeadingCommentRanges
// PORT: the scanner comment range iterators are private to the printer.
fn get_leading_comment_ranges(_text: &str, _pos: i32) -> Vec<CommentRange> {
    unported!("scanner.GetLeadingCommentRanges")
}

// Go: scanner/scanner.go:2817 GetTrailingCommentRanges
// PORT: the scanner comment range iterators are private to the printer.
fn get_trailing_comment_ranges(_text: &str, _pos: i32) -> Vec<CommentRange> {
    unported!("scanner.GetTrailingCommentRanges")
}
