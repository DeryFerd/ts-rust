//! Port of Go `transformers/moduletransforms/commonjsmodule.go` lines 1 to 1037:
//! `NewCommonJSModuleTransformer` through `visitTopLevelNestedBlock`. The
//! rest of the file is in `commonjs_module_p2.rs`.
//!
//! PORT: Go builds five visitors in `NewCommonJSModuleTransformer`
//! (`Visitor()`, `topLevelVisitor`, `topLevelNestedVisitor`,
//! `discardedValueVisitor`, `assignmentPatternVisitor`). Each is an
//! `EmitContext.NewNodeVisitor` over one visit method. Here `with_visitor`
//! builds the visitor named by `VisitorKind` on each use, with the
//! transformer as the visitor context, as the declaration transform does.

use super::external_module_info::{
    ExternalModuleInfo, collect_external_module_info,
    create_external_helpers_import_declaration_if_needed, get_export_needs_import_star_helper,
    get_import_needs_import_default_helper, get_import_needs_import_star_helper,
};
use super::utilities::{
    common_js_module_indicator_of, external_module_indicator_of, get_external_module_name_literal,
    is_declaration_file_of, is_effective_external_module_file, is_external_module_file,
    rewrite_module_specifier,
};
use crate::ast::visitor::NodeVisitor;
use crate::frontend::tspath;
use crate::prelude::*;
use crate::transformers::modifier_visitor::extract_modifiers;
use crate::transformers::transformer::{
    TransformOptions, TransformReferenceResolver, Transformer, TransformerBox,
};
use crate::transformers::utilities::{
    convert_variable_declaration_to_assignment_expression, is_generated_identifier, is_local_name,
    single_or_many,
};

/// Names the Go visitor fields of `CommonJSModuleTransformer`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum VisitorKind {
    /// Go `tx.Visitor()` (`tx.visit`).
    Root,
    /// Go `tx.topLevelVisitor` (`tx.visitTopLevel`): visits statements at top level of a module
    TopLevel,
    /// Go `tx.topLevelNestedVisitor` (`tx.visitTopLevelNested`): visits nested statements at top level of a module
    TopLevelNested,
    /// Go `tx.discardedValueVisitor` (`tx.visitDiscardedValue`): visits expressions whose values would be discarded at runtime
    DiscardedValue,
    /// Go `tx.assignmentPatternVisitor` (`tx.visitAssignmentPattern`): visits assignment patterns in a destructuring assignment
    AssignmentPattern,
}

// Go: transformers/moduletransforms/commonjsmodule.go:15 CommonJSModuleTransformer
pub struct CommonJSModuleTransformer {
    pub(super) emit_context: Rc<EmitContext>,
    pub(super) compiler_options: &'static CompilerOptions,
    pub(super) resolver: Rc<dyn TransformReferenceResolver>,
    pub(super) get_emit_module_format_of_file: Rc<dyn Fn(Node) -> ModuleKind>,
    pub(super) module_kind: ModuleKind,
    pub(super) language_version: ScriptTarget,
    pub(super) current_source_file: Node,
    pub(super) current_module_info: Option<Rc<ExternalModuleInfo>>,
    /// used for ancestor tracking via pushNode/popNode to detect expression identifiers
    pub(super) parent_node: Node,
    /// used for ancestor tracking via pushNode/popNode to detect expression identifiers
    pub(super) current_node: Node,
}

// Go: transformers/moduletransforms/commonjsmodule.go:32 NewCommonJSModuleTransformer
pub fn new_commonjs_module_transformer(opts: &TransformOptions) -> TransformerBox {
    let compiler_options = opts.compiler_options;
    let emit_context = opts.context.clone();
    Box::new(CommonJSModuleTransformer {
        emit_context,
        compiler_options,
        resolver: opts.resolver.clone(),
        get_emit_module_format_of_file: opts.get_emit_module_format_of_file.clone(),
        module_kind: compiler_options.get_emit_module_kind(),
        language_version: compiler_options.get_emit_script_target(),
        current_source_file: Node::NIL,
        current_module_info: None,
        parent_node: Node::NIL,
        current_node: Node::NIL,
    })
}

impl Transformer for CommonJSModuleTransformer {
    fn emit_context(&self) -> &Rc<EmitContext> {
        &self.emit_context
    }

    // Go: transformers/transformer.go:39 Transformer.TransformSourceFile
    fn transform_source_file(&mut self, file: Node) -> Node {
        self.with_visitor(VisitorKind::Root, |v| v.visit_source_file(file))
    }
}

impl CommonJSModuleTransformer {
    /// Runs `f` with the Go visitor named by `kind`.
    pub(super) fn with_visitor<R>(
        &mut self,
        kind: VisitorKind,
        f: impl FnOnce(&mut NodeVisitor<'_, &mut CommonJSModuleTransformer>) -> R,
    ) -> R {
        let emit_context = self.emit_context.clone();
        let mut visitor = emit_context.new_node_visitor(
            move |node, v: &mut NodeVisitor<'_, &mut CommonJSModuleTransformer>| {
                v.ctx.dispatch(kind, node)
            },
            self,
        );
        f(&mut visitor)
    }

    /// The Go visit callback of each visitor.
    fn dispatch(&mut self, kind: VisitorKind, node: Node) -> Node {
        match kind {
            VisitorKind::Root => self.visit(node),
            VisitorKind::TopLevel => self.visit_top_level(node),
            VisitorKind::TopLevelNested => self.visit_top_level_nested(node),
            VisitorKind::DiscardedValue => self.visit_discarded_value(node),
            VisitorKind::AssignmentPattern => self.visit_assignment_pattern(node),
        }
    }

    /// Go `<visitor>.VisitNode(node)`.
    pub(super) fn visit_node_with(&mut self, kind: VisitorKind, node: Node) -> Node {
        self.with_visitor(kind, |v| v.visit_node(node))
    }

    /// Go `<visitor>.VisitNodes(nodes)`.
    pub(super) fn visit_nodes_with(&mut self, kind: VisitorKind, nodes: NodeList) -> NodeList {
        self.with_visitor(kind, |v| v.visit_nodes(nodes))
    }

    /// Go `<visitor>.VisitSlice(nodes)`.
    pub(super) fn visit_slice_with(
        &mut self,
        kind: VisitorKind,
        nodes: &[Node],
    ) -> (Vec<Node>, bool) {
        self.with_visitor(kind, |v| v.visit_slice(nodes))
    }

    /// Go `<visitor>.VisitEachChild(node)`.
    pub(super) fn visit_each_child_with(&mut self, kind: VisitorKind, node: Node) -> Node {
        self.with_visitor(kind, |v| v.visit_each_child(node))
    }

    /// Go `<visitor>.VisitEmbeddedStatement(node)`.
    pub(super) fn visit_embedded_statement_with(&mut self, kind: VisitorKind, node: Node) -> Node {
        self.with_visitor(kind, |v| v.visit_embedded_statement(node))
    }

    /// Go `tx.EmitContext().VisitIterationBody(body, <visitor>)`.
    pub(super) fn visit_iteration_body_with(&mut self, kind: VisitorKind, body: Node) -> Node {
        let emit_context = self.emit_context.clone();
        self.with_visitor(kind, |v| emit_context.visit_iteration_body(body, v))
    }

    /// Go `tx.currentModuleInfo`.
    pub(super) fn module_info(&self) -> Rc<ExternalModuleInfo> {
        self.current_module_info
            .clone()
            .expect("currentModuleInfo is nil")
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:47 CommonJSModuleTransformer.pushNode
    /// Pushes a new child node onto the ancestor tracking stack, returning the grandparent node to be restored later via `popNode`.
    pub(super) fn push_node(&mut self, node: Node) -> Node {
        let grandparent_node = self.parent_node;
        self.parent_node = self.current_node;
        self.current_node = node;
        grandparent_node
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:55 CommonJSModuleTransformer.popNode
    /// Pops the last child node off the ancestor tracking stack, restoring the grandparent node.
    pub(super) fn pop_node(&mut self, grandparent_node: Node) {
        self.current_node = self.parent_node;
        self.parent_node = grandparent_node;
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:61 CommonJSModuleTransformer.visitTopLevel
    /// Visits a node at the top level of the source file.
    fn visit_top_level(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);

        let result = match node.kind() {
            SyntaxKind::ImportDeclaration => self.visit_top_level_import_declaration(node),
            SyntaxKind::ImportEqualsDeclaration => {
                self.visit_top_level_import_equals_declaration(node)
            }
            SyntaxKind::ExportDeclaration => self.visit_top_level_export_declaration(node),
            SyntaxKind::ExportAssignment => self.visit_top_level_export_assignment(node),
            SyntaxKind::FunctionDeclaration => self.visit_top_level_function_declaration(node),
            SyntaxKind::ClassDeclaration => self.visit_top_level_class_declaration(node),
            SyntaxKind::VariableStatement => self.visit_top_level_variable_statement(node),
            _ => self.visit_top_level_nested_no_stack(node),
        };
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:87 CommonJSModuleTransformer.visitTopLevelNested
    /// Visits nested elements at the top-level of a module.
    fn visit_top_level_nested(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);
        let result = self.visit_top_level_nested_no_stack(node);
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:95 CommonJSModuleTransformer.visitTopLevelNestedNoStack
    /// Visits nested elements at the top-level of a module without ancestor tracking.
    fn visit_top_level_nested_no_stack(&mut self, node: Node) -> Node {
        match node.kind() {
            SyntaxKind::VariableStatement => self.visit_top_level_variable_statement(node),
            SyntaxKind::ForStatement => self.visit_top_level_nested_for_statement(node),
            SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
                self.visit_top_level_nested_for_in_or_of_statement(node)
            }
            SyntaxKind::DoStatement => self.visit_top_level_nested_do_statement(node),
            SyntaxKind::WhileStatement => self.visit_top_level_nested_while_statement(node),
            SyntaxKind::LabeledStatement => self.visit_top_level_nested_labeled_statement(node),
            SyntaxKind::WithStatement => self.visit_top_level_nested_with_statement(node),
            SyntaxKind::IfStatement => self.visit_top_level_nested_if_statement(node),
            SyntaxKind::SwitchStatement => self.visit_top_level_nested_switch_statement(node),
            SyntaxKind::CaseBlock => self.visit_top_level_nested_case_block(node),
            SyntaxKind::CaseClause | SyntaxKind::DefaultClause => {
                self.visit_top_level_nested_case_or_default_clause(node)
            }
            SyntaxKind::TryStatement => self.visit_top_level_nested_try_statement(node),
            SyntaxKind::CatchClause => self.visit_top_level_nested_catch_clause(node),
            SyntaxKind::Block => self.visit_top_level_nested_block(node),
            _ => self.visit_no_stack(node, false /*resultIsDiscarded*/),
        }
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:133 CommonJSModuleTransformer.visit
    /// Visits source elements that are not top-level or top-level nested statements.
    fn visit(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);
        let result = self.visit_no_stack(node, false /*resultIsDiscarded*/);
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:141 CommonJSModuleTransformer.visitNoStack
    /// Visits source elements that are not top-level or top-level nested statements without ancestor tracking.
    pub(super) fn visit_no_stack(&mut self, node: Node, result_is_discarded: bool) -> Node {
        // This visitor does not need to descend into the tree if there are no dynamic imports or identifiers in the subtree
        if !is_source_file(node)
            && !node.subtree_facts().intersects(
                SubtreeFacts::SUBTREE_CONTAINS_DYNAMIC_IMPORT
                    | SubtreeFacts::SUBTREE_CONTAINS_IDENTIFIER,
            )
        {
            return node;
        }

        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::ForStatement => self.visit_for_statement(node),
            SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
                self.visit_for_in_or_of_statement(node)
            }
            SyntaxKind::ExpressionStatement => self.visit_expression_statement(node),
            SyntaxKind::VoidExpression => self.visit_void_expression(node),
            SyntaxKind::ParenthesizedExpression => {
                self.visit_parenthesized_expression(node, result_is_discarded)
            }
            SyntaxKind::PartiallyEmittedExpression => {
                self.visit_partially_emitted_expression(node, result_is_discarded)
            }
            SyntaxKind::CallExpression => self.visit_call_expression(node),
            SyntaxKind::TaggedTemplateExpression => self.visit_tagged_template_expression(node),
            SyntaxKind::BinaryExpression => self.visit_binary_expression(node, result_is_discarded),
            SyntaxKind::PrefixUnaryExpression => {
                self.visit_prefix_unary_expression(node, result_is_discarded)
            }
            SyntaxKind::PostfixUnaryExpression => {
                self.visit_postfix_unary_expression(node, result_is_discarded)
            }
            SyntaxKind::ShorthandPropertyAssignment => {
                self.visit_shorthand_property_assignment(node)
            }
            SyntaxKind::Identifier => self.visit_identifier(node),
            _ => self.visit_each_child_with(VisitorKind::Root, node),
        }
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:183 CommonJSModuleTransformer.visitDiscardedValue
    /// Visits source elements whose value is discarded if they are expressions.
    fn visit_discarded_value(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);
        let result = self.visit_no_stack(node, true /*resultIsDiscarded*/);
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:190 CommonJSModuleTransformer.visitAssignmentPattern
    fn visit_assignment_pattern(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);
        let result = self.visit_assignment_pattern_no_stack(node);
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:197 CommonJSModuleTransformer.visitAssignmentPatternNoStack
    pub(super) fn visit_assignment_pattern_no_stack(&mut self, node: Node) -> Node {
        match node.kind() {
            // AssignmentPattern
            SyntaxKind::ObjectLiteralExpression | SyntaxKind::ArrayLiteralExpression => {
                self.visit_each_child_with(VisitorKind::AssignmentPattern, node)
            }

            // AssignmentProperty
            SyntaxKind::PropertyAssignment => self.visit_assignment_property(node),
            SyntaxKind::ShorthandPropertyAssignment => {
                self.visit_shorthand_assignment_property(node)
            }

            // AssignmentRestProperty
            SyntaxKind::SpreadAssignment => self.visit_assignment_rest_property(node),

            // AssignmentRestElement
            SyntaxKind::SpreadElement => self.visit_assignment_rest_element(node),

            // AssignmentElement
            _ => {
                if is_expression(node) {
                    return self.visit_assignment_element(node);
                }

                self.visit_no_stack(node, false /*resultIsDiscarded*/)
            }
        }
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:228 CommonJSModuleTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        if is_declaration_file_of(node)
            || !(is_effective_external_module_file(node, self.compiler_options)
                || node
                    .subtree_facts()
                    .intersects(SubtreeFacts::SUBTREE_CONTAINS_DYNAMIC_IMPORT))
        {
            return node;
        }

        self.current_source_file = node;
        self.current_module_info = Some(Rc::new(collect_external_module_info(
            node,
            self.compiler_options,
            &self.emit_context,
            &*self.resolver,
        )));
        let updated = self.transform_common_js_module(node);
        self.current_source_file = Node::NIL;
        self.current_module_info = None;
        updated
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:244 CommonJSModuleTransformer.shouldEmitUnderscoreUnderscoreESModule
    fn should_emit_underscore_underscore_es_module(&self) -> bool {
        let file = self.current_source_file;
        if tspath::file_extension_is_one_of(
            source_file_file_name(file),
            tspath::SUPPORTED_JS_EXTENSIONS_FLAT,
        ) && common_js_module_indicator_of(file).is_some()
        {
            let external_module_indicator = external_module_indicator_of(file);
            if external_module_indicator.is_nil()
                || external_module_indicator.kind() == SyntaxKind::SourceFile
            {
                return false;
            }
        }
        if self.module_info().export_equals.is_nil() && is_external_module_file(file) {
            return true;
        }
        false
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:256 CommonJSModuleTransformer.createUnderscoreUnderscoreESModule
    fn create_underscore_underscore_es_module(&self) -> Node {
        let ec = &self.emit_context;
        let f = ec.factory();
        let statement = f.new_expression_statement(f.new_call_expression(
            f.new_property_access_expression(
                f.new_identifier("Object"),
                Node::NIL, /*questionDotToken*/
                f.new_identifier("defineProperty"),
                NodeFlags::NONE,
            ),
            Node::NIL,     /*questionDotToken*/
            NodeList::NIL, /*typeArguments*/
            f.new_node_list(&[
                f.new_identifier("exports"),
                f.new_string_literal("__esModule", TokenFlags::NONE),
                f.new_object_literal_expression(
                    f.new_node_list(&[f.new_property_assignment(
                        ModifierList::NIL, /*modifiers*/
                        f.new_identifier("value"),
                        Node::NIL, /*postfixToken*/
                        Node::NIL, /*typeNode*/
                        f.new_true_expression(),
                    )]),
                    false, /*multiLine*/
                ),
            ]),
            NodeFlags::NONE,
        ));
        ec.set_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
        statement
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:290 CommonJSModuleTransformer.transformCommonJSModule
    fn transform_common_js_module(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        ec.start_variable_environment();

        // emit standard prologue directives (e.g. "use strict")
        let node_statements = node.statements().to_vec();
        let (prologue, rest) = f.split_standard_prologue(&node_statements);
        let mut statements: Vec<Node> = prologue.to_vec();

        // emit custom prologues from other transformations
        let (custom, rest) = f.split_custom_prologue(rest);
        let (custom, _) = self.visit_slice_with(VisitorKind::TopLevel, custom);
        statements.extend(custom);

        // emits `Object.defineProperty(exports, "__esModule", { value: true });` at the top of the file
        if self.should_emit_underscore_underscore_es_module() {
            statements.push(self.create_underscore_underscore_es_module());
        }

        // initialize all exports to `undefined`, e.g.:
        //  exports.a = exports.b = void 0;
        let info = self.module_info();
        if !info.exported_names.is_empty() {
            const CHUNK_SIZE: usize = 50;
            let l = info.exported_names.len();
            let mut i = 0;
            while i < l {
                let mut right = f.new_void_zero_expression();
                for &next_id in &info.exported_names[i..(i + CHUNK_SIZE).min(l)] {
                    let left = if next_id.kind() == SyntaxKind::StringLiteral {
                        f.new_element_access_expression(
                            f.new_identifier("exports"),
                            Node::NIL, /*questionDotToken*/
                            f.new_string_literal_from_node(next_id),
                            NodeFlags::NONE,
                        )
                    } else {
                        let name = f.clone_node(next_id);
                        ec.set_emit_flags(name, EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS);
                        f.new_property_access_expression(
                            f.new_identifier("exports"),
                            Node::NIL, /*questionDotToken*/
                            name,
                            NodeFlags::NONE,
                        )
                    };
                    right = f.new_assignment_expression(left, right);
                }
                let statement = f.new_expression_statement(right);
                ec.add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
                statements.push(statement);
                i += CHUNK_SIZE;
            }
        }

        // initialize exports for function declarations, e.g.:
        //  exports.f = f;
        //  function f() {}
        // These are marked as custom prologue so they are ordered before the external helpers
        // import declaration (e.g., `const tslib_1 = require("tslib")`), matching TypeScript's emit order.
        let exported_functions_start = statements.len();
        for &func in &info.exported_functions {
            statements = self.append_exports_of_class_or_function_declaration(statements, func);
        }
        for &s in &statements[exported_functions_start..] {
            ec.add_emit_flags(s, EmitFlags::CUSTOM_PROLOGUE);
        }

        // visit the remaining statements in the source file
        let (rest, _) = self.visit_slice_with(VisitorKind::TopLevel, rest);
        statements.extend(rest);

        // emit `module.exports = ...` if needd
        statements = self.append_export_equals_if_needed(statements);

        // merge temp variables into the statement list
        statements = ec.end_and_merge_variable_environment(&statements);

        let statement_list = f.new_node_list_with_loc(&statements, node.statement_list().loc());
        let mut result = f.update_source_file(node, statement_list, node.end_of_file_token());
        ec.add_emit_helper(result, &ec.read_emit_helpers());

        let external_helpers_import_declaration =
            create_external_helpers_import_declaration_if_needed(
                &ec,
                result,
                self.compiler_options,
                (self.get_emit_module_format_of_file)(node),
                false, /*hasExportStarsToExportValues*/
                false, /*hasImportStar*/
                false, /*hasImportDefault*/
            );
        if external_helpers_import_declaration.is_some() {
            let result_statements = result.statements().to_vec();
            let (prologue, rest) = f.split_standard_prologue(&result_statements);
            let (custom, rest) = f.split_custom_prologue(rest);
            let mut statements: Vec<Node> = prologue.to_vec();
            statements.extend_from_slice(custom);
            let visited =
                self.visit_node_with(VisitorKind::TopLevel, external_helpers_import_declaration);
            statements.push(visited);
            statements.extend_from_slice(rest);
            let statement_list =
                f.new_node_list_with_loc(&statements, result.statement_list().loc());
            result = f.update_source_file(result, statement_list, node.end_of_file_token());
        }

        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:388 CommonJSModuleTransformer.appendExportEqualsIfNeeded
    /// Adds the down-level representation of `export=` to the statement list if one exists in the source file.
    ///
    /// - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    fn append_export_equals_if_needed(&mut self, mut statements: Vec<Node>) -> Vec<Node> {
        let export_equals = self.module_info().export_equals;
        if export_equals.is_some() {
            let expression_result = self.visit_export_equals(export_equals);
            if expression_result.is_some() {
                let ec = self.emit_context.clone();
                let f = ec.factory();
                let statement = f.new_expression_statement(f.new_assignment_expression(
                    f.new_property_access_expression(
                        f.new_identifier("module"),
                        Node::NIL, /*questionDotToken*/
                        f.new_identifier("exports"),
                        NodeFlags::NONE,
                    ),
                    expression_result,
                ));

                ec.assign_comment_and_source_map_ranges(statement, export_equals);
                ec.add_emit_flags(statement, EmitFlags::NO_COMMENTS);
                statements.push(statement);
            }
        }
        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:412 CommonJSModuleTransformer.visitExportEquals
    fn visit_export_equals(&mut self, node: Node) -> Node {
        let grandparent_node = self.push_node(node);
        let result = self.visit_node_with(VisitorKind::Root, node.expression());
        self.pop_node(grandparent_node);
        result
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:422 CommonJSModuleTransformer.appendExportsOfImportDeclaration
    /// Appends the exports of an ImportDeclaration to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `decl` parameter is the declaration whose exports are to be recorded.
    fn append_exports_of_import_declaration(
        &mut self,
        mut statements: Vec<Node>,
        decl: Node,
    ) -> Vec<Node> {
        if self.module_info().export_equals.is_some() {
            return statements;
        }

        let import_clause = decl.import_clause();
        if import_clause.is_nil() {
            return statements;
        }

        let mut seen = FxHashSet::default();
        if import_clause.name().is_some() {
            statements = self.append_exports_of_declaration(
                statements,
                import_clause,
                Some(&mut seen),
                false, /*liveBinding*/
            );
        }

        let named_bindings = import_clause.named_bindings();
        if named_bindings.is_some() {
            match named_bindings.kind() {
                SyntaxKind::NamespaceImport => {
                    statements = self.append_exports_of_declaration(
                        statements,
                        named_bindings,
                        Some(&mut seen),
                        false, /*liveBinding*/
                    );
                }

                SyntaxKind::NamedImports => {
                    for import_binding in named_bindings.elements().to_vec() {
                        statements = self.append_exports_of_declaration(
                            statements,
                            import_binding,
                            Some(&mut seen),
                            true, /*liveBinding*/
                        );
                    }
                }
                _ => {}
            }
        }

        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:458 CommonJSModuleTransformer.appendExportsOfVariableStatement
    /// Appends the exports of a VariableStatement to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `node` parameter is the VariableStatement whose exports are to be recorded.
    pub(super) fn append_exports_of_variable_statement(
        &mut self,
        statements: Vec<Node>,
        node: Node,
    ) -> Vec<Node> {
        self.append_exports_of_variable_declaration_list(
            statements,
            node.declaration_list(),
            false, /*isForInOrOfInitializer*/
        )
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:466 CommonJSModuleTransformer.appendExportsOfVariableDeclarationList
    /// Appends the exports of a VariableDeclarationList to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `node` parameter is the VariableDeclarationList whose exports are to be recorded.
    pub(super) fn append_exports_of_variable_declaration_list(
        &mut self,
        mut statements: Vec<Node>,
        node: Node,
        is_for_in_or_of_initializer: bool,
    ) -> Vec<Node> {
        if self.module_info().export_equals.is_some() {
            return statements;
        }

        for decl in node.declarations().nodes().to_vec() {
            statements = self.append_exports_of_binding_element(
                statements,
                decl,
                is_for_in_or_of_initializer,
            );
        }

        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:482 CommonJSModuleTransformer.appendExportsOfBindingElement
    /// Appends the exports of a VariableDeclaration or BindingElement to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `decl` parameter is the declaration whose exports are to be recorded.
    fn append_exports_of_binding_element(
        &mut self,
        mut statements: Vec<Node>,
        decl: Node, /*VariableDeclaration | BindingElement*/
        is_for_in_or_of_initializer: bool,
    ) -> Vec<Node> {
        if self.module_info().export_equals.is_some() || decl.name().is_nil() {
            return statements;
        }

        if is_binding_pattern(decl.name()) {
            for element in decl.name().elements().to_vec() {
                if !is_omitted_expression(element) {
                    statements = self.append_exports_of_binding_element(
                        statements,
                        element,
                        is_for_in_or_of_initializer,
                    );
                }
            }
        } else if !is_generated_identifier(&self.emit_context, decl.name())
            && (!is_variable_declaration(decl)
                || decl.initializer().is_some()
                || is_for_in_or_of_initializer)
        {
            statements = self.append_exports_of_declaration(
                statements, decl, None,  /*seen*/
                false, /*liveBinding*/
            );
        }

        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:505 CommonJSModuleTransformer.appendExportsOfClassOrFunctionDeclaration
    /// Appends the exports of a ClassDeclaration or FunctionDeclaration to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `decl` parameter is the declaration whose exports are to be recorded.
    pub(super) fn append_exports_of_class_or_function_declaration(
        &mut self,
        mut statements: Vec<Node>,
        decl: Node,
    ) -> Vec<Node> {
        if self.module_info().export_equals.is_some() {
            return statements;
        }

        let mut seen = FxHashSet::default();
        if has_syntactic_modifier(decl, ModifierFlags::EXPORT) {
            let ec = self.emit_context.clone();
            let f = ec.factory();
            let export_name = if has_syntactic_modifier(decl, ModifierFlags::DEFAULT) {
                f.new_identifier("default")
            } else {
                f.get_declaration_name(decl)
            };

            let export_value = f.get_local_name(decl);
            statements = self.append_export_statement(
                statements,
                &mut seen,
                export_name,
                export_value,
                Some(decl.loc()),
                false, /*allowComments*/
                false, /*liveBinding*/
            );
        }

        if decl.name().is_some() {
            return self.append_exports_of_declaration(
                statements,
                decl,
                Some(&mut seen),
                false, /*liveBinding*/
            );
        }

        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:535 CommonJSModuleTransformer.appendExportsOfDeclaration
    /// Appends the exports of a declaration to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `decl` parameter is the declaration to export.
    pub(super) fn append_exports_of_declaration(
        &mut self,
        mut statements: Vec<Node>,
        decl: Node,
        seen: Option<&mut FxHashSet<String>>,
        live_binding: bool,
    ) -> Vec<Node> {
        let info = self.module_info();
        if info.export_equals.is_some() {
            return statements;
        }

        let mut local_seen = FxHashSet::default();
        let seen = match seen {
            Some(seen) => seen,
            None => &mut local_seen,
        };

        let name = decl.name();
        if info.export_specifiers.len() > 0 && name.is_some() && is_identifier(name) {
            let name = self.emit_context.factory().get_declaration_name(decl);
            let export_specifiers = info.export_specifiers.get(name.text());
            if !export_specifiers.is_empty() {
                let export_value = self.visit_expression_identifier(name);
                for export_specifier in export_specifiers {
                    statements = self.append_export_statement(
                        statements,
                        seen,
                        export_specifier.name(),
                        export_value,
                        Some(export_specifier.name().loc()), /*location*/
                        false,                               /*allowComments*/
                        live_binding,
                    );
                }
            }
        }

        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:567 CommonJSModuleTransformer.appendExportStatement
    /// Appends the down-level representation of an export to a statement list, returning the statement list.
    ///
    ///   - The `statements` parameter is a statement list to which the down-level export statements are to be appended.
    ///   - The `exportName` parameter is the name of the export.
    ///   - The `expression` parameter is the expression to export.
    ///   - The `location` parameter is the location to use for source maps and comments for the export.
    ///   - The `allowComments` parameter indicates whether to allow comments on the export.
    #[allow(clippy::too_many_arguments)]
    fn append_export_statement(
        &mut self,
        mut statements: Vec<Node>,
        seen: &mut FxHashSet<String>,
        export_name: Node,
        expression: Node,
        location: Option<TextRange>,
        allow_comments: bool,
        live_binding: bool,
    ) -> Vec<Node> {
        if export_name.kind() != SyntaxKind::StringLiteral {
            if seen.contains(export_name.text()) {
                return statements;
            }
            seen.insert(export_name.text().to_string());
        }
        statements.push(self.create_export_statement(
            export_name,
            expression,
            location,
            allow_comments,
            live_binding,
        ));
        statements
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:584 CommonJSModuleTransformer.createExportStatement
    /// Creates a call to the current file's export function to export a value.
    ///
    ///   - The `name` parameter is the bound name of the export.
    ///   - The `value` parameter is the exported value.
    ///   - The `location` parameter is the location to use for source maps and comments for the export.
    ///   - The `allowComments` parameter indicates whether to emit comments for the statement.
    pub(super) fn create_export_statement(
        &mut self,
        name: Node,
        value: Node,
        location: Option<TextRange>,
        allow_comments: bool,
        live_binding: bool,
    ) -> Node {
        let ec = self.emit_context.clone();
        let statement = ec
            .factory()
            .new_expression_statement(self.create_export_expression(
                name,
                value,
                None, /*location*/
                live_binding,
            ));
        if let Some(location) = location {
            ec.set_comment_range(statement, location);
        }
        ec.add_emit_flags(statement, EmitFlags::START_ON_NEW_LINE);
        if !allow_comments {
            ec.add_emit_flags(statement, EmitFlags::NO_COMMENTS);
        }
        statement
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:601 CommonJSModuleTransformer.createExportExpression
    /// Creates a call to the current file's export function to export a value.
    ///
    ///   - The `name` parameter is the bound name of the export.
    ///   - The `value` parameter is the exported value.
    ///   - The `location` parameter is the location to use for source maps and comments for the export.
    pub(super) fn create_export_expression(
        &self,
        name: Node,
        value: Node,
        location: Option<TextRange>,
        live_binding: bool,
    ) -> Node {
        let ec = &self.emit_context;
        let f = ec.factory();
        let expression = if live_binding {
            // For a live binding we emit a getter on `exports` that returns the value:
            //  Object.defineProperty(exports, "<name>", { enumerable: true, get: function () { return <value>; } });
            f.new_call_expression(
                f.new_property_access_expression(
                    f.new_identifier("Object"),
                    Node::NIL, /*questionDotToken*/
                    f.new_identifier("defineProperty"),
                    NodeFlags::NONE,
                ),
                Node::NIL,     /*questionDotToken*/
                NodeList::NIL, /*typeArguments*/
                f.new_node_list(&[
                    f.new_identifier("exports"),
                    f.new_string_literal_from_node(name),
                    f.new_object_literal_expression(
                        f.new_node_list(&[
                            f.new_property_assignment(
                                ModifierList::NIL, /*modifiers*/
                                f.new_identifier("enumerable"),
                                Node::NIL, /*postfixToken*/
                                Node::NIL, /*typeNode*/
                                f.new_true_expression(),
                            ),
                            f.new_property_assignment(
                                ModifierList::NIL, /*modifiers*/
                                f.new_identifier("get"),
                                Node::NIL, /*postfixToken*/
                                Node::NIL, /*typeNode*/
                                f.new_function_expression(
                                    ModifierList::NIL, /*modifiers*/
                                    Node::NIL,         /*asteriskToken*/
                                    Node::NIL,         /*name*/
                                    NodeList::NIL,     /*typeParameters*/
                                    f.new_node_list(&[]),
                                    Node::NIL, /*type*/
                                    Node::NIL, /*fullSignature*/
                                    f.new_block(
                                        f.new_node_list(&[f.new_return_statement(value)]),
                                        false, /*multiLine*/
                                    ),
                                ),
                            ),
                        ]),
                        false, /*multiLine*/
                    ),
                ]),
                NodeFlags::NONE,
            )
        } else {
            // Otherwise, we emit a simple property assignment.
            let left = if name.kind() == SyntaxKind::StringLiteral {
                // emits:
                //  exports["<name>"] = <value>;
                f.new_element_access_expression(
                    f.new_identifier("exports"),
                    Node::NIL, /*questionDotToken*/
                    f.new_string_literal_from_node(name),
                    NodeFlags::NONE,
                )
            } else {
                // emits:
                //  exports.<name> = <value>;
                f.new_property_access_expression(
                    f.new_identifier("exports"),
                    Node::NIL, /*questionDotToken*/
                    f.clone_node(name),
                    NodeFlags::NONE,
                )
            };
            f.new_assignment_expression(left, value)
        };
        if let Some(location) = location {
            ec.set_comment_range(expression, location);
        }
        expression
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:681 CommonJSModuleTransformer.createRequireCall
    /// Creates a `require()` call to import an external module.
    fn create_require_call(
        &self,
        node: Node, /*ImportDeclaration | ImportEqualsDeclaration | ExportDeclaration*/
    ) -> Node {
        let ec = &self.emit_context;
        let f = ec.factory();
        let mut args: Vec<Node> = Vec::new();
        let module_name = get_external_module_name_literal(
            f,
            node,
            self.current_source_file,
            None, /*resolver*/
            self.compiler_options,
        );
        if module_name.is_some() {
            args.push(rewrite_module_specifier(
                ec,
                module_name,
                self.compiler_options,
            ));
        }
        f.new_call_expression(
            f.new_identifier("require"),
            Node::NIL,     /*questionDotToken*/
            NodeList::NIL, /*typeArguments*/
            f.new_node_list(&args),
            NodeFlags::NONE,
        )
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:695 CommonJSModuleTransformer.getHelperExpressionForExport
    fn get_helper_expression_for_export(&mut self, node: Node, inner_expr: Node) -> Node {
        if get_export_needs_import_star_helper(node) {
            let helper = self
                .emit_context
                .factory()
                .new_import_star_helper(inner_expr);
            return self.visit_node_with(VisitorKind::Root, helper);
        }
        inner_expr
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:702 CommonJSModuleTransformer.getHelperExpressionForImport
    fn get_helper_expression_for_import(&mut self, node: Node, inner_expr: Node) -> Node {
        if get_import_needs_import_star_helper(node) {
            let helper = self
                .emit_context
                .factory()
                .new_import_star_helper(inner_expr);
            return self.visit_node_with(VisitorKind::Root, helper);
        }
        if get_import_needs_import_default_helper(node) {
            let helper = self
                .emit_context
                .factory()
                .new_import_default_helper(inner_expr);
            return self.visit_node_with(VisitorKind::Root, helper);
        }
        inner_expr
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:712 CommonJSModuleTransformer.visitTopLevelImportDeclaration
    fn visit_top_level_import_declaration(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        if node.import_clause().is_nil() {
            // import "mod";
            let statement = f.new_expression_statement(self.create_require_call(node));
            ec.set_original(statement, node);
            ec.assign_comment_and_source_map_ranges(statement, node);
            return statement;
        }

        let mut statements: Vec<Node> = Vec::new();
        let mut variables: Vec<Node> = Vec::new();
        let namespace_declaration = get_namespace_declaration_node(node);
        if namespace_declaration.is_some() && !is_default_import(node) {
            // import * as n from "mod";
            let name = f.clone_node(namespace_declaration.name());
            let require_call = self.create_require_call(node);
            let initializer = self.get_helper_expression_for_import(node, require_call);
            variables.push(f.new_variable_declaration(
                name,
                Node::NIL, /*exclamationToken*/
                Node::NIL, /*type*/
                initializer,
            ));
        } else {
            // import d from "mod";
            // import { x, y } from "mod";
            // import d, { x, y } from "mod";
            // import d, * as n from "mod";
            let name = f.new_generated_name_for_node(node);
            let require_call = self.create_require_call(node);
            let initializer = self.get_helper_expression_for_import(node, require_call);
            variables.push(f.new_variable_declaration(
                name,
                Node::NIL, /*exclamationToken*/
                Node::NIL, /*type*/
                initializer,
            ));

            if namespace_declaration.is_some() && is_default_import(node) {
                variables.push(f.new_variable_declaration(
                    f.clone_node(namespace_declaration.name()),
                    Node::NIL, /*exclamationToken*/
                    Node::NIL, /*type*/
                    f.new_generated_name_for_node(node),
                ));
            }
        }

        let var_statement = f.new_variable_statement(
            ModifierList::NIL, /*modifiers*/
            f.new_variable_declaration_list(f.new_node_list(&variables), NodeFlags::CONST),
        );

        ec.set_original(var_statement, node);
        ec.assign_comment_and_source_map_ranges(var_statement, node);
        statements.push(var_statement);
        statements = self.append_exports_of_import_declaration(statements, node);
        single_or_many(Some(&statements), f)
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:777 CommonJSModuleTransformer.visitTopLevelImportEqualsDeclaration
    fn visit_top_level_import_equals_declaration(&mut self, node: Node) -> Node {
        if !is_external_module_import_equals_declaration(node) {
            // import m = n;
            panic!(
                "import= for internal module references should be handled in an earlier transformer."
            );
        }

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut statements: Vec<Node> = Vec::new();
        if has_syntactic_modifier(node, ModifierFlags::EXPORT) {
            // export import m = require("mod");
            let statement = f.new_expression_statement(self.create_export_expression(
                node.name(),
                self.create_require_call(node),
                Some(node.loc()),
                false, /*liveBinding*/
            ));

            ec.set_original(statement, node);
            ec.assign_comment_and_source_map_ranges(statement, node);
            statements.push(statement);
        } else {
            // import m = require("mod");
            let statement = f.new_variable_statement(
                ModifierList::NIL, /*modifiers*/
                f.new_variable_declaration_list(
                    f.new_node_list(&[f.new_variable_declaration(
                        f.clone_node(node.name()),
                        Node::NIL, /*exclamationToken*/
                        Node::NIL, /*typeNode*/
                        self.create_require_call(node),
                    )]),
                    NodeFlags::CONST,
                ),
            );
            ec.set_original(statement, node);
            ec.assign_comment_and_source_map_ranges(statement, node);
            statements.push(statement);
        }

        statements = self.append_exports_of_declaration(
            statements, node, None,  /*seen*/
            false, /*liveBinding*/
        );
        single_or_many(Some(&statements), f)
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:825 CommonJSModuleTransformer.visitTopLevelExportDeclaration
    fn visit_top_level_export_declaration(&mut self, node: Node) -> Node {
        if node.module_specifier().is_nil() {
            // Elide export declarations with no module specifier as they are handled
            // elsewhere.
            return Node::NIL;
        }

        let ec = self.emit_context.clone();
        let f = ec.factory();
        let generated_name = f.new_generated_name_for_node(node);
        if node.export_clause().is_some() && is_named_exports(node.export_clause()) {
            // export { x, y } from "mod";
            let mut statements: Vec<Node> = Vec::new();
            let var_statement = f.new_variable_statement(
                ModifierList::NIL, /*modifiers*/
                f.new_variable_declaration_list(
                    f.new_node_list(&[f.new_variable_declaration(
                        generated_name,
                        Node::NIL, /*exclamationToken*/
                        Node::NIL, /*type*/
                        self.create_require_call(node),
                    )]),
                    NodeFlags::NONE,
                ),
            );
            ec.set_original(var_statement, node);
            ec.assign_comment_and_source_map_ranges(var_statement, node);
            statements.push(var_statement);

            for specifier in node.export_clause().elements().to_vec() {
                let specifier_name = specifier.property_name_or_name();
                let export_needs_import_default = module_export_name_is_default(specifier_name);

                let target = if export_needs_import_default {
                    f.new_import_default_helper(generated_name)
                } else {
                    generated_name
                };

                let export_name = if is_string_literal(specifier.name()) {
                    f.new_string_literal_from_node(specifier.name())
                } else {
                    f.get_export_name(specifier)
                };

                let exported_value = if is_string_literal(specifier_name) {
                    f.new_element_access_expression(
                        target,
                        Node::NIL, /*questionDotToken*/
                        specifier_name,
                        NodeFlags::NONE,
                    )
                } else {
                    f.new_property_access_expression(
                        target,
                        Node::NIL, /*questionDotToken*/
                        specifier_name,
                        NodeFlags::NONE,
                    )
                };
                let statement = f.new_expression_statement(self.create_export_expression(
                    export_name,
                    exported_value,
                    None, /*location*/
                    true, /*liveBinding*/
                ));
                ec.set_original(statement, specifier);
                ec.assign_comment_and_source_map_ranges(statement, specifier);
                statements.push(statement);
            }

            return single_or_many(Some(&statements), f);
        }

        if node.export_clause().is_some() {
            // export * as ns from "mod";
            // export * as default from "mod";
            let export_name = if is_string_literal(node.export_clause().name()) {
                f.new_string_literal_from_node(node.export_clause().name())
            } else {
                f.clone_node(node.export_clause().name())
            };
            let require_call = self.create_require_call(node);
            let helper_expression = self.get_helper_expression_for_export(node, require_call);
            let statement = f.new_expression_statement(self.create_export_expression(
                export_name,
                helper_expression,
                None,  /*location*/
                false, /*liveBinding*/
            ));
            ec.set_original(statement, node);
            ec.assign_comment_and_source_map_ranges(statement, node);
            return statement;
        }

        // export * from "mod";
        let helper =
            f.new_export_star_helper(self.create_require_call(node), f.new_identifier("exports"));
        let statement = f.new_expression_statement(self.visit_node_with(VisitorKind::Root, helper));
        ec.set_original(statement, node);
        ec.assign_comment_and_source_map_ranges(statement, node);
        statement
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:925 CommonJSModuleTransformer.visitTopLevelExportAssignment
    fn visit_top_level_export_assignment(&mut self, node: Node) -> Node {
        if node.is_export_equals() {
            return Node::NIL;
        }

        let name = self.emit_context.factory().new_identifier("default");
        let value = self.visit_node_with(VisitorKind::Root, node.expression());
        self.create_export_statement(
            name,
            value,
            Some(node.loc()), /*location*/
            true,             /*allowComments*/
            false,            /*liveBinding*/
        )
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:939 CommonJSModuleTransformer.visitTopLevelFunctionDeclaration
    fn visit_top_level_function_declaration(&mut self, node: Node) -> Node {
        if has_syntactic_modifier(node, ModifierFlags::EXPORT) {
            let ec = self.emit_context.clone();
            let f = ec.factory();
            let modifiers =
                extract_modifiers(&ec, node.modifiers(), !ModifierFlags::EXPORT_DEFAULT);
            let name = f.get_declaration_name(node);
            let parameters = self.visit_nodes_with(VisitorKind::Root, node.parameter_list());
            let body = self.visit_node_with(VisitorKind::Root, node.body());
            f.update_function_declaration(
                node,
                modifiers,
                node.asterisk_token(),
                name,
                NodeList::NIL, /*typeParameters*/
                parameters,
                Node::NIL, /*type*/
                Node::NIL, /*fullSignature*/
                body,
            )
        } else {
            self.visit_each_child_with(VisitorKind::Root, node)
        }
    }

    // Go: transformers/moduletransforms/commonjsmodule.go:957 CommonJSModuleTransformer.visitTopLevelClassDeclaration
    fn visit_top_level_class_declaration(&mut self, node: Node) -> Node {
        let ec = self.emit_context.clone();
        let f = ec.factory();
        let mut statements: Vec<Node> = Vec::new();
        if has_syntactic_modifier(node, ModifierFlags::EXPORT) {
            let modifiers =
                extract_modifiers(&ec, node.modifiers(), !ModifierFlags::EXPORT_DEFAULT);
            let modifiers = self.with_visitor(VisitorKind::Root, |v| v.visit_modifiers(modifiers));
            let name = f.get_declaration_name(node);
            let heritage_clauses =
                self.visit_nodes_with(VisitorKind::Root, node.heritage_clauses());
            let members = self.visit_nodes_with(VisitorKind::Root, node.member_list());
            statements.push(f.update_class_declaration(
                node,
                modifiers,
                name,
                NodeList::NIL, /*typeParameters*/
                heritage_clauses,
                members,
            ));
        } else {
            statements.push(self.visit_each_child_with(VisitorKind::Root, node));
        }
        statements = self.append_exports_of_class_or_function_declaration(statements, node);
        single_or_many(Some(&statements), f)
    }
}
