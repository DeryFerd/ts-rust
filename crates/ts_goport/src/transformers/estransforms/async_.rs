//! Port of Go `transformers/estransforms/async.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{
    SuperAccessState, TxVisitors, impl_es_transformer, source_file_is_declaration_file,
};
use crate::prelude::*;
use crate::printer::{
    ADVANCED_ASYNC_SUPER_HELPER, ASYNC_SUPER_HELPER, AutoGenerateOptions, EmitContext, EmitFlags,
    GeneratedIdentifierFlags,
};
use crate::transformers::utilities::convert_binding_pattern_to_assignment_pattern;

// Go: transformers/estransforms/async.go:12 asyncContextFlags
type AsyncContextFlags = i32;

const ASYNC_CONTEXT_NON_TOP_LEVEL: AsyncContextFlags = 1 << 0;
const ASYNC_CONTEXT_HAS_LEXICAL_THIS: AsyncContextFlags = 1 << 1;

// Go: transformers/estransforms/async.go:19 lexicalArgumentsInfo
#[derive(Clone, Copy)]
struct LexicalArgumentsInfo {
    binding: Node,
    used: bool,
}

impl Default for LexicalArgumentsInfo {
    fn default() -> Self {
        Self {
            binding: Node::NIL,
            used: false,
        }
    }
}

// Go: transformers/estransforms/async.go:24 asyncTransformer
pub struct AsyncTransformer {
    emit_context: Rc<EmitContext>,
    /// Go embedded `superAccessState`.
    super_access: SuperAccessState,

    context_flags: AsyncContextFlags,

    /// Go `*collections.Set[string]`; `None` is nil.
    enclosing_function_parameter_names: Option<FxHashSet<String>>,
    lexical_arguments: LexicalArgumentsInfo,
}

impl_es_transformer!(AsyncTransformer);

// Go: transformers/estransforms/async.go:37 newAsyncTransformer
pub fn new_async_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    let mut tx = AsyncTransformer {
        emit_context: opts.context.clone(),
        super_access: SuperAccessState::default(),
        context_flags: 0,
        enclosing_function_parameter_names: None,
        lexical_arguments: LexicalArgumentsInfo::default(),
    };
    tx.super_access.init_super_access_visitor(&opts.context);
    Some(Box::new(tx))
}

/// Go `printer.AutoGenerateOptions{Flags: Optimistic | FileLevel}`.
fn optimistic_file_level() -> AutoGenerateOptions {
    AutoGenerateOptions {
        flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
        ..Default::default()
    }
}

impl AsyncTransformer {
    // Go: transformers/estransforms/async.go:46 asyncTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        if source_file_is_declaration_file(node) {
            return node;
        }

        self.set_context_flag(ASYNC_CONTEXT_NON_TOP_LEVEL, false);
        self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, false);
        let visited = self.visit_each_child(node);
        let ec = self.ec();
        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        visited
    }

    // Go: transformers/estransforms/async.go:57 asyncTransformer.setContextFlag
    fn set_context_flag(&mut self, flag: AsyncContextFlags, val: bool) {
        if val {
            self.context_flags |= flag;
        } else {
            self.context_flags &= !flag;
        }
    }

    // Go: transformers/estransforms/async.go:65 asyncTransformer.inContext
    fn in_context(&self, flags: AsyncContextFlags) -> bool {
        self.context_flags & flags != 0
    }

    // Go: transformers/estransforms/async.go:69 asyncTransformer.inTopLevelContext
    fn in_top_level_context(&self) -> bool {
        !self.in_context(ASYNC_CONTEXT_NON_TOP_LEVEL)
    }

    // Go: transformers/estransforms/async.go:73 asyncTransformer.inHasLexicalThisContext
    fn in_has_lexical_this_context(&self) -> bool {
        self.in_context(ASYNC_CONTEXT_HAS_LEXICAL_THIS)
    }

    // Go: transformers/estransforms/async.go:77 asyncTransformer.doWithContext
    fn do_with_context(
        &mut self,
        flags: AsyncContextFlags,
        cb: fn(&mut Self, Node) -> Node,
        node: Node,
    ) -> Node {
        let flags_to_set = flags & !self.context_flags;
        if flags_to_set != 0 {
            self.set_context_flag(flags_to_set, true);
            let result = cb(self, node);
            self.set_context_flag(flags_to_set, false);
            return result;
        }
        cb(self, node)
    }

    // Go: transformers/estransforms/async.go:88 asyncTransformer.visitDefault
    fn visit_default(&mut self, node: Node) -> Node {
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/async.go:92 asyncTransformer.fallbackVisitor
    fn fallback_visitor(&mut self, node: Node) -> Node {
        if self.super_access.captured_super_properties.is_none()
            && self.lexical_arguments.binding.is_nil()
        {
            return node;
        }
        self.super_access.track_super_access(node);
        match node.kind() {
            SyntaxKind::FunctionExpression
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::Constructor => return node,
            SyntaxKind::Parameter
            | SyntaxKind::BindingElement
            | SyntaxKind::VariableDeclaration => {
                // fall through to visitEachChild
            }
            SyntaxKind::Identifier => {
                if self.lexical_arguments.binding.is_some()
                    && node.text() == "arguments"
                    && !is_identifier_name(node)
                    && !is_label_name(node)
                {
                    self.lexical_arguments.used = true;
                    return self.lexical_arguments.binding;
                }
            }
            _ => {}
        }
        self.with_visitor(Self::visit_fallback, |v| v.visit_each_child(node))
    }

    // Go: transformers/estransforms/async.go:121 asyncTransformer.visitFallback
    fn visit_fallback(&mut self, node: Node) -> Node {
        self.fallback_visitor(node)
    }

    // Go: transformers/estransforms/async.go:125 asyncTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        let ec = self.ec();
        if ec.emit_flags(node).intersects(EmitFlags::NO_LEXICAL_THIS)
            && self.in_has_lexical_this_context()
        {
            self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, false);
            let result = self.visit_worker(node);
            self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, true);
            return result;
        }
        self.visit_worker(node)
    }

    /// The body of Go `visit` after the deferred context restore.
    fn visit_worker(&mut self, node: Node) -> Node {
        if !node.subtree_facts().intersects(
            SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT | SubtreeFacts::SUBTREE_CONTAINS_AWAIT,
        ) {
            return self.fallback_visitor(node);
        }
        self.super_access.track_super_access(node);
        let non_top_level_with_this = ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS;
        match node.kind() {
            // ES2017 async modifier should be elided for targets < ES2017
            SyntaxKind::AsyncKeyword => Node::NIL,
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::AwaitExpression => self.visit_await_expression(node),
            SyntaxKind::MethodDeclaration => self.do_with_context(
                non_top_level_with_this,
                Self::visit_method_declaration,
                node,
            ),
            SyntaxKind::FunctionDeclaration => self.do_with_context(
                non_top_level_with_this,
                Self::visit_function_declaration,
                node,
            ),
            SyntaxKind::FunctionExpression => self.do_with_context(
                non_top_level_with_this,
                Self::visit_function_expression,
                node,
            ),
            SyntaxKind::ArrowFunction => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL,
                Self::visit_arrow_function,
                node,
            ),
            SyntaxKind::GetAccessor => self.do_with_context(
                non_top_level_with_this,
                Self::visit_get_accessor_declaration,
                node,
            ),
            SyntaxKind::SetAccessor => self.do_with_context(
                non_top_level_with_this,
                Self::visit_set_accessor_declaration,
                node,
            ),
            SyntaxKind::Constructor => self.do_with_context(
                non_top_level_with_this,
                Self::visit_constructor_declaration,
                node,
            ),
            SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression => {
                self.do_with_context(non_top_level_with_this, Self::visit_default, node)
            }
            _ => self.visit_each_child(node),
        }
    }

    /// Go `tx.asyncBodyVisitor.VisitEachChild(node)`.
    fn async_body_visit_each_child(&mut self, node: Node) -> Node {
        self.with_visitor(Self::visit_async_body_node, |v| v.visit_each_child(node))
    }

    /// Go `tx.asyncBodyVisitor.VisitEmbeddedStatement(node)`.
    fn async_body_visit_embedded_statement(&mut self, node: Node) -> Node {
        self.with_visitor(Self::visit_async_body_node, |v| {
            v.visit_embedded_statement(node)
        })
    }

    // Go: transformers/estransforms/async.go:167 asyncTransformer.visitAsyncBodyNode
    fn visit_async_body_node(&mut self, node: Node) -> Node {
        if is_node_with_possible_hoisted_declaration(node) {
            match node.kind() {
                SyntaxKind::VariableStatement => {
                    return self.visit_variable_statement_in_async_body(node);
                }
                SyntaxKind::ForStatement => return self.visit_for_statement_in_async_body(node),
                SyntaxKind::ForInStatement => {
                    return self.visit_for_in_statement_in_async_body(node);
                }
                SyntaxKind::ForOfStatement => {
                    return self.visit_for_of_statement_in_async_body(node);
                }
                SyntaxKind::CatchClause => return self.visit_catch_clause_in_async_body(node),
                SyntaxKind::Block
                | SyntaxKind::SwitchStatement
                | SyntaxKind::CaseBlock
                | SyntaxKind::CaseClause
                | SyntaxKind::DefaultClause
                | SyntaxKind::TryStatement
                | SyntaxKind::DoStatement
                | SyntaxKind::WhileStatement
                | SyntaxKind::IfStatement
                | SyntaxKind::WithStatement
                | SyntaxKind::LabeledStatement => return self.async_body_visit_each_child(node),
                _ => {}
            }
        }
        self.visit(node)
    }

    // Go: transformers/estransforms/async.go:197 asyncTransformer.visitCatchClauseInAsyncBody
    fn visit_catch_clause_in_async_body(&mut self, node: Node) -> Node {
        let mut catch_clause_names: FxHashSet<String> = FxHashSet::default();
        if node.variable_declaration().is_some() {
            self.record_declaration_name(node.variable_declaration(), &mut catch_clause_names);
        }

        // names declared in a catch variable are block scoped
        let mut catch_clause_unshadowed_names: Option<FxHashSet<String>> = None;
        for escaped_name in &catch_clause_names {
            if self
                .enclosing_function_parameter_names
                .as_ref()
                .is_some_and(|names| names.contains(escaped_name))
            {
                let unshadowed = catch_clause_unshadowed_names.get_or_insert_with(|| {
                    self.enclosing_function_parameter_names
                        .clone()
                        .unwrap_or_default()
                });
                unshadowed.remove(escaped_name);
            }
        }

        if let Some(unshadowed) = catch_clause_unshadowed_names {
            let saved_enclosing_function_parameter_names =
                self.enclosing_function_parameter_names.replace(unshadowed);
            let result = self.async_body_visit_each_child(node);
            self.enclosing_function_parameter_names = saved_enclosing_function_parameter_names;
            return result;
        }
        self.async_body_visit_each_child(node)
    }

    // Go: transformers/estransforms/async.go:224 asyncTransformer.visitVariableStatementInAsyncBody
    fn visit_variable_statement_in_async_body(&mut self, node: Node) -> Node {
        let decl_list = node.declaration_list();
        if self.is_variable_declaration_list_with_colliding_name(decl_list) {
            let expression =
                self.visit_variable_declaration_list_with_colliding_names(decl_list, false);
            if expression.is_some() {
                return self.ec().factory().new_expression_statement(expression);
            }
            return Node::NIL;
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/async.go:236 asyncTransformer.visitForInStatementInAsyncBody
    fn visit_for_in_statement_in_async_body(&mut self, node: Node) -> Node {
        let visited_initializer =
            if self.is_variable_declaration_list_with_colliding_name(node.initializer()) {
                self.visit_variable_declaration_list_with_colliding_names(node.initializer(), true)
            } else {
                self.visit_node(node.initializer())
            };

        let expression = self.visit_node(node.expression());
        let statement = self.async_body_visit_embedded_statement(node.statement());
        self.ec().factory().update_for_in_or_of_statement(
            node,
            Node::NIL, /*awaitModifier*/
            visited_initializer,
            expression,
            statement,
        )
    }

    // Go: transformers/estransforms/async.go:253 asyncTransformer.visitForOfStatementInAsyncBody
    fn visit_for_of_statement_in_async_body(&mut self, node: Node) -> Node {
        let visited_initializer =
            if self.is_variable_declaration_list_with_colliding_name(node.initializer()) {
                self.visit_variable_declaration_list_with_colliding_names(node.initializer(), true)
            } else {
                self.visit_node(node.initializer())
            };

        let await_modifier = self.visit_node(node.await_modifier());
        let expression = self.visit_node(node.expression());
        let statement = self.async_body_visit_embedded_statement(node.statement());
        self.ec().factory().update_for_in_or_of_statement(
            node,
            await_modifier,
            visited_initializer,
            expression,
            statement,
        )
    }

    // Go: transformers/estransforms/async.go:270 asyncTransformer.visitForStatementInAsyncBody
    fn visit_for_statement_in_async_body(&mut self, node: Node) -> Node {
        let initializer = node.initializer();
        let visited_initializer = if initializer.is_some()
            && self.is_variable_declaration_list_with_colliding_name(initializer)
        {
            self.visit_variable_declaration_list_with_colliding_names(initializer, false)
        } else {
            self.visit_node(node.initializer())
        };

        let condition = self.visit_node(node.condition());
        let incrementor = self.visit_node(node.incrementor());
        let statement = self.async_body_visit_embedded_statement(node.statement());
        self.ec().factory().update_for_statement(
            node,
            visited_initializer,
            condition,
            incrementor,
            statement,
        )
    }

    // Go: transformers/estransforms/async.go:291 asyncTransformer.visitAwaitExpression
    /// visitAwaitExpression visits an AwaitExpression node.
    ///
    /// This function will be called any time a ES2017 await expression is encountered.
    fn visit_await_expression(&mut self, node: Node) -> Node {
        // do not downlevel a top-level await as it is module syntax...
        if self.in_top_level_context() {
            return self.visit_each_child(node);
        }
        let expression = self.visit_node(node.expression());
        let ec = self.ec();
        let yield_expr = ec
            .factory()
            .new_yield_expression(Node::NIL /*asteriskToken*/, expression);
        set_node_loc(yield_expr, node.loc());
        ec.set_original(yield_expr, node);
        yield_expr
    }

    // Go: transformers/estransforms/async.go:305 asyncTransformer.visitConstructorDeclaration
    fn visit_constructor_declaration(&mut self, node: Node) -> Node {
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();
        let modifiers = self.visit_modifiers(node.modifiers());
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.transform_method_body(node);
        let updated = self.ec().factory().update_constructor_declaration(
            node,
            modifiers,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:325 asyncTransformer.visitMethodDeclaration
    /// visitMethodDeclaration visits a MethodDeclaration node.
    ///
    /// This function will be called when one of the following conditions are met:
    /// - The node is marked as async
    fn visit_method_declaration(&mut self, node: Node) -> Node {
        let function_flags = get_function_flags(node);
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();

        let parameters;
        let body;
        if function_flags.intersects(FunctionFlags::ASYNC) {
            parameters = self.transform_async_function_parameter_list(node);
            body = self.transform_async_function_body(node, parameters);
        } else {
            parameters = self.visit_parameters(node.parameter_list());
            body = self.transform_method_body(node);
        }

        let modifiers = self.visit_modifiers(node.modifiers());
        let updated = self.ec().factory().update_method_declaration(
            node,
            modifiers,
            node.asterisk_token(),
            node.name(),
            Node::NIL,     /*postfixToken*/
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:356 asyncTransformer.visitGetAccessorDeclaration
    fn visit_get_accessor_declaration(&mut self, node: Node) -> Node {
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();
        let modifiers = self.visit_modifiers(node.modifiers());
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.transform_method_body(node);
        let updated = self.ec().factory().update_get_accessor_declaration(
            node,
            modifiers,
            node.name(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:373 asyncTransformer.visitSetAccessorDeclaration
    fn visit_set_accessor_declaration(&mut self, node: Node) -> Node {
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();
        let modifiers = self.visit_modifiers(node.modifiers());
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.transform_method_body(node);
        let updated = self.ec().factory().update_set_accessor_declaration(
            node,
            modifiers,
            node.name(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:394 asyncTransformer.visitFunctionDeclaration
    /// visitFunctionDeclaration visits a FunctionDeclaration node.
    ///
    /// This function will be called when one of the following conditions are met:
    /// - The node is marked async
    fn visit_function_declaration(&mut self, node: Node) -> Node {
        let function_flags = get_function_flags(node);
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();

        let parameters;
        let body;
        if function_flags.intersects(FunctionFlags::ASYNC) {
            parameters = self.transform_async_function_parameter_list(node);
            body = self.transform_async_function_body(node, parameters);
        } else {
            parameters = self.visit_parameters(node.parameter_list());
            body = self.visit_function_body(node.body());
        }

        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_node(node.name());
        let updated = self.ec().factory().update_function_declaration(
            node,
            modifiers,
            node.asterisk_token(),
            name,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:429 asyncTransformer.visitFunctionExpression
    /// visitFunctionExpression visits a FunctionExpression node.
    ///
    /// This function will be called when one of the following conditions are met:
    /// - The node is marked async
    fn visit_function_expression(&mut self, node: Node) -> Node {
        let function_flags = get_function_flags(node);
        let saved_lexical_arguments = self.lexical_arguments;
        self.lexical_arguments = LexicalArgumentsInfo::default();

        let parameters;
        let body;
        if function_flags.intersects(FunctionFlags::ASYNC) {
            parameters = self.transform_async_function_parameter_list(node);
            body = self.transform_async_function_body(node, parameters);
        } else {
            parameters = self.visit_parameters(node.parameter_list());
            body = self.visit_function_body(node.body());
        }

        let modifiers = self.visit_modifiers(node.modifiers());
        let name = self.visit_node(node.name());
        let updated = self.ec().factory().update_function_expression(
            node,
            modifiers,
            node.asterisk_token(),
            name,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.lexical_arguments = saved_lexical_arguments;
        updated
    }

    // Go: transformers/estransforms/async.go:464 asyncTransformer.visitArrowFunction
    /// visitArrowFunction visits an ArrowFunction.
    ///
    /// This function will be called when one of the following conditions are met:
    /// - The node is marked async
    fn visit_arrow_function(&mut self, node: Node) -> Node {
        // `arguments` in class static blocks is always an error, but we preserve Strada's emit
        // behavior for baseline compatibility. In Strada, checker-based `isArgumentsLocalBinding`
        // returns false for `arguments` in static blocks (since the binding doesn't exist due to
        // the error), so the async transform leaves them untouched.
        if self
            .ec()
            .emit_flags(node)
            .intersects(EmitFlags::NO_LEXICAL_ARGUMENTS)
        {
            let saved_lexical_arguments = self.lexical_arguments;
            self.lexical_arguments = LexicalArgumentsInfo::default();
            let result = self.visit_arrow_function_worker(node);
            self.lexical_arguments = saved_lexical_arguments;
            return result;
        }
        self.visit_arrow_function_worker(node)
    }

    /// The body of Go `visitArrowFunction` after the deferred restore.
    fn visit_arrow_function_worker(&mut self, node: Node) -> Node {
        let function_flags = get_function_flags(node);

        let parameters;
        let body;
        if function_flags.intersects(FunctionFlags::ASYNC) {
            parameters = self.transform_async_function_parameter_list(node);
            body = self.transform_async_function_body(node, parameters);
        } else {
            parameters = self.visit_parameters(node.parameter_list());
            body = self.visit_function_body(node.body());
        }

        let modifiers = self.visit_modifiers(node.modifiers());
        self.ec().factory().update_arrow_function(
            node,
            modifiers,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            node.equals_greater_than_token(),
            body,
        )
    }

    // Go: transformers/estransforms/async.go:502 asyncTransformer.recordDeclarationName
    fn record_declaration_name(&self, node: Node, names: &mut FxHashSet<String>) {
        let name = node.name();
        if name.is_nil() {
            return;
        }
        if is_identifier(name) {
            names.insert(name.text().to_string());
        } else if is_binding_pattern(name) {
            for element in name.elements().iter() {
                if !is_omitted_expression(element) {
                    self.record_declaration_name(element, names);
                }
            }
        }
    }

    // Go: transformers/estransforms/async.go:518 asyncTransformer.isVariableDeclarationListWithCollidingName
    fn is_variable_declaration_list_with_colliding_name(&self, node: Node) -> bool {
        node.is_some()
            && is_variable_declaration_list(node)
            && !node.flags().intersects(NodeFlags::BLOCK_SCOPED)
            && node
                .declarations()
                .nodes()
                .iter()
                .any(|d| self.collides_with_parameter_name(d))
    }

    // Go: transformers/estransforms/async.go:525 asyncTransformer.visitVariableDeclarationListWithCollidingNames
    fn visit_variable_declaration_list_with_colliding_names(
        &mut self,
        node: Node,
        has_receiver: bool,
    ) -> Node {
        self.hoist_variable_declaration_list(node);

        let mut variables: Vec<Node> = Vec::new();
        for decl in node.declarations().nodes().iter() {
            if decl.initializer().is_some() {
                variables.push(decl);
            }
        }

        if variables.is_empty() {
            if has_receiver {
                let name = node.declarations().nodes().get(0).name();
                let target = if is_binding_pattern(name) {
                    convert_binding_pattern_to_assignment_pattern(&self.ec(), name)
                } else {
                    name
                };
                return self.visit_node(target);
            }
            return Node::NIL;
        }

        let mut expressions: Vec<Node> = Vec::new();
        for variable in variables {
            expressions.push(self.transform_initialized_variable(variable));
        }
        self.ec().factory().inline_expressions(&expressions)
    }

    // Go: transformers/estransforms/async.go:554 asyncTransformer.hoistVariableDeclarationList
    fn hoist_variable_declaration_list(&self, node: Node) {
        for decl in node.declarations().nodes().iter() {
            self.hoist_variable(decl);
        }
    }

    // Go: transformers/estransforms/async.go:560 asyncTransformer.hoistVariable
    fn hoist_variable(&self, node: Node) {
        let name = node.name();
        if name.is_nil() {
            return;
        }
        if is_identifier(name) {
            self.emit_context.add_variable_declaration(name);
        } else if is_binding_pattern(name) {
            for element in name.elements().iter() {
                if !is_omitted_expression(element) {
                    self.hoist_variable(element);
                }
            }
        }
    }

    // Go: transformers/estransforms/async.go:576 asyncTransformer.transformInitializedVariable
    fn transform_initialized_variable(&mut self, node: Node) -> Node {
        let ec = self.ec();
        let target = if is_binding_pattern(node.name()) {
            convert_binding_pattern_to_assignment_pattern(&ec, node.name())
        } else {
            node.name()
        };
        let converted = ec
            .factory()
            .new_assignment_expression(target, node.initializer());
        ec.set_source_map_range(converted, node.loc());
        self.visit_node(converted)
    }

    // Go: transformers/estransforms/async.go:588 asyncTransformer.collidesWithParameterName
    fn collides_with_parameter_name(&self, node: Node) -> bool {
        let name = node.name();
        if name.is_nil() {
            return false;
        }
        if is_identifier(name) {
            return self
                .enclosing_function_parameter_names
                .as_ref()
                .is_some_and(|names| names.contains(name.text()));
        }
        if is_binding_pattern(name) {
            for element in name.elements().iter() {
                if !is_omitted_expression(element) && self.collides_with_parameter_name(element) {
                    return true;
                }
            }
        }
        false
    }

    /// Saves the Go `superAccessState` fields that `transformMethodBody` and
    /// `transformAsyncFunctionBody` save and restore.
    fn save_super_access(&self) -> (Option<IndexSet<String>>, bool, bool, Node, Node) {
        let s = &self.super_access;
        (
            s.captured_super_properties.clone(),
            s.has_super_element_access,
            s.has_super_property_assignment,
            s.super_binding,
            s.super_index_binding,
        )
    }

    fn restore_super_access(&mut self, saved: (Option<IndexSet<String>>, bool, bool, Node, Node)) {
        let s = &mut self.super_access;
        s.captured_super_properties = saved.0;
        s.has_super_element_access = saved.1;
        s.has_super_property_assignment = saved.2;
        s.super_binding = saved.3;
        s.super_index_binding = saved.4;
    }

    /// Go: reset the `superAccessState` fields for a new method body.
    fn reset_super_access(&mut self) {
        let f = self.emit_context.factory();
        let super_binding = f.new_unique_name_ex("_super", optimistic_file_level());
        let super_index_binding = f.new_unique_name_ex("_superIndex", optimistic_file_level());
        let s = &mut self.super_access;
        s.captured_super_properties = Some(IndexSet::new());
        s.has_super_element_access = false;
        s.has_super_property_assignment = false;
        s.super_binding = super_binding;
        s.super_index_binding = super_index_binding;
    }

    fn captured_super_properties_len(&self) -> usize {
        self.super_access
            .captured_super_properties
            .as_ref()
            .map_or(0, IndexSet::len)
    }

    // Go: transformers/estransforms/async.go:607 asyncTransformer.transformMethodBody
    fn transform_method_body(&mut self, node: Node) -> Node {
        let saved = self.save_super_access();
        self.reset_super_access();

        let ec = self.ec();
        let f = ec.factory();
        ec.start_variable_environment();
        let mut updated = self.visit_function_body(node.body());

        // Minor optimization, emit `_super` helper to capture `super` access in an arrow.
        let emit_super_helpers = (self.captured_super_properties_len() > 0
            || self.super_access.has_super_element_access)
            && (get_function_flags(self.get_original_if_function_like(node))
                & FunctionFlags::ASYNC_GENERATOR)
                != FunctionFlags::ASYNC_GENERATOR;

        if emit_super_helpers && self.captured_super_properties_len() > 0 {
            ec.add_initialization_statement(
                self.super_access.create_super_access_variable_statement(),
            );
        }

        let merged_statements =
            ec.end_and_merge_variable_environment_list(updated.statement_list());
        if emit_super_helpers && self.super_access.has_super_element_access && !updated.multi_line()
        {
            let new_block = f.new_block(merged_statements, true);
            set_node_loc(new_block, updated.loc());
            updated = new_block;
        } else {
            updated = f.update_block(updated, merged_statements, updated.multi_line());
        }

        if emit_super_helpers && self.super_access.has_super_element_access {
            if self.super_access.has_super_property_assignment {
                ec.add_emit_helper(updated, &[&ADVANCED_ASYNC_SUPER_HELPER]);
            } else {
                ec.add_emit_helper(updated, &[&ASYNC_SUPER_HELPER]);
            }
        }

        self.restore_super_access(saved);
        updated
    }

    // Go: transformers/estransforms/async.go:651 asyncTransformer.createCaptureArgumentsStatement
    fn create_capture_arguments_statement(&self) -> Node {
        let ec = &self.emit_context;
        let f = ec.factory();
        let variable = f.new_variable_declaration(
            self.lexical_arguments.binding,
            Node::NIL,
            Node::NIL,
            f.new_identifier("arguments"),
        );
        let decl_list =
            f.new_variable_declaration_list(f.new_node_list(&[variable]), NodeFlags::NONE);
        let statement = f.new_variable_statement(ModifierList::NIL, decl_list);
        ec.add_emit_flags(
            statement,
            EmitFlags::START_ON_NEW_LINE | EmitFlags::CUSTOM_PROLOGUE,
        );
        statement
    }

    // Go: transformers/estransforms/async.go:664 asyncTransformer.transformAsyncFunctionParameterList
    fn transform_async_function_parameter_list(&mut self, node: Node) -> NodeList {
        if is_simple_parameter_list(&node.parameters().to_vec()) {
            return self.visit_parameters(node.parameter_list());
        }

        let f = self.emit_context.factory();
        let mut new_parameters: Vec<Node> = Vec::new();
        for param in node.parameters().iter() {
            if param.initializer().is_some() || param.dot_dot_dot_token().is_some() {
                // for an arrow function, capture the remaining arguments in a rest parameter.
                // for any other function/method this isn't necessary as we can just use `arguments`.
                if node.kind() == SyntaxKind::ArrowFunction {
                    let rest_parameter = f.new_parameter_declaration(
                        ModifierList::NIL,
                        f.new_token(SyntaxKind::DotDotDotToken),
                        f.new_unique_name_ex(
                            "args",
                            AutoGenerateOptions {
                                flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                                ..Default::default()
                            },
                        ),
                        Node::NIL,
                        Node::NIL,
                        Node::NIL,
                    );
                    new_parameters.push(rest_parameter);
                }
                break;
            }
            // for arrow functions we capture fixed parameters to forward to `__awaiter`. For all other functions
            // we add fixed parameters to preserve the function's `length` property.
            let new_parameter = f.new_parameter_declaration(
                ModifierList::NIL,
                Node::NIL,
                f.new_generated_name_for_node_ex(
                    param.name(),
                    AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                        ..Default::default()
                    },
                ),
                Node::NIL,
                Node::NIL,
                Node::NIL,
            );
            new_parameters.push(new_parameter);
        }
        f.new_node_list_with_loc(&new_parameters, node.parameter_list().loc())
    }

    // Go: transformers/estransforms/async.go:707 asyncTransformer.transformAsyncFunctionBody
    fn transform_async_function_body(&mut self, node: Node, outer_parameters: NodeList) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        let is_arrow = node.kind() == SyntaxKind::ArrowFunction;
        let saved = self.save_super_access();
        if !is_arrow {
            self.reset_super_access();
        }

        let mut inner_parameters = NodeList::NIL;
        if !is_simple_parameter_list(&node.parameters().to_vec()) {
            inner_parameters = self.visit_parameters(node.parameter_list());
        }

        let saved_lexical_arguments = self.lexical_arguments;
        let capture_lexical_arguments = self.lexical_arguments.binding.is_nil();
        if capture_lexical_arguments {
            self.lexical_arguments = LexicalArgumentsInfo {
                binding: f.new_unique_name("arguments"),
                used: false,
            };
        }

        let mut arguments_expression = Node::NIL;
        if inner_parameters.is_some() {
            if is_arrow {
                // `node` does not have a simple parameter list, so `outerParameters` refers to placeholders that are
                // forwarded to `innerParameters`, matching how they are introduced in `transformAsyncFunctionParameterList`.
                let mut parameter_bindings: Vec<Node> = Vec::new();
                let outer_nodes = outer_parameters.nodes();
                let outer_len = outer_nodes.len();
                for (i, original_parameter) in node.parameters().iter().enumerate() {
                    if i >= outer_len {
                        break;
                    }
                    let outer_parameter = outer_nodes.get(i);
                    if original_parameter.initializer().is_some()
                        || original_parameter.dot_dot_dot_token().is_some()
                    {
                        parameter_bindings.push(f.new_spread_element(outer_parameter.name()));
                        break;
                    }
                    parameter_bindings.push(outer_parameter.name());
                }
                arguments_expression =
                    f.new_array_literal_expression(f.new_node_list(&parameter_bindings), false);
            } else {
                arguments_expression = f.new_identifier("arguments");
            }
        }

        // An async function is emit as an outer function that calls an inner
        // generator function. To preserve lexical bindings, we pass the current
        // `this` and `arguments` objects to `__awaiter`. The generator function
        // passed to `__awaiter` is executed inside of the callback to the
        // promise constructor.

        let saved_enclosing_function_parameter_names =
            self.enclosing_function_parameter_names.take();
        let mut names: FxHashSet<String> = FxHashSet::default();
        for parameter in node.parameters().iter() {
            self.record_declaration_name(parameter, &mut names);
        }
        self.enclosing_function_parameter_names = Some(names);

        let has_lexical_this = self.in_has_lexical_this_context();

        let mut async_body = self.transform_async_function_body_worker(node.body());
        async_body = f.update_block(
            async_body,
            ec.end_and_merge_variable_environment_list(async_body.statement_list()),
            async_body.multi_line(),
        );

        // Substitute super property accesses with _super/_superIndex helpers
        let emit_super_helpers = self.super_access.captured_super_properties.is_some()
            && (self.captured_super_properties_len() > 0
                || self.super_access.has_super_element_access);
        if emit_super_helpers {
            inner_parameters = self.super_access.super_access_visit_nodes(inner_parameters);
            async_body = self
                .super_access
                .substitute_super_accesses_in_body(async_body);
        }

        let result;
        if !is_arrow {
            ec.start_variable_environment();

            // Minor optimization, emit `_super` helper to capture `super` access in an arrow.
            if emit_super_helpers && self.captured_super_properties_len() > 0 {
                ec.add_initialization_statement(
                    self.super_access.create_super_access_variable_statement(),
                );
            }

            if capture_lexical_arguments && self.lexical_arguments.used {
                ec.add_initialization_statement(self.create_capture_arguments_statement());
            }

            let statements = [f.new_return_statement(f.new_awaiter_helper(
                has_lexical_this,
                arguments_expression,
                inner_parameters,
                async_body,
            ))];

            let block = f.new_block(
                ec.end_and_merge_variable_environment_list(f.new_node_list(&statements)),
                true,
            );
            set_node_loc(block, node.body().loc());

            if emit_super_helpers && self.super_access.has_super_element_access {
                if self.super_access.has_super_property_assignment {
                    ec.add_emit_helper(block, &[&ADVANCED_ASYNC_SUPER_HELPER]);
                } else {
                    ec.add_emit_helper(block, &[&ASYNC_SUPER_HELPER]);
                }
            }

            result = block;
        } else {
            let mut r = f.new_awaiter_helper(
                has_lexical_this,
                arguments_expression,
                inner_parameters,
                async_body,
            );

            if capture_lexical_arguments && self.lexical_arguments.used {
                let block = self.convert_to_function_block(r);
                r = f.update_block(
                    block,
                    ec.merge_environment_list(
                        block.statement_list(),
                        &[self.create_capture_arguments_statement()],
                    ),
                    block.multi_line(),
                );
            }
            result = r;
        }

        self.enclosing_function_parameter_names = saved_enclosing_function_parameter_names;
        if !is_arrow {
            self.restore_super_access(saved);
            self.lexical_arguments = saved_lexical_arguments;
        } else if capture_lexical_arguments && !self.lexical_arguments.used {
            // If we created a new binding but it wasn't used, restore the previous state.
            // If it was used, keep the binding alive so sibling arrows can reuse it
            // (the `var` declaration hoists to the enclosing function scope).
            self.lexical_arguments = saved_lexical_arguments;
        } else if capture_lexical_arguments {
            // Keep the binding but clear the used flag so siblings don't re-emit the capture statement.
            self.lexical_arguments.used = false;
        }
        result
    }

    // Go: transformers/estransforms/async.go:869 asyncTransformer.transformAsyncFunctionBodyWorker
    fn transform_async_function_body_worker(&mut self, body: Node) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        if is_block(body) {
            let statements = self.with_visitor(Self::visit_async_body_node, |v| {
                v.visit_nodes(body.statement_list())
            });
            return f.update_block(body, statements, body.multi_line());
        }
        // Convert expression body to block body with return statement
        let visited = self.with_visitor(Self::visit_async_body_node, |v| v.visit_node(body));
        let ret = f.new_return_statement(visited);
        set_node_loc(ret, body.loc());
        let list = f.new_node_list_with_loc(&[ret], body.loc());
        let block = f.new_block(list, false /*multiLine*/);
        set_node_loc(block, body.loc());
        block
    }

    // Go: transformers/estransforms/async.go:889 asyncTransformer.convertToFunctionBlock
    fn convert_to_function_block(&self, node: Node) -> Node {
        if is_block(node) {
            return node;
        }
        let ec = &self.emit_context;
        let f = ec.factory();
        let ret = f.new_return_statement(node);
        set_node_loc(ret, node.loc());
        ec.set_original(ret, node);
        let list = f.new_node_list_with_loc(&[ret], node.loc());
        let block = f.new_block(list, true);
        set_node_loc(block, node.loc());
        block
    }

    // Go: transformers/estransforms/async.go:954 asyncTransformer.getOriginalIfFunctionLike
    fn get_original_if_function_like(&self, node: Node) -> Node {
        let original = self.emit_context.most_original(node);
        if original.is_some() && is_function_like_declaration(original) {
            return original;
        }
        node
    }
}

// Go: transformers/estransforms/async.go:963 isSimpleParameterList
/// isSimpleParameterList checks if every parameter has no initializer and an Identifier name.
pub(super) fn is_simple_parameter_list(params: &[Node]) -> bool {
    for &param in params {
        if param.initializer().is_some() || !is_identifier(param.name()) {
            return false;
        }
    }
    true
}

// Go: transformers/estransforms/async.go:974 isNodeWithPossibleHoistedDeclaration
/// isNodeWithPossibleHoistedDeclaration checks if a node could contain hoisted declarations.
pub(super) fn is_node_with_possible_hoisted_declaration(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Block
            | SyntaxKind::VariableStatement
            | SyntaxKind::WithStatement
            | SyntaxKind::IfStatement
            | SyntaxKind::SwitchStatement
            | SyntaxKind::CaseBlock
            | SyntaxKind::CaseClause
            | SyntaxKind::DefaultClause
            | SyntaxKind::LabeledStatement
            | SyntaxKind::ForStatement
            | SyntaxKind::ForInStatement
            | SyntaxKind::ForOfStatement
            | SyntaxKind::DoStatement
            | SyntaxKind::WhileStatement
            | SyntaxKind::TryStatement
            | SyntaxKind::CatchClause
    )
}

// Go: transformers/estransforms/async.go:910 assignmentTargetContainsSuperProperty
pub(crate) fn assignment_target_contains_super_property(node: Node) -> bool {
    match node.kind() {
        SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
            node.expression().kind() == SyntaxKind::SuperKeyword
        }
        SyntaxKind::ParenthesizedExpression => {
            assignment_target_contains_super_property(node.expression())
        }
        SyntaxKind::ArrayLiteralExpression => node
            .elements()
            .iter()
            .any(assignment_target_contains_super_property),
        SyntaxKind::ObjectLiteralExpression => {
            for prop in node.properties().iter() {
                match prop.kind() {
                    SyntaxKind::PropertyAssignment => {
                        if assignment_target_contains_super_property(prop.initializer()) {
                            return true;
                        }
                    }
                    SyntaxKind::ShorthandPropertyAssignment => {
                        if assignment_target_contains_super_property(prop.name()) {
                            return true;
                        }
                    }
                    SyntaxKind::SpreadAssignment => {
                        if assignment_target_contains_super_property(prop.expression()) {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            false
        }
        SyntaxKind::SpreadElement => assignment_target_contains_super_property(node.expression()),
        _ => false,
    }
}

// Go: transformers/estransforms/async.go:942 isUpdateExpression
pub(crate) fn is_update_expression(node: Node) -> bool {
    if is_prefix_unary_expression(node) {
        let op = node.operator();
        return op == SyntaxKind::PlusPlusToken || op == SyntaxKind::MinusMinusToken;
    }
    if is_postfix_unary_expression(node) {
        let op = node.operator();
        return op == SyntaxKind::PlusPlusToken || op == SyntaxKind::MinusMinusToken;
    }
    false
}
