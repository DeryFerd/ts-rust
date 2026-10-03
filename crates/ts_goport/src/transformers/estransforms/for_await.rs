//! Port of Go `transformers/estransforms/forawait.go`.

use super::async_::is_simple_parameter_list;
use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{SuperAccessState, TxVisitors, impl_es_transformer};
use crate::prelude::*;
use crate::printer::{
    ADVANCED_ASYNC_SUPER_HELPER, ASYNC_SUPER_HELPER, AutoGenerateOptions, EmitContext, EmitFlags,
    GeneratedIdentifierFlags,
};

// Go: transformers/estransforms/forawait.go:12 forAwaitHierarchyFacts
/// Facts we track as we traverse the tree
type ForAwaitHierarchyFacts = i32;

const FOR_AWAIT_HIERARCHY_FACTS_NONE: ForAwaitHierarchyFacts = 0;

//
// Ancestor facts
//

const FOR_AWAIT_HIERARCHY_FACTS_HAS_LEXICAL_THIS: ForAwaitHierarchyFacts = 1 << 0;
const FOR_AWAIT_HIERARCHY_FACTS_ITERATION_CONTAINER: ForAwaitHierarchyFacts = 1 << 1;

//
// Ancestor masks
//

// PORT: Go `1<<iota - 1` at iota 2.
const FOR_AWAIT_HIERARCHY_FACTS_ANCESTOR_FACTS_MASK: ForAwaitHierarchyFacts = (1 << 2) - 1;

const FOR_AWAIT_HIERARCHY_FACTS_SOURCE_FILE_EXCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_ITERATION_CONTAINER;
const FOR_AWAIT_HIERARCHY_FACTS_STRICT_MODE_SOURCE_FILE_INCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_NONE;

const FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_HAS_LEXICAL_THIS;
const FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_ITERATION_CONTAINER;

const FOR_AWAIT_HIERARCHY_FACTS_ARROW_FUNCTION_INCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_NONE;
const FOR_AWAIT_HIERARCHY_FACTS_ARROW_FUNCTION_EXCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES;

const FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_INCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_ITERATION_CONTAINER;
const FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_EXCLUDES: ForAwaitHierarchyFacts =
    FOR_AWAIT_HIERARCHY_FACTS_NONE;

// Go: transformers/estransforms/forawait.go:43 forawaitTransformer
pub struct ForawaitTransformer {
    emit_context: Rc<EmitContext>,
    /// Go embedded `superAccessState`.
    super_access: SuperAccessState,
    #[allow(dead_code)]
    compiler_options: &'static CompilerOptions,

    enclosing_function_flags: FunctionFlags,
    for_await_hierarchy_facts: ForAwaitHierarchyFacts,
    exported_variable_statement: bool,
}

impl_es_transformer!(ForawaitTransformer);

// Go: transformers/estransforms/forawait.go:56 newforawaitTransformer
pub fn new_forawait_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    let mut tx = ForawaitTransformer {
        emit_context: opts.context.clone(),
        super_access: SuperAccessState::default(),
        compiler_options: opts.compiler_options,
        enclosing_function_flags: FunctionFlags::NORMAL,
        for_await_hierarchy_facts: FOR_AWAIT_HIERARCHY_FACTS_NONE,
        exported_variable_statement: false,
    };
    tx.super_access.init_super_access_visitor(&opts.context);
    Some(Box::new(tx))
}

/// Go `printer.AutoGenerateOptions{Flags: GeneratedIdentifierFlagsReservedInNestedScopes}`.
fn reserved_in_nested_scopes() -> AutoGenerateOptions {
    AutoGenerateOptions {
        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
        ..Default::default()
    }
}

impl ForawaitTransformer {
    fn is_async(&self) -> bool {
        self.enclosing_function_flags
            .intersects(FunctionFlags::ASYNC)
    }

    fn is_generator(&self) -> bool {
        self.enclosing_function_flags
            .intersects(FunctionFlags::GENERATOR)
    }

    // Go: transformers/estransforms/forawait.go:72 forawaitTransformer.affectsSubtree
    fn affects_subtree(
        &self,
        exclude_facts: ForAwaitHierarchyFacts,
        include_facts: ForAwaitHierarchyFacts,
    ) -> bool {
        self.for_await_hierarchy_facts
            != ((self.for_await_hierarchy_facts & !exclude_facts) | include_facts)
    }

    // Go: transformers/estransforms/forawait.go:78 forawaitTransformer.enterSubtree
    /// enterSubtree sets the HierarchyFacts for this node prior to visiting this node's subtree,
    /// returning the facts set prior to modification.
    fn enter_subtree(
        &mut self,
        exclude_facts: ForAwaitHierarchyFacts,
        include_facts: ForAwaitHierarchyFacts,
    ) -> ForAwaitHierarchyFacts {
        let ancestor_facts = self.for_await_hierarchy_facts;
        self.for_await_hierarchy_facts = ((self.for_await_hierarchy_facts & !exclude_facts)
            | include_facts)
            & FOR_AWAIT_HIERARCHY_FACTS_ANCESTOR_FACTS_MASK;
        ancestor_facts
    }

    // Go: transformers/estransforms/forawait.go:86 forawaitTransformer.exitSubtree
    /// exitSubtree restores the HierarchyFacts for this node's ancestor after visiting this node's
    /// subtree.
    fn exit_subtree(&mut self, ancestor_facts: ForAwaitHierarchyFacts) {
        self.for_await_hierarchy_facts = ancestor_facts;
    }

    /// Go `tx.noAsyncModifierVisitor` callback.
    fn no_async_modifier_visit(&mut self, node: Node) -> Node {
        if node.kind() == SyntaxKind::AsyncKeyword {
            return Node::NIL;
        }
        node
    }

    // Go: transformers/estransforms/forawait.go:90 forawaitTransformer.visitModifiersNoAsync
    fn visit_modifiers_no_async(&mut self, modifiers: ModifierList) -> ModifierList {
        self.with_visitor(Self::no_async_modifier_visit, |v| {
            v.visit_modifiers(modifiers)
        })
    }

    // Go: transformers/estransforms/forawait.go:94 forawaitTransformer.doWithHierarchyFacts
    fn do_with_hierarchy_facts(
        &mut self,
        cb: fn(&mut Self, Node) -> Node,
        node: Node,
        exclude_facts: ForAwaitHierarchyFacts,
        include_facts: ForAwaitHierarchyFacts,
    ) -> Node {
        if self.affects_subtree(exclude_facts, include_facts) {
            let ancestor_facts = self.enter_subtree(exclude_facts, include_facts);
            let result = cb(self, node);
            self.exit_subtree(ancestor_facts);
            return result;
        }
        cb(self, node)
    }

    // Go: transformers/estransforms/forawait.go:104 forawaitTransformer.visitDefault
    fn visit_default(&mut self, node: Node) -> Node {
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/forawait.go:108 forawaitTransformer.fallbackVisitor
    fn fallback_visitor(&mut self, node: Node) -> Node {
        if self.super_access.captured_super_properties.is_none() {
            return node;
        }
        match node.kind() {
            SyntaxKind::FunctionExpression
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::Constructor => return node,
            _ => {}
        }
        self.super_access.track_super_access(node);
        self.with_visitor(Self::visit_fallback, |v| v.visit_each_child(node))
    }

    // Go: transformers/estransforms/forawait.go:122 forawaitTransformer.visitFallback
    fn visit_fallback(&mut self, node: Node) -> Node {
        self.fallback_visitor(node)
    }

    // Go: transformers/estransforms/forawait.go:126 forawaitTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR)
        {
            return self.fallback_visitor(node);
        }
        self.super_access.track_super_access(node);
        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::AwaitExpression => self.visit_await_expression(node),
            SyntaxKind::YieldExpression => self.visit_yield_expression(node),
            SyntaxKind::ReturnStatement => self.visit_return_statement(node),
            SyntaxKind::LabeledStatement => self.visit_labeled_statement(node),
            SyntaxKind::DoStatement | SyntaxKind::WhileStatement | SyntaxKind::ForInStatement => {
                self.do_with_hierarchy_facts(
                    Self::visit_default,
                    node,
                    FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_EXCLUDES,
                    FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_INCLUDES,
                )
            }
            SyntaxKind::ForOfStatement => self.visit_for_of_statement(node, Node::NIL),
            SyntaxKind::ForStatement => self.do_with_hierarchy_facts(
                Self::visit_default,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_INCLUDES,
            ),
            SyntaxKind::Constructor => self.do_with_hierarchy_facts(
                Self::visit_constructor_declaration,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::MethodDeclaration => self.do_with_hierarchy_facts(
                Self::visit_method_declaration,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::GetAccessor => self.do_with_hierarchy_facts(
                Self::visit_get_accessor_declaration,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::SetAccessor => self.do_with_hierarchy_facts(
                Self::visit_set_accessor_declaration,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::FunctionDeclaration => self.do_with_hierarchy_facts(
                Self::visit_function_declaration,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::FunctionExpression => self.do_with_hierarchy_facts(
                Self::visit_function_expression,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
            ),
            SyntaxKind::ArrowFunction => self.do_with_hierarchy_facts(
                Self::visit_arrow_function,
                node,
                FOR_AWAIT_HIERARCHY_FACTS_ARROW_FUNCTION_EXCLUDES,
                FOR_AWAIT_HIERARCHY_FACTS_ARROW_FUNCTION_INCLUDES,
            ),
            SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression => self
                .do_with_hierarchy_facts(
                    Self::visit_default,
                    node,
                    FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_EXCLUDES,
                    FOR_AWAIT_HIERARCHY_FACTS_CLASS_OR_FUNCTION_INCLUDES,
                ),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/forawait.go:219 forawaitTransformer.visitAwaitExpression
    fn visit_await_expression(&mut self, node: Node) -> Node {
        if self.is_async() && self.is_generator() {
            let expression = self.visit_node(node.expression());
            let ec = self.ec();
            let f = ec.factory();
            let result = f.new_yield_expression(
                Node::NIL, /*asteriskToken*/
                f.new_await_helper(expression),
            );
            set_node_loc(result, node.loc());
            ec.set_original(result, node);
            return result;
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/forawait.go:232 forawaitTransformer.visitYieldExpression
    fn visit_yield_expression(&mut self, node: Node) -> Node {
        if self.is_async() && self.is_generator() {
            let ec = self.ec();
            let f = ec.factory();
            if node.asterisk_token().is_some() {
                let expression = self.visit_node(node.expression());

                let async_values_result = f.new_async_values_helper(expression);
                set_node_loc(async_values_result, expression.loc());

                let async_delegator_result = f.new_async_delegator_helper(async_values_result);
                set_node_loc(async_delegator_result, expression.loc());

                let inner_yield =
                    f.update_yield_expression(node, node.asterisk_token(), async_delegator_result);

                let awaited_yield = f.new_await_helper(inner_yield);

                let result =
                    f.new_yield_expression(Node::NIL /*asteriskToken*/, awaited_yield);
                set_node_loc(result, node.loc());
                ec.set_original(result, node);
                return result;
            }

            let inner_expression = if node.expression().is_some() {
                self.visit_node(node.expression())
            } else {
                f.new_void_zero_expression()
            };

            let result = f.new_yield_expression(
                Node::NIL, /*asteriskToken*/
                self.create_downlevel_await(inner_expression),
            );
            set_node_loc(result, node.loc());
            ec.set_original(result, node);
            return result;
        }

        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/forawait.go:279 forawaitTransformer.visitReturnStatement
    fn visit_return_statement(&mut self, node: Node) -> Node {
        if self.is_async() && self.is_generator() {
            let expression = if node.expression().is_some() {
                self.visit_node(node.expression())
            } else {
                self.ec().factory().new_void_zero_expression()
            };
            let awaited = self.create_downlevel_await(expression);
            return self.ec().factory().update_return_statement(node, awaited);
        }

        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/forawait.go:296 forawaitTransformer.visitLabeledStatement
    fn visit_labeled_statement(&mut self, node: Node) -> Node {
        if self.is_async() {
            let statement = unwrap_innermost_statement_of_label(node);
            if statement.kind() == SyntaxKind::ForOfStatement
                && statement.await_modifier().is_some()
            {
                return self.visit_for_of_statement(statement, node);
            }
            let visited = self.visit_node(statement);
            return self.ec().factory().restore_enclosing_label(visited, node);
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/forawait.go:317 forawaitTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        let ancestor_facts = self.enter_subtree(
            FOR_AWAIT_HIERARCHY_FACTS_SOURCE_FILE_EXCLUDES,
            FOR_AWAIT_HIERARCHY_FACTS_STRICT_MODE_SOURCE_FILE_INCLUDES,
        );
        self.exported_variable_statement = false;
        let visited = self.visit_each_child(node);
        let ec = self.ec();
        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        self.exit_subtree(ancestor_facts);
        visited
    }

    // Go: transformers/estransforms/forawait.go:330 forawaitTransformer.visitForOfStatement
    /// visitForOfStatement visits a ForOfStatement and converts it into a ES2015-compatible ForOfStatement.
    fn visit_for_of_statement(&mut self, node: Node, outermost_labeled_statement: Node) -> Node {
        let ancestor_facts = self.enter_subtree(
            FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_EXCLUDES,
            FOR_AWAIT_HIERARCHY_FACTS_ITERATION_STATEMENT_INCLUDES,
        );
        let result = if node.await_modifier().is_some() {
            self.transform_for_await_of_statement(node, outermost_labeled_statement, ancestor_facts)
        } else {
            let visited = self.visit_each_child(node);
            self.ec()
                .factory()
                .restore_enclosing_label(visited, outermost_labeled_statement)
        };
        self.exit_subtree(ancestor_facts);
        result
    }

    // Go: transformers/estransforms/forawait.go:342 forawaitTransformer.convertForOfStatementHead
    fn convert_for_of_statement_head(
        &mut self,
        node: Node,
        bound_value: Node,
        non_user_code: Node,
    ) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        let value = f.new_temp_variable();
        ec.add_variable_declaration(value);
        let iterator_value_expression = f.new_assignment_expression(value, bound_value);
        let iterator_value_statement = f.new_expression_statement(iterator_value_expression);
        ec.set_source_map_range(iterator_value_statement, node.expression().loc());

        let exit_non_user_code_expression = f.new_assignment_expression(
            non_user_code,
            f.new_keyword_expression(SyntaxKind::FalseKeyword),
        );
        let exit_non_user_code_statement =
            f.new_expression_statement(exit_non_user_code_expression);
        ec.set_source_map_range(exit_non_user_code_statement, node.expression().loc());

        let mut statements: Vec<Node> =
            vec![iterator_value_statement, exit_non_user_code_statement];
        let binding = f.create_for_of_binding_statement(node.initializer(), value);
        statements.push(self.visit_node(binding));

        let mut body_location = TextRange::default();
        let mut statements_location = TextRange::default();
        let statement = self.visit_embedded_statement(node.statement());
        if is_block(statement) {
            statements.extend(statement.statements().iter());
            body_location = statement.loc();
            statements_location = statement.statement_list().loc();
        } else {
            statements.push(statement);
        }

        let stmt_list = f.new_node_list_with_loc(&statements, statements_location);
        let block = f.new_block(stmt_list, true);
        set_node_loc(block, body_location);
        block
    }

    // Go: transformers/estransforms/forawait.go:376 forawaitTransformer.createDownlevelAwait
    fn create_downlevel_await(&self, expression: Node) -> Node {
        let f = self.emit_context.factory();
        if self.is_generator() {
            return f.new_yield_expression(
                Node::NIL, /*asteriskToken*/
                f.new_await_helper(expression),
            );
        }
        f.new_await_expression(expression)
    }

    // Go: transformers/estransforms/forawait.go:386 forawaitTransformer.transformForAwaitOfStatement
    fn transform_for_await_of_statement(
        &mut self,
        node: Node,
        outermost_labeled_statement: Node,
        ancestor_facts: ForAwaitHierarchyFacts,
    ) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        let expression = self.visit_node(node.expression());

        let iterator = if is_identifier(expression) {
            f.new_generated_name_for_node(expression)
        } else {
            f.new_temp_variable()
        };

        let result = if is_identifier(expression) {
            f.new_generated_name_for_node(iterator)
        } else {
            f.new_temp_variable()
        };

        let non_user_code = f.new_temp_variable();
        let done = f.new_temp_variable();
        ec.add_variable_declaration(done);
        let error_record = f.new_unique_name("e");
        let catch_variable = f.new_generated_name_for_node(error_record);
        let return_method = f.new_temp_variable();
        let call_values = f.new_async_values_helper(expression);
        set_node_loc(call_values, node.expression().loc());
        let call_next = f.new_call_expression(
            f.new_property_access_expression(
                iterator,
                Node::NIL,
                f.new_identifier("next"),
                NodeFlags::NONE,
            ),
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&[]),
            NodeFlags::NONE,
        );
        let get_done = f.new_property_access_expression(
            result,
            Node::NIL,
            f.new_identifier("done"),
            NodeFlags::NONE,
        );
        let get_value = f.new_property_access_expression(
            result,
            Node::NIL,
            f.new_identifier("value"),
            NodeFlags::NONE,
        );
        let call_return = f.new_function_call_call(return_method, iterator, &[]);

        ec.add_variable_declaration(error_record);
        ec.add_variable_declaration(return_method);

        // if we are enclosed in an outer loop ensure we reset 'errorRecord' per each iteration
        let initializer = if ancestor_facts & FOR_AWAIT_HIERARCHY_FACTS_ITERATION_CONTAINER != 0 {
            f.inline_expressions(&[
                f.new_assignment_expression(error_record, f.new_void_zero_expression()),
                call_values,
            ])
        } else {
            call_values
        };

        // Build the for statement
        let iterator_decl = f.new_variable_declaration(iterator, Node::NIL, Node::NIL, initializer);
        set_node_loc(iterator_decl, node.expression().loc());
        let var_decl_list = f.new_variable_declaration_list(
            f.new_node_list(&[
                f.new_variable_declaration(
                    non_user_code,
                    Node::NIL,
                    Node::NIL,
                    f.new_keyword_expression(SyntaxKind::TrueKeyword),
                ),
                iterator_decl,
                f.new_variable_declaration(result, Node::NIL, Node::NIL, Node::NIL),
            ]),
            NodeFlags::NONE,
        );
        set_node_loc(var_decl_list, node.expression().loc());

        let condition = f.inline_expressions(&[
            f.new_assignment_expression(result, self.create_downlevel_await(call_next)),
            f.new_assignment_expression(done, get_done),
            f.new_prefix_unary_expression(SyntaxKind::ExclamationToken, done),
        ]);

        let incrementor = f.new_assignment_expression(
            non_user_code,
            f.new_keyword_expression(SyntaxKind::TrueKeyword),
        );

        let head = self.convert_for_of_statement_head(node, get_value, non_user_code);
        let for_statement = f.new_for_statement(var_decl_list, condition, incrementor, head);
        set_node_loc(for_statement, node.loc());
        ec.add_emit_flags(for_statement, EmitFlags::NO_TOKEN_TRAILING_SOURCE_MAPS);
        ec.set_original(for_statement, node);

        // Build the try/catch/finally
        let try_block = f.new_block(
            f.new_node_list(&[
                f.restore_enclosing_label(for_statement, outermost_labeled_statement)
            ]),
            true,
        );

        // catch clause: { e_1 = { error: e_2 }; }
        let catch_body = f.new_block(
            f.new_node_list(&[f.new_expression_statement(f.new_assignment_expression(
                error_record,
                f.new_object_literal_expression(
                    f.new_node_list(&[f.new_property_assignment(
                        ModifierList::NIL,
                        f.new_identifier("error"),
                        Node::NIL,
                        Node::NIL,
                        catch_variable,
                    )]),
                    false,
                ),
            ))]),
            false,
        );
        ec.add_emit_flags(catch_body, EmitFlags::SINGLE_LINE);
        let catch_clause = f.new_catch_clause(
            f.new_variable_declaration(catch_variable, Node::NIL, Node::NIL, Node::NIL),
            catch_body,
        );

        // finally block
        // inner try: if (!nonUserCode && !done && (returnMethod = iterator.return)) await returnMethod.call(iterator);
        let inner_if_condition = f.new_binary_expression(
            ModifierList::NIL,
            f.new_binary_expression(
                ModifierList::NIL,
                f.new_prefix_unary_expression(SyntaxKind::ExclamationToken, non_user_code),
                Node::NIL,
                f.new_token(SyntaxKind::AmpersandAmpersandToken),
                f.new_prefix_unary_expression(SyntaxKind::ExclamationToken, done),
            ),
            Node::NIL,
            f.new_token(SyntaxKind::AmpersandAmpersandToken),
            f.new_assignment_expression(
                return_method,
                f.new_property_access_expression(
                    iterator,
                    Node::NIL,
                    f.new_identifier("return"),
                    NodeFlags::NONE,
                ),
            ),
        );
        let inner_if_statement = f.new_if_statement(
            inner_if_condition,
            f.new_expression_statement(self.create_downlevel_await(call_return)),
            Node::NIL,
        );
        ec.add_emit_flags(inner_if_statement, EmitFlags::SINGLE_LINE);

        let inner_try_block = f.new_block(f.new_node_list(&[inner_if_statement]), false);

        // inner finally: if (errorRecord) throw errorRecord.error;
        let inner_finally_if = f.new_if_statement(
            error_record,
            f.new_throw_statement(f.new_property_access_expression(
                error_record,
                Node::NIL,
                f.new_identifier("error"),
                NodeFlags::NONE,
            )),
            Node::NIL,
        );
        ec.add_emit_flags(inner_finally_if, EmitFlags::SINGLE_LINE);
        let inner_finally_block = f.new_block(f.new_node_list(&[inner_finally_if]), false);
        ec.add_emit_flags(inner_finally_block, EmitFlags::SINGLE_LINE);

        let inner_try_statement =
            f.new_try_statement(inner_try_block, Node::NIL, inner_finally_block);
        let finally_block = f.new_block(f.new_node_list(&[inner_try_statement]), true);

        f.new_try_statement(try_block, catch_clause, finally_block)
    }

    // Go: transformers/estransforms/forawait.go:531 forawaitTransformer.visitConstructorDeclaration
    fn visit_constructor_declaration(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.visit_function_body(node.body());
        let updated = self.ec().factory().update_constructor_declaration(
            node,
            node.modifiers(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:548 forawaitTransformer.visitGetAccessorDeclaration
    fn visit_get_accessor_declaration(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.visit_function_body(node.body());
        let updated = self.ec().factory().update_get_accessor_declaration(
            node,
            node.modifiers(),
            name,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:566 forawaitTransformer.visitSetAccessorDeclaration
    fn visit_set_accessor_declaration(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.visit_function_body(node.body());
        let updated = self.ec().factory().update_set_accessor_declaration(
            node,
            node.modifiers(),
            name,
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    /// The shared head of Go `visitMethodDeclaration`, `visitFunctionDeclaration` and
    /// `visitFunctionExpression`: `(modifiers, asteriskToken, parameters, body)`.
    fn transform_function_like_parts(
        &mut self,
        node: Node,
    ) -> (ModifierList, Node, NodeList, Node) {
        let modifiers = if self.is_generator() {
            self.visit_modifiers_no_async(node.modifiers())
        } else {
            node.modifiers()
        };

        let asterisk_token = if self.is_async() {
            Node::NIL
        } else {
            node.asterisk_token()
        };

        let parameters;
        let body;
        if self.is_async() && self.is_generator() {
            parameters = self.transform_async_generator_function_parameter_list(node);
            body = self.transform_async_generator_function_body(node);
        } else {
            parameters = self.visit_parameters(node.parameter_list());
            body = self.visit_function_body(node.body());
        }
        (modifiers, asterisk_token, parameters, body)
    }

    // Go: transformers/estransforms/forawait.go:584 forawaitTransformer.visitMethodDeclaration
    fn visit_method_declaration(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);

        let (modifiers, asterisk_token, parameters, body) =
            self.transform_function_like_parts(node);

        let name = self.visit_node(node.name());
        let updated = self.ec().factory().update_method_declaration(
            node,
            modifiers,
            asterisk_token,
            name,
            Node::NIL,     /*postfixToken*/
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:629 forawaitTransformer.visitFunctionDeclaration
    fn visit_function_declaration(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);

        let (modifiers, asterisk_token, parameters, body) =
            self.transform_function_like_parts(node);

        let updated = self.ec().factory().update_function_declaration(
            node,
            modifiers,
            asterisk_token,
            node.name(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:673 forawaitTransformer.visitArrowFunction
    fn visit_arrow_function(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);
        let parameters = self.visit_parameters(node.parameter_list());
        let body = self.visit_function_body(node.body());
        let updated = self.ec().factory().update_arrow_function(
            node,
            node.modifiers(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            node.equals_greater_than_token(),
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:691 forawaitTransformer.visitFunctionExpression
    fn visit_function_expression(&mut self, node: Node) -> Node {
        let saved_enclosing_function_flags = self.enclosing_function_flags;
        self.enclosing_function_flags = get_function_flags(node);

        let (modifiers, asterisk_token, parameters, body) =
            self.transform_function_like_parts(node);

        let updated = self.ec().factory().update_function_expression(
            node,
            modifiers,
            asterisk_token,
            node.name(),
            NodeList::NIL, /*typeParameters*/
            parameters,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            body,
        );
        self.enclosing_function_flags = saved_enclosing_function_flags;
        updated
    }

    // Go: transformers/estransforms/forawait.go:735 forawaitTransformer.transformAsyncGeneratorFunctionParameterList
    fn transform_async_generator_function_parameter_list(&mut self, node: Node) -> NodeList {
        if is_simple_parameter_list(&node.parameters().to_vec()) {
            return self.visit_parameters(node.parameter_list());
        }
        // Add fixed parameters to preserve the function's `length` property.
        let f = self.emit_context.factory();
        let mut new_parameters: Vec<Node> = Vec::new();
        for param in node.parameters().iter() {
            if param.initializer().is_some() || param.dot_dot_dot_token().is_some() {
                break;
            }
            let new_parameter = f.new_parameter_declaration(
                ModifierList::NIL,
                Node::NIL,
                f.new_generated_name_for_node_ex(param.name(), reserved_in_nested_scopes()),
                Node::NIL,
                Node::NIL,
                Node::NIL,
            );
            new_parameters.push(new_parameter);
        }
        f.new_node_list_with_loc(&new_parameters, node.parameter_list().loc())
    }

    // Go: transformers/estransforms/forawait.go:761 forawaitTransformer.transformAsyncGeneratorFunctionBody
    fn transform_async_generator_function_body(&mut self, node: Node) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        let mut inner_parameters = NodeList::NIL;
        if !is_simple_parameter_list(&node.parameters().to_vec()) {
            inner_parameters = self.visit_parameters(node.parameter_list());
        }

        let saved_captured_super_properties = self.super_access.captured_super_properties.take();
        let saved_has_super_element_access = self.super_access.has_super_element_access;
        let saved_has_super_property_assignment = self.super_access.has_super_property_assignment;
        let saved_super_binding = self.super_access.super_binding;
        let saved_super_index_binding = self.super_access.super_index_binding;
        let optimistic_file_level = || AutoGenerateOptions {
            flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
            ..Default::default()
        };
        self.super_access.captured_super_properties = Some(IndexSet::new());
        self.super_access.has_super_element_access = false;
        self.super_access.has_super_property_assignment = false;
        self.super_access.super_binding = f.new_unique_name_ex("_super", optimistic_file_level());
        self.super_access.super_index_binding =
            f.new_unique_name_ex("_superIndex", optimistic_file_level());

        let body = node.body();
        let statements = self.visit_nodes(body.statement_list());
        let mut async_body = f.update_block(body, statements, body.multi_line());
        async_body = f.update_block(
            async_body,
            ec.end_and_merge_variable_environment_list(async_body.statement_list()),
            async_body.multi_line(),
        );

        // Substitute super property accesses with _super/_superIndex helpers
        let captured_len = self
            .super_access
            .captured_super_properties
            .as_ref()
            .map_or(0, IndexSet::len);
        let emit_super_helpers = captured_len > 0 || self.super_access.has_super_element_access;
        if emit_super_helpers {
            async_body = self
                .super_access
                .substitute_super_accesses_in_body(async_body);
        }

        let inner_params = if inner_parameters.is_some() {
            inner_parameters
        } else {
            f.new_node_list(&[])
        };

        let name = if node.name().is_some() {
            f.new_generated_name_for_node(node.name())
        } else {
            Node::NIL
        };

        let generator_func = f.new_function_expression(
            ModifierList::NIL, /*modifiers*/
            f.new_token(SyntaxKind::AsteriskToken),
            name,
            NodeList::NIL, /*typeParameters*/
            inner_params,
            Node::NIL, /*returnType*/
            Node::NIL, /*fullSignature*/
            async_body,
        );

        let return_statement = f.new_return_statement(f.new_async_generator_helper(
            generator_func,
            self.for_await_hierarchy_facts & FOR_AWAIT_HIERARCHY_FACTS_HAS_LEXICAL_THIS != 0,
        ));

        ec.start_variable_environment();
        if emit_super_helpers && captured_len > 0 {
            ec.add_initialization_statement(
                self.super_access.create_super_access_variable_statement(),
            );
        }

        let outer_statements = [return_statement];

        let block = f.update_block(
            body,
            ec.end_and_merge_variable_environment_list(f.new_node_list(&outer_statements)),
            body.multi_line(),
        );

        if emit_super_helpers && self.super_access.has_super_element_access {
            if self.super_access.has_super_property_assignment {
                ec.add_emit_helper(block, &[&ADVANCED_ASYNC_SUPER_HELPER]);
            } else {
                ec.add_emit_helper(block, &[&ASYNC_SUPER_HELPER]);
            }
        }

        self.super_access.captured_super_properties = saved_captured_super_properties;
        self.super_access.has_super_element_access = saved_has_super_element_access;
        self.super_access.has_super_property_assignment = saved_has_super_property_assignment;
        self.super_access.super_binding = saved_super_binding;
        self.super_access.super_index_binding = saved_super_index_binding;

        block
    }
}

// Go: transformers/estransforms/forawait.go:308 unwrapInnermostStatementOfLabel
/// unwrapInnermostStatementOfLabel follows LabeledStatement chains to find the innermost statement.
fn unwrap_innermost_statement_of_label(mut node: Node) -> Node {
    loop {
        if node.statement().kind() != SyntaxKind::LabeledStatement {
            return node.statement();
        }
        node = node.statement();
    }
}
