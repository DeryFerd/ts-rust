//! Port of Go `transformers/estransforms/objectrestspread.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, impl_es_transformer};
use crate::ast::visitor::syntax_list_children;
use crate::prelude::*;
use crate::printer::{EmitContext, EmitFlags};
use crate::transformers::destructuring::{
    FlattenLevel, flatten_destructuring_assignment, flatten_destructuring_binding,
};

// Go: transformers/estransforms/objectrestspread.go:10 objectRestSpreadTransformer
pub struct ObjectRestSpreadTransformer {
    emit_context: Rc<EmitContext>,
    compiler_options: &'static CompilerOptions,

    in_exported_variable_statement: bool,
    expression_result_is_unused: bool,

    /// Go `map[*ast.Node]struct{}`; `None` is the nil map.
    parameters_with_preceding_object_rest_or_spread: Option<FxHashSet<Node>>,
}

impl_es_transformer!(ObjectRestSpreadTransformer);

/// Go `oldParamScope`.
type OldParamScope = Option<FxHashSet<Node>>;

impl ObjectRestSpreadTransformer {
    // Go: transformers/estransforms/objectrestspread.go:19 objectRestSpreadTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_ES_OBJECT_REST_OR_SPREAD)
            && self
                .parameters_with_preceding_object_rest_or_spread
                .is_none()
        {
            return node;
        }
        // Save the expressionResultIsUnused flag set by the parent for this node,
        // then reset to false for children (the default). Specific cases below override as needed.
        let expression_result_is_unused = self.expression_result_is_unused;
        self.expression_result_is_unused = false;
        let result = self.visit_worker(node, expression_result_is_unused);
        self.expression_result_is_unused = expression_result_is_unused;
        result
    }

    /// The body of Go `visit` after the deferred restore is registered.
    fn visit_worker(&mut self, node: Node, expression_result_is_unused: bool) -> Node {
        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::ObjectLiteralExpression => self.visit_object_literal_expression(node),
            SyntaxKind::BinaryExpression => {
                self.visit_binary_expression(node, expression_result_is_unused)
            }
            SyntaxKind::ExpressionStatement => {
                self.expression_result_is_unused = true;
                self.visit_each_child(node)
            }
            SyntaxKind::ParenthesizedExpression => {
                self.expression_result_is_unused = expression_result_is_unused;
                self.visit_each_child(node)
            }
            SyntaxKind::ForOfStatement => self.visit_for_oftatement(node),
            SyntaxKind::VariableStatement => self.visit_variable_statement(node),
            SyntaxKind::VariableDeclaration => self.visit_variable_declaration(node),
            SyntaxKind::CatchClause => self.visit_catch_clause(node),
            SyntaxKind::Parameter => self.visit_parameter(node),
            SyntaxKind::Constructor => self.visit_contructor_declaration(node),
            SyntaxKind::GetAccessor => self.visit_get_accessor_declaration(node),
            SyntaxKind::SetAccessor => self.visit_set_accessor_declaration(node),
            SyntaxKind::MethodDeclaration => self.visit_method_declaration(node),
            SyntaxKind::FunctionDeclaration => self.visit_function_declaration(node),
            SyntaxKind::ArrowFunction => self.visit_arrow_function(node),
            SyntaxKind::FunctionExpression => self.visit_function_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/objectrestspread.go:69 objectRestSpreadTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        let visited = self.visit_each_child(node);
        let ec = self.ec();
        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        visited
    }

    // Go: transformers/estransforms/objectrestspread.go:75 objectRestSpreadTransformer.visitParameter
    fn visit_parameter(&mut self, node: Node) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        if let Some(params) = &self.parameters_with_preceding_object_rest_or_spread
            && params.contains(&node)
        {
            let mut name = node.name();
            if is_binding_pattern(name) {
                name = f.new_generated_name_for_node(node);
            }
            return f.update_parameter_declaration(
                node,
                ModifierList::NIL,
                node.dot_dot_dot_token(),
                name,
                Node::NIL,
                Node::NIL,
                Node::NIL,
            );
        }
        if node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
        {
            // Binding patterns are converted into a generated name and are
            // evaluated inside the function body.
            let name = f.new_generated_name_for_node(node);
            let initializer = self.visit_node(node.initializer());
            return f.update_parameter_declaration(
                node,
                ModifierList::NIL,
                node.dot_dot_dot_token(),
                name,
                Node::NIL,
                Node::NIL,
                initializer,
            );
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:109 objectRestSpreadTransformer.collectParametersWithPrecedingObjectRestOrSpread
    fn collect_parameters_with_preceding_object_rest_or_spread(
        &self,
        node: Node,
    ) -> Option<FxHashSet<Node>> {
        let mut result: Option<FxHashSet<Node>> = None;
        for parameter in node.parameters().iter() {
            if let Some(result) = result.as_mut() {
                result.insert(parameter);
            } else if parameter
                .subtree_facts()
                .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
            {
                result = Some(FxHashSet::default());
            }
        }
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:123 objectRestSpreadTransformer.enterParameterListContext
    fn enter_parameter_list_context(&mut self, node: Node) -> OldParamScope {
        let old = self.parameters_with_preceding_object_rest_or_spread.take();
        self.parameters_with_preceding_object_rest_or_spread =
            self.collect_parameters_with_preceding_object_rest_or_spread(node);
        old
    }

    // Go: transformers/estransforms/objectrestspread.go:129 objectRestSpreadTransformer.exitParameterListContext
    fn exit_parameter_list_context(&mut self, scope: OldParamScope) {
        self.parameters_with_preceding_object_rest_or_spread = scope;
    }

    // Go: transformers/estransforms/objectrestspread.go:133 objectRestSpreadTransformer.visitContructorDeclaration
    fn visit_contructor_declaration(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_constructor_declaration(
            node,
            node.modifiers(),
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:147 objectRestSpreadTransformer.visitGetAccessorDeclaration
    fn visit_get_accessor_declaration(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_get_accessor_declaration(
            node,
            node.modifiers(),
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:162 objectRestSpreadTransformer.visitSetAccessorDeclaration
    fn visit_set_accessor_declaration(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_set_accessor_declaration(
            node,
            node.modifiers(),
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:177 objectRestSpreadTransformer.visitMethodDeclaration
    fn visit_method_declaration(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_method_declaration(
            node,
            node.modifiers(),
            node.asterisk_token(),
            name,
            node.postfix_token(),
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:194 objectRestSpreadTransformer.visitFunctionDeclaration
    fn visit_function_declaration(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_function_declaration(
            node,
            node.modifiers(),
            node.asterisk_token(),
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:210 objectRestSpreadTransformer.visitArrowFunction
    fn visit_arrow_function(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_arrow_function(
            node,
            node.modifiers(),
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            node.equals_greater_than_token(),
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:225 objectRestSpreadTransformer.visitFunctionExpression
    fn visit_function_expression(&mut self, node: Node) -> Node {
        let old = self.enter_parameter_list_context(node);
        let name = self.visit_node(node.name());
        let parameters = self.visit_nodes(node.parameter_list());
        let body = self.transform_function_body(node);
        let result = self.ec().factory().update_function_expression(
            node,
            node.modifiers(),
            node.asterisk_token(),
            name,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            body,
        );
        self.exit_parameter_list_context(old);
        result
    }

    // Go: transformers/estransforms/objectrestspread.go:241 objectRestSpreadTransformer.transformFunctionBody
    fn transform_function_body(&mut self, node: Node) -> Node {
        let ec = self.ec();
        let f = ec.factory();
        // EmitContext().VisitFunctionBody is not used here because this transformer needs to inject
        // object rest assignments between visiting the body and merging the variable environment.
        ec.start_variable_environment();
        let mut body = self.visit_node(node.body());
        let extras = ec.end_variable_environment();
        ec.start_variable_environment();
        let new_statements = self.collect_object_rest_assignments(node);
        let extras = ec.end_and_merge_variable_environment(&extras);
        if new_statements.is_empty() && extras.is_empty() {
            return body;
        }

        if body.is_nil() {
            body = f.new_block(f.new_node_list(&[]), true);
        }
        let mut prefix: Vec<Node> = Vec::new();
        let mut suffix: Vec<Node> = Vec::new();
        if is_block(body) {
            let mut custom = false;
            let body_statements = body.statements().to_vec();
            for (i, &statement) in body_statements.iter().enumerate() {
                if !custom && is_prologue_directive(statement) {
                    prefix.push(statement);
                } else if ec
                    .emit_flags(statement)
                    .intersects(EmitFlags::CUSTOM_PROLOGUE)
                {
                    custom = true;
                    prefix.push(statement);
                } else {
                    suffix = body_statements[i..].to_vec();
                    break;
                }
            }
        } else {
            let ret = f.new_return_statement(body);
            set_node_loc(ret, body.loc());
            let list = f.new_node_list_with_loc(&[], body.loc());
            body = f.new_block(list, true);
            suffix.push(ret);
        }

        let mut all: Vec<Node> = prefix;
        all.extend(extras);
        all.extend(new_statements);
        all.extend(suffix);
        let new_statement_list = f.new_node_list_with_loc(&all, body.statement_list().loc());
        f.update_block(body, new_statement_list, body.multi_line())
    }

    /// Go `transformers.FlattenDestructuringBinding(&ch.Transformer, ...)`.
    fn flatten_binding(
        &mut self,
        node: Node,
        rval: Node,
        level: FlattenLevel,
        hoist_temp_variables: bool,
        skip_initializer: bool,
    ) -> Node {
        let ec = self.ec();
        self.with_visitor(Self::root_visit, |v| {
            flatten_destructuring_binding(
                &ec,
                v,
                node,
                rval,
                level,
                hoist_temp_variables,
                skip_initializer,
            )
        })
    }

    /// Go: a `var` statement for the flattened `declarations` with `EFCustomPrologue`.
    // PORT: Go makes an empty list, then appends to its `Nodes`. A synthetic
    // list is fixed at creation, so the list is made with the declarations.
    fn new_custom_prologue_var_statement(&self, declarations: Node) -> Node {
        let ec = &self.emit_context;
        let f = ec.factory();
        let decls = if declarations.kind() == SyntaxKind::SyntaxList {
            syntax_list_children(declarations)
        } else {
            vec![declarations]
        };
        let declaration_list =
            f.new_variable_declaration_list(f.new_node_list(&decls), NodeFlags::NONE);
        let statement = f.new_variable_statement(ModifierList::NIL, declaration_list);
        ec.add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
        statement
    }

    // Go: transformers/estransforms/objectrestspread.go:284 objectRestSpreadTransformer.collectObjectRestAssignments
    fn collect_object_rest_assignments(&mut self, node: Node) -> Vec<Node> {
        let ec = self.ec();
        let f = ec.factory();
        let mut contains_preceding_object_rest_or_spread = false;
        let mut results: Vec<Node> = Vec::new();
        for parameter in node.parameters().iter() {
            if contains_preceding_object_rest_or_spread {
                if is_binding_pattern(parameter.name()) {
                    // In cases where a binding pattern is simply '[]' or '{}',
                    // we usually don't want to emit a var declaration; however, in the presence
                    // of an initializer, we must emit that expression to preserve side effects.
                    if !parameter.name().elements().is_empty() {
                        let declarations = self.flatten_binding(
                            parameter,
                            f.new_generated_name_for_node(parameter),
                            FlattenLevel::All,
                            false,
                            false,
                        );
                        if declarations.is_some() {
                            results.push(self.new_custom_prologue_var_statement(declarations));
                        }
                    } else if parameter.initializer().is_some() {
                        let name = f.new_generated_name_for_node(parameter);
                        let initializer = self.visit_node(parameter.initializer());
                        let assignment = f.new_assignment_expression(name, initializer);
                        let statement = f.new_expression_statement(assignment);
                        ec.add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
                        results.push(statement);
                    }
                } else if parameter.initializer().is_some() {
                    // Converts a parameter initializer into a function body statement, i.e.:
                    //
                    //  function f(x = 1) { }
                    //
                    // becomes
                    //
                    //  function f(x) {
                    //    if (typeof x === "undefined") { x = 1; }
                    //  }
                    let name = f.clone_node(parameter.name());
                    set_node_loc(name, parameter.name().loc());
                    ec.add_emit_flags(name, EmitFlags::NO_SOURCE_MAP);

                    let initializer = self.visit_node(parameter.initializer());
                    ec.add_emit_flags(
                        initializer,
                        EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS,
                    );

                    let assignment = f.new_assignment_expression(name, initializer);
                    set_node_loc(assignment, parameter.loc());
                    ec.add_emit_flags(assignment, EmitFlags::NO_COMMENTS);

                    let block = f.new_block(
                        f.new_node_list(&[f.new_expression_statement(assignment)]),
                        false,
                    );
                    set_node_loc(block, parameter.loc());
                    ec.add_emit_flags(
                        block,
                        EmitFlags::SINGLE_LINE
                            | EmitFlags::NO_TRAILING_SOURCE_MAP
                            | EmitFlags::NO_TOKEN_SOURCE_MAPS
                            | EmitFlags::NO_COMMENTS,
                    );

                    let type_check = f.new_type_check(f.clone_node(name), "undefined");
                    let statement = f.new_if_statement(type_check, block, Node::NIL);
                    set_node_loc(statement, parameter.loc());
                    ec.add_emit_flags(
                        statement,
                        EmitFlags::NO_TOKEN_SOURCE_MAPS
                            | EmitFlags::NO_TRAILING_SOURCE_MAP
                            | EmitFlags::CUSTOM_PROLOGUE
                            | EmitFlags::NO_COMMENTS
                            | EmitFlags::START_ON_NEW_LINE,
                    );
                    results.push(statement);
                }
            } else if parameter
                .subtree_facts()
                .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
            {
                contains_preceding_object_rest_or_spread = true;
                let declarations = self.flatten_binding(
                    parameter,
                    f.new_generated_name_for_node(parameter),
                    FlattenLevel::ObjectRest,
                    false,
                    true,
                );
                if declarations.is_some() {
                    results.push(self.new_custom_prologue_var_statement(declarations));
                }
            }
        }

        results
    }

    // Go: transformers/estransforms/objectrestspread.go:376 objectRestSpreadTransformer.visitCatchClause
    fn visit_catch_clause(&mut self, node: Node) -> Node {
        let variable_declaration = node.variable_declaration();
        if variable_declaration.is_some()
            && is_binding_pattern(variable_declaration.name())
            && variable_declaration
                .name()
                .subtree_facts()
                .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
        {
            let ec = self.ec();
            let f = ec.factory();
            let name = f.new_generated_name_for_node(variable_declaration.name());
            let updated_decl = f.update_variable_declaration(
                variable_declaration,
                variable_declaration.name(),
                Node::NIL,
                Node::NIL,
                name,
            );
            let visited_bindings = self.flatten_binding(
                updated_decl,
                Node::NIL,
                FlattenLevel::ObjectRest,
                false,
                false,
            );
            let mut block = self.visit_node(node.block());
            if visited_bindings.is_some() {
                let decls = if visited_bindings.kind() == SyntaxKind::SyntaxList {
                    syntax_list_children(visited_bindings)
                } else {
                    vec![visited_bindings]
                };
                let new_statement = f.new_variable_statement(
                    ModifierList::NIL,
                    f.new_variable_declaration_list(f.new_node_list(&decls), NodeFlags::NONE),
                );
                let mut statements: Vec<Node> = vec![new_statement];
                statements.extend(block.statements().iter());
                let statement_list =
                    f.new_node_list_with_loc(&statements, block.statement_list().loc());

                block = f.update_block(block, statement_list, block.multi_line());
            }
            return f.update_catch_clause(
                node,
                f.update_variable_declaration(
                    variable_declaration,
                    name,
                    Node::NIL,
                    Node::NIL,
                    Node::NIL,
                ),
                block,
            );
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:410 objectRestSpreadTransformer.visitVariableStatement
    fn visit_variable_statement(&mut self, node: Node) -> Node {
        if has_syntactic_modifier(node, ModifierFlags::EXPORT) {
            let old_in_exported_variable_statement = self.in_exported_variable_statement;
            self.in_exported_variable_statement = true;
            let result = self.visit_each_child(node);
            self.in_exported_variable_statement = old_in_exported_variable_statement;
            return result;
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:421 objectRestSpreadTransformer.visitVariableDeclaration
    fn visit_variable_declaration(&mut self, node: Node) -> Node {
        if self.in_exported_variable_statement {
            self.in_exported_variable_statement = false;
            let result = self.visit_variable_declaration_worker(node, true);
            self.in_exported_variable_statement = true;
            return result;
        }
        self.visit_variable_declaration_worker(node, false)
    }

    // Go: transformers/estransforms/objectrestspread.go:431 objectRestSpreadTransformer.visitVariableDeclarationWorker
    fn visit_variable_declaration_worker(&mut self, node: Node, exported: bool) -> Node {
        // If we are here it is because the name contains a binding pattern with a rest somewhere in it.
        if is_binding_pattern(node.name())
            && node
                .subtree_facts()
                .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
        {
            return self.flatten_binding(
                node,
                Node::NIL,
                FlattenLevel::ObjectRest,
                exported,
                false,
            );
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:443 objectRestSpreadTransformer.visitForOftatement
    fn visit_for_oftatement(&mut self, node: Node) -> Node {
        let initializer = node.initializer();
        if initializer
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
            || (is_assignment_pattern(initializer) && contains_object_rest_or_spread(initializer))
        {
            let initializer_without_parens = skip_parentheses(initializer);
            if is_variable_declaration_list(initializer_without_parens)
                || is_assignment_pattern(initializer_without_parens)
            {
                let ec = self.ec();
                let f = ec.factory();
                let mut body_location = TextRange::default();
                let mut statements_location = TextRange::default();
                let temp = f.new_temp_variable();
                let binding = f.create_for_of_binding_statement(initializer_without_parens, temp);
                let res = self.visit_node(binding);
                let mut statements: Vec<Node> = Vec::with_capacity(1);
                if res.is_some() {
                    statements.push(res);
                }
                let statement = node.statement();
                if is_block(statement) {
                    for s in statement.statements().iter() {
                        let visited = self.visit_each_child(s);
                        if visited.is_some() {
                            statements.push(visited);
                        }
                    }
                    body_location = statement.loc();
                    statements_location = statement.statement_list().loc();
                } else if statement.is_some() {
                    statements.push(self.visit_each_child(statement));
                    body_location = statement.loc();
                    statements_location = statement.loc();
                }

                let list = f.new_variable_declaration_list(
                    f.new_node_list(&[f.new_variable_declaration(
                        temp,
                        Node::NIL,
                        Node::NIL,
                        Node::NIL,
                    )]),
                    NodeFlags::LET,
                );
                set_node_loc(list, initializer.loc());

                let expr = self.visit_each_child(node.expression());

                let statements_list = f.new_node_list_with_loc(&statements, statements_location);

                let block = f.new_block(statements_list, true);
                set_node_loc(block, body_location);

                return f.update_for_in_or_of_statement(
                    node,
                    node.await_modifier(),
                    list,
                    expr,
                    block,
                );
            }
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:500 objectRestSpreadTransformer.visitBinaryExpression
    fn visit_binary_expression(&mut self, node: Node, expression_result_is_unused: bool) -> Node {
        if is_destructuring_assignment(node) && contains_object_rest_or_spread(node.left()) {
            let ec = self.ec();
            return self.with_visitor(Self::root_visit, |v| {
                flatten_destructuring_assignment(
                    &ec,
                    v,
                    node,
                    !expression_result_is_unused,
                    FlattenLevel::ObjectRest,
                    None,
                )
            });
        }
        if node.operator_token().kind() == SyntaxKind::CommaToken {
            self.expression_result_is_unused = true;
            let left = self.visit_node(node.left());
            self.expression_result_is_unused = expression_result_is_unused;
            let right = self.visit_node(node.right());
            return self.ec().factory().update_binary_expression(
                node,
                ModifierList::NIL,
                left,
                Node::NIL,
                node.operator_token(),
                right,
            );
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/objectrestspread.go:518 objectRestSpreadTransformer.visitObjectLiteralExpression
    fn visit_object_literal_expression(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD)
        {
            return self.visit_each_child(node);
        }
        // spread elements emit like so:
        // non-spread elements are chunked together into object literals, and then all are passed to __assign:
        //     { a, ...o, b } => __assign(__assign({a}, o), {b});
        // If the first element is a spread element, then the first argument to __assign is {}:
        //     { ...o, a, b, ...o2 } => __assign(__assign(__assign({}, o), {a, b}), o2)
        //
        // We cannot call __assign with more than two elements, since any element could cause side effects. For
        // example:
        //      var k = { a: 1, b: 2 };
        //      var o = { a: 3, ...k, b: k.a++ };
        //      // expected: { a: 1, b: 1 }
        // If we translate the above to `__assign({ a: 3 }, k, { b: k.a++ })`, the `k.a++` will evaluate before
        // `k` is spread and we end up with `{ a: 2, b: 1 }`.
        //
        // This also occurs for spread elements, not just property assignments:
        //      var k = { a: 1, get b() { l = { z: 9 }; return 2; } };
        //      var l = { c: 3 };
        //      var o = { ...k, ...l };
        //      // expected: { a: 1, b: 2, z: 9 }
        // If we translate the above to `__assign({}, k, l)`, the `l` will evaluate before `k` is spread and we
        // end up with `{ a: 1, b: 2, c: 3 }`

        let ec = self.ec();
        let f = ec.factory();
        let mut objects = self.chunk_object_literal_elements(node.property_list());
        if !objects.is_empty() && objects[0].kind() != SyntaxKind::ObjectLiteralExpression {
            objects.insert(
                0,
                f.new_object_literal_expression(f.new_node_list(&[]), false),
            );
        }
        let target = self.compiler_options.get_emit_script_target();
        let mut expression = objects[0];
        if objects.len() > 1 {
            for &obj in &objects[1..] {
                expression = f.new_assign_helper(&[expression, obj], target);
            }
            return expression;
        }
        f.new_assign_helper(&objects, target)
    }

    // Go: transformers/estransforms/objectrestspread.go:559 objectRestSpreadTransformer.chunkObjectLiteralElements
    fn chunk_object_literal_elements(&mut self, list: NodeList) -> Vec<Node> {
        if list.is_nil() || list.nodes().is_empty() {
            return Vec::new();
        }
        let ec = self.ec();
        let f = ec.factory();
        let elements = list.nodes().to_vec();
        let mut chunk_object: Vec<Node> = Vec::new();
        let mut objects: Vec<Node> = Vec::with_capacity(1);
        for e in elements {
            if e.kind() == SyntaxKind::SpreadAssignment {
                if !chunk_object.is_empty() {
                    objects.push(
                        f.new_object_literal_expression(f.new_node_list(&chunk_object), false),
                    );
                    chunk_object = Vec::new();
                }
                let target = e.expression();
                objects.push(self.visit_node(target));
            } else {
                let elem = if e.kind() == SyntaxKind::PropertyAssignment {
                    let initializer = self.visit_node(e.initializer());
                    f.new_property_assignment(
                        ModifierList::NIL,
                        e.name(),
                        Node::NIL,
                        Node::NIL,
                        initializer,
                    )
                } else {
                    self.visit_node(e)
                };
                chunk_object.push(elem);
            }
        }
        if !chunk_object.is_empty() {
            objects.push(f.new_object_literal_expression(f.new_node_list(&chunk_object), false));
        }
        objects
    }
}

// Go: transformers/estransforms/objectrestspread.go:590 newObjectRestSpreadTransformer
pub fn new_object_rest_spread_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(ObjectRestSpreadTransformer {
        emit_context: opts.context.clone(),
        compiler_options: opts.compiler_options,
        in_exported_variable_statement: false,
        expression_result_is_unused: false,
        parameters_with_preceding_object_rest_or_spread: None,
    }))
}
