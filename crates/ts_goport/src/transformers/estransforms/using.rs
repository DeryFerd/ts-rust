//! Port of Go `transformers/estransforms/using.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::named_evaluation::{is_named_evaluation, transform_named_evaluation};
use super::utilities::{
    TxVisitors, convert_class_declaration_to_class_expression, impl_es_transformer,
    source_file_is_declaration_file,
};
use crate::ast::visitor::syntax_list_children;
use crate::prelude::*;
use crate::printer::{AutoGenerateOptions, EmitContext, EmitFlags, GeneratedIdentifierFlags};
use crate::transformers::utilities::{
    convert_binding_pattern_to_assignment_pattern, is_generated_identifier, is_local_name,
};

// Go: transformers/estransforms/using.go:11 usingDeclarationTransformer
pub struct UsingDeclarationTransformer {
    emit_context: Rc<EmitContext>,

    /// Go `map[string]*ast.ExportSpecifierNode`; `None` is the nil map.
    export_bindings: Option<FxHashMap<String, Node>>,
    export_binding_names: Vec<String>,
    export_vars: Vec<Node>,
    default_export_binding: Node,
    export_equals_binding: Node,
}

impl_es_transformer!(UsingDeclarationTransformer);

// Go: transformers/estransforms/using.go:21 newUsingDeclarationTransformer
pub fn new_using_declaration_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(UsingDeclarationTransformer {
        emit_context: opts.context.clone(),
        export_bindings: None,
        export_binding_names: Vec::new(),
        export_vars: Vec::new(),
        default_export_binding: Node::NIL,
        export_equals_binding: Node::NIL,
    }))
}

// Go: transformers/estransforms/using.go:26 usingKind
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum UsingKind {
    None,
    Sync,
    Async,
}

/// Go `printer.AutoGenerateOptions{Flags: ReservedInNestedScopes | FileLevel | Optimistic}`.
fn default_export_binding_options() -> AutoGenerateOptions {
    AutoGenerateOptions {
        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES
            | GeneratedIdentifierFlags::FILE_LEVEL
            | GeneratedIdentifierFlags::OPTIMISTIC,
        ..Default::default()
    }
}

impl UsingDeclarationTransformer {
    // Go: transformers/estransforms/using.go:34 usingDeclarationTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_USING)
        {
            return node;
        }

        match node.kind() {
            SyntaxKind::SourceFile => self.visit_source_file(node),
            SyntaxKind::Block => self.visit_block(node),
            SyntaxKind::ForStatement => self.visit_for_statement(node),
            SyntaxKind::ForOfStatement => self.visit_for_of_statement(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/using.go:54 usingDeclarationTransformer.visitSourceFile
    fn visit_source_file(&mut self, node: Node) -> Node {
        if source_file_is_declaration_file(node) {
            return node;
        }

        let ec = self.ec();
        let f = ec.factory();
        let visited;
        let node_statements = node.statements().to_vec();
        let using_kind = get_using_kind_of_statements(&node_statements);
        if using_kind != UsingKind::None {
            // Imports and exports must stay at the top level. This means we must hoist all imports, exports, and
            // top-level function declarations and bindings out of the `try` statements we generate. For example:
            //
            // given:
            //
            //  import { w } from "mod";
            //  const x = expr1;
            //  using y = expr2;
            //  const z = expr3;
            //  export function f() {
            //    console.log(z);
            //  }
            //
            // produces:
            //
            //  import { x } from "mod";        // <-- preserved
            //  const x = expr1;                // <-- preserved
            //  var y, z;                       // <-- hoisted
            //  export function f() {           // <-- hoisted
            //    console.log(z);
            //  }
            //  const env_1 = { stack: [], error: void 0, hasError: false };
            //  try {
            //    y = __addDisposableResource(env_1, expr2, false);
            //    z = expr3;
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResource(env_1);
            //  }
            //
            // In this transformation, we hoist `y`, `z`, and `f` to a new outer statement list while moving all other
            // statements in the source file into the `try` block, which is the same approach we use for System module
            // emit. Unlike System module emit, we attempt to preserve all statements prior to the first top-level
            // `using` to isolate the complexity of the transformed output to only where it is necessary.
            ec.start_variable_environment();

            self.export_bindings = Some(FxHashMap::default());
            self.export_vars = Vec::new();

            let (prologue, rest) = f.split_standard_prologue(&node_statements);
            let mut top_level_statements: Vec<Node> = Vec::new();
            top_level_statements.extend(self.visit_slice(prologue).0);

            // Collect and transform any leading statements up to the first `using` or `await using`. This preserves
            // the original statement order much as is possible.

            let mut pos = 0;
            while pos < rest.len() {
                let statement = rest[pos];
                if get_using_kind(statement) != UsingKind::None {
                    if pos > 0 {
                        top_level_statements.extend(self.visit_slice(&rest[..pos]).0);
                    }
                    break;
                }
                pos += 1;
            }

            if pos >= rest.len() {
                panic!("Should have encountered at least one 'using' statement.");
            }

            // transform the rest of the body
            let env_binding = self.create_env_binding();
            let body_statements = self.transform_using_declarations(
                &rest[pos..],
                env_binding,
                Some(&mut top_level_statements),
            );

            // add `export {}` declarations for any hoisted bindings.
            if self.export_bindings.as_ref().is_some_and(|b| !b.is_empty()) {
                let bindings = self.export_bindings.as_ref().expect("export bindings");
                let mut export_specifiers: Vec<Node> =
                    Vec::with_capacity(self.export_binding_names.len());
                for name in &self.export_binding_names {
                    let specifier = bindings.get(name).copied().unwrap_or(Node::NIL);
                    go_assert!(
                        specifier.is_some(),
                        "Missing export binding for hoisted export name"
                    );
                    export_specifiers.push(specifier);
                }
                top_level_statements.push(f.new_export_declaration(
                    ModifierList::NIL, /*modifiers*/
                    false,             /*isTypeOnly*/
                    f.new_named_exports(f.new_node_list(&export_specifiers)),
                    Node::NIL, /*moduleSpecifier*/
                    Node::NIL, /*attributes*/
                ));
            }

            top_level_statements.extend(ec.end_variable_environment());
            if !self.export_vars.is_empty() {
                top_level_statements.push(f.new_variable_statement(
                    f.new_modifier_list(&[f.new_modifier(SyntaxKind::ExportKeyword)]),
                    f.new_variable_declaration_list(
                        f.new_node_list(&self.export_vars),
                        NodeFlags::LET,
                    ),
                ));
            }
            top_level_statements.extend(self.create_downlevel_using_statements(
                &body_statements,
                env_binding,
                using_kind == UsingKind::Async,
            ));

            if self.export_equals_binding.is_some() {
                top_level_statements.push(f.new_export_assignment(
                    ModifierList::NIL, /*modifiers*/
                    true,              /*isExportEquals*/
                    Node::NIL,         /*typeNode*/
                    self.export_equals_binding,
                ));
            }

            visited = f.update_source_file(
                node,
                f.new_node_list(&top_level_statements),
                node.end_of_file_token(),
            );
        } else {
            visited = self.visit_each_child(node);
        }
        ec.add_emit_helper(visited, &ec.read_emit_helpers());
        self.export_vars = Vec::new();
        self.export_bindings = None;
        self.export_binding_names = Vec::new();
        self.default_export_binding = Node::NIL;
        self.export_equals_binding = Node::NIL;
        visited
    }

    // Go: transformers/estransforms/using.go:192 usingDeclarationTransformer.visitBlock
    fn visit_block(&mut self, node: Node) -> Node {
        let node_statements = node.statements().to_vec();
        let using_kind = get_using_kind_of_statements(&node_statements);
        if using_kind != UsingKind::None {
            let ec = self.ec();
            let f = ec.factory();
            let (prologue, rest) = f.split_standard_prologue(&node_statements);
            let env_binding = self.create_env_binding();
            let mut statements: Vec<Node> = Vec::with_capacity(prologue.len() + 2);
            statements.extend(self.visit_slice(prologue).0);
            let transformed = self.transform_using_declarations(
                rest,
                env_binding,
                None, /*topLevelStatements*/
            );
            statements.extend(self.create_downlevel_using_statements(
                &transformed,
                env_binding,
                using_kind == UsingKind::Async,
            ));
            let statement_list = f.new_node_list_with_loc(&statements, node.statement_list().loc());
            return f.update_block(node, statement_list, node.multi_line());
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/using.go:211 usingDeclarationTransformer.visitForStatement
    fn visit_for_statement(&mut self, node: Node) -> Node {
        if node.initializer().is_some() && is_using_variable_declaration_list(node.initializer()) {
            // given:
            //
            //  for (using x = expr; cond; incr) { ... }
            //
            // produces a shallow transformation to:
            //
            //  {
            //    using x = expr;
            //    for (; cond; incr) { ... }
            //  }
            //
            // before handing the shallow transformation back to the visitor for an in-depth transformation.
            let ec = self.ec();
            let f = ec.factory();
            let block = f.new_block(
                f.new_node_list(&[
                    f.new_variable_statement(
                        ModifierList::NIL, /*modifiers*/
                        node.initializer(),
                    ),
                    f.update_for_statement(
                        node,
                        Node::NIL, /*initializer*/
                        node.condition(),
                        node.incrementor(),
                        node.statement(),
                    ),
                ]),
                false, /*multiLine*/
            );
            return self.visit_node(block);
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/using.go:241 usingDeclarationTransformer.visitForOfStatement
    fn visit_for_of_statement(&mut self, node: Node) -> Node {
        if is_using_variable_declaration_list(node.initializer()) {
            // given:
            //
            //  for (using x of y) { ... }
            //
            // produces a shallow transformation to:
            //
            //  for (const x_1 of y) {
            //    using x = x;
            //    ...
            //  }
            //
            // before handing the shallow transformation back to the visitor for an in-depth transformation.
            let ec = self.ec();
            let f = ec.factory();
            let for_initializer = node.initializer();
            let mut for_decl = for_initializer
                .declarations()
                .nodes()
                .first()
                .unwrap_or(Node::NIL);
            if for_decl.is_nil() {
                for_decl = f.new_variable_declaration(
                    f.new_temp_variable(),
                    Node::NIL,
                    Node::NIL,
                    Node::NIL,
                );
            }

            let is_await_using =
                get_using_kind_of_variable_declaration_list(for_initializer) == UsingKind::Async;
            let temp = f.new_generated_name_for_node(for_decl.name());
            let using_var = f.update_variable_declaration(
                for_decl,
                for_decl.name(),
                Node::NIL, /*exclamationToken*/
                Node::NIL, /*type*/
                temp,
            );
            let using_var_list = f.new_variable_declaration_list(
                f.new_node_list(&[using_var]),
                if is_await_using {
                    NodeFlags::AWAIT_USING
                } else {
                    NodeFlags::USING
                },
            );
            let using_var_statement =
                f.new_variable_statement(ModifierList::NIL /*modifiers*/, using_var_list);
            let statement = if is_block(node.statement()) {
                let mut statements: Vec<Node> =
                    Vec::with_capacity(node.statement().statements().len() + 1);
                statements.push(using_var_statement);
                statements.extend(node.statement().statements().iter());
                f.update_block(
                    node.statement(),
                    f.new_node_list(&statements),
                    node.statement().multi_line(),
                )
            } else {
                f.new_block(
                    f.new_node_list(&[using_var_statement, node.statement()]),
                    true, /*multiLine*/
                )
            };
            let updated = f.update_for_in_or_of_statement(
                node,
                node.await_modifier(),
                f.new_variable_declaration_list(
                    f.new_node_list(&[f.new_variable_declaration(
                        temp,
                        Node::NIL, /*exclamationToken*/
                        Node::NIL, /*type*/
                        Node::NIL,
                    )]),
                    NodeFlags::CONST,
                ),
                node.expression(),
                statement,
            );
            return self.visit_node(updated);
        }
        self.visit_each_child(node)
    }

    /// Go `hoist` closure of `transformUsingDeclarations`.
    fn hoist(&mut self, node: Node, top_level_statements: Option<&mut Vec<Node>>) -> Node {
        let Some(top_level_statements) = top_level_statements else {
            return node;
        };

        match node.kind() {
            SyntaxKind::ImportDeclaration
            | SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::ExportDeclaration
            | SyntaxKind::FunctionDeclaration => {
                self.hoist_import_or_export_or_hoisted_declaration(node, top_level_statements);
                Node::NIL
            }
            SyntaxKind::ExportAssignment => self.hoist_export_assignment(node),
            SyntaxKind::ClassDeclaration => self.hoist_class_declaration(node),
            SyntaxKind::VariableStatement => self.hoist_variable_statement(node),
            _ => node,
        }
    }

    // Go: transformers/estransforms/using.go:306 usingDeclarationTransformer.transformUsingDeclarations
    fn transform_using_declarations(
        &mut self,
        statements_in: &[Node],
        env_binding: Node,
        mut top_level_statements: Option<&mut Vec<Node>>,
    ) -> Vec<Node> {
        let ec = self.ec();
        let f = ec.factory();
        let mut statements: Vec<Node> = Vec::new();

        // Go `hoistOrAppendNode` closure.
        let hoist_or_append_node =
            |tx: &mut Self, node: Node, top: Option<&mut Vec<Node>>, statements: &mut Vec<Node>| {
                let node = tx.hoist(node, top);
                if node.is_some() {
                    statements.push(node);
                }
            };

        for &statement in statements_in {
            let using_kind = get_using_kind(statement);
            if using_kind != UsingKind::None {
                let declaration_list = statement.declaration_list();
                let mut declarations: Vec<Node> = Vec::new();
                for mut declaration in declaration_list.declarations().nodes().iter() {
                    if !is_identifier(declaration.name()) {
                        // Since binding patterns are a grammar error, we reset `declarations` so we don't process this as a `using`.
                        declarations = Vec::new();
                        break;
                    }

                    // perform a shallow transform for any named evaluation
                    if is_named_evaluation(&ec, declaration) {
                        declaration = transform_named_evaluation(
                            &ec,
                            declaration,
                            false, /*ignoreEmptyStringLiteral*/
                            "",    /*assignedName*/
                        );
                    }

                    let mut initializer = self.visit_node(declaration.initializer());
                    if initializer.is_nil() {
                        initializer = f.new_void_zero_expression();
                    }
                    declarations.push(f.update_variable_declaration(
                        declaration,
                        declaration.name(),
                        Node::NIL, /*exclamationToken*/
                        Node::NIL, /*type*/
                        f.new_add_disposable_resource_helper(
                            env_binding,
                            initializer,
                            using_kind == UsingKind::Async,
                        ),
                    ));
                }

                // Only replace the statement if it was valid.
                if !declarations.is_empty() {
                    let var_list = f.new_variable_declaration_list(
                        f.new_node_list(&declarations),
                        NodeFlags::CONST,
                    );
                    ec.set_original(var_list, declaration_list);
                    set_node_loc(var_list, declaration_list.loc());
                    let updated = f.update_variable_statement(
                        statement,
                        ModifierList::NIL, /*modifiers*/
                        var_list,
                    );
                    hoist_or_append_node(
                        self,
                        updated,
                        top_level_statements.as_deref_mut(),
                        &mut statements,
                    );
                    continue;
                }
            }

            let result = self.visit(statement);
            if result.is_some() {
                if result.kind() == SyntaxKind::SyntaxList {
                    for node in syntax_list_children(result) {
                        hoist_or_append_node(
                            self,
                            node,
                            top_level_statements.as_deref_mut(),
                            &mut statements,
                        );
                    }
                } else {
                    hoist_or_append_node(
                        self,
                        result,
                        top_level_statements.as_deref_mut(),
                        &mut statements,
                    );
                }
            }
        }
        statements
    }

    // Go: transformers/estransforms/using.go:397 usingDeclarationTransformer.hoistImportOrExportOrHoistedDeclaration
    fn hoist_import_or_export_or_hoisted_declaration(
        &mut self,
        node: Node,
        top_level_statements: &mut Vec<Node>,
    ) {
        // NOTE: `node` has already been visited
        top_level_statements.push(node);
    }

    // Go: transformers/estransforms/using.go:402 usingDeclarationTransformer.hoistExportAssignment
    fn hoist_export_assignment(&mut self, node: Node) -> Node {
        if node.is_export_equals() {
            self.hoist_export_equals(node)
        } else {
            self.hoist_export_default(node)
        }
    }

    // Go: transformers/estransforms/using.go:410 usingDeclarationTransformer.hoistExportDefault
    fn hoist_export_default(&mut self, node: Node) -> Node {
        // NOTE: `node` has already been visited
        if self.default_export_binding.is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return node;
        }

        // given:
        //
        //   export default expr;
        //
        // produces:
        //
        //   // top level
        //   var default_1;
        //   export { default_1 as default };
        //
        //   // body
        //   default_1 = expr;

        let ec = self.ec();
        let f = ec.factory();
        self.default_export_binding =
            f.new_unique_name_ex("_default", default_export_binding_options());
        self.hoist_binding_identifier(
            self.default_export_binding,
            true, /*isExport*/
            f.new_identifier("default"),
            node,
        );

        // give a class or function expression an assigned name, if needed.
        let mut expression = node.expression();
        let mut inner_expression =
            skip_outer_expressions(expression, OuterExpressionKinds::OEK_ALL);
        if is_named_evaluation(&ec, inner_expression) {
            inner_expression = transform_named_evaluation(
                &ec,
                inner_expression,
                false, /*ignoreEmptyStringLiteral*/
                "default",
            );
            expression = f.restore_outer_expressions(
                expression,
                inner_expression,
                OuterExpressionKinds::OEK_ALL,
            );
        }

        let assignment = f.new_assignment_expression(self.default_export_binding, expression);
        f.new_expression_statement(assignment)
    }

    // Go: transformers/estransforms/using.go:445 usingDeclarationTransformer.hoistExportEquals
    fn hoist_export_equals(&mut self, node: Node) -> Node {
        // NOTE: `node` has already been visited
        if self.export_equals_binding.is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return node;
        }

        // given:
        //
        //   export = expr;
        //
        // produces:
        //
        //   // top level
        //   var default_1;
        //
        //   try {
        //       // body
        //       default_1 = expr;
        //   } ...
        //
        //   // top level suffix
        //   export = default_1;

        let ec = self.ec();
        let f = ec.factory();
        self.export_equals_binding =
            f.new_unique_name_ex("_default", default_export_binding_options());
        ec.add_variable_declaration(self.export_equals_binding);

        // give a class or function expression an assigned name, if needed.
        let assignment = f.new_assignment_expression(self.export_equals_binding, node.expression());
        f.new_expression_statement(assignment)
    }

    // Go: transformers/estransforms/using.go:477 usingDeclarationTransformer.hoistClassDeclaration
    fn hoist_class_declaration(&mut self, node: Node) -> Node {
        // NOTE: `node` has already been visited
        if node.name().is_nil() && self.default_export_binding.is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return node;
        }

        let ec = self.ec();
        let f = ec.factory();
        let is_exported = has_syntactic_modifier(node, ModifierFlags::EXPORT);
        let is_default = has_syntactic_modifier(node, ModifierFlags::DEFAULT);

        // When hoisting a class declaration at the top level of a file containing a top-level `using` statement, we
        // must first convert it to a class expression so that we can hoist the binding outside of the `try`.
        let mut expression = convert_class_declaration_to_class_expression(&ec, node);
        if node.name().is_some() {
            // given:
            //
            //  using x = expr;
            //  class C {}
            //
            // produces:
            //
            //  var x, C;
            //  const env_1 = { ... };
            //  try {
            //    x = __addDisposableResource(env_1, expr, false);
            //    C = class {};
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResources(env_1);
            //  }
            //
            // If the class is exported, we also produce an `export { C };`
            self.hoist_binding_identifier(
                f.get_local_name(node),
                is_exported && !is_default,
                Node::NIL, /*exportAlias*/
                node,
            );
            expression = f.new_assignment_expression(f.get_declaration_name(node), expression);
            ec.set_original(expression, node);
            ec.set_source_map_range(expression, node.loc());
            ec.set_comment_range(expression, node.loc());
            if is_named_evaluation(&ec, expression) {
                expression = transform_named_evaluation(
                    &ec, expression, false, /*ignoreEmptyStringLiteral*/
                    "",    /*assignedName*/
                );
            }
        }

        if is_default && self.default_export_binding.is_nil() {
            // In the case of a default export, we create a temporary variable that we export as the default and then
            // assign to that variable.
            //
            // given:
            //
            //  using x = expr;
            //  export default class C {}
            //
            // produces:
            //
            //  export { default_1 as default };
            //  var x, C, default_1;
            //  const env_1 = { ... };
            //  try {
            //    x = __addDisposableResource(env_1, expr, false);
            //    default_1 = C = class {};
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResources(env_1);
            //  }
            //
            // Though we will never reassign `default_1`, this most closely matches the specified runtime semantics.
            self.default_export_binding =
                f.new_unique_name_ex("_default", default_export_binding_options());
            self.hoist_binding_identifier(
                self.default_export_binding,
                true, /*isExport*/
                f.new_identifier("default"),
                node,
            );
            expression = f.new_assignment_expression(self.default_export_binding, expression);
            ec.set_original(expression, node);
            if is_named_evaluation(&ec, expression) {
                expression = transform_named_evaluation(
                    &ec, expression, false, /*ignoreEmptyStringLiteral*/
                    "default",
                );
            }
        }

        f.new_expression_statement(expression)
    }

    // Go: transformers/estransforms/using.go:562 usingDeclarationTransformer.hoistVariableStatement
    fn hoist_variable_statement(&mut self, node: Node) -> Node {
        // NOTE: `node` has already been visited
        let ec = self.ec();
        let f = ec.factory();
        let mut expressions: Vec<Node> = Vec::new();
        let is_exported = has_syntactic_modifier(node, ModifierFlags::EXPORT);
        for variable in node.declaration_list().declarations().nodes().iter() {
            self.hoist_binding_element(variable, is_exported, variable);
            if variable.initializer().is_some() {
                expressions.push(self.hoist_initialized_variable(variable));
            }
        }
        if !expressions.is_empty() {
            let statement = f.new_expression_statement(f.inline_expressions(&expressions));
            ec.set_original(statement, node);
            ec.set_comment_range(statement, node.loc());
            ec.set_source_map_range(statement, node.loc());
            return statement;
        }
        Node::NIL
    }

    // Go: transformers/estransforms/using.go:582 usingDeclarationTransformer.hoistInitializedVariable
    fn hoist_initialized_variable(&mut self, node: Node) -> Node {
        // NOTE: `node` has already been visited
        if node.initializer().is_nil() {
            panic!("Expected initializer");
        }
        let ec = self.ec();
        let f = ec.factory();
        let target = if is_identifier(node.name()) {
            let target = f.clone_node(node.name());
            ec.set_emit_flags(
                target,
                ec.emit_flags(target)
                    .without(EmitFlags::LOCAL_NAME | EmitFlags::EXPORT_NAME),
            );
            target
        } else {
            convert_binding_pattern_to_assignment_pattern(&ec, node.name())
        };

        let assignment = f.new_assignment_expression(target, node.initializer());
        ec.set_original(assignment, node);
        ec.set_comment_range(assignment, node.loc());
        ec.set_source_map_range(assignment, node.loc());
        assignment
    }

    // Go: transformers/estransforms/using.go:602 usingDeclarationTransformer.hoistBindingElement
    fn hoist_binding_element(
        &mut self,
        node: Node, /*VariableDeclaration|BindingElement*/
        is_exported_declaration: bool,
        original: Node,
    ) {
        // NOTE: `node` has already been visited
        if is_binding_pattern(node.name()) {
            for element in node.name().elements().iter() {
                if element.name().is_some() {
                    self.hoist_binding_element(element, is_exported_declaration, original);
                }
            }
        } else {
            self.hoist_binding_identifier(
                node.name(),
                is_exported_declaration,
                Node::NIL, /*exportAlias*/
                original,
            );
        }
    }

    // Go: transformers/estransforms/using.go:615 usingDeclarationTransformer.hoistBindingIdentifier
    fn hoist_binding_identifier(
        &mut self,
        node: Node,
        is_export: bool,
        export_alias: Node,
        original: Node,
    ) {
        // NOTE: `node` has already been visited
        let ec = self.ec();
        let f = ec.factory();
        let mut name = node;
        if !is_generated_identifier(&ec, node) {
            name = f.clone_node(name);
        }
        if is_export {
            if export_alias.is_nil() && !is_local_name(&ec, name) {
                let var_decl = f.new_variable_declaration(
                    name,
                    Node::NIL, /*exclamationToken*/
                    Node::NIL, /*type*/
                    Node::NIL, /*initializer*/
                );
                if original.is_some() {
                    ec.set_original(var_decl, original);
                }
                self.export_vars.push(var_decl);
                return;
            }

            let (local_name, export_name) = if export_alias.is_some() {
                (name, export_alias)
            } else {
                (Node::NIL, name)
            };
            let specifier =
                f.new_export_specifier(false /*isTypeOnly*/, local_name, export_name);
            if original.is_some() {
                ec.set_original(specifier, original);
            }
            let bindings = self.export_bindings.get_or_insert_with(FxHashMap::default);
            let key = name.text().to_string();
            if !bindings.contains_key(&key) {
                self.export_binding_names.push(key.clone());
            }
            bindings.insert(key, specifier);
        }
        ec.add_variable_declaration(name);
    }

    // Go: transformers/estransforms/using.go:654 usingDeclarationTransformer.createEnvBinding
    fn create_env_binding(&self) -> Node {
        self.emit_context.factory().new_unique_name("env")
    }

    // Go: transformers/estransforms/using.go:658 usingDeclarationTransformer.createDownlevelUsingStatements
    fn create_downlevel_using_statements(
        &self,
        body_statements: &[Node],
        env_binding: Node,
        async_: bool,
    ) -> Vec<Node> {
        let f = self.emit_context.factory();
        let mut statements: Vec<Node> = Vec::with_capacity(2);

        // produces:
        //
        //  const env_1 = { stack: [], error: void 0, hasError: false };
        //
        let env_object = f.new_object_literal_expression(
            f.new_node_list(&[
                f.new_property_assignment(
                    ModifierList::NIL, /*modifiers*/
                    f.new_identifier("stack"),
                    Node::NIL, /*postfixToken*/
                    Node::NIL, /*typeNode*/
                    f.new_array_literal_expression(NodeList::NIL, false /*multiLine*/),
                ),
                f.new_property_assignment(
                    ModifierList::NIL, /*modifiers*/
                    f.new_identifier("error"),
                    Node::NIL, /*postfixToken*/
                    Node::NIL, /*typeNode*/
                    f.new_void_zero_expression(),
                ),
                f.new_property_assignment(
                    ModifierList::NIL, /*modifiers*/
                    f.new_identifier("hasError"),
                    Node::NIL, /*postfixToken*/
                    Node::NIL, /*typeNode*/
                    f.new_false_expression(),
                ),
            ]),
            false, /*multiLine*/
        );
        let env_var = f.new_variable_declaration(
            env_binding,
            Node::NIL, /*exclamationToken*/
            Node::NIL, /*typeNode*/
            env_object,
        );
        let env_var_list =
            f.new_variable_declaration_list(f.new_node_list(&[env_var]), NodeFlags::CONST);
        let env_var_statement =
            f.new_variable_statement(ModifierList::NIL /*modifiers*/, env_var_list);
        statements.push(env_var_statement);

        // when `async` is `false`, produces:
        //
        //  try {
        //    <bodyStatements>
        //  }
        //  catch (e_1) {
        //      env_1.error = e_1;
        //      env_1.hasError = true;
        //  }
        //  finally {
        //    __disposeResources(env_1);
        //  }

        // when `async` is `true`, produces:
        //
        //  try {
        //    <bodyStatements>
        //  }
        //  catch (e_1) {
        //      env_1.error = e_1;
        //      env_1.hasError = true;
        //  }
        //  finally {
        //    const result_1 = __disposeResources(env_1);
        //    if (result_1) {
        //      await result_1;
        //    }
        //  }

        // Unfortunately, it is necessary to use two properties to indicate an error because `throw undefined` is legal
        // JavaScript.
        let try_block = f.new_block(f.new_node_list(body_statements), true /*multiLine*/);
        let body_catch_binding = f.new_unique_name("e");
        let catch_clause = f.new_catch_clause(
            f.new_variable_declaration(
                body_catch_binding,
                Node::NIL, /*exclamationToken*/
                Node::NIL, /*type*/
                Node::NIL, /*initializer*/
            ),
            f.new_block(
                f.new_node_list(&[
                    f.new_expression_statement(f.new_assignment_expression(
                        f.new_property_access_expression(
                            env_binding,
                            Node::NIL,
                            f.new_identifier("error"),
                            NodeFlags::NONE,
                        ),
                        body_catch_binding,
                    )),
                    f.new_expression_statement(f.new_assignment_expression(
                        f.new_property_access_expression(
                            env_binding,
                            Node::NIL,
                            f.new_identifier("hasError"),
                            NodeFlags::NONE,
                        ),
                        f.new_true_expression(),
                    )),
                ]),
                true, /*multiLine*/
            ),
        );

        let finally_block = if async_ {
            let result = f.new_unique_name("result");
            f.new_block(
                f.new_node_list(&[
                    f.new_variable_statement(
                        ModifierList::NIL, /*modifiers*/
                        f.new_variable_declaration_list(
                            f.new_node_list(&[f.new_variable_declaration(
                                result,
                                Node::NIL, /*exclamationToken*/
                                Node::NIL, /*type*/
                                f.new_dispose_resources_helper(env_binding),
                            )]),
                            NodeFlags::CONST,
                        ),
                    ),
                    f.new_if_statement(
                        result,
                        f.new_expression_statement(f.new_await_expression(result)),
                        Node::NIL, /*elseStatement*/
                    ),
                ]),
                true, /*multiLine*/
            )
        } else {
            f.new_block(
                f.new_node_list(&[
                    f.new_expression_statement(f.new_dispose_resources_helper(env_binding))
                ]),
                true, /*multiLine*/
            )
        };

        let try_statement = f.new_try_statement(try_block, catch_clause, finally_block);
        statements.push(try_statement);
        statements
    }
}

// Go: transformers/estransforms/using.go:761 isUsingVariableDeclarationList
pub(super) fn is_using_variable_declaration_list(node: Node) -> bool {
    is_variable_declaration_list(node)
        && get_using_kind_of_variable_declaration_list(node) != UsingKind::None
}

// Go: transformers/estransforms/using.go:765 getUsingKindOfVariableDeclarationList
pub(super) fn get_using_kind_of_variable_declaration_list(node: Node) -> UsingKind {
    let block_scoped = node.flags() & NodeFlags::BLOCK_SCOPED;
    if block_scoped == NodeFlags::AWAIT_USING {
        UsingKind::Async
    } else if block_scoped == NodeFlags::USING {
        UsingKind::Sync
    } else {
        UsingKind::None
    }
}

// Go: transformers/estransforms/using.go:776 getUsingKindOfVariableStatement
pub(super) fn get_using_kind_of_variable_statement(node: Node) -> UsingKind {
    get_using_kind_of_variable_declaration_list(node.declaration_list())
}

// Go: transformers/estransforms/using.go:780 getUsingKind
pub(super) fn get_using_kind(statement: Node) -> UsingKind {
    if is_variable_statement(statement) {
        return get_using_kind_of_variable_statement(statement);
    }
    UsingKind::None
}

// Go: transformers/estransforms/using.go:787 getUsingKindOfStatements
pub(super) fn get_using_kind_of_statements(statements: &[Node]) -> UsingKind {
    let mut result = UsingKind::None;
    for &statement in statements {
        let using_kind = get_using_kind(statement);
        if using_kind == UsingKind::Async {
            return UsingKind::Async;
        }
        if using_kind > result {
            result = using_kind;
        }
    }
    result
}
