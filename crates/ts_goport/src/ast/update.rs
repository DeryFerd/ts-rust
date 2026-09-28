//! Port of the Go `NodeFactory.Update*` methods (`ast/ast_generated.go`),
//! `UpdateSourceFile` (`ast/ast.go`), `NodeFactoryHooks` and `updateNode`
//! (`ast/ast.go`).
//!
//! Each `update_*` method returns `node` itself when every argument equals the
//! current child (Go pointer equality on `Node`, `NodeList` and
//! `ModifierList` handles). Otherwise it creates a new node with the Go `New*`
//! constructor and copies `Flags` and `Loc` from `node` (`update_node`).

use crate::prelude::*;

// Go: ast/ast.go:59 NodeFactoryHooks
/// Go `ast.NodeFactoryHooks`. The printer's `EmitContext` sets them.
#[derive(Clone, Default)]
pub struct NodeFactoryHooks {
    /// Hooks the creation of a node.
    pub on_create: Option<Rc<dyn Fn(Node)>>,
    /// Hooks the updating of a node: `(updated, original)`.
    pub on_update: Option<Rc<dyn Fn(Node, Node)>>,
    /// Hooks the cloning of a node: `(updated, original)`.
    pub on_clone: Option<Rc<dyn Fn(Node, Node)>>,
}

impl std::fmt::Debug for NodeFactoryHooks {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeFactoryHooks")
            .field("on_create", &self.on_create.is_some())
            .field("on_update", &self.on_update.is_some())
            .field("on_clone", &self.on_clone.is_some())
            .finish()
    }
}

// Go: ast/ast.go:101 updateNode
/// Copies `Flags` and `Loc` from `original` to a new `updated` node and runs
/// the `OnUpdate` hook.
pub fn update_node(updated: Node, original: Node, hooks: &NodeFactoryHooks) -> Node {
    if updated != original {
        set_node_flags(updated, original.flags());
        set_node_loc(updated, original.loc());
        if let Some(on_update) = &hooks.on_update {
            on_update(updated, original);
        }
    }
    updated
}

impl NodeFactory {
    // Go: ast/ast_generated.go:850 UpdateQualifiedName
    pub fn update_qualified_name(&self, node: Node, left: Node, right: Node) -> Node {
        if left != node.left() || right != node.right() {
            return update_node(self.new_qualified_name(left, right), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:894 UpdateComputedPropertyName
    pub fn update_computed_property_name(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_computed_property_name(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:937 UpdateDecorator
    pub fn update_decorator(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_decorator(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1001 UpdateIfStatement
    pub fn update_if_statement(
        &self,
        node: Node,
        expression: Node,
        then_statement: Node,
        else_statement: Node,
    ) -> Node {
        if expression != node.expression()
            || then_statement != node.then_statement()
            || else_statement != node.else_statement()
        {
            return update_node(
                self.new_if_statement(expression, then_statement, else_statement),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1047 UpdateDoStatement
    pub fn update_do_statement(&self, node: Node, statement: Node, expression: Node) -> Node {
        if statement != node.statement() || expression != node.expression() {
            return update_node(
                self.new_do_statement(statement, expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1092 UpdateWhileStatement
    pub fn update_while_statement(&self, node: Node, expression: Node, statement: Node) -> Node {
        if expression != node.expression() || statement != node.statement() {
            return update_node(
                self.new_while_statement(expression, statement),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1142 UpdateForStatement
    pub fn update_for_statement(
        &self,
        node: Node,
        initializer: Node,
        condition: Node,
        incrementor: Node,
        statement: Node,
    ) -> Node {
        if initializer != node.initializer()
            || condition != node.condition()
            || incrementor != node.incrementor()
            || statement != node.statement()
        {
            return update_node(
                self.new_for_statement(initializer, condition, incrementor, statement),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1198 UpdateForInOrOfStatement
    pub fn update_for_in_or_of_statement(
        &self,
        node: Node,
        await_modifier: Node,
        initializer: Node,
        expression: Node,
        statement: Node,
    ) -> Node {
        if await_modifier != node.await_modifier()
            || initializer != node.initializer()
            || expression != node.expression()
            || statement != node.statement()
        {
            return update_node(
                self.new_for_in_or_of_statement(
                    node.kind(),
                    await_modifier,
                    initializer,
                    expression,
                    statement,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1243 UpdateBreakStatement
    pub fn update_break_statement(&self, node: Node, label: Node) -> Node {
        if label != node.label() {
            return update_node(self.new_break_statement(label), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1281 UpdateContinueStatement
    pub fn update_continue_statement(&self, node: Node, label: Node) -> Node {
        if label != node.label() {
            return update_node(self.new_continue_statement(label), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1320 UpdateReturnStatement
    pub fn update_return_statement(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_return_statement(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1361 UpdateWithStatement
    pub fn update_with_statement(&self, node: Node, expression: Node, statement: Node) -> Node {
        if expression != node.expression() || statement != node.statement() {
            return update_node(
                self.new_with_statement(expression, statement),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1407 UpdateSwitchStatement
    pub fn update_switch_statement(&self, node: Node, expression: Node, case_block: Node) -> Node {
        if expression != node.expression() || case_block != node.case_block() {
            return update_node(
                self.new_switch_statement(expression, case_block),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1452 UpdateCaseBlock
    pub fn update_case_block(&self, node: Node, clauses: NodeList) -> Node {
        if clauses != node.clauses() {
            return update_node(self.new_case_block(clauses), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1498 UpdateCaseOrDefaultClause
    pub fn update_case_or_default_clause(
        &self,
        node: Node,
        expression: Node,
        statements: NodeList,
    ) -> Node {
        if expression != node.expression() || statements != node.statement_list() {
            return update_node(
                self.new_case_or_default_clause(node.kind(), expression, statements),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1546 UpdateThrowStatement
    pub fn update_throw_statement(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_throw_statement(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1593 UpdateTryStatement
    pub fn update_try_statement(
        &self,
        node: Node,
        try_block: Node,
        catch_clause: Node,
        finally_block: Node,
    ) -> Node {
        if try_block != node.try_block()
            || catch_clause != node.catch_clause()
            || finally_block != node.finally_block()
        {
            return update_node(
                self.new_try_statement(try_block, catch_clause, finally_block),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1641 UpdateCatchClause
    pub fn update_catch_clause(&self, node: Node, variable_declaration: Node, block: Node) -> Node {
        if variable_declaration != node.variable_declaration() || block != node.block() {
            return update_node(
                self.new_catch_clause(variable_declaration, block),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1702 UpdateLabeledStatement
    pub fn update_labeled_statement(&self, node: Node, label: Node, statement: Node) -> Node {
        if label != node.label() || statement != node.statement() {
            return update_node(
                self.new_labeled_statement(label, statement),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1745 UpdateExpressionStatement
    pub fn update_expression_statement(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_expression_statement(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1791 UpdateBlock
    pub fn update_block(&self, node: Node, statements: NodeList, multi_line: bool) -> Node {
        if statements != node.statement_list() || multi_line != node.multi_line() {
            return update_node(self.new_block(statements, multi_line), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:1836 UpdateVariableStatement
    pub fn update_variable_statement(
        &self,
        node: Node,
        modifiers: ModifierList,
        declaration_list: Node,
    ) -> Node {
        if modifiers != node.modifiers() || declaration_list != node.declaration_list() {
            return update_node(
                self.new_variable_statement(modifiers, declaration_list),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1883 UpdateVariableDeclaration
    pub fn update_variable_declaration(
        &self,
        node: Node,
        name: Node,
        exclamation_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        if name != node.name()
            || exclamation_token != node.exclamation_token()
            || type_node != node.type_()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_variable_declaration(name, exclamation_token, type_node, initializer),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1931 UpdateVariableDeclarationList
    pub fn update_variable_declaration_list(
        &self,
        node: Node,
        declarations: NodeList,
        flags: NodeFlags,
    ) -> Node {
        if declarations != node.declarations() || flags != node.flags() {
            return update_node(
                self.new_variable_declaration_list(declarations, flags),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:1970 UpdateBindingPattern
    pub fn update_binding_pattern(&self, node: Node, elements: NodeList) -> Node {
        if elements != node.element_list() {
            return update_node(
                self.new_binding_pattern(node.kind(), elements),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2024 UpdateParameterDeclaration
    pub fn update_parameter_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        dot_dot_dot_token: Node,
        name: Node,
        question_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || dot_dot_dot_token != node.dot_dot_dot_token()
            || name != node.name()
            || question_token != node.question_token()
            || type_node != node.type_()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_parameter_declaration(
                    modifiers,
                    dot_dot_dot_token,
                    name,
                    question_token,
                    type_node,
                    initializer,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2081 UpdateBindingElement
    pub fn update_binding_element(
        &self,
        node: Node,
        dot_dot_dot_token: Node,
        property_name: Node,
        name: Node,
        initializer: Node,
    ) -> Node {
        if dot_dot_dot_token != node.dot_dot_dot_token()
            || property_name != node.property_name()
            || name != node.name()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_binding_element(dot_dot_dot_token, property_name, name, initializer),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2127 UpdateMissingDeclaration
    pub fn update_missing_declaration(&self, node: Node, modifiers: ModifierList) -> Node {
        if modifiers != node.modifiers() {
            return update_node(self.new_missing_declaration(modifiers), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2178 UpdateFunctionDeclaration
    pub fn update_function_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || asterisk_token != node.asterisk_token()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_function_declaration(
                    modifiers,
                    asterisk_token,
                    name,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2232 UpdateClassDeclaration
    pub fn update_class_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || heritage_clauses != node.heritage_clauses()
            || members != node.member_list()
        {
            return update_node(
                self.new_class_declaration(
                    modifiers,
                    name,
                    type_parameters,
                    heritage_clauses,
                    members,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2282 UpdateClassExpression
    pub fn update_class_expression(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || heritage_clauses != node.heritage_clauses()
            || members != node.member_list()
        {
            return update_node(
                self.new_class_expression(
                    modifiers,
                    name,
                    type_parameters,
                    heritage_clauses,
                    members,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2331 UpdateHeritageClause
    pub fn update_heritage_clause(&self, node: Node, token: SyntaxKind, types: NodeList) -> Node {
        if token != node.token() || types != node.types() {
            return update_node(self.new_heritage_clause(token, types), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2380 UpdateInterfaceDeclaration
    pub fn update_interface_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || heritage_clauses != node.heritage_clauses()
            || members != node.member_list()
        {
            return update_node(
                self.new_interface_declaration(
                    modifiers,
                    name,
                    type_parameters,
                    heritage_clauses,
                    members,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2445 UpdateTypeAliasDeclaration
    pub fn update_type_alias_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || type_node != node.type_()
        {
            match node.kind() {
                SyntaxKind::TypeAliasDeclaration => {
                    return update_node(
                        self.new_type_alias_declaration(
                            modifiers,
                            name,
                            type_parameters,
                            type_node,
                        ),
                        node,
                        self.hooks(),
                    );
                }
                SyntaxKind::JsTypeAliasDeclaration => {
                    return update_node(
                        self.new_js_type_alias_declaration(
                            modifiers,
                            name,
                            type_parameters,
                            type_node,
                        ),
                        node,
                        self.hooks(),
                    );
                }
                _ => panic!(
                    "unexpected kind in UpdateTypeAliasDeclaration: {:?}",
                    node.kind()
                ),
            }
        }
        node
    }

    // Go: ast/ast_generated.go:2511 UpdateEnumMember
    pub fn update_enum_member(&self, node: Node, name: Node, initializer: Node) -> Node {
        if name != node.name() || initializer != node.initializer() {
            return update_node(self.new_enum_member(name, initializer), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2560 UpdateEnumDeclaration
    pub fn update_enum_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        members: NodeList,
    ) -> Node {
        if modifiers != node.modifiers() || name != node.name() || members != node.member_list() {
            return update_node(
                self.new_enum_declaration(modifiers, name, members),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2603 UpdateModuleBlock
    pub fn update_module_block(&self, node: Node, statements: NodeList) -> Node {
        if statements != node.statement_list() {
            return update_node(self.new_module_block(statements), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2705 UpdateImportDeclaration
    pub fn update_import_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        import_clause: Node,
        module_specifier: Node,
        attributes: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || import_clause != node.import_clause()
            || module_specifier != node.module_specifier()
            || attributes != node.attributes()
        {
            match node.kind() {
                SyntaxKind::ImportDeclaration => {
                    return update_node(
                        self.new_import_declaration(
                            modifiers,
                            import_clause,
                            module_specifier,
                            attributes,
                        ),
                        node,
                        self.hooks(),
                    );
                }
                SyntaxKind::JsImportDeclaration => {
                    return update_node(
                        self.new_js_import_declaration(
                            modifiers,
                            import_clause,
                            module_specifier,
                            attributes,
                        ),
                        node,
                        self.hooks(),
                    );
                }
                _ => panic!(
                    "unexpected kind in UpdateImportDeclaration: {:?}",
                    node.kind()
                ),
            }
        }
        node
    }

    // Go: ast/ast_generated.go:2771 UpdateExternalModuleReference
    pub fn update_external_module_reference(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_external_module_reference(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2815 UpdateNamespaceImport
    pub fn update_namespace_import(&self, node: Node, name: Node) -> Node {
        if name != node.name() {
            return update_node(self.new_namespace_import(name), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2862 UpdateNamedImports
    pub fn update_named_imports(&self, node: Node, elements: NodeList) -> Node {
        if elements != node.element_list() {
            return update_node(self.new_named_imports(elements), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:2912 UpdateExportAssignment
    pub fn update_export_assignment(
        &self,
        node: Node,
        modifiers: ModifierList,
        is_export_equals: bool,
        type_node: Node,
        expression: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || is_export_equals != node.is_export_equals()
            || type_node != node.type_()
            || expression != node.expression()
        {
            return update_node(
                self.new_export_assignment(modifiers, is_export_equals, type_node, expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2954 UpdateNamespaceExportDeclaration
    pub fn update_namespace_export_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
    ) -> Node {
        if modifiers != node.modifiers() || name != node.name() {
            return update_node(
                self.new_namespace_export_declaration(modifiers, name),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:2997 UpdateNamespaceExport
    pub fn update_namespace_export(&self, node: Node, name: Node) -> Node {
        if name != node.name() {
            return update_node(self.new_namespace_export(name), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:3044 UpdateNamedExports
    pub fn update_named_exports(&self, node: Node, elements: NodeList) -> Node {
        if elements != node.element_list() {
            return update_node(self.new_named_exports(elements), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:3093 UpdateExportSpecifier
    pub fn update_export_specifier(
        &self,
        node: Node,
        is_type_only: bool,
        property_name: Node,
        name: Node,
    ) -> Node {
        if is_type_only != node.is_type_only()
            || property_name != node.property_name()
            || name != node.name()
        {
            return update_node(
                self.new_export_specifier(is_type_only, property_name, name),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3140 UpdateCallSignatureDeclaration
    pub fn update_call_signature_declaration(
        &self,
        node: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_call_signature_declaration(type_parameters, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3183 UpdateConstructSignatureDeclaration
    pub fn update_construct_signature_declaration(
        &self,
        node: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_construct_signature_declaration(type_parameters, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3231 UpdateConstructorDeclaration
    pub fn update_constructor_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_constructor_declaration(
                    modifiers,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3279 UpdateGetAccessorDeclaration
    pub fn update_get_accessor_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_get_accessor_declaration(
                    modifiers,
                    name,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3332 UpdateSetAccessorDeclaration
    pub fn update_set_accessor_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_set_accessor_declaration(
                    modifiers,
                    name,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3387 UpdateIndexSignatureDeclaration
    pub fn update_index_signature_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_index_signature_declaration(modifiers, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3433 UpdateMethodSignatureDeclaration
    pub fn update_method_signature_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_method_signature_declaration(
                    modifiers,
                    name,
                    postfix_token,
                    type_parameters,
                    parameters,
                    type_node,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3493 UpdateMethodDeclaration
    pub fn update_method_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        postfix_token: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || asterisk_token != node.asterisk_token()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_method_declaration(
                    modifiers,
                    asterisk_token,
                    name,
                    postfix_token,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3551 UpdatePropertySignatureDeclaration
    pub fn update_property_signature_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_node != node.type_()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_property_signature_declaration(
                    modifiers,
                    name,
                    postfix_token,
                    type_node,
                    initializer,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3605 UpdatePropertyDeclaration
    pub fn update_property_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_node != node.type_()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_property_declaration(
                    modifiers,
                    name,
                    postfix_token,
                    type_node,
                    initializer,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3681 UpdateClassStaticBlockDeclaration
    pub fn update_class_static_block_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers() || body != node.body() {
            return update_node(
                self.new_class_static_block_declaration(modifiers, body),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3903 UpdateBinaryExpression
    pub fn update_binary_expression(
        &self,
        node: Node,
        modifiers: ModifierList,
        left: Node,
        type_node: Node,
        operator_token: Node,
        right: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || left != node.left()
            || type_node != node.type_()
            || operator_token != node.operator_token()
            || right != node.right()
        {
            return update_node(
                self.new_binary_expression(modifiers, left, type_node, operator_token, right),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3947 UpdatePrefixUnaryExpression
    pub fn update_prefix_unary_expression(
        &self,
        node: Node,
        operator: SyntaxKind,
        operand: Node,
    ) -> Node {
        if operator != node.operator() || operand != node.operand() {
            return update_node(
                self.new_prefix_unary_expression(operator, operand),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:3991 UpdatePostfixUnaryExpression
    pub fn update_postfix_unary_expression(
        &self,
        node: Node,
        operand: Node,
        operator: SyntaxKind,
    ) -> Node {
        if operand != node.operand() || operator != node.operator() {
            return update_node(
                self.new_postfix_unary_expression(operand, operator),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4035 UpdateYieldExpression
    pub fn update_yield_expression(
        &self,
        node: Node,
        asterisk_token: Node,
        expression: Node,
    ) -> Node {
        if asterisk_token != node.asterisk_token() || expression != node.expression() {
            return update_node(
                self.new_yield_expression(asterisk_token, expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4084 UpdateArrowFunction
    pub fn update_arrow_function(
        &self,
        node: Node,
        modifiers: ModifierList,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        equals_greater_than_token: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || equals_greater_than_token != node.equals_greater_than_token()
            || body != node.body()
        {
            return update_node(
                self.new_arrow_function(
                    modifiers,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    equals_greater_than_token,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4141 UpdateFunctionExpression
    pub fn update_function_expression(
        &self,
        node: Node,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || asterisk_token != node.asterisk_token()
            || name != node.name()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
            || full_signature != node.full_signature()
            || body != node.body()
        {
            return update_node(
                self.new_function_expression(
                    modifiers,
                    asterisk_token,
                    name,
                    type_parameters,
                    parameters,
                    type_node,
                    full_signature,
                    body,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4192 UpdateAsExpression
    pub fn update_as_expression(&self, node: Node, expression: Node, type_node: Node) -> Node {
        if expression != node.expression() || type_node != node.type_() {
            return update_node(
                self.new_as_expression(expression, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4232 UpdateSatisfiesExpression
    pub fn update_satisfies_expression(
        &self,
        node: Node,
        expression: Node,
        type_node: Node,
    ) -> Node {
        if expression != node.expression() || type_node != node.type_() {
            return update_node(
                self.new_satisfies_expression(expression, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4279 UpdateConditionalExpression
    pub fn update_conditional_expression(
        &self,
        node: Node,
        condition: Node,
        question_token: Node,
        when_true: Node,
        colon_token: Node,
        when_false: Node,
    ) -> Node {
        if condition != node.condition()
            || question_token != node.question_token()
            || when_true != node.when_true()
            || colon_token != node.colon_token()
            || when_false != node.when_false()
        {
            return update_node(
                self.new_conditional_expression(
                    condition,
                    question_token,
                    when_true,
                    colon_token,
                    when_false,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4337 UpdatePropertyAccessExpression
    pub fn update_property_access_expression(
        &self,
        node: Node,
        expression: Node,
        question_dot_token: Node,
        name: Node,
        flags: NodeFlags,
    ) -> Node {
        if expression != node.expression()
            || question_dot_token != node.question_dot_token()
            || name != node.name()
            || flags != node.flags()
        {
            return update_node(
                self.new_property_access_expression(expression, question_dot_token, name, flags),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4387 UpdateElementAccessExpression
    pub fn update_element_access_expression(
        &self,
        node: Node,
        expression: Node,
        question_dot_token: Node,
        argument_expression: Node,
        flags: NodeFlags,
    ) -> Node {
        if expression != node.expression()
            || question_dot_token != node.question_dot_token()
            || argument_expression != node.argument_expression()
            || flags != node.flags()
        {
            return update_node(
                self.new_element_access_expression(
                    expression,
                    question_dot_token,
                    argument_expression,
                    flags,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4441 UpdateCallExpression
    pub fn update_call_expression(
        &self,
        node: Node,
        expression: Node,
        question_dot_token: Node,
        type_arguments: NodeList,
        arguments: NodeList,
        flags: NodeFlags,
    ) -> Node {
        if expression != node.expression()
            || question_dot_token != node.question_dot_token()
            || type_arguments != node.type_argument_list()
            || arguments != node.argument_list()
            || flags != node.flags()
        {
            return update_node(
                self.new_call_expression(
                    expression,
                    question_dot_token,
                    type_arguments,
                    arguments,
                    flags,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4487 UpdateNewExpression
    pub fn update_new_expression(
        &self,
        node: Node,
        expression: Node,
        type_arguments: NodeList,
        arguments: NodeList,
    ) -> Node {
        if expression != node.expression()
            || type_arguments != node.type_argument_list()
            || arguments != node.argument_list()
        {
            return update_node(
                self.new_new_expression(expression, type_arguments, arguments),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4529 UpdateMetaProperty
    pub fn update_meta_property(&self, node: Node, keyword_token: SyntaxKind, name: Node) -> Node {
        if keyword_token != node.keyword_token() || name != node.name() {
            return update_node(
                self.new_meta_property(keyword_token, name),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4573 UpdateNonNullExpression
    pub fn update_non_null_expression(
        &self,
        node: Node,
        expression: Node,
        flags: NodeFlags,
    ) -> Node {
        if expression != node.expression() || flags != node.flags() {
            return update_node(
                self.new_non_null_expression(expression, flags),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4611 UpdateSpreadElement
    pub fn update_spread_element(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_spread_element(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:4652 UpdateTemplateExpression
    pub fn update_template_expression(
        &self,
        node: Node,
        head: Node,
        template_spans: NodeList,
    ) -> Node {
        if head != node.head() || template_spans != node.template_spans() {
            return update_node(
                self.new_template_expression(head, template_spans),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4697 UpdateTemplateSpan
    pub fn update_template_span(&self, node: Node, expression: Node, literal: Node) -> Node {
        if expression != node.expression() || literal != node.literal() {
            return update_node(
                self.new_template_span(expression, literal),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4749 UpdateTaggedTemplateExpression
    pub fn update_tagged_template_expression(
        &self,
        node: Node,
        tag: Node,
        question_dot_token: Node,
        type_arguments: NodeList,
        template: Node,
        flags: NodeFlags,
    ) -> Node {
        if tag != node.tag()
            || question_dot_token != node.question_dot_token()
            || type_arguments != node.type_argument_list()
            || template != node.template()
            || flags != node.flags()
        {
            return update_node(
                self.new_tagged_template_expression(
                    tag,
                    question_dot_token,
                    type_arguments,
                    template,
                    flags,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4790 UpdateParenthesizedExpression
    pub fn update_parenthesized_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_parenthesized_expression(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4835 UpdateArrayLiteralExpression
    pub fn update_array_literal_expression(
        &self,
        node: Node,
        elements: NodeList,
        multi_line: bool,
    ) -> Node {
        if elements != node.element_list() || multi_line != node.multi_line() {
            return update_node(
                self.new_array_literal_expression(elements, multi_line),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4881 UpdateObjectLiteralExpression
    pub fn update_object_literal_expression(
        &self,
        node: Node,
        properties: NodeList,
        multi_line: bool,
    ) -> Node {
        if properties != node.property_list() || multi_line != node.multi_line() {
            return update_node(
                self.new_object_literal_expression(properties, multi_line),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:4925 UpdateSpreadAssignment
    pub fn update_spread_assignment(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_spread_assignment(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:4971 UpdatePropertyAssignment
    pub fn update_property_assignment(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_node != node.type_()
            || initializer != node.initializer()
        {
            return update_node(
                self.new_property_assignment(
                    modifiers,
                    name,
                    postfix_token,
                    type_node,
                    initializer,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5027 UpdateShorthandPropertyAssignment
    pub fn update_shorthand_property_assignment(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        equals_token: Node,
        object_assignment_initializer: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || postfix_token != node.postfix_token()
            || type_node != node.type_()
            || equals_token != node.equals_token()
            || object_assignment_initializer != node.object_assignment_initializer()
        {
            return update_node(
                self.new_shorthand_property_assignment(
                    modifiers,
                    name,
                    postfix_token,
                    type_node,
                    equals_token,
                    object_assignment_initializer,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5074 UpdateDeleteExpression
    pub fn update_delete_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_delete_expression(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5116 UpdateTypeOfExpression
    pub fn update_type_of_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_type_of_expression(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5158 UpdateVoidExpression
    pub fn update_void_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_void_expression(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5200 UpdateAwaitExpression
    pub fn update_await_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(self.new_await_expression(expression), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5240 UpdateTypeAssertion
    pub fn update_type_assertion(&self, node: Node, type_node: Node, expression: Node) -> Node {
        if type_node != node.type_() || expression != node.expression() {
            return update_node(
                self.new_type_assertion(type_node, expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5314 UpdateUnionTypeNode
    pub fn update_union_type_node(&self, node: Node, types: NodeList) -> Node {
        if types != node.types() {
            return update_node(self.new_union_type_node(types), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5352 UpdateIntersectionTypeNode
    pub fn update_intersection_type_node(&self, node: Node, types: NodeList) -> Node {
        if types != node.types() {
            return update_node(self.new_intersection_type_node(types), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5397 UpdateConditionalTypeNode
    pub fn update_conditional_type_node(
        &self,
        node: Node,
        check_type: Node,
        extends_type: Node,
        true_type: Node,
        false_type: Node,
    ) -> Node {
        if check_type != node.check_type()
            || extends_type != node.extends_type()
            || true_type != node.true_type()
            || false_type != node.false_type()
        {
            return update_node(
                self.new_conditional_type_node(check_type, extends_type, true_type, false_type),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5440 UpdateTypeOperatorNode
    pub fn update_type_operator_node(
        &self,
        node: Node,
        operator: SyntaxKind,
        type_node: Node,
    ) -> Node {
        if operator != node.operator() || type_node != node.type_() {
            return update_node(
                self.new_type_operator_node(operator, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5478 UpdateInferTypeNode
    pub fn update_infer_type_node(&self, node: Node, type_parameter: Node) -> Node {
        if type_parameter != node.type_parameter() {
            return update_node(self.new_infer_type_node(type_parameter), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5516 UpdateArrayTypeNode
    pub fn update_array_type_node(&self, node: Node, element_type: Node) -> Node {
        if element_type != node.element_type() {
            return update_node(self.new_array_type_node(element_type), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5556 UpdateIndexedAccessTypeNode
    pub fn update_indexed_access_type_node(
        &self,
        node: Node,
        object_type: Node,
        index_type: Node,
    ) -> Node {
        if object_type != node.object_type() || index_type != node.index_type() {
            return update_node(
                self.new_indexed_access_type_node(object_type, index_type),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5595 UpdateTypeReferenceNode
    pub fn update_type_reference_node(
        &self,
        node: Node,
        type_name: Node,
        type_arguments: NodeList,
    ) -> Node {
        if type_name != node.type_name() || type_arguments != node.type_argument_list() {
            return update_node(
                self.new_type_reference_node(type_name, type_arguments),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5636 UpdateExpressionWithTypeArguments
    pub fn update_expression_with_type_arguments(
        &self,
        node: Node,
        expression: Node,
        type_arguments: NodeList,
    ) -> Node {
        if expression != node.expression() || type_arguments != node.type_argument_list() {
            return update_node(
                self.new_expression_with_type_arguments(expression, type_arguments),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5674 UpdateLiteralTypeNode
    pub fn update_literal_type_node(&self, node: Node, literal: Node) -> Node {
        if literal != node.literal() {
            return update_node(self.new_literal_type_node(literal), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5737 UpdateTypePredicateNode
    pub fn update_type_predicate_node(
        &self,
        node: Node,
        asserts_modifier: Node,
        parameter_name: Node,
        type_node: Node,
    ) -> Node {
        if asserts_modifier != node.asserts_modifier()
            || parameter_name != node.parameter_name()
            || type_node != node.type_()
        {
            return update_node(
                self.new_type_predicate_node(asserts_modifier, parameter_name, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5778 UpdateImportAttribute
    pub fn update_import_attribute(&self, node: Node, name: Node, value: Node) -> Node {
        if name != node.name() || value != node.value() {
            return update_node(self.new_import_attribute(name, value), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:5830 UpdateImportAttributes
    pub fn update_import_attributes(
        &self,
        node: Node,
        token: SyntaxKind,
        attributes: NodeList,
        multi_line: bool,
    ) -> Node {
        if token != node.token()
            || attributes != import_attributes_list(node)
            || multi_line != node.multi_line()
        {
            return update_node(
                self.new_import_attributes(token, attributes, multi_line),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5873 UpdateTypeQueryNode
    pub fn update_type_query_node(
        &self,
        node: Node,
        expr_name: Node,
        type_arguments: NodeList,
    ) -> Node {
        if expr_name != node.expr_name() || type_arguments != node.type_argument_list() {
            return update_node(
                self.new_type_query_node(expr_name, type_arguments),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5923 UpdateMappedTypeNode
    pub fn update_mapped_type_node(
        &self,
        node: Node,
        readonly_token: Node,
        type_parameter: Node,
        name_type: Node,
        question_token: Node,
        type_node: Node,
        members: NodeList,
    ) -> Node {
        if readonly_token != node.readonly_token()
            || type_parameter != node.type_parameter()
            || name_type != node.name_type()
            || question_token != node.question_token()
            || type_node != node.type_()
            || members != node.member_list()
        {
            return update_node(
                self.new_mapped_type_node(
                    readonly_token,
                    type_parameter,
                    name_type,
                    question_token,
                    type_node,
                    members,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:5967 UpdateTypeLiteralNode
    pub fn update_type_literal_node(&self, node: Node, members: NodeList) -> Node {
        if members != node.member_list() {
            return update_node(self.new_type_literal_node(members), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6005 UpdateTupleTypeNode
    pub fn update_tuple_type_node(&self, node: Node, elements: NodeList) -> Node {
        if elements != node.element_list() {
            return update_node(self.new_tuple_type_node(elements), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6050 UpdateNamedTupleMember
    pub fn update_named_tuple_member(
        &self,
        node: Node,
        dot_dot_dot_token: Node,
        name: Node,
        question_token: Node,
        type_node: Node,
    ) -> Node {
        if dot_dot_dot_token != node.dot_dot_dot_token()
            || name != node.name()
            || question_token != node.question_token()
            || type_node != node.type_()
        {
            return update_node(
                self.new_named_tuple_member(dot_dot_dot_token, name, question_token, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6095 UpdateOptionalTypeNode
    pub fn update_optional_type_node(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(self.new_optional_type_node(type_node), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6133 UpdateRestTypeNode
    pub fn update_rest_type_node(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(self.new_rest_type_node(type_node), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6171 UpdateParenthesizedTypeNode
    pub fn update_parenthesized_type_node(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(
                self.new_parenthesized_type_node(type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6211 UpdateFunctionTypeNode
    pub fn update_function_type_node(
        &self,
        node: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_function_type_node(type_parameters, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6252 UpdateConstructorTypeNode
    pub fn update_constructor_type_node(
        &self,
        node: Node,
        modifiers: ModifierList,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_constructor_type_node(modifiers, type_parameters, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6373 UpdateTemplateLiteralTypeNode
    pub fn update_template_literal_type_node(
        &self,
        node: Node,
        head: Node,
        template_spans: NodeList,
    ) -> Node {
        if head != node.head() || template_spans != node.template_spans() {
            return update_node(
                self.new_template_literal_type_node(head, template_spans),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6413 UpdateTemplateLiteralTypeSpan
    pub fn update_template_literal_type_span(
        &self,
        node: Node,
        type_node: Node,
        literal: Node,
    ) -> Node {
        if type_node != node.type_() || literal != node.literal() {
            return update_node(
                self.new_template_literal_type_span(type_node, literal),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6455 UpdateSyntheticExpression
    pub fn update_synthetic_expression(
        &self,
        node: Node,
        type_node: TypeId,
        is_spread: bool,
        tuple_name_source: Node,
    ) -> Node {
        if type_node != synthetic_expression_type(node)
            || is_spread != node.is_spread()
            || tuple_name_source != node.tuple_name_source()
        {
            return update_node(
                self.new_synthetic_expression(type_node, is_spread, tuple_name_source),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6493 UpdatePartiallyEmittedExpression
    pub fn update_partially_emitted_expression(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_partially_emitted_expression(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6540 UpdateJsxElement
    pub fn update_jsx_element(
        &self,
        node: Node,
        opening_element: Node,
        children: NodeList,
        closing_element: Node,
    ) -> Node {
        if opening_element != node.opening_element()
            || children != node.children()
            || closing_element != node.closing_element()
        {
            return update_node(
                self.new_jsx_element(opening_element, children, closing_element),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6580 UpdateJsxAttributes
    pub fn update_jsx_attributes(&self, node: Node, properties: NodeList) -> Node {
        if properties != node.property_list() {
            return update_node(self.new_jsx_attributes(properties), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6621 UpdateJsxNamespacedName
    pub fn update_jsx_namespaced_name(&self, node: Node, namespace: Node, name: Node) -> Node {
        if namespace != node.namespace() || name != node.name() {
            return update_node(
                self.new_jsx_namespaced_name(namespace, name),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6668 UpdateJsxOpeningElement
    pub fn update_jsx_opening_element(
        &self,
        node: Node,
        tag_name: Node,
        type_arguments: NodeList,
        attributes: Node,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_arguments != node.type_argument_list()
            || attributes != node.attributes()
        {
            return update_node(
                self.new_jsx_opening_element(tag_name, type_arguments, attributes),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6711 UpdateJsxSelfClosingElement
    pub fn update_jsx_self_closing_element(
        &self,
        node: Node,
        tag_name: Node,
        type_arguments: NodeList,
        attributes: Node,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_arguments != node.type_argument_list()
            || attributes != node.attributes()
        {
            return update_node(
                self.new_jsx_self_closing_element(tag_name, type_arguments, attributes),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6754 UpdateJsxFragment
    pub fn update_jsx_fragment(
        &self,
        node: Node,
        opening_fragment: Node,
        children: NodeList,
        closing_fragment: Node,
    ) -> Node {
        if opening_fragment != node.opening_fragment()
            || children != node.children()
            || closing_fragment != node.closing_fragment()
        {
            return update_node(
                self.new_jsx_fragment(opening_fragment, children, closing_fragment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6838 UpdateJsxAttribute
    pub fn update_jsx_attribute(&self, node: Node, name: Node, initializer: Node) -> Node {
        if name != node.name() || initializer != node.initializer() {
            return update_node(
                self.new_jsx_attribute(name, initializer),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6881 UpdateJsxSpreadAttribute
    pub fn update_jsx_spread_attribute(&self, node: Node, expression: Node) -> Node {
        if expression != node.expression() {
            return update_node(
                self.new_jsx_spread_attribute(expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:6919 UpdateJsxClosingElement
    pub fn update_jsx_closing_element(&self, node: Node, tag_name: Node) -> Node {
        if tag_name != node.tag_name() {
            return update_node(self.new_jsx_closing_element(tag_name), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:6959 UpdateJsxExpression
    pub fn update_jsx_expression(
        &self,
        node: Node,
        dot_dot_dot_token: Node,
        expression: Node,
    ) -> Node {
        if dot_dot_dot_token != node.dot_dot_dot_token() || expression != node.expression() {
            return update_node(
                self.new_jsx_expression(dot_dot_dot_token, expression),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7023 UpdateSyntaxList
    // PORT: Go `core.Same` (slice identity) becomes element equality. The visitor passes the
    // unchanged children when `core.SameMap` would return the original slice.
    pub fn update_syntax_list(&self, node: Node, children: &[Node]) -> Node {
        if children != syntax_list_children(node).as_slice() {
            return update_node(self.new_syntax_list(children), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:7064 UpdateJSDoc
    pub fn update_js_doc(&self, node: Node, comment: NodeList, tags: NodeList) -> Node {
        if comment != node.comment() || tags != node.tags() {
            return update_node(self.new_js_doc(comment, tags), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:7102 UpdateJSDocTypeExpression
    pub fn update_js_doc_type_expression(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(
                self.new_js_doc_type_expression(type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7140 UpdateJSDocNonNullableType
    pub fn update_js_doc_non_nullable_type(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(
                self.new_js_doc_non_nullable_type(type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7178 UpdateJSDocNullableType
    pub fn update_js_doc_nullable_type(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(self.new_js_doc_nullable_type(type_node), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:7237 UpdateJSDocVariadicType
    pub fn update_js_doc_variadic_type(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(self.new_js_doc_variadic_type(type_node), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:7275 UpdateJSDocOptionalType
    pub fn update_js_doc_optional_type(&self, node: Node, type_node: Node) -> Node {
        if type_node != node.type_() {
            return update_node(self.new_js_doc_optional_type(type_node), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:7315 UpdateJSDocTypeTag
    pub fn update_js_doc_type_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_type_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7353 UpdateJSDocUnknownTag
    pub fn update_js_doc_unknown_tag(&self, node: Node, tag_name: Node, comment: NodeList) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_unknown_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7395 UpdateJSDocTemplateTag
    pub fn update_js_doc_template_tag(
        &self,
        node: Node,
        tag_name: Node,
        constraint: Node,
        type_parameters: NodeList,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || constraint != node.constraint()
            || type_parameters != node.type_parameter_list()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_template_tag(tag_name, constraint, type_parameters, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7438 UpdateJSDocReturnTag
    pub fn update_js_doc_return_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_return_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7476 UpdateJSDocPublicTag
    pub fn update_js_doc_public_tag(&self, node: Node, tag_name: Node, comment: NodeList) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_public_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7514 UpdateJSDocPrivateTag
    pub fn update_js_doc_private_tag(&self, node: Node, tag_name: Node, comment: NodeList) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_private_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7552 UpdateJSDocProtectedTag
    pub fn update_js_doc_protected_tag(
        &self,
        node: Node,
        tag_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_protected_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7590 UpdateJSDocReadonlyTag
    pub fn update_js_doc_readonly_tag(
        &self,
        node: Node,
        tag_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_readonly_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7628 UpdateJSDocOverrideTag
    pub fn update_js_doc_override_tag(
        &self,
        node: Node,
        tag_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_override_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7666 UpdateJSDocDeprecatedTag
    pub fn update_js_doc_deprecated_tag(
        &self,
        node: Node,
        tag_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name() || comment != node.comment() {
            return update_node(
                self.new_js_doc_deprecated_tag(tag_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7706 UpdateJSDocSeeTag
    pub fn update_js_doc_see_tag(
        &self,
        node: Node,
        tag_name: Node,
        name_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || name_expression != node.name_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_see_tag(tag_name, name_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7746 UpdateJSDocImplementsTag
    pub fn update_js_doc_implements_tag(
        &self,
        node: Node,
        tag_name: Node,
        class_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || class_name != node.class_name()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_implements_tag(tag_name, class_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7786 UpdateJSDocAugmentsTag
    pub fn update_js_doc_augments_tag(
        &self,
        node: Node,
        tag_name: Node,
        class_name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || class_name != node.class_name()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_augments_tag(tag_name, class_name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7826 UpdateJSDocSatisfiesTag
    pub fn update_js_doc_satisfies_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_satisfies_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7866 UpdateJSDocThrowsTag
    pub fn update_js_doc_throws_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_throws_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7906 UpdateJSDocThisTag
    pub fn update_js_doc_this_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_this_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7950 UpdateJSDocImportTag
    pub fn update_js_doc_import_tag(
        &self,
        node: Node,
        tag_name: Node,
        import_clause: Node,
        module_specifier: Node,
        attributes: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || import_clause != node.import_clause()
            || module_specifier != node.module_specifier()
            || attributes != node.attributes()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_import_tag(
                    tag_name,
                    import_clause,
                    module_specifier,
                    attributes,
                    comment,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:7996 UpdateJSDocCallbackTag
    pub fn update_js_doc_callback_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || name != node.name()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_callback_tag(tag_name, type_expression, name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8043 UpdateJSDocOverloadTag
    pub fn update_js_doc_overload_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_overload_tag(tag_name, type_expression, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8085 UpdateJSDocTypedefTag
    pub fn update_js_doc_typedef_tag(
        &self,
        node: Node,
        tag_name: Node,
        type_expression: Node,
        name: Node,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || type_expression != node.type_expression()
            || name != node.name()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_typedef_tag(tag_name, type_expression, name, comment),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8132 UpdateJSDocSignature
    pub fn update_js_doc_signature(
        &self,
        node: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        if type_parameters != node.type_parameter_list()
            || parameters != node.parameter_list()
            || type_node != node.type_()
        {
            return update_node(
                self.new_js_doc_signature(type_parameters, parameters, type_node),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8170 UpdateJSDocNameReference
    pub fn update_js_doc_name_reference(&self, node: Node, name: Node) -> Node {
        if name != node.name() {
            return update_node(self.new_js_doc_name_reference(name), node, self.hooks());
        }
        node
    }

    // Go: ast/ast_generated.go:8231 UpdateModuleDeclaration
    pub fn update_module_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        keyword: SyntaxKind,
        name: Node,
        body: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || keyword != node.keyword()
            || name != node.name()
            || body != node.body()
        {
            return update_node(
                self.new_module_declaration(modifiers, keyword, name, body),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8282 UpdateImportEqualsDeclaration
    pub fn update_import_equals_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        is_type_only: bool,
        name: Node,
        module_reference: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || is_type_only != node.is_type_only()
            || name != node.name()
            || module_reference != node.module_reference()
        {
            return update_node(
                self.new_import_equals_declaration(modifiers, is_type_only, name, module_reference),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8334 UpdateExportDeclaration
    pub fn update_export_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        is_type_only: bool,
        export_clause: Node,
        module_specifier: Node,
        attributes: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || is_type_only != node.is_type_only()
            || export_clause != node.export_clause()
            || module_specifier != node.module_specifier()
            || attributes != node.attributes()
        {
            return update_node(
                self.new_export_declaration(
                    modifiers,
                    is_type_only,
                    export_clause,
                    module_specifier,
                    attributes,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8382 UpdateImportTypeNode
    pub fn update_import_type_node(
        &self,
        node: Node,
        is_type_of: bool,
        argument: Node,
        attributes: Node,
        qualifier: Node,
        type_arguments: NodeList,
    ) -> Node {
        if is_type_of != node.is_type_of()
            || argument != node.argument()
            || attributes != node.attributes()
            || qualifier != node.qualifier()
            || type_arguments != node.type_argument_list()
        {
            return update_node(
                self.new_import_type_node(
                    is_type_of,
                    argument,
                    attributes,
                    qualifier,
                    type_arguments,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8430 UpdateImportClause
    pub fn update_import_clause(
        &self,
        node: Node,
        phase_modifier: SyntaxKind,
        name: Node,
        named_bindings: Node,
    ) -> Node {
        if phase_modifier != node.phase_modifier()
            || name != node.name()
            || named_bindings != node.named_bindings()
        {
            return update_node(
                self.new_import_clause(phase_modifier, name, named_bindings),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8479 UpdateImportSpecifier
    pub fn update_import_specifier(
        &self,
        node: Node,
        is_type_only: bool,
        property_name: Node,
        name: Node,
    ) -> Node {
        if is_type_only != node.is_type_only()
            || property_name != node.property_name()
            || name != node.name()
        {
            return update_node(
                self.new_import_specifier(is_type_only, property_name, name),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8546 UpdateJSDocLink
    // PORT: Go `text []string` and `core.Same`; ts_ast stores the link text as one string, compared by value.
    pub fn update_js_doc_link(&self, node: Node, name: Node, text: &str) -> Node {
        if name != node.name() || text != node.text() {
            // PORT: Go passes the `[]string` text; here the one joined string.
            return update_node(
                self.new_js_doc_link(name, vec![text.to_string()]),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8590 UpdateJSDocLinkPlain
    // PORT: Go `text []string` and `core.Same`; ts_ast stores the link text as one string, compared by value.
    pub fn update_js_doc_link_plain(&self, node: Node, name: Node, text: &str) -> Node {
        if name != node.name() || text != node.text() {
            // PORT: Go passes the `[]string` text; here the one joined string.
            return update_node(
                self.new_js_doc_link_plain(name, vec![text.to_string()]),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8634 UpdateJSDocLinkCode
    // PORT: Go `text []string` and `core.Same`; ts_ast stores the link text as one string, compared by value.
    pub fn update_js_doc_link_code(&self, node: Node, name: Node, text: &str) -> Node {
        if name != node.name() || text != node.text() {
            // PORT: Go passes the `[]string` text; here the one joined string.
            return update_node(
                self.new_js_doc_link_code(name, vec![text.to_string()]),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8686 UpdateTypeParameterDeclaration
    pub fn update_type_parameter_declaration(
        &self,
        node: Node,
        modifiers: ModifierList,
        name: Node,
        constraint: Node,
        expression: Node,
        default_type: Node,
    ) -> Node {
        if modifiers != node.modifiers()
            || name != node.name()
            || constraint != node.constraint()
            || expression != node.expression()
            || default_type != node.default_type()
        {
            return update_node(
                self.new_type_parameter_declaration(
                    modifiers,
                    name,
                    constraint,
                    expression,
                    default_type,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8734 UpdateSyntheticReferenceExpression
    pub fn update_synthetic_reference_expression(
        &self,
        node: Node,
        expression: Node,
        this_arg: Node,
    ) -> Node {
        if expression != node.expression() || this_arg != node.this_arg() {
            return update_node(
                self.new_synthetic_reference_expression(expression, this_arg),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8780 UpdateJSDocTypeLiteral
    // PORT: Go `core.Same` (slice identity) becomes element equality. The visitor passes the
    // unchanged children when `core.SameMap` would return the original slice.
    pub fn update_js_doc_type_literal(
        &self,
        node: Node,
        jsdoc_property_tags: &[Node],
        is_array_type: bool,
    ) -> Node {
        if jsdoc_property_tags != node.js_doc_property_tags().as_slice()
            || is_array_type != node.is_array_type()
        {
            return update_node(
                self.new_js_doc_type_literal(jsdoc_property_tags, is_array_type),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast_generated.go:8827 UpdateJSDocParameterOrPropertyTag
    pub fn update_js_doc_parameter_or_property_tag(
        &self,
        node: Node,
        tag_name: Node,
        name: Node,
        is_bracketed: bool,
        type_expression: Node,
        is_name_first: bool,
        comment: NodeList,
    ) -> Node {
        if tag_name != node.tag_name()
            || name != node.name()
            || is_bracketed != node.is_bracketed()
            || type_expression != node.type_expression()
            || is_name_first != node.is_name_first()
            || comment != node.comment()
        {
            return update_node(
                self.new_js_doc_parameter_or_property_tag(
                    node.kind(),
                    tag_name,
                    name,
                    is_bracketed,
                    type_expression,
                    is_name_first,
                    comment,
                ),
                node,
                self.hooks(),
            );
        }
        node
    }

    // Go: ast/ast.go:2693 UpdateSourceFile
    pub fn update_source_file(
        &self,
        node: Node,
        statements: NodeList,
        end_of_file_token: Node,
    ) -> Node {
        if statements != node.statement_list() || end_of_file_token != node.end_of_file_token() {
            let updated = self.new_source_file_from(node, statements, end_of_file_token);
            return update_node(updated, node, self.hooks());
        }
        node
    }
}

/// Go `node.AsImportAttributes().Attributes`.
// PORT: `Node::attribute_list` returns the same handle but gives NIL for other
// kinds; this keeps Go's panic from `AsImportAttributes`.
pub(crate) fn import_attributes_list(node: Node) -> NodeList {
    crate::ast::synthetic::list_of!(node, |d| match d {
        ts_ast::NodeData::ImportAttributes(d) => Some(Some(AnyList::Nodes(&d.attributes))),
        _ => None,
    })
    .unwrap_or_else(|| panic!("AsImportAttributes called on {:?}", node.kind()))
}
