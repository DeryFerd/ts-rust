use crate::prelude::*;

// Port of printer/printer.go lines 3690 to 4691: declarations, module
// references, JSX, clauses, property assignments, enum members, JSDoc and
// top-level nodes.
//
// PORT: every Go `*ast.X` parameter is a `Node`. Go `node.AsX()` conversions
// are dropped. Go `(*Printer).emitX` method values passed to `emitList` are
// `Printer::emit_x` (`fn(&mut Printer, Node)`).
// PORT: Go variadic `greatestEnd(end, nodes...)` is
// `greatest_end(end, &[&a, &b])`, where each element is a `Node`,
// `NodeList`, `ModifierList` or `TextRange` behind the `tryGetEnd` trait of
// printer/utilities.rs.

//
// Declarations
//

impl Printer {
    // Go: printer.go:3693 emitVariableDeclaration
    pub(crate) fn emit_variable_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_binding_name(node.name());
        self.emit_punctuation_node(node.exclamation_token());
        self.emit_type_annotation(node.type_());
        let type_node = self.emit_context.get_type_node(node.name());
        self.emit_initializer(
            node.initializer(),
            greatest_end(node.name().end(), &[&node.type_(), &type_node]),
            node,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:3702 emitVariableDeclarationNode
    pub(crate) fn emit_variable_declaration_node(&mut self, node: Node) {
        self.emit_variable_declaration(node);
    }

    // Go: printer.go:3706 emitVariableDeclarationList
    pub(crate) fn emit_variable_declaration_list(&mut self, node: Node) {
        let state = self.enter_node(node);
        if is_var_let(node) {
            self.write_keyword("let");
        } else if is_var_const(node) {
            self.write_keyword("const");
        } else if is_var_using(node) {
            self.write_keyword("using");
        } else if is_var_await_using(node) {
            self.write_keyword("await");
            self.write_space();
            self.write_keyword("using");
        } else {
            self.write_keyword("var");
        }
        self.write_space();
        self.emit_list(
            Printer::emit_variable_declaration_node,
            node,
            node.declarations(),
            ListFormat::VARIABLE_DECLARATION_LIST,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:3727 emitFunctionDeclaration
    pub(crate) fn emit_function_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.generate_name_if_needed(node.name());
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("function");
        self.emit_token_node(node.asterisk_token());
        self.write_space();
        let name = node.name();
        if name != Node::NIL {
            self.emit_identifier_name(name);
        }
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(node.body());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer.go:3747 emitClassDeclaration
    pub(crate) fn emit_class_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.generate_name_if_needed(node.name());
        let pos = self.emit_modifier_list(node, node.modifiers(), true /*allowDecorators*/);
        self.emit_token(SyntaxKind::ClassKeyword, pos, WriteKind::KEYWORD, node);
        if node.name() != Node::NIL {
            self.write_space();
            self.emit_identifier_name(node.name());
        }
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.emit_type_parameters(node, node.type_parameter_list());
        self.emit_list(
            Printer::emit_heritage_clause_node,
            node,
            node.heritage_clauses(),
            ListFormat::CLASS_HERITAGE_CLAUSES,
        );
        self.write_space();
        self.write_punctuation("{");
        self.push_name_generation_scope(node);
        self.generate_all_member_names(node.member_list());
        self.emit_list(
            Printer::emit_class_element,
            node,
            node.member_list(),
            ListFormat::CLASS_MEMBERS,
        );
        self.pop_name_generation_scope(node);
        self.write_punctuation("}");
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer.go:3771 emitInterfaceDeclaration
    pub(crate) fn emit_interface_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("interface");
        self.write_space();
        self.emit_binding_identifier(node.name());
        self.emit_type_parameters(node, node.type_parameter_list());
        self.emit_list(
            Printer::emit_heritage_clause_node,
            node,
            node.heritage_clauses(),
            ListFormat::HERITAGE_CLAUSES,
        );
        self.write_space();
        self.write_punctuation("{");
        self.push_name_generation_scope(node);
        self.generate_all_member_names(node.member_list());
        self.emit_list(
            Printer::emit_type_element,
            node,
            node.member_list(),
            ListFormat::INTERFACE_MEMBERS,
        );
        self.pop_name_generation_scope(node);
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer.go:3789 emitTypeAliasDeclaration
    pub(crate) fn emit_type_alias_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("type");
        self.write_space();
        self.emit_binding_identifier(node.name());
        self.emit_type_parameters(node, node.type_parameter_list());
        self.write_space();
        self.write_punctuation("=");
        self.write_space();
        self.emit_type_node_outside_extends(node.type_());
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:3804 emitEnumDeclaration
    pub(crate) fn emit_enum_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("enum");
        self.write_space();
        self.emit_binding_identifier(node.name());
        self.write_space();
        self.write_punctuation("{");
        self.emit_list(
            Printer::emit_enum_member_node,
            node,
            node.member_list(),
            ListFormat::ENUM_MEMBERS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer.go:3817 emitModuleDeclaration
    pub(crate) fn emit_module_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        if node.keyword() != SyntaxKind::GlobalKeyword {
            self.write_keyword(if node.keyword() == SyntaxKind::NamespaceKeyword {
                "namespace"
            } else {
                "module"
            });
            self.write_space();
        }
        self.emit_module_name(node.name());
        let mut body = node.body();
        while body != Node::NIL && is_module_declaration(body) {
            let module = body;
            self.write_punctuation(".");
            self.emit_nested_module_name(module.name());
            body = module.body();
        }
        if body == Node::NIL {
            self.write_trailing_semicolon();
        } else {
            self.write_space();
            self.emit_module_block(body);
        }
        self.exit_node(node, state);
    }

    // Go: printer.go:3841 emitModuleBlock
    pub(crate) fn emit_module_block(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.generate_names(node);
        self.emit_token(
            SyntaxKind::OpenBraceToken,
            node.pos(),
            WriteKind::PUNCTUATION,
            node,
        );
        let format = if self.is_empty_block(node, node.statement_list())
            || self.should_emit_on_single_line(node)
        {
            ListFormat::SINGLE_LINE_BLOCK_STATEMENTS
        } else {
            ListFormat::MULTI_LINE_BLOCK_STATEMENTS
        };
        self.emit_list(Printer::emit_statement, node, node.statement_list(), format);
        self.emit_token_ex(
            SyntaxKind::CloseBraceToken,
            node.statement_list().end(),
            WriteKind::PUNCTUATION,
            node,
            if format.intersects(ListFormat::MULTI_LINE) {
                TokenEmitFlags::INDENT_LEADING_COMMENTS
            } else {
                TokenEmitFlags::NONE
            },
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:3853 emitCaseBlock
    pub(crate) fn emit_case_block(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token(
            SyntaxKind::OpenBraceToken,
            node.pos(),
            WriteKind::PUNCTUATION,
            node,
        );
        self.emit_list(
            Printer::emit_case_or_default_clause_node,
            node,
            node.clauses(),
            ListFormat::CASE_BLOCK_CLAUSES,
        );
        self.emit_token_ex(
            SyntaxKind::CloseBraceToken,
            node.clauses().end(),
            WriteKind::PUNCTUATION,
            node,
            TokenEmitFlags::INDENT_LEADING_COMMENTS,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:3861 emitImportEqualsDeclaration
    pub(crate) fn emit_import_equals_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        let pos = self.emit_token(
            SyntaxKind::ImportKeyword,
            greatest_end(node.pos(), &[&node.modifiers()]),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        if node.is_type_only() {
            self.emit_token(SyntaxKind::TypeKeyword, pos, WriteKind::KEYWORD, node);
            self.write_space();
        }
        self.emit_binding_identifier(node.name());
        self.write_space();
        self.emit_token(
            SyntaxKind::EqualsToken,
            node.name().end(),
            WriteKind::PUNCTUATION,
            node,
        );
        self.write_space();
        self.emit_module_reference(node.module_reference());
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:3879 emitModuleReference
    pub(crate) fn emit_module_reference(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::Identifier => self.emit_identifier_reference(node),
            SyntaxKind::QualifiedName => self.emit_qualified_name(node),
            SyntaxKind::ExternalModuleReference => self.emit_external_module_reference(node),
            kind => panic!("unhandled ModuleReference: {kind:?}"),
        }
    }

    // Go: printer.go:3892 emitImportDeclaration
    pub(crate) fn emit_import_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.emit_token(
            SyntaxKind::ImportKeyword,
            greatest_end(node.pos(), &[&node.modifiers()]),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        if node.import_clause() != Node::NIL {
            self.emit_import_clause(node.import_clause());
            self.write_space();
            self.emit_token(
                SyntaxKind::FromKeyword,
                node.import_clause().end(),
                WriteKind::KEYWORD,
                node,
            );
            self.write_space();
        }
        self.emit_expression(node.module_specifier(), OperatorPrecedence::LOWEST);
        if node.attributes() != Node::NIL {
            self.write_space();
            self.emit_import_attributes(node.attributes());
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:3912 emitImportClause
    pub(crate) fn emit_import_clause(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.phase_modifier() != SyntaxKind::Unknown {
            self.emit_token(node.phase_modifier(), node.pos(), WriteKind::KEYWORD, node);
            self.write_space();
        }
        let name = node.name();
        if name != Node::NIL {
            self.emit_binding_identifier(node.name());
            if node.named_bindings() != Node::NIL {
                self.emit_token(
                    SyntaxKind::CommaToken,
                    name.end(),
                    WriteKind::PUNCTUATION,
                    node,
                );
                self.write_space();
            }
        }
        self.emit_named_import_bindings(node.named_bindings());
        self.exit_node(node, state);
    }

    // Go: printer.go:3929 emitNamespaceImport
    pub(crate) fn emit_namespace_import(&mut self, node: Node) {
        let state = self.enter_node(node);
        let pos = self.emit_token(
            SyntaxKind::AsteriskToken,
            node.pos(),
            WriteKind::PUNCTUATION,
            node,
        );
        self.write_space();
        self.emit_token(SyntaxKind::AsKeyword, pos, WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_binding_identifier(node.name());
        self.exit_node(node, state);
    }

    // Go: printer.go:3939 emitNamedImports
    pub(crate) fn emit_named_imports(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Printer::emit_import_specifier_node,
            node,
            node.element_list(),
            ListFormat::NAMED_IMPORTS_OR_EXPORTS_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer.go:3947 emitNamedImportBindings
    pub(crate) fn emit_named_import_bindings(&mut self, node: Node) {
        if node == Node::NIL {
            return;
        }
        match node.kind() {
            SyntaxKind::NamespaceImport => self.emit_namespace_import(node),
            SyntaxKind::NamedImports => self.emit_named_imports(node),
            kind => panic!("unhandled NamedImportBindings: {kind:?}"),
        }
    }

    // Go: printer.go:3961 emitImportSpecifier
    pub(crate) fn emit_import_specifier(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.is_type_only() {
            self.write_keyword("type");
            self.write_space();
        }
        if node.property_name() != Node::NIL {
            self.emit_module_export_name(node.property_name());
            self.write_space();
            self.emit_token(
                SyntaxKind::AsKeyword,
                node.property_name().end(),
                WriteKind::KEYWORD,
                node,
            );
            self.write_space();
        }
        self.emit_binding_identifier(node.name());
        self.exit_node(node, state);
    }

    // Go: printer.go:3977 emitImportSpecifierNode
    pub(crate) fn emit_import_specifier_node(&mut self, node: Node) {
        self.emit_import_specifier(node);
    }

    // Go: printer.go:3981 emitExportAssignment
    pub(crate) fn emit_export_assignment(&mut self, node: Node) {
        let state = self.enter_node(node);
        let next_pos = self.emit_token(
            SyntaxKind::ExportKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        if node.is_export_equals() {
            self.emit_token(SyntaxKind::EqualsToken, next_pos, WriteKind::OPERATOR, node);
        } else {
            self.emit_token(
                SyntaxKind::DefaultKeyword,
                next_pos,
                WriteKind::KEYWORD,
                node,
            );
        }
        self.write_space();
        if node.is_export_equals() {
            self.emit_expression(node.expression(), OperatorPrecedence::ASSIGNMENT);
        } else {
            // parenthesize `class` and `function` expressions so as not to conflict with exported `class` and `function` declarations
            let expr =
                get_leftmost_expression(node.expression(), false /*stopAtCallExpressions*/);
            if is_class_expression(expr) || is_function_expression(expr) {
                self.emit_expression(node.expression(), OperatorPrecedence::PARENTHESES);
            } else {
                self.emit_expression(node.expression(), OperatorPrecedence::ASSIGNMENT);
            }
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:4006 emitExportDeclaration
    pub(crate) fn emit_export_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        let mut pos = self.emit_token(
            SyntaxKind::ExportKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        if node.is_type_only() {
            pos = self.emit_token(SyntaxKind::TypeKeyword, pos, WriteKind::KEYWORD, node);
            self.write_space();
        }
        if node.export_clause() != Node::NIL {
            self.emit_named_export_bindings(node.export_clause());
        } else {
            pos = self.emit_token(SyntaxKind::AsteriskToken, pos, WriteKind::PUNCTUATION, node);
        }
        if node.module_specifier() != Node::NIL {
            self.write_space();
            self.emit_token(
                SyntaxKind::FromKeyword,
                greatest_end(pos, &[&node.export_clause()]),
                WriteKind::KEYWORD,
                node,
            );
            self.write_space();
            self.emit_expression(node.module_specifier(), OperatorPrecedence::LOWEST);
        }
        if node.attributes() != Node::NIL {
            self.write_space();
            self.emit_import_attributes(node.attributes());
        }
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:4034 emitImportAttributes
    pub(crate) fn emit_import_attributes(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token(node.token(), node.pos(), WriteKind::KEYWORD, node);
        self.write_space();
        // PORT: Go `node.AsImportAttributes().Attributes` is the
        // `attribute_list()` accessor of ast/node.rs.
        self.emit_list(
            Printer::emit_import_attribute_node,
            node,
            node.attribute_list(),
            ListFormat::IMPORT_ATTRIBUTES,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:4042 emitImportAttribute
    pub(crate) fn emit_import_attribute(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_import_attribute_name(node.name());
        self.write_punctuation(":");
        self.write_space();
        let value = node.value();
        if !self
            .emit_context
            .emit_flags(node.value())
            .intersects(EmitFlags::NO_LEADING_COMMENTS)
        {
            let comment_range = self.emit_context.comment_range(value);
            self.emit_trailing_comments(comment_range.pos(), CommentSeparator::AFTER);
        }
        self.emit_expression(value, OperatorPrecedence::DISALLOW_COMMA);
        self.exit_node(node, state);
    }

    // Go: printer.go:4056 emitImportAttributeNode
    pub(crate) fn emit_import_attribute_node(&mut self, node: Node) {
        self.emit_import_attribute(node);
    }

    // Go: printer.go:4060 emitNamespaceExportDeclaration
    pub(crate) fn emit_namespace_export_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        let mut pos = self.emit_token(
            SyntaxKind::ExportKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        pos = self.emit_token(SyntaxKind::AsKeyword, pos, WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_token(SyntaxKind::NamespaceKeyword, pos, WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_binding_identifier(node.name());
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer.go:4073 emitNamespaceExport
    pub(crate) fn emit_namespace_export(&mut self, node: Node) {
        let state = self.enter_node(node);
        let pos = self.emit_token(
            SyntaxKind::AsteriskToken,
            node.pos(),
            WriteKind::PUNCTUATION,
            node,
        );
        self.write_space();
        self.emit_token(SyntaxKind::AsKeyword, pos, WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_module_export_name(node.name());
        self.exit_node(node, state);
    }

    // Go: printer.go:4083 emitNamedExports
    pub(crate) fn emit_named_exports(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Printer::emit_export_specifier_node,
            node,
            node.element_list(),
            ListFormat::NAMED_IMPORTS_OR_EXPORTS_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer.go:4091 emitNamedExportBindings
    pub(crate) fn emit_named_export_bindings(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::NamespaceExport => self.emit_namespace_export(node),
            SyntaxKind::NamedExports => self.emit_named_exports(node),
            kind => panic!("unhandled NamedExportBindings: {kind:?}"),
        }
    }

    // Go: printer.go:4102 emitExportSpecifier
    pub(crate) fn emit_export_specifier(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.is_type_only() {
            self.write_keyword("type");
            self.write_space();
        }
        if node.property_name() != Node::NIL {
            self.emit_module_export_name(node.property_name());
            self.write_space();
            self.emit_token(
                SyntaxKind::AsKeyword,
                node.property_name().end(),
                WriteKind::KEYWORD,
                node,
            );
            self.write_space();
        }
        self.emit_module_export_name(node.name());
        self.exit_node(node, state);
    }

    // Go: printer.go:4118 emitExportSpecifierNode
    pub(crate) fn emit_export_specifier_node(&mut self, node: Node) {
        self.emit_export_specifier(node);
    }

    // Go: printer.go:4122 emitEmbeddedStatement
    pub(crate) fn emit_embedded_statement(&mut self, parent_node: Node, node: Node) {
        if is_block(node)
            || self.should_emit_on_single_line(parent_node)
            || self.options.preserve_source_newlines
                && self.get_leading_line_terminator_count(parent_node, node, ListFormat::NONE) == 0
        {
            self.write_space();
            self.emit_statement(node);
        } else {
            self.write_line();
            self.increase_indent();
            if node.kind() == SyntaxKind::EmptyStatement {
                self.emit_empty_statement(node, true /*isEmbeddedStatement*/);
            } else {
                self.emit_statement(node);
            }
            self.decrease_indent();
        }
    }

    // Go: printer.go:4140 emitStatement
    pub(crate) fn emit_statement(&mut self, node: Node) {
        match node.kind() {
            // Statements
            SyntaxKind::Block => self.emit_block(node),
            SyntaxKind::EmptyStatement => {
                self.emit_empty_statement(node, false /*isEmbeddedStatement*/)
            }
            SyntaxKind::VariableStatement => self.emit_variable_statement(node),
            SyntaxKind::ExpressionStatement => self.emit_expression_statement(node),
            SyntaxKind::IfStatement => self.emit_if_statement(node),
            SyntaxKind::DoStatement => self.emit_do_statement(node),
            SyntaxKind::WhileStatement => self.emit_while_statement(node),
            SyntaxKind::ForStatement => self.emit_for_statement(node),
            SyntaxKind::ForInStatement => self.emit_for_in_statement(node),
            SyntaxKind::ForOfStatement => self.emit_for_of_statement(node),
            SyntaxKind::ContinueStatement => self.emit_continue_statement(node),
            SyntaxKind::BreakStatement => self.emit_break_statement(node),
            SyntaxKind::ReturnStatement => self.emit_return_statement(node),
            SyntaxKind::WithStatement => self.emit_with_statement(node),
            SyntaxKind::SwitchStatement => self.emit_switch_statement(node),
            SyntaxKind::LabeledStatement => self.emit_labeled_statement(node),
            SyntaxKind::ThrowStatement => self.emit_throw_statement(node),
            SyntaxKind::TryStatement => self.emit_try_statement(node),
            SyntaxKind::DebuggerStatement => self.emit_debugger_statement(node),
            SyntaxKind::NotEmittedStatement => self.emit_not_emitted_statement(node),

            // Declaration Statements
            SyntaxKind::FunctionDeclaration => self.emit_function_declaration(node),
            SyntaxKind::ClassDeclaration => self.emit_class_declaration(node),
            SyntaxKind::InterfaceDeclaration => self.emit_interface_declaration(node),
            SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration => {
                self.emit_type_alias_declaration(node);
            }
            SyntaxKind::EnumDeclaration => self.emit_enum_declaration(node),
            SyntaxKind::ModuleDeclaration => self.emit_module_declaration(node),
            SyntaxKind::MissingDeclaration => {}

            // Import/Export Statements
            SyntaxKind::NamespaceExportDeclaration => self.emit_namespace_export_declaration(node),
            SyntaxKind::ImportEqualsDeclaration => self.emit_import_equals_declaration(node),
            SyntaxKind::ImportDeclaration => self.emit_import_declaration(node),
            SyntaxKind::ExportAssignment => self.emit_export_assignment(node),
            SyntaxKind::ExportDeclaration => self.emit_export_declaration(node),

            kind => panic!("unhandled statement: {kind:?}"),
        }
    }
}

//
// Module references
//

impl Printer {
    // Go: printer.go:4221 emitExternalModuleReference
    pub(crate) fn emit_external_module_reference(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("require");
        self.write_punctuation("(");
        self.emit_expression(node.expression(), OperatorPrecedence::DISALLOW_COMMA);
        self.write_punctuation(")");
        self.exit_node(node, state);
    }
}

//
// JSX
//

impl Printer {
    // Go: printer.go:4234 emitJsxElement
    pub(crate) fn emit_jsx_element(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_jsx_opening_element(node.opening_element());
        self.emit_list(
            Printer::emit_jsx_child,
            node,
            node.children(),
            ListFormat::JSX_ELEMENT_OR_FRAGMENT_CHILDREN,
        );
        self.emit_jsx_closing_element(node.closing_element());
        self.exit_node(node, state);
    }

    // Go: printer.go:4242 emitJsxSelfClosingElement
    pub(crate) fn emit_jsx_self_closing_element(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("<");
        self.emit_jsx_tag_name(node.tag_name());
        self.emit_type_arguments(node, node.type_argument_list());
        self.write_space();
        self.emit_jsx_attributes(node.attributes());
        self.write_punctuation("/>");
        self.exit_node(node, state);
    }

    // Go: printer.go:4253 emitJsxFragment
    pub(crate) fn emit_jsx_fragment(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_jsx_opening_fragment(node.opening_fragment());
        self.emit_list(
            Printer::emit_jsx_child,
            node,
            node.children(),
            ListFormat::JSX_ELEMENT_OR_FRAGMENT_CHILDREN,
        );
        self.emit_jsx_closing_fragment(node.closing_fragment());
        self.exit_node(node, state);
    }

    // Go: printer.go:4261 emitJsxOpeningElement
    pub(crate) fn emit_jsx_opening_element(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("<");
        let indented = self.write_line_separators_and_indent_before(node.tag_name(), node);
        self.emit_jsx_tag_name(node.tag_name());
        self.emit_type_arguments(node, node.type_argument_list());
        if node.attributes().properties().len() > 0 {
            self.write_space();
        }
        self.emit_jsx_attributes(node.attributes());
        self.write_line_separators_after(node.attributes(), node);
        self.decrease_indent_if(indented);
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    // Go: printer.go:4277 emitJsxClosingElement
    pub(crate) fn emit_jsx_closing_element(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("</");
        self.emit_jsx_tag_name(node.tag_name());
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    // Go: printer.go:4285 emitJsxOpeningFragment
    pub(crate) fn emit_jsx_opening_fragment(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("<");
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    // Go: printer.go:4292 emitJsxClosingFragment
    pub(crate) fn emit_jsx_closing_fragment(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("</");
        self.write_punctuation(">");
        self.exit_node(node, state);
    }

    // Go: printer.go:4299 emitJsxText
    pub(crate) fn emit_jsx_text(&mut self, node: Node) {
        let state = self.enter_node(node);
        // TODO(rbuckton): Should this be using `getLiteralTextOfNode` instead?
        self.write_literal(node.text());
        self.exit_node(node, state);
    }

    // Go: printer.go:4306 emitJsxAttributes
    pub(crate) fn emit_jsx_attributes(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_list(
            Printer::emit_jsx_attribute_like,
            node,
            node.property_list(),
            ListFormat::JSX_ELEMENT_ATTRIBUTES,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:4312 emitJsxAttribute
    pub(crate) fn emit_jsx_attribute(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_jsx_attribute_name(node.name());
        if node.initializer() != Node::NIL {
            self.write_punctuation("=");
            self.emit_jsx_attribute_value(node.initializer());
        }
        self.exit_node(node, state);
    }

    // Go: printer.go:4322 emitJsxSpreadAttribute
    pub(crate) fn emit_jsx_spread_attribute(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("{...");
        self.emit_expression(node.expression(), OperatorPrecedence::LOWEST);
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer.go:4330 emitJsxAttributeLike
    pub(crate) fn emit_jsx_attribute_like(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::JsxAttribute => self.emit_jsx_attribute(node),
            SyntaxKind::JsxSpreadAttribute => self.emit_jsx_spread_attribute(node),
            kind => panic!("unhandled JsxAttributeLike: {kind:?}"),
        }
    }

    // Go: printer.go:4341 emitJsxExpression
    pub(crate) fn emit_jsx_expression(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.expression() != Node::NIL
            || !self.comments_disabled
                && !node_is_synthesized(node)
                && self.has_comments_at_position(node.pos())
        {
            // preserve empty expressions if they contain comments!
            let indented = self.current_source_file != Node::NIL
                && !node_is_synthesized(node)
                && get_lines_between_positions(self.current_source_file, node.pos(), node.end())
                    != 0;
            self.increase_indent_if(indented);
            let end = self.emit_token(
                SyntaxKind::OpenBraceToken,
                node.pos(),
                WriteKind::PUNCTUATION,
                node,
            );
            self.emit_token_node(node.dot_dot_dot_token());
            if node.expression() != Node::NIL {
                self.emit_expression(node.expression(), OperatorPrecedence::DISALLOW_COMMA);
            }
            self.emit_token(
                SyntaxKind::CloseBraceToken,
                greatest_end(end, &[&node.expression(), &node.dot_dot_dot_token()]),
                WriteKind::PUNCTUATION,
                node,
            );
            self.decrease_indent_if(indented);
        }
        self.exit_node(node, state);
    }

    // Go: printer.go:4357 emitJsxNamespacedName
    pub(crate) fn emit_jsx_namespaced_name(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_identifier_name(node.namespace());
        self.write_punctuation(":");
        self.emit_identifier_name(node.name());
        self.exit_node(node, state);
    }

    // Go: printer.go:4365 emitJsxChild
    pub(crate) fn emit_jsx_child(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::JsxText => self.emit_jsx_text(node),
            SyntaxKind::JsxExpression => self.emit_jsx_expression(node),
            SyntaxKind::JsxElement => self.emit_jsx_element(node),
            SyntaxKind::JsxSelfClosingElement => self.emit_jsx_self_closing_element(node),
            SyntaxKind::JsxFragment => self.emit_jsx_fragment(node),
            kind => panic!("unhandled JsxChild: {kind:?}"),
        }
    }

    // Go: printer.go:4382 emitJsxTagName
    pub(crate) fn emit_jsx_tag_name(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::Identifier => self.emit_identifier_reference(node),
            SyntaxKind::ThisKeyword => self.emit_keyword_expression(node),
            SyntaxKind::JsxNamespacedName => self.emit_jsx_namespaced_name(node),
            SyntaxKind::PropertyAccessExpression => self.emit_property_access_expression(node),
            kind => panic!("unhandled JsxTagName: {kind:?}"),
        }
    }

    // Go: printer.go:4397 emitJsxAttributeName
    pub(crate) fn emit_jsx_attribute_name(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::Identifier => self.emit_identifier_name(node),
            SyntaxKind::JsxNamespacedName => self.emit_jsx_namespaced_name(node),
            kind => panic!("unhandled JsxAttributeName: {kind:?}"),
        }
    }

    // Go: printer.go:4408 emitJsxAttributeValue
    pub(crate) fn emit_jsx_attribute_value(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::StringLiteral => self.emit_string_literal(node),
            SyntaxKind::JsxExpression => self.emit_jsx_expression(node),
            SyntaxKind::JsxElement => self.emit_jsx_element(node),
            SyntaxKind::JsxSelfClosingElement => self.emit_jsx_self_closing_element(node),
            SyntaxKind::JsxFragment => self.emit_jsx_fragment(node),
            _ => self.emit_expression(node, OperatorPrecedence::LOWEST),
        }
    }
}

//
// Clauses
//

impl Printer {
    // Go: printer.go:4429 emitCaseOrDefaultClauseStatements
    pub(crate) fn emit_case_or_default_clause_statements(&mut self, node: Node, colon_pos: i32) {
        let statements = node.statement_list();
        let emit_as_single_statement = statements.nodes().len() == 1
            // treat synthesized nodes as located on the same line for emit purposes
            && (self.current_source_file == Node::NIL
                || node_is_synthesized(node)
                || node_is_synthesized(statements.nodes().get(0))
                || range_start_positions_are_on_same_line(
                    node.loc(),
                    statements.nodes().get(0).loc(),
                    self.current_source_file,
                ));

        let mut format = ListFormat::CASE_OR_DEFAULT_CLAUSE_STATEMENTS;
        if emit_as_single_statement {
            // When emitting as a single statement, use writeToken (no comments) for the colon
            // to avoid duplicating trailing comments that will be picked up by the statement list.
            self.write_token_text(SyntaxKind::ColonToken, WriteKind::PUNCTUATION, colon_pos);
            self.write_space();
            format = format.without(ListFormat::MULTI_LINE | ListFormat::INDENTED);
        } else {
            self.emit_token(
                SyntaxKind::ColonToken,
                colon_pos,
                WriteKind::PUNCTUATION,
                node,
            );
        }

        self.emit_list(Printer::emit_statement, node, statements, format);
    }

    // Go: printer.go:4451 emitCaseClause
    pub(crate) fn emit_case_clause(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token(
            SyntaxKind::CaseKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();
        self.emit_expression(node.expression(), OperatorPrecedence::LOWEST);
        self.emit_case_or_default_clause_statements(node, node.expression().end());
        self.exit_node(node, state);
    }

    // Go: printer.go:4460 emitDefaultClause
    pub(crate) fn emit_default_clause(&mut self, node: Node) {
        let state = self.enter_node(node);
        let pos = self.emit_token(
            SyntaxKind::DefaultKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.emit_case_or_default_clause_statements(node, pos);
        self.exit_node(node, state);
    }

    // Go: printer.go:4467 emitCaseOrDefaultClauseNode
    pub(crate) fn emit_case_or_default_clause_node(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::CaseClause => self.emit_case_clause(node),
            SyntaxKind::DefaultClause => self.emit_default_clause(node),
            kind => panic!("unhandled CaseOrDefaultClause: {kind:?}"),
        }
    }

    // Go: printer.go:4478 emitHeritageClause
    pub(crate) fn emit_heritage_clause(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_space();
        self.emit_token(node.token(), node.pos(), WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_list(
            Printer::emit_expression_with_type_arguments_node,
            node,
            node.types(),
            ListFormat::HERITAGE_CLAUSE_TYPES,
        );
        self.exit_node(node, state);
    }

    // Go: printer.go:4487 emitHeritageClauseNode
    pub(crate) fn emit_heritage_clause_node(&mut self, node: Node) {
        self.emit_heritage_clause(node);
    }

    // Go: printer.go:4491 emitCatchClause
    pub(crate) fn emit_catch_clause(&mut self, node: Node) {
        let state = self.enter_node(node);
        let open_paren_pos = self.emit_token(
            SyntaxKind::CatchKeyword,
            node.pos(),
            WriteKind::KEYWORD,
            node,
        );
        self.write_space();

        if node.variable_declaration() != Node::NIL {
            self.emit_token(
                SyntaxKind::OpenParenToken,
                open_paren_pos,
                WriteKind::PUNCTUATION,
                node,
            );
            self.emit_variable_declaration(node.variable_declaration());
            self.emit_token(
                SyntaxKind::CloseParenToken,
                node.variable_declaration().end(),
                WriteKind::PUNCTUATION,
                node,
            );
            self.write_space();
        }

        self.emit_block(node.block());
        self.exit_node(node, state);
    }
}

//
// Property assignments
//

impl Printer {
    // Go: printer.go:4511 emitPropertyAssignment
    pub(crate) fn emit_property_assignment(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_property_name(node.name());
        self.write_punctuation(":");
        self.write_space();
        // This is to ensure that we emit comment in the following case:
        //      For example:
        //          obj = {
        //              id: /*comment1*/ ()=>void
        //          }
        // "comment1" is not considered to be leading comment for node.initializer
        // but rather a trailing comment on the previous node.
        let initializer = node.initializer();
        if !self
            .emit_context
            .emit_flags(initializer)
            .intersects(EmitFlags::NO_LEADING_COMMENTS)
        {
            let comment_range = self.emit_context.comment_range(initializer);
            self.emit_trailing_comments(comment_range.pos(), CommentSeparator::AFTER);
        }
        self.emit_expression(initializer, OperatorPrecedence::DISALLOW_COMMA);
        self.exit_node(node, state);
    }

    // Go: printer.go:4532 emitShorthandPropertyAssignment
    pub(crate) fn emit_shorthand_property_assignment(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_property_name(node.name());
        if node.object_assignment_initializer() != Node::NIL {
            self.write_space();
            self.write_punctuation("=");
            self.write_space();
            self.emit_expression(
                node.object_assignment_initializer(),
                OperatorPrecedence::DISALLOW_COMMA,
            );
        }
        self.exit_node(node, state);
    }

    // Go: printer.go:4544 emitSpreadAssignment
    pub(crate) fn emit_spread_assignment(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.expression() != Node::NIL {
            self.emit_token(
                SyntaxKind::DotDotDotToken,
                node.pos(),
                WriteKind::PUNCTUATION,
                node,
            );
            self.emit_expression(node.expression(), OperatorPrecedence::DISALLOW_COMMA);
        }
        self.exit_node(node, state);
    }
}

//
// Enum
//

impl Printer {
    // Go: printer.go:4557 emitEnumMember
    pub(crate) fn emit_enum_member(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_property_name(node.name());
        self.emit_initializer(node.initializer(), node.name().end(), node);
        self.exit_node(node, state);
    }

    // Go: printer.go:4564 emitEnumMemberNode
    pub(crate) fn emit_enum_member_node(&mut self, node: Node) {
        self.emit_enum_member(node);
    }
}

//
// JSDoc
//

impl Printer {
    // Go: printer.go:4572 emitJSDocNode
    pub(crate) fn emit_js_doc_node(&mut self, _node: Node) {
        // !!!
        panic!("not implemented");
    }
}

//
// Top-level nodes
//

impl Printer {
    // Go: printer.go:4581 emitShebangIfNeeded
    pub(crate) fn emit_shebang_if_needed(&mut self, node: Node) {
        if node_is_synthesized(node) {
            return;
        }
        let shebang = get_shebang(source_file_text(node));
        if !shebang.is_empty() {
            self.write_comment(&shebang);
            self.write_line();
        }
    }

    // Go: printer.go:4592 emitPrologueDirectives
    pub(crate) fn emit_prologue_directives(&mut self, statements: NodeList) -> i32 {
        for (i, statement) in statements.nodes().iter().enumerate() {
            if is_prologue_directive(statement) {
                self.write_line();
                self.emit_statement(statement);
            } else {
                return i as i32;
            }
        }
        statements.nodes().len() as i32
    }

    // Go: printer.go:4604 emitHelpers
    pub(crate) fn emit_helpers(&mut self, node: Node) -> bool {
        let mut helpers_emitted = false;
        let source_file = self.current_source_file;
        let should_skip = self.options.no_emit_helpers
            || (source_file != Node::NIL
                && self.emit_context.has_recorded_external_helpers(source_file));
        let mut helpers = self.emit_context.get_emit_helpers(node).to_vec();
        if !helpers.is_empty() {
            // PORT: Go `slices.SortStableFunc`; `sort_by` is stable.
            helpers.sort_by(|x, y| compare_emit_helpers(x, y).cmp(&0));
            for helper in &helpers {
                if !helper.scoped {
                    // Skip the helper if it can be skipped and the noEmitHelpers compiler
                    // option is set, or if it can be imported and the importHelpers compiler
                    // option is set.
                    if should_skip {
                        continue;
                    }
                }
                if let Some(text_callback) = &helper.text_callback {
                    // PORT: Go passes the `p.makeFileLevelOptimisticUniqueName`
                    // func value. Here a closure calls the Printer method.
                    let text = text_callback(&mut |name: &str| {
                        self.make_file_level_optimistic_unique_name(name)
                    });
                    self.write_lines(&text);
                } else {
                    self.write_lines(&helper.text);
                }
                helpers_emitted = true;
            }
        }

        helpers_emitted
    }

    // Go: printer.go:4632 emitSourceFile
    pub(crate) fn emit_source_file(&mut self, node: Node) {
        let saved_current_source_file = self.current_source_file;
        let saved_comments_disabled = self.comments_disabled;
        self.current_source_file = node;

        self.write_line();

        let statements = node.statement_list();
        self.push_name_generation_scope(node);
        self.generate_all_names(statements);

        let mut index = 0;
        let info = source_file_info(node);
        // PORT: Go `var state *commentState` starts nil; both branches assign it.
        let state;
        if info.script_kind != ScriptKind::JSON {
            self.emit_shebang_if_needed(node);
            index = self.emit_prologue_directives(statements);
            if !self.writer().is_at_start_of_line() {
                self.write_line();
            }
            state = self.emit_detached_comments_before_statement_list(node, statements.loc());
            self.emit_helpers(node);
            if info.is_declaration_file {
                self.emit_triple_slash_directives(node);
            }
        } else {
            state = self.emit_detached_comments_before_statement_list(node, statements.loc());
        }

        // !!! Emit triple-slash directives
        self.emit_list_range(
            Printer::emit_statement,
            node,
            statements,
            ListFormat::MULTI_LINE,
            index,
            -1, /*count*/
        );
        self.pop_name_generation_scope(node);
        self.emit_detached_comments_after_statement_list(node, statements.loc(), state);
        self.current_source_file = saved_current_source_file;
        self.comments_disabled = saved_comments_disabled;
    }

    // Go: printer.go:4674 emitTripleSlashDirectives
    pub(crate) fn emit_triple_slash_directives(&mut self, node: Node) {
        let info = source_file_info(node);
        self.emit_directive("path", &info.referenced_files);
        self.emit_directive("types", &info.type_reference_directives);
        self.emit_directive("lib", &info.lib_reference_directives);
    }

    // Go: printer.go:4680 emitDirective
    pub(crate) fn emit_directive(&mut self, kind: &str, refs: &[FileReference]) {
        for ref_ in refs {
            let mut resolution_mode = String::new();
            if ref_.resolution_mode != ResolutionMode::NONE {
                resolution_mode = format!(
                    "resolution-mode=\"{}\" ",
                    if ref_.resolution_mode == ResolutionMode::ESM {
                        "import"
                    } else {
                        "require"
                    }
                );
            }
            self.write_comment(&format!(
                "/// <reference {}=\"{}\" {}{}/>",
                kind,
                ref_.file_name,
                resolution_mode,
                if ref_.preserve {
                    "preserve=\"true\" "
                } else {
                    ""
                }
            ));
            self.write_line();
        }
    }
}
