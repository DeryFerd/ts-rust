//! More Go `ast.NodeFactory` constructors (`ast/ast_generated.go`) that
//! `ast/factory.rs` does not have. `ast/update.rs` and `ast/clone.rs` call
//! them.
//!
//! The argument rules are the same as in `ast/factory.rs`: Go `*Node` is
//! `Node`, Go `*NodeList` is `NodeList`, Go `*ModifierList` is
//! `ModifierList`, and Go `nil` is the `NIL` value of each. Nodes go to the
//! factory target (synthetic arena or the store of the parsed file).

use crate::astdata::NodeData as D;
use crate::prelude::*;

/// Go `TokenFlagsNone` in astdata form.
const NO_TOKEN_FLAGS: crate::astdata::TokenFlags = crate::astdata::TokenFlags(0);

impl NodeFactory {
    // Go: ast/ast_generated.go:875 NewDoStatement
    pub fn new_do_statement(&self, statement: Node, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::DoStatement,
            D::DoStatement(Box::new(crate::astdata::DoStatementData {
                expression: self.id(expression),
                flow_node: None,
                statement: self.id(statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:920 NewWhileStatement
    pub fn new_while_statement(&self, expression: Node, statement: Node) -> Node {
        self.new_node(
            SyntaxKind::WhileStatement,
            D::WhileStatement(Box::new(crate::astdata::WhileStatementData {
                expression: self.id(expression),
                flow_node: None,
                statement: self.id(statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:968 NewForStatement
    pub fn new_for_statement(
        &self,
        initializer: Node,
        condition: Node,
        incrementor: Node,
        statement: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::ForStatement,
            D::ForStatement(Box::new(crate::astdata::ForStatementData {
                condition: self.oid(condition),
                flow_node: None,
                incrementor: self.oid(incrementor),
                initializer: self.oid(initializer),
                locals: crate::astdata::SymbolTable,
                next_container: None,
                statement: self.id(statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1024 NewForInOrOfStatement
    pub fn new_for_in_or_of_statement(
        &self,
        kind: SyntaxKind,
        await_modifier: Node,
        initializer: Node,
        expression: Node,
        statement: Node,
    ) -> Node {
        self.new_node(
            kind,
            D::ForInOrOfStatement(Box::new(crate::astdata::ForInOrOfStatementData {
                await_modifier: self.oid(await_modifier),
                expression: self.id(expression),
                flow_node: None,
                initializer: self.id(initializer),
                locals: crate::astdata::SymbolTable,
                next_container: None,
                statement: self.id(statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1072 NewBreakStatement
    pub fn new_break_statement(&self, label: Node) -> Node {
        self.new_node(
            SyntaxKind::BreakStatement,
            D::BreakStatement(Box::new(crate::astdata::BreakStatementData {
                flow_node: None,
                label: self.oid(label),
            })),
        )
    }

    // Go: ast/ast_generated.go:1110 NewContinueStatement
    pub fn new_continue_statement(&self, label: Node) -> Node {
        self.new_node(
            SyntaxKind::ContinueStatement,
            D::ContinueStatement(Box::new(crate::astdata::ContinueStatementData {
                flow_node: None,
                label: self.oid(label),
            })),
        )
    }

    // Go: ast/ast_generated.go:1189 NewWithStatement
    pub fn new_with_statement(&self, expression: Node, statement: Node) -> Node {
        self.new_node(
            SyntaxKind::WithStatement,
            D::WithStatement(Box::new(crate::astdata::WithStatementData {
                expression: self.id(expression),
                flow_node: None,
                statement: self.id(statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1235 NewSwitchStatement
    pub fn new_switch_statement(&self, expression: Node, case_block: Node) -> Node {
        self.new_node(
            SyntaxKind::SwitchStatement,
            D::SwitchStatement(Box::new(crate::astdata::SwitchStatementData {
                case_block: self.id(case_block),
                expression: self.id(expression),
                flow_node: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1281 NewCaseBlock
    pub fn new_case_block(&self, clauses: NodeList) -> Node {
        self.new_node(
            SyntaxKind::CaseBlock,
            D::CaseBlock(Box::new(crate::astdata::CaseBlockData {
                clauses: self.req_list(clauses),
                locals: crate::astdata::SymbolTable,
                next_container: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1326 NewCaseOrDefaultClause
    pub fn new_case_or_default_clause(
        &self,
        kind: SyntaxKind,
        expression: Node,
        statements: NodeList,
    ) -> Node {
        self.new_node(
            kind,
            D::CaseOrDefaultClause(Box::new(crate::astdata::CaseOrDefaultClauseData {
                expression: self.id(expression),
                fallthrough_flow_node: None,
                statements: self.req_list(statements),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1375 NewThrowStatement
    pub fn new_throw_statement(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ThrowStatement,
            D::ThrowStatement(Box::new(crate::astdata::ThrowStatementData {
                expression: self.id(expression),
                flow_node: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1420 NewTryStatement
    pub fn new_try_statement(
        &self,
        try_block: Node,
        catch_clause: Node,
        finally_block: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::TryStatement,
            D::TryStatement(Box::new(crate::astdata::TryStatementData {
                catch_clause: self.oid(catch_clause),
                finally_block: self.oid(finally_block),
                flow_node: None,
                try_block: self.id(try_block),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1469 NewCatchClause
    pub fn new_catch_clause(&self, variable_declaration: Node, block: Node) -> Node {
        self.new_node(
            SyntaxKind::CatchClause,
            D::CatchClause(Box::new(crate::astdata::CatchClauseData {
                block: self.id(block),
                locals: crate::astdata::SymbolTable,
                next_container: None,
                variable_declaration: self.oid(variable_declaration),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1507 NewDebuggerStatement
    pub fn new_debugger_statement(&self) -> Node {
        self.new_node(
            SyntaxKind::DebuggerStatement,
            D::DebuggerStatement(Box::new(crate::astdata::DebuggerStatementData {
                flow_node: None,
            })),
        )
    }

    // Go: ast/ast_generated.go:1530 NewLabeledStatement
    pub fn new_labeled_statement(&self, label: Node, statement: Node) -> Node {
        self.new_node(
            SyntaxKind::LabeledStatement,
            D::LabeledStatement(Box::new(crate::astdata::LabeledStatementData {
                flow_node: None,
                label: self.id(label),
                statement: self.id(statement),
            })),
        )
    }

    // Go: ast/ast_generated.go:1799 NewBindingPattern
    pub fn new_binding_pattern(&self, kind: SyntaxKind, elements: NodeList) -> Node {
        self.new_node(
            kind,
            D::BindingPattern(Box::new(crate::astdata::BindingPatternData {
                elements: self.req_list(elements),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1907 NewBindingElement
    pub fn new_binding_element(
        &self,
        dot_dot_dot_token: Node,
        property_name: Node,
        name: Node,
        initializer: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::BindingElement,
            D::BindingElement(Box::new(crate::astdata::BindingElementData {
                dot_dot_dot_token: self.oid(dot_dot_dot_token),
                flow_node: None,
                initializer: self.oid(initializer),
                local_symbol: None,
                property_name: self.oid(property_name),
                symbol: None,
                facts: 0,
                name: self.oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:1956 NewMissingDeclaration
    pub fn new_missing_declaration(&self, modifiers: ModifierList) -> Node {
        self.new_node(
            SyntaxKind::MissingDeclaration,
            D::MissingDeclaration(Box::new(crate::astdata::MissingDeclarationData {
                flow_node: None,
                symbol: None,
                modifiers: self.mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:2272 NewJSTypeAliasDeclaration
    pub fn new_js_type_alias_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        type_node: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsTypeAliasDeclaration,
            D::TypeAliasDeclaration(Box::new(crate::astdata::TypeAliasDeclarationData {
                flow_node: None,
                local_symbol: None,
                locals: crate::astdata::SymbolTable,
                next_container: None,
                symbol: None,
                type_: self.id(type_node),
                type_parameters: self.opt_list(type_parameters),
                modifiers: self.mods(modifiers),
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2534 NewJSImportDeclaration
    pub fn new_js_import_declaration(
        &self,
        modifiers: ModifierList,
        import_clause: Node,
        module_specifier: Node,
        attributes: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsImportDeclaration,
            D::ImportDeclaration(Box::new(crate::astdata::ImportDeclarationData {
                attributes: self.oid(attributes),
                flow_node: None,
                import_clause: self.oid(import_clause),
                module_specifier: self.id(module_specifier),
                symbol: None,
                facts: 0,
                modifiers: self.mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:2647 NewNamespaceImport
    pub fn new_namespace_import(&self, name: Node) -> Node {
        self.new_node(
            SyntaxKind::NamespaceImport,
            D::NamespaceImport(Box::new(crate::astdata::NamespaceImportData {
                local_symbol: None,
                symbol: None,
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2785 NewNamespaceExportDeclaration
    pub fn new_namespace_export_declaration(&self, modifiers: ModifierList, name: Node) -> Node {
        self.new_node(
            SyntaxKind::NamespaceExportDeclaration,
            D::NamespaceExportDeclaration(Box::new(
                crate::astdata::NamespaceExportDeclarationData {
                    flow_node: None,
                    symbol: None,
                    modifiers: self.mods(modifiers),
                    name: self.id(name),
                },
            )),
        )
    }

    // Go: ast/ast_generated.go:2829 NewNamespaceExport
    pub fn new_namespace_export(&self, name: Node) -> Node {
        self.new_node(
            SyntaxKind::NamespaceExport,
            D::NamespaceExport(Box::new(crate::astdata::NamespaceExportData {
                symbol: None,
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3488 NewSemicolonClassElement
    pub fn new_semicolon_class_element(&self) -> Node {
        self.new_node(
            SyntaxKind::SemicolonClassElement,
            D::SemicolonClassElement(Box::new(crate::astdata::SemicolonClassElementData {
                symbol: None,
            })),
        )
    }

    // Go: ast/ast_generated.go:3516 NewClassStaticBlockDeclaration
    pub fn new_class_static_block_declaration(&self, modifiers: ModifierList, body: Node) -> Node {
        self.new_node(
            SyntaxKind::ClassStaticBlockDeclaration,
            D::ClassStaticBlockDeclaration(Box::new(
                crate::astdata::ClassStaticBlockDeclarationData {
                    body: self.id(body),
                    locals: crate::astdata::SymbolTable,
                    next_container: None,
                    return_flow_node: None,
                    symbol: None,
                    facts: 0,
                    modifiers: self.mods(modifiers),
                },
            )),
        )
    }

    // Go: ast/ast_generated.go:3554 NewOmittedExpression
    pub fn new_omitted_expression(&self) -> Node {
        self.new_node(
            SyntaxKind::OmittedExpression,
            D::OmittedExpression(Box::new(crate::astdata::OmittedExpressionData)),
        )
    }

    // Go: ast/ast_generated.go:3821 NewPostfixUnaryExpression
    pub fn new_postfix_unary_expression(&self, operand: Node, operator: SyntaxKind) -> Node {
        self.new_node(
            SyntaxKind::PostfixUnaryExpression,
            D::PostfixUnaryExpression(Box::new(crate::astdata::PostfixUnaryExpressionData {
                operand: self.id(operand),
                operator,
            })),
        )
    }

    // Go: ast/ast_generated.go:4359 NewMetaProperty
    pub fn new_meta_property(&self, keyword_token: SyntaxKind, name: Node) -> Node {
        self.new_node(
            SyntaxKind::MetaProperty,
            D::MetaProperty(Box::new(crate::astdata::MetaPropertyData {
                flow_node: None,
                keyword_token,
                facts: 0,
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:4482 NewTemplateExpression
    pub fn new_template_expression(&self, head: Node, template_spans: NodeList) -> Node {
        self.new_node(
            SyntaxKind::TemplateExpression,
            D::TemplateExpression(Box::new(crate::astdata::TemplateExpressionData {
                head: self.id(head),
                template_spans: self.req_list(template_spans),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:4527 NewTemplateSpan
    pub fn new_template_span(&self, expression: Node, literal: Node) -> Node {
        self.new_node(
            SyntaxKind::TemplateSpan,
            D::TemplateSpan(Box::new(crate::astdata::TemplateSpanData {
                expression: self.id(expression),
                literal: self.id(literal),
            })),
        )
    }

    // Go: ast/ast_generated.go:4756 NewSpreadAssignment
    pub fn new_spread_assignment(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::SpreadAssignment,
            D::SpreadAssignment(Box::new(crate::astdata::SpreadAssignmentData {
                expression: self.id(expression),
                symbol: None,
            })),
        )
    }

    // Go: ast/ast_generated.go:4855 NewShorthandPropertyAssignment
    pub fn new_shorthand_property_assignment(
        &self,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        equals_token: Node,
        object_assignment_initializer: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::ShorthandPropertyAssignment,
            D::ShorthandPropertyAssignment(Box::new(
                crate::astdata::ShorthandPropertyAssignmentData {
                    equals_token: self.oid(equals_token),
                    object_assignment_initializer: self.oid(object_assignment_initializer),
                    postfix_token: self.oid(postfix_token),
                    symbol: None,
                    type_: self.oid(type_node),
                    facts: 0,
                    modifiers: self.mods(modifiers),
                    name: self.id(name),
                },
            )),
        )
    }

    // Go: ast/ast_generated.go:6311 NewPartiallyEmittedExpression
    pub fn new_partially_emitted_expression(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::PartiallyEmittedExpression,
            D::PartiallyEmittedExpression(Box::new(
                crate::astdata::PartiallyEmittedExpressionData {
                    expression: self.id(expression),
                },
            )),
        )
    }

    // Go: ast/ast_generated.go:6356 NewJsxElement
    pub fn new_jsx_element(
        &self,
        opening_element: Node,
        children: NodeList,
        closing_element: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsxElement,
            D::JsxElement(Box::new(crate::astdata::JsxElementData {
                children: self.req_list(children),
                closing_element: self.id(closing_element),
                opening_element: self.id(opening_element),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:6398 NewJsxAttributes
    pub fn new_jsx_attributes(&self, properties: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsxAttributes,
            D::JsxAttributes(Box::new(crate::astdata::JsxAttributesData {
                properties: self.req_list(properties),
                symbol: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:6438 NewJsxNamespacedName
    pub fn new_jsx_namespaced_name(&self, namespace: Node, name: Node) -> Node {
        self.new_node(
            SyntaxKind::JsxNamespacedName,
            D::JsxNamespacedName(Box::new(crate::astdata::JsxNamespacedNameData {
                namespace: self.id(namespace),
                facts: 0,
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:6484 NewJsxOpeningElement
    pub fn new_jsx_opening_element(
        &self,
        tag_name: Node,
        type_arguments: NodeList,
        attributes: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsxOpeningElement,
            D::JsxOpeningElement(Box::new(crate::astdata::JsxOpeningElementData {
                attributes: self.id(attributes),
                tag_name: self.id(tag_name),
                type_arguments: self.opt_list(type_arguments),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:6527 NewJsxSelfClosingElement
    pub fn new_jsx_self_closing_element(
        &self,
        tag_name: Node,
        type_arguments: NodeList,
        attributes: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsxSelfClosingElement,
            D::JsxSelfClosingElement(Box::new(crate::astdata::JsxSelfClosingElementData {
                attributes: self.id(attributes),
                tag_name: self.id(tag_name),
                type_arguments: self.opt_list(type_arguments),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:6570 NewJsxFragment
    pub fn new_jsx_fragment(
        &self,
        opening_fragment: Node,
        children: NodeList,
        closing_fragment: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsxFragment,
            D::JsxFragment(Box::new(crate::astdata::JsxFragmentData {
                children: self.req_list(children),
                closing_fragment: self.id(closing_fragment),
                opening_fragment: self.id(opening_fragment),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:6609 NewJsxOpeningFragment
    pub fn new_jsx_opening_fragment(&self) -> Node {
        self.new_node(
            SyntaxKind::JsxOpeningFragment,
            D::JsxOpeningFragment(Box::new(crate::astdata::JsxOpeningFragmentData)),
        )
    }

    // Go: ast/ast_generated.go:6630 NewJsxClosingFragment
    pub fn new_jsx_closing_fragment(&self) -> Node {
        self.new_node(
            SyntaxKind::JsxClosingFragment,
            D::JsxClosingFragment(Box::new(crate::astdata::JsxClosingFragmentData)),
        )
    }

    // Go: ast/ast_generated.go:6655 NewJsxAttribute
    pub fn new_jsx_attribute(&self, name: Node, initializer: Node) -> Node {
        self.new_node(
            SyntaxKind::JsxAttribute,
            D::JsxAttribute(Box::new(crate::astdata::JsxAttributeData {
                initializer: self.oid(initializer),
                symbol: None,
                facts: 0,
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:6700 NewJsxSpreadAttribute
    pub fn new_jsx_spread_attribute(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::JsxSpreadAttribute,
            D::JsxSpreadAttribute(Box::new(crate::astdata::JsxSpreadAttributeData {
                expression: self.id(expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:6738 NewJsxClosingElement
    pub fn new_jsx_closing_element(&self, tag_name: Node) -> Node {
        self.new_node(
            SyntaxKind::JsxClosingElement,
            D::JsxClosingElement(Box::new(crate::astdata::JsxClosingElementData {
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:6777 NewJsxExpression
    pub fn new_jsx_expression(&self, dot_dot_dot_token: Node, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::JsxExpression,
            D::JsxExpression(Box::new(crate::astdata::JsxExpressionData {
                dot_dot_dot_token: self.oid(dot_dot_dot_token),
                expression: self.oid(expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:6817 NewJsxText
    pub fn new_jsx_text(
        &self,
        text: impl Into<String>,
        contains_only_trivia_white_spaces: bool,
    ) -> Node {
        self.new_text_node(
            SyntaxKind::JsxText,
            D::JsxText(Box::new(crate::astdata::JsxTextData {
                contains_only_trivia_white_spaces,
                text: text.into(),
                token_flags: NO_TOKEN_FLAGS,
            })),
        )
    }

    // Go: ast/ast_generated.go:6882 NewJSDoc
    pub fn new_js_doc(&self, comment: NodeList, tags: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDoc,
            D::JsDoc(Box::new(crate::astdata::JsDocData {
                comment: self.req_list(comment),
                tags: self.opt_list(tags),
            })),
        )
    }

    // Go: ast/ast_generated.go:6921 NewJSDocTypeExpression
    pub fn new_js_doc_type_expression(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocTypeExpression,
            D::JsDocTypeExpression(Box::new(crate::astdata::JsDocTypeExpressionData {
                type_: self.id(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:6959 NewJSDocNonNullableType
    pub fn new_js_doc_non_nullable_type(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocNonNullableType,
            D::JsDocNonNullableType(Box::new(crate::astdata::JsDocNonNullableTypeData {
                type_: self.id(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:6997 NewJSDocNullableType
    pub fn new_js_doc_nullable_type(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocNullableType,
            D::JsDocNullableType(Box::new(crate::astdata::JsDocNullableTypeData {
                type_: self.id(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:7034 NewJSDocAllType
    pub fn new_js_doc_all_type(&self) -> Node {
        self.new_node(
            SyntaxKind::JsDocAllType,
            D::JsDocAllType(Box::new(crate::astdata::JsDocAllTypeData)),
        )
    }

    // Go: ast/ast_generated.go:7056 NewJSDocVariadicType
    pub fn new_js_doc_variadic_type(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocVariadicType,
            D::JsDocVariadicType(Box::new(crate::astdata::JsDocVariadicTypeData {
                type_: self.id(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:7094 NewJSDocOptionalType
    pub fn new_js_doc_optional_type(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocOptionalType,
            D::JsDocOptionalType(Box::new(crate::astdata::JsDocOptionalTypeData {
                type_: self.id(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:7132 NewJSDocTypeTag
    pub fn new_js_doc_type_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocTypeTag,
            D::JsDocTypeTag(Box::new(crate::astdata::JsDocTypeTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.id(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7171 NewJSDocUnknownTag
    pub fn new_js_doc_unknown_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocUnknownTag,
            D::JsDocUnknownTag(Box::new(crate::astdata::JsDocUnknownTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7211 NewJSDocTemplateTag
    pub fn new_js_doc_template_tag(
        &self,
        tag_name: Node,
        constraint: Node,
        type_parameters: NodeList,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocTemplateTag,
            D::JsDocTemplateTag(Box::new(crate::astdata::JsDocTemplateTagData {
                comment: self.opt_list(comment),
                constraint: self.id(constraint),
                tag_name: self.id(tag_name),
                type_parameters: self.req_list(type_parameters),
            })),
        )
    }

    // Go: ast/ast_generated.go:7255 NewJSDocReturnTag
    pub fn new_js_doc_return_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocReturnTag,
            D::JsDocReturnTag(Box::new(crate::astdata::JsDocReturnTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.oid(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7294 NewJSDocPublicTag
    pub fn new_js_doc_public_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocPublicTag,
            D::JsDocPublicTag(Box::new(crate::astdata::JsDocPublicTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7332 NewJSDocPrivateTag
    pub fn new_js_doc_private_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocPrivateTag,
            D::JsDocPrivateTag(Box::new(crate::astdata::JsDocPrivateTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7370 NewJSDocProtectedTag
    pub fn new_js_doc_protected_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocProtectedTag,
            D::JsDocProtectedTag(Box::new(crate::astdata::JsDocProtectedTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7408 NewJSDocReadonlyTag
    pub fn new_js_doc_readonly_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocReadonlyTag,
            D::JsDocReadonlyTag(Box::new(crate::astdata::JsDocReadonlyTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7446 NewJSDocOverrideTag
    pub fn new_js_doc_override_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocOverrideTag,
            D::JsDocOverrideTag(Box::new(crate::astdata::JsDocOverrideTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7484 NewJSDocDeprecatedTag
    pub fn new_js_doc_deprecated_tag(&self, tag_name: Node, comment: NodeList) -> Node {
        self.new_node(
            SyntaxKind::JsDocDeprecatedTag,
            D::JsDocDeprecatedTag(Box::new(crate::astdata::JsDocDeprecatedTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7523 NewJSDocSeeTag
    pub fn new_js_doc_see_tag(
        &self,
        tag_name: Node,
        name_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocSeeTag,
            D::JsDocSeeTag(Box::new(crate::astdata::JsDocSeeTagData {
                comment: self.opt_list(comment),
                name_expression: self.id(name_expression),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7563 NewJSDocImplementsTag
    pub fn new_js_doc_implements_tag(
        &self,
        tag_name: Node,
        class_name: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocImplementsTag,
            D::JsDocImplementsTag(Box::new(crate::astdata::JsDocImplementsTagData {
                class_name: self.id(class_name),
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7603 NewJSDocAugmentsTag
    pub fn new_js_doc_augments_tag(
        &self,
        tag_name: Node,
        class_name: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocAugmentsTag,
            D::JsDocAugmentsTag(Box::new(crate::astdata::JsDocAugmentsTagData {
                class_name: self.id(class_name),
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7643 NewJSDocSatisfiesTag
    pub fn new_js_doc_satisfies_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocSatisfiesTag,
            D::JsDocSatisfiesTag(Box::new(crate::astdata::JsDocSatisfiesTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.id(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7683 NewJSDocThrowsTag
    pub fn new_js_doc_throws_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocThrowsTag,
            D::JsDocThrowsTag(Box::new(crate::astdata::JsDocThrowsTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.oid(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7723 NewJSDocThisTag
    pub fn new_js_doc_this_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocThisTag,
            D::JsDocThisTag(Box::new(crate::astdata::JsDocThisTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.id(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7765 NewJSDocImportTag
    pub fn new_js_doc_import_tag(
        &self,
        tag_name: Node,
        import_clause: Node,
        module_specifier: Node,
        attributes: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocImportTag,
            D::JsDocImportTag(Box::new(crate::astdata::JsDocImportTagData {
                attributes: self.oid(attributes),
                comment: self.opt_list(comment),
                import_clause: self.oid(import_clause),
                module_specifier: self.id(module_specifier),
                tag_name: self.id(tag_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7812 NewJSDocCallbackTag
    pub fn new_js_doc_callback_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        name: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocCallbackTag,
            D::JsDocCallbackTag(Box::new(crate::astdata::JsDocCallbackTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.id(type_expression),
                name: self.oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7860 NewJSDocOverloadTag
    pub fn new_js_doc_overload_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocOverloadTag,
            D::JsDocOverloadTag(Box::new(crate::astdata::JsDocOverloadTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.id(type_expression),
            })),
        )
    }

    // Go: ast/ast_generated.go:7901 NewJSDocTypedefTag
    pub fn new_js_doc_typedef_tag(
        &self,
        tag_name: Node,
        type_expression: Node,
        name: Node,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocTypedefTag,
            D::JsDocTypedefTag(Box::new(crate::astdata::JsDocTypedefTagData {
                comment: self.opt_list(comment),
                tag_name: self.id(tag_name),
                type_expression: self.oid(type_expression),
                name: self.oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:7950 NewJSDocSignature
    pub fn new_js_doc_signature(
        &self,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocSignature,
            D::JsDocSignature(Box::new(crate::astdata::JsDocSignatureData {
                full_signature: None,
                locals: crate::astdata::SymbolTable,
                next_container: None,
                parameters: self.req_list(parameters),
                symbol: None,
                type_: self.oid(type_node),
                type_parameters: self.opt_list(type_parameters),
            })),
        )
    }

    // Go: ast/ast_generated.go:7990 NewJSDocNameReference
    pub fn new_js_doc_name_reference(&self, name: Node) -> Node {
        self.new_node(
            SyntaxKind::JsDocNameReference,
            D::JsDocNameReference(Box::new(crate::astdata::JsDocNameReferenceData {
                name: self.id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:8345 NewJSDocText
    pub fn new_js_doc_text(&self, text: Vec<String>) -> Node {
        self.new_text_node(
            SyntaxKind::JsDocText,
            D::JsDocText(Box::new(crate::astdata::JsDocTextData { text })),
        )
    }

    // Go: ast/ast_generated.go:8369 NewJSDocLink
    pub fn new_js_doc_link(&self, name: Node, text: Vec<String>) -> Node {
        self.new_text_node(
            SyntaxKind::JsDocLink,
            D::JsDocLink(Box::new(crate::astdata::JsDocLinkData {
                name: self.oid(name),
                text,
            })),
        )
    }

    // Go: ast/ast_generated.go:8413 NewJSDocLinkPlain
    pub fn new_js_doc_link_plain(&self, name: Node, text: Vec<String>) -> Node {
        self.new_text_node(
            SyntaxKind::JsDocLinkPlain,
            D::JsDocLinkPlain(Box::new(crate::astdata::JsDocLinkPlainData {
                name: self.oid(name),
                text,
            })),
        )
    }

    // Go: ast/ast_generated.go:8457 NewJSDocLinkCode
    pub fn new_js_doc_link_code(&self, name: Node, text: Vec<String>) -> Node {
        self.new_text_node(
            SyntaxKind::JsDocLinkCode,
            D::JsDocLinkCode(Box::new(crate::astdata::JsDocLinkCodeData {
                name: self.oid(name),
                text,
            })),
        )
    }

    // Go: ast/ast_generated.go:8558 NewSyntheticReferenceExpression
    pub fn new_synthetic_reference_expression(&self, expression: Node, this_arg: Node) -> Node {
        self.new_node(
            SyntaxKind::SyntheticReferenceExpression,
            D::SyntheticReferenceExpression(Box::new(
                crate::astdata::SyntheticReferenceExpressionData {
                    expression: self.id(expression),
                    this_arg: self.id(this_arg),
                },
            )),
        )
    }

    // Go: ast/ast_generated.go:8604 NewJSDocTypeLiteral
    // PORT: a Go nil or empty slice is `None`; Go code only ranges over it.
    pub fn new_js_doc_type_literal(
        &self,
        jsdoc_property_tags: &[Node],
        is_array_type: bool,
    ) -> Node {
        self.new_node(
            SyntaxKind::JsDocTypeLiteral,
            D::JsDocTypeLiteral(Box::new(crate::astdata::JsDocTypeLiteralData {
                is_array_type,
                js_doc_property_tags: (!jsdoc_property_tags.is_empty())
                    .then(|| jsdoc_property_tags.iter().map(|&t| self.id(t)).collect()),
                symbol: None,
            })),
        )
    }

    // Go: ast/ast_generated.go:8647 NewJSDocParameterOrPropertyTag
    pub fn new_js_doc_parameter_or_property_tag(
        &self,
        kind: SyntaxKind,
        tag_name: Node,
        name: Node,
        is_bracketed: bool,
        type_expression: Node,
        is_name_first: bool,
        comment: NodeList,
    ) -> Node {
        self.new_node(
            kind,
            D::JsDocParameterOrPropertyTag(Box::new(
                crate::astdata::JsDocParameterOrPropertyTagData {
                    comment: self.opt_list(comment),
                    is_bracketed,
                    is_name_first,
                    tag_name: self.id(tag_name),
                    type_expression: self.oid(type_expression),
                    name: self.id(name),
                },
            )),
        )
    }
}
