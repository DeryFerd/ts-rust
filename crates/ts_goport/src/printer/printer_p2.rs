//! Printer part 2: printer.go 1345 to 2454. Signature elements, type members,
//! types and binding patterns.
//!
//! PORT: Go methods take typed node pointers (`*ast.TypeParameterDeclaration`,
//! ...). Here every method takes a `Node` handle. Go `node.AsX().Field` becomes
//! the matching `Node` accessor. Go `ListFormat`, `WriteKind`,
//! `tokenEmitFlags` and `EmitFlags` constants use the crate `go_enum!` and
//! `go_flags!` style (`LFModifiers` -> `ListFormat::MODIFIERS`,
//! `WriteKindKeyword` -> `WriteKind::KEYWORD`, `tefNoComments` ->
//! `TokenEmitFlags::NO_COMMENTS`, `EFNoSourceMap` -> `EmitFlags::NO_SOURCE_MAP`).
//! Go `PrintHandlers` is embedded in `Printer`; here it is the field
//! `print_handlers`.

use crate::gostd::debug::kind_string;
use crate::prelude::*;
use crate::printer::*;

//
// Signature elements
//

impl Printer {
    // Go: printer/printer.go:1363 emitModifierList
    pub(crate) fn emit_modifier_list(
        &mut self,
        parent_node: Node,
        modifiers: ModifierList,
        allow_decorators: bool,
    ) -> i32 {
        if modifiers.is_nil() || modifiers.nodes().is_empty() {
            return parent_node.pos();
        }

        if modifiers.nodes().iter().all(is_modifier) {
            // if all modifier-likes are `Modifier`, simply emit the list as modifiers.
            self.emit_list(
                Printer::emit_keyword_node,
                parent_node,
                modifiers.node_list(),
                ListFormat::MODIFIERS,
            );
        } else if modifiers.nodes().iter().all(is_decorator) {
            if !allow_decorators {
                return parent_node.pos();
            }

            // if all modifier-likes are `Decorator`, simply emit the list as decorators.
            self.emit_list(
                Printer::emit_modifier_like,
                parent_node,
                modifiers.node_list(),
                ListFormat::DECORATORS,
            );
        } else {
            if let Some(f) = self.print_handlers.on_before_emit_node_list.as_mut() {
                f(modifiers.node_list());
            }

            // partition modifiers into contiguous chunks of `Modifier` or `Decorator` so as to
            // use consistent formatting for each chunk
            #[derive(Clone, Copy, PartialEq, Eq)]
            enum Mode {
                None,
                Modifiers,
                Decorators,
            }

            let nodes = modifiers.nodes().to_vec();
            let mut last_mode = Mode::None;
            let mut mode = Mode::None;
            let mut start = 0usize;
            let mut pos = 0usize;

            while start < nodes.len() {
                while pos < nodes.len() {
                    let last_modifier = nodes[pos];
                    if is_decorator(last_modifier) {
                        mode = Mode::Decorators;
                    } else {
                        mode = Mode::Modifiers;
                    }
                    if last_mode == Mode::None {
                        last_mode = mode;
                    } else if mode != last_mode {
                        break;
                    }
                    pos += 1;
                }

                let mut text_range = TextRange::new(-1, -1);
                if start == 0 {
                    text_range = TextRange::new(modifiers.pos(), text_range.end());
                }
                // PORT: Go compares `pos == len(modifiers.Nodes)-1` with int
                // arithmetic; `nodes` is never empty here, so the subtraction
                // cannot underflow.
                if pos == nodes.len() - 1 {
                    text_range = TextRange::new(text_range.pos(), modifiers.end());
                }
                if allow_decorators || last_mode == Mode::Modifiers {
                    self.emit_list_items(
                        Printer::emit_modifier_like,
                        parent_node,
                        &nodes[start..pos],
                        if last_mode == Mode::Modifiers {
                            ListFormat::MODIFIERS
                        } else {
                            ListFormat::DECORATORS
                        },
                        false, /*hasTrailingComma*/
                        text_range,
                    );
                }
                start = pos;
                last_mode = mode;
                pos += 1;
            }

            if let Some(f) = self.print_handlers.on_after_emit_node_list.as_mut() {
                f(modifiers.node_list());
            }
        }

        greatest_end(
            parent_node.pos(),
            &[&modifiers.nodes().last().unwrap_or(Node::NIL)],
        )
    }

    // Go: printer/printer.go:1444 emitTypeParameter
    pub(crate) fn emit_type_parameter(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.emit_binding_identifier(node.name());
        if node.constraint().is_some() {
            self.write_space();
            self.write_keyword("extends");
            self.write_space();
            self.emit_type_node_outside_extends(node.constraint());
        }
        if node.default_type().is_some() {
            self.write_space();
            self.write_operator("=");
            self.write_space();
            self.emit_type_node_outside_extends(node.default_type());
        }
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1463 emitTypeParameterDeclarationNode
    pub(crate) fn emit_type_parameter_declaration_node(&mut self, node: Node) {
        // NOTE: QuickInfo uses TypeFormatFlagsWriteTypeArgumentsOfSignature to instruct the NodeBuilder to store type arguments
        // (i.e. type nodes) instead of type parameter declarations in the type parameter list.
        if is_type_parameter_declaration(node) {
            self.emit_type_parameter(node);
        } else {
            self.emit_type_argument(node);
        }
    }

    // Go: printer/printer.go:1473 emitParameterName
    pub(crate) fn emit_parameter_name(&mut self, node: Node) {
        let saved_write_kind = self.write_kind;
        self.write_kind = WriteKind::PARAMETER;
        self.emit_binding_name(node);
        self.write_kind = saved_write_kind;
    }

    // Go: printer/printer.go:1480 emitParameter
    pub(crate) fn emit_parameter(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), true /*allowDecorators*/);
        self.emit_token_node(node.dot_dot_dot_token());
        self.emit_parameter_name(node.name());
        self.emit_token_node(node.question_token());

        self.emit_type_annotation(node.type_());

        // The comment position has to fallback to any present node within the parameter declaration because as it turns
        // out, the parser can make parameter declarations with _just_ an initializer.
        let equal_token_pos = greatest_end(
            node.pos(),
            &[
                &node.type_(),
                &node.question_token(),
                &node.name(),
                &node.modifiers(),
            ],
        );
        self.emit_initializer(node.initializer(), equal_token_pos, node);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1495 emitParameterDeclarationNode
    pub(crate) fn emit_parameter_declaration_node(&mut self, node: Node) {
        self.emit_parameter(node);
    }

    // Go: printer/printer.go:1499 emitDecorator
    pub(crate) fn emit_decorator(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("@");
        self.emit_expression(node.expression(), OperatorPrecedence::LEFT_HAND_SIDE);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1506 emitModifierLike
    pub(crate) fn emit_modifier_like(&mut self, node: Node) {
        if is_decorator(node) {
            self.emit_decorator(node);
        } else if is_modifier(node) {
            self.emit_keyword_node(node);
        } else {
            panic!("unhandled ModifierLike: {}", kind_string(node.kind()));
        }
    }

    // Go: printer/printer.go:1517 emitTypeParameters
    pub(crate) fn emit_type_parameters(&mut self, parent_node: Node, nodes: NodeList) {
        if nodes.is_nil() {
            return;
        }
        // TODO: preserve trailing comma after Strada migration
        let format = ListFormat::TYPE_PARAMETERS
            | if is_arrow_function(parent_node)
            /*p.shouldAllowTrailingComma(parentNode, nodes)*/
            {
                ListFormat::ALLOW_TRAILING_COMMA
            } else {
                ListFormat::NONE
            };
        self.emit_list(
            Printer::emit_type_parameter_declaration_node,
            parent_node,
            nodes,
            format,
        );
    }

    // Go: printer/printer.go:1524 emitTypeAnnotation
    pub(crate) fn emit_type_annotation(&mut self, node: Node) {
        if node.is_nil() {
            return;
        }

        self.write_punctuation(":");
        self.write_space();
        self.emit_type_node_outside_extends(node);
    }

    // Go: printer/printer.go:1534 emitInitializer
    pub(crate) fn emit_initializer(
        &mut self,
        node: Node,
        equal_token_pos: i32,
        context_node: Node,
    ) {
        if node.is_nil() {
            return;
        }

        self.write_space();
        self.emit_token(
            SyntaxKind::EqualsToken,
            equal_token_pos,
            WriteKind::OPERATOR,
            context_node,
        );
        self.write_space();
        self.emit_expression(node, OperatorPrecedence::DISALLOW_COMMA);
    }

    // Go: printer/printer.go:1545 emitParameters
    pub(crate) fn emit_parameters(&mut self, parent_node: Node, parameters: NodeList) {
        self.generate_all_names(parameters);
        // TODO: preserve trailing comma after Strada migration
        self.emit_list(
            Printer::emit_parameter_declaration_node,
            parent_node,
            parameters,
            ListFormat::PARAMETERS, /*|core.IfElse(p.shouldAllowTrailingComma(parentNode, parameters), LFAllowTrailingComma, LFNone)*/
        );
    }
}

// Go: printer/printer.go:1550 canEmitSimpleArrowHead
pub(crate) fn can_emit_simple_arrow_head(parent_node: Node, parameters: NodeList) -> bool {
    // only arrow functions with a single parameter may have simple arrow head
    if !is_arrow_function(parent_node) || parameters.nodes().len() != 1 {
        return false;
    }

    let parent = parent_node;
    let parameter = parameters.nodes().get(0);

    parameter.pos() == parent.pos() && // may not have parsed tokens between start of parent and parameter
        parent.type_parameter_list().is_nil() && // parent may not have type parameters
        parent.type_().is_nil() && // parent may not have return type annotation
        (parent.modifiers().is_nil() || parent.modifiers().nodes().is_empty()) && // parent may not have modifiers
        !parameters.has_trailing_comma() && // parameters may not have a trailing comma
        parameter.modifiers().is_nil() && // parameter may not have decorators or modifiers
        parameter.dot_dot_dot_token().is_nil() && // parameter may not be rest
        parameter.question_token().is_nil() && // parameter may not be optional
        parameter.type_().is_nil() && // parameter may not have a type annotation
        parameter.initializer().is_nil() && // parameter may not have an initializer
        is_identifier(parameter.name()) // parameter name must be identifier
}

impl Printer {
    // Go: printer/printer.go:1572 emitParametersForArrow
    pub(crate) fn emit_parameters_for_arrow(
        &mut self,
        parent_node: Node, /*FunctionType | ConstructorType | ArrowFunction*/
        parameters: NodeList,
    ) {
        if can_emit_simple_arrow_head(parent_node, parameters) {
            self.generate_all_names(parameters);
            self.emit_list(
                Printer::emit_parameter_declaration_node,
                parent_node,
                parameters,
                ListFormat::SINGLE_ARROW_PARAMETER,
            );
        } else {
            self.emit_parameters(parent_node, parameters);
        }
    }

    // Go: printer/printer.go:1581 emitParametersForIndexSignature
    pub(crate) fn emit_parameters_for_index_signature(
        &mut self,
        parent_node: Node,
        parameters: NodeList,
    ) {
        self.generate_all_names(parameters);
        self.emit_list(
            Printer::emit_parameter_declaration_node,
            parent_node,
            parameters,
            ListFormat::INDEX_SIGNATURE_PARAMETERS,
        );
    }

    // Go: printer/printer.go:1586 emitSignature
    pub(crate) fn emit_signature(&mut self, node: Node) {
        // PORT: Go reads `node.FunctionLikeData()`. Its TypeParameters,
        // Parameters and Type fields are the `type_parameter_list`,
        // `parameter_list` and `type_` accessors.

        // !!! In old emitter, quickinfo used type arguments in place of type parameters on instantiated signatures
        ////if n.TypeArguments != nil {
        ////	p.emitTypeArguments(node, n.TypeArguments)
        ////} else {
        self.emit_type_parameters(node, node.type_parameter_list());
        ////}

        self.emit_parameters(node, node.parameter_list());
        self.emit_type_annotation(node.type_());
    }

    // Go: printer/printer.go:1600 emitFunctionBody
    pub(crate) fn emit_function_body(&mut self, body: Node) {
        self.emit_context
            .add_emit_flags(body, EmitFlags::NO_SOURCE_MAP);

        // Use only notification hooks for the body block, not the full comment pipeline.
        // Without this, trailing comments from the original method declaration
        // (e.g., "// Error") leak into synthesized comma expressions when methods
        // are hoisted into pending expressions.
        if let Some(f) = self.print_handlers.on_before_emit_node.as_mut() {
            f(body);
        }

        self.generate_names(body);

        // !!! Emit with comment after Strada migration
        ////p.emitTokenWithComment(ast.KindOpenBraceToken, body.Pos(), WriteKindPunctuation, body.AsNode())
        self.write_punctuation("{");

        self.increase_indent();
        let statements = body.statement_list();
        let detached_state =
            self.emit_detached_comments_before_statement_list(body, statements.loc());
        let statement_offset = self.emit_prologue_directives(statements);
        let pos = self.writer().get_text_pos();
        self.emit_helpers(body);

        if self.should_emit_block_function_body_on_single_line(body)
            && statement_offset == 0
            && pos == self.writer().get_text_pos()
        {
            self.decrease_indent();
            self.emit_list_range(
                Printer::emit_statement,
                body,
                statements,
                ListFormat::SINGLE_LINE_FUNCTION_BODY_STATEMENTS,
                statement_offset,
                -1,
            );
            self.increase_indent();
        } else {
            self.emit_list_range(
                Printer::emit_statement,
                body,
                statements,
                ListFormat::MULTI_LINE_FUNCTION_BODY_STATEMENTS,
                statement_offset,
                -1,
            );
        }

        self.emit_detached_comments_after_statement_list(body, statements.loc(), detached_state);
        self.decrease_indent();

        // !!! Emit comment after Strada migration
        ////p.emitTokenEx(ast.KindCloseBraceToken, body.Statements.End(), WriteKindPunctuation, body.AsNode(), tefNone)
        self.emit_token_ex(
            SyntaxKind::CloseBraceToken,
            statements.end(),
            WriteKind::PUNCTUATION,
            body,
            TokenEmitFlags::NO_COMMENTS,
        );

        if let Some(f) = self.print_handlers.on_after_emit_node.as_mut() {
            f(body);
        }
    }

    // Go: printer/printer.go:1643 emitFunctionBodyNode
    pub(crate) fn emit_function_body_node(&mut self, node: Node) {
        if node.is_nil() {
            self.write_trailing_semicolon();
            return;
        }

        self.write_space();
        self.emit_function_body(node);
    }

    //
    // Type Members
    //

    // Go: printer/printer.go:1657 emitPropertySignature
    pub(crate) fn emit_property_signature(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.emit_property_name(node.name());
        self.emit_token_node(node.postfix_token());
        self.emit_type_annotation(node.type_());
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1667 emitPropertyDeclaration
    pub(crate) fn emit_property_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), true /*allowDecorators*/);
        self.emit_property_name(node.name());
        self.emit_token_node(node.postfix_token());
        self.emit_type_annotation(node.type_());
        let equal_token_pos =
            greatest_end(node.name().end(), &[&node.type_(), &node.postfix_token()]);
        self.emit_initializer(node.initializer(), equal_token_pos, node);
        self.write_trailing_semicolon();
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1678 emitMethodSignature
    pub(crate) fn emit_method_signature(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.emit_property_name(node.name());
        self.emit_token_node(node.postfix_token());
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1693 emitMethodDeclaration
    pub(crate) fn emit_method_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), true /*allowDecorators*/);
        self.emit_token_node(node.asterisk_token());
        self.emit_property_name(node.name());
        self.emit_token_node(node.postfix_token());
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(node.body());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1709 emitClassStaticBlockDeclaration
    pub(crate) fn emit_class_static_block_declaration(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("static");
        self.push_name_generation_scope(node);
        self.emit_function_body_node(node.body());
        self.pop_name_generation_scope(node);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1718 emitConstructor
    pub(crate) fn emit_constructor(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("constructor");
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(node.body());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1732 emitAccessorDeclaration
    pub(crate) fn emit_accessor_declaration(&mut self, token: SyntaxKind, node: Node) {
        let state = self.enter_node(node);
        let pos = self.emit_modifier_list(node, node.modifiers(), true /*allowDecorators*/);
        self.emit_token(token, pos, WriteKind::KEYWORD, node);
        self.write_space();
        self.emit_property_name(node.name());
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.emit_function_body_node(node.body());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1748 emitGetAccessorDeclaration
    pub(crate) fn emit_get_accessor_declaration(&mut self, node: Node) {
        self.emit_accessor_declaration(SyntaxKind::GetKeyword, node);
    }

    // Go: printer/printer.go:1752 emitSetAccessorDeclaration
    pub(crate) fn emit_set_accessor_declaration(&mut self, node: Node) {
        self.emit_accessor_declaration(SyntaxKind::SetKeyword, node);
    }

    // Go: printer/printer.go:1756 emitCallSignature
    pub(crate) fn emit_call_signature(&mut self, node: Node) {
        let state = self.enter_node(node);
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1768 emitConstructSignature
    pub(crate) fn emit_construct_signature(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("new");
        self.write_space();
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_signature(node);
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1782 emitIndexSignature
    pub(crate) fn emit_index_signature(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        self.emit_parameters_for_index_signature(node, node.parameter_list());
        self.emit_type_annotation(node.type_());
        self.write_trailing_semicolon();
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1796 emitClassElement
    pub(crate) fn emit_class_element(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::PropertyDeclaration => self.emit_property_declaration(node),
            SyntaxKind::MethodDeclaration => self.emit_method_declaration(node),
            SyntaxKind::ClassStaticBlockDeclaration => {
                self.emit_class_static_block_declaration(node)
            }
            SyntaxKind::Constructor => self.emit_constructor(node),
            SyntaxKind::GetAccessor => self.emit_get_accessor_declaration(node),
            SyntaxKind::SetAccessor => self.emit_set_accessor_declaration(node),
            SyntaxKind::IndexSignature => self.emit_index_signature(node),
            SyntaxKind::SemicolonClassElement => self.emit_semicolon_class_element(node),
            SyntaxKind::NotEmittedStatement => self.emit_not_emitted_statement(node),
            SyntaxKind::JsTypeAliasDeclaration => self.emit_type_alias_declaration(node),
            _ => panic!("unexpected ClassElement: {}", kind_string(node.kind())),
        }
    }

    // Go: printer/printer.go:1823 emitTypeElement
    pub(crate) fn emit_type_element(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::PropertySignature => self.emit_property_signature(node),
            SyntaxKind::MethodSignature => self.emit_method_signature(node),
            SyntaxKind::CallSignature => self.emit_call_signature(node),
            SyntaxKind::ConstructSignature => self.emit_construct_signature(node),
            SyntaxKind::GetAccessor => self.emit_get_accessor_declaration(node),
            SyntaxKind::SetAccessor => self.emit_set_accessor_declaration(node),
            SyntaxKind::IndexSignature => self.emit_index_signature(node),
            SyntaxKind::NotEmittedTypeElement => self.emit_not_emitted_type_element(node),
            _ => panic!("unexpected TypeElement: {}", kind_string(node.kind())),
        }
    }

    // Go: printer/printer.go:1846 emitObjectLiteralElement
    pub(crate) fn emit_object_literal_element(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::PropertyAssignment => self.emit_property_assignment(node),
            SyntaxKind::ShorthandPropertyAssignment => {
                self.emit_shorthand_property_assignment(node)
            }
            SyntaxKind::SpreadAssignment => self.emit_spread_assignment(node),
            SyntaxKind::MethodDeclaration => self.emit_method_declaration(node),
            SyntaxKind::GetAccessor => self.emit_get_accessor_declaration(node),
            SyntaxKind::SetAccessor => self.emit_set_accessor_declaration(node),
            _ => panic!(
                "unhandled ObjectLiteralElement: {}",
                kind_string(node.kind())
            ),
        }
    }

    //
    // Types
    //

    // Go: printer/printer.go:1869 emitKeywordTypeNode
    pub(crate) fn emit_keyword_type_node(&mut self, node: Node) {
        self.emit_keyword_node(node);
    }

    // Go: printer/printer.go:1873 emitTypePredicateParameterName
    pub(crate) fn emit_type_predicate_parameter_name(&mut self, node: Node) {
        match node.kind() {
            SyntaxKind::Identifier => self.emit_identifier_reference(node),
            SyntaxKind::ThisType => self.emit_this_type(node),
            _ => panic!(
                "unexpected TypePredicateParameterName: {}",
                kind_string(node.kind())
            ),
        }
    }

    // Go: printer/printer.go:1884 emitTypePredicate
    pub(crate) fn emit_type_predicate(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.asserts_modifier().is_some() {
            self.emit_token_node(node.asserts_modifier());
            self.write_space();
        }
        self.emit_type_predicate_parameter_name(node.parameter_name());
        if node.type_().is_some() {
            self.write_space();
            self.write_keyword("is");
            self.write_space();
            self.emit_type_node_outside_extends(node.type_());
        }
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1900 emitTypeArgument
    pub(crate) fn emit_type_argument(&mut self, node: Node) {
        self.emit_type_node_outside_extends(node);
    }

    // Go: printer/printer.go:1904 emitTypeArguments
    pub(crate) fn emit_type_arguments(&mut self, parent_node: Node, nodes: NodeList) {
        if nodes.is_nil() {
            return;
        }
        // TODO: preserve trailing comma after Strada migration
        self.emit_list(
            Printer::emit_type_parameter_declaration_node,
            parent_node,
            nodes,
            ListFormat::TYPE_ARGUMENTS, /*|core.IfElse(p.shouldAllowTrailingComma(parentNode, nodes), LFAllowTrailingComma, LFNone)*/
        );
    }

    // Go: printer/printer.go:1911 emitTypeReference
    pub(crate) fn emit_type_reference(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_entity_name(node.type_name());
        self.emit_type_arguments(node, node.type_argument_list());
        self.exit_node(node, state);
    }

    // Emits the return type of a FunctionTypeNode or ConstructorTypeNode, including the arrow (`=>`)
    // Go: printer/printer.go:1919 emitReturnType
    pub(crate) fn emit_return_type(&mut self, node: Node) {
        if node.is_nil() {
            return;
        }
        self.write_punctuation("=>");
        self.write_space();
        if self.in_extends
            && node.kind() == SyntaxKind::InferType
            && node.type_parameter().constraint().is_some()
        {
            // if the parent FunctionTypeNode or ConstructorTypeNode is in the `extends` clause of a ConditionalTypeNode,
            // we must parenthesize `infer ... extends ...` so as not to result in an ambiguous parse.
            //
            // `T extends () => infer U extends V ? W : X` would parse the `? W : X` as part of a ConditionalTypeNode in the
            // return type of the FunctionTypeNode, thus we must emit as `T extends () => (infer U extends V) ? W : X`
            self.emit_type_node_preserving_extends(node, TypePrecedence::HIGHEST);
        } else {
            self.emit_type_node_preserving_extends(node, TypePrecedence::LOWEST);
        }
    }

    // Go: printer/printer.go:1937 emitFunctionType
    pub(crate) fn emit_function_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        // !!! in the old emitter, quickinfo uses type arguments in place of type parameters for instantiated signatures
        self.emit_type_parameters(node, node.type_parameter_list());
        self.emit_parameters(node, node.parameter_list());
        self.write_space();
        self.emit_return_type(node.type_());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1952 emitConstructorType
    pub(crate) fn emit_constructor_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_modifier_list(node, node.modifiers(), false /*allowDecorators*/);
        self.write_keyword("new");
        self.write_space();
        let indented = self.should_emit_indented(node);
        self.increase_indent_if(indented);
        self.push_name_generation_scope(node);
        // !!! in the old emitter, quickinfo uses type arguments in place of type parameters for instantiated signatures
        self.emit_type_parameters(node, node.type_parameter_list());
        self.emit_parameters(node, node.parameter_list());
        self.write_space();
        self.emit_return_type(node.type_());
        self.pop_name_generation_scope(node);
        self.decrease_indent_if(indented);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1970 emitTypeQuery
    pub(crate) fn emit_type_query(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("typeof");
        self.write_space();
        self.emit_entity_name(node.expr_name());
        self.emit_type_arguments(node, node.type_argument_list());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1979 emitTypeLiteral
    pub(crate) fn emit_type_literal(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.push_name_generation_scope(node);
        self.generate_all_member_names(node.member_list());
        self.write_punctuation("{");
        let flags = if self.should_emit_on_single_line(node) {
            ListFormat::SINGLE_LINE_TYPE_LITERAL_MEMBERS
        } else {
            ListFormat::MULTI_LINE_TYPE_LITERAL_MEMBERS
        };
        self.emit_list(
            Printer::emit_type_element,
            node,
            node.member_list(),
            flags | ListFormat::NO_SPACE_IF_EMPTY,
        );
        self.write_punctuation("}");
        self.pop_name_generation_scope(node);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:1991 emitArrayType
    pub(crate) fn emit_array_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_postfix_type_operand(node.element_type(), node);
        self.write_punctuation("[");
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    // emitPostfixTypeOperand emits the operand of a postfix type (ArrayType, IndexedAccessType,
    // OptionalType). It is equivalent to `emitTypeNode(operand, TypePrecedencePostfix)` except
    // that it preserves a parsed `typeof X` operand without adding parentheses (e.g.,
    // `typeof C[K]` instead of `(typeof C)[K]`). TypeScript's `parenthesizeNonArrayTypeOfPostfixType`
    // factory rule wraps `TypeQuery` in `ParenthesizedType` only when a postfix type is constructed
    // via the factory, so parsed postfix types preserve the source as written during round-trip
    // emit while synthesized postfix types (e.g., from declaration emit) still get the parentheses.
    // Go: printer/printer.go:2006 emitPostfixTypeOperand
    pub(crate) fn emit_postfix_type_operand(&mut self, operand: Node, parent: Node) {
        if is_parse_tree_node(parent) && operand.kind() == SyntaxKind::TypeQuery {
            self.emit_type_node(operand, TypePrecedence::TYPE_OPERATOR);
            return;
        }
        self.emit_type_node(operand, TypePrecedence::POSTFIX);
    }

    // Go: printer/printer.go:2014 emitTupleElementType
    pub(crate) fn emit_tuple_element_type(&mut self, node: Node) {
        self.emit_type_node_outside_extends(node);
    }

    // Go: printer/printer.go:2018 emitTupleType
    pub(crate) fn emit_tuple_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token(
            SyntaxKind::OpenBracketToken,
            node.pos(),
            WriteKind::PUNCTUATION,
            node,
        );
        let flags = if self.should_emit_on_single_line(node) {
            ListFormat::SINGLE_LINE_TUPLE_TYPE_ELEMENTS
        } else {
            ListFormat::MULTI_LINE_TUPLE_TYPE_ELEMENTS
        };
        self.emit_list(
            Printer::emit_tuple_element_type,
            node,
            node.element_list(),
            flags | ListFormat::NO_SPACE_IF_EMPTY,
        );
        self.emit_token(
            SyntaxKind::CloseBracketToken,
            node.element_list().end(),
            WriteKind::PUNCTUATION,
            node,
        );
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2027 emitRestType
    pub(crate) fn emit_rest_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("...");
        self.emit_type_node_outside_extends(node.type_());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2034 emitOptionalType
    pub(crate) fn emit_optional_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        // !!! May need extra parenthesization if we also have JSDocNullableType
        self.emit_postfix_type_operand(node.type_(), node);
        self.write_punctuation("?");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2042 emitNamedTupleMember
    pub(crate) fn emit_named_tuple_member(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_punctuation_node(node.dot_dot_dot_token());
        self.emit_identifier_name(node.name());
        self.emit_punctuation_node(node.question_token());
        let colon_pos = greatest_end(node.name().end(), &[&node.question_token()]);
        self.emit_token(
            SyntaxKind::ColonToken,
            colon_pos,
            WriteKind::PUNCTUATION,
            node,
        );
        self.write_space();
        self.emit_type_node_outside_extends(node.type_());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2053 emitUnionTypeConstituent
    pub(crate) fn emit_union_type_constituent(&mut self, node: Node) {
        self.emit_type_node(node, TypePrecedence::TYPE_OPERATOR);
    }

    // Go: printer/printer.go:2057 emitUnionType
    pub(crate) fn emit_union_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_list(
            Printer::emit_union_type_constituent,
            node,
            node.types(),
            ListFormat::UNION_TYPE_CONSTITUENTS,
        );
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2063 emitIntersectionTypeConstituent
    pub(crate) fn emit_intersection_type_constituent(&mut self, node: Node) {
        self.emit_type_node(node, TypePrecedence::TYPE_OPERATOR);
    }

    // Go: printer/printer.go:2067 emitIntersectionType
    pub(crate) fn emit_intersection_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_list(
            Printer::emit_intersection_type_constituent,
            node,
            node.types(),
            ListFormat::INTERSECTION_TYPE_CONSTITUENTS, /*, parenthesizer.parenthesizeConstituentTypeOfIntersectionType*/
        ); // !!!
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2073 emitConditionalType
    pub(crate) fn emit_conditional_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_type_node(node.check_type(), TypePrecedence::UNION);
        self.write_space();
        self.write_keyword("extends");
        self.write_space();
        self.emit_type_node_in_extends(node.extends_type());
        self.write_space();
        self.write_punctuation("?");
        self.write_space();
        self.emit_type_node_outside_extends(node.true_type());
        self.write_space();
        self.write_punctuation(":");
        self.write_space();
        self.emit_type_node_outside_extends(node.false_type());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2091 emitInferTypeParameter
    pub(crate) fn emit_infer_type_parameter(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_binding_identifier(node.name());
        if node.constraint().is_some() {
            self.write_space();
            self.write_keyword("extends");
            self.write_space();
            self.emit_type_node_in_extends(node.constraint());
        }
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2103 emitInferType
    pub(crate) fn emit_infer_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("infer");
        self.write_space();
        self.emit_infer_type_parameter(node.type_parameter());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2111 emitParenthesizedType
    pub(crate) fn emit_parenthesized_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("(");
        self.emit_type_node_outside_extends(node.type_());
        self.write_punctuation(")");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2119 emitThisType
    pub(crate) fn emit_this_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_keyword("this");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2125 emitTypeOperator
    pub(crate) fn emit_type_operator(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token(node.operator(), node.pos(), WriteKind::KEYWORD, node);
        self.write_space();
        let precedence = if node.operator() == SyntaxKind::ReadonlyKeyword {
            TypePrecedence::POSTFIX
        } else {
            TypePrecedence::TYPE_OPERATOR
        };
        self.emit_type_node(node.type_(), precedence);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2133 emitIndexedAccessType
    pub(crate) fn emit_indexed_access_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_postfix_type_operand(node.object_type(), node);
        self.write_punctuation("[");
        self.emit_type_node_outside_extends(node.index_type());
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2142 emitMappedTypeParameter
    pub(crate) fn emit_mapped_type_parameter(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_binding_identifier(node.name());
        self.write_space();
        self.write_keyword("in");
        self.write_space();
        self.emit_type_node_outside_extends(node.constraint());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2152 emitMappedType
    pub(crate) fn emit_mapped_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        let single_line = self.should_emit_on_single_line(node);
        self.write_punctuation("{");
        if single_line {
            self.write_space();
        } else {
            self.write_line();
            self.increase_indent();
        }
        let readonly_token = node.readonly_token();
        if readonly_token.is_some() {
            self.emit_token_node(readonly_token);
            if readonly_token.kind() != SyntaxKind::ReadonlyKeyword {
                self.write_keyword("readonly");
            }
            self.write_space();
        }
        self.write_punctuation("[");
        self.emit_mapped_type_parameter(node.type_parameter());
        if node.name_type().is_some() {
            self.write_space();
            self.write_keyword("as");
            self.write_space();
            self.emit_type_node_outside_extends(node.name_type());
        }
        self.write_punctuation("]");
        let question_token = node.question_token();
        if question_token.is_some() {
            self.emit_punctuation_node(question_token);
            if question_token.kind() != SyntaxKind::QuestionToken {
                self.write_punctuation("?");
            }
        }
        if node.type_().is_some() {
            self.write_punctuation(":");
            self.write_space();
            self.emit_type_node_outside_extends(node.type_());
        }
        self.write_trailing_semicolon();
        let members = node.member_list();
        if members.is_some() && !members.nodes().is_empty() {
            if single_line {
                self.write_space();
            } else {
                self.write_line();
            }
            self.emit_list(
                Printer::emit_type_element,
                node,
                members,
                ListFormat::PRESERVE_LINES,
            );
        }
        if single_line {
            self.write_space();
        } else {
            self.write_line();
            self.decrease_indent();
        }
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2210 emitLiteralType
    pub(crate) fn emit_literal_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_expression(node.literal(), OperatorPrecedence::COMMA);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2216 emitTemplateTypeSpan
    pub(crate) fn emit_template_type_span(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_type_node_outside_extends(node.type_());
        self.emit_template_middle_tail(node.literal());
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2223 emitTemplateTypeSpanNode
    pub(crate) fn emit_template_type_span_node(&mut self, node: Node) {
        self.emit_template_type_span(node);
    }

    // Go: printer/printer.go:2227 emitTemplateType
    pub(crate) fn emit_template_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_template_head(node.head());
        self.emit_list(
            Printer::emit_template_type_span_node,
            node,
            node.template_spans(),
            ListFormat::TEMPLATE_EXPRESSION_SPANS,
        );
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2234 emitImportTypeNodeAttributes
    pub(crate) fn emit_import_type_node_attributes(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.write_space();
        self.write_keyword(if node.token() == SyntaxKind::AssertKeyword {
            "assert"
        } else {
            "with"
        });
        self.write_punctuation(":");
        self.write_space();
        // PORT: Go `node.AsImportAttributes().Attributes` is the NodeList
        // accessor `attribute_list` (the Go method `Attributes()` wins the
        // `attributes` name).
        self.emit_list(
            Printer::emit_import_attribute_node,
            node,
            node.attribute_list(),
            ListFormat::IMPORT_ATTRIBUTES,
        );
        self.write_space();
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2247 emitImportTypeNode
    pub(crate) fn emit_import_type_node(&mut self, node: Node) {
        let state = self.enter_node(node);
        if node.is_type_of() {
            self.write_keyword("typeof");
            self.write_space();
        }
        self.write_keyword("import");
        self.write_punctuation("(");
        self.emit_type_node_outside_extends(node.argument());
        if node.attributes().is_some() {
            self.write_punctuation(",");
            self.write_space();
            self.emit_import_type_node_attributes(node.attributes());
        }
        self.write_punctuation(")");
        if node.qualifier().is_some() {
            self.write_punctuation(".");
            self.emit_entity_name(node.qualifier());
        }
        self.emit_type_arguments(node, node.type_argument_list());
        self.exit_node(node, state);
    }

    // emits a Type node in the `extends` clause of a ConditionalType
    // Go: printer/printer.go:2271 emitTypeNodeInExtends
    pub(crate) fn emit_type_node_in_extends(&mut self, node: Node) {
        let saved_in_extends = self.in_extends;
        self.in_extends = true;
        self.emit_type_node_preserving_extends(node, TypePrecedence::LOWEST);
        self.in_extends = saved_in_extends;
    }

    // emits a Type node not in the `extends` clause of a ConditionalType or InferType
    // Go: printer/printer.go:2279 emitTypeNodeOutsideExtends
    pub(crate) fn emit_type_node_outside_extends(&mut self, node: Node) {
        let saved_in_extends = self.in_extends;
        self.in_extends = false;
        self.emit_type_node_preserving_extends(node, TypePrecedence::LOWEST);
        self.in_extends = saved_in_extends;
    }

    // emits a Type node preserving whether or not we are currently in the `extends` clause of a ConditionalType or InferType
    // Go: printer/printer.go:2287 emitTypeNodePreservingExtends
    pub(crate) fn emit_type_node_preserving_extends(
        &mut self,
        node: Node,
        precedence: TypePrecedence,
    ) {
        self.emit_type_node(node, precedence);
    }

    // Go: printer/printer.go:2291 emitTypeNode
    pub(crate) fn emit_type_node(&mut self, node: Node, mut precedence: TypePrecedence) {
        if self.in_extends && precedence <= TypePrecedence::CONDITIONAL {
            // in the `extends` clause of a ConditionalType or InferType, a ConditionalType must be parenthesized
            precedence = TypePrecedence::FUNCTION;
        }

        let saved_in_extends = self.in_extends;
        let parens = get_type_node_precedence(node) < precedence;
        if parens {
            self.in_extends = false;
            self.write_punctuation("(");
        }

        match node.kind() {
            // Keyword Types
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::IntrinsicKeyword => self.emit_keyword_type_node(node),

            // Types
            SyntaxKind::TypePredicate => self.emit_type_predicate(node),
            SyntaxKind::TypeReference => self.emit_type_reference(node),
            SyntaxKind::FunctionType => self.emit_function_type(node),
            SyntaxKind::ConstructorType => self.emit_constructor_type(node),
            SyntaxKind::TypeQuery => self.emit_type_query(node),
            SyntaxKind::TypeLiteral => self.emit_type_literal(node),
            SyntaxKind::ArrayType => self.emit_array_type(node),
            SyntaxKind::TupleType => self.emit_tuple_type(node),
            SyntaxKind::OptionalType => self.emit_optional_type(node),
            SyntaxKind::RestType => self.emit_rest_type(node),
            SyntaxKind::UnionType => self.emit_union_type(node),
            SyntaxKind::IntersectionType => self.emit_intersection_type(node),
            SyntaxKind::ConditionalType => self.emit_conditional_type(node),
            SyntaxKind::InferType => self.emit_infer_type(node),
            SyntaxKind::ParenthesizedType => self.emit_parenthesized_type(node),
            SyntaxKind::ThisType => self.emit_this_type(node),
            SyntaxKind::TypeOperator => self.emit_type_operator(node),
            SyntaxKind::IndexedAccessType => self.emit_indexed_access_type(node),
            SyntaxKind::MappedType => self.emit_mapped_type(node),
            SyntaxKind::LiteralType => self.emit_literal_type(node),
            SyntaxKind::NamedTupleMember => self.emit_named_tuple_member(node),
            SyntaxKind::TemplateLiteralType => self.emit_template_type(node),
            SyntaxKind::TemplateLiteralTypeSpan => self.emit_template_type_span(node),
            SyntaxKind::ImportType => self.emit_import_type_node(node),

            SyntaxKind::PropertyAccessExpression => {
                // Occurs in pseudo-types such as `f<T>.C`, where `f` is a generic function and `C` is a local type
                self.emit_property_access_expression(node);
            }
            SyntaxKind::ExpressionWithTypeArguments => {
                // !!! Should this actually be considered a type?
                self.emit_expression_with_type_arguments(node);
            }

            SyntaxKind::JsDocAllType => self.emit_js_doc_all_type(node),
            SyntaxKind::JsDocNonNullableType => self.emit_js_doc_non_nullable_type(node),
            SyntaxKind::JsDocNullableType => self.emit_js_doc_nullable_type(node),
            SyntaxKind::JsDocOptionalType => self.emit_js_doc_optional_type(node),
            SyntaxKind::JsDocVariadicType => self.emit_js_doc_variadic_type(node),

            _ => panic!("unhandled TypeNode: {}", kind_string(node.kind())),
        }

        if parens {
            self.write_punctuation(")");
        }

        self.in_extends = saved_in_extends;
    }

    //
    // Binding patterns
    //

    // Go: printer/printer.go:2403 emitObjectBindingPattern
    pub(crate) fn emit_object_binding_pattern(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("{");
        self.emit_list(
            Printer::emit_binding_element_node,
            node,
            node.element_list(),
            ListFormat::OBJECT_BINDING_PATTERN_ELEMENTS,
        );
        self.write_punctuation("}");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2411 emitArrayBindingPattern
    pub(crate) fn emit_array_binding_pattern(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("[");
        self.emit_list(
            Printer::emit_binding_element_node,
            node,
            node.element_list(),
            ListFormat::ARRAY_BINDING_PATTERN_ELEMENTS,
        );
        self.write_punctuation("]");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2419 emitBindingElement
    pub(crate) fn emit_binding_element(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_token_node(node.dot_dot_dot_token());
        if node.property_name().is_some() {
            self.emit_property_name(node.property_name());
            self.write_punctuation(":");
            self.write_space();
        }
        // Old parser used `OmittedExpression` as a substitute for `Elision`. New parser uses a `BindingElement` with nil members
        let name = node.name();
        if name.is_some() {
            self.emit_binding_name(name);
            self.emit_initializer(node.initializer(), node.name().end(), node);
        }
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2435 emitBindingElementNode
    pub(crate) fn emit_binding_element_node(&mut self, node: Node) {
        self.emit_binding_element(node);
    }

    // Go: printer/printer.go:2439 emitJSDocAllType
    pub(crate) fn emit_js_doc_all_type(&mut self, node: Node) {
        self.emit_keyword_node(node);
    }

    // Go: printer/printer.go:2443 emitJSDocNonNullableType
    pub(crate) fn emit_js_doc_non_nullable_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("!");
        self.emit_type_node(node.type_(), TypePrecedence::NON_ARRAY);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2450 emitJSDocNullableType
    pub(crate) fn emit_js_doc_nullable_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("?");
        self.emit_type_node(node.type_(), TypePrecedence::NON_ARRAY);
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2457 emitJSDocOptionalType
    pub(crate) fn emit_js_doc_optional_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.emit_type_node(node.type_(), TypePrecedence::JS_DOC);
        self.write_punctuation("=");
        self.exit_node(node, state);
    }

    // Go: printer/printer.go:2464 emitJSDocVariadicType
    pub(crate) fn emit_js_doc_variadic_type(&mut self, node: Node) {
        let state = self.enter_node(node);
        self.write_punctuation("...");
        self.emit_type_node(node.type_(), TypePrecedence::JS_DOC);
        self.exit_node(node, state);
    }
}
