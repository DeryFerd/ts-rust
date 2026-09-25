//! Port of Go `ast.NodeFactory` (`ast/ast.go`, `ast/ast_generated.go`).
//!
//! Every `New*` constructor that the checker, the node builder and the printer
//! use. Nodes are allocated in the synthetic arena (`ast/synthetic.rs`).
//!
//! Argument rules:
//! - Go `*Node` is `Node`; Go `nil` is `Node::NIL`.
//! - Go `*NodeList` is `NodeList`; Go `*ModifierList` is `ModifierList`.
//!   `NodeList::NIL` / `ModifierList::NIL` is Go `nil`.
//! - A parsed node may be passed as a child. The new node then refers to that
//!   same parsed node (Go shares the pointer); see `synthetic.rs`.
//!
//! Go `newNode` does not set parents. Callers set `Parent` when Go does, with
//! `set_node_parent`.

use crate::prelude::*;
use ts_ast::NodeData as D;

/// Go `*ast.NodeFactory`.
// PORT: Go `NodeFactoryHooks` (OnCreate/OnUpdate/OnClone) live in
// `ast/update.rs`; only the printer's emit context sets them. The counters use
// `Cell` so a shared `&NodeFactory` can create nodes while the checker is
// borrowed.
#[derive(Debug, Default)]
pub struct NodeFactory {
    hooks: NodeFactoryHooks,
    node_count: std::cell::Cell<usize>,
    text_count: std::cell::Cell<usize>,
}

/// Synthetic-space id of a required child.
fn id(n: Node) -> ts_ast::NodeId {
    synthetic_child_id(n)
}

/// Synthetic-space id of an optional child.
fn oid(n: Node) -> Option<ts_ast::NodeId> {
    synthetic_opt_child_id(n)
}

/// A required list field.
fn req_list(l: NodeList) -> ts_ast::NodeList {
    synthetic_req_list_value(l)
}

/// An optional list field.
fn opt_list(l: NodeList) -> Option<ts_ast::NodeList> {
    synthetic_list_value(l)
}

/// A modifiers field.
fn mods(m: ModifierList) -> Option<ts_ast::ModifierList> {
    synthetic_modifiers_value(m)
}

/// ts_ast token flags from Go token flags.
fn token_flags(flags: TokenFlags) -> ts_ast::TokenFlags {
    ts_ast::TokenFlags(flags.bits() as u32)
}

const NO_TOKEN_FLAGS: ts_ast::TokenFlags = ts_ast::TokenFlags(0);

impl NodeFactory {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    // Go: ast/ast.go:67 NewNodeFactory
    #[must_use]
    pub fn new_with_hooks(hooks: NodeFactoryHooks) -> Self {
        Self { hooks, ..Self::default() }
    }

    /// Go `f.hooks`.
    pub(crate) fn hooks(&self) -> &NodeFactoryHooks {
        &self.hooks
    }

    // Go: ast/ast.go:84 (f *NodeFactory) newNode
    fn new_node(&self, kind: SyntaxKind, data: D) -> Node {
        self.node_count.set(self.node_count.get() + 1);
        let node = alloc_synthetic_node(kind, data);
        // Go: ast.go:73
        if let Some(h) = &self.hooks.on_create {
            h(node);
        }
        node
    }

    /// `newNode` plus Go `f.textCount++`, for nodes that carry text.
    fn new_text_node(&self, kind: SyntaxKind, data: D) -> Node {
        self.text_count.set(self.text_count.get() + 1);
        self.new_node(kind, data)
    }

    /// `newNode` plus Go `node.Flags |= flags & NodeFlagsOptionalChain`.
    fn new_chain_node(&self, kind: SyntaxKind, data: D, flags: NodeFlags) -> Node {
        let node = self.new_node(kind, data);
        set_node_flags(node, node.flags() | (flags & NodeFlags::OPTIONAL_CHAIN));
        node
    }

    // Go: ast/ast.go:89 NodeCount
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.node_count.get()
    }

    // Go: ast/ast.go:93 TextCount
    #[must_use]
    pub fn text_count(&self) -> usize {
        self.text_count.get()
    }

    // ── Lists ──────────────────────────────────────────────────────────

    // Go: ast/ast.go:127 NewNodeList
    #[must_use]
    pub fn new_node_list(&self, nodes: &[Node]) -> NodeList {
        new_synthetic_node_list(nodes, TextRange::undefined())
    }

    // Go: ast/ast.go:158 NewModifierList
    #[must_use]
    pub fn new_modifier_list(&self, nodes: &[Node]) -> ModifierList {
        new_synthetic_modifier_list(nodes, TextRange::undefined())
    }

    // ── Tokens, names and literals ─────────────────────────────────────

    // Go: ast/ast_generated.go:599 NewToken
    pub fn new_token(&self, kind: SyntaxKind) -> Node {
        self.new_node(kind, D::Token(Box::new(ts_ast::TokenData)))
    }

    // Go: ast/ast.go:1674 NewModifier
    pub fn new_modifier(&self, kind: SyntaxKind) -> Node {
        self.new_token(kind)
    }

    // Go: ast/ast_generated.go:792 NewIdentifier
    pub fn new_identifier(&self, text: impl Into<String>) -> Node {
        self.new_text_node(
            SyntaxKind::Identifier,
            D::Identifier(Box::new(ts_ast::IdentifierData { flow_node: None, text: text.into() })),
        )
    }

    // Go: ast/ast_generated.go:816 NewPrivateIdentifier
    pub fn new_private_identifier(&self, text: impl Into<String>) -> Node {
        self.new_text_node(
            SyntaxKind::PrivateIdentifier,
            D::PrivateIdentifier(Box::new(ts_ast::PrivateIdentifierData { text: text.into() })),
        )
    }

    // Go: ast/ast_generated.go:843 NewQualifiedName
    pub fn new_qualified_name(&self, left: Node, right: Node) -> Node {
        self.new_node(
            SyntaxKind::QualifiedName,
            D::QualifiedName(Box::new(ts_ast::QualifiedNameData {
                flow_node: None,
                left: id(left),
                right: id(right),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:888 NewComputedPropertyName
    pub fn new_computed_property_name(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ComputedPropertyName,
            D::ComputedPropertyName(Box::new(ts_ast::ComputedPropertyNameData { expression: id(expression), facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:3764 NewStringLiteral
    pub fn new_string_literal(&self, text: impl Into<String>, flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::StringLiteral,
            D::StringLiteral(Box::new(ts_ast::StringLiteralData {
                text: text.into(),
                token_flags: token_flags(flags & TokenFlags::STRING_LITERAL_FLAGS),
            })),
        )
    }

    // Go: ast/ast_generated.go:3788 NewNumericLiteral
    pub fn new_numeric_literal(&self, text: impl Into<String>, flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::NumericLiteral,
            D::NumericLiteral(Box::new(ts_ast::NumericLiteralData {
                text: text.into(),
                token_flags: token_flags(flags & TokenFlags::NUMERIC_LITERAL_FLAGS),
            })),
        )
    }

    // Go: ast/ast_generated.go:3812 NewBigIntLiteral
    pub fn new_big_int_literal(&self, text: impl Into<String>, flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::BigIntLiteral,
            D::BigIntLiteral(Box::new(ts_ast::BigIntLiteralData {
                text: text.into(),
                token_flags: token_flags(flags & TokenFlags::NUMERIC_LITERAL_FLAGS),
            })),
        )
    }

    // Go: ast/ast_generated.go:3836 NewRegularExpressionLiteral
    pub fn new_regular_expression_literal(&self, text: impl Into<String>, flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::RegularExpressionLiteral,
            D::RegularExpressionLiteral(Box::new(ts_ast::RegularExpressionLiteralData {
                text: text.into(),
                token_flags: token_flags(flags & TokenFlags::REGULAR_EXPRESSION_LITERAL_FLAGS),
            })),
        )
    }

    // Go: ast/ast_generated.go:3862 NewNoSubstitutionTemplateLiteral
    // PORT: Go sets no `RawText`; ts_ast stores an empty string for it.
    pub fn new_no_substitution_template_literal(&self, text: impl Into<String>, template_flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::NoSubstitutionTemplateLiteral,
            D::NoSubstitutionTemplateLiteral(Box::new(ts_ast::NoSubstitutionTemplateLiteralData {
                raw_text: String::new(),
                symbol: None,
                template_flags: token_flags(template_flags & TokenFlags::TEMPLATE_LITERAL_LIKE_FLAGS),
                text: text.into(),
                token_flags: NO_TOKEN_FLAGS,
            })),
        )
    }

    // Go: ast/ast_generated.go:6287 NewTemplateHead
    pub fn new_template_head(&self, text: impl Into<String>, raw_text: impl Into<String>, template_flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::TemplateHead,
            D::TemplateHead(Box::new(ts_ast::TemplateHeadData {
                raw_text: raw_text.into(),
                template_flags: token_flags(template_flags & TokenFlags::TEMPLATE_LITERAL_LIKE_FLAGS),
                text: text.into(),
                token_flags: NO_TOKEN_FLAGS,
            })),
        )
    }

    // Go: ast/ast_generated.go:6313 NewTemplateMiddle
    pub fn new_template_middle(&self, text: impl Into<String>, raw_text: impl Into<String>, template_flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::TemplateMiddle,
            D::TemplateMiddle(Box::new(ts_ast::TemplateMiddleData {
                raw_text: raw_text.into(),
                template_flags: token_flags(template_flags & TokenFlags::TEMPLATE_LITERAL_LIKE_FLAGS),
                text: text.into(),
                token_flags: NO_TOKEN_FLAGS,
            })),
        )
    }

    // Go: ast/ast_generated.go:6339 NewTemplateTail
    pub fn new_template_tail(&self, text: impl Into<String>, raw_text: impl Into<String>, template_flags: TokenFlags) -> Node {
        self.new_text_node(
            SyntaxKind::TemplateTail,
            D::TemplateTail(Box::new(ts_ast::TemplateTailData {
                raw_text: raw_text.into(),
                template_flags: token_flags(template_flags & TokenFlags::TEMPLATE_LITERAL_LIKE_FLAGS),
                text: text.into(),
                token_flags: NO_TOKEN_FLAGS,
            })),
        )
    }

    // ── Type nodes ─────────────────────────────────────────────────────

    // Go: ast/ast_generated.go:5271 NewKeywordTypeNode
    pub fn new_keyword_type_node(&self, kind: SyntaxKind) -> Node {
        self.new_node(kind, D::KeywordTypeNode(Box::new(ts_ast::KeywordTypeNodeData)))
    }

    // Go: ast/ast_generated.go:5308 NewUnionTypeNode
    pub fn new_union_type_node(&self, types: NodeList) -> Node {
        self.new_node(SyntaxKind::UnionType, D::UnionTypeNode(Box::new(ts_ast::UnionTypeNodeData { types: req_list(types) })))
    }

    // Go: ast/ast_generated.go:5346 NewIntersectionTypeNode
    pub fn new_intersection_type_node(&self, types: NodeList) -> Node {
        self.new_node(
            SyntaxKind::IntersectionType,
            D::IntersectionTypeNode(Box::new(ts_ast::IntersectionTypeNodeData { types: req_list(types) })),
        )
    }

    // Go: ast/ast_generated.go:5388 NewConditionalTypeNode
    pub fn new_conditional_type_node(&self, check_type: Node, extends_type: Node, true_type: Node, false_type: Node) -> Node {
        self.new_node(
            SyntaxKind::ConditionalType,
            D::ConditionalTypeNode(Box::new(ts_ast::ConditionalTypeNodeData {
                check_type: id(check_type),
                extends_type: id(extends_type),
                false_type: id(false_type),
                locals: ts_ast::SymbolTable,
                next_container: None,
                true_type: id(true_type),
            })),
        )
    }

    // Go: ast/ast_generated.go:5433 NewTypeOperatorNode
    pub fn new_type_operator_node(&self, operator: SyntaxKind, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::TypeOperator,
            D::TypeOperatorNode(Box::new(ts_ast::TypeOperatorNodeData { operator, type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:5472 NewInferTypeNode
    pub fn new_infer_type_node(&self, type_parameter: Node) -> Node {
        self.new_node(
            SyntaxKind::InferType,
            D::InferTypeNode(Box::new(ts_ast::InferTypeNodeData { type_parameter: id(type_parameter) })),
        )
    }

    // Go: ast/ast_generated.go:5510 NewArrayTypeNode
    pub fn new_array_type_node(&self, element_type: Node) -> Node {
        self.new_node(
            SyntaxKind::ArrayType,
            D::ArrayTypeNode(Box::new(ts_ast::ArrayTypeNodeData { element_type: id(element_type) })),
        )
    }

    // Go: ast/ast_generated.go:5549 NewIndexedAccessTypeNode
    pub fn new_indexed_access_type_node(&self, object_type: Node, index_type: Node) -> Node {
        self.new_node(
            SyntaxKind::IndexedAccessType,
            D::IndexedAccessTypeNode(Box::new(ts_ast::IndexedAccessTypeNodeData {
                index_type: id(index_type),
                object_type: id(object_type),
            })),
        )
    }

    // Go: ast/ast_generated.go:5588 NewTypeReferenceNode
    pub fn new_type_reference_node(&self, type_name: Node, type_arguments: NodeList) -> Node {
        self.new_node(
            SyntaxKind::TypeReference,
            D::TypeReferenceNode(Box::new(ts_ast::TypeReferenceNodeData {
                type_arguments: opt_list(type_arguments),
                type_name: id(type_name),
            })),
        )
    }

    // Go: ast/ast_generated.go:5629 NewExpressionWithTypeArguments
    pub fn new_expression_with_type_arguments(&self, expression: Node, type_arguments: NodeList) -> Node {
        self.new_node(
            SyntaxKind::ExpressionWithTypeArguments,
            D::ExpressionWithTypeArguments(Box::new(ts_ast::ExpressionWithTypeArgumentsData {
                expression: id(expression),
                type_arguments: opt_list(type_arguments),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:5668 NewLiteralTypeNode
    pub fn new_literal_type_node(&self, literal: Node) -> Node {
        self.new_node(SyntaxKind::LiteralType, D::LiteralTypeNode(Box::new(ts_ast::LiteralTypeNodeData { literal: id(literal) })))
    }

    // Go: ast/ast_generated.go:5705 NewThisTypeNode
    pub fn new_this_type_node(&self) -> Node {
        self.new_node(SyntaxKind::ThisType, D::ThisTypeNode(Box::new(ts_ast::ThisTypeNodeData)))
    }

    // Go: ast/ast_generated.go:5729 NewTypePredicateNode
    pub fn new_type_predicate_node(&self, asserts_modifier: Node, parameter_name: Node, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::TypePredicate,
            D::TypePredicateNode(Box::new(ts_ast::TypePredicateNodeData {
                asserts_modifier: oid(asserts_modifier),
                parameter_name: id(parameter_name),
                type_: oid(type_node),
            })),
        )
    }

    // Go: ast/ast_generated.go:5866 NewTypeQueryNode
    pub fn new_type_query_node(&self, expr_name: Node, type_arguments: NodeList) -> Node {
        self.new_node(
            SyntaxKind::TypeQuery,
            D::TypeQueryNode(Box::new(ts_ast::TypeQueryNodeData {
                expr_name: id(expr_name),
                type_arguments: opt_list(type_arguments),
            })),
        )
    }

    // Go: ast/ast_generated.go:5912 NewMappedTypeNode
    pub fn new_mapped_type_node(
        &self,
        readonly_token: Node,
        type_parameter: Node,
        name_type: Node,
        question_token: Node,
        type_node: Node,
        members: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::MappedType,
            D::MappedTypeNode(Box::new(ts_ast::MappedTypeNodeData {
                locals: ts_ast::SymbolTable,
                members: opt_list(members),
                name_type: oid(name_type),
                next_container: None,
                question_token: oid(question_token),
                readonly_token: oid(readonly_token),
                symbol: None,
                type_: oid(type_node),
                type_parameter: id(type_parameter),
            })),
        )
    }

    // Go: ast/ast_generated.go:5961 NewTypeLiteralNode
    pub fn new_type_literal_node(&self, members: NodeList) -> Node {
        self.new_node(
            SyntaxKind::TypeLiteral,
            D::TypeLiteralNode(Box::new(ts_ast::TypeLiteralNodeData { members: req_list(members), symbol: None })),
        )
    }

    // Go: ast/ast_generated.go:5999 NewTupleTypeNode
    pub fn new_tuple_type_node(&self, elements: NodeList) -> Node {
        self.new_node(SyntaxKind::TupleType, D::TupleTypeNode(Box::new(ts_ast::TupleTypeNodeData { elements: req_list(elements) })))
    }

    // Go: ast/ast_generated.go:6041 NewNamedTupleMember
    pub fn new_named_tuple_member(&self, dot_dot_dot_token: Node, name: Node, question_token: Node, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::NamedTupleMember,
            D::NamedTupleMember(Box::new(ts_ast::NamedTupleMemberData {
                dot_dot_dot_token: oid(dot_dot_dot_token),
                question_token: oid(question_token),
                symbol: None,
                type_: id(type_node),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:6089 NewOptionalTypeNode
    pub fn new_optional_type_node(&self, type_node: Node) -> Node {
        self.new_node(SyntaxKind::OptionalType, D::OptionalTypeNode(Box::new(ts_ast::OptionalTypeNodeData { type_: id(type_node) })))
    }

    // Go: ast/ast_generated.go:6127 NewRestTypeNode
    pub fn new_rest_type_node(&self, type_node: Node) -> Node {
        self.new_node(SyntaxKind::RestType, D::RestTypeNode(Box::new(ts_ast::RestTypeNodeData { type_: id(type_node) })))
    }

    // Go: ast/ast_generated.go:6165 NewParenthesizedTypeNode
    pub fn new_parenthesized_type_node(&self, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::ParenthesizedType,
            D::ParenthesizedTypeNode(Box::new(ts_ast::ParenthesizedTypeNodeData { type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:6203 NewFunctionTypeNode
    pub fn new_function_type_node(&self, type_parameters: NodeList, parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::FunctionType,
            D::FunctionTypeNode(Box::new(ts_ast::FunctionTypeNodeData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                modifiers: None,
            })),
        )
    }

    // Go: ast/ast_generated.go:6243 NewConstructorTypeNode
    pub fn new_constructor_type_node(&self, modifiers: ModifierList, type_parameters: NodeList, parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::ConstructorType,
            D::ConstructorTypeNode(Box::new(ts_ast::ConstructorTypeNodeData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:6366 NewTemplateLiteralTypeNode
    pub fn new_template_literal_type_node(&self, head: Node, template_spans: NodeList) -> Node {
        self.new_node(
            SyntaxKind::TemplateLiteralType,
            D::TemplateLiteralTypeNode(Box::new(ts_ast::TemplateLiteralTypeNodeData {
                head: id(head),
                template_spans: req_list(template_spans),
            })),
        )
    }

    // Go: ast/ast_generated.go:6406 NewTemplateLiteralTypeSpan
    pub fn new_template_literal_type_span(&self, type_node: Node, literal: Node) -> Node {
        self.new_node(
            SyntaxKind::TemplateLiteralTypeSpan,
            D::TemplateLiteralTypeSpan(Box::new(ts_ast::TemplateLiteralTypeSpanData { literal: id(literal), type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:8372 NewImportTypeNode
    pub fn new_import_type_node(&self, is_type_of: bool, argument: Node, attributes: Node, qualifier: Node, type_arguments: NodeList) -> Node {
        self.new_node(
            SyntaxKind::ImportType,
            D::ImportTypeNode(Box::new(ts_ast::ImportTypeNodeData {
                argument: id(argument),
                attributes: oid(attributes),
                is_type_of,
                qualifier: oid(qualifier),
                type_arguments: opt_list(type_arguments),
            })),
        )
    }

    // ── Signatures and type elements ───────────────────────────────────

    // Go: ast/ast_generated.go:8676 NewTypeParameterDeclaration
    pub fn new_type_parameter_declaration(&self, modifiers: ModifierList, name: Node, constraint: Node, expression: Node, default_type: Node) -> Node {
        self.new_node(
            SyntaxKind::TypeParameter,
            D::TypeParameterDeclaration(Box::new(ts_ast::TypeParameterDeclarationData {
                constraint: oid(constraint),
                default_type: oid(default_type),
                expression: oid(expression),
                symbol: None,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2013 NewParameterDeclaration
    pub fn new_parameter_declaration(
        &self,
        modifiers: ModifierList,
        dot_dot_dot_token: Node,
        name: Node,
        question_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::Parameter,
            D::ParameterDeclaration(Box::new(ts_ast::ParameterDeclarationData {
                dot_dot_dot_token: oid(dot_dot_dot_token),
                initializer: oid(initializer),
                question_token: oid(question_token),
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3132 NewCallSignatureDeclaration
    pub fn new_call_signature_declaration(&self, type_parameters: NodeList, parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::CallSignature,
            D::CallSignatureDeclaration(Box::new(ts_ast::CallSignatureDeclarationData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
            })),
        )
    }

    // Go: ast/ast_generated.go:3175 NewConstructSignatureDeclaration
    pub fn new_construct_signature_declaration(&self, type_parameters: NodeList, parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::ConstructSignature,
            D::ConstructSignatureDeclaration(Box::new(ts_ast::ConstructSignatureDeclarationData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
            })),
        )
    }

    // Go: ast/ast_generated.go:3220 NewConstructorDeclaration
    pub fn new_constructor_declaration(
        &self,
        modifiers: ModifierList,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::Constructor,
            D::ConstructorDeclaration(Box::new(ts_ast::ConstructorDeclarationData {
                asterisk_token: None,
                body: oid(body),
                end_flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                return_flow_node: None,
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:3267 NewGetAccessorDeclaration
    #[allow(clippy::too_many_arguments)]
    pub fn new_get_accessor_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::GetAccessor,
            D::GetAccessorDeclaration(Box::new(ts_ast::GetAccessorDeclarationData {
                asterisk_token: None,
                body: oid(body),
                end_flow_node: None,
                flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                postfix_token: None,
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3320 NewSetAccessorDeclaration
    #[allow(clippy::too_many_arguments)]
    pub fn new_set_accessor_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::SetAccessor,
            D::SetAccessorDeclaration(Box::new(ts_ast::SetAccessorDeclarationData {
                asterisk_token: None,
                body: oid(body),
                end_flow_node: None,
                flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                postfix_token: None,
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3379 NewIndexSignatureDeclaration
    // PORT: Go keeps a nil `Type`; ts_ast requires one, so nil is stored in
    // the nil slot and `type_node()` still reads nil.
    pub fn new_index_signature_declaration(&self, modifiers: ModifierList, parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::IndexSignature,
            D::IndexSignatureDeclaration(Box::new(ts_ast::IndexSignatureDeclarationData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: id(type_node),
                type_parameters: None,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:3422 NewMethodSignatureDeclaration
    pub fn new_method_signature_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::MethodSignature,
            D::MethodSignatureDeclaration(Box::new(ts_ast::MethodSignatureDeclarationData {
                full_signature: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                postfix_token: oid(postfix_token),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3479 NewMethodDeclaration
    #[allow(clippy::too_many_arguments)]
    pub fn new_method_declaration(
        &self,
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
        self.new_node(
            SyntaxKind::MethodDeclaration,
            D::MethodDeclaration(Box::new(ts_ast::MethodDeclarationData {
                asterisk_token: oid(asterisk_token),
                body: oid(body),
                end_flow_node: None,
                flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                postfix_token: oid(postfix_token),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3541 NewPropertySignatureDeclaration
    // PORT: ts_ast requires `Type` and `Initializer`; Go nil goes to the nil
    // slot, so `type_node()` and `initializer()` still read nil.
    pub fn new_property_signature_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::PropertySignature,
            D::PropertySignatureDeclaration(Box::new(ts_ast::PropertySignatureDeclarationData {
                initializer: id(initializer),
                postfix_token: oid(postfix_token),
                symbol: None,
                type_: id(type_node),
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:3595 NewPropertyDeclaration
    pub fn new_property_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        postfix_token: Node,
        type_node: Node,
        initializer: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::PropertyDeclaration,
            D::PropertyDeclaration(Box::new(ts_ast::PropertyDeclarationData {
                initializer: oid(initializer),
                postfix_token: oid(postfix_token),
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2660 NewNotEmittedTypeElement
    pub fn new_not_emitted_type_element(&self) -> Node {
        self.new_node(SyntaxKind::NotEmittedTypeElement, D::NotEmittedTypeElement(Box::new(ts_ast::NotEmittedTypeElementData)))
    }

    // ── Declarations ───────────────────────────────────────────────────

    // Go: ast/ast_generated.go:2504 NewEnumMember
    pub fn new_enum_member(&self, name: Node, initializer: Node) -> Node {
        self.new_node(
            SyntaxKind::EnumMember,
            D::EnumMember(Box::new(ts_ast::EnumMemberData {
                initializer: oid(initializer),
                postfix_token: None,
                symbol: None,
                facts: 0,
                modifiers: None,
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2552 NewEnumDeclaration
    pub fn new_enum_declaration(&self, modifiers: ModifierList, name: Node, members: NodeList) -> Node {
        self.new_node(
            SyntaxKind::EnumDeclaration,
            D::EnumDeclaration(Box::new(ts_ast::EnumDeclarationData {
                flow_node: None,
                local_symbol: None,
                members: req_list(members),
                symbol: None,
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2165 NewFunctionDeclaration
    #[allow(clippy::too_many_arguments)]
    pub fn new_function_declaration(
        &self,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::FunctionDeclaration,
            D::FunctionDeclaration(Box::new(ts_ast::FunctionDeclarationData {
                asterisk_token: oid(asterisk_token),
                body: oid(body),
                end_flow_node: None,
                flow_node: None,
                full_signature: oid(full_signature),
                local_symbol: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                return_flow_node: None,
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2222 NewClassDeclaration
    pub fn new_class_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::ClassDeclaration,
            D::ClassDeclaration(Box::new(ts_ast::ClassDeclarationData {
                flow_node: None,
                heritage_clauses: opt_list(heritage_clauses),
                local_symbol: None,
                locals: ts_ast::SymbolTable,
                members: req_list(members),
                next_container: None,
                symbol: None,
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2272 NewClassExpression
    pub fn new_class_expression(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::ClassExpression,
            D::ClassExpression(Box::new(ts_ast::ClassExpressionData {
                heritage_clauses: opt_list(heritage_clauses),
                local_symbol: None,
                locals: ts_ast::SymbolTable,
                members: req_list(members),
                next_container: None,
                symbol: None,
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2324 NewHeritageClause
    pub fn new_heritage_clause(&self, token: SyntaxKind, types: NodeList) -> Node {
        self.new_node(
            SyntaxKind::HeritageClause,
            D::HeritageClause(Box::new(ts_ast::HeritageClauseData { token, types: req_list(types), facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:2370 NewInterfaceDeclaration
    pub fn new_interface_declaration(
        &self,
        modifiers: ModifierList,
        name: Node,
        type_parameters: NodeList,
        heritage_clauses: NodeList,
        members: NodeList,
    ) -> Node {
        self.new_node(
            SyntaxKind::InterfaceDeclaration,
            D::InterfaceDeclaration(Box::new(ts_ast::InterfaceDeclarationData {
                flow_node: None,
                heritage_clauses: opt_list(heritage_clauses),
                local_symbol: None,
                members: req_list(members),
                symbol: None,
                type_parameters: opt_list(type_parameters),
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2427 NewTypeAliasDeclaration
    pub fn new_type_alias_declaration(&self, modifiers: ModifierList, name: Node, type_parameters: NodeList, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::TypeAliasDeclaration,
            D::TypeAliasDeclaration(Box::new(ts_ast::TypeAliasDeclarationData {
                flow_node: None,
                local_symbol: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                symbol: None,
                type_: id(type_node),
                type_parameters: opt_list(type_parameters),
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:8222 NewModuleDeclaration
    pub fn new_module_declaration(&self, modifiers: ModifierList, keyword: SyntaxKind, name: Node, body: Node) -> Node {
        self.new_node(
            SyntaxKind::ModuleDeclaration,
            D::ModuleDeclaration(Box::new(ts_ast::ModuleDeclarationData {
                asterisk_token: None,
                body: oid(body),
                end_flow_node: None,
                flow_node: None,
                keyword,
                local_symbol: None,
                locals: ts_ast::SymbolTable,
                next_container: None,
                symbol: None,
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:2597 NewModuleBlock
    pub fn new_module_block(&self, statements: NodeList) -> Node {
        self.new_node(
            SyntaxKind::ModuleBlock,
            D::ModuleBlock(Box::new(ts_ast::ModuleBlockData { flow_node: None, statements: req_list(statements), facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:5771 NewImportAttribute
    pub fn new_import_attribute(&self, name: Node, value: Node) -> Node {
        self.new_node(
            SyntaxKind::ImportAttribute,
            D::ImportAttribute(Box::new(ts_ast::ImportAttributeData { value: id(value), facts: 0, name: id(name) })),
        )
    }

    // Go: ast/ast_generated.go:5822 NewImportAttributes
    pub fn new_import_attributes(&self, token: SyntaxKind, attributes: NodeList, multi_line: bool) -> Node {
        self.new_node(
            SyntaxKind::ImportAttributes,
            D::ImportAttributes(Box::new(ts_ast::ImportAttributesData {
                attributes: req_list(attributes),
                multi_line,
                token,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:2903 NewExportAssignment
    pub fn new_export_assignment(&self, modifiers: ModifierList, is_export_equals: bool, type_node: Node, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ExportAssignment,
            D::ExportAssignment(Box::new(ts_ast::ExportAssignmentData {
                expression: id(expression),
                flow_node: None,
                is_export_equals,
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:3038 NewNamedExports
    pub fn new_named_exports(&self, elements: NodeList) -> Node {
        self.new_node(
            SyntaxKind::NamedExports,
            D::NamedExports(Box::new(ts_ast::NamedExportsData { elements: req_list(elements), facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:3085 NewExportSpecifier
    pub fn new_export_specifier(&self, is_type_only: bool, property_name: Node, name: Node) -> Node {
        self.new_node(
            SyntaxKind::ExportSpecifier,
            D::ExportSpecifier(Box::new(ts_ast::ExportSpecifierData {
                is_type_only,
                local_symbol: None,
                property_name: oid(property_name),
                symbol: None,
                facts: 0,
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:8324 NewExportDeclaration
    pub fn new_export_declaration(
        &self,
        modifiers: ModifierList,
        is_type_only: bool,
        export_clause: Node,
        module_specifier: Node,
        attributes: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::ExportDeclaration,
            D::ExportDeclaration(Box::new(ts_ast::ExportDeclarationData {
                attributes: oid(attributes),
                export_clause: oid(export_clause),
                flow_node: None,
                is_type_only,
                module_specifier: oid(module_specifier),
                symbol: None,
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // ── Expressions ────────────────────────────────────────────────────

    // Go: ast/ast_generated.go:3734 NewKeywordExpression
    pub fn new_keyword_expression(&self, kind: SyntaxKind) -> Node {
        self.new_node(kind, D::KeywordExpression(Box::new(ts_ast::KeywordExpressionData { flow_node: None })))
    }

    // Go: ast/ast_generated.go:4327 NewPropertyAccessExpression
    pub fn new_property_access_expression(&self, expression: Node, question_dot_token: Node, name: Node, flags: NodeFlags) -> Node {
        self.new_chain_node(
            SyntaxKind::PropertyAccessExpression,
            D::PropertyAccessExpression(Box::new(ts_ast::PropertyAccessExpressionData {
                expression: id(expression),
                flow_node: None,
                question_dot_token: oid(question_dot_token),
                facts: 0,
                name: id(name),
            })),
            flags,
        )
    }

    // Go: ast/ast_generated.go:4377 NewElementAccessExpression
    pub fn new_element_access_expression(
        &self,
        expression: Node,
        question_dot_token: Node,
        argument_expression: Node,
        flags: NodeFlags,
    ) -> Node {
        self.new_chain_node(
            SyntaxKind::ElementAccessExpression,
            D::ElementAccessExpression(Box::new(ts_ast::ElementAccessExpressionData {
                argument_expression: id(argument_expression),
                expression: id(expression),
                flow_node: None,
                question_dot_token: oid(question_dot_token),
                facts: 0,
            })),
            flags,
        )
    }

    // Go: ast/ast_generated.go:4430 NewCallExpression
    pub fn new_call_expression(
        &self,
        expression: Node,
        question_dot_token: Node,
        type_arguments: NodeList,
        arguments: NodeList,
        flags: NodeFlags,
    ) -> Node {
        self.new_chain_node(
            SyntaxKind::CallExpression,
            D::CallExpression(Box::new(ts_ast::CallExpressionData {
                arguments: req_list(arguments),
                expression: id(expression),
                question_dot_token: oid(question_dot_token),
                symbol: None,
                type_arguments: opt_list(type_arguments),
                facts: 0,
            })),
            flags,
        )
    }

    // Go: ast/ast_generated.go:4479 NewNewExpression
    pub fn new_new_expression(&self, expression: Node, type_arguments: NodeList, arguments: NodeList) -> Node {
        self.new_node(
            SyntaxKind::NewExpression,
            D::NewExpression(Box::new(ts_ast::NewExpressionData {
                arguments: opt_list(arguments),
                expression: id(expression),
                type_arguments: opt_list(type_arguments),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:4565 NewNonNullExpression
    pub fn new_non_null_expression(&self, expression: Node, flags: NodeFlags) -> Node {
        self.new_chain_node(
            SyntaxKind::NonNullExpression,
            D::NonNullExpression(Box::new(ts_ast::NonNullExpressionData { expression: id(expression) })),
            flags,
        )
    }

    // Go: ast/ast_generated.go:4738 NewTaggedTemplateExpression
    pub fn new_tagged_template_expression(
        &self,
        tag: Node,
        question_dot_token: Node,
        type_arguments: NodeList,
        template: Node,
        flags: NodeFlags,
    ) -> Node {
        self.new_chain_node(
            SyntaxKind::TaggedTemplateExpression,
            D::TaggedTemplateExpression(Box::new(ts_ast::TaggedTemplateExpressionData {
                question_dot_token: oid(question_dot_token),
                tag: id(tag),
                template: id(template),
                type_arguments: opt_list(type_arguments),
                facts: 0,
            })),
            flags,
        )
    }

    // Go: ast/ast_generated.go:3940 NewPrefixUnaryExpression
    pub fn new_prefix_unary_expression(&self, operator: SyntaxKind, operand: Node) -> Node {
        self.new_node(
            SyntaxKind::PrefixUnaryExpression,
            D::PrefixUnaryExpression(Box::new(ts_ast::PrefixUnaryExpressionData { operand: id(operand), operator })),
        )
    }

    // Go: ast/ast_generated.go:3893 NewBinaryExpression
    pub fn new_binary_expression(&self, modifiers: ModifierList, left: Node, type_node: Node, operator_token: Node, right: Node) -> Node {
        self.new_node(
            SyntaxKind::BinaryExpression,
            D::BinaryExpression(Box::new(ts_ast::BinaryExpressionData {
                left: id(left),
                operator_token: id(operator_token),
                right: id(right),
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:4269 NewConditionalExpression
    pub fn new_conditional_expression(&self, condition: Node, question_token: Node, when_true: Node, colon_token: Node, when_false: Node) -> Node {
        self.new_node(
            SyntaxKind::ConditionalExpression,
            D::ConditionalExpression(Box::new(ts_ast::ConditionalExpressionData {
                colon_token: id(colon_token),
                condition: id(condition),
                question_token: id(question_token),
                when_false: id(when_false),
                when_true: id(when_true),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:4784 NewParenthesizedExpression
    pub fn new_parenthesized_expression(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ParenthesizedExpression,
            D::ParenthesizedExpression(Box::new(ts_ast::ParenthesizedExpressionData { expression: id(expression) })),
        )
    }

    // Go: ast/ast_generated.go:4128 NewFunctionExpression
    #[allow(clippy::too_many_arguments)]
    pub fn new_function_expression(
        &self,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::FunctionExpression,
            D::FunctionExpression(Box::new(ts_ast::FunctionExpressionData {
                asterisk_token: oid(asterisk_token),
                body: id(body),
                end_flow_node: None,
                flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                return_flow_node: None,
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
                name: oid(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:4072 NewArrowFunction
    #[allow(clippy::too_many_arguments)]
    pub fn new_arrow_function(
        &self,
        modifiers: ModifierList,
        type_parameters: NodeList,
        parameters: NodeList,
        type_node: Node,
        full_signature: Node,
        equals_greater_than_token: Node,
        body: Node,
    ) -> Node {
        self.new_node(
            SyntaxKind::ArrowFunction,
            D::ArrowFunction(Box::new(ts_ast::ArrowFunctionData {
                asterisk_token: None,
                body: id(body),
                end_flow_node: None,
                equals_greater_than_token: id(equals_greater_than_token),
                flow_node: None,
                full_signature: oid(full_signature),
                locals: ts_ast::SymbolTable,
                next_container: None,
                parameters: req_list(parameters),
                symbol: None,
                type_: oid(type_node),
                type_parameters: opt_list(type_parameters),
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:6447 NewSyntheticExpression
    // PORT: Go `Type any` holds a `*checker.Type`; here it is a `TypeId`,
    // read back with `synthetic_expression_type`.
    pub fn new_synthetic_expression(&self, type_: TypeId, is_spread: bool, tuple_name_source: Node) -> Node {
        let node = self.new_node(
            SyntaxKind::SyntheticExpression,
            D::SyntheticExpression(Box::new(ts_ast::SyntheticExpressionData {
                is_spread,
                tuple_name_source: oid(tuple_name_source),
                type_: ts_ast::OpaqueValue,
            })),
        );
        set_synthetic_expression_type(node, type_);
        node
    }

    // Go: ast/ast_generated.go:4605 NewSpreadElement
    pub fn new_spread_element(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::SpreadElement, D::SpreadElement(Box::new(ts_ast::SpreadElementData { expression: id(expression) })))
    }

    // Go: ast/ast_generated.go:4828 NewArrayLiteralExpression
    pub fn new_array_literal_expression(&self, elements: NodeList, multi_line: bool) -> Node {
        self.new_node(
            SyntaxKind::ArrayLiteralExpression,
            D::ArrayLiteralExpression(Box::new(ts_ast::ArrayLiteralExpressionData { elements: req_list(elements), multi_line, facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:4874 NewObjectLiteralExpression
    pub fn new_object_literal_expression(&self, properties: NodeList, multi_line: bool) -> Node {
        self.new_node(
            SyntaxKind::ObjectLiteralExpression,
            D::ObjectLiteralExpression(Box::new(ts_ast::ObjectLiteralExpressionData {
                multi_line,
                properties: req_list(properties),
                symbol: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:4961 NewPropertyAssignment
    pub fn new_property_assignment(&self, modifiers: ModifierList, name: Node, postfix_token: Node, type_node: Node, initializer: Node) -> Node {
        self.new_node(
            SyntaxKind::PropertyAssignment,
            D::PropertyAssignment(Box::new(ts_ast::PropertyAssignmentData {
                initializer: id(initializer),
                postfix_token: oid(postfix_token),
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                modifiers: mods(modifiers),
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:4185 NewAsExpression
    pub fn new_as_expression(&self, expression: Node, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::AsExpression,
            D::AsExpression(Box::new(ts_ast::AsExpressionData { expression: id(expression), type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:4225 NewSatisfiesExpression
    pub fn new_satisfies_expression(&self, expression: Node, type_node: Node) -> Node {
        self.new_node(
            SyntaxKind::SatisfiesExpression,
            D::SatisfiesExpression(Box::new(ts_ast::SatisfiesExpressionData { expression: id(expression), type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:5233 NewTypeAssertion
    pub fn new_type_assertion(&self, type_node: Node, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::TypeAssertionExpression,
            D::TypeAssertion(Box::new(ts_ast::TypeAssertionData { expression: id(expression), type_: id(type_node) })),
        )
    }

    // Go: ast/ast_generated.go:5068 NewDeleteExpression
    pub fn new_delete_expression(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::DeleteExpression, D::DeleteExpression(Box::new(ts_ast::DeleteExpressionData { expression: id(expression) })))
    }

    // Go: ast/ast_generated.go:5110 NewTypeOfExpression
    pub fn new_type_of_expression(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::TypeOfExpression, D::TypeOfExpression(Box::new(ts_ast::TypeOfExpressionData { expression: id(expression) })))
    }

    // Go: ast/ast_generated.go:5152 NewVoidExpression
    pub fn new_void_expression(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::VoidExpression, D::VoidExpression(Box::new(ts_ast::VoidExpressionData { expression: id(expression) })))
    }

    // Go: ast/ast_generated.go:5194 NewAwaitExpression
    pub fn new_await_expression(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::AwaitExpression, D::AwaitExpression(Box::new(ts_ast::AwaitExpressionData { expression: id(expression) })))
    }

    // Go: ast/ast_generated.go:4028 NewYieldExpression
    pub fn new_yield_expression(&self, asterisk_token: Node, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::YieldExpression,
            D::YieldExpression(Box::new(ts_ast::YieldExpressionData { asterisk_token: oid(asterisk_token), expression: oid(expression) })),
        )
    }

    // Go: ast/ast_generated.go:931 NewDecorator
    pub fn new_decorator(&self, expression: Node) -> Node {
        self.new_node(SyntaxKind::Decorator, D::Decorator(Box::new(ts_ast::DecoratorData { expression: id(expression), facts: 0 })))
    }

    // ── Statements ─────────────────────────────────────────────────────

    // Go: ast/ast_generated.go:1784 NewBlock
    pub fn new_block(&self, statements: NodeList, multi_line: bool) -> Node {
        self.new_node(
            SyntaxKind::Block,
            D::Block(Box::new(ts_ast::BlockData {
                flow_node: None,
                locals: ts_ast::SymbolTable,
                multi_line,
                next_container: None,
                statements: req_list(statements),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:1829 NewVariableStatement
    pub fn new_variable_statement(&self, modifiers: ModifierList, declaration_list: Node) -> Node {
        self.new_node(
            SyntaxKind::VariableStatement,
            D::VariableStatement(Box::new(ts_ast::VariableStatementData {
                declaration_list: id(declaration_list),
                flow_node: None,
                facts: 0,
                modifiers: mods(modifiers),
            })),
        )
    }

    // Go: ast/ast_generated.go:1874 NewVariableDeclaration
    pub fn new_variable_declaration(&self, name: Node, exclamation_token: Node, type_node: Node, initializer: Node) -> Node {
        self.new_node(
            SyntaxKind::VariableDeclaration,
            D::VariableDeclaration(Box::new(ts_ast::VariableDeclarationData {
                exclamation_token: oid(exclamation_token),
                initializer: oid(initializer),
                local_symbol: None,
                symbol: None,
                type_: oid(type_node),
                facts: 0,
                name: id(name),
            })),
        )
    }

    // Go: ast/ast_generated.go:1923 NewVariableDeclarationList
    pub fn new_variable_declaration_list(&self, declarations: NodeList, flags: NodeFlags) -> Node {
        let node = self.new_node(
            SyntaxKind::VariableDeclarationList,
            D::VariableDeclarationList(Box::new(ts_ast::VariableDeclarationListData { declarations: req_list(declarations), facts: 0 })),
        );
        set_node_flags(node, flags);
        node
    }

    // Go: ast/ast_generated.go:1739 NewExpressionStatement
    pub fn new_expression_statement(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ExpressionStatement,
            D::ExpressionStatement(Box::new(ts_ast::ExpressionStatementData { expression: id(expression), flow_node: None })),
        )
    }

    // Go: ast/ast_generated.go:1314 NewReturnStatement
    pub fn new_return_statement(&self, expression: Node) -> Node {
        self.new_node(
            SyntaxKind::ReturnStatement,
            D::ReturnStatement(Box::new(ts_ast::ReturnStatementData { expression: oid(expression), flow_node: None, facts: 0 })),
        )
    }

    // Go: ast/ast_generated.go:993 NewIfStatement
    pub fn new_if_statement(&self, expression: Node, then_statement: Node, else_statement: Node) -> Node {
        self.new_node(
            SyntaxKind::IfStatement,
            D::IfStatement(Box::new(ts_ast::IfStatementData {
                else_statement: oid(else_statement),
                expression: id(expression),
                flow_node: None,
                then_statement: id(then_statement),
                facts: 0,
            })),
        )
    }

    // Go: ast/ast_generated.go:968 NewEmptyStatement
    pub fn new_empty_statement(&self) -> Node {
        self.new_node(SyntaxKind::EmptyStatement, D::EmptyStatement(Box::new(ts_ast::EmptyStatementData { flow_node: None })))
    }

    // Go: ast/ast_generated.go:2638 NewNotEmittedStatement
    pub fn new_not_emitted_statement(&self) -> Node {
        self.new_node(SyntaxKind::NotEmittedStatement, D::NotEmittedStatement(Box::new(ts_ast::NotEmittedStatementData { flow_node: None })))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factory_nodes_read_like_go_nodes() {
        let f = NodeFactory::new();
        let this = f.new_keyword_expression(SyntaxKind::ThisKeyword);
        let name = f.new_identifier("x");
        let access = f.new_property_access_expression(this, Node::NIL, name, NodeFlags::OPTIONAL_CHAIN | NodeFlags::SYNTHESIZED);

        // Go `newNode`: undefined loc, nil parent, and only OptionalChain kept.
        assert_eq!(access.kind(), SyntaxKind::PropertyAccessExpression);
        assert_eq!(access.flags(), NodeFlags::OPTIONAL_CHAIN);
        assert_eq!(access.loc(), TextRange::undefined());
        assert!(access.parent().is_nil());
        // Children keep their identity, like Go pointers.
        assert_eq!(access.expression(), this);
        assert_eq!(access.name(), name);
        assert_eq!(name.text(), "x");

        // Go field writes after creation.
        set_node_parent(this, access);
        assert_eq!(this.parent(), access);
        set_node_loc(access, TextRange::new(3, 7));
        assert_eq!(access.pos(), 3);

        // Go nil in a field that ts_ast requires still reads as nil.
        let sig = f.new_index_signature_declaration(ModifierList::NIL, f.new_node_list(&[]), Node::NIL);
        assert!(sig.type_().is_nil());
        assert_eq!(f.node_count(), 4);
        assert_eq!(f.text_count(), 1);
    }

    #[test]
    fn literal_flags_are_masked_like_go() {
        let f = NodeFactory::new();
        let s = f.new_string_literal("a", TokenFlags(-1));
        assert_eq!(s.token_flags(), TokenFlags::STRING_LITERAL_FLAGS);
        let list = f.new_node_list(&[s]);
        assert_eq!(list.loc(), TextRange::undefined());
        assert_eq!(list.nodes().get(0), s);
    }

    #[test]
    fn synthetic_expression_keeps_its_type() {
        let f = NodeFactory::new();
        let e = f.new_synthetic_expression(TypeId(42), true, Node::NIL);
        assert_eq!(synthetic_expression_type(e), TypeId(42));
        assert!(e.is_spread());
        assert!(e.tuple_name_source().is_nil());
    }
}
