//! Port of `transformers/tstransforms/typeserializer.go`.

use crate::prelude::*;
use crate::transformers::utilities::is_generated_identifier;

// Go: transformers/tstransforms/typeserializer.go:11 metadataSerializer
// PORT: Go keeps both the factory and the emit context; the factory is
// `ec.factory()` here.
pub(super) struct MetadataSerializer {
    resolver: Rc<dyn EmitResolver>,
    language_version: ScriptTarget,
    strict_null_checks: bool,
    ec: Rc<EmitContext>,
    c: MetadataSerializerContext,
}

// Go: transformers/tstransforms/typeserializer.go:20 metadataSerializerContext
#[derive(Clone, Copy, Default)]
pub(super) struct MetadataSerializerContext {
    pub(super) current_lexical_scope: Node,
    pub(super) current_name_scope: Node,
    pub(super) serializing_conditional_type_branch: bool,
}

// Go: transformers/tstransforms/typeserializer.go:26 newMetadataSerializer
pub(super) fn new_metadata_serializer(
    resolver: Rc<dyn EmitResolver>,
    ec: Rc<EmitContext>,
    language_version: ScriptTarget,
    strict_null_checks: bool,
) -> MetadataSerializer {
    MetadataSerializer {
        resolver,
        language_version,
        strict_null_checks,
        ec,
        c: MetadataSerializerContext::default(),
    }
}

impl MetadataSerializer {
    // Go: transformers/tstransforms/typeserializer.go:30 metadataSerializer.setContext
    fn set_context(&mut self, ctx: MetadataSerializerContext) {
        self.c = ctx;
    }

    // Go: transformers/tstransforms/typeserializer.go:34 metadataSerializer.SerializeTypeOfNode
    pub(super) fn serialize_type_of_node_exported(
        &mut self,
        ctx: MetadataSerializerContext,
        node: Node,
        container: Node,
    ) -> Node {
        let old_ctx = self.c;
        self.c = ctx;
        let result = self.serialize_type_of_node(node, container);
        self.set_context(old_ctx);
        result
    }

    // Go: transformers/tstransforms/typeserializer.go:41 metadataSerializer.SerializeParameterTypesOfNode
    pub(super) fn serialize_parameter_types_of_node_exported(
        &mut self,
        ctx: MetadataSerializerContext,
        node: Node,
        container: Node,
    ) -> Node {
        let old_ctx = self.c;
        self.c = ctx;
        let result = self.serialize_parameter_types_of_node(node, container);
        self.set_context(old_ctx);
        result
    }

    // Go: transformers/tstransforms/typeserializer.go:48 metadataSerializer.SerializeReturnTypeOfNode
    pub(super) fn serialize_return_type_of_node_exported(
        &mut self,
        ctx: MetadataSerializerContext,
        node: Node,
    ) -> Node {
        let old_ctx = self.c;
        self.c = ctx;
        let result = self.serialize_return_type_of_node(node);
        self.set_context(old_ctx);
        result
    }

    /// Go `s.f`.
    fn f(&self) -> &crate::printer::factory::NodeFactory {
        self.ec.factory()
    }

    // Go: transformers/tstransforms/typeserializer.go:91 metadataSerializer.serializeTypeOfNode
    /// Serializes the type of a node for use with decorator type metadata.
    /// @param node The node that should have its type serialized.
    fn serialize_type_of_node(&mut self, node: Node, container: Node) -> Node {
        match node.kind() {
            SyntaxKind::PropertyDeclaration | SyntaxKind::Parameter => {
                self.serialize_type_node(node.type_())
            }
            SyntaxKind::GetAccessor | SyntaxKind::SetAccessor => {
                self.serialize_type_node(get_accessor_type_node(node, container))
            }
            SyntaxKind::ClassDeclaration
            | SyntaxKind::ClassExpression
            | SyntaxKind::MethodDeclaration => self.f().new_identifier("Function"),
            _ => self.f().new_void_zero_expression(),
        }
    }

    // Go: transformers/tstransforms/typeserializer.go:108 metadataSerializer.serializeParameterTypesOfNode
    /// Serializes the type of a node for use with decorator type metadata.
    /// @param node The node that should have its type serialized.
    fn serialize_parameter_types_of_node(&mut self, node: Node, container: Node) -> Node {
        let mut value_declaration = Node::NIL;
        if is_class_like(node) {
            value_declaration = get_first_constructor_with_body(node);
        } else if is_function_like(node) && node_is_present(node.body()) {
            value_declaration = node;
        }

        if value_declaration.is_nil() {
            let f = self.f();
            return f.new_array_literal_expression(f.new_node_list(&[]), false);
        }

        let mut expressions: Vec<Node> = Vec::new();
        let parameters = get_parameters_of_decorated_declaration(value_declaration, container);
        for (i, parameter) in parameters.nodes().iter().enumerate() {
            if i == 0 && is_identifier(parameter.name()) && parameter.name().text() == "this" {
                continue;
            }
            if parameter.dot_dot_dot_token().is_some() {
                expressions.push(
                    self.serialize_type_node(get_rest_parameter_element_type(parameter.type_())),
                );
            } else {
                expressions.push(self.serialize_type_of_node(parameter, container));
            }
        }
        let f = self.f();
        f.new_array_literal_expression(f.new_node_list(&expressions), false)
    }

    // Go: transformers/tstransforms/typeserializer.go:147 metadataSerializer.serializeReturnTypeOfNode
    /// Serializes the return type of a node for use with decorator type metadata.
    /// @param node The node that should have its return type serialized.
    fn serialize_return_type_of_node(&mut self, node: Node) -> Node {
        if is_function_like(node) && node.type_().is_some() {
            return self.serialize_type_node(node.type_());
        } else if is_async_function(node) {
            return self.f().new_identifier("Promise");
        }
        self.f().new_void_zero_expression()
    }

    // Go: transformers/tstransforms/typeserializer.go:175 metadataSerializer.serializeTypeNode
    /// Serializes a type node for use with decorator type metadata.
    ///
    /// Types are serialized in the following fashion:
    /// - Void types point to "undefined" (e.g. "void 0")
    /// - Function and Constructor types point to the global "Function" constructor.
    /// - Interface types with a call or construct signature types point to the global
    ///   "Function" constructor.
    /// - Array and Tuple types point to the global "Array" constructor.
    /// - Type predicates and booleans point to the global "Boolean" constructor.
    /// - String literal types and strings point to the global "String" constructor.
    /// - Enum and number types point to the global "Number" constructor.
    /// - Symbol types point to the global "Symbol" constructor.
    /// - Type references to classes (or class-like variables) point to the constructor for the class.
    /// - Anything else points to the global "Object" constructor.
    ///
    /// @param node The type node to serialize.
    fn serialize_type_node(&mut self, node: Node) -> Node {
        if node.is_nil() {
            return self.f().new_identifier("Object");
        }

        let node = skip_type_parentheses(node);

        match node.kind() {
            SyntaxKind::VoidKeyword | SyntaxKind::UndefinedKeyword | SyntaxKind::NeverKeyword => {
                return self.f().new_void_zero_expression();
            }
            SyntaxKind::FunctionType | SyntaxKind::ConstructorType => {
                return self.f().new_identifier("Function");
            }
            SyntaxKind::ArrayType | SyntaxKind::TupleType => {
                return self.f().new_identifier("Array");
            }
            SyntaxKind::TypePredicate => {
                if node.asserts_modifier().is_some() {
                    return self.f().new_void_zero_expression();
                }
                return self.f().new_identifier("Boolean");
            }
            SyntaxKind::BooleanKeyword => return self.f().new_identifier("Boolean"),
            SyntaxKind::TemplateLiteralType | SyntaxKind::StringKeyword => {
                return self.f().new_identifier("String");
            }
            SyntaxKind::ObjectKeyword => return self.f().new_identifier("Object"),
            SyntaxKind::LiteralType => {
                return self.serialize_literal_of_literal_type_node(node.literal());
            }
            SyntaxKind::NumberKeyword => return self.f().new_identifier("Number"),
            SyntaxKind::BigIntKeyword => return self.serialize_big_int_constructor(),
            SyntaxKind::SymbolKeyword => return self.f().new_identifier("Symbol"),
            SyntaxKind::TypeReference => return self.serialize_type_reference_node(node),
            SyntaxKind::IntersectionType => {
                let types = node.types().nodes().to_vec();
                return self.serialize_union_or_intersection_constituents(&types, true);
            }
            SyntaxKind::UnionType => {
                let types = node.types().nodes().to_vec();
                return self.serialize_union_or_intersection_constituents(&types, false);
            }
            SyntaxKind::ConditionalType => {
                let old_state = self.c.serializing_conditional_type_branch;
                self.c.serializing_conditional_type_branch = true;
                let result = self.serialize_union_or_intersection_constituents(
                    &[node.true_type(), node.false_type()],
                    false,
                );
                // PORT: Go restores this with `defer`.
                self.c.serializing_conditional_type_branch = old_state;
                return result;
            }
            SyntaxKind::TypeOperator => {
                if node.operator() == SyntaxKind::ReadonlyKeyword {
                    return self.serialize_type_node(node.type_());
                }
                // TODO: why is `unique symbol` not handled as `Symbol`? This falls back to `Object`
            }
            SyntaxKind::TypeQuery
            | SyntaxKind::IndexedAccessType
            | SyntaxKind::MappedType
            | SyntaxKind::TypeLiteral
            | SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::ThisType
            | SyntaxKind::ImportType => {
                // These types fall back to Object.
            }

            // handle JSDoc types from an invalid parse
            SyntaxKind::JsDocAllType | SyntaxKind::JsDocVariadicType => {
                // no meaningful serialization for these invalid-parse JSDoc types
            }
            SyntaxKind::JsDocNullableType
            | SyntaxKind::JsDocNonNullableType
            | SyntaxKind::JsDocOptionalType => {
                return self.serialize_type_node(node.type_());
            }
            _ => crate::gostd::debug::fail_bad_syntax_kind(node.kind(), None),
        }
        self.f().new_identifier("Object")
    }

    // Go: transformers/tstransforms/typeserializer.go:243 metadataSerializer.serializeUnionOrIntersectionConstituents
    fn serialize_union_or_intersection_constituents(
        &mut self,
        types: &[Node],
        is_intersection: bool,
    ) -> Node {
        // Note when updating logic here also update `getEntityNameForDecoratorMetadata` in checker.ts so that aliases can be marked as referenced
        let mut serialized_type = Node::NIL;
        for &type_node in types {
            let type_node = skip_type_parentheses(type_node);
            if type_node.kind() == SyntaxKind::NeverKeyword {
                if is_intersection {
                    return self.f().new_void_zero_expression(); // Reduce to `never` in an intersection
                }
                continue; // Elide `never` in a union
            }

            if type_node.kind() == SyntaxKind::UnknownKeyword {
                if !is_intersection {
                    return self.f().new_identifier("Object"); // Reduce to `unknown` in a union
                }
                continue; // Elide `unknown` in an intersection
            }

            if type_node.kind() == SyntaxKind::AnyKeyword {
                return self.f().new_identifier("Object"); // Reduce to `any` in a union or intersection
            }

            if !self.strict_null_checks
                && ((is_literal_type_node(type_node)
                    && type_node.literal().kind() == SyntaxKind::NullKeyword)
                    || type_node.kind() == SyntaxKind::UndefinedKeyword)
            {
                continue; // Elide null and undefined from unions for metadata, just like what we did prior to the implementation of strict null checks
            }

            let serialized_constituent = self.serialize_type_node(type_node);
            if is_identifier(serialized_constituent) && serialized_constituent.text() == "Object" {
                // One of the individual is global object, return immediately
                return serialized_constituent;
            }

            // If there exists union that is not `void 0` expression, check if the the common type is identifier.
            // anything more complex and we will just default to Object
            if serialized_type.is_some() {
                // Different types
                if !self.equate_serialized_type_nodes(serialized_type, serialized_constituent) {
                    return self.f().new_identifier("Object");
                }
            } else {
                // Initialize the union type
                serialized_type = serialized_constituent;
            }
        }

        // If we were able to find common type, use it
        if serialized_type.is_some() {
            return serialized_type;
        }
        self.f().new_void_zero_expression() // Fallback is only hit if all union constituents are null/undefined/never
    }

    // Go: transformers/tstransforms/typeserializer.go:300 metadataSerializer.serializeLiteralOfLiteralTypeNode
    fn serialize_literal_of_literal_type_node(&mut self, node: Node) -> Node {
        match node.kind() {
            SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral => {
                self.f().new_identifier("String")
            }
            SyntaxKind::PrefixUnaryExpression => {
                let operand = node.operand();
                match operand.kind() {
                    SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral => {
                        self.serialize_literal_of_literal_type_node(operand)
                    }
                    _ => crate::gostd::debug::fail_bad_syntax_kind(operand.kind(), None),
                }
            }
            SyntaxKind::NumericLiteral => self.f().new_identifier("Number"),
            SyntaxKind::BigIntLiteral => self.serialize_big_int_constructor(),
            SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword => {
                self.f().new_identifier("Boolean")
            }
            SyntaxKind::NullKeyword => self.f().new_void_zero_expression(),
            _ => crate::gostd::debug::fail_bad_syntax_kind(node.kind(), None),
        }
    }

    // Go: transformers/tstransforms/typeserializer.go:332 metadataSerializer.serializeTypeReferenceNode
    /// Serializes a TypeReferenceNode to an appropriate JS constructor value for use with decorator type metadata.
    /// @param node The type reference node.
    fn serialize_type_reference_node(&mut self, node: Node) -> Node {
        let mut serial_scope = self.c.current_name_scope;
        if serial_scope.is_nil() {
            serial_scope = self.c.current_lexical_scope;
        }
        let kind = self.resolver.get_type_reference_serialization_kind(
            self.ec.parse_node(node.type_name()),
            self.ec.parse_node(serial_scope),
        );
        let f = self.ec.factory();
        match kind {
            TypeReferenceSerializationKind::UNKNOWN => {
                // From conditional type type reference that cannot be resolved is Similar to any or unknown
                if self.c.serializing_conditional_type_branch {
                    return f.new_identifier("Object");
                }

                let serialized =
                    self.serialize_entity_name_as_expression_fallback(node.type_name());
                let f = self.ec.factory();
                let temp = f.new_temp_variable();
                self.ec.add_variable_declaration(temp);
                f.new_conditional_expression(
                    f.new_type_check(f.new_assignment_expression(temp, serialized), "function"),
                    f.new_token(SyntaxKind::QuestionToken),
                    temp,
                    f.new_token(SyntaxKind::ColonToken),
                    f.new_identifier("Object"),
                )
            }

            TypeReferenceSerializationKind::TYPE_WITH_CONSTRUCT_SIGNATURE_AND_VALUE => {
                self.serialize_entity_name_as_expression(node.type_name())
            }

            TypeReferenceSerializationKind::VOID_NULLABLE_OR_NEVER_TYPE => {
                f.new_void_zero_expression()
            }

            TypeReferenceSerializationKind::BIG_INT_LIKE_TYPE => {
                self.serialize_big_int_constructor()
            }

            TypeReferenceSerializationKind::BOOLEAN_TYPE => f.new_identifier("Boolean"),

            TypeReferenceSerializationKind::NUMBER_LIKE_TYPE => f.new_identifier("Number"),

            TypeReferenceSerializationKind::STRING_LIKE_TYPE => f.new_identifier("String"),

            TypeReferenceSerializationKind::ARRAY_LIKE_TYPE => f.new_identifier("Array"),

            TypeReferenceSerializationKind::ES_SYMBOL_TYPE => f.new_identifier("Symbol"),

            TypeReferenceSerializationKind::TYPE_WITH_CALL_SIGNATURE => {
                f.new_identifier("Function")
            }

            TypeReferenceSerializationKind::PROMISE => f.new_identifier("Promise"),

            TypeReferenceSerializationKind::OBJECT_TYPE => f.new_identifier("Object"),
            _ => crate::gostd::debug::assert_never(
                &kind.0.to_string(),
                Some("unknown type reference serialization kind"),
            ),
        }
    }

    // Go: transformers/tstransforms/typeserializer.go:392 metadataSerializer.serializeBigIntConstructor
    fn serialize_big_int_constructor(&self) -> Node {
        let f = self.f();
        if self.language_version >= ScriptTarget::ES2020 {
            return f.new_identifier("BigInt");
        }
        f.new_conditional_expression(
            f.new_type_check(f.new_identifier("BigInt"), "function"),
            f.new_token(SyntaxKind::QuestionToken),
            f.new_identifier("BigInt"),
            f.new_token(SyntaxKind::ColonToken),
            f.new_identifier("Object"),
        )
    }

    // Go: transformers/tstransforms/typeserializer.go:409 metadataSerializer.serializeEntityNameAsExpression
    /// Serializes an entity name as an expression for decorator type metadata.
    /// @param node The entity name to serialize.
    fn serialize_entity_name_as_expression(&self, node: Node) -> Node {
        match node.kind() {
            SyntaxKind::Identifier => {
                // Create a clone of the name with a new parent, and treat it as if it were
                // a source tree node for the purposes of the checker.
                let name = self.f().clone_node(node);
                set_node_loc(name, node.loc());
                self.ec.unset_original(name); // make this identifier emulate a parse node, making it behave correctly when inspected by the module transforms
                // ensure the parent is set to a parse tree node.
                set_node_parent(name, self.ec.parse_node(self.c.current_lexical_scope));
                name
            }
            SyntaxKind::QualifiedName => self.serialize_qualified_name_as_expression(node),
            _ => Node::NIL,
        }
    }

    // Go: transformers/tstransforms/typeserializer.go:428 metadataSerializer.serializeQualifiedNameAsExpression
    /// Serializes an qualified name as an expression for decorator type metadata.
    /// @param node The qualified name to serialize.
    fn serialize_qualified_name_as_expression(&self, node: Node) -> Node {
        self.f().new_property_access_expression(
            self.serialize_entity_name_as_expression(node.left()),
            Node::NIL,
            node.right(),
            NodeFlags::NONE,
        )
    }

    // Go: transformers/tstransforms/typeserializer.go:436 metadataSerializer.serializeEntityNameAsExpressionFallback
    /// Serializes an entity name which may not exist at runtime, but whose access shouldn't throw
    /// @param node The entity name to serialize.
    fn serialize_entity_name_as_expression_fallback(&self, node: Node) -> Node {
        if node.kind() == SyntaxKind::Identifier {
            // A -> typeof A !== "undefined" && A
            let copied = self.serialize_entity_name_as_expression(node);
            return self.create_checked_value(copied, copied);
        }
        if node.left().kind() == SyntaxKind::Identifier {
            // A.B -> typeof A !== "undefined" && A.B
            return self.create_checked_value(
                self.serialize_entity_name_as_expression(node.left()),
                self.serialize_entity_name_as_expression(node),
            );
        }
        // A.B.C -> typeof A !== "undefined" && (_a = A.B) !== void 0 && _a.C
        let left = self.serialize_entity_name_as_expression_fallback(node.left());
        let f = self.f();
        let temp = f.new_temp_variable();
        self.ec.add_variable_declaration(temp);
        f.new_logical_and_expression(
            f.new_logical_and_expression(
                left.left(),
                f.new_strict_inequality_expression(
                    f.new_assignment_expression(temp, left.right()),
                    f.new_void_zero_expression(),
                ),
            ),
            f.new_property_access_expression(temp, Node::NIL, node.right(), NodeFlags::NONE),
        )
    }

    // Go: transformers/tstransforms/typeserializer.go:471 metadataSerializer.createCheckedValue
    /// Produces an expression that results in `right` if `left` is not undefined at runtime:
    ///
    /// ```text
    /// typeof left !== "undefined" && right
    /// ```
    ///
    /// We use `typeof L !== "undefined"` (rather than `L !== undefined`) since `L` may not be declared.
    /// It's acceptable for this expression to result in `false` at runtime, as the result is intended to be
    /// further checked by any containing expression.
    fn create_checked_value(&self, left: Node, right: Node) -> Node {
        let f = self.f();
        f.new_logical_and_expression(
            f.new_strict_inequality_expression(
                f.new_type_of_expression(left),
                f.new_string_literal("undefined", TokenFlags::NONE),
            ),
            right,
        )
    }

    // Go: transformers/tstransforms/typeserializer.go:478 metadataSerializer.equateSerializedTypeNodes
    fn equate_serialized_type_nodes(&self, left: Node, right: Node) -> bool {
        // temp vars used in fallback
        if is_generated_identifier(&self.ec, left) {
            return is_generated_identifier(&self.ec, right);
        }
        // entity names
        if is_identifier(left) {
            return is_identifier(right) && left.text() == right.text();
        }
        if is_property_access_expression(left) {
            return is_property_access_expression(right)
                && self.equate_serialized_type_nodes(left.expression(), right.expression())
                && self.equate_serialized_type_nodes(left.name(), right.name());
        }
        // `void 0`
        if is_void_expression(left) {
            return is_void_expression(right)
                && is_numeric_literal(left.expression())
                && is_numeric_literal(right.expression())
                && left.expression().text() == "0"
                && right.expression().text() == "0";
        }
        // `"undefined"` or `"function"` in `typeof` checks
        if is_string_literal(left) {
            return is_string_literal(right) && left.text() == right.text();
        }
        // used in `typeof` checks for fallback
        if is_type_of_expression(left) {
            return is_type_of_expression(right)
                && self.equate_serialized_type_nodes(left.expression(), right.expression());
        }
        // parens in `typeof` checks with temps
        if is_parenthesized_expression(left) {
            return is_parenthesized_expression(right)
                && self.equate_serialized_type_nodes(left.expression(), right.expression());
        }
        // conditionals used in fallback
        if is_conditional_expression(left) {
            return is_conditional_expression(right)
                && self.equate_serialized_type_nodes(left.condition(), right.condition())
                && self.equate_serialized_type_nodes(left.when_true(), right.when_true())
                && self.equate_serialized_type_nodes(left.when_false(), right.when_false());
        }
        // logical binary and assignments used in fallback
        if is_binary_expression(left) {
            return is_binary_expression(right)
                && left.operator_token().kind() == right.operator_token().kind()
                && self.equate_serialized_type_nodes(left.left(), right.left())
                && self.equate_serialized_type_nodes(left.right(), right.right());
        }
        false
    }
}

// Go: transformers/tstransforms/typeserializer.go:55 GetSetAccessorValueParameter
pub fn get_set_accessor_value_parameter(node: Node) -> Node {
    if node.is_some() && !node.parameter_list().nodes().is_empty() {
        let parameters = node.parameters();
        if parameters.len() >= 2 && is_this_parameter(parameters.get(0)) {
            return parameters.get(1);
        }
        return parameters.get(0);
    }
    Node::NIL
}

// Go: transformers/tstransforms/typeserializer.go:70 getSetAccessorTypeAnnotationNode
/// Get the type annotation for the value parameter.
///
/// @internal
fn get_set_accessor_type_annotation_node(node: Node) -> Node {
    let p = get_set_accessor_value_parameter(node);
    if p.is_some() && p.type_().is_some() {
        return p.type_();
    }
    Node::NIL
}

// Go: transformers/tstransforms/typeserializer.go:78 getAccessorTypeNode
fn get_accessor_type_node(node: Node, container: Node) -> Node {
    let accessors = get_all_accessor_declarations(&container.members().to_vec(), node);
    if accessors.set_accessor.is_some() {
        return get_set_accessor_type_annotation_node(accessors.set_accessor);
    }
    if accessors.get_accessor.is_some() {
        return accessors.get_accessor.type_();
    }
    Node::NIL
}

// Go: transformers/tstransforms/typeserializer.go:136 getParametersOfDecoratedDeclaration
fn get_parameters_of_decorated_declaration(node: Node, container: Node) -> NodeList {
    if container.is_some() && node.kind() == SyntaxKind::GetAccessor {
        let acc = get_all_accessor_declarations(&container.members().to_vec(), node);
        if acc.set_accessor.is_some() {
            return acc.set_accessor.parameter_list();
        }
    }
    node.parameter_list()
}
