// Go: internal/typeparser/extends_schema_tagged.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// SchemaTaggedResult holds the parsed result of a class extending Schema.TaggedClass/TaggedError/TaggedRequest.
#[derive(Clone, Debug)]
pub struct SchemaTaggedResult {
    /// The class name identifier
    pub class_name: Node,
    /// The Self type argument node (first type arg of the inner call)
    pub self_type_node: Node,
    /// The identifier arg from the inner call (first arg), or nil
    pub key_string_literal: Node,
    /// The tag arg from the outer call (first arg), or nil
    pub tag_string_literal: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_schema_tagged.go extendsSchemaTagged
    /// extendsSchemaTagged checks if a class declaration extends Schema.<memberName>
    /// with the double-call pattern:
    ///
    ///     class X extends Schema.TaggedClass<X>("identifier")("tag", { ... }) {}
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (outer call)
    /// whose own .expression is also a CallExpression (inner call) with type arguments,
    /// and the inner call resolves to Schema.<memberName>.
    ///
    /// Returns nil if the class does not match.
    pub fn extends_schema_tagged(
        &mut self,
        class_node: Node,
        member_name: &str,
    ) -> Option<Rc<SchemaTaggedResult>> {
        if class_node.is_nil() {
            return None;
        }

        // Must have a name
        if class_node.name().is_nil() {
            return None;
        }

        let heritage_elements = get_extends_heritage_clause_elements(class_node);
        if heritage_elements.is_empty() {
            return None;
        }

        for element in heritage_elements {
            if element.is_nil() {
                continue;
            }

            let ewta = element;
            if ewta.is_nil() || ewta.expression().is_nil() {
                continue;
            }

            // The expression should be a CallExpression (the outer call)
            let outer_call_node = ewta.expression();
            if !is_call_expression(outer_call_node) {
                continue;
            }
            let outer_call = outer_call_node;
            if outer_call.is_nil() {
                continue;
            }

            // The outer call's expression should also be a CallExpression (the inner call)
            let inner_call_node = outer_call.expression();
            if inner_call_node.is_nil() || !is_call_expression(inner_call_node) {
                continue;
            }
            let inner_call = inner_call_node;
            if inner_call.is_nil() {
                continue;
            }

            // The inner call must have type arguments (Schema.TaggedClass<Self>())
            let inner_type_arguments = inner_call.type_argument_list();
            if inner_type_arguments.is_nil() || inner_type_arguments.nodes().is_empty() {
                continue;
            }

            // Check if the inner call's expression resolves to Schema.<memberName>
            if inner_call.expression().is_nil() {
                continue;
            }
            if !self
                .is_node_reference_to_effect_schema_module_api(inner_call.expression(), member_name)
            {
                continue;
            }

            // Extract keyStringLiteral from inner call's first argument (if it's a string literal)
            let mut key_string_literal = Node::NIL;
            let inner_arguments = inner_call.argument_list();
            if inner_arguments.is_some() && !inner_arguments.nodes().is_empty() {
                let arg = inner_arguments.nodes().get(0);
                if is_string_literal(arg) {
                    key_string_literal = arg;
                }
            }

            // Extract tagStringLiteral from outer call's first argument (if it's a string literal)
            let mut tag_string_literal = Node::NIL;
            let outer_arguments = outer_call.argument_list();
            if outer_arguments.is_some() && !outer_arguments.nodes().is_empty() {
                let arg = outer_arguments.nodes().get(0);
                if is_string_literal(arg) {
                    tag_string_literal = arg;
                }
            }

            return Some(Rc::new(SchemaTaggedResult {
                class_name: class_node.name(),
                self_type_node: inner_type_arguments.nodes().get(0),
                key_string_literal,
                tag_string_literal,
            }));
        }

        None
    }

    // Go: typeparser/extends_schema_tagged.go ExtendsSchemaTaggedClass
    /// ExtendsSchemaTaggedClass checks if a class declaration extends Schema.TaggedClass<T>("identifier")("tag", { ... }).
    pub fn extends_schema_tagged_class(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<SchemaTaggedResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_tagged_class, class_node, {
            self.extends_schema_tagged(class_node, "TaggedClass")
        })
    }

    // Go: typeparser/extends_schema_tagged.go ExtendsSchemaTaggedError
    /// ExtendsSchemaTaggedError checks if a class declaration extends Schema.TaggedError<T>("identifier")("tag", { ... }).
    pub fn extends_schema_tagged_error(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<SchemaTaggedResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_tagged_error, class_node, {
            self.extends_schema_tagged(class_node, "TaggedError")
        })
    }

    // Go: typeparser/extends_schema_tagged.go ExtendsSchemaTaggedRequest
    /// ExtendsSchemaTaggedRequest checks if a class declaration extends Schema.TaggedRequest<T>("identifier")("tag", { ... }).
    pub fn extends_schema_tagged_request(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<SchemaTaggedResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_tagged_request, class_node, {
            self.extends_schema_tagged(class_node, "TaggedRequest")
        })
    }
}
