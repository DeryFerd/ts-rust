// Go: internal/typeparser/extends_schema_class.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// SchemaClassResult holds the parsed result of a class extending Schema.Class or Schema.RequestClass.
#[derive(Clone, Debug)]
pub struct SchemaClassResult {
    /// The class name identifier
    pub class_name: Node,
    /// The Self type argument node (first type arg of the inner call)
    pub self_type_node: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_schema_class.go ExtendsSchemaClass
    /// ExtendsSchemaClass checks if a class declaration extends Schema.Class<Self>("name")({}).
    /// It detects the double-call pattern:
    ///
    ///     class X extends Schema.Class<X>("name")({}) {}
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (outer call)
    /// whose own .expression is also a CallExpression (inner call) with type arguments,
    /// and the inner call resolves to Schema.Class.
    ///
    /// Returns nil if the class does not extend Schema.Class.
    pub fn extends_schema_class(&mut self, class_node: Node) -> Option<Rc<SchemaClassResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_class, class_node, {
            self.extends_schema_class_like(class_node, "Class")
        })
    }

    // Go: typeparser/extends_schema_class.go ExtendsSchemaRequestClass
    /// ExtendsSchemaRequestClass checks if a class declaration extends Schema.RequestClass<Self>("name")({}).
    /// Same double-call pattern as ExtendsSchemaClass but for Schema.RequestClass.
    ///
    /// Returns nil if the class does not extend Schema.RequestClass.
    pub fn extends_schema_request_class(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<SchemaClassResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_request_class, class_node, {
            self.extends_schema_class_like(class_node, "RequestClass")
        })
    }

    // Go: typeparser/extends_schema_class.go extendsSchemaClassLike
    /// extendsSchemaClassLike is the shared implementation for ExtendsSchemaClass and ExtendsSchemaRequestClass.
    pub fn extends_schema_class_like(
        &mut self,
        class_node: Node,
        member_name: &str,
    ) -> Option<Rc<SchemaClassResult>> {
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

            // The inner call must have type arguments (Schema.Class<Self>())
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

            return Some(Rc::new(SchemaClassResult {
                class_name: class_node.name(),
                self_type_node: inner_type_arguments.nodes().get(0),
            }));
        }

        None
    }
}
