// Go: internal/typeparser/extends_context_service.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// ServiceMapServiceResult holds the parsed result of a class extending Context.Service.
#[derive(Clone, Debug)]
pub struct ServiceMapServiceResult {
    /// The class name identifier
    pub class_name: Node,
    /// The Self type argument node (first type arg of the inner call)
    pub self_type_node: Node,
    /// The key string literal from the outer call's first argument, or nil
    pub key_string_literal: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_context_service.go ExtendsContextService
    /// ExtendsContextService checks if a class declaration extends Context.Service<Self, Shape>()(key).
    /// It detects the double-call pattern:
    ///
    ///     class X extends Context.Service<X, Shape>()("key") {}
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (outer call)
    /// whose own .expression is also a CallExpression (inner call) with type arguments,
    /// and the inner call resolves to Context.Service.
    ///
    /// Returns nil if the class does not extend Context.Service.
    pub fn extends_context_service(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<ServiceMapServiceResult>> {
        if class_node.is_nil() {
            return None;
        }

        cached!(self, extends_service_map_service, class_node, 'compute: {
            // Must have a name
            if class_node.name().is_nil() {
                break 'compute None;
            }

            let heritage_elements = get_extends_heritage_clause_elements(class_node);
            if heritage_elements.is_empty() {
                break 'compute None;
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

                // The inner call must have type arguments (Context.Service<Self, Shape>())
                let inner_type_arguments = inner_call.type_argument_list();
                if inner_type_arguments.is_nil() || inner_type_arguments.nodes().is_empty() {
                    continue;
                }

                // Check if the inner call's expression resolves to Context.Service
                if inner_call.expression().is_nil() {
                    continue;
                }
                if !self.is_node_reference_to_effect_context_module_api(
                    inner_call.expression(),
                    "Service",
                ) {
                    continue;
                }

                // Extract key string literal from outer call's first argument
                let mut key_string_literal = Node::NIL;
                let outer_arguments = outer_call.argument_list();
                if outer_arguments.is_some() && !outer_arguments.nodes().is_empty() {
                    let arg = outer_arguments.nodes().get(0);
                    if is_string_literal(arg) {
                        key_string_literal = arg;
                    }
                }

                break 'compute Some(Rc::new(ServiceMapServiceResult {
                    class_name: class_node.name(),
                    self_type_node: inner_type_arguments.nodes().get(0),
                    key_string_literal,
                }));
            }

            None
        })
    }
}
