// Go: internal/typeparser/extends_effect_service.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectServiceResult holds the parsed result of a class extending Effect.Service.
#[derive(Clone, Debug)]
pub struct EffectServiceResult {
    /// The class name identifier
    pub class_name: Node,
    /// The Self type argument node (first type arg of the inner call)
    pub self_type_node: Node,
    /// The options expression (second argument of the outer call), or nil
    pub options: Node,
    /// The key string literal from the outer call's first argument, or nil
    pub key_string_literal: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_effect_service.go ExtendsEffectV3Service
    /// ExtendsEffectV3Service checks if a class declaration extends Effect.Service<Self>()(key, options).
    /// It detects the double-call pattern:
    ///
    ///     class X extends Effect.Service<X>()("key", { ... }) {}
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (outer call)
    /// whose own .expression is also a CallExpression (inner call) with type arguments,
    /// and the inner call resolves to Effect.Service.
    ///
    /// Returns nil if the class does not extend Effect.Service.
    pub fn extends_effect_v3_service(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<EffectServiceResult>> {
        if class_node.is_nil() {
            return None;
        }

        cached!(self, extends_effect_service, class_node, 'compute: {
            if self.supported_effect_version() == EffectMajorVersion::V4 {
                break 'compute None;
            }

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

                // The inner call must have type arguments (Effect.Service<Self>())
                let inner_type_arguments = inner_call.type_argument_list();
                if inner_type_arguments.is_nil() || inner_type_arguments.nodes().is_empty() {
                    continue;
                }

                // Check if the inner call's expression resolves to Effect.Service
                if inner_call.expression().is_nil() {
                    continue;
                }
                if !self.is_node_reference_to_effect_module_api(inner_call.expression(), "Service")
                {
                    continue;
                }

                // Extract the key string literal from outer call's first argument
                let mut key_string_literal = Node::NIL;
                let outer_arguments = outer_call.argument_list();
                if outer_arguments.is_some() && !outer_arguments.nodes().is_empty() {
                    let arg = outer_arguments.nodes().get(0);
                    if is_string_literal(arg) {
                        key_string_literal = arg;
                    }
                }

                // Extract the options expression (second argument of the outer call, if present)
                let mut options = Node::NIL;
                if outer_arguments.is_some() && outer_arguments.nodes().len() >= 2 {
                    options = outer_arguments.nodes().get(1);
                }

                break 'compute Some(Rc::new(EffectServiceResult {
                    class_name: class_node.name(),
                    self_type_node: inner_type_arguments.nodes().get(0),
                    options,
                    key_string_literal,
                }));
            }

            None
        })
    }
}
