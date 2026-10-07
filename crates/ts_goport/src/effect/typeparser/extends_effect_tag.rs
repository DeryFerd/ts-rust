// Go: internal/typeparser/extends_effect_tag.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectTagResult holds the parsed result of a class extending Effect.Tag.
#[derive(Clone, Debug)]
pub struct EffectTagResult {
    /// The class name identifier
    pub class_name: Node,
    /// The Self type argument node (first type arg of the outer call)
    pub self_type_node: Node,
    /// The key string literal from the inner call's first argument, or nil
    pub key_string_literal: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_effect_tag.go ExtendsEffectTag
    /// ExtendsEffectTag checks if a class declaration extends Effect.Tag("key")<Self, Shape>().
    /// It detects the pattern:
    ///
    /// ```text
    /// class X extends Effect.Tag("key")<X, Shape>() {}
    /// ```
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (outer call)
    /// that has type arguments <Self, Shape>, and whose own .expression is a CallExpression
    /// (inner call: Effect.Tag("key")), and the inner call's expression resolves to Effect.Tag.
    ///
    /// Returns nil if the class does not extend Effect.Tag.
    pub fn extends_effect_tag(&mut self, class_node: Node) -> Option<Rc<EffectTagResult>> {
        if class_node.is_nil() {
            return None;
        }

        cached!(self, extends_effect_tag, class_node, 'compute: {
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

                // The expression should be a CallExpression (the outer call with type arguments)
                let outer_call_node = ewta.expression();
                if !is_call_expression(outer_call_node) {
                    continue;
                }
                let outer_call = outer_call_node;
                if outer_call.is_nil() {
                    continue;
                }

                // The outer call must have type arguments (<Self, Shape>)
                let outer_type_arguments = outer_call.type_argument_list();
                if outer_type_arguments.is_nil() || outer_type_arguments.nodes().is_empty() {
                    continue;
                }

                // The outer call's expression should also be a CallExpression (the inner call: Effect.Tag("key"))
                let inner_call_node = outer_call.expression();
                if inner_call_node.is_nil() || !is_call_expression(inner_call_node) {
                    continue;
                }
                let inner_call = inner_call_node;
                if inner_call.is_nil() {
                    continue;
                }

                // Check if the inner call's expression resolves to Effect.Tag
                if inner_call.expression().is_nil() {
                    continue;
                }
                if !self.is_node_reference_to_effect_module_api(inner_call.expression(), "Tag") {
                    continue;
                }

                // Extract key string literal from inner call's first argument
                let mut key_string_literal = Node::NIL;
                let inner_arguments = inner_call.argument_list();
                if inner_arguments.is_some() && !inner_arguments.nodes().is_empty() {
                    let arg = inner_arguments.nodes().get(0);
                    if is_string_literal(arg) {
                        key_string_literal = arg;
                    }
                }

                break 'compute Some(Rc::new(EffectTagResult {
                    class_name: class_node.name(),
                    self_type_node: outer_type_arguments.nodes().get(0),
                    key_string_literal,
                }));
            }

            None
        })
    }
}
