// Go: internal/typeparser/extends_data_tagged.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// DataTaggedErrorResult holds the parsed result of a class extending Data.TaggedError.
#[derive(Clone, Debug)]
pub struct DataTaggedErrorResult {
    /// The class name identifier
    pub class_name: Node,
    /// The key string literal from the call's first argument, or nil
    pub key_string_literal: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_data_tagged.go ExtendsDataTaggedError
    /// ExtendsDataTaggedError checks if a class declaration extends Data.TaggedError("key")<Fields>.
    /// It detects the pattern:
    ///
    /// ```text
    /// class X extends Data.TaggedError("key")<{ msg: string }> {}
    /// ```
    ///
    /// where the ExpressionWithTypeArguments.expression is a CallExpression (Data.TaggedError("key")),
    /// the call's expression is a PropertyAccessExpression resolving to Data.TaggedError,
    /// and the type arguments <Fields> are on the ExpressionWithTypeArguments.
    ///
    /// Returns nil if the class does not extend Data.TaggedError.
    pub fn extends_data_tagged_error(
        &mut self,
        class_node: Node,
    ) -> Option<Rc<DataTaggedErrorResult>> {
        if class_node.is_nil() {
            return None;
        }

        cached!(self, extends_data_tagged_error, class_node, 'compute: {
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

                // The expression should be a CallExpression: Data.TaggedError("key")
                let call_node = ewta.expression();
                if !is_call_expression(call_node) {
                    continue;
                }
                let call = call_node;
                if call.is_nil() {
                    continue;
                }

                // The call's expression should be a PropertyAccessExpression: Data.TaggedError
                if call.expression().is_nil() {
                    continue;
                }
                if !self
                    .is_node_reference_to_effect_data_module_api(call.expression(), "TaggedError")
                {
                    continue;
                }

                // Extract key string literal from call's first argument
                let mut key_string_literal = Node::NIL;
                let arguments = call.argument_list();
                if arguments.is_some() && !arguments.nodes().is_empty() {
                    let arg = arguments.nodes().get(0);
                    if is_string_literal(arg) {
                        key_string_literal = arg;
                    }
                }

                break 'compute Some(Rc::new(DataTaggedErrorResult {
                    class_name: class_node.name(),
                    key_string_literal,
                }));
            }

            None
        })
    }
}
