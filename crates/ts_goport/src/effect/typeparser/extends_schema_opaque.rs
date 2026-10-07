// Go: internal/typeparser/extends_schema_opaque.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// SchemaOpaqueResult holds the type argument from a class extending Schema.Opaque.
#[derive(Clone, Debug)]
pub struct SchemaOpaqueResult {
    pub self_type_node: Node,
}

impl TypeParser<'_> {
    // Go: typeparser/extends_schema_opaque.go ExtendsSchemaOpaque
    /// ExtendsSchemaOpaque checks for the exact Schema.Opaque double-call heritage shape:
    ///
    ///     class X extends Schema.Opaque<X>()(schema) {}
    pub fn extends_schema_opaque(&mut self, class_node: Node) -> Option<Rc<SchemaOpaqueResult>> {
        if class_node.is_nil() {
            return None;
        }
        cached!(self, extends_schema_opaque, class_node, 'compute: {
            for element in get_extends_heritage_clause_elements(class_node) {
                if element.is_nil() {
                    continue;
                }
                let extends_expression = element;
                if extends_expression.is_nil()
                    || !is_call_expression(extends_expression.expression())
                {
                    continue;
                }
                let outer_call = extends_expression.expression();
                if outer_call.is_nil() || !is_call_expression(outer_call.expression()) {
                    continue;
                }
                let inner_call = outer_call.expression();
                if inner_call.is_nil()
                    || inner_call.expression().is_nil()
                    || inner_call.type_argument_list().is_nil()
                    || inner_call.type_argument_list().nodes().len() != 1
                {
                    continue;
                }
                let inner_type_arguments = inner_call.type_argument_list();
                if self.is_node_reference_to_effect_schema_module_api(
                    inner_call.expression(),
                    "Opaque",
                ) {
                    break 'compute Some(Rc::new(SchemaOpaqueResult {
                        self_type_node: inner_type_arguments.nodes().get(0),
                    }));
                }
            }
            None
        })
    }
}
