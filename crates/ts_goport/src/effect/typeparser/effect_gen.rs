//! Port of Effect-TS/tsgo `internal/typeparser/effect_gen.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectGenCallResult represents a parsed Effect.gen(...) call.
// Go: typeparser/effect_gen.go EffectGenCallResult
#[derive(Clone)]
pub struct EffectGenCallResult {
    pub call: Node,
    /// Namespace receiver for Effect.gen; nil for named imports and local aliases.
    pub effect_module: Node,
    pub options_node: Node,
    pub generator_function: Node,
    pub body: Node,
    pub pipe_arguments: Vec<Node>,
}

impl TypeParser<'_> {
    /// EffectGenCall parses a node as Effect.gen(<generator>).
    /// Returns nil when the node is not an Effect.gen call.
    // Go: typeparser/effect_gen.go EffectGenCall
    pub fn effect_gen_call(&mut self, node: Node) -> Option<Rc<EffectGenCallResult>> {
        if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
            return None;
        }

        cached!(self, effect_gen_call, node, 'compute: {
            let call = node;
            if call.argument_list().is_nil() || call.arguments().is_empty() {
                break 'compute None;
            }

            let (options_node, body_arg, pipe_args) =
                split_effect_fn_arguments(&call.arguments().to_vec());
            if !is_generator_function_node(body_arg) {
                break 'compute None;
            }
            let gen_fn = body_arg;

            let expr = call.expression();
            if expr.is_nil() || !self.is_node_reference_to_effect_module_api(expr, "gen") {
                break 'compute None;
            }

            let mut effect_module = Node::NIL;
            if expr.kind() == SyntaxKind::PropertyAccessExpression {
                effect_module = expr.expression();
            }

            Some(Rc::new(EffectGenCallResult {
                call,
                effect_module,
                options_node,
                generator_function: gen_fn,
                body: gen_fn.body(),
                pipe_arguments: pipe_args,
            }))
        })
    }
}
