//! Port of Effect-TS/tsgo `internal/typeparser/effect_fn.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

// PORT: Go `type EffectFnVariant string`. `as_str` gives the Go string.
// Go: typeparser/effect_fn.go EffectFnVariant
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EffectFnVariant {
    Fn,
    FnUntraced,
    FnUntracedEager,
}

impl EffectFnVariant {
    /// The Go string value of the variant.
    pub const fn as_str(self) -> &'static str {
        match self {
            EffectFnVariant::Fn => "fn",
            EffectFnVariant::FnUntraced => "fnUntraced",
            EffectFnVariant::FnUntracedEager => "fnUntracedEager",
        }
    }
}

impl std::fmt::Display for EffectFnVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// EffectFnCallResult represents a parsed Effect.fn-family call.
// Go: typeparser/effect_fn.go EffectFnCallResult
#[derive(Clone)]
pub struct EffectFnCallResult {
    pub call: Node,
    pub variant: EffectFnVariant,
    pub effect_module: Node,
    pub options_node: Node,
    /// ArrowFunction or FunctionExpression
    pub function_node: Node,
    pub function_return_type: TypeId,
    /// Transformation args after the body (may be empty/nil)
    pub pipe_arguments: Vec<Node>,
    pub pipe_args_out_type: Vec<TypeId>,
    /// The name string from curried Effect.fn("name")(...), or nil
    pub trace_expression: Node,
}

impl EffectFnCallResult {
    // Go: typeparser/effect_fn.go EffectFnCallResult.IsGenerator
    pub fn is_generator(&self) -> bool {
        self.generator_function().is_some()
    }

    // Go: typeparser/effect_fn.go EffectFnCallResult.GeneratorFunction
    pub fn generator_function(&self) -> Node {
        if self.function_node.is_nil()
            || self.function_node.kind() != SyntaxKind::FunctionExpression
        {
            return Node::NIL;
        }
        let fn_ = self.function_node;
        if fn_.asterisk_token().is_nil() {
            return Node::NIL;
        }
        fn_
    }

    // Go: typeparser/effect_fn.go EffectFnCallResult.Body
    pub fn body(&self) -> Node {
        if self.function_node.is_nil() {
            return Node::NIL;
        }
        match self.function_node.kind() {
            SyntaxKind::ArrowFunction => {
                let fn_ = self.function_node;
                fn_.body()
            }
            SyntaxKind::FunctionExpression => {
                let fn_ = self.function_node;
                fn_.body()
            }
            _ => Node::NIL,
        }
    }
}

// Go: typeparser/effect_fn.go splitEffectFnArguments
pub fn split_effect_fn_arguments(args: &[Node]) -> (Node, Node, Vec<Node>) {
    let mut start = 0;
    let mut options = Node::NIL;
    if !args.is_empty() {
        let first = args[0];
        if first.is_some()
            && first.kind() != SyntaxKind::ArrowFunction
            && first.kind() != SyntaxKind::FunctionExpression
        {
            options = first;
            start = 1;
        }
    }
    for i in start..args.len() {
        let arg = args[i];
        if arg.is_nil() {
            continue;
        }
        match arg.kind() {
            SyntaxKind::ArrowFunction | SyntaxKind::FunctionExpression => {
                if i + 1 < args.len() {
                    return (options, arg, args[i + 1..].to_vec());
                }
                return (options, arg, Vec::new());
            }
            _ => {}
        }
    }
    (options, Node::NIL, Vec::new())
}

// Go: typeparser/effect_fn.go isGeneratorFunctionNode
pub fn is_generator_function_node(node: Node) -> bool {
    if node.is_nil() || node.kind() != SyntaxKind::FunctionExpression {
        return false;
    }
    let fn_ = node;
    fn_.asterisk_token().is_some()
}

impl TypeParser<'_> {
    // Go: typeparser/effect_fn.go buildEffectFnPipeArgsOutType
    fn build_effect_fn_pipe_args_out_type(
        &mut self,
        call: Node,
        trailing_start_index: usize,
        pipe_args: &[Node],
    ) -> Vec<TypeId> {
        let mut out_types = vec![TypeId::NIL; pipe_args.len()];
        if call.is_nil() {
            return out_types;
        }

        let call_node = call;
        for i in 0..pipe_args.len() {
            let arg_index = trailing_start_index + i;
            let contextual_type = self
                .checker
                .get_contextual_type_for_argument_at_index_exported(call_node, arg_index as i32);
            if contextual_type.is_nil() {
                continue;
            }
            let call_sigs = self
                .checker
                .get_signatures_of_type_exported(contextual_type, SignatureKind::CALL);
            if call_sigs.is_empty() {
                continue;
            }
            out_types[i] = self
                .checker
                .get_return_type_of_signature_exported(call_sigs[0]);
        }

        out_types
    }

    // Go: typeparser/effect_fn.go buildEffectFnFunctionReturnType
    fn build_effect_fn_function_return_type(
        &mut self,
        call: Node,
        trailing_start_index: usize,
        pipe_args: &[Node],
    ) -> TypeId {
        if call.is_nil() {
            return TypeId::NIL;
        }

        if pipe_args.is_empty() {
            let fn_type = self.get_type_at_location(call);
            if fn_type.is_nil() {
                return TypeId::NIL;
            }
            let call_sigs = self
                .checker
                .get_signatures_of_type_exported(fn_type, SignatureKind::CALL);
            if call_sigs.is_empty() {
                return TypeId::NIL;
            }
            return self
                .checker
                .get_return_type_of_signature_exported(call_sigs[0]);
        }

        let resolved = self.checker.get_resolved_signature_exported(call);
        if resolved.is_nil() {
            return TypeId::NIL;
        }
        let params = self.checker.sig(resolved).parameters().to_vec();
        if trailing_start_index >= params.len() {
            return TypeId::NIL;
        }
        let first_pipe_param_type = self
            .checker
            .get_type_of_symbol_at_location(params[trailing_start_index], pipe_args[0]);
        if first_pipe_param_type.is_nil() {
            return TypeId::NIL;
        }
        let first_pipe_call_sigs = self
            .checker
            .get_signatures_of_type_exported(first_pipe_param_type, SignatureKind::CALL);
        if first_pipe_call_sigs.is_empty() {
            return TypeId::NIL;
        }
        let pipe_input_params = self
            .checker
            .sig(first_pipe_call_sigs[0])
            .parameters()
            .to_vec();
        if pipe_input_params.is_empty() {
            return TypeId::NIL;
        }
        self.checker
            .get_type_of_symbol_at_location(pipe_input_params[0], pipe_args[0])
    }

    /// EffectFnCall parses a node as an Effect.fn-family call.
    /// It supports fn, fnUntraced, and fnUntracedEager, both regular and generator forms.
    // Go: typeparser/effect_fn.go EffectFnCall
    pub fn effect_fn_call(&mut self, node: Node) -> Option<Rc<EffectFnCallResult>> {
        if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
            return None;
        }

        cached!(self, effect_fn_call, node, 'compute: {
            let call = node;
            if call.argument_list().is_nil() || call.arguments().is_empty() {
                break 'compute None;
            }

            let arguments = call.arguments().to_vec();
            let (options_node, body_arg, pipe_args) = split_effect_fn_arguments(&arguments);
            if body_arg.is_nil() {
                break 'compute None;
            }
            let trailing_start_index = arguments.len() - pipe_args.len();

            // Determine the expression to check for Effect.fn reference.
            // For curried calls like Effect.fn("name")(regularFn), call.Expression is a CallExpression.
            // For direct calls like Effect.fn(regularFn), call.Expression is a PropertyAccessExpression.
            let expr = call.expression();
            if expr.is_nil() {
                break 'compute None;
            }

            let expression_to_check: Node;
            let mut trace_expression = Node::NIL;
            let variant: EffectFnVariant;

            if expr.kind() == SyntaxKind::CallExpression {
                let inner_call = expr;
                if inner_call.expression().is_nil() {
                    break 'compute None;
                }
                expression_to_check = inner_call.expression();

                // Extract trace expression from curried form: Effect.fn("name")(...)
                if !inner_call.argument_list().is_nil() && !inner_call.arguments().is_empty() {
                    trace_expression = inner_call.arguments().get(0);
                }
            } else {
                expression_to_check = expr;
            }

            if expression_to_check.is_nil() {
                break 'compute None;
            }

            if self.is_node_reference_to_effect_module_api(expression_to_check, "fn") {
                variant = EffectFnVariant::Fn;
            } else if self.is_node_reference_to_effect_module_api(expression_to_check, "fnUntraced")
            {
                if trace_expression.is_some() {
                    break 'compute None;
                }
                variant = EffectFnVariant::FnUntraced;
            } else if self
                .is_node_reference_to_effect_module_api(expression_to_check, "fnUntracedEager")
            {
                if trace_expression.is_some() {
                    break 'compute None;
                }
                variant = EffectFnVariant::FnUntracedEager;
            } else {
                break 'compute None;
            }

            let mut effect_module = Node::NIL;
            if expression_to_check.kind() == SyntaxKind::PropertyAccessExpression {
                let property_access = expression_to_check;
                effect_module = property_access.expression();
            }

            Some(Rc::new(EffectFnCallResult {
                call,
                variant,
                effect_module,
                options_node,
                function_node: body_arg,
                function_return_type: self.build_effect_fn_function_return_type(
                    call,
                    trailing_start_index,
                    &pipe_args,
                ),
                pipe_args_out_type: self.build_effect_fn_pipe_args_out_type(
                    call,
                    trailing_start_index,
                    &pipe_args,
                ),
                pipe_arguments: pipe_args,
                trace_expression,
            }))
        })
    }
}
