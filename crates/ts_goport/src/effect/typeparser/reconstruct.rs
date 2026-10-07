//! Port of Effect-TS/tsgo `internal/typeparser/reconstruct.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: typeparser/reconstruct.go nodeText
/// nodeText extracts the source text of a node from the source file.
pub fn node_text(sf: Node, node: Node) -> String {
    if node.is_nil() || sf.is_nil() {
        return String::new();
    }
    let text = source_file_text(sf);
    let pos = node.pos();
    let end = node.end();
    if pos >= 0 && end >= pos && end as usize <= text.len() {
        return go_cut_slice(&text, pos as usize, end as usize).into_owned();
    }
    String::new()
}

// Go: typeparser/reconstruct.go ReconstructPipingFlow
/// ReconstructPipingFlow reconstructs a piping flow into a string expression
/// by applying transformations sequentially.
/// For example: subject with transformations [f, g] becomes "g(f(subject))".
///
/// Note: Effect.fn and Effect.fnUntraced transformations cannot be reconstructed
/// as a chain since they are part of the Effect.fn call itself. In this case,
/// the original subject node text is returned.
pub fn reconstruct_piping_flow(
    sf: Node,
    subject: Option<&PipingFlowSubject>,
    transformations: &[PipingFlowTransformation],
) -> String {
    let Some(subject) = subject else {
        return String::new();
    };
    if sf.is_nil() {
        return String::new();
    }

    // Check if all transformations are effectFn or effectFnUntraced.
    // In this case, reconstruction is not possible - return the original node text.
    if !transformations.is_empty() {
        let mut all_effect_fn = true;
        for t in transformations {
            if t.kind != TransformationKind::EffectFn
                && t.kind != TransformationKind::EffectFnUntraced
            {
                all_effect_fn = false;
                break;
            }
        }
        if all_effect_fn {
            return node_text(sf, subject.node);
        }
    }

    let mut result = node_text(sf, subject.node);

    for t in transformations {
        if t.kind == TransformationKind::EffectFn || t.kind == TransformationKind::EffectFnUntraced
        {
            // Effect.fn transformations cannot be reconstructed as part of a chain
            continue;
        }

        let callee_text = node_text(sf, t.callee);

        if t.kind == TransformationKind::Call {
            // Single-arg call: callee(result)
            result = callee_text + "(" + &result + ")";
        } else {
            // Pipe or pipeable: apply the transformation
            if !t.args.is_empty() {
                // Curried form: callee(args...)(result)
                let mut args_text = String::new();
                for (i, &arg) in t.args.iter().enumerate() {
                    if i > 0 {
                        args_text.push_str(", ");
                    }
                    args_text.push_str(&node_text(sf, arg));
                }
                result = callee_text + "(" + &args_text + ")(" + &result + ")";
            } else {
                // Constant: callee(result)
                result = callee_text + "(" + &result + ")";
            }
        }
    }

    result
}
