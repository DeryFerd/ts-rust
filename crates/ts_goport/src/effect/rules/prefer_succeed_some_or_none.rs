//! Port of Effect-TS/tsgo `internal/rules/prefer_succeed_some_or_none.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// PreferSucceedSomeOrNone suggests Effect.succeedNone and Effect.succeedSome for
// Effect.succeed calls that directly wrap Option.none or Option.some.
pub static PREFER_SUCCEED_SOME_OR_NONE: Rule = Rule {
    name: "preferSucceedSomeOrNone",
    group: "style",
    description: "Suggests using Effect.succeedNone or Effect.succeedSome instead of wrapping Option.none or Option.some with Effect.succeed",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377117],
    run: run_prefer_succeed_some_or_none,
};

fn run_prefer_succeed_some_or_none(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_prefer_succeed_some_or_none(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_0_expresses_this_Option_success_value_directly_effect_preferSucceedSomeOrNone,
            Vec::new(),
            vec![m.replacement_name.clone()],
        ));
    }
    diagnostics
}

// PreferSucceedSomeOrNoneMatch holds the nodes needed by the diagnostic and quick fix.
#[derive(Clone, Debug)]
pub struct PreferSucceedSomeOrNoneMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub flow: Option<Rc<PipingFlow>>,
    pub transformation_count: i32,
    pub effect_module_node: Node,
    pub replacement_name: String,
    pub value_node: Node,
    pub value_type_arguments: NodeList,
}

#[derive(Clone, Debug)]
struct NormalizedOptionInput {
    replacement_name: String,
    value_node: Node,
    value_type_arguments: NodeList,
}

// AnalyzePreferSucceedSomeOrNone finds piping flows in which Option.none or
// Option.some feeds directly into Effect.succeed. This covers both nested calls
// and pipe forms such as Option.none().pipe(Effect.succeed).
pub fn analyze_prefer_succeed_some_or_none(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<PreferSucceedSomeOrNoneMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        let mut is_succeed =
            |tp: &mut TypeParser<'_>, transformation: &PipingFlowTransformation| -> bool {
                transformation.callee.is_some()
                    && transformation.args.is_empty()
                    && (transformation.type_arguments.is_nil()
                        || transformation.type_arguments.nodes().is_empty())
                    && tp.is_node_reference_to_effect_module_api(transformation.callee, "succeed")
            };
        let mut is_none_subject = |tp: &mut TypeParser<'_>, subject: &PipingFlowSubject| -> bool {
            is_option_none_call(tp, subject.node)
        };
        if flow.matches_prefix(tp, &mut is_none_subject, &mut [&mut is_succeed]) {
            matches.push(prefer_succeed_some_or_none_match(
                sf,
                flow,
                0,
                &NormalizedOptionInput {
                    replacement_name: "succeedNone".to_string(),
                    value_node: Node::NIL,
                    value_type_arguments: NodeList::NIL,
                },
            ));
        }

        let mut is_some = |tp: &mut TypeParser<'_>,
                           transformation: &PipingFlowTransformation|
         -> bool {
            transformation.callee.is_some()
                && transformation.args.is_empty()
                && tp.is_node_reference_to_effect_option_module_api(transformation.callee, "some")
        };
        let sequences =
            flow.find_transformation_sequences(tp, &mut [&mut is_some, &mut is_succeed]);
        for sequence in &sequences {
            let option_index = sequence.start;
            matches.push(prefer_succeed_some_or_none_match(
                sf,
                flow,
                option_index + 1,
                &NormalizedOptionInput {
                    replacement_name: "succeedSome".to_string(),
                    value_node: flow.transformation_input_node(option_index),
                    value_type_arguments: flow.transformations[option_index as usize]
                        .type_arguments,
                },
            ));
        }
    }
    matches
}

fn prefer_succeed_some_or_none_match(
    sf: Node,
    flow: &Rc<PipingFlow>,
    succeed_index: i32,
    option_input: &NormalizedOptionInput,
) -> PreferSucceedSomeOrNoneMatch {
    let transformation = &flow.transformations[succeed_index as usize];
    let mut effect_module_node = Node::NIL;
    if transformation.callee.kind() == SyntaxKind::PropertyAccessExpression {
        effect_module_node = transformation.callee.expression();
    }
    let mut m = PreferSucceedSomeOrNoneMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, transformation.callee),
        flow: None,
        transformation_count: 0,
        effect_module_node,
        replacement_name: option_input.replacement_name.clone(),
        value_node: option_input.value_node,
        value_type_arguments: option_input.value_type_arguments,
    };
    if transformation.kind == TransformationKind::Call
        || transformation.kind == TransformationKind::Pipe
        || transformation.kind == TransformationKind::Pipeable
    {
        m.flow = Some(flow.clone());
        m.transformation_count = succeed_index + 1;
    }
    m
}

pub fn is_option_none_call(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
        return false;
    }
    let call = node;
    // PORT: Go also checks `call.Arguments != nil`; a parsed call always has
    // the list, and `arguments()` gives an empty slice for a nil one.
    call.arguments().is_empty()
        && call.type_arguments().is_empty()
        && tp.is_node_reference_to_effect_option_module_api(call.expression(), "none")
}
