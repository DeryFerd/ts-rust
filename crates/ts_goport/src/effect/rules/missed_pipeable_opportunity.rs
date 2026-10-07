//! Port of Effect-TS/tsgo `internal/rules/missed_pipeable_opportunity.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// MissedPipeableOpportunity detects nested function call chains that can be converted to .pipe() style.
pub static MISSED_PIPEABLE_OPPORTUNITY: Rule = Rule {
    name: "missedPipeableOpportunity",
    group: "style",
    description: "Suggests using .pipe() for nested function calls",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377050],
    run: run_missed_pipeable_opportunity,
};

fn run_missed_pipeable_opportunity(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    // PORT: Go's `ctx.Options` can be nil (then 2); the port always has options.
    let effect_config = ctx.options;
    let min_arg_count = effect_config.get_pipeable_min_arg_count();

    let matches = analyze_missed_pipeable_opportunity(ctx.tp, ctx.source_file, min_arg_count);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_nested_call_structure_has_a_pipeable_form_0_pipe_represents_the_same_call_sequence_in_pipe_style_and_may_be_easier_to_read_effect_missedPipeableOpportunity,
            Vec::new(),
            vec![m.subject_text.clone()],
        ));
    }
    diags
}

// MissedPipeableOpportunityMatch holds the parsed result needed by both the diagnostic rule
// and the quick-fix for the missedPipeableOpportunity pattern.
#[derive(Clone, Debug)]
pub struct MissedPipeableOpportunityMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub pipeable_start_index: i32,
    pub pipeable_transformations: Vec<PipingFlowTransformation>,
    pub flow: Rc<PipingFlow>,
    pub subject_text: String,
    pub after_transformations: Vec<PipingFlowTransformation>,
}

// AnalyzeMissedPipeableOpportunity finds all nested call chains that can be converted to .pipe() style.
pub fn analyze_missed_pipeable_opportunity(
    tp: &mut TypeParser<'_>,
    sf: Node,
    min_arg_count: i64,
) -> Vec<MissedPipeableOpportunityMatch> {
    let flows = tp.piping_flows(sf, false);

    let mut matches = Vec::new();

    for flow in flows.iter() {
        let n = flow.transformations.len();
        // Skip flows with too few transformations
        if (n as i64) < min_arg_count {
            continue;
        }

        // Skip if final output type is callable (has call signatures)
        let last_transformation = &flow.transformations[n - 1];
        if last_transformation.out_type.is_some() {
            let call_sigs = tp
                .checker
                .get_signatures_of_type_exported(last_transformation.out_type, SignatureKind::CALL);
            if !call_sigs.is_empty() {
                continue;
            }
        }

        // Search for valid pipeable segments
        let mut search_start_index: usize = 0;

        while search_start_index <= n {
            // Find the first pipeable type starting from searchStartIndex
            let mut first_pipeable_index: Option<usize> = None;

            for i in search_start_index..=n {
                if is_pipeable_at_index(tp, flow, i) {
                    first_pipeable_index = Some(i);
                    break;
                }
            }

            let Some(first_pipeable_index) = first_pipeable_index else {
                break;
            };

            // Collect transformations while their callees are safely pipeable
            let mut pipeable_transformations: Vec<PipingFlowTransformation> = Vec::new();

            for i in first_pipeable_index..n {
                let t = &flow.transformations[i];
                if !tp.is_safely_pipeable_callee(t.callee) {
                    break;
                }
                pipeable_transformations.push(t.clone());
            }

            // Count "call" kind transformations
            let mut call_kind_count: i64 = 0;
            for t in &pipeable_transformations {
                if t.kind == TransformationKind::Call {
                    call_kind_count += 1;
                }
            }

            if call_kind_count >= min_arg_count {
                let pipeable_end_index = first_pipeable_index + pipeable_transformations.len();

                // Get subject text for the diagnostic message
                let subject_text = get_subject_text(sf, flow, first_pipeable_index);

                let after_transformations = flow.transformations[pipeable_end_index..].to_vec();

                matches.push(MissedPipeableOpportunityMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, flow.node),
                    pipeable_start_index: first_pipeable_index as i32,
                    pipeable_transformations,
                    flow: flow.clone(),
                    subject_text,
                    after_transformations,
                });

                // Found and reported a valid segment, move past it (no overlapping diagnostics)
                break;
            }

            // Not enough transformations, try starting from the next position
            search_start_index = first_pipeable_index + pipeable_transformations.len() + 1;
        }
    }

    matches
}

// isPipeableAtIndex checks if the type at a given index in a flow is pipeable.
// Index 0 = subject, index > 0 = transformations[index - 1].outType
fn is_pipeable_at_index(tp: &mut TypeParser<'_>, flow: &PipingFlow, index: usize) -> bool {
    if index == 0 {
        let subject_type = flow.subject.out_type;
        if subject_type.is_nil() {
            return false;
        }
        return tp.is_pipeable_type(subject_type);
    }

    let t = &flow.transformations[index - 1];
    if t.out_type.is_nil() {
        return false;
    }
    tp.is_pipeable_type(t.out_type)
}

// getSubjectText extracts the subject text for the diagnostic message.
// If the pipeable segment starts at index 0, uses the subject node text directly.
// Otherwise, traverses the flow node to find the node at the right depth.
fn get_subject_text(sf: Node, flow: &PipingFlow, first_pipeable_index: usize) -> String {
    if first_pipeable_index == 0 {
        return trimmed_node_text(sf, flow.subject.node);
    }

    // Traverse from flow.node into arguments to find the node at the right depth
    let mut current = flow.node;
    let mut i = flow.transformations.len();
    while i > first_pipeable_index {
        let t = &flow.transformations[i - 1];
        if t.kind == TransformationKind::Call && is_call_expression(current) {
            let call = current;
            if !call.arguments().is_empty() {
                current = call.arguments().get(0);
            } else {
                return String::new();
            }
        } else {
            return String::new();
        }
        i -= 1;
    }
    trimmed_node_text(sf, current)
}

// trimmedNodeText extracts the source text of a node, trimmed of leading trivia.
fn trimmed_node_text(sf: Node, node: Node) -> String {
    if node.is_nil() || sf.is_nil() {
        return String::new();
    }
    let text = source_file_text(sf);
    let pos = get_token_pos_of_node(node, sf, false);
    let end = node.end();
    if pos >= 0 && end >= pos && end as usize <= text.len() {
        return text[pos as usize..end as usize].trim().to_string();
    }
    String::new()
}
