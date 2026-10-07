//! Port of Effect-TS/tsgo `internal/rules/unnecessary_pipe_chain.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// UnnecessaryPipeChain detects chained pipe() and .pipe() calls that can
/// be simplified to a single pipe call.
pub static UNNECESSARY_PIPE_CHAIN: Rule = Rule {
    name: "unnecessaryPipeChain",
    group: "style",
    description: "Simplifies chained pipe calls into a single pipe call",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377015],
    run: run_unnecessary_pipe_chain,
};

fn run_unnecessary_pipe_chain(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_unnecessary_pipe_chain(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_expression_contains_chained_pipe_calls_that_can_be_simplified_to_a_single_pipe_call_effect_unnecessaryPipeChain,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// UnnecessaryPipeChainMatch holds the diagnostic and parsed pipe call results
/// needed by both the diagnostic rule and the quick-fix.
#[derive(Clone, Debug)]
pub struct UnnecessaryPipeChainMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The outer pipe call parse result
    pub outer: Rc<ParsedPipeCallResult>,
    /// The inner pipe call parse result (subject of outer)
    pub inner: Rc<ParsedPipeCallResult>,
}

/// AnalyzeUnnecessaryPipeChain finds all chained pipe() and .pipe() calls
/// (outer pipe whose subject is also a pipe call), returning matches with
/// the diagnostic and both parsed results.
pub fn analyze_unnecessary_pipe_chain(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<UnnecessaryPipeChainMatch> {
    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<UnnecessaryPipeChainMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression {
            if let Some(result) = tp.parse_pipe_call(n) {
                if let Some(inner) = tp.parse_pipe_call(result.subject) {
                    if pipe_merge_supports_arity(tp, &inner, &result) {
                        matches.push(UnnecessaryPipeChainMatch {
                            source_file: sf,
                            location: get_error_range_for_node(sf, result.node),
                            outer: result,
                            inner,
                        });
                    }
                }
            }
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);
    matches
}

fn pipe_merge_supports_arity(
    tp: &mut TypeParser<'_>,
    inner: &ParsedPipeCallResult,
    outer: &ParsedPipeCallResult,
) -> bool {
    if contains_spread_argument(&inner.args) || contains_spread_argument(&outer.args) {
        return false;
    }

    let mut argument_count = (inner.args.len() + outer.args.len()) as i32;
    if inner.kind == TransformationKind::Pipe {
        argument_count += 1; // Standalone pipe retains its subject as the first argument.
    }

    let callee_type = tp.get_type_at_location(inner.node.expression());
    for signature in tp
        .checker
        .get_signatures_of_type_exported(callee_type, SignatureKind::CALL)
    {
        let sig = tp.checker.sig(signature);
        if argument_count < sig.min_argument_count() {
            continue;
        }
        if sig.has_rest_parameter() || argument_count <= sig.parameters().len() as i32 {
            return true;
        }
    }
    false
}

fn contains_spread_argument(args: &[Node]) -> bool {
    for &arg in args {
        if arg.is_some() && arg.kind() == SyntaxKind::SpreadElement {
            return true;
        }
    }
    false
}
