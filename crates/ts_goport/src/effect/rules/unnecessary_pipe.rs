// Go: internal/rules/unnecessary_pipe.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// UnnecessaryPipe detects pipe() and .pipe() calls with no transformation
/// arguments and suggests removing the unnecessary pipe wrapper.
pub static UNNECESSARY_PIPE: Rule = Rule {
    name: "unnecessaryPipe",
    group: "style",
    description: "Removes pipe calls with no arguments",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377013],
    run: run_unnecessary_pipe,
};

fn run_unnecessary_pipe(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_unnecessary_pipe(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_pipe_call_contains_no_arguments_effect_unnecessaryPipe,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// UnnecessaryPipeMatch holds the diagnostic and parsed pipe call result needed
/// by both the diagnostic rule and the quick-fix.
#[derive(Clone, Debug)]
pub struct UnnecessaryPipeMatch {
    /// The source file where this match was found
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The parsed pipe call (contains Subject node and call Node)
    pub result: Rc<ParsedPipeCallResult>,
}

// Go: rules/unnecessary_pipe.go AnalyzeUnnecessaryPipe
/// AnalyzeUnnecessaryPipe finds all pipe() and .pipe() calls with no transformation
/// arguments, returning matches with both the diagnostic and the parsed result.
pub fn analyze_unnecessary_pipe(tp: &mut TypeParser<'_>, sf: Node) -> Vec<UnnecessaryPipeMatch> {
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<UnnecessaryPipeMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression {
            if let Some(result) = tp.parse_pipe_call(n) {
                if result.args.is_empty() {
                    matches.push(UnnecessaryPipeMatch {
                        source_file: sf,
                        location: get_error_range_for_node(sf, result.node),
                        result,
                    });
                }
            }
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    let mut matches = Vec::new();
    walk(tp, sf, &mut matches, sf);
    matches
}
