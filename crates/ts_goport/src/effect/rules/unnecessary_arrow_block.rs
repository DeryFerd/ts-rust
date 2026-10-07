//! Port of Effect-TS/tsgo `internal/rules/unnecessary_arrow_block.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// UnnecessaryArrowBlock suggests using a concise arrow body when a block only
/// contains a single return statement.
// Go: rules/unnecessary_arrow_block.go UnnecessaryArrowBlock
pub static UNNECESSARY_ARROW_BLOCK: Rule = Rule {
    name: "unnecessaryArrowBlock",
    group: "style",
    description: "Suggests using a concise arrow body when the block only returns an expression",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377084],
    run: run_unnecessary_arrow_block,
};

fn run_unnecessary_arrow_block(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_unnecessary_arrow_block(ctx.tp, sf);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_arrow_function_block_only_returns_an_expression_and_can_use_a_concise_body_effect_unnecessaryArrowBlock,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

// Go: rules/unnecessary_arrow_block.go UnnecessaryArrowBlockMatch
#[derive(Clone, Debug)]
pub struct UnnecessaryArrowBlockMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub arrow_function: Node,
    pub body_block: Node,
    pub returned_expression: Node,
}

// Go: rules/unnecessary_arrow_block.go AnalyzeUnnecessaryArrowBlock
pub fn analyze_unnecessary_arrow_block(
    _tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<UnnecessaryArrowBlockMatch> {
    let mut matches = Vec::new();

    fn walk(sf: Node, matches: &mut Vec<UnnecessaryArrowBlockMatch>, n: Node) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::ArrowFunction
            && let Some(m) = analyze_unnecessary_arrow_block_node(sf, n)
        {
            matches.push(m);
        }

        n.for_each_child(|child| walk(sf, matches, child));
        false
    }

    walk(sf, &mut matches, sf);
    matches
}

// Go: rules/unnecessary_arrow_block.go analyzeUnnecessaryArrowBlockNode
fn analyze_unnecessary_arrow_block_node(sf: Node, n: Node) -> Option<UnnecessaryArrowBlockMatch> {
    let arrow_fn = n;
    if arrow_fn.is_nil() || arrow_fn.body().is_nil() || arrow_fn.body().kind() != SyntaxKind::Block
    {
        return None;
    }

    let body = arrow_fn.body();
    // PORT: Go also returns nil for a nil `Statements` list; an empty slice
    // has the same result.
    if body.statements().len() != 1 {
        return None;
    }

    let stmt = body.statements().get(0);
    if stmt.is_nil() || stmt.kind() != SyntaxKind::ReturnStatement {
        return None;
    }

    let returned_expression = stmt.expression();
    if returned_expression.is_nil() {
        return None;
    }

    Some(UnnecessaryArrowBlockMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, arrow_fn.body()),
        arrow_function: n,
        body_block: arrow_fn.body(),
        returned_expression,
    })
}
