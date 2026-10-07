// Go: internal/rules/obsolete_match_import.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static OBSOLETE_MATCH_IMPORT: Rule = Rule {
    name: "obsoleteMatchImport",
    group: "correctness",
    description: "Warns when importing @effect/match in projects targeting Effect v4, where Match is included directly in the effect package",
    default_severity: Severity::Warning,
    supported_effect: &["v4"],
    codes: &[377129],
    run: run_obsolete_match_import,
};

fn run_obsolete_match_import(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_obsolete_match_import(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_module_reference_imports_0_which_is_obsolete_in_Effect_v4_In_Effect_v4_pattern_matching_is_provided_directly_by_Match_from_effect_or_effect_SlashMatch_effect_obsoleteMatchImport,
            Vec::new(),
            vec![m.imported_specifier.clone()],
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct ObsoleteMatchImportMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub imported_specifier: String,
}

// Go: rules/obsolete_match_import.go AnalyzeObsoleteMatchImport
pub fn analyze_obsolete_match_import(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ObsoleteMatchImportMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    let is_obsolete_match_specifier = |specifier: &str| -> bool {
        specifier == "@effect/match" || specifier.starts_with("@effect/match/")
    };

    for stmt in sf.statements().iter() {
        match stmt.kind() {
            SyntaxKind::ImportDeclaration => {
                let import_decl = stmt;
                if import_decl.module_specifier().is_nil()
                    || import_decl.module_specifier().kind() != SyntaxKind::StringLiteral
                {
                    continue;
                }
                let specifier = import_decl.module_specifier().text();
                if is_obsolete_match_specifier(specifier) {
                    matches.push(ObsoleteMatchImportMatch {
                        source_file: sf,
                        location: get_error_range_for_node(sf, import_decl.module_specifier()),
                        imported_specifier: specifier.to_string(),
                    });
                }
            }

            SyntaxKind::ExportDeclaration => {
                let export_decl = stmt;
                if export_decl.module_specifier().is_nil()
                    || export_decl.module_specifier().kind() != SyntaxKind::StringLiteral
                {
                    continue;
                }
                let specifier = export_decl.module_specifier().text();
                if is_obsolete_match_specifier(specifier) {
                    matches.push(ObsoleteMatchImportMatch {
                        source_file: sf,
                        location: get_error_range_for_node(sf, export_decl.module_specifier()),
                        imported_specifier: specifier.to_string(),
                    });
                }
            }

            SyntaxKind::VariableStatement => {
                let var_stmt = stmt;
                if var_stmt.declaration_list().is_nil() {
                    continue;
                }
                let decl_list = var_stmt.declaration_list();
                if decl_list.declarations().is_nil() {
                    continue;
                }
                for decl_node in decl_list.declarations().nodes().iter() {
                    let decl = decl_node;
                    if decl.initializer().is_nil()
                        || decl.initializer().kind() != SyntaxKind::CallExpression
                    {
                        continue;
                    }
                    let call_expr = decl.initializer();
                    if call_expr.expression().is_nil()
                        || call_expr.expression().kind() != SyntaxKind::Identifier
                    {
                        continue;
                    }
                    if get_text_of_node(call_expr.expression()) != "require" {
                        continue;
                    }
                    if call_expr.argument_list().is_nil() || call_expr.arguments().len() != 1 {
                        continue;
                    }
                    let arg = call_expr.arguments().get(0);
                    if arg.kind() != SyntaxKind::StringLiteral {
                        continue;
                    }
                    let specifier = arg.text();
                    if is_obsolete_match_specifier(specifier) {
                        matches.push(ObsoleteMatchImportMatch {
                            source_file: sf,
                            location: get_error_range_for_node(sf, arg),
                            imported_specifier: specifier.to_string(),
                        });
                    }
                }
            }

            _ => {}
        }
    }

    matches
}
