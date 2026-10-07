//! Port of Effect-TS/tsgo `internal/rules/obsolete_schema_import.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.ObsoleteSchemaImport
pub static OBSOLETE_SCHEMA_IMPORT: Rule = Rule {
    name: "obsoleteSchemaImport",
    group: "correctness",
    description: "Warns when importing @effect/schema in projects targeting Effect v4, where Schema is included directly in the effect package",
    default_severity: Severity::Warning,
    supported_effect: &["v4"],
    codes: &[377128],
    run: run_obsolete_schema_import,
};

fn run_obsolete_schema_import(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_obsolete_schema_import(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_module_reference_imports_0_which_is_obsolete_in_Effect_v4_In_Effect_v4_Schema_is_provided_directly_by_Schema_from_effect_or_effect_SlashSchema_effect_obsoleteSchemaImport,
            Vec::new(),
            vec![m.imported_specifier.clone()],
        ));
    }
    diags
}

// Go: rules.ObsoleteSchemaImportMatch
#[derive(Clone)]
pub struct ObsoleteSchemaImportMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub imported_specifier: String,
}

// Go: rules.AnalyzeObsoleteSchemaImport
// PORT: Go also returns nil for a nil type parser; the Rust one is never nil.
pub fn analyze_obsolete_schema_import(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ObsoleteSchemaImportMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    let is_obsolete_schema_specifier = |specifier: &str| -> bool {
        specifier == "@effect/schema" || specifier.starts_with("@effect/schema/")
    };

    for stmt in sf.statements() {
        match stmt.kind() {
            SyntaxKind::ImportDeclaration => {
                let import_decl = stmt;
                if import_decl.module_specifier().is_nil()
                    || import_decl.module_specifier().kind() != SyntaxKind::StringLiteral
                {
                    continue;
                }
                let specifier = import_decl.module_specifier().text();
                if is_obsolete_schema_specifier(specifier) {
                    matches.push(ObsoleteSchemaImportMatch {
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
                if is_obsolete_schema_specifier(specifier) {
                    matches.push(ObsoleteSchemaImportMatch {
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
                for decl_node in decl_list.declarations().nodes() {
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
                    if call_expr.arguments().len() != 1 {
                        continue;
                    }
                    let arg = call_expr.arguments().get(0);
                    if arg.kind() != SyntaxKind::StringLiteral {
                        continue;
                    }
                    let specifier = arg.text();
                    if is_obsolete_schema_specifier(specifier) {
                        matches.push(ObsoleteSchemaImportMatch {
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
