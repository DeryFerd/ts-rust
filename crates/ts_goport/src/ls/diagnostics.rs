//! Port of Go `ls/diagnostics.go`.

use crate::ls::prelude::*;

// Go: ls/diagnostics.go:14 getAllDiagnostics
// getAllDiagnostics collects all diagnostics for a file: syntactic, semantic,
// suggestion, and (when declarations are emitted) declaration diagnostics.
// PORT: Go `*compiler.Program` methods are the `ls_program` functions
// (plan contract C3).
pub fn get_all_diagnostics(
    ctx: &Context,
    program: &'static compiler::NewProgram,
    file: Node,
) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    diags.extend(ls_program::get_syntactic_diagnostics(program, ctx, file));
    diags.extend(ls_program::get_semantic_diagnostics(program, ctx, file));
    diags.extend(ls_program::get_suggestion_diagnostics(program, ctx, file));
    if program.options().get_emit_declarations() {
        diags.extend(ls_program::get_declaration_diagnostics(program, ctx, file));
    }
    diags
}

impl LanguageService {
    // Go: ls/diagnostics.go:25 ProvideDiagnostics
    // PORT: Go passes the URI by value; here by reference.
    pub fn provide_diagnostics(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<lsproto::DocumentDiagnosticResponse, GoError> {
        let (program, file) = self.get_program_and_file(uri);

        let diagnostics = get_all_diagnostics(ctx, program, file);

        Ok(
            lsproto::RelatedFullDocumentDiagnosticReportOrUnchangedDocumentDiagnosticReport {
                full_document_diagnostic_report: Some(
                    lsproto::RelatedFullDocumentDiagnosticReport {
                        items: self.to_lsp_diagnostics(ctx, &[diagnostics.as_slice()]),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            },
        )
    }

    // Go: ls/diagnostics.go:37 toLSPDiagnostics
    // PORT: the Go variadic `...[]*ast.Diagnostic` is a slice of slices.
    pub fn to_lsp_diagnostics(
        &self,
        ctx: &Context,
        diagnostics: &[&[Diagnostic]],
    ) -> Vec<lsproto::Diagnostic> {
        let mut size = 0;
        for diag_slice in diagnostics {
            size += diag_slice.len();
        }
        let mut lsp_diagnostics: Vec<lsproto::Diagnostic> = Vec::with_capacity(size);
        for diag_slice in diagnostics {
            for diag in diag_slice.iter() {
                lsp_diagnostics.push(lsconv::diagnostic_to_lsp_pull(
                    ctx,
                    &self.converters,
                    diag,
                    self.user_preferences()
                        .report_style_checks_as_warnings
                        .is_true(),
                ));
            }
        }
        lsp_diagnostics
    }
}
