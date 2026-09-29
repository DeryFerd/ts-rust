//! Port of Go `ls/diagnostics.go`.

use crate::ls::prelude::*;

use crate::spanmap::{Fidelity, SpanMap};

// Go: ls/diagnostics.go:18 getAllDiagnostics
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
    let mut files = vec![file];
    files.extend_from_slice(source_file_supplemental_source_files(file));
    for source_file in files {
        diags.extend(ls_program::get_syntactic_diagnostics(program, ctx, source_file));
        diags.extend(ls_program::get_semantic_diagnostics(program, ctx, source_file));
        diags.extend(ls_program::get_suggestion_diagnostics(program, ctx, source_file));
        if program.options().get_emit_declarations() {
            diags.extend(ls_program::get_declaration_diagnostics(program, ctx, source_file));
        }
    }
    diags
}

impl LanguageService {
    // Go: ls/diagnostics.go:32 ProvideDiagnostics
    // PORT: Go passes the URI by value; here by reference.
    pub fn provide_diagnostics(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<lsproto::DocumentDiagnosticResponse, GoError> {
        let (program, file) = self.get_program_and_file(uri);

        if self.user_preferences().enable_validation.is_false() {
            return Ok(
                lsproto::RelatedFullDocumentDiagnosticReportOrUnchangedDocumentDiagnosticReport {
                    full_document_diagnostic_report: Some(
                        lsproto::RelatedFullDocumentDiagnosticReport {
                            items: Vec::new(),
                            ..Default::default()
                        },
                    ),
                    ..Default::default()
                },
            );
        }

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

    // Go: ls/diagnostics.go:53 toLSPDiagnostics
    // PORT: the Go variadic `...[]*ast.Diagnostic` is a slice of slices.
    pub fn to_lsp_diagnostics(
        &self,
        ctx: &Context,
        diagnostics: &[&[Diagnostic]],
    ) -> Vec<lsproto::Diagnostic> {
        let report_style_checks_as_warnings = self
            .user_preferences()
            .report_style_checks_as_warnings
            .is_true();
        let mut size = 0;
        for diag_slice in diagnostics {
            size += diag_slice.len();
        }
        let mut lsp_diagnostics: Vec<lsproto::Diagnostic> = Vec::with_capacity(size);
        // Compiler diagnostics located entirely in a content-mapped file's synthesized code have no location
        // in the original file. Collect them per file and surface them through a single aggregate at the top
        // of the file (with the real messages as related information) rather than dropping them or scattering
        // them at position 0.
        // PORT: Go `collections.OrderedMap`; `IndexMap` keeps the same
        // insertion order.
        let mut synthesized_by_file: IndexMap<Node, Vec<Diagnostic>> = IndexMap::new();
        for diag_slice in diagnostics {
            for diag in diag_slice.iter() {
                if is_synthesized_content_mapped_diagnostic(diag) {
                    synthesized_by_file
                        .entry(diag.file())
                        .or_default()
                        .push(diag.clone());
                    continue;
                }
                lsp_diagnostics.push(lsconv::diagnostic_to_lsp_pull(
                    ctx,
                    &self.converters,
                    diag,
                    report_style_checks_as_warnings,
                ));
            }
        }
        for (&file, diags) in &synthesized_by_file {
            let aggregate = aggregate_synthesized_diagnostics(file, diags);
            lsp_diagnostics.push(lsconv::diagnostic_to_lsp_pull(
                ctx,
                &self.converters,
                &aggregate,
                report_style_checks_as_warnings,
            ));
        }
        lsp_diagnostics
    }
}

// Go: ls/diagnostics.go:84 isSynthesizedContentMappedDiagnostic
// isSynthesizedContentMappedDiagnostic reports whether diag is a compiler diagnostic on a content-mapped
// file whose location lies entirely in synthesized virtual code with no counterpart in the original
// file, and so has no meaningful position to report against the original file.
pub fn is_synthesized_content_mapped_diagnostic(diag: &Diagnostic) -> bool {
    let file = diag.file();
    // PORT: Go `file == nil || file.SpanMap() == nil`; the span map of a nil
    // file is `None`.
    let Some(span_map) = source_file_span_map(file) else {
        return false;
    };
    if !diag.source().is_empty() {
        return false;
    }
    let (_, fidelity) = SpanMap::virtual_to_original_span(Some(span_map), diag.loc());
    fidelity == Fidelity::NONE
}

// Go: ls/diagnostics.go:97 aggregateSynthesizedDiagnostics
// aggregateSynthesizedDiagnostics builds a single diagnostic at the top of a content-mapped file standing
// in for compiler diagnostics located in synthesized code with no original location. The originals are
// attached as related information so their messages are surfaced rather than silently dropped. (A later
// change will point the related locations at a read-only view of the file's virtual TypeScript.)
pub fn aggregate_synthesized_diagnostics(file: Node, diags: &[Diagnostic]) -> Diagnostic {
    let mut aggregate = new_diagnostic(
        file,
        TextRange::new(0, 0),
        diag::Virtual_code_produced_by_the_content_mapper_0_has_problems_with_no_corresponding_location_in_this_file,
        vec![source_file_content_mapper(file).to_string()],
    );
    aggregate.set_related_info(diags.to_vec());
    aggregate.set_category(worst_category(diags));
    aggregate
}

// Go: ls/diagnostics.go:109 worstCategory
pub fn worst_category(diags: &[Diagnostic]) -> ts_diagnostics::Category {
    let mut worst = diags[0].category();
    for diag in diags {
        match diag.category() {
            ts_diagnostics::Category::Error => return ts_diagnostics::Category::Error,
            ts_diagnostics::Category::Warning => {
                worst = ts_diagnostics::Category::Warning;
            }
            _ => {}
        }
    }
    worst
}
