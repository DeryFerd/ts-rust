//! Pinned non-pretty error text from retained project inputs and diagnostics.

use std::collections::{BTreeMap, BTreeSet};

use ts_compiler::{Program, ProgramDiagnostic};
use ts_core::SourceText;

use super::{ProjectStage, ProjectTextArtifact, ordered_project_sources};
use crate::{
    CompilationDiagnostic, CompilationDiagnosticOrdering, CompilationRelatedInformation,
    DiagnosticTextContext, HARNESS_NEW_LINE, annotate_diagnostic_source,
    append_annotated_diagnostic_with_context, append_annotation_line,
    compare_compilation_diagnostics, compilation_diagnostic_category,
    diagnostic_ordering_is_authenticated, diagnostic_primary_order_key, is_default_library_file,
    normalize_comparison_path, program_diagnostic_origin,
    recover_structured_compilation_diagnostic, remove_test_path_prefixes,
    render_diagnostic_header_with_context,
};

pub(super) struct ProjectErrors {
    pub(super) file_order: Vec<String>,
    pub(super) output: ProjectStage<ProjectTextArtifact>,
}

enum ErrorTextFailure {
    Unavailable(String),
    Invariant { code: &'static str, detail: String },
}

impl ErrorTextFailure {
    fn into_stage(self) -> ProjectStage<ProjectTextArtifact> {
        match self {
            Self::Unavailable(detail) => ProjectStage::Unavailable { detail },
            Self::Invariant { code, detail } => ProjectStage::Invariant {
                code: code.to_owned(),
                detail,
            },
        }
    }
}

struct ErrorInputs {
    order: Vec<String>,
    texts: BTreeMap<String, SourceText>,
}

pub(super) fn render(program: &Program, diagnostics: &[ProgramDiagnostic]) -> ProjectErrors {
    if diagnostics.is_empty() {
        return ProjectErrors {
            file_order: Vec::new(),
            output: ProjectStage::NoContent {
                detail: "The diagnostic snapshot is empty.".to_owned(),
            },
        };
    }
    match render_nonempty(program, diagnostics) {
        Ok((file_order, text)) => ProjectErrors {
            file_order,
            output: ProjectStage::Complete {
                value: ProjectTextArtifact::new(text),
            },
        },
        Err(error) => ProjectErrors {
            file_order: Vec::new(),
            output: error.into_stage(),
        },
    }
}

fn go_file_name(file_name: &str) -> String {
    file_name.strip_prefix("/__typescript/lib/").map_or_else(
        || file_name.to_owned(),
        |name| format!("bundled:///libs/{name}"),
    )
}

fn is_built_file(file_name: &str) -> bool {
    file_name.starts_with("built/local/") || file_name.starts_with("/.ts/")
}

fn is_config_file(file_name: &str) -> bool {
    file_name.contains("tsconfig") && file_name.contains("json")
}

fn referenced_files(diagnostics: &[ProgramDiagnostic], files: &mut BTreeSet<String>) {
    for diagnostic in diagnostics {
        if let Some(name) = &diagnostic.file_name {
            files.insert(name.clone());
        }
        referenced_files(&diagnostic.related_information, files);
    }
}

fn collect_inputs(
    program: &Program,
    diagnostics: &[ProgramDiagnostic],
) -> Result<ErrorInputs, ErrorTextFailure> {
    let mut order = ordered_project_sources(program, program.ordered_root_file_names())
        .iter()
        .map(|source| source.file_name.clone())
        .collect::<Vec<_>>();
    let mut needed = order.iter().cloned().collect::<BTreeSet<_>>();
    referenced_files(diagnostics, &mut needed);
    let mut texts = BTreeMap::new();
    for name in &needed {
        if name.contains(['\r', '\n', '\0']) {
            return Err(ErrorTextFailure::Unavailable(format!(
                "Error artifact filenames with line breaks or NUL are not supported: {name:?}",
            )));
        }
        if let Some(source) = program.source_file(name) {
            texts.insert(name.clone(), SourceText::from(source.source_text.clone()));
        }
    }
    if needed.iter().any(|name| !texts.contains_key(name)) {
        let graph = program.project_graph_snapshot();
        if let (Some(name), Some(config)) = (graph.config_file_path, graph.config)
            && let Some(source) = config.source_text
            && needed.contains(&name)
        {
            texts.insert(name, SourceText::from(source));
        }
    }
    if let Some(name) = needed.iter().find(|name| !texts.contains_key(*name)) {
        return Err(ErrorTextFailure::Unavailable(format!(
            "No retained diagnostic source text is available for {name:?}. The renderer does not read files again.",
        )));
    }
    let seen = order.iter().cloned().collect::<BTreeSet<_>>();
    let extras = diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.file_name.as_ref())
        .filter(|name| {
            let go_name = go_file_name(name);
            !seen.contains(*name) && !is_default_library_file(&go_name) && !is_built_file(&go_name)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    order.extend(extras);
    Ok(ErrorInputs { order, texts })
}

fn validate_diagnostic(
    diagnostic: &ProgramDiagnostic,
    inputs: &ErrorInputs,
) -> Result<(), ErrorTextFailure> {
    if diagnostic.code.is_none() {
        return Err(ErrorTextFailure::Unavailable(
            "A diagnostic has no TypeScript code.".to_owned(),
        ));
    }
    if let Some(name) = &diagnostic.file_name {
        let source = inputs
            .texts
            .get(name)
            .expect("diagnostic source collection was validated");
        let range = diagnostic.range.ok_or_else(|| {
            ErrorTextFailure::Unavailable(format!(
                "Diagnostic TS{} in {name:?} has no retained byte range.",
                diagnostic.code.unwrap(),
            ))
        })?;
        let start = range.start.get() as usize;
        let end = range.end.get() as usize;
        let text = source.as_scannable_str();
        if start > end
            || end > text.len()
            || !text.is_char_boundary(start)
            || !text.is_char_boundary(end)
        {
            return Err(ErrorTextFailure::Invariant {
                code: "INV.PROJECT.ERROR_RANGE",
                detail: format!("Diagnostic range {start}..{end} is invalid for {name:?}."),
            });
        }
    }
    for related in &diagnostic.related_information {
        validate_diagnostic(related, inputs)?;
    }
    Ok(())
}

fn ordering(program: &Program, diagnostic: &ProgramDiagnostic) -> CompilationDiagnosticOrdering {
    CompilationDiagnosticOrdering {
        origin: program_diagnostic_origin(program, diagnostic),
        diagnostic: recover_structured_compilation_diagnostic(diagnostic.code, &diagnostic.message),
    }
}

// Keep newlines inside message arguments. Only message-chain separators use CRLF.
fn flattened_message(
    diagnostic: &ProgramDiagnostic,
    ordering: &CompilationDiagnosticOrdering,
) -> Result<String, ErrorTextFailure> {
    if let Some(structured) = &ordering.diagnostic {
        let mut text = ts_diagnostics::message_by_code(structured.code())
            .and_then(|message| message.format(&structured.arguments).ok())
            .expect("recovered diagnostics retain a valid catalog message");
        for detail in &structured.details {
            text.push_str(HARNESS_NEW_LINE);
            text.push_str(detail);
        }
        return Ok(text);
    }
    if diagnostic.message.contains(['\r', '\n']) {
        return Err(ErrorTextFailure::Unavailable(format!(
            "Diagnostic TS{} lacks the message structure needed to preserve embedded newlines.",
            diagnostic.code.unwrap(),
        )));
    }
    Ok(diagnostic.message.clone())
}

fn related_record(
    program: &Program,
    diagnostic: &ProgramDiagnostic,
    inputs: &ErrorInputs,
) -> Result<CompilationRelatedInformation, ErrorTextFailure> {
    let ordering = ordering(program, diagnostic);
    Ok(CompilationRelatedInformation {
        file_name: diagnostic.file_name.as_deref().map(go_file_name),
        source_text: diagnostic
            .file_name
            .as_ref()
            .map(|name| inputs.texts[name].clone()),
        range: diagnostic.range,
        code: diagnostic.code,
        category: Some(compilation_diagnostic_category(diagnostic.category)),
        message: flattened_message(diagnostic, &ordering)?,
        related_information: diagnostic
            .related_information
            .iter()
            .map(|related| related_record(program, related, inputs))
            .collect::<Result<_, _>>()?,
        ordering,
    })
}

fn primary_record(
    program: &Program,
    diagnostic: &ProgramDiagnostic,
    inputs: &ErrorInputs,
) -> Result<CompilationDiagnostic, ErrorTextFailure> {
    validate_diagnostic(diagnostic, inputs)?;
    let ordering = ordering(program, diagnostic);
    Ok(CompilationDiagnostic {
        file_name: diagnostic.file_name.as_deref().map(go_file_name),
        source_text: diagnostic
            .file_name
            .as_ref()
            .map(|name| inputs.texts[name].clone()),
        range: diagnostic.range,
        code: diagnostic.code,
        category: Some(compilation_diagnostic_category(diagnostic.category)),
        message: flattened_message(diagnostic, &ordering)?,
        related_information: Some(
            diagnostic
                .related_information
                .iter()
                .map(|related| related_record(program, related, inputs))
                .collect::<Result<_, _>>()?,
        ),
        ordering,
    })
}

fn comparison_key(name: &str) -> String {
    normalize_comparison_path(&remove_test_path_prefixes(name))
        .chars()
        .map(|character| character.to_lowercase().next().unwrap_or(character))
        .collect()
}

#[allow(clippy::too_many_lines)] // Preserve the pinned global, file, and count sequence.
fn render_nonempty(
    program: &Program,
    diagnostics: &[ProgramDiagnostic],
) -> Result<(Vec<String>, String), ErrorTextFailure> {
    let inputs = collect_inputs(program, diagnostics)?;
    let mut records = diagnostics
        .iter()
        .map(|diagnostic| primary_record(program, diagnostic, &inputs))
        .collect::<Result<Vec<_>, _>>()?;
    records.sort_by(compare_compilation_diagnostics);
    let ordered = records.iter().collect::<Vec<_>>();
    for pair in ordered.windows(2) {
        if diagnostic_primary_order_key(pair[0]) == diagnostic_primary_order_key(pair[1])
            && (!diagnostic_ordering_is_authenticated(pair[0])
                || !diagnostic_ordering_is_authenticated(pair[1]))
        {
            return Err(ErrorTextFailure::Unavailable(
                "Diagnostics with the same path, range, and code lack authenticated message ordering.".to_owned(),
            ));
        }
    }
    let context = DiagnosticTextContext::Project;
    let mut unsupported = Vec::new();
    let mut text = render_diagnostic_header_with_context(context, &ordered, &mut unsupported);
    text.push_str(HARNESS_NEW_LINE);
    text.push_str(HARNESS_NEW_LINE);
    let mut annotations = String::new();
    let mut first = true;
    let mut ordinary_count = 0;
    for (index, diagnostic) in ordered.iter().enumerate() {
        if diagnostic.file_name.is_none() {
            append_annotated_diagnostic_with_context(
                &mut annotations,
                &mut first,
                diagnostic,
                index,
                context,
                &mut unsupported,
            );
            ordinary_count += 1;
        }
    }
    for name in &inputs.order {
        let go_name = go_file_name(name);
        let key = comparison_key(&go_name);
        let matching = ordered
            .iter()
            .enumerate()
            .filter(|(_, diagnostic)| {
                diagnostic
                    .file_name
                    .as_deref()
                    .is_some_and(|name| comparison_key(name) == key)
            })
            .collect::<Vec<_>>();
        ordinary_count += matching
            .iter()
            .filter(|(_, diagnostic)| {
                let name = diagnostic
                    .file_name
                    .as_deref()
                    .expect("file diagnostics have names");
                !is_default_library_file(name) && !is_config_file(name)
            })
            .count();
        let display_name = remove_test_path_prefixes(&go_name);
        append_annotation_line(
            &mut annotations,
            &mut first,
            &format!("==== {display_name} ({} errors) ====", matching.len()),
        );
        annotate_diagnostic_source(
            context,
            inputs.texts[name].as_scannable_str(),
            &display_name,
            &matching,
            &mut annotations,
            &mut first,
            &mut unsupported,
        );
    }
    let library_count = ordered
        .iter()
        .filter(|diagnostic| {
            diagnostic
                .file_name
                .as_deref()
                .is_some_and(|name| is_default_library_file(name) || is_built_file(name))
        })
        .count();
    let config_count = ordered
        .iter()
        .filter(|diagnostic| diagnostic.file_name.as_deref().is_some_and(is_config_file))
        .count();
    if ordinary_count + library_count + config_count != diagnostics.len() {
        return Err(ErrorTextFailure::Invariant {
            code: "INV.PROJECT.ERROR_COUNT",
            detail: "The pinned error-file accounting does not cover each diagnostic exactly once."
                .to_owned(),
        });
    }
    if !unsupported.is_empty() {
        return Err(ErrorTextFailure::Unavailable(unsupported.join("\n")));
    }
    text.push_str(&annotations);
    Ok((inputs.order, text))
}

#[cfg(test)]
mod tests {
    use ts_compiler::{Program, ProgramDiagnostic};
    use ts_core::{TextPos, TextRange};
    use ts_diagnostics::Category;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{collect_inputs, go_file_name, primary_record, render};
    use crate::{Case, project::ProjectStage, render_error_baseline};

    fn program(files: &[(&str, &str)]) -> Program {
        let fs = MemoryFileSystem::new(true);
        for (name, source) in files {
            fs.write_file(name, source).unwrap();
        }
        Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/case",
            &files
                .iter()
                .map(|(name, _)| (*name).to_owned())
                .collect::<Vec<_>>(),
            CompilerOptions {
                no_lib: true,
                no_emit: true,
                skip_lib_check: true,
                ..CompilerOptions::default()
            },
            |_, _| (),
        )
        .unwrap()
        .0
    }

    fn diagnostic(
        file: Option<&str>,
        range: Option<(u32, u32)>,
        code: u32,
        message: &str,
    ) -> ProgramDiagnostic {
        ProgramDiagnostic {
            file_name: file.map(str::to_owned),
            range: range.map(|(start, end)| TextRange::new(TextPos::new(start), TextPos::new(end))),
            code: Some(code),
            category: Category::Error,
            message: message.to_owned(),
            related_information: Vec::new(),
        }
    }

    fn text(output: ProjectStage<super::ProjectTextArtifact>) -> String {
        let ProjectStage::Complete { value } = output else {
            panic!("missing error text: {output:?}");
        };
        value.text
    }

    #[test]
    fn project_errors_use_utf16_columns_byte_ranges_and_scalar_squiggles() {
        let source = "const sample = \"\u{1f600}\u{00e9}\u{1f642}\";\r\n";
        let program = program(&[
            ("/case/main.ts", source),
            ("/case/related.ts", "const other = 1;\r\n"),
        ]);
        let mut error = diagnostic(
            Some("/case/main.ts"),
            Some((20, 26)),
            2322,
            "Type 'string' is not assignable to type 'number'.",
        );
        error.related_information.push(diagnostic(
            Some("/case/related.ts"),
            Some((6, 11)),
            1005,
            "'/.src/related' expected.",
        ));
        let output = render(&program, &[error]);
        assert_eq!(output.file_order, ["/case/main.ts", "/case/related.ts"]);
        let expected = format!(
            concat!(
                "/case/main.ts(1,19): error TS2322: Type 'string' is not assignable to type 'number'.\r\n\r\n\r\n",
                "==== /case/main.ts (1 errors) ====\r\n",
                "    const sample = \"\u{1f600}\u{00e9}\u{1f642}\";\r\n",
                "{}~~\r\n",
                "!!! error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
                "!!! related TS1005 /case/related.ts:1:7: '/.src/related' expected.\r\n",
                "    \r\n",
                "==== /case/related.ts (0 errors) ====\r\n",
                "    const other = 1;\r\n",
                "    ",
            ),
            " ".repeat(21),
        );
        assert_eq!(text(output.output), expected);
        assert_eq!(
            program.source_file("/case/main.ts").unwrap().source_text,
            source
        );
    }

    #[test]
    fn project_errors_keep_header_sort_separate_from_input_order() {
        let program = program(&[
            ("/case/z.ts", "const z = 1;\n"),
            ("/case/a.ts", "const a = 2;\n"),
        ]);
        let errors = [
            diagnostic(Some("/case/z.ts"), Some((6, 7)), 1005, "'z' expected."),
            diagnostic(Some("/case/a.ts"), Some((6, 7)), 1005, "'a' expected."),
            diagnostic(
                None,
                None,
                6046,
                "Argument for 'target' option must be: 'es5'.",
            ),
        ];
        let result = render(&program, &errors);
        assert_eq!(result.file_order, ["/case/z.ts", "/case/a.ts"]);
        let text = text(result.output);
        assert!(text.starts_with(
            "error TS6046: Argument for 'target' option must be: 'es5'.\r\n/case/a.ts(1,7)"
        ));
        assert!(text.find("==== /case/z.ts").unwrap() < text.find("==== /case/a.ts").unwrap());
    }

    #[test]
    fn project_errors_match_shared_fixture_format_for_plain_inputs() {
        let source = "let value = 1;\n";
        let program = program(&[("/case/main.ts", source)]);
        let errors = [diagnostic(
            Some("/case/main.ts"),
            Some((4, 9)),
            2322,
            "Type 'number' is not assignable to type 'string'.",
        )];
        let inputs =
            collect_inputs(&program, &errors).unwrap_or_else(|_| panic!("missing test inputs"));
        let records = errors
            .iter()
            .map(|error| {
                primary_record(&program, error, &inputs)
                    .unwrap_or_else(|_| panic!("invalid test diagnostic"))
            })
            .collect::<Vec<_>>();
        let fixture =
            Case::parse("case.ts", format!("// @filename: /case/main.ts\n{source}")).unwrap();
        let expected = render_error_baseline(&fixture, &records);
        assert!(expected.unsupported_details.is_empty());
        assert_eq!(text(render(&program, &errors).output), expected.text);
    }

    #[test]
    fn project_errors_keep_no_content_distinct_from_missing_source() {
        let program = program(&[("/case/main.ts", "const value = 1;\n")]);
        let empty = render(&program, &[]);
        assert!(empty.file_order.is_empty());
        let encoded = serde_json::to_value(empty.output).unwrap();
        assert_eq!(encoded["status"], "no_content");
        assert!(encoded.get("value").is_none());
        assert!(encoded.get("digest").is_none());
        let missing = render(
            &program,
            &[diagnostic(
                Some("/case/not-loaded.ts"),
                Some((0, 1)),
                1005,
                "'x' expected.",
            )],
        );
        assert!(matches!(missing.output, ProjectStage::Unavailable { .. }));
    }

    #[test]
    fn project_errors_reject_ranges_inside_utf8_characters() {
        let program = program(&[("/case/main.ts", "const value = \"\u{1f642}\";\n")]);
        let result = render(
            &program,
            &[diagnostic(
                Some("/case/main.ts"),
                Some((16, 17)),
                1005,
                "'x' expected.",
            )],
        );
        assert!(
            matches!(result.output, ProjectStage::Invariant { ref code, .. } if code == "INV.PROJECT.ERROR_RANGE")
        );
    }

    #[test]
    fn project_errors_preserve_newlines_inside_message_arguments() {
        let program = program(&[("/case/main.ts", "const value = 1;\n")]);
        let errors = [diagnostic(
            None,
            None,
            2304,
            "Cannot find name 'first\nsecond'.",
        )];
        let text = text(render(&program, &errors).output);
        assert!(text.starts_with("error TS2304: Cannot find name 'first\nsecond'.\r\n\r\n"));
        assert!(
            text.contains(
                "!!! error TS2304: Cannot find name 'first\r\n!!! error TS2304: second'."
            )
        );
    }

    #[test]
    fn project_errors_map_only_the_compiler_library_prefix() {
        assert_eq!(
            go_file_name("/__typescript/lib/lib.es5.d.ts"),
            "bundled:///libs/lib.es5.d.ts"
        );
        assert_eq!(go_file_name("/case/lib.user.d.ts"), "/case/lib.user.d.ts");
        let program = program(&[("/case/lib.user.d.ts", "type Value = number;\n")]);
        let errors = [diagnostic(
            Some("/case/lib.user.d.ts"),
            Some((0, 4)),
            1005,
            "'x' expected.",
        )];
        let text = text(render(&program, &errors).output);
        assert!(text.starts_with("/case/lib.user.d.ts(1,1): error TS1005: 'x' expected.\r\n"));
    }

    #[test]
    fn project_error_locations_keep_the_lf_byte_on_the_previous_crlf_line() {
        let source = "const a = 1;\r\nconst b = 2;\r\n";
        let program = program(&[("/case/main.ts", source)]);
        let mut error = diagnostic(Some("/case/main.ts"), Some((6, 7)), 1005, "'a' expected.");
        error.related_information.push(diagnostic(
            Some("/case/main.ts"),
            Some((13, 13)),
            1005,
            "'b' expected.",
        ));
        let text = text(render(&program, &[error]).output);
        assert!(text.contains("!!! related TS1005 /case/main.ts:1:14: 'b' expected."));
    }
}
