//! Go `Program.verifyCompilerOptions` checks that read an option the command
//! line can override.
//!
//! PORT: `ts_compiler` runs its copy of `verifyCompilerOptions` on the tsconfig
//! options, before command line overrides (goport forces `--noEmit`). Go runs
//! it on the final options. So each check below is decided again here with
//! the final options. The Rust graph loader has no tsconfig AST, so the
//! location of a kept diagnostic comes from the matching `ts_compiler` record.
//! When there is no such record, the diagnostic is global (Go does the same
//! when the tsconfig has no matching property).

use super::*;

/// Codes that `ts_compiler` reports from its options verification, but that
/// `verify_compiler_options` decides with the final options.
const REVERIFIED_OPTION_CODES: [i32; 2] = [
    // Go: program.go:1041 inferred rootDir layout check
    5011, // Go: program.go:1137 allowImportingTsExtensions without noEmit
    5096,
];

/// Removes the `ts_compiler` records that `verify_compiler_options` decides.
pub(super) fn without_reverified_option_diagnostics(diagnostics: &[Diagnostic]) -> Vec<Diagnostic> {
    diagnostics
        .iter()
        .filter(|d| !REVERIFIED_OPTION_CODES.contains(&d.code()))
        .cloned()
        .collect()
}

// Go: compiler/program.go:724 verifyCompilerOptions
// Only the checks in `REVERIFIED_OPTION_CODES`. The other checks keep the
// `ts_compiler` records, because no goport override changes them.
pub(super) fn verify_compiler_options() -> Vec<Diagnostic> {
    let options = options();
    let mut diagnostics = Vec::new();

    if !options.no_emit.is_true()
        && !options.composite.is_true()
        && options.root_dir.is_empty()
        && !options.config_file_path.is_empty()
        && (!options.out_dir.is_empty()
            || (options.get_emit_declarations() && !options.declaration_dir.is_empty())
            || !options.out_file.is_empty())
    {
        // Check if rootDir inferred changed and issue diagnostic
        let dir = common_source_directory();
        let mut emitted_files = Vec::new();
        for file in prog().source_files() {
            if !file.info.is_declaration_file && source_file_may_be_emitted(file.root, false) {
                emitted_files.push(file.info.file_name.clone());
            }
        }
        let case_sensitivity = state().case_sensitivity;
        let dir59 = get_computed_common_source_directory(
            &emitted_files,
            get_current_directory(),
            case_sensitivity,
        );
        if !dir59.is_empty()
            && ts_path::canonical_file_name(dir, case_sensitivity)
                != ts_path::canonical_file_name(&dir59, case_sensitivity)
        {
            // change in layout
            diagnostics.push(option_diagnostic(5011, || {
                let relative = ts_path::relative_path_from_directory(
                    &ts_path::directory_path(&options.config_file_path),
                    &dir59,
                    case_sensitivity,
                );
                let mut diagnostic = new_compiler_diagnostic(
                    diag::The_common_source_directory_of_0_is_1_The_rootDir_setting_must_be_explicitly_set_to_this_or_another_path_to_adjust_your_output_s_file_layout,
                    vec![
                        ts_path::base_file_name(&options.config_file_path).to_string(),
                        ensure_path_is_non_module_name(relative),
                    ],
                );
                diagnostic.add_message_chain(Some(new_compiler_diagnostic(
                    diag::Visit_https_Colon_Slash_Slashaka_ms_Slashts6_for_migration_information,
                    Vec::new(),
                )));
                diagnostic
            }));
        }
    }

    if options.allow_importing_ts_extensions.is_true()
        && !(options.no_emit.is_true()
            || options.emit_declaration_only.is_true()
            || options.rewrite_relative_import_extensions.is_true())
    {
        diagnostics.push(option_diagnostic(5096, || {
            new_compiler_diagnostic(
                diag::Option_allowImportingTsExtensions_can_only_be_used_when_one_of_noEmit_emitDeclarationOnly_or_rewriteRelativeImportExtensions_is_set,
                Vec::new(),
            )
        }));
    }

    diagnostics
}

// Go: tsoptions createDiagnosticForOption, located on the tsconfig property.
// PORT: the located copy is the `ts_compiler` record with this code. Without
// one, `global` builds the diagnostic that Go reports when the tsconfig has
// no matching property.
fn option_diagnostic(code: i32, global: impl FnOnce() -> Diagnostic) -> Diagnostic {
    with_tables(|tables| {
        tables
            .config_diagnostics
            .iter()
            .chain(&tables.program_diagnostics)
            .find(|d| d.code() == code)
            .cloned()
    })
    .unwrap_or_else(global)
}

// Go: outputpaths/commonsourcedirectory.go:51 GetComputedCommonSourceDirectory
fn get_computed_common_source_directory(
    emitted_files: &[String],
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let common_source_directory = compute_common_source_directory_of_filenames(
        emitted_files,
        current_directory,
        case_sensitivity,
    );
    if common_source_directory.is_empty() {
        return common_source_directory;
    }
    ts_path::ensure_trailing_directory_separator(&common_source_directory)
}

// Go: tspath/path.go EnsurePathIsNonModuleName
fn ensure_path_is_non_module_name(path: String) -> String {
    if ts_path::root_length(&path) == 0
        && !path.starts_with("./")
        && !path.starts_with("../")
        && path != "."
        && path != ".."
    {
        return format!("./{path}");
    }
    path
}
