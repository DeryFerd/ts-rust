//! Rust port of `internal/tsoptions/tsconfigparsing_test.go`.
//!
//! Baselines: `config/tsconfigParsing` (`baseline.Run`) and the TypeScript
//! submodule `config/tsconfigParsing` (`baseline.RunAgainstSubmodule`).
//!
//! PORT: Go runs the subtests in parallel (`t.Parallel`); here they run in
//! order. `BenchmarkParseSrcCompiler` is a benchmark, not a test, and is not
//! ported.
//!
//! The test data tables are generated from the Go source, so the text of
//! each config (tabs included) is the same bytes.

use std::collections::BTreeMap;

use ts_goport::execute::tsc::diagnostics::FormattingOptions;
use ts_goport::frontend::json::{JsonError, MarshalerTo};
use ts_goport::frontend::prelude::*;
use ts_goport::frontend::tsoptions;
use ts_goport::scanner_util::get_ecma_line_and_utf16_character_of_position;

use super::tsoptionstest::{
    AnyJson, CompilerOptionsJson, Subtests, TypeAcquisitionJson, VfsParseConfigHost, file_map,
    format_diagnostics_with_color_and_context, formatting_options, get_parsed_command_line,
    marshal_indent_write, new_vfs_parse_config_host, skip_if_no_type_script_submodule,
    type_script_submodule_path, write_format_diagnostics,
};
use crate::support::baseline;

// Go: tsconfigparsing_test.go:31 testConfig
#[derive(Clone)]
struct TestConfig {
    json_text: &'static str,
    config_file_name: &'static str,
    base_path: &'static str,
    all_file_list: BTreeMap<String, String>,
}

// Go: tsconfigparsing_test.go:38 parseConfigFileTextToJsonTests (element type)
struct ParseConfigFileTextToJsonTest {
    title: &'static str,
    input: &'static [&'static str],
}

// Go: tsconfigparsing_test.go:128 TestParseConfigFileTextToJson
#[test]
fn parse_config_file_text_to_json() {
    if skip_if_no_type_script_submodule("TestParseConfigFileTextToJson") {
        return;
    }
    let mut t = Subtests::new("TestParseConfigFileTextToJson");
    for rec in parse_config_file_text_to_json_tests() {
        t.run(rec.title, || {
            let mut baseline_content = String::new();
            for (i, json_text) in rec.input.iter().enumerate() {
                baseline_content.push_str("Input::\n");
                baseline_content.push_str(json_text);
                baseline_content.push('\n');
                let (parsed, errors) = tsoptions::parse_config_file_text_to_json(
                    "/apath/tsconfig.json",
                    Path("/apath".to_string()),
                    json_text,
                );
                baseline_content.push_str("Config::\n");
                if let Err(err) = write_json_readable_text(&mut baseline_content, &AnyJson(&parsed))
                {
                    panic!("Failed to write JSON text: {err}");
                }
                baseline_content.push('\n');
                baseline_content.push_str("Errors::\n");
                format_diagnostics_with_color_and_context(
                    &mut baseline_content,
                    &errors,
                    &formatting_options("\n", "/", true),
                );
                baseline_content.push('\n');
                if i != rec.input.len() - 1 {
                    baseline_content.push('\n');
                }
            }
            baseline::run_against_submodule(
                &format!("{} jsonParse.js", rec.title),
                &baseline_content,
                &baseline::Options {
                    subfolder: "config/tsconfigParsing".into(),
                    ..Default::default()
                },
            )
        });
    }
    t.finish();
}

// Go: tsconfigparsing_test.go:161 parseJsonConfigTestCase
struct ParseJsonConfigTestCase {
    title: &'static str,
    no_submodule_baseline: bool,
    input: Vec<TestConfig>,
}

/// Go `func(config testConfig, host tsoptions.ParseConfigHost, basePath string) *tsoptions.ParsedCommandLine`.
type GetParsed = fn(&TestConfig, &dyn ParseConfigHost, &str) -> ParsedCommandLine;

// Go: tsconfigparsing_test.go:807 TestParseJsonConfigFileContent
#[test]
fn parse_json_config_file_content() {
    if skip_if_no_type_script_submodule("TestParseJsonConfigFileContent") {
        return;
    }
    let mut t = Subtests::new("TestParseJsonConfigFileContent");
    for rec in parse_json_config_file_tests() {
        let name = format!("{} with json api", rec.title);
        t.run(&name, || {
            baseline_parse_config_with(
                &format!("{} with json api.js", rec.title),
                rec.no_submodule_baseline,
                &rec.input,
                get_parsed_with_json_api,
            )
        });
    }
    t.finish();
}

// Go: tsconfigparsing_test.go:818 getParsedWithJsonApi
fn get_parsed_with_json_api(
    config: &TestConfig,
    host: &dyn ParseConfigHost,
    base_path: &str,
) -> ParsedCommandLine {
    let config_file_name = get_normalized_absolute_path(config.config_file_name, base_path);
    let path = to_path(
        config.config_file_name,
        base_path,
        host.fs().use_case_sensitive_file_names(),
    );
    let (parsed, _) =
        tsoptions::parse_config_file_text_to_json(&config_file_name, path, config.json_text);
    tsoptions::parse_json_config_file_content(
        &parsed,
        host,
        base_path,
        None,
        &config_file_name,
        /*resolutionStack*/ &[],
        /*extraFileExtensions*/ &[],
        /*extendedConfigCache*/ None,
    )
}

// Go: tsconfigparsing_test.go:834 TestParseJsonSourceFileConfigFileContent
#[test]
fn parse_json_source_file_config_file_content() {
    if skip_if_no_type_script_submodule("TestParseJsonSourceFileConfigFileContent") {
        return;
    }
    let mut t = Subtests::new("TestParseJsonSourceFileConfigFileContent");
    for rec in parse_json_config_file_tests() {
        let name = format!("{} with jsonSourceFile api", rec.title);
        t.run(&name, || {
            baseline_parse_config_with(
                &format!("{} with jsonSourceFile api.js", rec.title),
                rec.no_submodule_baseline,
                &rec.input,
                get_parsed_with_json_source_file_api,
            )
        });
    }
    t.finish();
}

// Go: tsconfigparsing_test.go:845 TestParseJsonSourceFileConfigFileContentReportsInvalidExtendedConfig
#[test]
fn parse_json_source_file_config_file_content_reports_invalid_extended_config() {
    let files = file_map(&[
        (
            "/project/tsconfig.json",
            "{\n  \"extends\": \"./bad.json\"\n}",
        ),
        // The parser recovers from this as object-like JSON, producing expected-token errors for ':', ',', ',', and '}'.
        ("/project/bad.json", "{ this is not json"),
        ("/project/main.ts", "export const x = 1;"),
    ]);
    let host =
        new_vfs_parse_config_host(&files, "/project", true /*useCaseSensitiveFileNames*/);
    let config_file_name = "/project/tsconfig.json";
    let config_file = new_tsconfig_source_file_from_file_path(
        config_file_name,
        to_path(
            config_file_name,
            &host.get_current_directory(),
            host.fs().use_case_sensitive_file_names(),
        ),
        &files[config_file_name],
    );

    let parsed = tsoptions::parse_json_source_file_config_file_content(
        config_file,
        &host,
        &host.get_current_directory(),
        None,
        None,
        config_file_name,
        &[],
        &[],
        None,
    );

    let parse_errors: Vec<&Diagnostic> = parsed
        .errors
        .iter()
        .filter(|diagnostic| diagnostic.code == diag::X_0_expected.code() as i32)
        .collect();
    let expected_parse_error_messages = [":", ",", ",", "}"];
    let expected_parse_error_positions = [7, 10, 14, 18];
    assert_eq!(expected_parse_error_messages.len(), parse_errors.len());
    assert_eq!(
        parse_errors
            .iter()
            .map(|diagnostic| diagnostic.message_args[0].as_str())
            .collect::<Vec<_>>(),
        expected_parse_error_messages
    );
    assert_eq!(
        parse_errors
            .iter()
            .map(|diagnostic| diagnostic.pos)
            .collect::<Vec<_>>(),
        expected_parse_error_positions
    );
    for diagnostic in &parse_errors {
        assert_eq!(source_file_file_name(diagnostic.file), "/project/bad.json");
    }
}

// Extending an empty config file used to panic on nil Statements (#4265).
// Go: tsconfigparsing_test.go:891 TestParseJsonSourceFileConfigFileContentWithEmptyExtendedConfig
#[test]
fn parse_json_source_file_config_file_content_with_empty_extended_config() {
    let files = file_map(&[
        (
            "/project/tsconfig.json",
            "{\n  \"extends\": \"./base.json\"\n}",
        ),
        ("/project/base.json", ""),
        ("/project/main.ts", "export const x = 1;"),
    ]);
    let host =
        new_vfs_parse_config_host(&files, "/project", true /*useCaseSensitiveFileNames*/);
    let config_file_name = "/project/tsconfig.json";
    let config_file = new_tsconfig_source_file_from_file_path(
        config_file_name,
        to_path(
            config_file_name,
            &host.get_current_directory(),
            host.fs().use_case_sensitive_file_names(),
        ),
        &files[config_file_name],
    );

    let parsed = tsoptions::parse_json_source_file_config_file_content(
        config_file,
        &host,
        &host.get_current_directory(),
        None,
        None,
        config_file_name,
        &[],
        &[],
        None,
    );

    // PORT: Go asserts `parsed != nil`; the Rust result is a value.
    assert_eq!(
        parsed.file_names().to_vec(),
        vec!["/project/main.ts".to_string()]
    );
}

// Go: tsconfigparsing_test.go:924 TestParseJsonSourceFileConfigFileContentDoesNotDuplicateUnquotedKeyDiagnostics
#[test]
fn parse_json_source_file_config_file_content_does_not_duplicate_unquoted_key_diagnostics() {
    let parsed = get_parsed_command_line(
        "{\n  compilerOptions: {\n    strict: true\n  }\n}",
        &file_map(&[("/main.ts", "export const x = 1;")]),
        "/",
        true, /*useCaseSensitiveFileNames*/
    );

    let diags = parsed.get_config_file_parsing_diagnostics();
    assert_eq!(diags.len(), 2);
    let expected_locations: [(i32, i32); 2] = [(1, 2), (2, 4)];
    for (index, diagnostic) in diags.iter().enumerate() {
        assert_eq!(
            diagnostic.code,
            diag::String_literal_with_double_quotes_expected.code() as i32
        );
        let (line, character) =
            get_ecma_line_and_utf16_character_of_position(diagnostic.file, diagnostic.pos);
        assert_eq!(line, expected_locations[index].0);
        assert_eq!(character, expected_locations[index].1);
    }
}

// Go: tsconfigparsing_test.go:949 TestParseJsonSourceFileConfigFileContentReportsQuestionTokenDiagnostics
#[test]
fn parse_json_source_file_config_file_content_reports_question_token_diagnostics() {
    let parsed = get_parsed_command_line(
        "{\n  compilerOptions?: {\n    strict?: true\n  }\n}",
        &file_map(&[("/main.ts", "export const x = 1;")]),
        "/",
        true, /*useCaseSensitiveFileNames*/
    );

    let mut question_token_diagnostics: Vec<Diagnostic> = Vec::new();
    for diagnostic in parsed.get_config_file_parsing_diagnostics() {
        if diagnostic.code
            == diag::The_0_modifier_can_only_be_used_in_TypeScript_files.code() as i32
        {
            question_token_diagnostics.push(diagnostic);
        }
    }
    assert_eq!(question_token_diagnostics.len(), 2);
    let expected_locations: [(i32, i32); 2] = [(1, 17), (2, 10)];
    for (index, diagnostic) in question_token_diagnostics.iter().enumerate() {
        let (line, character) =
            get_ecma_line_and_utf16_character_of_position(diagnostic.file, diagnostic.pos);
        assert_eq!(line, expected_locations[index].0);
        assert_eq!(character, expected_locations[index].1);
    }
}

// Go: tsconfigparsing_test.go:978 TestParseNullEnumCompilerOptions
#[test]
fn parse_null_enum_compiler_options() {
    let config = TestConfig {
        json_text: "{\n\t\t\t\"compilerOptions\": {\n\t\t\t\t\"target\": null,\n\t\t\t\t\"module\": null\n\t\t\t}\n\t\t}",
        config_file_name: "tsconfig.json",
        base_path: "/",
        all_file_list: file_map(&[("/app.ts", "")]),
    };
    // PORT: Go ranges over a map, so the subtest order is random.
    let get_parsed_functions: [(&str, GetParsed); 2] = [
        ("json api", get_parsed_with_json_api),
        ("jsonSourceFile api", get_parsed_with_json_source_file_api),
    ];
    let mut t = Subtests::new("TestParseNullEnumCompilerOptions");
    for (name, get_parsed) in get_parsed_functions {
        t.run(name, || {
            let mut all_file_lists = config.all_file_list.clone();
            all_file_lists.insert("/tsconfig.json".to_string(), config.json_text.to_string());
            let host = new_vfs_parse_config_host(
                &all_file_lists,
                config.base_path,
                true, /*useCaseSensitiveFileNames*/
            );
            let parsed_config_file_content = get_parsed(&config, &host, config.base_path);
            assert_eq!(parsed_config_file_content.errors.len(), 0);
            Ok(())
        });
    }
    t.finish();
}

// Go: tsconfigparsing_test.go:1009 getParsedWithJsonSourceFileApi
fn get_parsed_with_json_source_file_api(
    config: &TestConfig,
    host: &dyn ParseConfigHost,
    base_path: &str,
) -> ParsedCommandLine {
    let config_file_name = get_normalized_absolute_path(config.config_file_name, base_path);
    let path = to_path(
        config.config_file_name,
        base_path,
        host.fs().use_case_sensitive_file_names(),
    );
    let parsed = parse_source_file(
        &SourceFileParseOptions {
            file_name: config_file_name.clone(),
            path,
            ..Default::default()
        },
        config.json_text,
        ScriptKind::JSON,
    );
    let ts_config_source_file = ts_config_source_file(&parsed);
    tsoptions::parse_json_source_file_config_file_content(
        ts_config_source_file,
        host,
        &host.get_current_directory(),
        None,
        None,
        &config_file_name,
        /*resolutionStack*/ &[],
        /*extraFileExtensions*/ &[],
        /*extendedConfigCache*/ None,
    )
}

/// Go `&tsoptions.TsConfigSourceFile{SourceFile: parsed}`.
// PORT: the Rust value keeps the root node, path and file name of the
// embedded Go `*ast.SourceFile`.
fn ts_config_source_file(parsed: &ParsedSourceFile) -> TsConfigSourceFile {
    TsConfigSourceFile {
        source_file: parsed.root,
        path: parsed.path().clone(),
        file_name: parsed.file_name().to_string(),
        ..Default::default()
    }
}

// Go: tsconfigparsing_test.go:1032 baselineParseConfigWith
// PORT: Go `t.Fatal` and the fatal `assert.NilError` are panics; the
// `baseline.Run` result (Go `t.Errorf`) is the returned `Err`.
fn baseline_parse_config_with(
    baseline_file_name: &str,
    no_submodule_baseline: bool,
    input: &[TestConfig],
    get_parsed: GetParsed,
) -> Result<(), String> {
    let _ = no_submodule_baseline;
    let no_submodule_baseline = true;
    let mut baseline_content = String::new();
    for (i, config) in input.iter().enumerate() {
        let mut base_path = config.base_path.to_string();
        if base_path.is_empty() {
            base_path =
                get_normalized_absolute_path(&get_directory_path(config.config_file_name), "");
        }
        let config_file_name = combine_paths(&base_path, &[config.config_file_name]);
        let mut all_file_lists = config.all_file_list.clone();
        all_file_lists.insert(config_file_name.clone(), config.json_text.to_string());
        let host = new_vfs_parse_config_host(
            &all_file_lists,
            config.base_path,
            true, /*useCaseSensitiveFileNames*/
        );
        let parsed_config_file_content = get_parsed(config, &host, &base_path);

        baseline_content.push_str("Fs::\n");
        if let Err(err) = print_fs(&mut baseline_content, &*host.fs(), "/") {
            panic!("{err:?}");
        }
        baseline_content.push('\n');
        baseline_content.push_str("configFileName:: ");
        baseline_content.push_str(config.config_file_name);
        baseline_content.push('\n');
        if no_submodule_baseline {
            baseline_content.push_str("CompilerOptions::\n");
            if let Err(err) = marshal_indent_write(
                &mut baseline_content,
                &CompilerOptionsJson(&parsed_config_file_content.parsed_config.compiler_options),
                "",
                "  ",
            ) {
                panic!("{err}");
            }
            baseline_content.push('\n');
            baseline_content.push('\n');

            if let Some(type_acquisition) =
                &parsed_config_file_content.parsed_config.type_acquisition
            {
                baseline_content.push_str("TypeAcquisition::\n");
                if let Err(err) = marshal_indent_write(
                    &mut baseline_content,
                    &TypeAcquisitionJson(type_acquisition),
                    "",
                    "  ",
                ) {
                    panic!("{err}");
                }
                baseline_content.push('\n');
                baseline_content.push('\n');
            }
        }
        baseline_content.push_str("FileNames::\n");
        baseline_content.push_str(
            &parsed_config_file_content
                .parsed_config
                .file_names
                .join(","),
        );
        baseline_content.push('\n');
        baseline_content.push_str("Errors::\n");
        format_diagnostics_with_color_and_context(
            &mut baseline_content,
            &parsed_config_file_content.errors,
            &formatting_options("\r\n", &base_path, true),
        );
        baseline_content.push('\n');
        if i != input.len() - 1 {
            baseline_content.push('\n');
        }
    }
    let opts = baseline::Options {
        subfolder: "config/tsconfigParsing".into(),
        ..Default::default()
    };
    if no_submodule_baseline {
        baseline::run(baseline_file_name, &baseline_content, &opts)
    } else {
        baseline::run_against_submodule(baseline_file_name, &baseline_content, &opts)
    }
}

// Go: tsconfigparsing_test.go:1091 writeJsonReadableText
fn write_json_readable_text<T: MarshalerTo + ?Sized>(
    output: &mut String,
    input: &T,
) -> Result<(), JsonError> {
    marshal_indent_write(output, input, "", "  ")
}

// Go: tsconfigparsing_test.go:1098 TestParseTypeAcquisition (element type of `cases`)
struct TypeAcquisitionCase {
    title: &'static str,
    config_name: &'static str,
    config: &'static str,
}

// Go: tsconfigparsing_test.go:1095 TestParseTypeAcquisition
#[test]
fn parse_type_acquisition() {
    // repo.SkipIfNoTypeScriptSubmodule(t)
    let mut t = Subtests::new("TestParseTypeAcquisition");
    for test in type_acquisition_cases() {
        let with_json_api_name = format!("{} with json api", test.title);
        let input = vec![TestConfig {
            json_text: test.config,
            config_file_name: test.config_name,
            base_path: "/apath",
            all_file_list: file_map(&[("/apath/a.ts", ""), ("/apath/b.ts", "")]),
        }];
        t.run(&with_json_api_name, || {
            baseline_parse_config_with(
                &format!("{with_json_api_name}.js"),
                true,
                &input,
                get_parsed_with_json_api,
            )
        });
        let with_json_source_file_api_name = format!("{} with jsonSourceFile api", test.title);
        t.run(&with_json_source_file_api_name, || {
            baseline_parse_config_with(
                &format!("{with_json_source_file_api_name}.js"),
                true,
                &input,
                get_parsed_with_json_source_file_api,
            )
        });
    }
    t.finish();
}

// Go: tsconfigparsing_test.go:1192 printFS
fn print_fs(output: &mut String, files: &dyn Fs, root: &str) -> Result<(), FsError> {
    let mut walk_fn = |path: &str, d: Option<&DirEntry>, err: Option<FsError>| {
        if let Some(err) = err {
            return Err(err);
        }
        let d = d.expect("WalkDir passes an entry when there is no error");
        if d.type_().is_regular() {
            let (content, ok) = files.read_file(path);
            if !ok {
                return Err(FsError::Other(format!("failed to read file {path}")));
            }
            output.push_str(&format!("//// [{path}]\r\n{content}\r\n\r\n"));
        }
        Ok(())
    };
    files.walk_dir(root, &mut walk_fn)
}

// Go: tsconfigparsing_test.go:1210 TestParseSrcCompiler
#[test]
fn parse_src_compiler() {
    if skip_if_no_type_script_submodule("TestParseSrcCompiler") {
        return;
    }

    let submodule = type_script_submodule_path();
    let compiler_dir = normalize_slashes(&submodule.join("src").join("compiler").to_string_lossy());
    let tsconfig_file_name = combine_paths(&compiler_dir, &["tsconfig.json"]);

    let fs = osvfs_fs();
    let host = VfsParseConfigHost {
        vfs: Rc::clone(&fs),
        current_directory: compiler_dir.clone(),
    };

    let (json_text, ok) = fs.read_file(&tsconfig_file_name);
    assert!(ok);
    let tsconfig_path = to_path(
        &tsconfig_file_name,
        &compiler_dir,
        fs.use_case_sensitive_file_names(),
    );
    let parsed = parse_source_file(
        &SourceFileParseOptions {
            file_name: tsconfig_file_name.clone(),
            path: tsconfig_path,
            ..Default::default()
        },
        Box::leak(json_text.into_boxed_str()),
        ScriptKind::JSON,
    );

    if !parsed.diagnostics.is_empty() {
        let mut log = String::new();
        write_format_diagnostics(&mut log, &parsed.diagnostics, &FormattingOptions::default());
        panic!("{log}");
    }

    let ts_config_source_file = ts_config_source_file(&parsed);

    let parse_config_file_content = tsoptions::parse_json_source_file_config_file_content(
        ts_config_source_file,
        &host,
        &host.get_current_directory(),
        None,
        None,
        &tsconfig_file_name,
        /*resolutionStack*/ &[],
        /*extraFileExtensions*/ &[],
        /*extendedConfigCache*/ None,
    );

    if !parse_config_file_content.errors.is_empty() {
        let mut log = String::new();
        write_format_diagnostics(
            &mut log,
            &parse_config_file_content.errors,
            &FormattingOptions::default(),
        );
        panic!("{log}");
    }

    let opts = parse_config_file_content.compiler_options();
    assert_eq!(
        **opts,
        CompilerOptions {
            lib: Some(vec!["lib.es2020.d.ts".to_string()]),
            module: ModuleKind::NODE_NEXT,
            module_resolution: ModuleResolutionKind::NODE_NEXT,
            new_line: NewLineKind::LF,
            out_dir: normalize_slashes(&submodule.join("built").join("local").to_string_lossy()),
            target: ScriptTarget::ES2020,
            types: Some(vec!["node".to_string()]),
            config_file_path: tsconfig_file_name.clone(),
            declaration: Tristate::True,
            declaration_map: Tristate::True,
            emit_declaration_only: Tristate::True,
            always_strict: Tristate::True,
            composite: Tristate::True,
            isolated_declarations: Tristate::True,
            no_implicit_override: Tristate::True,
            preserve_const_enums: Tristate::True,
            root_dir: normalize_slashes(&submodule.join("src").to_string_lossy()),
            skip_lib_check: Tristate::True,
            strict: Tristate::True,
            strict_bind_call_apply: Tristate::False,
            source_map: Tristate::True,
            use_unknown_in_catch_variables: Tristate::False,
            pretty: Tristate::True,
            ..Default::default()
        }
    );

    let file_names = &parse_config_file_content.parsed_config.file_names;
    let mut relative_paths: Vec<String> = Vec::with_capacity(file_names.len());
    for file_name in file_names {
        if file_name.contains(".generated.") {
            continue;
        }

        relative_paths.push(convert_to_relative_path(
            file_name,
            &ComparePathsOptions {
                current_directory: compiler_dir.clone(),
                use_case_sensitive_file_names: fs.use_case_sensitive_file_names(),
            },
        ));
    }

    assert_eq!(
        relative_paths,
        [
            "binder.ts",
            "builder.ts",
            "builderPublic.ts",
            "builderState.ts",
            "builderStatePublic.ts",
            "checker.ts",
            "commandLineParser.ts",
            "core.ts",
            "corePublic.ts",
            "debug.ts",
            "emitter.ts",
            "executeCommandLine.ts",
            "expressionToTypeNode.ts",
            "moduleNameResolver.ts",
            "moduleSpecifiers.ts",
            "parser.ts",
            "path.ts",
            "performance.ts",
            "performanceCore.ts",
            "program.ts",
            "programDiagnostics.ts",
            "resolutionCache.ts",
            "scanner.ts",
            "semver.ts",
            "sourcemap.ts",
            "symbolWalker.ts",
            "sys.ts",
            "tracing.ts",
            "transformer.ts",
            "tsbuild.ts",
            "tsbuildPublic.ts",
            "types.ts",
            "utilities.ts",
            "utilitiesPublic.ts",
            "visitorPublic.ts",
            "watch.ts",
            "watchPublic.ts",
            "watchUtilities.ts",
            "_namespaces/ts.moduleSpecifiers.ts",
            "_namespaces/ts.performance.ts",
            "_namespaces/ts.ts",
            "factory/baseNodeFactory.ts",
            "factory/emitHelpers.ts",
            "factory/emitNode.ts",
            "factory/nodeChildren.ts",
            "factory/nodeConverters.ts",
            "factory/nodeFactory.ts",
            "factory/nodeTests.ts",
            "factory/parenthesizerRules.ts",
            "factory/utilities.ts",
            "factory/utilitiesPublic.ts",
            "transformers/classFields.ts",
            "transformers/classThis.ts",
            "transformers/declarations.ts",
            "transformers/destructuring.ts",
            "transformers/es2015.ts",
            "transformers/es2016.ts",
            "transformers/es2017.ts",
            "transformers/es2018.ts",
            "transformers/es2019.ts",
            "transformers/es2020.ts",
            "transformers/es2021.ts",
            "transformers/esDecorators.ts",
            "transformers/esnext.ts",
            "transformers/generators.ts",
            "transformers/jsx.ts",
            "transformers/legacyDecorators.ts",
            "transformers/namedEvaluation.ts",
            "transformers/taggedTemplate.ts",
            "transformers/ts.ts",
            "transformers/typeSerializer.ts",
            "transformers/utilities.ts",
            "transformers/declarations/diagnostics.ts",
            "transformers/module/esnextAnd2015.ts",
            "transformers/module/impliedNodeFormatDependent.ts",
            "transformers/module/module.ts",
            "transformers/module/system.ts",
        ]
    );
}

// memoCache is a minimal memoizing ExtendedConfigCache used by tests to simulate
// cache hits across multiple parses of configs that extend a common base.
// Go: tsconfigparsing_test.go:1424 memoCache
// PORT: the trait takes `&self`, so the map is in a `RefCell`.
#[derive(Default)]
struct MemoCache {
    m: RefCell<FxHashMap<Path, Rc<ExtendedConfigCacheEntry>>>,
}

impl ExtendedConfigCache for MemoCache {
    // Go: tsconfigparsing_test.go:1428 (*memoCache).GetExtendedConfig
    fn get_extended_config(
        &self,
        file_name: &str,
        path: &Path,
        resolution_stack: &[Path],
        host: &dyn ParseConfigHost,
    ) -> Rc<ExtendedConfigCacheEntry> {
        let cached = self.m.borrow().get(path).cloned();
        if let Some(e) = cached {
            return e;
        }
        let e = Rc::new(parse_extended_config(
            file_name,
            path.clone(),
            resolution_stack,
            host,
            Some(self),
        ));
        self.m.borrow_mut().insert(path.clone(), Rc::clone(&e));
        e
    }
}

// TestExtendedConfigErrorsAppearOnCacheHit verifies that diagnostics produced while parsing an
// extended config are still reported when the extended config comes from the cache.
// Go: tsconfigparsing_test.go:1444 TestExtendedConfigErrorsAppearOnCacheHit
#[test]
fn extended_config_errors_appear_on_cache_hit() {
    let mut t = Subtests::new("TestExtendedConfigErrorsAppearOnCacheHit");

    t.run("single config parsed twice", || {
        let files = file_map(&[
            ("/tsconfig.json", "{\n  \"extends\": \"./base.json\"\n}"),
            // 'excludes' instead of 'exclude' triggers diagnostic
            ("/base.json", "{\n  \"excludes\": [\"**/*.ts\"]\n}"),
            ("/app.ts", "export {}"),
        ]);

        let host = new_vfs_parse_config_host(&files, "/", true /*useCaseSensitiveFileNames*/);

        let cache = MemoCache::default();
        let first = parse_config_with_cache(&host, "/tsconfig.json", &cache);
        assert!(
            !first.errors.is_empty(),
            "expected diagnostics on first parse, got 0"
        );
        let second = parse_config_with_cache(&host, "/tsconfig.json", &cache);
        assert!(
            !second.errors.is_empty(),
            "expected diagnostics on second parse (cache hit), got 0"
        );
        Ok(())
    });

    t.run("two configs share same base", || {
        let files = file_map(&[
            ("/base.json", "{\n  \"excludes\": [\"**/*.ts\"]\n}"),
            (
                "/projA/tsconfig.json",
                "{\n  \"extends\": \"../base.json\"\n}",
            ),
            (
                "/projB/tsconfig.json",
                "{\n  \"extends\": \"../base.json\"\n}",
            ),
            ("/projA/app.ts", "export {}"),
            ("/projB/app.ts", "export {}"),
        ]);

        let host = new_vfs_parse_config_host(&files, "/", true /*useCaseSensitiveFileNames*/);

        let cache = MemoCache::default();
        let first = parse_config_with_cache(&host, "/projA/tsconfig.json", &cache);
        assert!(
            !first.errors.is_empty(),
            "expected diagnostics for projA parse, got 0"
        );
        let second = parse_config_with_cache(&host, "/projB/tsconfig.json", &cache);
        assert!(
            !second.errors.is_empty(),
            "expected diagnostics for projB parse (cache hit on base), got 0"
        );
        Ok(())
    });
    t.finish();
}

// Go: tsconfigparsing_test.go:1462 and :1507 parseConfig (the closure in
// both subtests of TestExtendedConfigErrorsAppearOnCacheHit)
fn parse_config_with_cache(
    host: &VfsParseConfigHost,
    config_file_name: &str,
    cache: &dyn ExtendedConfigCache,
) -> ParsedCommandLine {
    let cfg_path = to_path(
        config_file_name,
        &host.get_current_directory(),
        host.fs().use_case_sensitive_file_names(),
    );
    let (json_text, ok) = host.fs().read_file(config_file_name);
    assert!(ok, "missing {config_file_name} in test fs");
    let parsed = parse_source_file(
        &SourceFileParseOptions {
            file_name: config_file_name.to_string(),
            path: cfg_path,
            ..Default::default()
        },
        Box::leak(json_text.into_boxed_str()),
        ScriptKind::JSON,
    );
    let ts_config_source_file = ts_config_source_file(&parsed);
    tsoptions::parse_json_source_file_config_file_content(
        ts_config_source_file,
        host,
        &host.get_current_directory(),
        None,
        None,
        config_file_name,
        &[],
        &[],
        Some(cache),
    )
}

// Go: tsconfigparsing_test.go:1535 TestExtendedConfigConfigDirPathsAreNotCached
#[test]
fn extended_config_config_dir_paths_are_not_cached() {
    let files = file_map(&[
        (
            "/tsconfig.base.json",
            "{\n  \"compilerOptions\": {\n    \"paths\": {\n      \"@pkg/*\": [\"${configDir}/src/*\"]\n    }\n  }\n}",
        ),
        (
            "/packages/a/tsconfig.json",
            "{\n  \"extends\": \"../../tsconfig.base.json\"\n}",
        ),
        (
            "/packages/b/tsconfig.json",
            "{\n  \"extends\": \"../../tsconfig.base.json\"\n}",
        ),
        ("/packages/a/index.ts", "export {}"),
        ("/packages/b/index.ts", "export {}"),
    ]);

    let host = new_vfs_parse_config_host(&files, "/", true /*useCaseSensitiveFileNames*/);
    let cache = MemoCache::default();

    let parse_config = |config_file_name: &str| -> ParsedCommandLine {
        let (parsed, errors) = tsoptions::get_parsed_command_line_of_config_file(
            config_file_name,
            None,
            None,
            &host,
            Some(&cache),
        );
        assert!(
            errors.is_empty(),
            "unexpected errors parsing {config_file_name}: {} errors",
            errors.len()
        );
        parsed.expect("parsed command line")
    };

    parse_config("/packages/a/tsconfig.json");
    let parsed = parse_config("/packages/b/tsconfig.json");
    let paths = parsed
        .compiler_options()
        .paths
        .as_ref()
        .and_then(|paths| paths.get("@pkg/*").cloned())
        .flatten();
    assert_eq!(paths, Some(vec!["/packages/b/src/*".to_string()]));
}

// ---------------------------------------------------------------------------
// Test data, generated from the Go source (tsconfigparsing_test.go).
// ---------------------------------------------------------------------------

// Go: tsconfigparsing_test.go:38 parseConfigFileTextToJsonTests
fn parse_config_file_text_to_json_tests() -> Vec<ParseConfigFileTextToJsonTest> {
    vec![
        ParseConfigFileTextToJsonTest {
            title: "returns empty config for file with only whitespaces",
            input: &["", " "],
        },
        ParseConfigFileTextToJsonTest {
            title: "returns empty config for file with comments only",
            input: &["// Comment", "/* Comment*/"],
        },
        ParseConfigFileTextToJsonTest {
            title: "returns empty config when config is empty object",
            input: &[r"{}"],
        },
        ParseConfigFileTextToJsonTest {
            title: "returns config object without comments",
            input: &[
                r#"{ // Excluded files
            "exclude": [
                // Exclude d.ts
                "file.d.ts"
            ]
        }"#,
                r#"{
            /* Excluded
                    Files
            */
            "exclude": [
                /* multiline comments can be in the middle of a line */"file.d.ts"
            ]
        }"#,
            ],
        },
        ParseConfigFileTextToJsonTest {
            title: "keeps string content untouched",
            input: &[
                r#"{
            "exclude": [
                "xx//file.d.ts"
            ]
        }"#,
                r#"{
            "exclude": [
                "xx/*file.d.ts*/"
            ]
        }"#,
            ],
        },
        ParseConfigFileTextToJsonTest {
            title: "handles escaped characters in strings correctly",
            input: &[
                r#"{
            "exclude": [
                "xx\"//files"
            ]
        }"#,
                r#"{
            "exclude": [
                "xx\\" // end of line comment
            ]
        }"#,
            ],
        },
        ParseConfigFileTextToJsonTest {
            title: "returns object when users correctly specify library",
            input: &[
                r#"{
            "compilerOptions": {
                "lib": ["es5"]
            }
        }"#,
                r#"{
            "compilerOptions": {
                "lib": ["es5", "es6"]
            }
        }"#,
            ],
        },
    ]
}

// Go: tsconfigparsing_test.go:167 parseJsonConfigFileTests
fn parse_json_config_file_tests() -> Vec<ParseJsonConfigTestCase> {
    vec![
        ParseJsonConfigTestCase {
            title: "ignore dotted files and folders",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r"{}",
                config_file_name: "tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[
                    ("/apath/test.ts", ""),
                    ("/apath/.git/a.ts", ""),
                    ("/apath/.b.ts", ""),
                    ("/apath/..c.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "allow dotted files and folders when explicitly requested",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                    "files": ["/apath/.git/a.ts", "/apath/.b.ts", "/apath/..c.ts"]
                }"#,
                config_file_name: "tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[
                    ("/apath/test.ts", ""),
                    ("/apath/.git/a.ts", ""),
                    ("/apath/.b.ts", ""),
                    ("/apath/..c.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "implicitly exclude common package folders",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r"{}",
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    ("/node_modules/a.ts", ""),
                    ("/bower_components/b.ts", ""),
                    ("/jspm_packages/c.ts", ""),
                    ("/d.ts", ""),
                    ("/folder/e.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for empty files list",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "files": []
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for empty files list when no references are provided",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "files": [],
                "references": []
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for directory with no .ts files",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r"{
            }",
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.js", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for empty include",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "include": []
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "tests/cases/unittests",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for include with parent directory after recursive wildcard",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "include": ["**/../*.ts"]
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/main.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "parses tsconfig with compilerOptions, files, include, and exclude",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "compilerOptions": {
    "outDir": "./dist",
    "strict": true,
    "noImplicitAny": true,
    "target": "ES2017",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "moduleDetection": "auto",
    "jsx": "react",
	"maxNodeModuleJsDepth": 1,
	"paths": {
      "jquery": ["./vendor/jquery/dist/jquery"]
    }
  },
  "files": ["/apath/src/index.ts", "/apath/src/app.ts"],
  "include": ["/apath/src/**/*"],
  "exclude": ["/apath/node_modules", "/apath/dist"]
}"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[
                    ("/apath/src/index.ts", ""),
                    ("/apath/src/app.ts", ""),
                    ("/apath/node_modules/module.ts", ""),
                    ("/apath/dist/output.js", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors when commandline option is in tsconfig",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
  "compilerOptions": {
    "help": true
  }
}"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "does not generate errors for empty files list when one or more references are provided",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "files": [],
                "references": [{ "path": "/apath" }]
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "exclude outDir unless overridden",
            no_submodule_baseline: false,
            input: vec![
                TestConfig {
                    json_text: r#"{
                "compilerOptions": {
                    "outDir": "bin"
                }
            }"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[("/bin/a.ts", ""), ("/b.ts", "")]),
                },
                TestConfig {
                    json_text: r#"{
                "compilerOptions": {
                    "outDir": "bin"
                },
                "exclude": [ "obj" ]
            }"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[("/bin/a.ts", ""), ("/b.ts", "")]),
                },
            ],
        },
        ParseJsonConfigTestCase {
            title: "exclude declarationDir unless overridden",
            no_submodule_baseline: false,
            input: vec![
                TestConfig {
                    json_text: r#"{
                "compilerOptions": {
                    "declarationDir": "declarations"
                }
            }"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[("/declarations/a.d.ts", ""), ("/a.ts", "")]),
                },
                TestConfig {
                    json_text: r#"{
                "compilerOptions": {
                    "declarationDir": "declarations"
                },
                "exclude": [ "types" ]
            }"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[("/declarations/a.d.ts", ""), ("/a.ts", "")]),
                },
            ],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for empty directory",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "compilerOptions": {
                    "allowJs": true
                }
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors for includes with outDir",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                "compilerOptions": {
                    "outDir": "./"
                },
                "include": ["**/*"]
            }"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors when include is not string",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
  "include": [
    [
      "./**/*.ts"
    ]
  ]
}"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "generates errors when files is not string",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
  "files": [
    {
      "compilerOptions": {
        "experimentalDecorators": true,
        "allowJs": true
      }
    }
  ]
}"#,
                config_file_name: "/apath/tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/a.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "with outDir from base tsconfig",
            no_submodule_baseline: false,
            input: vec![
                TestConfig {
                    json_text: r#"{
  "extends": "./tsconfigWithoutConfigDir.json"
}"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[
                        (
                            "/tsconfigWithoutConfigDir.json",
                            TSCONFIG_WITHOUT_CONFIG_DIR,
                        ),
                        ("/bin/a.ts", ""),
                        ("/b.ts", ""),
                    ]),
                },
                TestConfig {
                    json_text: r#"{
  "extends": "./tsconfigWithConfigDir.json"
}"#,
                    config_file_name: "tsconfig.json",
                    base_path: "/",
                    all_file_list: file_map(&[
                        ("/tsconfigWithConfigDir.json", TSCONFIG_WITH_CONFIG_DIR),
                        ("/bin/a.ts", ""),
                        ("/b.ts", ""),
                    ]),
                },
            ],
        },
        ParseJsonConfigTestCase {
            title: "returns error when tsconfig have excludes",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
                    "compilerOptions": {
                        "lib": ["es5"]
                    },
                    "excludes": [
                        "foge.ts"
                    ]
                }"#,
                config_file_name: "tsconfig.json",
                base_path: "/apath",
                all_file_list: file_map(&[("/apath/test.ts", ""), ("/apath/foge.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "parses tsconfig with extends, files, include and other options",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
				"extends": "./tsconfigWithExtends.json",
				"compilerOptions": {
				    "outDir": "./dist",
    				"strict": true,
    				"noImplicitAny": true,
					"baseUrl": "",
				},
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    ("/tsconfigWithExtends.json", TSCONFIG_WITH_EXTENDS),
                    ("/src/index.ts", ""),
                    ("/src/app.ts", ""),
                    ("/node_modules/module.ts", ""),
                    ("/dist/output.js", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "parses tsconfig with extends and configDir",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
				"extends": "./tsconfig.base.json"
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    ("/tsconfig.base.json", TSCONFIG_WITH_EXTENDS_AND_CONFIG_DIR),
                    ("/src/index.ts", ""),
                    ("/src/app.ts", ""),
                    ("/node_modules/module.ts", ""),
                    ("/dist/output.js", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "reports error for an unknown option",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
			    "compilerOptions": {
				"unknown": true
			    }
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[("/app.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "reports errors for wrong type option and invalid enum value",
            no_submodule_baseline: false,
            input: vec![TestConfig {
                json_text: r#"{
			    "compilerOptions": {
				"target": "invalid value",
				"removeComments": "should be a boolean",
				"moduleResolution": "invalid value"
			    }
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[("/app.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "reports errors for incorrectly cased option names",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
			    "compilerOptions": {
				"sourcemap": true,
				"declarationmap": true,
				"nouncheckedindexedaccess": true,
				"exactoptionalpropertytypes": true,
				"verbatimmodulesyntax": true,
				"isolatedmodules": true,
				"nouncheckedsideeffectimports": true,
				"moduledetection": "force",
				"skiplibcheck": true,
				"checkjs": true
			    }
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[("/app.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "handles empty types array",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
			    "compilerOptions": {
					"types": []
				}
			}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[("/app.ts", "")]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "issue 1267 scenario - extended files not picked up",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-base/backend.json",
  "compilerOptions": {
    "baseUrl": "./",
    "outDir": "dist",
    "rootDir": "src",
    "resolveJsonModule": true
  },
  "exclude": ["node_modules", "dist"],
  "include": ["src/**/*"]
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-base/backend.json",
                        r#"{
  "$schema": "https://json.schemastore.org/tsconfig",
  "display": "Backend",
  "compilerOptions": {
    "allowJs": true,
    "module": "nodenext",
    "removeComments": true,
    "emitDecoratorMetadata": true,
    "experimentalDecorators": true,
    "allowSyntheticDefaultImports": true,
    "target": "esnext",
    "lib": ["ESNext"],
    "incremental": false,
    "esModuleInterop": true,
    "noImplicitAny": true,
    "moduleResolution": "nodenext",
    "types": ["node", "vitest/globals"],
    "sourceMap": true,
    "strictPropertyInitialization": false
  },
  "files": [
    "types/ical2json.d.ts",
    "types/express.d.ts",
    "types/multer.d.ts",
    "types/reset.d.ts",
    "types/stripe-custom-typings.d.ts",
    "types/nestjs-modules.d.ts",
    "types/luxon.d.ts",
    "types/nestjs-pino.d.ts"
  ],
  "ts-node": {
    "files": true
  }
}"#,
                    ),
                    ("/tsconfig-base/types/ical2json.d.ts", "export {}"),
                    ("/tsconfig-base/types/express.d.ts", "export {}"),
                    ("/tsconfig-base/types/multer.d.ts", "export {}"),
                    ("/tsconfig-base/types/reset.d.ts", "export {}"),
                    (
                        "/tsconfig-base/types/stripe-custom-typings.d.ts",
                        "export {}",
                    ),
                    ("/tsconfig-base/types/nestjs-modules.d.ts", "export {}"),
                    (
                        "/tsconfig-base/types/luxon.d.ts",
                        r"declare module 'luxon' {
  interface TSSettings {
    throwOnInvalid: true
  }
}
export {}",
                    ),
                    ("/tsconfig-base/types/nestjs-pino.d.ts", "export {}"),
                    ("/src/main.ts", "export {}"),
                    ("/src/utils.ts", "export {}"),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "null overrides in extended tsconfig - array fields",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "lib": null,
    "typeRoots": null
  }
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node", "@types/jest"],
    "lib": ["es2020", "dom"],
    "typeRoots": ["./types", "./node_modules/@types"]
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "null overrides in extended tsconfig - string fields",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "outDir": null,
    "baseUrl": null,
    "rootDir": null
  }
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "outDir": "./dist",
    "baseUrl": "./src",
    "rootDir": "./src"
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "null overrides in extended tsconfig - mixed field types",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "outDir": null,
    "strict": false,
    "lib": ["es2022"],
    "allowJs": null
  }
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020", "dom"],
    "outDir": "./dist",
    "strict": true,
    "allowJs": true,
    "target": "es2020"
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "null overrides with multiple extends levels",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-middle.json",
  "compilerOptions": {
    "types": null,
    "lib": null
  }
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-middle.json",
                        r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": ["jest"],
    "outDir": "./build"
  }
}"#,
                    ),
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020"],
    "outDir": "./dist",
    "strict": true
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ]),
            }],
        },
        ParseJsonConfigTestCase {
            title: "null overrides in middle level of extends chain",
            no_submodule_baseline: true,
            input: vec![TestConfig {
                json_text: r#"{
  "extends": "./tsconfig-middle.json",
  "compilerOptions": {
    "outDir": "./final"
  }
}"#,
                config_file_name: "tsconfig.json",
                base_path: "/",
                all_file_list: file_map(&[
                    (
                        "/tsconfig-middle.json",
                        r#"{
  "extends": "./tsconfig-base.json",
  "compilerOptions": {
    "types": null,
    "lib": null,
    "outDir": "./middle"
  }
}"#,
                    ),
                    (
                        "/tsconfig-base.json",
                        r#"{
  "compilerOptions": {
    "types": ["node"],
    "lib": ["es2020"],
    "outDir": "./base",
    "strict": true
  }
}"#,
                    ),
                    ("/app.ts", ""),
                ]),
            }],
        },
    ]
}

// Go: tsconfigparsing_test.go:772 tsconfigWithExtends
const TSCONFIG_WITH_EXTENDS: &str = r#"{
  "files": ["/src/index.ts", "/src/app.ts"],
  "include": ["/src/**/*"],
  "exclude": [],
  "ts-node": {
    "compilerOptions": {
      "module": "commonjs"
    },
    "transpileOnly": true
  }
}"#;

// Go: tsconfigparsing_test.go:784 tsconfigWithoutConfigDir
const TSCONFIG_WITHOUT_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outDir": "bin"
  }
}"#;

// Go: tsconfigparsing_test.go:790 tsconfigWithConfigDir
const TSCONFIG_WITH_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outDir": "${configDir}/bin"
  }
}"#;

// Go: tsconfigparsing_test.go:796 tsconfigWithExtendsAndConfigDir
const TSCONFIG_WITH_EXTENDS_AND_CONFIG_DIR: &str = r#"{
  "compilerOptions": {
    "outFile": "${configDir}/outFile",
    "outDir": "${configDir}/outDir",
    "rootDir": "${configDir}/rootDir",
    "tsBuildInfoFile": "${configDir}/tsBuildInfoFile",
    "baseUrl": "${configDir}/baseUrl",
    "declarationDir": "${configDir}/declarationDir",
  }
}"#;

// Go: tsconfigparsing_test.go:1098 TestParseTypeAcquisition (cases)
fn type_acquisition_cases() -> Vec<TypeAcquisitionCase> {
    vec![
        TypeAcquisitionCase {
            title: "Convert correctly format tsconfig.json to typeAcquisition ",
            config_name: "tsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enable": true,
		"include": ["0.d.ts", "1.d.ts"],
		"exclude": ["0.js", "1.js"],
	},
}"#,
        },
        TypeAcquisitionCase {
            title: "Convert incorrect format tsconfig.json to typeAcquisition ",
            config_name: "tsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enableAutoDiscovy": true,
	}
}"#,
        },
        TypeAcquisitionCase {
            title: "Convert default tsconfig.json to typeAcquisition ",
            config_name: "tsconfig.json",
            config: r"{}",
        },
        TypeAcquisitionCase {
            title: "Convert tsconfig.json with only enable property to typeAcquisition ",
            config_name: "tsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enable": true,
	},
}"#,
        },
        TypeAcquisitionCase {
            title: "Convert jsconfig.json to typeAcquisition ",
            config_name: "jsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enable": false,
		"include": ["0.d.ts"],
		"exclude": ["0.js"],
	},
}"#,
        },
        TypeAcquisitionCase {
            title: "Convert default jsconfig.json to typeAcquisition ",
            config_name: "jsconfig.json",
            config: r"{}",
        },
        TypeAcquisitionCase {
            title: "Convert incorrect format jsconfig.json to typeAcquisition ",
            config_name: "jsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enableAutoDiscovy": true,
	},
}"#,
        },
        TypeAcquisitionCase {
            title: "Convert jsconfig.json with only enable property to typeAcquisition ",
            config_name: "jsconfig.json",
            config: r#"{
	"typeAcquisition": {
		"enable": false,
	},
}"#,
        },
    ]
}
