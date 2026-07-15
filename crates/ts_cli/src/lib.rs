//! TypeScript-compatible command-line parsing and exit statuses.

use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};

use ts_config::JsonValue;
use ts_options::{CompilerOptions as NormalizedCompilerOptions, parse_compiler_options_map};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum ExitStatus {
    Success = 0,
    DiagnosticsPresentOutputsSkipped = 1,
    DiagnosticsPresentOutputsGenerated = 2,
    InvalidProjectOutputsSkipped = 3,
    ProjectReferenceCycleOutputsSkipped = 4,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Command {
    Build(BuildOptions),
    Help,
    Lsp,
    Version,
    Compile(Box<CompilerOptions>),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BuildOptions {
    pub projects: Vec<String>,
    pub incremental: bool,
    pub no_emit: bool,
    pub pretty: Option<bool>,
    pub watch: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)] // Compiler switches are independently composable.
pub struct CompilerOptions {
    pub compiler_options: NormalizedCompilerOptions,
    pub specified_options: BTreeSet<String>,
    pub files: Vec<String>,
    pub no_check: bool,
    pub no_emit: bool,
    pub no_lib: bool,
    pub ignore_config: bool,
    pub project: Option<String>,
    pub pretty: Option<bool>,
    pub watch: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandLineError {
    pub code: u16,
    pub message: String,
}

impl CommandLineError {
    #[must_use]
    pub fn render(&self) -> String {
        format!("error TS{}: {}", self.code, self.message)
    }
}

/// Parse `tsgo` arguments, expanding TypeScript response files.
///
/// # Errors
///
/// Returns a TypeScript command-line diagnostic for unknown/missing options,
/// unreadable response files, or recursive response-file inclusion.
pub fn parse_command_line(
    args: &[String],
    mut read_file: impl FnMut(&Path) -> std::io::Result<String>,
) -> Result<Command, CommandLineError> {
    let mut expanded = Vec::new();
    expand_response_files(args, &mut read_file, &mut HashSet::new(), &mut expanded)?;
    parse_expanded(&expanded)
}

fn parse_expanded(args: &[String]) -> Result<Command, CommandLineError> {
    if args.is_empty() {
        return Ok(Command::Help);
    }
    if matches!(args[0].to_ascii_lowercase().as_str(), "--build" | "-b") {
        return parse_build_options(&args[1..]).map(Command::Build);
    }
    let mut options = CompilerOptions::default();
    let mut compiler_options = BTreeMap::new();
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let lower = argument.to_ascii_lowercase();
        match lower.as_str() {
            "--help" | "-h" | "-?" => return Ok(Command::Help),
            "--lsp" => return Ok(Command::Lsp),
            "--version" | "-v" => return Ok(Command::Version),
            "--watch" | "-w" => options.watch = true,
            "--ignoreconfig" => options.ignore_config = true,
            "--pretty" => {
                let explicit_value = args
                    .get(index + 1)
                    .and_then(|value| parse_bool_value(value));
                options.pretty = Some(explicit_value.unwrap_or(true));
                if explicit_value.is_some() {
                    index += 1;
                }
            }
            "--project" | "-p" => {
                index += 1;
                options.project = Some(required_option_value(args, index, argument)?);
            }
            _ if lower.starts_with("--pretty=") => {
                options.pretty = Some(parse_bool_option(argument, "pretty")?);
            }
            _ if compiler_boolean_name(&lower).is_some() => {
                let name = compiler_boolean_name(&lower).expect("guard checked option name");
                let explicit_value = args
                    .get(index + 1)
                    .and_then(|value| parse_bool_value(value));
                compiler_options.insert(
                    name.to_owned(),
                    JsonValue::Bool(explicit_value.unwrap_or(true)),
                );
                if explicit_value.is_some() {
                    index += 1;
                }
            }
            _ if compiler_string_name(&lower).is_some() => {
                let name = compiler_string_name(&lower).expect("guard checked option name");
                index += 1;
                compiler_options.insert(
                    name.to_owned(),
                    JsonValue::String(required_option_value(args, index, argument)?),
                );
            }
            _ if argument.starts_with('-') => {
                return Err(CommandLineError {
                    code: 5023,
                    message: format!("Unknown compiler option '{argument}'."),
                });
            }
            _ => options.files.push(argument.clone()),
        }
        index += 1;
    }
    let parsed = parse_compiler_options_map(&compiler_options);
    if let Some(diagnostic) = parsed.diagnostics.first() {
        return Err(CommandLineError {
            code: u16::try_from(diagnostic.code()).unwrap_or(u16::MAX),
            message: diagnostic
                .render()
                .unwrap_or_else(|error| error.to_string()),
        });
    }
    options.no_check = parsed.options.no_check;
    options.no_emit = parsed.options.no_emit;
    options.no_lib = parsed.options.no_lib;
    options.specified_options = compiler_options.keys().cloned().collect();
    options.compiler_options = parsed.options;
    Ok(Command::Compile(Box::new(options)))
}

fn compiler_boolean_name(argument: &str) -> Option<&'static str> {
    Some(match argument {
        "--alwaysstrict" => "alwaysstrict",
        "--allowjs" => "allowjs",
        "--allowunreachablecode" => "allowunreachablecode",
        "--allowsyntheticdefaultimports" => "allowsyntheticdefaultimports",
        "--checkjs" => "checkjs",
        "--declaration" => "declaration",
        "--esmoduleinterop" => "esmoduleinterop",
        "--forceconsistentcasinginfilenames" => "forceconsistentcasinginfilenames",
        "--importhelpers" => "importhelpers",
        "--isolatedmodules" => "isolatedmodules",
        "--nocheck" => "nocheck",
        "--noemit" => "noemit",
        "--noemitonerror" => "noemitonerror",
        "--noimplicitany" => "noimplicitany",
        "--noimplicitreturns" => "noimplicitreturns",
        "--nolib" => "nolib",
        "--nofallthroughcasesinswitch" => "nofallthroughcasesinswitch",
        "--nounusedlocals" => "nounusedlocals",
        "--nounusedparameters" => "nounusedparameters",
        "--preserveconstenums" => "preserveconstenums",
        "--skiplibcheck" => "skiplibcheck",
        "--sourcemap" => "sourcemap",
        "--strict" => "strict",
        "--strictbindcallapply" => "strictbindcallapply",
        "--strictbuiltiniteratorreturn" => "strictbuiltiniteratorreturn",
        "--strictnullchecks" => "strictnullchecks",
        "--strictpropertyinitialization" => "strictpropertyinitialization",
        "--useunknownincatchvariables" => "useunknownincatchvariables",
        "--verbatimmodulesyntax" => "verbatimmodulesyntax",
        _ => return None,
    })
}

fn compiler_string_name(argument: &str) -> Option<&'static str> {
    Some(match argument {
        "--jsx" => "jsx",
        "--module" => "module",
        "--moduledetection" => "moduledetection",
        "--moduleresolution" => "moduleresolution",
        "--outfile" => "outfile",
        "--outdir" => "outdir",
        "--rootdir" => "rootdir",
        "--target" => "target",
        _ => return None,
    })
}

fn parse_build_options(args: &[String]) -> Result<BuildOptions, CommandLineError> {
    let mut options = BuildOptions::default();
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let lower = argument.to_ascii_lowercase();
        match lower.as_str() {
            "--incremental" => options.incremental = true,
            "--noemit" => options.no_emit = true,
            "--watch" | "-w" => options.watch = true,
            "--pretty" => {
                let explicit_value = args
                    .get(index + 1)
                    .and_then(|value| parse_bool_value(value));
                options.pretty = Some(explicit_value.unwrap_or(true));
                if explicit_value.is_some() {
                    index += 1;
                }
            }
            _ if lower.starts_with("--pretty=") => {
                options.pretty = Some(parse_bool_option(argument, "pretty")?);
            }
            _ if argument.starts_with('-') => {
                return Err(CommandLineError {
                    code: 5023,
                    message: format!("Unknown build option '{argument}'."),
                });
            }
            _ => options.projects.push(argument.clone()),
        }
        index += 1;
    }
    Ok(options)
}

fn required_option_value(
    args: &[String],
    index: usize,
    option: &str,
) -> Result<String, CommandLineError> {
    args.get(index)
        .filter(|value| !value.starts_with('-'))
        .cloned()
        .ok_or_else(|| CommandLineError {
            code: 6044,
            message: format!("Compiler option '{option}' expects an argument."),
        })
}

fn parse_bool_option(argument: &str, name: &str) -> Result<bool, CommandLineError> {
    match argument.split_once('=').map(|(_, value)| value) {
        Some(value) if value.eq_ignore_ascii_case("true") => Ok(true),
        Some(value) if value.eq_ignore_ascii_case("false") => Ok(false),
        _ => Err(CommandLineError {
            code: 5024,
            message: format!("Compiler option '{name}' requires a value of type boolean."),
        }),
    }
}

fn parse_bool_value(value: &str) -> Option<bool> {
    if value.eq_ignore_ascii_case("true") {
        Some(true)
    } else if value.eq_ignore_ascii_case("false") {
        Some(false)
    } else {
        None
    }
}

fn expand_response_files(
    args: &[String],
    read_file: &mut impl FnMut(&Path) -> std::io::Result<String>,
    active: &mut HashSet<String>,
    output: &mut Vec<String>,
) -> Result<(), CommandLineError> {
    for argument in args {
        let Some(path) = argument.strip_prefix('@') else {
            output.push(argument.clone());
            continue;
        };
        if !active.insert(path.to_owned()) {
            return Err(CommandLineError {
                code: 5083,
                message: format!("Cannot read file '{path}': Circular response file inclusion."),
            });
        }
        let contents = read_file(Path::new(path)).map_err(|error| CommandLineError {
            code: 5083,
            message: format!("Cannot read file '{path}': {error}."),
        })?;
        let nested = tokenize_response_file(&contents)?;
        expand_response_files(&nested, read_file, active, output)?;
        active.remove(path);
    }
    Ok(())
}

fn tokenize_response_file(source: &str) -> Result<Vec<String>, CommandLineError> {
    let mut arguments = Vec::new();
    let mut current = String::new();
    let mut quote = None;
    let mut chars = source.chars().peekable();
    while let Some(ch) = chars.next() {
        match (quote, ch) {
            (Some(expected), ch) if ch == expected => quote = None,
            (Some(_), '\\') if chars.peek().is_some_and(|next| matches!(next, '\'' | '"')) => {
                current.push(chars.next().expect("peeked response-file character"));
            }
            (None, '\'' | '"') => quote = Some(ch),
            (None, ch) if ch.is_whitespace() => {
                if !current.is_empty() {
                    arguments.push(std::mem::take(&mut current));
                }
            }
            (Some(_) | None, ch) => current.push(ch),
        }
    }
    if quote.is_some() {
        return Err(CommandLineError {
            code: 5074,
            message: "Unterminated quoted string in response file.".to_owned(),
        });
    }
    if !current.is_empty() {
        arguments.push(current);
    }
    Ok(arguments)
}

#[cfg(test)]
mod tests {
    use std::{io, path::Path};

    use super::{BuildOptions, Command, parse_command_line};

    fn parse(args: &[&str]) -> Result<Command, super::CommandLineError> {
        parse_command_line(
            &args.iter().map(ToString::to_string).collect::<Vec<_>>(),
            |_| Err(io::Error::new(io::ErrorKind::NotFound, "missing")),
        )
    }

    #[test]
    fn parses_syntax_only_compilation_case_insensitively() {
        let Command::Compile(options) = parse(&[
            "--NOCHECK",
            "--noEmit",
            "--noEmitOnError",
            "--noLib",
            "--ignoreConfig",
            "source.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };
        assert!(options.no_check);
        assert!(options.no_emit);
        assert!(options.compiler_options.no_emit_on_error);
        assert!(options.no_lib);
        assert!(options.ignore_config);
        assert_eq!(options.files, ["source.ts"]);
    }

    #[test]
    fn reports_unknown_and_missing_options() {
        let unknown = parse(&["--wat"]).unwrap_err();
        assert_eq!(unknown.code, 5023);
        assert_eq!(
            unknown.render(),
            "error TS5023: Unknown compiler option '--wat'."
        );
        assert_eq!(parse(&["--project"]).unwrap_err().code, 6044);
        assert_eq!(parse(&["--target", "future"]).unwrap_err().code, 6046);
    }

    #[test]
    fn parses_lsp_without_changing_compiler_arguments() {
        assert_eq!(parse(&["--LSP"]), Ok(Command::Lsp));
        let Command::Compile(options) = parse(&["--noEmit", "src/main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert!(options.no_emit);
        assert_eq!(options.files, ["src/main.ts"]);
    }

    #[test]
    fn parses_separated_pretty_value() {
        let Command::Compile(options) = parse(&["--pretty", "false", "main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert_eq!(options.pretty, Some(false));
        assert_eq!(options.files, ["main.ts"]);
    }

    #[test]
    fn parses_always_strict() {
        let Command::Compile(options) = parse(&["--alwaysStrict", "false", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };
        assert!(!options.compiler_options.always_strict);
        assert!(options.specified_options.contains("alwaysstrict"));
    }

    #[test]
    fn parses_strict_family_overrides_case_insensitively_with_provenance() {
        let Command::Compile(disabled) = parse(&[
            "--strict",
            "true",
            "--STRICTBindCallApply",
            "false",
            "--StrictBuiltinIteratorReturn",
            "false",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };
        assert!(disabled.compiler_options.strict);
        assert!(!disabled.compiler_options.strict_bind_call_apply);
        assert!(disabled.compiler_options.strict_bind_call_apply_specified);
        assert!(!disabled.compiler_options.strict_builtin_iterator_return);
        assert!(
            disabled
                .compiler_options
                .strict_builtin_iterator_return_specified
        );
        assert_eq!(
            disabled
                .specified_options
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            [
                "strict",
                "strictbindcallapply",
                "strictbuiltiniteratorreturn"
            ]
        );

        let Command::Compile(enabled) = parse(&[
            "--STRICT",
            "false",
            "--strictBindCallApply",
            "true",
            "--STRICTBUILTINITERATORRETURN",
            "true",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };
        assert!(!enabled.compiler_options.strict);
        assert!(enabled.compiler_options.strict_bind_call_apply);
        assert!(enabled.compiler_options.strict_bind_call_apply_specified);
        assert!(enabled.compiler_options.strict_builtin_iterator_return);
        assert!(
            enabled
                .compiler_options
                .strict_builtin_iterator_return_specified
        );
        assert_eq!(
            enabled
                .specified_options
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            [
                "strict",
                "strictbindcallapply",
                "strictbuiltiniteratorreturn"
            ]
        );
    }

    #[test]
    fn defaults_to_preserving_ecmascript_modules() {
        let Command::Compile(options) = parse(&["main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert_eq!(
            options.compiler_options.module,
            ts_options::ModuleKind::None
        );
        assert_eq!(
            options.compiler_options.module_resolution,
            ts_options::ModuleResolutionKind::Node10
        );
    }

    #[test]
    fn normalizes_common_compiler_options() {
        let Command::Compile(options) = parse(&[
            "--target",
            "es2022",
            "--module",
            "nodenext",
            "--moduleResolution",
            "nodenext",
            "--jsx",
            "react-jsx",
            "--outDir",
            "dist",
            "--rootDir",
            "src",
            "--declaration",
            "--sourceMap",
            "--preserveConstEnums",
            "--checkJs",
            "--strict",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };
        assert_eq!(
            options.compiler_options.target,
            ts_options::ScriptTarget::Es2022
        );
        assert_eq!(
            options.compiler_options.module,
            ts_options::ModuleKind::NodeNext
        );
        assert_eq!(
            options.compiler_options.module_resolution,
            ts_options::ModuleResolutionKind::NodeNext
        );
        assert_eq!(options.compiler_options.jsx, ts_options::JsxEmit::ReactJsx);
        assert_eq!(options.compiler_options.out_dir.as_deref(), Some("dist"));
        assert_eq!(options.compiler_options.root_dir.as_deref(), Some("src"));
        assert!(options.compiler_options.declaration);
        assert!(options.compiler_options.source_map);
        assert!(options.compiler_options.preserve_const_enums);
        assert!(options.compiler_options.check_js);
        assert!(options.compiler_options.allow_js);
        assert!(options.compiler_options.strict);
        assert!(options.compiler_options.no_implicit_any);
    }

    #[test]
    fn parses_out_file() {
        let Command::Compile(options) =
            parse(&["--module", "amd", "--outFile", "bundle.js", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };
        assert_eq!(
            options.compiler_options.out_file.as_deref(),
            Some("bundle.js")
        );
    }

    #[test]
    fn parses_build_projects_and_options() {
        assert_eq!(
            parse(&[
                "-b",
                "packages/a",
                "packages/b",
                "--incremental",
                "--noEmit",
                "--pretty",
                "false"
            ]),
            Ok(Command::Build(BuildOptions {
                projects: vec!["packages/a".into(), "packages/b".into()],
                incremental: true,
                no_emit: true,
                pretty: Some(false),
                watch: false,
            }))
        );
    }

    #[test]
    fn parses_watch_for_files_and_builds() {
        let Command::Compile(options) = parse(&["--watch", "main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert!(options.watch);
        let Command::Build(options) = parse(&["--build", "--watch", "project"]).unwrap() else {
            panic!("expected build command");
        };
        assert!(options.watch);
    }

    #[test]
    fn expands_nested_response_files_and_quotes() {
        let args = vec!["@outer.rsp".to_owned()];
        let command = parse_command_line(&args, |path: &Path| match path.to_str() {
            Some("outer.rsp") => Ok("--noEmit @inner.rsp".to_owned()),
            Some("inner.rsp") => {
                Ok("--project 'with spaces/tsconfig.json' src/index.ts".to_owned())
            }
            _ => unreachable!(),
        })
        .unwrap();
        let Command::Compile(options) = command else {
            panic!("expected compile command");
        };
        assert!(options.no_emit);
        assert_eq!(
            options.project.as_deref(),
            Some("with spaces/tsconfig.json")
        );
        assert_eq!(options.files, ["src/index.ts"]);
    }

    #[test]
    fn rejects_recursive_response_files() {
        let args = vec!["@same.rsp".to_owned()];
        let error = parse_command_line(&args, |_| Ok("@same.rsp".to_owned())).unwrap_err();
        assert_eq!(error.code, 5083);
    }
}
