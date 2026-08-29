//! TypeScript-compatible command-line parsing and exit statuses.

use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::{Path, PathBuf},
};

use ts_config::JsonValue;
use ts_options::{
    CompilerOptions as NormalizedCompilerOptions, is_module_resolution_diagnostic,
    parse_compiler_options_map,
};

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
#[allow(clippy::struct_excessive_bools)] // Build switches are independently composable.
pub struct BuildOptions {
    pub projects: Vec<String>,
    pub clean: bool,
    pub dry: bool,
    pub force: bool,
    pub help: bool,
    pub incremental: bool,
    pub list_emitted_files: bool,
    pub list_files: bool,
    pub no_check: Option<bool>,
    pub no_emit: bool,
    pub pretty: Option<bool>,
    pub quiet: bool,
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
    pub list_emitted_files: bool,
    pub list_files: bool,
    pub list_files_only: bool,
    pub project: Option<String>,
    pub pretty: Option<bool>,
    pub quiet: bool,
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
    read_file: impl FnMut(&Path) -> std::io::Result<String>,
) -> Result<Command, CommandLineError> {
    let expanded = expand_command_line(args, read_file)?;
    parse_expanded(&expanded)
}

/// Expands TypeScript response files using normalized absolute paths.
///
/// # Errors
///
/// Returns the pinned command-line diagnostic for unreadable, recursive, or
/// unterminated response files.
pub fn expand_command_line(
    args: &[String],
    mut read_file: impl FnMut(&Path) -> std::io::Result<String>,
) -> Result<Vec<String>, CommandLineError> {
    let mut expanded = Vec::new();
    expand_response_files(args, &mut read_file, &mut HashSet::new(), &mut expanded)?;
    Ok(expanded)
}

#[allow(clippy::too_many_lines)] // Preserve TypeScript's ordered command-line option dispatch.
fn parse_expanded(args: &[String]) -> Result<Command, CommandLineError> {
    if args
        .first()
        .is_some_and(|argument| matches!(argument.to_ascii_lowercase().as_str(), "--build" | "-b"))
    {
        return parse_build_options(&args[1..]).map(Command::Build);
    }
    let mut options = CompilerOptions::default();
    let mut compiler_options = BTreeMap::new();
    let mut requested_command = None;
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let lower = argument.to_ascii_lowercase();
        match lower.as_str() {
            "--help" | "-h" | "-?" => {
                if requested_command.is_none() {
                    requested_command = Some(Command::Help);
                }
            }
            "--lsp" => return Ok(Command::Lsp),
            "--version" | "-v" => requested_command = Some(Command::Version),
            "--watch" | "-w" => options.watch = optional_boolean_value(args, &mut index),
            "--ignoreconfig" => options.ignore_config = optional_boolean_value(args, &mut index),
            "--listemittedfiles" => {
                options.list_emitted_files = optional_boolean_value(args, &mut index);
            }
            "--listfiles" => options.list_files = optional_boolean_value(args, &mut index),
            "--listfilesonly" => {
                options.list_files_only = optional_boolean_value(args, &mut index);
            }
            "--pretty" => options.pretty = Some(optional_boolean_value(args, &mut index)),
            "--quiet" | "-q" => options.quiet = optional_boolean_value(args, &mut index),
            "--project" | "-p" => {
                index += 1;
                options.project = Some(required_option_value(args, index, "project")?);
            }
            _ if compiler_boolean_name(&lower).is_some() => {
                let name = compiler_boolean_name(&lower).expect("guard checked option name");
                let value = optional_boolean_value(args, &mut index);
                if name == "composite" && value {
                    return Err(CommandLineError {
                        code: 6230,
                        message: "Option 'composite' can only be specified in 'tsconfig.json' file or set to 'false' or 'null' on command line.".to_owned(),
                    });
                }
                compiler_options.insert(name.to_owned(), JsonValue::Bool(value));
            }
            _ if compiler_string_name(&lower).is_some() => {
                let name = compiler_string_name(&lower).expect("guard checked option name");
                index += 1;
                compiler_options.insert(
                    name.to_owned(),
                    JsonValue::String(required_option_value(args, index, name)?),
                );
            }
            _ if compiler_list_name(&lower).is_some() => {
                let name = compiler_list_name(&lower).expect("guard checked option name");
                index += 1;
                let values = required_option_value(args, index, name)?
                    .split(',')
                    .filter(|value| !value.is_empty())
                    .map(|value| JsonValue::String(value.to_owned()))
                    .collect();
                compiler_options.insert(name.to_owned(), JsonValue::Array(values));
            }
            "--maxnodemodulejsdepth" => {
                index += 1;
                let name = "maxnodemodulejsdepth";
                let value = args
                    .get(index)
                    .and_then(|value| value.parse::<i64>().ok())
                    .ok_or_else(|| missing_option_value_error(name))?;
                if value < 0 {
                    return Err(CommandLineError {
                        code: 5002,
                        message: format!(
                            "Option '{}' requires value to be greater than '0'.",
                            option_display_name(name)
                        ),
                    });
                }
                let number = ts_config::parse_jsonc("<command line>", &value.to_string())
                    .value
                    .expect("a normalized integer is valid JSON");
                compiler_options.insert(name.to_owned(), number);
            }
            "--paths" | "--rootdirs" => {
                let name = lower.trim_start_matches('-');
                index += 1;
                let value = required_option_value(args, index, name)?;
                if !value.eq_ignore_ascii_case("null") {
                    return Err(CommandLineError {
                        code: 6064,
                        message: format!(
                            "Option '{}' can only be specified in 'tsconfig.json' file or set to 'null' on command line.",
                            option_display_name(name)
                        ),
                    });
                }
                let cleared = if name == "paths" {
                    JsonValue::Object(BTreeMap::new())
                } else {
                    JsonValue::Array(Vec::new())
                };
                compiler_options.insert(name.to_owned(), cleared);
            }
            "--build" | "-b" => {
                return Err(CommandLineError {
                    code: 6369,
                    message: "Option '--build' must be the first command line argument.".to_owned(),
                });
            }
            "--clean" | "--dry" | "--force" => {
                return Err(CommandLineError {
                    code: 5093,
                    message: format!(
                        "Compiler option '{argument}' may only be used with '--build'."
                    ),
                });
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
    if let Some(diagnostic) = parsed
        .diagnostics
        .iter()
        .find(|diagnostic| !is_module_resolution_diagnostic(diagnostic))
    {
        return Err(CommandLineError {
            code: u16::try_from(diagnostic.code()).unwrap_or(u16::MAX),
            message: diagnostic
                .render()
                .unwrap_or_else(|error| error.to_string()),
        });
    }
    if let Some(command) = requested_command {
        return Ok(command);
    }
    if options.watch && options.list_files_only {
        return Err(incompatible_build_options("watch", "listFilesOnly"));
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
        "--allowarbitraryextensions" => "allowarbitraryextensions",
        "--allowimportingtsextensions" => "allowimportingtsextensions",
        "--allowjs" => "allowjs",
        "--allowumdglobalaccess" => "allowumdglobalaccess",
        "--allowunreachablecode" => "allowunreachablecode",
        "--allowunusedlabels" => "allowunusedlabels",
        "--allowsyntheticdefaultimports" => "allowsyntheticdefaultimports",
        "--assumechangesonlyaffectdirectdependencies" => {
            "assumechangesonlyaffectdirectdependencies"
        }
        "--checkjs" => "checkjs",
        "--composite" => "composite",
        "--declaration" | "-d" => "declaration",
        "--declarationmap" => "declarationmap",
        "--deduplicatepackages" => "deduplicatepackages",
        "--disablesizelimit" => "disablesizelimit",
        "--downleveliteration" => "downleveliteration",
        "--emitbom" => "emitbom",
        "--emitdeclarationonly" => "emitdeclarationonly",
        "--emitdecoratormetadata" => "emitdecoratormetadata",
        "--erasablesyntaxonly" => "erasablesyntaxonly",
        "--esmoduleinterop" => "esmoduleinterop",
        "--exactoptionalpropertytypes" => "exactoptionalpropertytypes",
        "--experimentaldecorators" => "experimentaldecorators",
        "--forceconsistentcasinginfilenames" => "forceconsistentcasinginfilenames",
        "--importhelpers" => "importhelpers",
        "--incremental" | "-i" => "incremental",
        "--inlinesourcemap" => "inlinesourcemap",
        "--inlinesources" => "inlinesources",
        "--isolateddeclarations" => "isolateddeclarations",
        "--isolatedmodules" => "isolatedmodules",
        "--libreplacement" => "libreplacement",
        "--nocheck" => "nocheck",
        "--noemit" => "noemit",
        "--noemithelpers" => "noemithelpers",
        "--noemitonerror" => "noemitonerror",
        "--noerrortruncation" => "noerrortruncation",
        "--noimplicitany" => "noimplicitany",
        "--noimplicitoverride" => "noimplicitoverride",
        "--noimplicitreturns" => "noimplicitreturns",
        "--noimplicitthis" => "noimplicitthis",
        "--nolib" => "nolib",
        "--nofallthroughcasesinswitch" => "nofallthroughcasesinswitch",
        "--nopropertyaccessfromindexsignature" => "nopropertyaccessfromindexsignature",
        "--noresolve" => "noresolve",
        "--nouncheckedindexedaccess" => "nouncheckedindexedaccess",
        "--nouncheckedsideeffectimports" => "nouncheckedsideeffectimports",
        "--nounusedlocals" => "nounusedlocals",
        "--nounusedparameters" => "nounusedparameters",
        "--preserveconstenums" => "preserveconstenums",
        "--preservesymlinks" => "preservesymlinks",
        "--removecomments" => "removecomments",
        "--resolvejsonmodule" => "resolvejsonmodule",
        "--resolvepackagejsonexports" => "resolvepackagejsonexports",
        "--resolvepackagejsonimports" => "resolvepackagejsonimports",
        "--rewriterelativeimportextensions" => "rewriterelativeimportextensions",
        "--skipdefaultlibcheck" => "skipdefaultlibcheck",
        "--skiplibcheck" => "skiplibcheck",
        "--sourcemap" => "sourcemap",
        "--stabletypeordering" => "stabletypeordering",
        "--strict" => "strict",
        "--strictbindcallapply" => "strictbindcallapply",
        "--strictbuiltiniteratorreturn" => "strictbuiltiniteratorreturn",
        "--strictfunctiontypes" => "strictfunctiontypes",
        "--strictnullchecks" => "strictnullchecks",
        "--strictpropertyinitialization" => "strictpropertyinitialization",
        "--stripinternal" => "stripinternal",
        "--usedefineforclassfields" => "usedefineforclassfields",
        "--useunknownincatchvariables" => "useunknownincatchvariables",
        "--verbatimmodulesyntax" => "verbatimmodulesyntax",
        _ => return None,
    })
}

fn compiler_string_name(argument: &str) -> Option<&'static str> {
    Some(match argument {
        "--baseurl" => "baseurl",
        "--declarationdir" => "declarationdir",
        "--ignoredeprecations" => "ignoredeprecations",
        "--jsx" => "jsx",
        "--jsxfactory" => "jsxfactory",
        "--jsxfragmentfactory" => "jsxfragmentfactory",
        "--jsximportsource" => "jsximportsource",
        "--maproot" => "maproot",
        "--module" | "-m" => "module",
        "--moduledetection" => "moduledetection",
        "--moduleresolution" => "moduleresolution",
        "--newline" => "newline",
        "--outfile" => "outfile",
        "--outdir" => "outdir",
        "--reactnamespace" => "reactnamespace",
        "--rootdir" => "rootdir",
        "--sourceroot" => "sourceroot",
        "--target" | "-t" => "target",
        "--tsbuildinfofile" => "tsbuildinfofile",
        _ => return None,
    })
}

fn compiler_list_name(argument: &str) -> Option<&'static str> {
    Some(match argument {
        "--customconditions" => "customconditions",
        "--lib" => "lib",
        "--modulesuffixes" => "modulesuffixes",
        "--typeroots" => "typeroots",
        "--types" => "types",
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
            "--clean" => options.clean = optional_boolean_value(args, &mut index),
            "--dry" | "-d" => options.dry = optional_boolean_value(args, &mut index),
            "--force" | "-f" => options.force = optional_boolean_value(args, &mut index),
            "--help" | "-h" | "-?" => options.help = true,
            "--incremental" | "-i" => {
                options.incremental = optional_boolean_value(args, &mut index);
            }
            "--listemittedfiles" => {
                options.list_emitted_files = optional_boolean_value(args, &mut index);
            }
            "--listfiles" => options.list_files = optional_boolean_value(args, &mut index),
            "--nocheck" => options.no_check = Some(optional_boolean_value(args, &mut index)),
            "--noemit" => options.no_emit = optional_boolean_value(args, &mut index),
            "--watch" | "-w" => options.watch = optional_boolean_value(args, &mut index),
            "--pretty" => options.pretty = Some(optional_boolean_value(args, &mut index)),
            "--quiet" | "-q" => options.quiet = optional_boolean_value(args, &mut index),
            _ if argument.starts_with("--")
                && (compiler_boolean_name(&lower).is_some()
                    || compiler_string_name(&lower).is_some()
                    || compiler_list_name(&lower).is_some()
                    || matches!(
                        lower.as_str(),
                        "--listfilesonly"
                            | "--maxnodemodulejsdepth"
                            | "--project"
                            | "--paths"
                            | "--rootdirs"
                    )) =>
            {
                return Err(CommandLineError {
                    code: 5094,
                    message: format!(
                        "Compiler option '{argument}' may not be used with '--build'."
                    ),
                });
            }
            _ if argument.starts_with('-') => {
                return Err(CommandLineError {
                    code: 5072,
                    message: format!("Unknown build option '{argument}'."),
                });
            }
            _ => options.projects.push(argument.clone()),
        }
        index += 1;
    }
    if options.clean && options.force {
        return Err(incompatible_build_options("clean", "force"));
    }
    if options.clean && options.watch {
        return Err(incompatible_build_options("clean", "watch"));
    }
    if options.watch && options.dry {
        return Err(incompatible_build_options("watch", "dry"));
    }
    Ok(options)
}

fn incompatible_build_options(first: &str, second: &str) -> CommandLineError {
    CommandLineError {
        code: 6370,
        message: format!("Options '{first}' and '{second}' cannot be combined."),
    }
}

fn required_option_value(
    args: &[String],
    index: usize,
    option: &str,
) -> Result<String, CommandLineError> {
    args.get(index)
        .filter(|value| !value.starts_with('-'))
        .cloned()
        .ok_or_else(|| missing_option_value_error(option))
}

fn missing_option_value_error(option: &str) -> CommandLineError {
    CommandLineError {
        code: 6044,
        message: format!(
            "Compiler option '{}' expects an argument.",
            option_display_name(option)
        ),
    }
}

fn option_display_name(name: &str) -> &str {
    match name {
        "baseurl" => "baseUrl",
        "customconditions" => "customConditions",
        "declarationdir" => "declarationDir",
        "ignoredeprecations" => "ignoreDeprecations",
        "jsxfactory" => "jsxFactory",
        "jsxfragmentfactory" => "jsxFragmentFactory",
        "jsximportsource" => "jsxImportSource",
        "maproot" => "mapRoot",
        "maxnodemodulejsdepth" => "maxNodeModuleJsDepth",
        "moduledetection" => "moduleDetection",
        "moduleresolution" => "moduleResolution",
        "modulesuffixes" => "moduleSuffixes",
        "newline" => "newLine",
        "outfile" => "outFile",
        "outdir" => "outDir",
        "reactnamespace" => "reactNamespace",
        "rootdir" => "rootDir",
        "rootdirs" => "rootDirs",
        "sourceroot" => "sourceRoot",
        "tsbuildinfofile" => "tsBuildInfoFile",
        "typeroots" => "typeRoots",
        _ => name,
    }
}

fn optional_boolean_value(args: &[String], index: &mut usize) -> bool {
    match args
        .get(*index + 1)
        .and_then(|value| parse_bool_value(value))
    {
        Some(value) => {
            *index += 1;
            value
        }
        None => true,
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
            if !argument.is_empty() {
                output.push(argument.clone());
            }
            continue;
        };
        let path = absolute_response_file_path(path);
        let display_path = path.display().to_string();
        if !active.insert(display_path.clone()) {
            return Err(CommandLineError {
                code: 5083,
                message: format!(
                    "Cannot read file '{display_path}': Circular response file inclusion."
                ),
            });
        }
        let contents = read_file(&path).map_err(|_| CommandLineError {
            code: 5083,
            message: format!("Cannot read file '{display_path}'."),
        })?;
        let nested = tokenize_response_file(&contents, &path)?;
        expand_response_files(&nested, read_file, active, output)?;
        active.remove(&display_path);
    }
    Ok(())
}

fn absolute_response_file_path(path: &str) -> PathBuf {
    let path = Path::new(path);
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir().map_or_else(|_| path.to_owned(), |directory| directory.join(path))
    };
    PathBuf::from(ts_vfs::normalize_path(&absolute.to_string_lossy()))
}

fn tokenize_response_file(source: &str, path: &Path) -> Result<Vec<String>, CommandLineError> {
    let mut arguments = Vec::new();
    let mut chars = source.chars().peekable();
    while chars.peek().is_some() {
        while chars.peek().is_some_and(|character| *character <= ' ') {
            chars.next();
        }
        let Some(character) = chars.peek().copied() else {
            break;
        };
        if character == '"' {
            chars.next();
            let mut argument = String::new();
            loop {
                match chars.next() {
                    Some('"') => break,
                    Some(character) => argument.push(character),
                    None => {
                        return Err(CommandLineError {
                            code: 6045,
                            message: format!(
                                "Unterminated quoted string in response file '{}'.",
                                path.display()
                            ),
                        });
                    }
                }
            }
            arguments.push(argument);
        } else {
            let mut argument = String::new();
            while chars.peek().is_some_and(|character| *character > ' ') {
                argument.push(chars.next().expect("peeked response-file character"));
            }
            arguments.push(argument);
        }
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
    fn no_arguments_select_implicit_project_compilation() {
        let Command::Compile(options) = parse(&[]).unwrap() else {
            panic!("expected implicit project compilation");
        };
        assert!(options.files.is_empty());
        assert!(options.project.is_none());
    }

    #[test]
    fn side_effect_import_checks_default_to_enabled() {
        let Command::Compile(defaults) = parse(&["main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert!(defaults.compiler_options.no_unchecked_side_effect_imports);

        let Command::Compile(disabled) =
            parse(&["--noUncheckedSideEffectImports", "false", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };
        assert!(!disabled.compiler_options.no_unchecked_side_effect_imports);
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
    fn validates_all_arguments_before_help_or_version() {
        assert_eq!(parse(&["--help", "--wat"]).unwrap_err().code, 5023);
        assert_eq!(parse(&["--version", "--wat"]).unwrap_err().code, 5023);
        assert_eq!(parse(&["--version", "--project"]).unwrap_err().code, 6044);
        assert_eq!(parse(&["--help", "--version"]), Ok(Command::Version));
        assert_eq!(parse(&["--version", "--help"]), Ok(Command::Version));
    }

    #[test]
    fn reports_canonical_option_names_for_missing_values() {
        assert_eq!(
            parse(&["-p"]).unwrap_err().render(),
            "error TS6044: Compiler option 'project' expects an argument."
        );
        assert_eq!(
            parse(&["-t"]).unwrap_err().render(),
            "error TS6044: Compiler option 'target' expects an argument."
        );
        assert_eq!(
            parse(&["--lib"]).unwrap_err().render(),
            "error TS6044: Compiler option 'lib' expects an argument."
        );
        assert_eq!(
            parse(&["--maxNodeModuleJsDepth"]).unwrap_err().render(),
            "error TS6044: Compiler option 'maxNodeModuleJsDepth' expects an argument."
        );
    }

    #[test]
    fn parses_numeric_compiler_options() {
        let Command::Compile(options) = parse(&["--maxNodeModuleJsDepth", "2", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };

        assert_eq!(options.compiler_options.max_node_module_js_depth, Some(2));
        assert!(options.specified_options.contains("maxnodemodulejsdepth"));
        assert_eq!(options.files, ["main.ts"]);
    }

    #[test]
    fn rejects_invalid_numeric_compiler_options_like_typescript() {
        assert_eq!(
            parse(&["--maxNodeModuleJsDepth", "nope"])
                .unwrap_err()
                .render(),
            "error TS6044: Compiler option 'maxNodeModuleJsDepth' expects an argument."
        );
        assert_eq!(
            parse(&["--maxNodeModuleJsDepth", "-1"])
                .unwrap_err()
                .render(),
            "error TS5002: Option 'maxNodeModuleJsDepth' requires value to be greater than '0'."
        );
    }

    #[test]
    fn parses_file_listing_compiler_options() {
        let Command::Compile(options) = parse(&[
            "--listFiles",
            "--listFilesOnly",
            "false",
            "--listEmittedFiles",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };

        assert!(options.list_files);
        assert!(!options.list_files_only);
        assert!(options.list_emitted_files);
        assert_eq!(options.files, ["main.ts"]);
    }

    #[test]
    fn parses_standard_compiler_option_aliases() {
        let Command::Compile(options) =
            parse(&["-t", "es2022", "-m", "esnext", "-d", "-i", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };

        assert_eq!(
            options.compiler_options.target,
            ts_options::ScriptTarget::Es2022
        );
        assert_eq!(
            options.compiler_options.module,
            ts_options::ModuleKind::EsNext
        );
        assert!(options.compiler_options.declaration);
        assert!(options.compiler_options.incremental);
        assert_eq!(
            options
                .specified_options
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["declaration", "incremental", "module", "target"]
        );
    }

    #[test]
    fn parses_supported_boolean_compiler_options() {
        let Command::Compile(options) = parse(&[
            "--allowArbitraryExtensions",
            "--allowImportingTsExtensions",
            "--declaration",
            "--declarationMap",
            "--downlevelIteration",
            "--emitBOM",
            "--emitDecoratorMetadata",
            "--experimentalDecorators",
            "--exactOptionalPropertyTypes",
            "--isolatedDeclarations",
            "--noEmitHelpers",
            "--noImplicitThis",
            "false",
            "--noUncheckedIndexedAccess",
            "--noUncheckedSideEffectImports",
            "--removeComments",
            "--resolveJsonModule",
            "--rewriteRelativeImportExtensions",
            "--stripInternal",
            "--useDefineForClassFields",
            "false",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };

        assert!(options.compiler_options.allow_arbitrary_extensions);
        assert!(options.compiler_options.allow_importing_ts_extensions);
        assert!(options.compiler_options.declaration);
        assert!(options.compiler_options.declaration_map);
        assert!(options.compiler_options.downlevel_iteration);
        assert!(options.compiler_options.emit_bom);
        assert!(options.compiler_options.emit_decorator_metadata);
        assert!(options.compiler_options.experimental_decorators);
        assert!(options.compiler_options.exact_optional_property_types);
        assert!(options.compiler_options.isolated_declarations);
        assert!(options.compiler_options.no_emit_helpers);
        assert!(!options.compiler_options.no_implicit_this);
        assert!(options.compiler_options.no_implicit_this_specified);
        assert!(options.compiler_options.no_unchecked_indexed_access);
        assert!(options.compiler_options.no_unchecked_side_effect_imports);
        assert!(options.compiler_options.remove_comments);
        assert!(options.compiler_options.resolve_json_module);
        assert!(options.compiler_options.rewrite_relative_import_extensions);
        assert!(options.compiler_options.strip_internal);
        assert_eq!(
            options.compiler_options.use_define_for_class_fields,
            Some(false)
        );
        assert_eq!(options.files, ["main.ts"]);
    }

    #[test]
    fn parses_supported_string_and_list_compiler_options() {
        let Command::Compile(options) = parse(&[
            "--baseUrl",
            "src",
            "--declaration",
            "--declarationDir",
            "types",
            "--customConditions",
            "browser,development",
            "--jsxFactory",
            "h",
            "--jsxFragmentFactory",
            "Fragment",
            "--jsxImportSource",
            "preact",
            "--mapRoot",
            "maps",
            "--moduleResolution",
            "bundler",
            "--moduleSuffixes",
            ".native,.ios",
            "--sourceMap",
            "--sourceRoot",
            "sources",
            "--tsBuildInfoFile",
            "cache/state.tsbuildinfo",
            "--lib",
            "ES2022,,DOM",
            "--types",
            "node,vitest",
            "--typeRoots",
            "./types,./vendor/types",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };

        assert_eq!(options.compiler_options.base_url.as_deref(), Some("src"));
        assert!(options.compiler_options.declaration);
        assert_eq!(
            options.compiler_options.declaration_dir.as_deref(),
            Some("types")
        );
        assert_eq!(
            options.compiler_options.custom_conditions,
            Some(vec!["browser".to_owned(), "development".to_owned()])
        );
        assert_eq!(options.compiler_options.jsx_factory.as_deref(), Some("h"));
        assert_eq!(
            options.compiler_options.jsx_fragment_factory.as_deref(),
            Some("Fragment")
        );
        assert_eq!(
            options.compiler_options.jsx_import_source.as_deref(),
            Some("preact")
        );
        assert_eq!(options.compiler_options.map_root.as_deref(), Some("maps"));
        assert_eq!(
            options.compiler_options.module_resolution,
            ts_options::ModuleResolutionKind::Bundler
        );
        assert_eq!(
            options.compiler_options.module_suffixes,
            Some(vec![".native".to_owned(), ".ios".to_owned()])
        );
        assert!(options.compiler_options.source_map);
        assert_eq!(
            options.compiler_options.source_root.as_deref(),
            Some("sources")
        );
        assert_eq!(
            options.compiler_options.ts_build_info_file.as_deref(),
            Some("cache/state.tsbuildinfo")
        );
        assert_eq!(
            options.compiler_options.lib,
            Some(vec!["ES2022".to_owned(), "DOM".to_owned()])
        );
        assert_eq!(
            options.compiler_options.types,
            Some(vec!["node".to_owned(), "vitest".to_owned()])
        );
        assert_eq!(
            options.compiler_options.type_roots,
            Some(vec!["./types".to_owned(), "./vendor/types".to_owned()])
        );

        let Command::Compile(legacy_jsx) =
            parse(&["--reactNamespace", "React", "main.ts"]).unwrap()
        else {
            panic!("expected legacy JSX compile command");
        };
        assert_eq!(
            legacy_jsx.compiler_options.react_namespace.as_deref(),
            Some("React")
        );
    }

    #[test]
    fn rejects_equals_syntax_like_the_typescript_cli() {
        let error = parse(&["--pretty=false"]).unwrap_err();
        assert_eq!(error.code, 5023);
        assert_eq!(
            error.render(),
            "error TS5023: Unknown compiler option '--pretty=false'."
        );

        let build_error = parse(&["--build", "--pretty=false"]).unwrap_err();
        assert_eq!(build_error.code, 5072);
    }

    #[test]
    fn parses_explicit_command_boolean_values() {
        let Command::Compile(options) =
            parse(&["--watch", "false", "--ignoreConfig", "false", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };

        assert!(!options.watch);
        assert!(!options.ignore_config);
        assert_eq!(options.files, ["main.ts"]);
    }

    #[test]
    fn parses_quiet_mode_for_compilation_and_builds() {
        let Command::Compile(quiet) = parse(&["-q", "main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert!(quiet.quiet);

        let Command::Compile(audible) = parse(&["--quiet", "false", "main.ts"]).unwrap() else {
            panic!("expected compile command");
        };
        assert!(!audible.quiet);

        let Command::Build(build) = parse(&["--build", "-q", "project"]).unwrap() else {
            panic!("expected build command");
        };
        assert!(build.quiet);
        assert_eq!(build.projects, ["project"]);
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
            "--StrictFunctionTypes",
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
        assert!(!disabled.compiler_options.strict_function_types);
        assert!(disabled.compiler_options.strict_function_types_specified);
        assert_eq!(
            disabled
                .specified_options
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            [
                "strict",
                "strictbindcallapply",
                "strictbuiltiniteratorreturn",
                "strictfunctiontypes"
            ]
        );

        let Command::Compile(enabled) = parse(&[
            "--STRICT",
            "false",
            "--strictBindCallApply",
            "true",
            "--STRICTBUILTINITERATORRETURN",
            "true",
            "--STRICTFUNCTIONTYPES",
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
        assert!(enabled.compiler_options.strict_function_types);
        assert!(enabled.compiler_options.strict_function_types_specified);
        assert_eq!(
            enabled
                .specified_options
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            [
                "strict",
                "strictbindcallapply",
                "strictbuiltiniteratorreturn",
                "strictfunctiontypes"
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
            ts_options::ModuleResolutionKind::Bundler
        );
        assert_eq!(
            options.compiler_options.target,
            ts_options::ScriptTarget::Es2025
        );
        assert_eq!(
            options
                .compiler_options
                .module
                .effective_for_target(options.compiler_options.target),
            ts_options::ModuleKind::Es2022
        );
        assert!(!options.compiler_options.module_specified);
        assert!(options.specified_options.is_empty());
    }

    #[test]
    fn target_default_preserves_explicit_legacy_command_line_options() {
        for (resolution, expected, diagnostic_name) in [
            (
                "classic",
                ts_options::ModuleResolutionKind::Classic,
                "Classic",
            ),
            ("node10", ts_options::ModuleResolutionKind::Node10, "node10"),
        ] {
            let Command::Compile(options) = parse(&[
                "--target",
                "es5",
                "--module",
                "commonjs",
                "--moduleResolution",
                resolution,
                "--resolveJsonModule",
                "false",
                "main.ts",
            ])
            .unwrap() else {
                panic!("expected compile command");
            };
            assert_eq!(
                options.compiler_options.target,
                ts_options::ScriptTarget::Es5
            );
            assert_eq!(
                options.compiler_options.module,
                ts_options::ModuleKind::CommonJs
            );
            assert!(options.compiler_options.module_specified);
            assert_eq!(
                options.compiler_options.module_resolution_configured,
                Some(expected),
            );
            assert_eq!(
                options.compiler_options.module_resolution,
                ts_options::ModuleResolutionKind::Bundler,
            );
            let diagnostics = options.compiler_options.module_resolution_diagnostics();
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].code(), 5108);
            assert_eq!(
                diagnostics[0].arguments,
                ["moduleResolution", diagnostic_name].map(str::to_owned),
            );
            assert!(!options.compiler_options.resolve_json_module);
            assert!(options.compiler_options.resolve_json_module_specified);
            assert_eq!(
                options
                    .specified_options
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
                ["module", "moduleresolution", "resolvejsonmodule", "target"]
            );
        }
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
    fn parses_package_json_resolution_options() {
        let Command::Compile(options) = parse(&[
            "--moduleResolution",
            "bundler",
            "--resolvePackageJsonExports",
            "false",
            "--resolvePackageJsonImports",
            "false",
            "main.ts",
        ])
        .unwrap() else {
            panic!("expected compile command");
        };

        assert!(!options.compiler_options.resolve_package_json_exports);
        assert!(!options.compiler_options.resolve_package_json_imports);
        assert!(
            options
                .specified_options
                .contains("resolvepackagejsonexports")
        );
        assert!(
            options
                .specified_options
                .contains("resolvepackagejsonimports")
        );
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
    fn defers_resolution_validation_without_losing_configured_options() {
        for (arguments, configured, effective, codes) in [
            (
                vec!["--moduleResolution", "node10", "main.ts"],
                ts_options::ModuleResolutionKind::Node10,
                ts_options::ModuleResolutionKind::Bundler,
                vec![5108],
            ),
            (
                vec!["--moduleResolution", "node16", "main.ts"],
                ts_options::ModuleResolutionKind::Node16,
                ts_options::ModuleResolutionKind::Node16,
                vec![5110],
            ),
            (
                vec![
                    "--module",
                    "nodenext",
                    "--moduleResolution",
                    "bundler",
                    "main.ts",
                ],
                ts_options::ModuleResolutionKind::Bundler,
                ts_options::ModuleResolutionKind::Bundler,
                vec![5095, 5109],
            ),
        ] {
            let Command::Compile(options) = parse(&arguments).unwrap() else {
                panic!("expected compile command");
            };
            assert_eq!(options.files, ["main.ts"]);
            assert!(options.specified_options.contains("moduleresolution"));
            assert_eq!(
                options.compiler_options.module_resolution_configured,
                Some(configured)
            );
            assert_eq!(options.compiler_options.module_resolution, effective);
            let diagnostics = options.compiler_options.module_resolution_diagnostics();
            assert_eq!(diagnostics.len(), codes.len());
            for (diagnostic, code) in diagnostics.iter().zip(codes) {
                assert_eq!(diagnostic.code(), code);
            }
        }
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
                ..BuildOptions::default()
            }))
        );
    }

    #[test]
    fn parses_explicit_build_boolean_values_and_incremental_alias() {
        assert_eq!(
            parse(&["-b", "-i", "false", "--noEmit", "false", "project"]),
            Ok(Command::Build(BuildOptions {
                projects: vec!["project".into()],
                incremental: false,
                no_emit: false,
                pretty: None,
                ..BuildOptions::default()
            }))
        );
    }

    #[test]
    fn parses_supported_build_overrides_and_force_alias() {
        let Command::Build(options) = parse(&[
            "--build",
            "project",
            "--noCheck",
            "false",
            "--listFiles",
            "--listEmittedFiles",
            "-f",
        ])
        .unwrap() else {
            panic!("expected build command");
        };

        assert_eq!(options.projects, ["project"]);
        assert_eq!(options.no_check, Some(false));
        assert!(options.list_files);
        assert!(options.list_emitted_files);
        assert!(options.force);
    }

    #[test]
    fn parses_build_help_cleanup_and_dry_runs() {
        let Command::Build(help) = parse(&["--build", "--help"]).unwrap() else {
            panic!("expected build command");
        };
        assert!(help.help);

        let Command::Build(clean) = parse(&["-b", "--clean", "-d", "project"]).unwrap() else {
            panic!("expected build command");
        };
        assert!(clean.clean);
        assert!(clean.dry);
        assert_eq!(clean.projects, ["project"]);
    }

    #[test]
    fn rejects_incompatible_build_modes_like_typescript() {
        for (arguments, expected) in [
            (
                &["--build", "--clean", "--watch"][..],
                "Options 'clean' and 'watch' cannot be combined.",
            ),
            (
                &["--build", "--clean", "--force"][..],
                "Options 'clean' and 'force' cannot be combined.",
            ),
            (
                &["--build", "--watch", "--dry"][..],
                "Options 'watch' and 'dry' cannot be combined.",
            ),
        ] {
            let error = parse(arguments).unwrap_err();
            assert_eq!(error.code, 6370);
            assert_eq!(error.message, expected);
        }
    }

    #[test]
    fn reports_unknown_build_options_with_typescript_diagnostic() {
        let error = parse(&["--build", "--wat"]).unwrap_err();
        assert_eq!(error.code, 5072);
        assert_eq!(
            error.render(),
            "error TS5072: Unknown build option '--wat'."
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
    fn rejects_watch_with_list_files_only_before_project_resolution() {
        for arguments in [
            &["--watch", "--listFilesOnly", "main.ts"][..],
            &["--watch", "--listFilesOnly"][..],
            &["--listFilesOnly", "--watch", "main.ts"][..],
            &["-w", "--listFilesOnly", "--project", "missing.json"][..],
            &[
                "--listFilesOnly",
                "-p",
                "missing.json",
                "main.ts",
                "--watch",
            ][..],
        ] {
            let error = parse(arguments).unwrap_err();
            assert_eq!(error.code, 6370, "arguments: {arguments:?}");
            assert_eq!(
                error.render(),
                "error TS6370: Options 'watch' and 'listFilesOnly' cannot be combined.",
                "arguments: {arguments:?}"
            );
        }
    }

    #[test]
    fn explicit_false_disables_watch_and_list_files_only_conflict() {
        let Command::Compile(disabled_watch) =
            parse(&["--watch", "false", "--listFilesOnly", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };
        assert!(!disabled_watch.watch);
        assert!(disabled_watch.list_files_only);

        let Command::Compile(disabled_listing) =
            parse(&["--watch", "--listFilesOnly", "false", "main.ts"]).unwrap()
        else {
            panic!("expected compile command");
        };
        assert!(disabled_listing.watch);
        assert!(!disabled_listing.list_files_only);
    }

    #[test]
    fn option_errors_and_requested_commands_precede_watch_listing_conflict() {
        for (arguments, expected_code) in [
            (&["--watch", "--listFilesOnly", "--wat"][..], 5023),
            (
                &["--watch", "--listFilesOnly", "--target", "future"][..],
                6046,
            ),
            (&["--watch", "--listFilesOnly", "--project"][..], 6044),
        ] {
            assert_eq!(
                parse(arguments).unwrap_err().code,
                expected_code,
                "arguments: {arguments:?}"
            );
        }
        assert_eq!(
            parse(&["--help", "--watch", "--listFilesOnly"]),
            Ok(Command::Help)
        );
        assert_eq!(
            parse(&["--watch", "--listFilesOnly", "--version"]),
            Ok(Command::Version)
        );
    }

    #[test]
    fn expands_nested_response_files_and_quotes() {
        let args = vec!["@outer.rsp".to_owned()];
        let command = parse_command_line(&args, |path: &Path| match path.file_name() {
            Some(name) if name == "outer.rsp" => Ok("--noEmit @inner.rsp".to_owned()),
            Some(name) if name == "inner.rsp" => {
                Ok("--project \"with spaces/tsconfig.json\" src/index.ts".to_owned())
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
    fn response_files_treat_single_quotes_as_filename_characters() {
        let args = vec!["@args.rsp".to_owned()];
        let command =
            parse_command_line(&args, |_| Ok("--ignoreConfig 'with-quotes.ts'".to_owned()))
                .unwrap();
        let Command::Compile(options) = command else {
            panic!("expected compile command");
        };

        assert_eq!(options.files, ["'with-quotes.ts'"]);
    }

    #[test]
    fn response_file_errors_use_normalized_absolute_paths() {
        let expected = std::env::current_dir()
            .unwrap()
            .join("missing.rsp")
            .display()
            .to_string();
        let missing = parse(&["@./nested/../missing.rsp"]).unwrap_err();
        assert_eq!(missing.code, 5083);
        assert_eq!(missing.message, format!("Cannot read file '{expected}'."));

        let unterminated = parse_command_line(&["@broken.rsp".to_owned()], |_| {
            Ok("\"unterminated".to_owned())
        })
        .unwrap_err();
        assert_eq!(unterminated.code, 6045);
        assert!(unterminated.message.contains("/broken.rsp'"));
    }

    #[test]
    fn rejects_recursive_response_files() {
        let args = vec!["@same.rsp".to_owned()];
        let error = parse_command_line(&args, |_| Ok("@same.rsp".to_owned())).unwrap_err();
        assert_eq!(error.code, 5083);
    }
}
