//! Port of Go `internal/outputpaths` (outputpaths.go, commonsourcedirectory.go).

use crate::frontend::prelude::*;

// Go: outputpaths/outputpaths.go:11 OutputPathsHost
pub trait OutputPathsHost {
    fn common_source_directory(&self) -> String;
    fn get_current_directory(&self) -> String;
    fn use_case_sensitive_file_names(&self) -> bool;
}

// Go: outputpaths/outputpaths.go:17 OutputPaths
#[derive(Clone, Debug, Default)]
pub struct OutputPaths {
    js_file_path: String,
    source_map_file_path: String,
    declaration_file_path: String,
    declaration_map_path: String,
}

impl OutputPaths {
    // Go: outputpaths/outputpaths.go:25 (*OutputPaths).DeclarationFilePath
    pub fn declaration_file_path(&self) -> &str {
        &self.declaration_file_path
    }

    // Go: outputpaths/outputpaths.go:30 (*OutputPaths).JsFilePath
    pub fn js_file_path(&self) -> &str {
        &self.js_file_path
    }

    // Go: outputpaths/outputpaths.go:34 (*OutputPaths).SourceMapFilePath
    pub fn source_map_file_path(&self) -> &str {
        &self.source_map_file_path
    }

    // Go: outputpaths/outputpaths.go:38 (*OutputPaths).DeclarationMapPath
    pub fn declaration_map_path(&self) -> &str {
        &self.declaration_map_path
    }
}

// Go: `*outputpaths.OutputPaths` implements `declarations.OutputPaths`
// (transformers/declarations/transform.go:28).
impl crate::declarations::OutputPaths for OutputPaths {
    fn declaration_file_path(&self) -> String {
        self.declaration_file_path.clone()
    }

    fn js_file_path(&self) -> String {
        self.js_file_path.clone()
    }
}

// Go: outputpaths/outputpaths.go:42 GetOutputPathsFor
pub fn get_output_paths_for(
    source_file: &ParsedSourceFile,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
    force_dts_emit: bool,
) -> OutputPaths {
    let own_output_file_path = get_own_emit_output_file_path(
        source_file.file_name(),
        options,
        host,
        get_output_extension(source_file.file_name(), options.jsx),
    );
    let is_json_file = source_file.script_kind == ScriptKind::JSON;
    // If json file emits to the same location skip writing it, if emitDeclarationOnly skip writing it
    let is_json_emitted_to_same_location = is_json_file
        && compare_paths(
            source_file.file_name(),
            &own_output_file_path,
            &ComparePathsOptions {
                current_directory: host.get_current_directory(),
                use_case_sensitive_file_names: host.use_case_sensitive_file_names(),
            },
        ) == 0;
    let mut paths = OutputPaths::default();
    if options.emit_declaration_only != Tristate::True && !is_json_emitted_to_same_location {
        paths.js_file_path = own_output_file_path;
        if source_file.script_kind != ScriptKind::JSON {
            paths.source_map_file_path = get_source_map_file_path(&paths.js_file_path, options);
        }
    }
    if force_dts_emit || options.get_emit_declarations() && !is_json_file {
        paths.declaration_file_path =
            get_declaration_emit_output_file_path(source_file.file_name(), options, host);
        if options.get_are_declaration_maps_enabled() {
            paths.declaration_map_path = format!("{}.map", paths.declaration_file_path);
        }
    }
    paths
}

// Go: outputpaths/outputpaths.go:67 ForEachEmittedFile
pub fn for_each_emitted_file(
    host: &dyn OutputPathsHost,
    options: &CompilerOptions,
    mut action: impl FnMut(&OutputPaths, Option<&Rc<ParsedSourceFile>>) -> bool,
    source_files: &[Rc<ParsedSourceFile>],
    force_dts_emit: bool,
) -> bool {
    for source_file in source_files {
        if action(
            &get_output_paths_for(source_file, options, host, force_dts_emit),
            Some(source_file),
        ) {
            return true;
        }
    }
    false
}

// Go: outputpaths/outputpaths.go:76 GetOutputJSFileName
pub fn get_output_js_file_name(
    input_file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    if options.emit_declaration_only.is_true() {
        return String::new();
    }
    let output_file_name = get_output_js_file_name_worker(input_file_name, options, host);
    if !file_extension_is(&output_file_name, EXTENSION_JSON)
        || compare_paths(
            input_file_name,
            &output_file_name,
            &ComparePathsOptions {
                current_directory: host.get_current_directory(),
                use_case_sensitive_file_names: host.use_case_sensitive_file_names(),
            },
        ) != 0
    {
        return output_file_name;
    }
    String::new()
}

// Go: outputpaths/outputpaths.go:91 GetOutputJSFileNameWorker
pub fn get_output_js_file_name_worker(
    input_file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    change_extension(
        &get_output_path_without_changing_extension(input_file_name, &options.out_dir, host),
        get_output_extension(input_file_name, options.jsx),
    )
}

// Go: outputpaths/outputpaths.go:98 GetOutputDeclarationFileNameWorker
pub fn get_output_declaration_file_name_worker(
    input_file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    let mut dir = options.declaration_dir.as_str();
    if dir.is_empty() {
        dir = options.out_dir.as_str();
    }
    change_extension(
        &get_output_path_without_changing_extension(input_file_name, dir, host),
        &get_declaration_emit_extension_for_path(input_file_name),
    )
}

// Go: outputpaths/outputpaths.go:109 GetOutputExtension
pub fn get_output_extension(file_name: &str, jsx: JsxEmit) -> &'static str {
    if file_extension_is(file_name, EXTENSION_JSON) {
        EXTENSION_JSON
    } else if jsx == JsxEmit::PRESERVE
        && file_extension_is_one_of(file_name, &[EXTENSION_JSX, EXTENSION_TSX])
    {
        EXTENSION_JSX
    } else if file_extension_is_one_of(file_name, &[EXTENSION_MTS, EXTENSION_MJS]) {
        EXTENSION_MJS
    } else if file_extension_is_one_of(file_name, &[EXTENSION_CTS, EXTENSION_CJS]) {
        EXTENSION_CJS
    } else {
        EXTENSION_JS
    }
}

// Go: outputpaths/outputpaths.go:124 GetDeclarationEmitOutputFilePath
pub fn get_declaration_emit_output_file_path(
    file: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
) -> String {
    let output_dir: Option<&str> = if !options.declaration_dir.is_empty() {
        Some(&options.declaration_dir)
    } else if !options.out_dir.is_empty() {
        Some(&options.out_dir)
    } else {
        None
    };

    let path = if let Some(output_dir) = output_dir {
        get_source_file_path_in_new_dir_worker(
            file,
            output_dir,
            &host.get_current_directory(),
            &host.common_source_directory(),
            host.use_case_sensitive_file_names(),
        )
    } else {
        file.to_string()
    };
    let declaration_extension = get_declaration_emit_extension_for_path(&path);
    format!("{}{}", remove_file_extension(&path), declaration_extension)
}

// Go: outputpaths/outputpaths.go:142 GetSourceFilePathInNewDir
pub fn get_source_file_path_in_new_dir(
    file_name: &str,
    new_dir_path: &str,
    current_directory: &str,
    common_source_directory: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    let mut source_file_path = get_normalized_absolute_path(file_name, current_directory);
    let common_source_directory = ensure_trailing_directory_separator(common_source_directory);
    let is_source_file_in_common_source_directory = contains_path(
        &common_source_directory,
        &source_file_path,
        &ComparePathsOptions {
            use_case_sensitive_file_names,
            current_directory: current_directory.to_string(),
        },
    );
    if is_source_file_in_common_source_directory {
        source_file_path = source_file_path[common_source_directory.len()..].to_string();
    }
    combine_paths(new_dir_path, &[&source_file_path])
}

// Go: outputpaths/outputpaths.go:155 getOutputPathWithoutChangingExtension
fn get_output_path_without_changing_extension(
    input_file_name: &str,
    output_directory: &str,
    host: &dyn OutputPathsHost,
) -> String {
    if !output_directory.is_empty() {
        return resolve_path(
            output_directory,
            &[&get_relative_path_from_directory(
                &host.common_source_directory(),
                input_file_name,
                &ComparePathsOptions {
                    use_case_sensitive_file_names: host.use_case_sensitive_file_names(),
                    current_directory: host.get_current_directory(),
                },
            )],
        );
    }
    input_file_name.to_string()
}

// Go: outputpaths/outputpaths.go:165 GetSourceFilePathInNewDirWorker
pub fn get_source_file_path_in_new_dir_worker(
    file_name: &str,
    new_dir_path: &str,
    current_directory: &str,
    common_source_directory: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    let mut source_file_path = get_normalized_absolute_path(file_name, current_directory);
    let common_dir =
        get_canonical_file_name(common_source_directory, use_case_sensitive_file_names);
    let canon_file = get_canonical_file_name(&source_file_path, use_case_sensitive_file_names);
    let is_source_file_in_common_source_directory = canon_file.starts_with(common_dir.as_str());
    if is_source_file_in_common_source_directory {
        source_file_path = source_file_path[common_source_directory.len()..].to_string();
    }
    combine_paths(new_dir_path, &[&source_file_path])
}

// Go: outputpaths/outputpaths.go:177 getOwnEmitOutputFilePath
fn get_own_emit_output_file_path(
    file_name: &str,
    options: &CompilerOptions,
    host: &dyn OutputPathsHost,
    extension: &str,
) -> String {
    let emit_output_file_path_without_extension = if !options.out_dir.is_empty() {
        let current_directory = host.get_current_directory();
        remove_file_extension(&get_source_file_path_in_new_dir(
            file_name,
            &options.out_dir,
            &current_directory,
            &host.common_source_directory(),
            host.use_case_sensitive_file_names(),
        ))
        .to_string()
    } else {
        remove_file_extension(file_name).to_string()
    };
    emit_output_file_path_without_extension + extension
}

// Go: outputpaths/outputpaths.go:194 GetSourceMapFilePath
pub fn get_source_map_file_path(js_file_path: &str, options: &CompilerOptions) -> String {
    if options.source_map.is_true() && !options.inline_source_map.is_true() {
        return format!("{js_file_path}.map");
    }
    String::new()
}

// Go: outputpaths/outputpaths.go:201 GetBuildInfoFileName
pub fn get_build_info_file_name(options: &CompilerOptions, opts: &ComparePathsOptions) -> String {
    if !options.is_incremental() && !options.build.is_true() {
        return String::new();
    }
    if !options.ts_build_info_file.is_empty() {
        return options.ts_build_info_file.clone();
    }
    if options.config_file_path.is_empty() {
        return String::new();
    }
    let config_file_extension_less = remove_file_extension(&options.config_file_path);
    let build_info_extension_less = if !options.out_dir.is_empty() {
        if !options.root_dir.is_empty() {
            resolve_path(
                &options.out_dir,
                &[&get_relative_path_from_directory(
                    &options.root_dir,
                    config_file_extension_less,
                    opts,
                )],
            )
        } else {
            combine_paths(
                &options.out_dir,
                &[&get_base_file_name(config_file_extension_less)],
            )
        }
    } else {
        config_file_extension_less.to_string()
    };
    build_info_extension_less + EXTENSION_TS_BUILD_INFO
}

// Go: outputpaths/commonsourcedirectory.go:8 computeCommonSourceDirectoryOfFilenames
fn compute_common_source_directory_of_filenames(
    file_names: &[String],
    current_directory: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    // PORT: Go nil slice is `None`.
    let mut common_path_components: Option<Vec<String>> = None;
    for source_file in file_names {
        // Each file contributes into common source file path
        let mut source_path_components =
            get_normalized_path_components(source_file, current_directory);

        // The base file name is not part of the common directory path
        source_path_components.pop();

        let Some(common) = common_path_components.as_mut() else {
            // first file
            common_path_components = Some(source_path_components);
            continue;
        };

        let n = common.len().min(source_path_components.len());
        for i in 0..n {
            if get_canonical_file_name(&common[i], use_case_sensitive_file_names)
                != get_canonical_file_name(
                    &source_path_components[i],
                    use_case_sensitive_file_names,
                )
            {
                if i == 0 {
                    // Failed to find any common path component
                    return String::new();
                }

                // New common path found that is 0 -> i-1
                common.truncate(i);
                break;
            }
        }

        // If the sourcePathComponents was shorter than the commonPathComponents, truncate to the sourcePathComponents
        if source_path_components.len() < common.len() {
            common.truncate(source_path_components.len());
        }
    }

    let common_path_components = common_path_components.unwrap_or_default();
    if common_path_components.is_empty() {
        // Can happen when all input files are .d.ts files
        return current_directory.to_string();
    }

    get_path_from_path_components(&common_path_components)
}

// Go: outputpaths/commonsourcedirectory.go:51 GetComputedCommonSourceDirectory
pub fn get_computed_common_source_directory(
    emitted_files: &[String],
    current_directory: &str,
    use_case_sensitive_file_names: bool,
) -> String {
    let mut common_source_directory = compute_common_source_directory_of_filenames(
        emitted_files,
        current_directory,
        use_case_sensitive_file_names,
    );
    if !common_source_directory.is_empty() {
        common_source_directory = ensure_trailing_directory_separator(&common_source_directory);
    }
    common_source_directory
}

// Go: outputpaths/commonsourcedirectory.go:59 GetCommonSourceDirectory
// PORT: Go `checkSourceFilesBelongToPath` is a nillable callback; its
// result is unused.
pub fn get_common_source_directory(
    options: &CompilerOptions,
    files: impl FnOnce() -> Vec<String>,
    current_directory: &str,
    use_case_sensitive_file_names: bool,
    check_source_files_belong_to_path: Option<&mut dyn FnMut(&[String], &str) -> bool>,
) -> String {
    let mut common_source_directory;
    if !options.root_dir.is_empty() {
        // If a rootDir is specified use it as the commonSourceDirectory
        common_source_directory = options.root_dir.clone();
        if let Some(check) = check_source_files_belong_to_path {
            check(&files(), &options.root_dir);
        }
    } else if !options.config_file_path.is_empty() {
        // If the rootDir is not specified, then the common source directory is the directory of the config file.
        common_source_directory = get_directory_path(&options.config_file_path);
        if let Some(check) = check_source_files_belong_to_path {
            check(&files(), &common_source_directory);
        }
    } else {
        common_source_directory = compute_common_source_directory_of_filenames(
            &files(),
            current_directory,
            use_case_sensitive_file_names,
        );
    }

    if !common_source_directory.is_empty() {
        // Make sure directory path ends with directory separator so this string can directly
        // used to replace with "" to get the relative path of the source file and the relative path doesn't
        // start with / making it rooted path
        common_source_directory = ensure_trailing_directory_separator(&common_source_directory);
    }

    common_source_directory
}
