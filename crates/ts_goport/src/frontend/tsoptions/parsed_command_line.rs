use crate::prelude::*;
use std::cell::OnceCell;
use std::rc::Weak;

// This file ports tsoptions/parsedcommandline.go and core/parsedoptions.go.
// PORT: Go `sync.Once` plus a cached field is a single-threaded `OnceCell`.
// PORT: Go methods that check `p == nil` take `&self`, which is never nil.
// A Go nil `*ParsedCommandLine` is `Option<ParsedCommandLine>` at the caller.
// PORT: Go `iter.Seq` results are eager `Vec`s. Every Go caller reads the
// whole sequence.

// Go: tsoptions/parsedcommandline.go:22 fileGlobPattern
// PORT: used only by `WildcardDirectoryGlobs`, which is not ported
// (`internal/glob` is out of scope).
#[allow(dead_code)]
const FILE_GLOB_PATTERN: &str = "*.{js,jsx,mjs,cjs,ts,tsx,mts,cts,json}";
// Go: tsoptions/parsedcommandline.go:23 recursiveFileGlobPattern
#[allow(dead_code)]
const RECURSIVE_FILE_GLOB_PATTERN: &str = "**/*.{js,jsx,mjs,cjs,ts,tsx,mts,cts,json}";

// Go: core/parsedoptions.go:3 ParsedOptions
// PORT: Go `*CompilerOptions` is `Rc<CompilerOptions>`, so copies of the
// struct share it like Go pointers do. Go `*TypeAcquisition` is an
// `Option`. Go `[]*ProjectReference` is `Vec<ProjectReference>`, the type
// that `parse_project_reference` returns.
// PORT: the Go `WatchOptions` field is left out. Watch mode is out of scope
// and the crate has no `WatchOptions` type. Go `ParseJsonConfigFileContent`
// never sets it.
#[derive(Clone, Debug, Default)]
pub struct ParsedOptions {
    pub compiler_options: Rc<CompilerOptions>,
    pub type_acquisition: Option<TypeAcquisition>,

    pub file_names: Vec<String>,
    pub project_references: Vec<ProjectReference>,
}

// PORT: the two Go maps that `ParseInputOutputNames` fills in one `Once`.
#[derive(Debug, Default)]
pub struct SourceAndOutputMaps {
    pub source_to_project_reference: FxHashMap<Path, Rc<SourceOutputAndProjectReference>>,
    pub output_dts_to_project_reference: FxHashMap<Path, Rc<SourceOutputAndProjectReference>>,
}

// Go: tsoptions/parsedcommandline.go:27 ParsedCommandLine
// PORT: all fields are `pub`, because Go code in the same package (the
// tsconfig parser) writes the unexported fields.
// PORT: Go `ConfigFile *TsConfigSourceFile` is `Option<Rc<...>>`, because
// `ReloadFileNamesOfParsedCommandLine` shares it with the new value.
// PORT: `includeGlobs` and its `Once` are left out (`internal/glob` is out
// of scope). `locale` and its `Once` are left out (`internal/locale` is out
// of scope); see `locale`.
#[derive(Debug, Default)]
pub struct ParsedCommandLine {
    pub parsed_config: ParsedOptions,

    /// TsConfigSourceFile, used in Program and ExecuteCommandLine
    pub config_file: Option<Rc<TsConfigSourceFile>>,
    pub errors: Vec<Diagnostic>,
    pub raw: CompilerOptionsValue,
    pub compile_on_save: Option<bool>,

    pub compare_paths_options: ComparePathsOptions,
    pub wildcard_directories: OnceCell<FxHashMap<String, bool>>,
    pub extra_file_extensions: Vec<FileExtensionInfo>,

    pub source_and_output_maps: OnceCell<SourceAndOutputMaps>,

    pub common_source_directory: OnceCell<String>,

    pub resolved_project_reference_paths: OnceCell<Vec<String>>,

    // PORT: Go `int` is `i32`.
    pub literal_file_names_len: i32,
    /// maps file names to their paths, used for quick lookups
    pub file_names_by_path: OnceCell<FxHashMap<Path, String>>,
}

// Go: tsoptions/parsedcommandline.go:60 NewParsedCommandLine
// PORT: Go returns a new pointer; this returns the value.
pub fn new_parsed_command_line(
    compiler_options: Rc<CompilerOptions>,
    root_file_names: Vec<String>,
    compare_paths_options: ComparePathsOptions,
) -> ParsedCommandLine {
    ParsedCommandLine {
        parsed_config: ParsedOptions { compiler_options, file_names: root_file_names, ..Default::default() },
        compare_paths_options,
        ..Default::default()
    }
}

// Go: tsoptions/parsedcommandline.go:74 SourceOutputAndProjectReference
// PORT: Go `Resolved *ParsedCommandLine` points back at the command line
// that owns the map. An `Rc` would make a reference cycle, so this is a
// `Weak`. `ParsedCommandLine::parse_input_output_names` takes `&Rc<Self>`.
#[derive(Debug)]
pub struct SourceOutputAndProjectReference {
    pub source: String,
    pub output_dts: String,
    pub resolved: Weak<ParsedCommandLine>,
}

// Go: tsoptions/parsedcommandline.go:80 interface assertions
// PORT: `module.ResolvedProjectReference` and `outputpaths.OutputPathsHost`
// are satisfied by the methods below; there is no Rust trait to assert.

impl ParsedCommandLine {
    // Go: tsoptions/parsedcommandline.go:85 (*ParsedCommandLine).ConfigName
    // PORT: Go panics when `ConfigFile` is nil; `expect` does the same.
    pub fn config_name(&self) -> &'static str {
        let config_file = self.config_file.as_ref().expect("nil pointer dereference: ConfigFile");
        source_file_file_name(config_file.source_file)
    }

    // Go: tsoptions/parsedcommandline.go:92 (*ParsedCommandLine).SourceToProjectReference
    // PORT: Go returns a nil map before `ParseInputOutputNames`; that is `None`.
    pub fn source_to_project_reference(&self) -> Option<&FxHashMap<Path, Rc<SourceOutputAndProjectReference>>> {
        self.source_and_output_maps.get().map(|m| &m.source_to_project_reference)
    }

    // Go: tsoptions/parsedcommandline.go:96 (*ParsedCommandLine).OutputDtsToProjectReference
    // PORT: Go returns a nil map before `ParseInputOutputNames`; that is `None`.
    pub fn output_dts_to_project_reference(&self) -> Option<&FxHashMap<Path, Rc<SourceOutputAndProjectReference>>> {
        self.source_and_output_maps.get().map(|m| &m.output_dts_to_project_reference)
    }

    // Go: tsoptions/parsedcommandline.go:100 (*ParsedCommandLine).ParseInputOutputNames
    pub fn parse_input_output_names(self: &Rc<Self>) {
        self.source_and_output_maps.get_or_init(|| {
            let mut source_to_output: FxHashMap<Path, Rc<SourceOutputAndProjectReference>> = FxHashMap::default();
            let mut output_dts_to_source: FxHashMap<Path, Rc<SourceOutputAndProjectReference>> = FxHashMap::default();

            for (output_dts, source) in self.get_output_declaration_and_source_file_names() {
                let path = to_path(&source, self.get_current_directory(), self.use_case_sensitive_file_names());
                let project_reference = Rc::new(SourceOutputAndProjectReference {
                    source,
                    output_dts: output_dts.clone(),
                    resolved: Rc::downgrade(self),
                });
                if !output_dts.is_empty() {
                    output_dts_to_source.insert(
                        to_path(&output_dts, self.get_current_directory(), self.use_case_sensitive_file_names()),
                        project_reference.clone(),
                    );
                }
                source_to_output.insert(path, project_reference);
            }
            SourceAndOutputMaps {
                output_dts_to_project_reference: output_dts_to_source,
                source_to_project_reference: source_to_output,
            }
        });
    }

    // Go: tsoptions/parsedcommandline.go:122 (*ParsedCommandLine).CommonSourceDirectory
    // PORT: `outputpaths.GetCommonSourceDirectory` is out of scope. Go also
    // passes `checkSourceFilesBelongToPath`, which appends to `Errors`; a
    // port must give that callback mutable access to `errors`.
    pub fn common_source_directory(&self) -> &str {
        self.common_source_directory.get_or_init(|| {
            let _files = || -> Vec<String> {
                self.parsed_config
                    .file_names
                    .iter()
                    .filter(|file| {
                        !(self.parsed_config.compiler_options.no_emit_for_js_files.is_true()
                            && has_js_file_extension(file))
                            && !is_declaration_file_name(file)
                    })
                    .cloned()
                    .collect()
            };
            unported!("outputpaths.GetCommonSourceDirectory")
        })
    }

    // Go: tsoptions/parsedcommandline.go:141 (*ParsedCommandLine).checkSourceFilesBelongToPath
    pub fn check_source_files_belong_to_path(&mut self, source_files: &[String], root_directory: &str) -> bool {
        let mut all_files_belong_to_path = true;
        for file in source_files {
            let absolute_source_file_path = get_canonical_file_name(
                &get_normalized_absolute_path(file, self.get_current_directory()),
                self.use_case_sensitive_file_names(),
            );
            if !contains_path(root_directory, file, &self.compare_paths_options) {
                self.errors.push(new_compiler_diagnostic(
                    diag::File_0_is_not_under_rootDir_1_rootDir_is_expected_to_contain_all_source_files,
                    args![absolute_source_file_path, root_directory],
                ));
                all_files_belong_to_path = false;
            }
        }

        all_files_belong_to_path
    }

    // Go: tsoptions/parsedcommandline.go:154 (*ParsedCommandLine).GetCurrentDirectory
    pub fn get_current_directory(&self) -> &str {
        &self.compare_paths_options.current_directory
    }

    // Go: tsoptions/parsedcommandline.go:158 (*ParsedCommandLine).UseCaseSensitiveFileNames
    pub fn use_case_sensitive_file_names(&self) -> bool {
        self.compare_paths_options.use_case_sensitive_file_names
    }

    // Go: tsoptions/parsedcommandline.go:162 (*ParsedCommandLine).getOutputDeclarationAndSourceFileNames
    // PORT: Go `iter.Seq2[dtsName, inputName]` is an eager `Vec` of pairs.
    pub fn get_output_declaration_and_source_file_names(&self) -> Vec<(String, String)> {
        let mut result = Vec::new();
        for file_name in &self.parsed_config.file_names {
            let mut output_dts = String::new();
            if !is_declaration_file_name(file_name) && !file_extension_is(file_name, EXTENSION_JSON) {
                output_dts = unported!("outputpaths.GetOutputDeclarationFileNameWorker");
            }
            result.push((output_dts, file_name.clone()));
        }
        result
    }

    // Go: tsoptions/parsedcommandline.go:176 (*ParsedCommandLine).GetOutputFileNames
    // PORT: Go `iter.Seq[string]` is an eager `Vec`. `outputpaths` is out of
    // scope, so the first file that needs an output name stops here.
    pub fn get_output_file_names(&self) -> Vec<String> {
        let result: Vec<String> = Vec::new();
        for file_name in &self.parsed_config.file_names {
            if is_declaration_file_name(file_name) {
                continue;
            }
            unported!("outputpaths.GetOutputJSFileName")
        }
        result
    }

    // Go: tsoptions/parsedcommandline.go:218 (*ParsedCommandLine).GetBuildInfoFileName
    pub fn get_build_info_file_name(&self) -> String {
        unported!("outputpaths.GetBuildInfoFileName")
    }

    // Go: tsoptions/parsedcommandline.go:223 (*ParsedCommandLine).WildcardDirectories
    /// Returns the cached wildcard directories, initializing them if needed.
    /// PORT: Go dereferences `ConfigFile.configFileSpecs` and panics when
    /// either is nil; `expect` does the same.
    pub fn wildcard_directories(&self) -> &FxHashMap<String, bool> {
        self.wildcard_directories.get_or_init(|| {
            let specs = self
                .config_file
                .as_ref()
                .and_then(|c| c.config_file_specs.as_ref())
                .expect("nil pointer dereference: ConfigFile.configFileSpecs");
            get_wildcard_directories(
                &specs.validated_include_specs,
                &specs.validated_exclude_specs,
                &self.compare_paths_options,
            )
        })
    }

    // Go: tsoptions/parsedcommandline.go:241 (*ParsedCommandLine).WildcardDirectoryGlobs
    // PORT: not ported. `internal/glob` is out of scope. See
    // `possibly_matches_file_name`, its only caller.

    // Go: tsoptions/parsedcommandline.go:263 (*ParsedCommandLine).LiteralFileNames
    /// Normalized file names explicitly specified in `files`
    /// PORT: Go returns nil without a config file; that is an empty slice.
    pub fn literal_file_names(&self) -> &[String] {
        if self.config_file.is_some() {
            return &self.file_names()[0..self.literal_file_names_len as usize];
        }
        &[]
    }

    // Go: tsoptions/parsedcommandline.go:270 (*ParsedCommandLine).SetParsedOptions
    pub fn set_parsed_options(&mut self, o: ParsedOptions) {
        self.parsed_config = o;
    }

    // Go: tsoptions/parsedcommandline.go:274 (*ParsedCommandLine).SetCompilerOptions
    pub fn set_compiler_options(&mut self, o: Rc<CompilerOptions>) {
        self.parsed_config.compiler_options = o;
    }

    // Go: tsoptions/parsedcommandline.go:278 (*ParsedCommandLine).CompilerOptions
    pub fn compiler_options(&self) -> &Rc<CompilerOptions> {
        &self.parsed_config.compiler_options
    }

    // Go: tsoptions/parsedcommandline.go:285 (*ParsedCommandLine).SetTypeAcquisition
    pub fn set_type_acquisition(&mut self, o: Option<TypeAcquisition>) {
        self.parsed_config.type_acquisition = o;
    }

    // Go: tsoptions/parsedcommandline.go:289 (*ParsedCommandLine).TypeAcquisition
    pub fn type_acquisition(&self) -> Option<&TypeAcquisition> {
        self.parsed_config.type_acquisition.as_ref()
    }

    // Go: tsoptions/parsedcommandline.go:294 (*ParsedCommandLine).FileNames
    /// All file names matched by files, include, and exclude patterns
    pub fn file_names(&self) -> &[String] {
        &self.parsed_config.file_names
    }

    // Go: tsoptions/parsedcommandline.go:298 (*ParsedCommandLine).FileNamesByPath
    pub fn file_names_by_path(&self) -> &FxHashMap<Path, String> {
        self.file_names_by_path.get_or_init(|| {
            let mut file_names_by_path =
                FxHashMap::with_capacity_and_hasher(self.parsed_config.file_names.len(), Default::default());
            for file_name in &self.parsed_config.file_names {
                let path = to_path(file_name, self.get_current_directory(), self.use_case_sensitive_file_names());
                file_names_by_path.insert(path, file_name.clone());
            }
            file_names_by_path
        })
    }

    // Go: tsoptions/parsedcommandline.go:309 (*ParsedCommandLine).ProjectReferences
    pub fn project_references(&self) -> &[ProjectReference] {
        &self.parsed_config.project_references
    }

    // Go: tsoptions/parsedcommandline.go:313 (*ParsedCommandLine).ResolvedProjectReferencePaths
    pub fn resolved_project_reference_paths(&self) -> &[String] {
        self.resolved_project_reference_paths
            .get_or_init(|| self.parsed_config.project_references.iter().map(resolve_project_reference_path).collect())
    }

    // Go: tsoptions/parsedcommandline.go:320 (*ParsedCommandLine).ExtendedSourceFiles
    /// PORT: Go returns nil without a config file; that is an empty slice.
    pub fn extended_source_files(&self) -> &[String] {
        match &self.config_file {
            None => &[],
            Some(config_file) => &config_file.extended_source_files,
        }
    }

    // Go: tsoptions/parsedcommandline.go:327 (*ParsedCommandLine).GetConfigFileParsingDiagnostics
    pub fn get_config_file_parsing_diagnostics(&self) -> Vec<Diagnostic> {
        if let Some(config_file) = &self.config_file {
            // todo: !!! should be ConfigFile.ParseDiagnostics, check if they are the same
            let mut result = source_file_diagnostics(config_file.source_file).to_vec();
            result.extend(self.errors.iter().cloned());
            return result;
        }
        self.errors.clone()
    }

    // Go: tsoptions/parsedcommandline.go:337 (*ParsedCommandLine).PossiblyMatchesFileName
    /// A fast check to see if a file is currently included by a config
    /// or would be included if the file were to be created. It may return false positives.
    /// PORT: Go builds globs from the wildcard directories with
    /// `internal/glob`, which is out of scope. A config with no wildcard
    /// directories has no globs, so that case is exact. Otherwise this stops
    /// with `unported!`.
    pub fn possibly_matches_file_name(&self, file_name: &str) -> bool {
        let path = to_path(file_name, self.get_current_directory(), self.use_case_sensitive_file_names());
        if self.file_names_by_path().contains_key(&path) {
            return true;
        }

        let specs = self
            .config_file
            .as_ref()
            .and_then(|c| c.config_file_specs.as_ref())
            .expect("nil pointer dereference: ConfigFile.configFileSpecs");
        for include in &specs.validated_include_specs {
            if !include.contains(['*', '?']) && !is_implicit_glob(include) {
                let include_path = to_path(include, self.get_current_directory(), self.use_case_sensitive_file_names());
                if include_path == path {
                    return true;
                }
            }
        }
        if !self.wildcard_directories().is_empty() {
            unported!("glob.Parse");
        }
        false
    }

    // Go: tsoptions/parsedcommandline.go:361 (*ParsedCommandLine).PossiblyMatchesDirectoryName
    pub fn possibly_matches_directory_name(&self, directory_path: &Path) -> bool {
        for (wildcard_dir, recursive) in self.wildcard_directories() {
            let wildcard_dir_path =
                to_path(wildcard_dir, self.get_current_directory(), self.use_case_sensitive_file_names());
            if *recursive {
                if wildcard_dir_path.contains_path(directory_path) {
                    return true;
                }
            } else if wildcard_dir_path == *directory_path {
                return true;
            }
        }
        false
    }

    // Go: tsoptions/parsedcommandline.go:377 (*ParsedCommandLine).GetMatchedFileSpec
    pub fn get_matched_file_spec(&self, file_name: &str) -> String {
        self.config_file_specs().get_matched_file_spec(file_name, &self.compare_paths_options)
    }

    // Go: tsoptions/parsedcommandline.go:381 (*ParsedCommandLine).GetMatchedIncludeSpec
    pub fn get_matched_include_spec(&self, file_name: &str) -> (String, bool) {
        let specs = self.config_file_specs();
        if specs.validated_include_specs.is_empty() {
            return (String::new(), false);
        }

        if specs.is_default_include_spec {
            return (specs.validated_include_specs[0].clone(), true);
        }

        (specs.get_matched_include_spec(file_name, &self.compare_paths_options), false)
    }

    // PORT: Go reads `p.ConfigFile.configFileSpecs` and panics when either
    // pointer is nil. This helper does that read once.
    fn config_file_specs(&self) -> &ConfigFileSpecs {
        self.config_file
            .as_ref()
            .and_then(|c| c.config_file_specs.as_ref())
            .expect("nil pointer dereference: ConfigFile.configFileSpecs")
    }

    // Go: tsoptions/parsedcommandline.go:393 (*ParsedCommandLine).ReloadFileNamesOfParsedCommandLine
    // PORT: Go copies the cached `wildcardDirectories` map pointer; this
    // clones the cache cell. `includeGlobs` is not ported.
    pub fn reload_file_names_of_parsed_command_line(&self, fs: &dyn Fs) -> ParsedCommandLine {
        let mut parsed_config = self.parsed_config.clone();
        let (file_names, literal_file_names_len) = get_file_names_from_config_specs(
            self.config_file_specs().clone(),
            self.get_current_directory(),
            self.compiler_options(),
            fs,
            &self.extra_file_extensions,
        );
        parsed_config.file_names = file_names;
        ParsedCommandLine {
            parsed_config,
            config_file: self.config_file.clone(),
            errors: self.errors.clone(),
            raw: self.raw.clone(),
            compile_on_save: self.compile_on_save,
            compare_paths_options: self.compare_paths_options.clone(),
            wildcard_directories: self.wildcard_directories.clone(),
            extra_file_extensions: self.extra_file_extensions.clone(),
            literal_file_names_len,
            ..Default::default()
        }
    }

    // Go: tsoptions/parsedcommandline.go:418 (*ParsedCommandLine).Locale
    // PORT: `internal/locale` is out of scope.
    pub fn locale(&self) -> ! {
        let _ = &self.parsed_config.compiler_options.locale;
        unported!("locale.Parse")
    }
}
