//! Go `internal/project/project.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go `*Project` is
//! `Rc<RefCell<Project>>` (the dirty maps change it through the pointer).
//! Go `*compiler.Program` is `Rc<compiler::NewProgram>` (nil is
//! `None`). Go `*tsoptions.ParsedCommandLine` is
//! `Option<Rc<tsoptions::ParsedCommandLine>>`; Go pointer equality is
//! `Rc::ptr_eq`.

use crate::project::prelude::*;

use crate::contentmapper;
use crate::frontend::compiler::CompilerHost as _;
use crate::frontend::core_ext::{ProjectReference, TypeAcquisition};
use crate::frontend::vfs::Fs as _;
use crate::program::ls_program;
use std::cell::Cell;

// Go: project/project.go:22 inferredProjectName
pub const INFERRED_PROJECT_NAME: &str = "/dev/null/inferred"; // lowercase so toPath is a no-op regardless of settings
// Go: project/project.go:23 hr
pub const HR: &str = "-----------------------------------------------";

// Go: project/project.go:29 Kind
// PORT: Go `type Kind int` with iota consts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Kind(pub i32);

impl Kind {
    // Go: project/project.go:32 KindInferred
    pub const INFERRED: Kind = Kind(0);
    // Go: project/project.go:33 KindConfigured
    pub const CONFIGURED: Kind = Kind(1);
}

// Go: project/project.go:36 ProgramUpdateKind
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProgramUpdateKind(pub i32);

impl ProgramUpdateKind {
    // Go: project/project.go:39 ProgramUpdateKindNone
    pub const NONE: ProgramUpdateKind = ProgramUpdateKind(0);
    // Go: project/project.go:40 ProgramUpdateKindCloned
    pub const CLONED: ProgramUpdateKind = ProgramUpdateKind(1);
    // Go: project/project.go:41 ProgramUpdateKindSameFileNames
    pub const SAME_FILE_NAMES: ProgramUpdateKind = ProgramUpdateKind(2);
    // Go: project/project.go:42 ProgramUpdateKindNewFiles
    pub const NEW_FILES: ProgramUpdateKind = ProgramUpdateKind(3);
}

// Go: project/project.go:45 PendingReload
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PendingReload(pub i32);

impl PendingReload {
    // Go: project/project.go:48 PendingReloadNone
    pub const NONE: PendingReload = PendingReload(0);
    // Go: project/project.go:49 PendingReloadFileNames
    pub const FILE_NAMES: PendingReload = PendingReload(1);
    // Go: project/project.go:50 PendingReloadFull
    pub const FULL: PendingReload = PendingReload(2);
}

// Go: project/project.go:55 Project
// Project represents a TypeScript project.
// If changing struct fields, also update the Clone method.
// PORT: `commandLineWithTypingsFiles` and its `sync.Once` are written by
// `getCommandLineWithTypingsFiles`, which `CreateProgram` calls; they are a
// `RefCell` and a `Cell<bool>` so both take `&self`. Go
// `*collections.Set[tspath.Path]` is `Option<Rc<FxHashSet<..>>>` (Go
// replaces it with a clone before adding). Go
// `*collections.SyncSet[tspath.Path]` (the program files watch input) is
// `Option<Rc<RefCell<FxHashSet<..>>>>`, the sourceFS seen-files set.
#[derive(Default)]
pub struct Project {
    pub kind: Kind,
    pub current_directory: String,
    pub config_file_name: String,
    pub config_file_path: tspath::Path,

    pub dirty: bool,
    pub dirty_file_path: tspath::Path,

    pub host: Option<Rc<CompilerHost>>,
    pub command_line: Option<Rc<tsoptions::ParsedCommandLine>>,
    pub command_line_with_typings_files: RefCell<Option<Rc<tsoptions::ParsedCommandLine>>>,
    pub command_line_with_typings_files_once: Cell<bool>,
    pub program: Option<Rc<compiler::NewProgram>>,
    // The kind of update that was performed on the program last time it was updated.
    pub program_update_kind: ProgramUpdateKind,
    // The ID of the snapshot that created the program stored in this project.
    pub program_last_update: u64,
    // Set of projects that this project could be referencing.
    // Only set before actually loading config file to get actual project references
    pub potential_project_references: Option<Rc<FxHashSet<tspath::Path>>>,

    pub program_files_watch: Option<Rc<WatchedFiles<Option<Rc<RefCell<FxHashSet<tspath::Path>>>>>>>,
    pub typings_watch: Option<Rc<WatchedFiles<PatternsAndIgnored>>>,
    // tsgo#4712. PORT: Go `*collections.Set[tspath.Path]` (nil until the
    // first program) is `Option<Rc<FxHashSet<..>>>`.
    pub content_mapper_watch: Option<Rc<WatchedFiles<Vec<String>>>>,
    pub content_mapper_watched_files: Option<Rc<FxHashSet<tspath::Path>>>,

    pub checker_pool: Option<Rc<CheckerPool>>,

    // installedTypingsInfo is the value of `project.ComputeTypingsInfo()` that was
    // used during the most recently completed typings installation.
    pub installed_typings_info: Option<Rc<ata::TypingsInfo>>,
    // typingsFiles are the root files added by the typings installer.
    pub typings_files: Vec<String>,
}

// Go: project/project.go:91 NewConfiguredProject
// PORT: Go `*ProjectCollectionBuilder` is only read here, so it is a borrow.
pub fn new_configured_project(
    config_file_name: &str,
    _config_file_path: &tspath::Path,
    builder: &ProjectCollectionBuilder,
    logger: Option<Rc<logging::LogTree>>,
) -> Rc<RefCell<Project>> {
    new_project(
        config_file_name,
        Kind::CONFIGURED,
        &tspath::get_directory_path(config_file_name),
        builder,
        logger,
    )
}

// Go: project/project.go:100 NewInferredProject
// PORT: Go `*core.CompilerOptions` (nil-able) is `Option<Rc<CompilerOptions>>`.
// PORT: Go `[]*core.ProjectReference` is `Option<Vec<ProjectReference>>`
// (the `ParsedOptions` field type; nil is `None`).
#[allow(clippy::too_many_arguments)]
pub fn new_inferred_project(
    current_directory: &str,
    compiler_options: Option<Rc<CompilerOptions>>,
    root_file_names: &[String],
    project_references: Option<Vec<ProjectReference>>,
    content_mappers: &[Rc<contentmapper::Mapper>],
    builder: &ProjectCollectionBuilder,
    logger: Option<Rc<logging::LogTree>>,
) -> Rc<RefCell<Project>> {
    let p = new_project(
        INFERRED_PROJECT_NAME,
        Kind::INFERRED,
        current_directory,
        builder,
        logger,
    );
    let compiler_options = match compiler_options {
        Some(compiler_options) => compiler_options,
        None => Rc::new(CompilerOptions {
            allow_js: Tristate::True,
            module: ModuleKind::ES_NEXT,
            module_resolution: ModuleResolutionKind::BUNDLER,
            target: ScriptTarget::LATEST_STANDARD,
            jsx: JsxEmit::REACT_JSX,
            allow_importing_ts_extensions: Tristate::True,
            strict_null_checks: Tristate::True,
            strict_function_types: Tristate::True,
            source_map: Tristate::True,
            allow_non_ts_extensions: Tristate::True,
            resolve_json_module: Tristate::True,
            ..Default::default()
        }),
    };
    let command_line = new_inferred_project_command_line(
        compiler_options,
        root_file_names.to_vec(),
        project_references,
        content_mappers,
        tspath::ComparePathsOptions {
            use_case_sensitive_file_names: builder.fs.fs.use_case_sensitive_file_names(),
            current_directory: current_directory.to_string(),
        },
    );
    p.borrow_mut().command_line = Some(Rc::new(command_line));
    p
}

// Go: project/project.go:140 newInferredProjectCommandLine (tsgo#4712)
pub fn new_inferred_project_command_line(
    compiler_options: Rc<CompilerOptions>,
    root_file_names: Vec<String>,
    project_references: Option<Vec<ProjectReference>>,
    content_mappers: &[Rc<contentmapper::Mapper>],
    compare_paths_options: tspath::ComparePathsOptions,
) -> tsoptions::ParsedCommandLine {
    let mut command_line = tsoptions::new_parsed_command_line(
        compiler_options,
        root_file_names,
        project_references,
        compare_paths_options,
    );
    command_line.parsed_config.content_mappers = content_mappers.to_vec();
    command_line
}

// Go: project/project.go:156 newInferredProjectFromProject (ts#63950)
// newInferredProjectFromProject creates an isolated synthetic project seeded
// from an existing project's compiler state.
pub fn new_inferred_project_from_project(
    project: &Project,
    builder: &ProjectCollectionBuilder,
    logger: Option<Rc<logging::LogTree>>,
) -> Rc<RefCell<Project>> {
    let inferred = new_project(
        INFERRED_PROJECT_NAME,
        Kind::INFERRED,
        &project.current_directory,
        builder,
        logger,
    );
    {
        let mut p = inferred.borrow_mut();
        let program = project
            .program
            .as_ref()
            .expect("invalid memory address or nil pointer dereference: Project.Program");
        p.command_line = Some(program.command_line().clone());
        p.program = project.program.clone();
        p.program_last_update = project.program_last_update;
        p.host = project.host.clone();
        p.checker_pool = project.checker_pool.clone();
        p.content_mapper_watched_files = project.content_mapper_watched_files.clone();
        p.dirty = false;
    }
    inferred
}

// Go: project/project.go:134 NewProject
pub fn new_project(
    config_file_name: &str,
    kind: Kind,
    current_directory: &str,
    builder: &ProjectCollectionBuilder,
    logger: Option<Rc<logging::LogTree>>,
) -> Rc<RefCell<Project>> {
    if logger.is_some() {
        logger.log(&format!(
            "Creating {}Project: {}, currentDirectory: {}",
            kind.string(),
            config_file_name,
            current_directory
        ));
    }
    let mut project = Project {
        config_file_name: config_file_name.to_string(),
        kind,
        current_directory: current_directory.to_string(),
        dirty: true,
        ..Default::default()
    };

    project.config_file_path = tspath::to_path(
        config_file_name,
        current_directory,
        builder.fs.fs.use_case_sensitive_file_names(),
    );
    project.program_files_watch = Some(new_watched_files(
        &format!("program files for {config_file_name}"),
        lsproto::WatchKind(
            lsproto::WatchKind::CREATE.0
                | lsproto::WatchKind::CHANGE.0
                | lsproto::WatchKind::DELETE.0,
        ),
        lsproto::get_client_capabilities(&builder.ctx)
            .workspace
            .did_change_watched_files
            .relative_pattern_support,
        create_resolution_lookup_glob_mapper(
            &builder.session_options.current_directory,
            &builder.session_options.default_library_path,
            &project.current_directory,
            builder.fs.fs.use_case_sensitive_file_names(),
        ),
    ));
    if !builder.session_options.typings_location.is_empty() {
        // Go: core.Identity
        let identity: Rc<dyn Fn(&PatternsAndIgnored) -> PatternsAndIgnored> =
            Rc::new(|p: &PatternsAndIgnored| p.clone());
        project.typings_watch = Some(new_watched_files(
            "typings installer files",
            lsproto::WatchKind(
                lsproto::WatchKind::CREATE.0
                    | lsproto::WatchKind::CHANGE.0
                    | lsproto::WatchKind::DELETE.0,
            ),
            lsproto::get_client_capabilities(&builder.ctx)
                .workspace
                .did_change_watched_files
                .relative_pattern_support,
            identity,
        ));
    }
    project.content_mapper_watch = Some(new_watched_files_for_paths(
        &format!("content mapper configuration files for {config_file_name}"),
        lsproto::WatchKind(
            lsproto::WatchKind::CREATE.0
                | lsproto::WatchKind::CHANGE.0
                | lsproto::WatchKind::DELETE.0,
        ),
        lsproto::get_client_capabilities(&builder.ctx)
            .workspace
            .did_change_watched_files
            .relative_pattern_support,
        &builder.session_options.current_directory,
        &builder.session_options.current_directory,
        builder.fs.fs.use_case_sensitive_file_names(),
    ));
    Rc::new(RefCell::new(project))
}

impl Project {
    // Go: project/project.go:169 Project.Name
    pub fn name(&self) -> String {
        self.config_file_name.clone()
    }

    // Go: project/project.go:198 Project.CurrentDirectory (ts#63935)
    pub fn current_directory(&self) -> String {
        self.current_directory.clone()
    }

    // Go: project/project.go:177 Project.DisplayName
    // DisplayName returns a short, human-readable name for the project,
    // relative to the given workspace root directory.
    // For configured projects, this is the config file path made relative.
    // For inferred projects, this is the last component of the current directory.
    pub fn display_name(&self, cwd: &str) -> String {
        if self.kind == Kind::INFERRED {
            return tspath::get_base_file_name(&self.current_directory);
        }
        tspath::convert_to_relative_path(
            &self.config_file_name,
            &tspath::ComparePathsOptions {
                current_directory: cwd.to_string(),
                ..Default::default()
            },
        )
    }

    // Go: project/project.go:186 Project.ID
    // PORT: Go also has `Id()` (the `ls.Project` method, same snake name);
    // it is the `ls::Project` impl below. Both return the config file path.
    pub fn id(&self) -> tspath::Path {
        self.config_file_path.clone()
    }

    // Go: project/project.go:191 Project.ConfigFileName
    // ConfigFileName panics if Kind() is not KindConfigured.
    pub fn config_file_name(&self) -> String {
        if self.kind != Kind::CONFIGURED {
            panic!("ConfigFileName called on non-configured project");
        }
        self.config_file_name.clone()
    }

    // Go: project/project.go:199 Project.ConfigFilePath
    // ConfigFilePath panics if Kind() is not KindConfigured.
    pub fn config_file_path(&self) -> tspath::Path {
        if self.kind != Kind::CONFIGURED {
            panic!("ConfigFilePath called on non-configured project");
        }
        self.config_file_path.clone()
    }

    // Go: project/project.go:210 Project.GetProgram
    // PORT: Go returns a nil program as nil; the `ls::Project` impl below
    // (which returns a program handle) panics on it.
    pub fn get_program(&self) -> Option<Rc<compiler::NewProgram>> {
        self.program.clone()
    }

    // Go: project/project.go:217 Project.GetProjectDiagnostics
    // GetProjectDiagnostics returns program diagnostics combined with any global
    // diagnostics discovered during checking. These are the diagnostics reported on
    // the tsconfig.json file.
    pub fn get_project_diagnostics(&self, _ctx: &Context) -> Vec<Diagnostic> {
        let mut global_diags: Vec<Diagnostic> = Vec::new();
        if let Some(checker_pool) = &self.checker_pool {
            global_diags = checker_pool.get_global_diagnostics();
        }
        let program = self
            .program
            .as_deref()
            .expect("invalid memory address or nil pointer dereference: Project.Program");
        // Go: slices.Concat
        let mut diagnostics = program.get_config_file_parsing_diagnostics();
        diagnostics.extend(ls_program::get_program_diagnostics(program));
        diagnostics.extend(global_diags);
        sort_and_deduplicate_diagnostics(diagnostics)
    }

    // Go: project/project.go:228 Project.HasFile
    pub fn has_file(&self, file_name: &str) -> bool {
        self.contains_file(&self.to_path(file_name))
    }

    // Go: project/project.go:232 Project.containsFile
    pub fn contains_file(&self, path: &tspath::Path) -> bool {
        self.program
            .as_ref()
            .is_some_and(|program| program.get_source_file_by_path(path).is_some())
    }

    // Go: project/project.go:236 Project.IsSourceFromProjectReference
    pub fn is_source_from_project_reference(&self, path: &tspath::Path) -> bool {
        self.program
            .as_ref()
            .is_some_and(|program| program.is_source_from_project_reference(path))
    }

    // Go: project/project.go:240 Project.Clone
    // PORT: Go `Clone()` is `clone_` (dirty decision 3). The `sync.Once` is
    // not copied (Go leaves the zero value).
    pub fn clone_(&self) -> Rc<RefCell<Project>> {
        Rc::new(RefCell::new(Project {
            kind: self.kind,
            current_directory: self.current_directory.clone(),
            config_file_name: self.config_file_name.clone(),
            config_file_path: self.config_file_path.clone(),

            dirty: self.dirty,
            dirty_file_path: self.dirty_file_path.clone(),

            host: self.host.clone(),
            command_line: self.command_line.clone(),
            command_line_with_typings_files: RefCell::new(
                self.command_line_with_typings_files.borrow().clone(),
            ),
            command_line_with_typings_files_once: Cell::new(false),
            program: self.program.clone(),
            program_update_kind: ProgramUpdateKind::NONE,
            program_last_update: self.program_last_update,
            potential_project_references: self.potential_project_references.clone(),

            program_files_watch: self.program_files_watch.clone(),
            typings_watch: self.typings_watch.clone(),
            content_mapper_watch: self.content_mapper_watch.clone(),
            content_mapper_watched_files: self.content_mapper_watched_files.clone(),

            checker_pool: self.checker_pool.clone(),

            installed_typings_info: self.installed_typings_info.clone(),
            typings_files: self.typings_files.clone(),
        }))
    }

    // Go: project/project.go:275 Project.SetCommandLine
    // SetCommandLine reassigns the project's command line and resets all state derived
    // from it. Changing the command line always requires a full program rebuild, so the
    // project is marked fully dirty. It also resets:
    //   - the memoized command line augmented with typings files (and its sync.Once, so
    //     the augmented command line is rebuilt from the new command line on next access);
    //   - potentialProjectReferences, the pre-load placeholder derived from the old
    //     command line (always nil for inferred projects, which have no project references).
    pub fn set_command_line(&mut self, command_line: Option<Rc<tsoptions::ParsedCommandLine>>) {
        self.command_line = command_line;
        *self.command_line_with_typings_files.borrow_mut() = None;
        self.command_line_with_typings_files_once = Cell::new(false);
        self.potential_project_references = None;
        self.dirty = true;
        self.dirty_file_path = tspath::Path::default();
    }

    // Go: project/project.go:285 Project.getCommandLineWithTypingsFiles
    // getCommandLineWithTypingsFiles returns the command line augmented with typing files if ATA is enabled.
    pub fn get_command_line_with_typings_files(&self) -> Option<Rc<tsoptions::ParsedCommandLine>> {
        if self.typings_files.is_empty() {
            return self.command_line.clone();
        }

        // Check if ATA is enabled for this project
        let type_acquisition = self.get_type_acquisition();
        match &type_acquisition {
            Some(type_acquisition) if type_acquisition.enable.is_true() => {}
            _ => return self.command_line.clone(),
        }

        // Go: p.commandLineWithTypingsFilesOnce.Do(..)
        if !self.command_line_with_typings_files_once.replace(true)
            && self.command_line_with_typings_files.borrow().is_none()
        {
            let command_line = self
                .command_line
                .as_ref()
                .expect("invalid memory address or nil pointer dereference: Project.CommandLine");
            // Create an augmented command line that includes typing files
            let original_root_names = command_line.file_names();
            let mut new_root_names: Vec<String> =
                Vec::with_capacity(original_root_names.len() + self.typings_files.len());
            new_root_names.extend_from_slice(original_root_names);
            new_root_names.extend_from_slice(&self.typings_files);

            // tsgo#4712
            let augmented = command_line.with_file_names(new_root_names);
            *self.command_line_with_typings_files.borrow_mut() = Some(Rc::new(augmented));
        }
        self.command_line_with_typings_files.borrow().clone()
    }

    // Go: project/project.go:318 Project.setPotentialProjectReference
    pub fn set_potential_project_reference(&mut self, config_file_path: &tspath::Path) {
        let mut potential_project_references = match &self.potential_project_references {
            None => FxHashSet::default(),
            // Go: p.potentialProjectReferences.Clone()
            Some(references) => (**references).clone(),
        };
        potential_project_references.insert(config_file_path.clone());
        self.potential_project_references = Some(Rc::new(potential_project_references));
    }

    // Go: project/project.go:327 Project.hasPotentialProjectReference
    pub fn has_potential_project_reference(
        &self,
        project_tree_request: &ProjectTreeRequest,
    ) -> bool {
        if let Some(command_line) = &self.command_line {
            for path in command_line.resolved_project_reference_paths() {
                if project_tree_request.is_project_referenced(&self.to_path(path)) {
                    return true;
                }
            }
        } else if let Some(potential_project_references) = &self.potential_project_references {
            for path in potential_project_references.iter() {
                if project_tree_request.is_project_referenced(path) {
                    return true;
                }
            }
        }
        false
    }

    // Go: project/project.go:349 Project.CreateProgram
    // PORT: Go `compiler.NewProgram(opts)` is `ls_program::new_program(opts,
    // create_checker_pool)` and `p.Program.UpdateProgram(..)` is
    // `ls_program::update_program(p.Program, ..)` (contract C3). Go
    // `ProgramOptions.CreateCheckerPool` is their last argument.
    pub fn create_program(&self) -> CreateProgramResult {
        let mut update_kind = ProgramUpdateKind::NEW_FILES;
        let mut program_cloned = false;
        let new_program: Rc<compiler::NewProgram>;

        let host = self
            .host
            .clone()
            .expect("invalid memory address or nil pointer dereference: Project.host");

        // Define a fresh CreateCheckerPool closure for this call. Each invocation of
        // CreateProgram must use its own closure so that concurrent goroutines cloning
        // the same project never share a captured variable through a stale closure
        // stored in the old program's options.
        // PORT: Go reads `p.host.sessionOptions.CheckerPoolOptions` when the
        // closure runs; the session options never change, so the value is
        // copied here. Go passes the method value `p.log`, whose body is
        // empty (`// !!!`); a closure that holds the project would make a
        // reference cycle (project -> program -> pool -> project), so the
        // pool gets an empty closure. Go reads the pool back with
        // `result.Program.GetCheckerPool().(*checkerPool)`; a Rust trait
        // object can not be downcast, so the closure also keeps the pool it
        // made and `CreateProgramResult.checker_pool` returns it.
        let created_checker_pool: Rc<RefCell<Option<Rc<CheckerPool>>>> =
            Rc::new(RefCell::new(None));
        let create_checker_pool: ls_program::CreateCheckerPool = {
            let checker_pool_options = host.session_options.checker_pool_options.clone();
            let created_checker_pool = created_checker_pool.clone();
            Rc::new(
                move |program: &Rc<compiler::NewProgram>| -> Rc<dyn ls_program::CheckerPool> {
                    let log: Rc<dyn Fn(&str)> = Rc::new(|_msg: &str| {
                        // Go: p.log(msg) (empty body)
                    });
                    let pool = new_checker_pool(
                        checker_pool_options.clone(),
                        Rc::clone(program),
                        Some(log),
                    );
                    *created_checker_pool.borrow_mut() = Some(pool.clone());
                    pool
                },
            )
        };

        // Create the command line, potentially augmented with typing files
        let command_line = self.get_command_line_with_typings_files();

        let same_command_line = match (&self.program, &command_line) {
            (Some(program), Some(command_line)) => Rc::ptr_eq(program.command_line(), command_line),
            _ => false,
        };
        if !self.dirty_file_path.is_empty() && self.program.is_some() && same_command_line {
            let program = self.program.as_deref().expect("checked above");
            let host_rc: Rc<dyn compiler::CompilerHost> = host.clone();
            let (updated_program, dirty_file, cloned) = ls_program::update_program(
                program,
                &self.dirty_file_path,
                host_rc,
                Some(create_checker_pool.clone()),
            );
            new_program = updated_program;
            program_cloned = cloned;
            // Go: p.host.builder (read in each branch below)
            let builder = || {
                host.builder.borrow().clone().expect(
                    "invalid memory address or nil pointer dereference: compilerHost.builder",
                )
            };
            if program_cloned {
                update_kind = ProgramUpdateKind::CLONED;
                let builder = builder();
                for file in new_program.source_files() {
                    // Use pointer identity: dirtyFile is the exact instance UpdateProgram acquired,
                    // and it is the only file whose refcount is already accounted for.
                    let is_dirty_file = dirty_file
                        .as_ref()
                        .is_some_and(|dirty_file| Rc::ptr_eq(dirty_file, file));
                    if !is_dirty_file
                        && !file.is_content_mapper_failure_stub()
                        && !file.is_content_mapper_supplemental()
                    {
                        // UpdateProgram acquired the changed file only, so we need to ref everything else
                        if !file.content_mapper().is_empty() {
                            builder
                                .content_mapped_parse_cache
                                .ref_(&content_mapped_parse_cache_key_for_file(file));
                        } else {
                            ref_program_file(
                                &builder.parse_cache,
                                file.parse_options(),
                                file.text,
                                file.script_kind,
                            );
                        }
                    }
                }
                for file in new_program.duplicate_source_files() {
                    if !file.is_content_mapper_failure_stub {
                        if !file.content_mapper.is_empty() {
                            builder
                                .content_mapped_parse_cache
                                .ref_(&content_mapped_parse_cache_key_for_duplicate(file));
                        } else {
                            ref_program_file(
                                &builder.parse_cache,
                                &file.parse_options,
                                file.text,
                                file.script_kind,
                            );
                        }
                    }
                }
            } else if let Some(dirty_file) = &dirty_file {
                // UpdateProgram always acquires the dirty file before deciding whether it can
                // reuse the old program. If it falls back to a full rebuild, release that
                // speculative acquire so the rebuilt program is the only remaining owner.
                if !dirty_file.content_mapper().is_empty() {
                    deref_content_mapped_file(
                        &builder().content_mapped_parse_cache,
                        &content_mapped_parse_cache_key_for_file(dirty_file),
                    );
                } else {
                    deref_program_file(
                        &builder().parse_cache,
                        dirty_file.parse_options(),
                        dirty_file.text,
                        dirty_file.script_kind,
                    );
                }
            }
        } else {
            let mut typings_location = String::new();
            let type_acquisition = self
                .get_type_acquisition()
                .expect("invalid memory address or nil pointer dereference: TypeAcquisition");
            if type_acquisition.enable.is_true() {
                typings_location = host.session_options.typings_location.clone();
            }
            let host_rc: Rc<dyn compiler::CompilerHost> = host.clone();
            new_program = ls_program::new_program(
                compiler::ProgramOptions {
                    host: host_rc,
                    config: command_line
                        .clone()
                        .expect("invalid memory address or nil pointer dereference: Config"),
                    use_source_of_project_reference: true,
                    single_threaded: Tristate::Unknown,
                    typings_location,
                    project_name: String::new(),
                },
                Some(create_checker_pool),
            );
        }

        if !program_cloned
            && self
                .program
                .as_ref()
                .is_some_and(|program| program.has_same_file_names(&new_program))
        {
            update_kind = ProgramUpdateKind::SAME_FILE_NAMES;
        }

        ls_program::bind_source_files(&new_program);

        let checker_pool = created_checker_pool.borrow().clone();
        CreateProgramResult {
            program: new_program,
            update_kind,
            checker_pool,
        }
    }

    // Go: project/project.go:415 Project.CloneWatchers
    pub fn clone_watchers(
        &self,
    ) -> Option<Rc<WatchedFiles<Option<Rc<RefCell<FxHashSet<tspath::Path>>>>>>> {
        let host = self
            .host
            .as_ref()
            .expect("invalid memory address or nil pointer dereference: Project.host");
        let seen_files = host.source_fs.seen_files.borrow().clone();
        WatchedFiles::clone_(self.program_files_watch.as_deref(), seen_files)
    }

    // Go: project/project.go:419 Project.log
    pub fn log(&self, _msg: &str) {
        // !!!
    }

    // Go: project/project.go:423 Project.toPath
    pub fn to_path(&self, file_name: &str) -> tspath::Path {
        let host = self
            .host
            .as_ref()
            .expect("invalid memory address or nil pointer dereference: Project.host");
        tspath::to_path(
            file_name,
            &self.current_directory,
            host.fs().use_case_sensitive_file_names(),
        )
    }

    // Go: project/project.go:427 Project.print
    pub fn print(
        &self,
        write_file_names: bool,
        _write_file_explanation: bool,
        builder: &mut String,
    ) -> String {
        builder.push_str(&format!("\nProject '{}'\n", self.name()));
        match &self.program {
            None => {
                builder.push_str("\tFiles (0) NoProgram\n");
            }
            Some(program) => {
                let source_files = program.get_source_files();
                builder.push_str(&format!("\tFiles ({})\n", source_files.len()));
                if write_file_names {
                    for source_file in source_files {
                        builder.push_str("\t\t");
                        builder.push_str(source_file.file_name());
                        builder.push('\n');
                    }
                    // !!!
                    // if writeFileExplanation {}
                }
            }
        }
        builder.push_str(HR);
        builder.clone()
    }

    // Go: project/project.go:449 Project.GetTypeAcquisition
    // GetTypeAcquisition returns the type acquisition settings for this project.
    // PORT: Go returns a pointer (nil-able); the command line's value is
    // copied into a new `Rc`.
    pub fn get_type_acquisition(&self) -> Option<Rc<TypeAcquisition>> {
        if self.kind == Kind::INFERRED {
            // For inferred projects, use default settings
            return Some(Rc::new(TypeAcquisition {
                enable: Tristate::True,
                include: Vec::new(),
                exclude: Vec::new(),
                disable_filename_based_type_acquisition: Tristate::False,
            }));
        }

        if let Some(command_line) = &self.command_line {
            return command_line
                .type_acquisition()
                .map(|type_acquisition| Rc::new(type_acquisition.clone()));
        }

        None
    }

    // Go: project/project.go:468 Project.GetUnresolvedImports
    // GetUnresolvedImports extracts unresolved imports from this project's program.
    // PORT: Go returns the program's cached set; the port copies it into an `Rc`.
    pub fn get_unresolved_imports(&self) -> Option<Rc<FxHashSet<String>>> {
        let program = self.program.as_ref()?;

        Some(Rc::new(program.get_unresolved_imports().clone()))
    }

    // Go: project/project.go:477 Project.ShouldTriggerATA
    // ShouldTriggerATA determines if ATA should be triggered for this project.
    pub fn should_trigger_ata(&self, snapshot_id: u64) -> bool {
        if self.program.is_none() || self.command_line.is_none() {
            return false;
        }

        let type_acquisition = self.get_type_acquisition();
        match &type_acquisition {
            Some(type_acquisition) if type_acquisition.enable.is_true() => {}
            _ => return false,
        }

        let Some(installed_typings_info) = &self.installed_typings_info else {
            return true;
        };
        if self.program_last_update == snapshot_id
            && self.program_update_kind == ProgramUpdateKind::NEW_FILES
        {
            return true;
        }

        !installed_typings_info.equals(&self.compute_typings_info())
    }

    // Go: project/project.go:494 Project.ComputeTypingsInfo
    pub fn compute_typings_info(&self) -> ata::TypingsInfo {
        ata::TypingsInfo {
            // Go: p.CommandLine.CompilerOptions() (nil receiver gives nil)
            compiler_options: self
                .command_line
                .as_ref()
                .map(|command_line| command_line.compiler_options().clone()),
            type_acquisition: self.get_type_acquisition(),
            unresolved_imports: self.get_unresolved_imports(),
        }
    }
}

// Go: project/project.go:240 Project.Clone (dirty.Cloneable)
impl dirty::Cloneable for Rc<RefCell<Project>> {
    fn clone_(&self) -> Self {
        self.borrow().clone_()
    }
}

// Go: project/project.go:89 `var _ ls.Project = (*Project)(nil)`
impl ls::Project for Project {
    // Go: project/project.go:206 Project.Id
    fn id(&self) -> tspath::Path {
        self.config_file_path.clone()
    }

    // Go: project/project.go:210 Project.GetProgram
    // PORT: `ls::Project` returns a program handle; Go returns nil for a
    // project without a program, which the port can not represent.
    fn get_program(&self) -> Rc<compiler::NewProgram> {
        self.program
            .clone()
            .expect("invalid memory address or nil pointer dereference: Project.Program")
    }

    // Go: project/project.go:228 Project.HasFile
    fn has_file(&self, file_name: &str) -> bool {
        Project::has_file(self, file_name)
    }
}

// PORT: projects are shared as `Rc<RefCell<Project>>`; this impl lets them
// coerce to `Rc<dyn ls::Project>` (Go passes the `*Project`).
impl ls::Project for RefCell<Project> {
    fn id(&self) -> tspath::Path {
        ls::Project::id(&*self.borrow())
    }

    fn get_program(&self) -> Rc<compiler::NewProgram> {
        ls::Project::get_program(&*self.borrow())
    }

    fn has_file(&self, file_name: &str) -> bool {
        ls::Project::has_file(&*self.borrow(), file_name)
    }
}

// Go: project/project.go:344 CreateProgramResult
// PORT: `checker_pool` is the pool that the CreateCheckerPool closure made
// for `program` (Go `result.Program.GetCheckerPool().(*checkerPool)`).
#[derive(Clone)]
pub struct CreateProgramResult {
    pub program: Rc<compiler::NewProgram>,
    pub update_kind: ProgramUpdateKind,
    pub checker_pool: Option<Rc<CheckerPool>>,
}
