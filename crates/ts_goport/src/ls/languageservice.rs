//! Port of Go `ls/languageservice.go`.

use crate::ls::prelude::*;

// Go: ls/languageservice.go:15 LanguageService
// PORT: plan contract C4. Go `*compiler.Program` is the leaked
// `&'static compiler::NewProgram`. Go `Host` is `Rc<dyn Host>`, Go
// `*lsconv.Converters` is shared (`Rc`). All methods take `&self`, so the
// mapper cache is a `RefCell`. The fields are `pub` because other files of
// package `ls` read them (Go same-package access).
// PORT: `P` is the program. It is `&'static NewProgram` except on a search
// thread of a cross-project request (`program_view.rs`). The methods that
// the search runs are in `impl<P: ProgramView> LanguageService<P>` blocks;
// all other methods are for the default `P` only.
pub struct LanguageService<P = &'static compiler::NewProgram> {
    pub project_path: tspath::Path,
    pub host: Rc<dyn Host>,
    pub active_config: lsutil::UserPreferences,
    pub program: P,
    pub converters: Rc<lsconv::Converters>,
    // PORT: Go caches `*DocumentPositionMapper` values, including nil. The
    // contract type holds only non-nil mappers, so a nil result is not cached
    // and is computed again on the next call. The host is a snapshot, so the
    // result is the same.
    pub document_position_mappers:
        RefCell<FxHashMap<String, Rc<sourcemap::DocumentPositionMapper>>>,
    /// Makes `program` the current program (`prog()`) while the language
    /// service lives, for the checker code that its methods run. A later
    /// language service or checker that is still alive takes over; use
    /// `enter_program` when several language services are used in turn.
    // PORT: Go reads the program through `l.program`; the ported checker
    // code reads the current program of the thread.
    _program_guard: ls_program::ProgramGuard,
}

// Go: ls/languageservice.go:24 NewLanguageService
// PORT: Go returns `*LanguageService`; the caller owns the value here.
pub fn new_language_service(
    project_path: tspath::Path,
    program: &'static compiler::NewProgram,
    host: Rc<dyn Host>,
    active_file: &str,
) -> LanguageService {
    // Go evaluates the composite literal fields in source order:
    // `host.Converters()` before `host.GetPreferences(activeFile)`.
    let converters = host.converters();
    let active_config = host.get_preferences(active_file);
    LanguageService {
        project_path,
        host,
        program,
        converters,
        active_config,
        document_position_mappers: RefCell::new(FxHashMap::default()),
        _program_guard: ls_program::enter(program),
    }
}

/// A language service for a program view that is not a `NewProgram` (a
/// search thread, see `search_thread.rs`). `program_guard` makes the
/// view's program version current (`ls_program::enter_version`).
pub fn new_language_service_for_view<P: ProgramView>(
    project_path: tspath::Path,
    program: P,
    host: Rc<dyn Host>,
    active_config: lsutil::UserPreferences,
    program_guard: ls_program::ProgramGuard,
) -> LanguageService<P> {
    let converters = host.converters();
    LanguageService {
        project_path,
        host,
        program,
        converters,
        active_config,
        document_position_mappers: RefCell::new(FxHashMap::default()),
        _program_guard: program_guard,
    }
}

impl LanguageService {
    /// Makes this language service's program current again while the guard
    /// lives (see the `_program_guard` field).
    pub fn enter_program(&self) -> ls_program::ProgramGuard {
        ls_program::enter(self.program)
    }
}

impl<P: ProgramView> LanguageService<P> {
    // Go: ls/languageservice.go:40 toPath
    pub fn to_path(&self, file_name: &str) -> tspath::Path {
        tspath::to_path(
            file_name,
            &self.program.get_current_directory(),
            self.use_case_sensitive_file_names(),
        )
    }

    // Go: ls/languageservice.go:44 GetProgram
    pub fn get_program(&self) -> P {
        self.program
    }

    // Go: ls/languageservice.go:48 UserPreferences
    // PORT: Go returns the struct by value (a copy).
    pub fn user_preferences(&self) -> lsutil::UserPreferences {
        self.active_config.clone()
    }

    // Go: ls/languageservice.go:52 FormatOptions
    // PORT: Go returns the struct by value (a copy).
    pub fn format_options(&self) -> lsutil::FormatCodeSettings {
        self.active_config.format_code_settings.clone()
    }

    // Go: ls/languageservice.go:56 tryGetProgramAndFile
    // PORT: Go `*ast.SourceFile` is the file root `Node` (`Node::NIL` when the
    // program has no such file).
    pub fn try_get_program_and_file(&self, file_name: &str) -> (P, Node) {
        let program = self.get_program();
        let file = program.source_file_root(file_name);
        (program, file)
    }

    // Go: ls/languageservice.go:62 getProgramAndFile
    // PORT: Go passes the URI by value; here by reference.
    pub fn get_program_and_file(&self, document_uri: &lsproto::DocumentUri) -> (P, Node) {
        let file_name = document_uri.file_name();
        let (program, file) = self.try_get_program_and_file(&file_name);
        if file.is_nil() {
            panic!("file not found: {file_name}");
        }
        (program, file)
    }

    // Go: ls/languageservice.go:71 GetDocumentPositionMapper
    // PORT: Go returns `*sourcemap.DocumentPositionMapper`; nil is `None`. See
    // the `document_position_mappers` field for the nil cache entry.
    pub fn get_document_position_mapper(
        &self,
        file_name: &str,
    ) -> Option<Rc<sourcemap::DocumentPositionMapper>> {
        let cached = self
            .document_position_mappers
            .borrow()
            .get(file_name)
            .cloned();
        if let Some(d) = cached {
            return Some(d);
        }
        let d = sourcemap::get_document_position_mapper(self, file_name);
        if let Some(d) = &d {
            self.document_position_mappers
                .borrow_mut()
                .insert(file_name.to_string(), d.clone());
        }
        d
    }

    // Go: ls/languageservice.go:80 ReadFile
    pub fn read_file(&self, file_name: &str) -> (String, bool) {
        self.host.read_file(file_name)
    }

    // Go: ls/languageservice.go:84 UseCaseSensitiveFileNames
    pub fn use_case_sensitive_file_names(&self) -> bool {
        self.host.use_case_sensitive_file_names()
    }

    // Go: ls/languageservice.go:88 GetECMALineInfo
    pub fn get_ecma_line_info(
        &self,
        file_name: &str,
    ) -> Option<Rc<sourcemap::lineinfo::ECMALineInfo>> {
        self.host.get_ecma_line_info(file_name)
    }
}

impl LanguageService {
    // Go: ls/languageservice.go:95 getPreparedAutoImportView
    // getPreparedAutoImportView returns an auto-import view for the given file if the registry is prepared
    // to provide up-to-date auto-imports for it. If not, it returns ErrNeedsAutoImports.
    // PORT: Go `*autoimport.View` is shared as `Rc<autoimport::View>` (wave 3
    // notes); nil is `None`.
    pub fn get_prepared_auto_import_view(
        &self,
        from_file: Node,
    ) -> Result<Option<Rc<autoimport::View>>, GoError> {
        let registry = self.host.auto_import_registry();
        if !autoimport::Registry::is_prepared_for_importing_file(
            registry.as_deref(),
            source_file_file_name(from_file),
            &self.project_path,
            &self.user_preferences(),
        ) {
            return Err((*ERR_NEEDS_AUTO_IMPORTS).clone());
        }

        // PORT: a nil registry is never prepared, so it is set here.
        let registry = registry.expect("invalid memory address or nil pointer dereference");
        let view = autoimport::new_view(
            registry,
            from_file,
            self.project_path.clone(),
            self.program,
            self.user_preferences().module_specifier_preferences(),
        );
        Ok(Some(Rc::new(view)))
    }

    // Go: ls/languageservice.go:110 getCurrentAutoImportView
    // getCurrentAutoImportView returns an auto-import view for the given file, based on the current state
    // of the auto-import registry, which may or may not be up-to-date.
    // PORT: Go builds a view with a nil registry and panics only when a view
    // method reads it. `autoimport::new_view` takes a non-nil registry, so a
    // nil registry panics here, earlier than in Go.
    pub fn get_current_auto_import_view(&self, from_file: Node) -> Rc<autoimport::View> {
        let registry = self
            .host
            .auto_import_registry()
            .expect("invalid memory address or nil pointer dereference");
        Rc::new(autoimport::new_view(
            registry,
            from_file,
            self.project_path.clone(),
            self.program,
            self.user_preferences().module_specifier_preferences(),
        ))
    }

    // Go: ls/languageservice.go:121 DirectoryExists
    // Used for module specifier completions.
    pub fn directory_exists(&self, path: &str) -> bool {
        self.host.directory_exists(path)
    }

    // Go: ls/languageservice.go:126 ReadDirectory
    // Used for module specifier completions.
    pub fn read_directory(
        &self,
        path: &str,
        extensions: &[String],
        includes: &[String],
    ) -> Vec<String> {
        self.host.read_directory(
            &self.program.get_current_directory(),
            path,
            extensions,
            &[], /*excludes*/
            includes,
            crate::frontend::vfs::vfsmatch::UNLIMITED_DEPTH,
        )
    }

    // Go: ls/languageservice.go:130 GetDirectories
    pub fn get_directories(&self, path: &str) -> Vec<String> {
        self.host.get_directories(path)
    }
}

// PORT: Go `*LanguageService` implements `sourcemap.Host` through its
// `UseCaseSensitiveFileNames`, `GetECMALineInfo` and `ReadFile` methods
// (`GetDocumentPositionMapper` passes `l`). The inherent methods above win in
// method syntax, so these calls do not recurse.
impl<P: ProgramView> sourcemap::Host for LanguageService<P> {
    fn use_case_sensitive_file_names(&self) -> bool {
        LanguageService::use_case_sensitive_file_names(self)
    }

    fn get_ecma_line_info(&self, file_name: &str) -> Option<Rc<sourcemap::lineinfo::ECMALineInfo>> {
        LanguageService::get_ecma_line_info(self, file_name)
    }

    fn read_file(&self, file_name: &str) -> (String, bool) {
        LanguageService::read_file(self, file_name)
    }
}
