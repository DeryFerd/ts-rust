use crate::ls::autoimport::prelude::*;

// Port of Go `ls/autoimport/aliasresolver.go`.
//
// PORT: Go `aliasResolver` implements `checker.Program`, so the registry can
// make a checker (`checker.NewChecker(aliasResolver, nil)`) over node_modules
// entrypoint files that are not in any program. A ts_goport checker reads
// its program version (`prog()`), so `new_checker` makes an alias resolver
// program (`program::new_alias_resolver_program`). The `checker.Program`
// methods are inherent methods with the Go logic. The `program.rs`
// functions call the lazy ones through `program::AliasResolverProgram`, and
// give Go's constant or panic for the others.
// PORT: the registry host parses the files outside any program. Each file
// is published with no program and bound into the binder lineage, as
// sourcedefinition does (`bind_alias_resolver_source_file`). A file that
// the checker asks for is read, published and bound then, and the checker
// catches its arena up to the lineage before it reads the file (see
// `new_checker`).

use crate::frontend::core_ext::HasFileName;
use crate::frontend::module;
use crate::frontend::module::ResolutionHost as _;
use crate::frontend::packagejson;
use crate::frontend::tsoptions;
use crate::frontend::tspath;
use crate::frontend::vfs::Fs as _;
use crate::modulespecifiers::symlinks::KnownSymlinks;
use crate::program::{AliasResolverProgram, AliasResolverProgramScope};
use std::cell::Cell;
use std::sync::Arc;

// Go: ls/autoimport/aliasresolver.go:16 pathAndFileName
#[derive(Clone, Debug, Default)]
pub struct PathAndFileName {
    pub path: tspath::Path,
    pub file_name: String,
}

// Go: ls/autoimport/aliasresolver.go:21 aliasResolver
// PORT: Go `collections.SyncMap` values are `RefCell<FxHashMap>` (one
// thread). A Go nil `symlinks` map is an empty map. `checker_program` is
// the port's (see `new_checker`).
pub struct AliasResolver {
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub host: Rc<dyn RegistryCloneHost>,
    pub module_resolver: Rc<module::DefaultResolver>,

    pub root_files: Vec<Node>,
    // symlinks maps from realpath to symlinked path and file name
    pub symlinks: FxHashMap<tspath::Path, PathAndFileName>,
    pub on_failed_ambient_module_lookup: Rc<dyn Fn(&dyn HasFileName, &str)>,
    pub resolved_modules: RefCell<
        FxHashMap<
            tspath::Path,
            Rc<RefCell<FxHashMap<module::ModeAwareCacheKey, Arc<ResolvedModule>>>>,
        >,
    >,
    /// The program of the checker, once `new_checker` made it (a stopped
    /// build makes none).
    pub checker_program: Cell<Option<&'static GoProgram>>,
}

// Go: ls/autoimport/aliasresolver.go:33 newAliasResolver
pub fn new_alias_resolver(
    root_files: Vec<Node>,
    symlinks: FxHashMap<tspath::Path, PathAndFileName>,
    host: Rc<dyn RegistryCloneHost>,
    module_resolver: Rc<module::DefaultResolver>,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    on_failed_ambient_module_lookup: Rc<dyn Fn(&dyn HasFileName, &str)>,
) -> Rc<AliasResolver> {
    let r = Rc::new(AliasResolver {
        to_path,
        host,
        module_resolver,
        root_files,
        symlinks,
        on_failed_ambient_module_lookup,
        resolved_modules: RefCell::new(FxHashMap::default()),
        checker_program: Cell::new(None),
    });
    r
}

/// Go `binder.BindSourceFile(file)` on a file that the registry host parsed
/// for the alias resolver. `current_directory` is the host's.
// PORT: the file is in no program. It is published with no program
// (`program::publish_parsed_files`) and bound into the binder lineage
// (`program::bind_file_outside_program`, Go `BindOnce`).
pub fn bind_alias_resolver_source_file(current_directory: &str, file: Node) {
    crate::program::publish_parsed_files(current_directory);
    crate::program::bind_file_outside_program(file);
}

impl AliasResolver {
    /// Go `checker.NewChecker(aliasResolver, nil)`. The checker's program is
    /// current on this thread while the returned scope lives; keep the scope
    /// as long as the checker is used. `reads` are files that the caller
    /// read with `get_source_file` before the checker (the second pass of
    /// the node_modules index update); the program keeps them live with the
    /// root files.
    // PORT: a checker copies the binder lineage when it is made
    // (`SymbolArena::for_checker`). Go binds a file when `GetSourceFile`
    // reads it, while the checker runs, and the checker reads its symbols at
    // once (checker.go:15531, :15639). Here `get_source_file` binds the file
    // into the lineage, and the checker catches its arena up to the lineage
    // before it reads the file (`program::catch_up_alias_resolver_checker`,
    // at the one checker read site). So, as in Go, a module name resolves
    // (`get_resolved_module`) and a file is read only when the checker asks
    // for it, also inside `NewChecker` (`mergeModuleAugmentation`,
    // checker.go:1458). There is one checker and one pass. The checker gets
    // nil only when the host gives nil (aliasresolver.go:86). A file read on
    // demand does not join the checker's files (Go `c.files`): the host's
    // parse cache key keeps it live until the clone's `dispose`.
    // PORT: Go reads a second-pass root file from the host with no bind
    // (registry.go:1102), but Go's parse cache binds each new parse
    // (project/parsecache.go:80, ts#63952). So a root file is always bound
    // in Go, also a new parse of a file of an ancestor bucket that this
    // clone did not build (`resolveAmbientModuleName`, registry.go:1844).
    // The port's parse cache does not bind (`parsecache::new_parse_cache`),
    // so every root file is bound here. That bind matters only for a new
    // parse: the session keeps one parse per path (`kept_files`,
    // project/autoimport.rs `dispose`), so a later clone usually reuses a
    // parse that an earlier clone bound. Go N' and the port give the same
    // export counts in the registry test
    // `second_pass_reads_a_root_file_of_an_ancestor_bucket_in_a_later_clone`.
    // PORT: Go's `NewChecker` has no context. `ctx` is for
    // `should_stop_build`: a build that the caller drops on cancel stops
    // before the program, and gets `None`. For any other context the result
    // is always `Some`.
    pub fn new_checker(
        self: &Rc<Self>,
        ctx: &Context,
        reads: &[Node],
    ) -> Option<(Rc<RefCell<Checker>>, AliasResolverProgramScope)> {
        // Go: NewChecker reads each root file; a nil file is a nil dereference.
        if self.root_files.iter().any(|file| file.is_nil()) {
            crate::core::go_nil_dereference();
        }
        let current_directory = self.get_current_directory();
        // The registry reads the second-pass root files from its host.
        crate::program::publish_parsed_files(&current_directory);
        let mut files: Vec<Node> = Vec::new();
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        for &file in self.root_files.iter().chain(reads) {
            if file.is_some() && seen.insert(file.file_index()) {
                crate::program::bind_file_outside_program(file);
                files.push(file);
            }
        }
        // PORT: a stop here makes no program shell.
        if should_stop_build(ctx) {
            return None;
        }
        let scope = crate::program::new_alias_resolver_program(
            self.options(),
            &self.root_files,
            &files,
            &current_directory,
            self.use_case_sensitive_file_names(),
            self.clone(),
        );
        self.checker_program.set(Some(scope.program()));
        let checker = ls_program::new_checker_for_version(scope.program());
        Some((Rc::new(RefCell::new(checker)), scope))
    }

    /// Go `binder.BindSourceFile(file)` in `GetSourceFile`.
    // PORT: the file is published and bound into the binder lineage
    // (`bind_alias_resolver_source_file`). A checker that exists catches up
    // before it reads the file (see `new_checker`).
    fn bind_source_file(&self, file: Node) {
        bind_alias_resolver_source_file(self.host.get_current_directory(), file);
    }

    // Go: ls/autoimport/aliasresolver.go:53 BindSourceFiles
    // BindSourceFiles implements checker.Program.
    pub fn bind_source_files(&self) {
        // We will bind as we parse
    }

    // Go: ls/autoimport/aliasresolver.go:58 SourceFiles
    // SourceFiles implements checker.Program.
    pub fn source_files(&self) -> Vec<Node> {
        self.root_files.clone()
    }

    // Go: ls/autoimport/aliasresolver.go:63 Options
    // Options implements checker.Program.
    pub fn options(&self) -> CompilerOptions {
        CompilerOptions {
            no_check: Tristate::True,
            ..Default::default()
        }
    }

    // Go: ls/autoimport/aliasresolver.go:70 GetCurrentDirectory (at 673a5f17d713;
    // ts#64159 renames it BaseDirectory, aliasresolver.go:69)
    // GetCurrentDirectory implements checker.Program.
    // PORT: Go N' returns `moduleResolver.BaseDirectory()`, the current
    // directory of the registry builder's resolution host
    // (`store.options.CurrentDirectory`, project/snapshot.go:669). The host
    // here gives the same directory (project/autoimport.rs).
    pub fn get_current_directory(&self) -> String {
        self.host.get_current_directory().to_string()
    }

    // Go: ls/autoimport/aliasresolver.go:75 UseCaseSensitiveFileNames (at
    // 673a5f17d713; ts#64159 renames it CaseSensitivity, aliasresolver.go:74)
    // UseCaseSensitiveFileNames implements checker.Program.
    pub fn use_case_sensitive_file_names(&self) -> bool {
        self.host.fs().use_case_sensitive_file_names()
    }

    // Go: ls/autoimport/aliasresolver.go:80 GetSourceFile
    // GetSourceFile implements checker.Program.
    pub fn get_source_file(&self, file_name: &str) -> Node {
        self.get_source_file_at(file_name, &(self.to_path)(file_name))
    }

    // Go: ls/autoimport/aliasresolver.go:83 getSourceFile
    fn get_source_file_at(&self, file_name: &str, path: &tspath::Path) -> Node {
        let file = self.host.get_source_file(file_name, path);
        // file may be nil due to symlink/realpath mismatch; see TestAutoImportBuilderFS
        if file.is_nil() {
            return Node::NIL;
        }
        self.bind_source_file(file);
        file
    }

    // Go: ls/autoimport/aliasresolver.go:91 GetDefaultResolutionModeForFile
    // GetDefaultResolutionModeForFile implements checker.Program.
    pub fn get_default_resolution_mode_for_file(&self, file: &dyn HasFileName) -> ResolutionMode {
        ModuleKind::ES_NEXT
    }

    // Go: ls/autoimport/aliasresolver.go:96 GetEmitModuleFormatOfFile
    // GetEmitModuleFormatOfFile implements checker.Program.
    pub fn get_emit_module_format_of_file(&self, source_file: &dyn HasFileName) -> ModuleKind {
        ModuleKind::ES_NEXT
    }

    // Go: ls/autoimport/aliasresolver.go:101 GetEmitSyntaxForUsageLocation
    // GetEmitSyntaxForUsageLocation implements checker.Program.
    pub fn get_emit_syntax_for_usage_location(
        &self,
        source_file: &dyn HasFileName,
        usage_location: Node,
    ) -> ResolutionMode {
        ModuleKind::ES_NEXT
    }

    // Go: ls/autoimport/aliasresolver.go:106 GetImpliedNodeFormatForEmit
    // GetImpliedNodeFormatForEmit implements checker.Program.
    pub fn get_implied_node_format_for_emit(&self, source_file: &dyn HasFileName) -> ModuleKind {
        ModuleKind::ES_NEXT
    }

    // Go: ls/autoimport/aliasresolver.go:111 GetModeForUsageLocation
    // GetModeForUsageLocation implements checker.Program.
    pub fn get_mode_for_usage_location(
        &self,
        file: &dyn HasFileName,
        module_specifier: Node,
    ) -> ResolutionMode {
        ModuleKind::ES_NEXT
    }

    // Go: ls/autoimport/aliasresolver.go:116 GetResolvedModule
    // GetResolvedModule implements checker.Program.
    pub fn get_resolved_module(
        &self,
        current_source_file: &dyn HasFileName,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Arc<ResolvedModule> {
        // Go: r.resolvedModules.LoadOrStore(currentSourceFile.Path(), &collections.SyncMap{})
        let cache = self
            .resolved_modules
            .borrow_mut()
            .entry(current_source_file.path())
            .or_insert_with(|| Rc::new(RefCell::new(FxHashMap::default())))
            .clone();
        let key = module::ModeAwareCacheKey {
            name: module_reference.to_string(),
            mode,
        };
        let cached = cache.borrow().get(&key).cloned();
        if let Some(resolved) = cached {
            return resolved;
        }
        let (resolved, _, _) = self.module_resolver.resolve_module_name(
            module_reference,
            &current_source_file.file_name(),
            mode,
            None,
        );
        // Go: cache.LoadOrStore(key, resolved)
        let resolved = cache.borrow_mut().entry(key).or_insert(resolved).clone();
        if !resolved.is_resolved() && !tspath::path_is_relative(module_reference) {
            (self.on_failed_ambient_module_lookup)(current_source_file, module_reference);
        }
        resolved
    }

    // Go: ls/autoimport/aliasresolver.go:137 GetSourceFileForResolvedModule
    // GetSourceFileForResolvedModule implements checker.Program.
    pub fn get_source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Node {
        self.get_source_file_at(&resolved.resolved_file_name, &resolved.resolved_path)
    }

    // Go: ls/autoimport/aliasresolver.go:142 GetResolvedModules
    // GetResolvedModules implements checker.Program.
    // PORT: the Go nil map is an empty map.
    pub fn get_resolved_modules(
        &self,
    ) -> FxHashMap<tspath::Path, module::ModeAwareCache<Arc<ResolvedModule>>> {
        // only used when producing diagnostics, which hopefully the checker won't do
        FxHashMap::default()
    }

    // ---

    // Go: ls/autoimport/aliasresolver.go:143 GetSymlinkCache
    // GetSymlinkCache implements checker.Program.
    pub fn get_symlink_cache(&self) -> Rc<KnownSymlinks> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:148 GetSourceFileMetaData
    // GetSourceFileMetaData implements checker.Program.
    pub fn get_source_file_meta_data(&self, path: &tspath::Path) -> SourceFileMetaData {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:153 CommonSourceDirectory
    // CommonSourceDirectory implements checker.Program.
    pub fn common_source_directory(&self) -> String {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:158 ContentMapperExtensions
    // ContentMapperExtensions implements checker.Program.
    // PORT: the Go nil slice is an empty `Vec`.
    pub fn content_mapper_extensions(&self) -> Vec<String> {
        Vec::new()
    }

    // Go: ls/autoimport/aliasresolver.go:163 FileExists
    // FileExists implements checker.Program.
    pub fn file_exists(&self, file_name: &str) -> bool {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:168 GetGlobalTypingsCacheLocation
    // GetGlobalTypingsCacheLocation implements checker.Program.
    pub fn get_global_typings_cache_location(&self) -> String {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:173 GetImportHelpersImportSpecifier
    // GetImportHelpersImportSpecifier implements checker.Program.
    pub fn get_import_helpers_import_specifier(&self, path: &tspath::Path) -> Node {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:178 GetJSXRuntimeImportSpecifier
    // GetJSXRuntimeImportSpecifier implements checker.Program.
    pub fn get_jsx_runtime_import_specifier(&self, path: &tspath::Path) -> (String, Node) {
        (String::new(), Node::NIL)
    }

    // Go: ls/autoimport/aliasresolver.go:183 GetNearestAncestorDirectoryWithPackageJson
    // GetNearestAncestorDirectoryWithPackageJson implements checker.Program.
    pub fn get_nearest_ancestor_directory_with_package_json(&self, dirname: &str) -> String {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:188 GetPackageJsonInfo
    // GetPackageJsonInfo implements checker.Program.
    pub fn get_package_json_info(
        &self,
        pkg_json_path: &str,
    ) -> Option<Rc<packagejson::InfoCacheEntry>> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:193 GetProjectReferenceFromOutputDts
    // GetProjectReferenceFromOutputDts implements checker.Program.
    pub fn get_project_reference_from_output_dts(
        &self,
        path: &tspath::Path,
    ) -> Option<Rc<tsoptions::SourceOutputAndProjectReference>> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:198 GetProjectReferenceFromSource
    // GetProjectReferenceFromSource implements checker.Program.
    pub fn get_project_reference_from_source(
        &self,
        path: &tspath::Path,
    ) -> Option<Rc<tsoptions::SourceOutputAndProjectReference>> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:203 GetRedirectForResolution
    // GetRedirectForResolution implements checker.Program.
    pub fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<Rc<tsoptions::ParsedCommandLine>> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:208 GetRedirectTargets
    // GetRedirectTargets implements checker.Program.
    pub fn get_redirect_targets(&self, path: &tspath::Path) -> Vec<String> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:213 GetResolvedModuleFromModuleSpecifier
    // GetResolvedModuleFromModuleSpecifier implements checker.Program.
    pub fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn HasFileName,
        module_specifier: Node,
    ) -> Option<Arc<ResolvedModule>> {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:218 GetSourceOfProjectReferenceIfOutputIncluded
    // GetSourceOfProjectReferenceIfOutputIncluded implements checker.Program.
    pub fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> String {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:223 IsSourceFileDefaultLibrary
    // IsSourceFileDefaultLibrary implements checker.Program.
    pub fn is_source_file_default_library(&self, path: &tspath::Path) -> bool {
        false
    }

    // Go: ls/autoimport/aliasresolver.go:226 IsSourceFileFromExternalLibrary
    // IsSourceFileFromExternalLibrary implements checker.Program.
    // Effect-TS/tsgo patch 018 adds it, because patch 002 adds the method to
    // `checker.Program`.
    // PORT: no port path calls it on an alias resolver; the Effect caller
    // (`rulerunner::run`) never runs on an alias resolver checker.
    pub fn is_source_file_from_external_library(&self, _file: Node) -> bool {
        false
    }

    // Go: ls/autoimport/aliasresolver.go:228 IsSourceFromProjectReference
    // IsSourceFromProjectReference implements checker.Program.
    pub fn is_source_from_project_reference(&self, path: &tspath::Path) -> bool {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:233 SourceFileMayBeEmitted
    // SourceFileMayBeEmitted implements checker.Program.
    pub fn source_file_may_be_emitted(&self, source_file: Node, force_dts_emit: bool) -> bool {
        go_panic("unimplemented".to_string())
    }

    // Go: ls/autoimport/aliasresolver.go:237 GetPackagesMap
    // PORT: the Go nil map is an empty map.
    pub fn get_packages_map(&self) -> FxHashMap<String, bool> {
        FxHashMap::default()
    }
}

// Go: ls/autoimport/aliasresolver.go:241 var _ checker.Program = (*aliasResolver)(nil)
// PORT: the lazy `checker.Program` methods, which the alias resolver
// program calls (see the file header).
impl AliasResolverProgram for AliasResolver {
    fn source_file(&self, file_name: &str) -> Node {
        self.get_source_file(file_name)
    }

    fn source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Node {
        self.get_source_file_for_resolved_module(resolved)
    }

    fn resolved_module(
        &self,
        file: Node,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Arc<ResolvedModule> {
        let info = source_file_info(file);
        let current_source_file = new_has_file_name(&info.file_name, &info.path);
        self.get_resolved_module(&current_source_file, module_reference, mode)
    }
}
