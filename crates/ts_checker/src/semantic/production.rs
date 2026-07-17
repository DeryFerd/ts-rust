//! Production construction boundary for the canonical checker core.
//!
//! This module adopts declaration-complete canonical binder output into one
//! checker-owned semantic store. Construction includes the dependency-closed
//! prefix of typescript-go's `initializeChecker`: ordered global merging,
//! deferred ambient-module collection, UMD globals, global-scope
//! augmentations, the built-in `undefined` conflict rule, intrinsic value
//! links, and eager standard-library type identities. Alias-dependent merging,
//! general checker diagnostics, deferred ambient-module merging, and non-global
//! module augmentations remain explicit typed boundaries.

use std::collections::{BTreeMap, BTreeSet};

use ts_ast::{
    FileId, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalExtractionError, CanonicalNameResolverOptions,
    CanonicalPatternAmbientModule, CanonicalProgramBindings, EscapedName, SemanticStoreId,
    SemanticSymbolId, SymbolFlags, SymbolStore, SymbolTableId,
};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostics, CanonicalEnumSemantics, ClassError,
    ClassMembers, ClassShells,
    CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes, CanonicalModuleResolutionLookup,
    CanonicalModuleResolutionManifest, CanonicalModuleResolutionManifestError,
    CanonicalModuleResolutionManifestInput, CanonicalTypeFormatFlags, CanonicalTypeMapperStore,
    CanonicalUnionPropertyError, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeHostError,
    IntrinsicBootstrapError, IntrinsicBootstrapOptions, RelationUnavailable, ResolvedUnionProperty,
    SignatureId, SourceCheckError, SourceCheckProvenanceError, SourceFileRef, SymbolMergeError,
    TypeDisplayUnavailable, TypeId,
    alias::{CanonicalAliasResolution, CanonicalAliasResolutionError, CanonicalAliasResolver},
    alias_flags::{
        CanonicalSymbolFlagsError, CanonicalSymbolFlagsResolution, CanonicalSymbolFlagsResolver,
    },
    alias_provider::{
        ProductionAliasSourceRegistry, ProductionAliasTargetHost, ProductionAliasTargetHostError,
    },
    classes::{
        execute_nongeneric_class_members, execute_nongeneric_class_shells,
        plan_nongeneric_class, plan_nongeneric_class_members,
    },
    global_types::initialize_global_library_types,
    instantiate::{InstantiationLimits, InstantiationSession},
    module_resolution::validate_module_resolution_manifest,
    name_resolution::{ProductionNameResolverHost, ProductionNameResolverHostError},
    source,
    type_nodes::CanonicalTypeQuery,
};

/// Compiler options consumed by the installed production-construction slice.
///
/// The intrinsic pair controls bootstrap identity. `strict_bind_call_apply`
/// selects the pinned `CallableFunction`/`NewableFunction` globals instead of
/// aliasing both fields to `Function`. `strict_builtin_iterator_return` is
/// retained for declared type-alias construction. `strict_function_types` is
/// retained as immutable context state for signature relation queries.
/// `no_implicit_any` controls diagnostics and evolving inference for
/// unannotated declarations.
/// `no_error_truncation` raises semantic type display to the pinned hard output
/// cutoff.
#[allow(clippy::struct_excessive_bools)] // Flat immutable compiler-option projection.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CanonicalCheckerOptions {
    pub intrinsic: IntrinsicBootstrapOptions,
    pub strict_bind_call_apply: bool,
    pub strict_builtin_iterator_return: bool,
    pub strict_function_types: bool,
    pub no_implicit_any: bool,
    pub no_error_truncation: bool,
    pub name_resolution: CanonicalNameResolverOptions,
}

impl From<IntrinsicBootstrapOptions> for CanonicalCheckerOptions {
    fn from(intrinsic: IntrinsicBootstrapOptions) -> Self {
        Self {
            intrinsic,
            strict_bind_call_apply: false,
            strict_builtin_iterator_return: false,
            strict_function_types: false,
            no_implicit_any: false,
            no_error_truncation: false,
            name_resolution: CanonicalNameResolverOptions::default(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct GlobalMergeCompletion {
    name_resolution: CanonicalNameResolverOptions,
}

impl GlobalMergeCompletion {
    const fn new(name_resolution: CanonicalNameResolverOptions) -> Self {
        Self { name_resolution }
    }

    pub(super) const fn name_resolution(self) -> CanonicalNameResolverOptions {
        self.name_resolution
    }

    #[cfg(test)]
    pub(super) const fn for_test(name_resolution: CanonicalNameResolverOptions) -> Self {
        Self::new(name_resolution)
    }
}

fn diagnostic_owners(
    files: &ProductionAliasSourceRegistry<'_>,
    initiating: SourceFileRef,
    diagnostics: &CanonicalCheckerDiagnostics,
) -> Result<Vec<SourceFileRef>, SourceCheckError> {
    diagnostics
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let Some(node) = diagnostic.node else {
                if let Some(range_override) = diagnostic.range_override {
                    return Err(SourceCheckError::Provenance(
                        SourceCheckProvenanceError::InvalidDiagnosticRange {
                            node: None,
                            range_override,
                        },
                    ));
                }
                return Ok(initiating);
            };
            let snapshot = files.snapshot(node.file).filter(|(arena, bound)| {
                node.is_for(arena.id(), bound.file_id()) && bound.contains(node)
            });
            let Some((arena, _)) = snapshot else {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::InvalidDiagnosticNode(node),
                ));
            };
            let owner = files
                .source_file(node.file)
                .ok_or(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::InvalidDiagnosticNode(node),
                ))?;
            if let Some(range_override) = diagnostic.range_override {
                let valid = arena
                    .get(node.node)
                    .zip(arena.get(owner.node_ref().node))
                    .is_some_and(|(anchor, source)| {
                        range_override.is_valid_for(node, anchor.range, source.range)
                    });
                if !valid {
                    return Err(SourceCheckError::Provenance(
                        SourceCheckProvenanceError::InvalidDiagnosticRange {
                            node: Some(node),
                            range_override,
                        },
                    ));
                }
            }
            Ok(owner)
        })
        .collect()
}

/// A dependency-closed, production-ready canonical checker foundation.
///
/// The context is the sole owner of the binder's canonical symbol graph after
/// it has been adopted by the checker store. AST arenas remain borrowed by
/// exact identity, while their completed [`BoundFile`] side data is owned here.
/// [`Self::file_order`] is authoritative; map iteration must never be used as
/// Program order.
#[derive(Debug)]
pub struct CanonicalCheckerContext<'arena> {
    options: CanonicalCheckerOptions,
    file_order: Vec<FileId>,
    files: ProductionAliasSourceRegistry<'arena>,
    store: CanonicalTypeMapperStore,
    instantiation_session: InstantiationSession,
    globals: SymbolTableId,
    global_types: CanonicalGlobalTypes,
    module_resolutions: CanonicalModuleResolutionManifest,
    diagnostics: CanonicalCheckerDiagnostics,
    source_diagnostic_staging: BTreeMap<SourceFileRef, CanonicalCheckerDiagnostics>,
    pending_ambient_modules: Vec<SemanticSymbolId>,
    pattern_ambient_modules: Vec<CanonicalPatternAmbientModule>,
}

/// Construction or kernel failure from a context-owned production alias query.
///
/// Variants preserve the exact underlying error so callers can distinguish a
/// stale or malformed retained Program from an unavailable target provider and
/// from a symbol-flags invariant failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalAliasQueryError {
    TargetHost(ProductionAliasTargetHostError),
    AliasResolution(CanonicalAliasResolutionError),
    SymbolFlags(CanonicalSymbolFlagsError),
}

impl std::fmt::Display for CanonicalAliasQueryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TargetHost(error) => error.fmt(formatter),
            Self::AliasResolution(error) => error.fmt(formatter),
            Self::SymbolFlags(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for CanonicalAliasQueryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TargetHost(error) => Some(error),
            Self::AliasResolution(error) => Some(error),
            Self::SymbolFlags(error) => Some(error),
        }
    }
}

impl From<ProductionAliasTargetHostError> for CanonicalAliasQueryError {
    fn from(error: ProductionAliasTargetHostError) -> Self {
        Self::TargetHost(error)
    }
}

impl From<CanonicalAliasResolutionError> for CanonicalAliasQueryError {
    fn from(error: CanonicalAliasResolutionError) -> Self {
        Self::AliasResolution(error)
    }
}

impl From<CanonicalSymbolFlagsError> for CanonicalAliasQueryError {
    fn from(error: CanonicalSymbolFlagsError) -> Self {
        Self::SymbolFlags(error)
    }
}

impl<'arena> CanonicalCheckerContext<'arena> {
    /// Atomically adopts completed binder state, registers every source root
    /// in the supplied Program order, and initializes intrinsic checker state.
    ///
    /// Binder extraction, exact Program correspondence, and source-root
    /// validation run before a checker store is created. Full-tree source
    /// registration, bootstrap, and global initialization then write only to a
    /// local store, which is dropped on failure, so callers can never observe a
    /// partial context.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalCheckerContextError`] when declaration extraction,
    /// the exact file/arena correspondence, source-root provenance, source
    /// registration, intrinsic bootstrap, or the supported global-
    /// initialization prefix fails.
    pub fn new(
        bindings: CanonicalProgramBindings,
        ordered_arenas: Vec<(FileId, &'arena NodeArena)>,
        options: impl Into<CanonicalCheckerOptions>,
    ) -> Result<Self, CanonicalCheckerContextError> {
        Self::new_internal(bindings, ordered_arenas, options.into(), None)
    }

    /// Constructs a context with an explicitly available, one-shot module-
    /// resolution manifest.
    ///
    /// An empty `module_resolutions` value remains observably different from
    /// [`Self::new`]: lookups report an available provider with an absent entry
    /// instead of an unavailable capability. Every entry is validated against
    /// the exact retained binder/arena snapshot before checker state exists.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalCheckerContextError::ModuleResolutions`] for a
    /// foreign, stale, duplicate, malformed, or invalid-target manifest entry,
    /// in addition to the errors documented by [`Self::new`].
    pub fn new_with_module_resolutions(
        bindings: CanonicalProgramBindings,
        ordered_arenas: Vec<(FileId, &'arena NodeArena)>,
        options: impl Into<CanonicalCheckerOptions>,
        module_resolutions: CanonicalModuleResolutionManifestInput,
    ) -> Result<Self, CanonicalCheckerContextError> {
        Self::new_internal(
            bindings,
            ordered_arenas,
            options.into(),
            Some(module_resolutions),
        )
    }

    fn new_internal(
        bindings: CanonicalProgramBindings,
        ordered_arenas: Vec<(FileId, &'arena NodeArena)>,
        options: CanonicalCheckerOptions,
        module_resolutions: Option<CanonicalModuleResolutionManifestInput>,
    ) -> Result<Self, CanonicalCheckerContextError> {
        let (symbols, mut bound_files) = bindings
            .try_into_parts()
            .map_err(CanonicalCheckerContextError::Extraction)?;

        preflight_program(&symbols, &bound_files, &ordered_arenas)?;

        let module_resolutions = match module_resolutions {
            Some(input) => validate_module_resolution_manifest(
                input,
                &symbols,
                ordered_arenas.iter().map(|(file, arena)| {
                    (
                        *file,
                        *arena,
                        bound_files
                            .get(file)
                            .expect("preflight established exact Program correspondence"),
                    )
                }),
            )
            .map_err(CanonicalCheckerContextError::ModuleResolutions)?,
            None => CanonicalModuleResolutionManifest::unavailable(),
        };

        let file_order = ordered_arenas
            .iter()
            .map(|(file, _)| *file)
            .collect::<Vec<_>>();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        let mut registered = Vec::with_capacity(ordered_arenas.len());
        for (file, arena) in ordered_arenas {
            let Some(bound) = bound_files.get(&file) else {
                return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
            };
            let source = bound.source_file();
            let Some(source_file) = store.register_source_file(arena, source.node, file) else {
                return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
            };
            registered.push((file, arena, source_file));
        }

        store
            .initialize_intrinsic_bootstrap(options.intrinsic)
            .map_err(CanonicalCheckerContextError::Bootstrap)?;
        if let Err(established_strict_builtin_iterator_return) =
            store.claim_strict_builtin_iterator_return(options.strict_builtin_iterator_return)
        {
            return Err(
                CanonicalCheckerContextError::StrictBuiltinIteratorReturnClaim {
                    established_strict_builtin_iterator_return,
                    requested_strict_builtin_iterator_return: options
                        .strict_builtin_iterator_return,
                },
            );
        }
        if let Err(established_strict_function_types) =
            store.claim_strict_function_types(options.strict_function_types)
        {
            return Err(CanonicalCheckerContextError::StrictFunctionTypesClaim {
                established_strict_function_types,
                requested_strict_function_types: options.strict_function_types,
            });
        }

        let mut retained_files = Vec::with_capacity(registered.len());
        for (file, arena, source_file) in registered {
            let Some(bound) = bound_files.remove(&file) else {
                return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
            };
            retained_files.push((arena, bound, source_file));
        }
        if let Some(file) = bound_files.keys().next().copied() {
            return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
        }
        let files = ProductionAliasSourceRegistry::new(&store, retained_files)
            .map_err(CanonicalCheckerContextError::AliasTargetHost)?;

        let initialized = initialize_globals(
            &mut store,
            &file_order,
            &files,
            options.strict_bind_call_apply,
            options.name_resolution,
        )
        .map_err(CanonicalCheckerContextError::GlobalInitialization)?;
        let error_type = store
            .intrinsic_bootstrap()
            .expect("successful checker bootstrap remains installed")
            .error_type;
        let instantiation_session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits::default(),
            error_type,
        )
        .expect("the bootstrap error type is a valid recovery identity");

        Ok(Self {
            options,
            file_order,
            files,
            store,
            instantiation_session,
            globals: initialized.globals,
            global_types: initialized.global_types,
            module_resolutions,
            diagnostics: CanonicalCheckerDiagnostics::default(),
            source_diagnostic_staging: BTreeMap::new(),
            pending_ambient_modules: initialized.pending_ambient_modules,
            pattern_ambient_modules: initialized.pattern_ambient_modules,
        })
    }

    /// The complete checker options retained for later semantic queries.
    #[must_use]
    pub const fn options(&self) -> CanonicalCheckerOptions {
        self.options
    }

    /// The exact caller-supplied Program order used for source registration.
    #[must_use]
    pub fn file_order(&self) -> &[FileId] {
        &self.file_order
    }

    /// Returns the exact AST arena and completed binder side data for `file`.
    #[must_use]
    pub fn file(&self, file: FileId) -> Option<(&'arena NodeArena, &BoundFile)> {
        self.files.snapshot(file)
    }

    /// Returns the checker-validated source-root identity for `file`.
    #[must_use]
    pub fn source_file(&self, file: FileId) -> Option<SourceFileRef> {
        self.files.source_file(file)
    }

    /// The canonical checker store, preserving the binder symbol-store brand.
    #[must_use]
    pub const fn store(&self) -> &CanonicalTypeMapperStore {
        &self.store
    }

    /// Resolves one property from an exact two-constituent union.
    ///
    /// The production adapter accepts either two already-resolved, raw
    /// alias-free property objects or two source-declared type literals. A
    /// declared union retains its canonical named-alias identity and every
    /// selected source property's declaration/owner provenance. Partial
    /// properties are cached internally and filtered from the public result.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalUnionPropertyError`] for a foreign or malformed
    /// identity, an unsupported constituent/mixed mode, or a member/type
    /// family outside this exact leaf.
    pub fn get_union_property(
        &mut self,
        union: TypeId,
        name: &str,
    ) -> Result<Option<ResolvedUnionProperty>, CanonicalUnionPropertyError> {
        self.store
            .resolved_union_property(union, name)
            .map_err(|error| CanonicalUnionPropertyError::from_internal(union, error))
    }

    #[cfg(test)]
    pub(super) fn store_mut_for_test(&mut self) -> &mut CanonicalTypeMapperStore {
        &mut self.store
    }

    /// Formats one context-owned type through the dependency-closed canonical
    /// semantic formatter. The retained `no_error_truncation` compiler option
    /// is applied in addition to the ordinary pinned `TypeToString` flags.
    ///
    /// # Errors
    ///
    /// Returns [`TypeDisplayUnavailable`] when the type is foreign, malformed,
    /// or requires a display family not installed in the current checker cut.
    pub fn type_to_string(&self, type_id: TypeId) -> Result<String, TypeDisplayUnavailable> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::type_to_string_with_host_global_types_and_flags(
            &self.store,
            &host,
            &self.global_types,
            type_id,
            self.type_format_flags(CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT),
        )
    }

    /// Flag-aware form of [`Self::type_to_string`] for the exact format flags
    /// observable in the installed primitive/literal/structural prefix. The
    /// retained `no_error_truncation` compiler option takes effect even when
    /// the caller does not supply [`CanonicalTypeFormatFlags::NO_TRUNCATION`].
    ///
    /// # Errors
    ///
    /// Returns [`TypeDisplayUnavailable`] under the same conditions as the
    /// default query.
    pub fn type_to_string_with_flags(
        &self,
        type_id: TypeId,
        flags: CanonicalTypeFormatFlags,
    ) -> Result<String, TypeDisplayUnavailable> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::type_to_string_with_host_global_types_and_flags(
            &self.store,
            &host,
            &self.global_types,
            type_id,
            self.type_format_flags(flags),
        )
    }

    /// Computes exact TS2322 source and target display arguments without
    /// mutating checker state. The retained `no_error_truncation` compiler
    /// option is applied to both display arguments.
    ///
    /// # Errors
    ///
    /// Returns [`TypeDisplayUnavailable`] when either type or its pinned
    /// relation-diagnostic representation is outside the installed prefix.
    pub fn get_type_names_for_assignability_error(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<AssignabilityErrorDisplay, TypeDisplayUnavailable> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::get_type_names_for_assignability_error_with_host_global_types_and_flags(
            &self.store,
            &host,
            &self.global_types,
            source,
            target,
            self.type_format_flags(CanonicalTypeFormatFlags::NONE),
        )
    }

    /// Tests assignability using the context's authoritative global identities
    /// and immutable `strictFunctionTypes` option.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when either type is malformed or the
    /// relation requires a semantic family outside the installed checker cut.
    pub fn is_type_assignable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let Self {
            options,
            store,
            global_types,
            ..
        } = self;
        store.is_type_assignable_to_with_global_types_and_strict_function_types(
            source,
            target,
            global_types,
            options.strict_function_types,
        )
    }

    fn type_format_flags(&self, mut flags: CanonicalTypeFormatFlags) -> CanonicalTypeFormatFlags {
        if self.options.no_error_truncation {
            flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
        }
        flags
    }

    /// The bootstrap-owned global symbol table after the supported
    /// `initializeChecker` prefix completed.
    #[must_use]
    pub const fn globals(&self) -> SymbolTableId {
        self.globals
    }

    /// Eager standard-library identities and global-type fallback diagnostics.
    #[must_use]
    pub const fn global_types(&self) -> &CanonicalGlobalTypes {
        &self.global_types
    }

    /// The immutable, checker-owned module-resolution capability.
    #[must_use]
    pub const fn module_resolutions(&self) -> &CanonicalModuleResolutionManifest {
        &self.module_resolutions
    }

    /// Looks up one exact module-specifier identity.
    #[must_use]
    pub fn module_resolution(&self, specifier: NodeRef) -> CanonicalModuleResolutionLookup {
        self.module_resolutions.lookup(specifier)
    }

    /// General checker diagnostics in raw issuance order.
    #[must_use]
    pub const fn diagnostics(&self) -> &CanonicalCheckerDiagnostics {
        &self.diagnostics
    }

    /// Resolves a bound alias through the retained production sources and
    /// immutable module-resolution manifest.
    ///
    /// The returned events are the exact one-time cycle events produced by the
    /// alias kernel. This slice does not issue diagnostics for them because the
    /// pinned diagnostic callback is not dependency-closed; callers retain
    /// ownership of event-to-diagnostic conversion. The query starts from an
    /// already-bound symbol and performs no alias-aware lexical name lookup.
    ///
    /// # Errors
    ///
    /// Returns the exact production-host construction or alias-kernel error.
    /// Provider failures remain retryable and do not publish an alias target.
    pub fn resolve_alias(
        &mut self,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalAliasResolution, CanonicalAliasQueryError> {
        let Self {
            files,
            store,
            module_resolutions,
            ..
        } = self;
        let mut host = ProductionAliasTargetHost::from_registry(store, files, module_resolutions)?;
        CanonicalAliasResolver::new(store, &mut host)
            .resolve_alias(alias)
            .map_err(Into::into)
    }

    /// Gets the pinned combined meanings of a bound symbol through production
    /// alias resolution.
    ///
    /// Cycle events are returned unchanged in
    /// [`CanonicalSymbolFlagsResolution::events`]. As with
    /// [`Self::resolve_alias`], exact diagnostic issuance and alias-aware
    /// lexical name lookup are outside this dependency-closed slice.
    ///
    /// # Errors
    ///
    /// Returns the exact production-host construction or symbol-flags kernel
    /// error, including any nested alias-resolution failure.
    pub fn get_symbol_flags(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<CanonicalSymbolFlagsResolution, CanonicalAliasQueryError> {
        let Self {
            files,
            store,
            module_resolutions,
            ..
        } = self;
        let mut host = ProductionAliasTargetHost::from_registry(store, files, module_resolutions)?;
        CanonicalSymbolFlagsResolver::new(store, &mut host)
            .get_symbol_flags(symbol)
            .map_err(Into::into)
    }

    /// Resolves one declared type through the context-owned query session.
    ///
    /// # Errors
    ///
    /// Returns a typed host, option, provenance, or unavailable error when the
    /// retained Program cannot resolve the symbol in the installed cut.
    pub fn get_declared_type_of_symbol(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Self {
            options,
            files,
            store,
            instantiation_session,
            diagnostics,
            global_types,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map_err(DeclaredTypeError::from)?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            global_types,
            *options,
            instantiation_session,
            diagnostics,
        )?
        .get_declared_type_of_symbol(symbol)
    }

    /// Installs or validates the exact instance and static identities for one
    /// local nongeneric class declaration.
    ///
    /// This is the shell stage only: annotated members, constructor
    /// signatures, heritage, and executable class checking remain separate
    /// typed boundaries.
    ///
    /// # Errors
    ///
    /// Returns a typed syntax, binder, declared-type, capacity, or poisoned
    /// cache error without publishing a partial class value graph.
    pub fn get_nongeneric_class_shells(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<ClassShells, ClassError> {
        let Self {
            options,
            files,
            store,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map_err(DeclaredTypeError::from)?;
        let plan = plan_nongeneric_class(store, &host, symbol)?;
        execute_nongeneric_class_shells(store, &host, &plan)
    }

    /// Materializes exact primitive annotated members and the default
    /// construct signature for one local nongeneric class declaration.
    ///
    /// The admitted class has no heritage, executable members, initializers,
    /// or non-keyword property annotations. The operation preflights and
    /// reserves the entire graph before publishing a cold shell.
    ///
    /// # Errors
    ///
    /// Returns a typed syntax, binder, capacity, declared-type, or poisoned
    /// cache error without publishing a partial class member graph.
    pub fn get_nongeneric_class_members(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<ClassMembers, ClassError> {
        let Self {
            options,
            files,
            store,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map_err(DeclaredTypeError::from)?;
        let plan = plan_nongeneric_class_members(store, &host, symbol)?;
        execute_nongeneric_class_members(store, &host, &plan)
    }

    /// Publishes or validates the exact type/value/member identities for one
    /// context-owned top-level literal enum.
    ///
    /// # Errors
    ///
    /// Returns a typed host, provenance, unsupported-syntax, or poisoned-cache
    /// error without partially publishing an enum graph.
    pub fn get_enum_semantics(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<CanonicalEnumSemantics, DeclaredTypeError> {
        let Self {
            options,
            files,
            store,
            instantiation_session,
            diagnostics,
            global_types,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            global_types,
            *options,
            instantiation_session,
            diagnostics,
        )?
        .get_enum_semantics(symbol)
    }

    /// Resolves one type node through the context-owned query session.
    ///
    /// # Errors
    ///
    /// Returns a typed host, option, provenance, or unavailable error when the
    /// retained Program cannot resolve the node in the installed cut.
    pub fn get_type_from_type_node(&mut self, node: NodeRef) -> Result<TypeId, DeclaredTypeError> {
        let Self {
            options,
            files,
            store,
            instantiation_session,
            diagnostics,
            global_types,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            global_types,
            *options,
            instantiation_session,
            diagnostics,
        )?
        .get_type_from_type_node(node)
    }

    /// Resolves the lazy return type of one exact annotated function-type
    /// signature through the context-owned query session.
    ///
    /// # Errors
    ///
    /// Returns a typed host, provenance, cache, or unavailable error when the
    /// signature is foreign or is outside the installed function-type cut.
    pub fn get_return_type_of_signature(
        &mut self,
        signature: SignatureId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let Self {
            options,
            files,
            store,
            instantiation_session,
            diagnostics,
            global_types,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            global_types,
            *options,
            instantiation_session,
            diagnostics,
        )?
        .get_return_type_of_signature(signature)
    }

    /// Checks the supported statements in one retained source file.
    ///
    /// The complete source is validated before semantic execution. Checker
    /// diagnostics and the source's `type_checked` marker are committed only
    /// after every supported statement completes, so a typed failure can be
    /// repaired and retried without exposing a partial source result. Safe
    /// canonical memo caches may survive a rejected attempt; diagnostics tied
    /// to those caches stay in context-private retry staging until success.
    ///
    /// # Errors
    ///
    /// Returns [`SourceCheckError`] for a foreign file, stale or malformed AST,
    /// unsupported source syntax, unavailable declared type or relation, type
    /// display boundary, or malformed literal cache.
    pub fn check_source_file(&mut self, file: FileId) -> Result<(), SourceCheckError> {
        let Self {
            options,
            files,
            store,
            instantiation_session,
            diagnostics,
            source_diagnostic_staging,
            global_types,
            module_resolutions,
            ..
        } = self;
        let (arena, bound) = files.snapshot(file).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingFile(file),
        ))?;
        let source_file = files.source_file(file).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingFile(file),
        ))?;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map_err(DeclaredTypeError::from)?;
        let mut alias_host =
            ProductionAliasTargetHost::from_registry(store, files, module_resolutions)
                .map_err(|_| SourceCheckError::Import(source_file.node_ref()))?;
        let mut staged = source_diagnostic_staging
            .remove(&source_file)
            .unwrap_or_default();
        let result = source::check_source_file(
            arena,
            bound,
            source_file,
            &host,
            &mut alias_host,
            global_types,
            store,
            *options,
            instantiation_session,
            &mut staged,
        );
        let owners = match diagnostic_owners(files, source_file, &staged) {
            Ok(owners) => owners,
            Err(error) => {
                source::merge_retry_diagnostics(
                    source_diagnostic_staging.entry(source_file).or_default(),
                    staged,
                );
                return Err(error);
            }
        };
        let result = result.and_then(|()| source::publish_type_checked(store, source_file));
        let mut partitioned = BTreeMap::<SourceFileRef, CanonicalCheckerDiagnostics>::new();
        for (owner, diagnostic) in owners.into_iter().zip(staged.into_vec()) {
            source::merge_retry_diagnostic(partitioned.entry(owner).or_default(), diagnostic);
        }
        for (owner, retained) in partitioned {
            let checked = store
                .source_file_links(owner)
                .is_some_and(|links| links.type_checked);
            if checked {
                if let Some(previous) = source_diagnostic_staging.remove(&owner) {
                    source::merge_retry_diagnostics(diagnostics, previous);
                }
                source::merge_retry_diagnostics(diagnostics, retained);
            } else {
                source::merge_retry_diagnostics(
                    source_diagnostic_staging.entry(owner).or_default(),
                    retained,
                );
            }
        }
        result
    }

    /// Forces one already-retained source through the complete checker
    /// preflight and execution path again.
    ///
    /// This is the incremental validation boundary for callers that need to
    /// verify warm semantic caches rather than accepting the source's
    /// `type_checked` fast path. Existing canonical identities are retained;
    /// malformed or stale caches fail through [`SourceCheckError`].
    ///
    /// # Errors
    ///
    /// Returns the same typed failures as [`Self::check_source_file`], or a
    /// provenance error when `file` is not retained by this context.
    pub fn recheck_source_file(&mut self, file: FileId) -> Result<(), SourceCheckError> {
        let source = self.source_file(file).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingFile(file),
        ))?;
        let mut links = self
            .store
            .source_file_links(source)
            .cloned()
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::StoreSourceMismatch(source),
            ))?;
        links.type_checked = false;
        if !self.store.set_source_file_links(source, links) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::StoreSourceMismatch(source),
            ));
        }
        self.check_source_file(file)
    }

    /// Quoted ambient-module symbols deferred until global library types exist.
    /// Entries follow Program order and escaped-byte name order within a file.
    #[must_use]
    pub fn pending_ambient_modules(&self) -> &[SemanticSymbolId] {
        &self.pending_ambient_modules
    }

    /// Wildcard ambient modules retained in Program/declaration order.
    #[must_use]
    pub fn pattern_ambient_modules(&self) -> &[CanonicalPatternAmbientModule] {
        &self.pattern_ambient_modules
    }

    /// Creates the canonical checker callback host only after this context has
    /// completed ordered global initialization.
    ///
    /// The host follows one merged-symbol redirect for declaration and table
    /// lookups. Alias-target resolution and diagnostic callback ownership are
    /// still explicit later checker capabilities.
    ///
    /// # Errors
    ///
    /// Returns a typed invariant error if the retained Program sources no
    /// longer match the checker-owned semantic graph.
    pub fn name_resolver_host(
        &self,
        options: CanonicalNameResolverOptions,
    ) -> Result<ProductionNameResolverHost<'_, '_>, ProductionNameResolverHostError> {
        ProductionNameResolverHost::from_registry(&self.store, &self.files, options)
    }

    /// The brand shared by adopted binder symbols and checker-owned records.
    #[must_use]
    pub fn id(&self) -> SemanticStoreId {
        self.store.id()
    }
}

#[derive(Debug)]
struct GlobalInitialization {
    globals: SymbolTableId,
    global_types: CanonicalGlobalTypes,
    pending_ambient_modules: Vec<SemanticSymbolId>,
    pattern_ambient_modules: Vec<CanonicalPatternAmbientModule>,
}

#[allow(clippy::too_many_lines)] // Preserves pinned initializeChecker phase order visibly.
fn initialize_globals(
    store: &mut CanonicalTypeMapperStore,
    file_order: &[FileId],
    files: &ProductionAliasSourceRegistry<'_>,
    strict_bind_call_apply: bool,
    name_resolution_options: CanonicalNameResolverOptions,
) -> Result<GlobalInitialization, CanonicalGlobalInitializationError> {
    let (globals, undefined_symbol) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| (bootstrap.globals, bootstrap.undefined_symbol))
        .ok_or(CanonicalGlobalInitializationError::MissingBootstrap)?;
    let mut pending_ambient_modules = Vec::new();
    let mut pattern_ambient_modules = Vec::new();

    // Preserve the explicit Program order. Every symbol-table pass below
    // sorts by escaped bytes because the canonical table intentionally uses a
    // hash map and must never become an implicit source of nondeterminism.
    for &file in file_order {
        let (_, bound) = files
            .snapshot(file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        let facts = bound.source_facts().ok_or(
            CanonicalGlobalInitializationError::MissingSourceFileFacts(file),
        )?;

        if !facts.is_external_or_common_js_module()
            && let Some(locals) = bound.locals(bound.source_file())
        {
            if let Some(global_this) = table_symbol(store, file, locals, "globalThis")? {
                let record = store.symbol(global_this).ok_or(
                    CanonicalGlobalInitializationError::InvalidSymbol(global_this),
                )?;
                if let Some(declaration) = record
                    .declarations()
                    .and_then(|declarations| declarations.first())
                    .copied()
                {
                    return Err(
                        CanonicalGlobalInitializationError::ScriptGlobalThisDeclaration {
                            file,
                            declaration,
                        },
                    );
                }
            }

            for (name, symbol) in ordered_table_entries(store, file, locals)? {
                let flags = store
                    .symbol(symbol)
                    .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(symbol))?
                    .flags();
                if flags.intersects(SymbolFlags::MODULE)
                    && is_ambient_module_symbol_name(name.as_bytes())
                {
                    pending_ambient_modules.push(symbol);
                } else {
                    store.merge_global_symbol(globals, symbol)?;
                }
            }
        }

        pattern_ambient_modules.extend_from_slice(bound.pattern_ambient_modules());

        if let Some(global_exports) = bound.global_exports() {
            if bound.symbol(bound.source_file()).is_none() {
                return Err(CanonicalGlobalInitializationError::MissingSourceFileSymbol(
                    file,
                ));
            }
            for (name, symbol) in ordered_table_entries(store, file, global_exports)? {
                let present = store
                    .symbol_table(globals)
                    .ok_or(CanonicalGlobalInitializationError::InvalidTable {
                        file,
                        table: globals,
                    })?
                    .get(name.as_ref())
                    .is_some();
                if !present {
                    match store.insert_symbol(globals, name, symbol) {
                        Some(None) => {}
                        Some(Some(_)) => {
                            return Err(
                                CanonicalGlobalInitializationError::UnexpectedUmdCollision {
                                    file,
                                    symbol,
                                },
                            );
                        }
                        None => {
                            return Err(CanonicalGlobalInitializationError::InvalidUmdInsertion {
                                file,
                                symbol,
                            });
                        }
                    }
                }
            }
        }
    }

    // Global-scope augmentations run only after every ordinary global and UMD
    // export is indexed, and before the built-in `undefined` rule.
    for &file in file_order {
        let (arena, bound) = files
            .snapshot(file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        for augmentation in bound.module_augmentations() {
            let augmentation_name = augmentation.name();
            let module = validate_augmentation_name(arena, bound, file, augmentation_name)?;
            let Some(NodeData::ModuleDeclaration(module_data)) =
                arena.get(module.node).map(|node| &node.data)
            else {
                return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
                    augmentation_name,
                ));
            };
            if module_data.keyword != SyntaxKind::GlobalKeyword {
                continue;
            }
            let symbol = bound
                .symbol(module)
                .ok_or(CanonicalGlobalInitializationError::MissingAugmentationSymbol(module))?;
            let record = store
                .symbol(symbol)
                .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(symbol))?;
            let Some(first_declaration) = record
                .declarations()
                .and_then(|declarations| declarations.first())
                .copied()
            else {
                return Err(
                    CanonicalGlobalInitializationError::MissingAugmentationDeclaration(symbol),
                );
            };
            if first_declaration != module {
                continue;
            }
            if let Some(exports) = record.exports() {
                store.merge_symbol_table(globals, exports, false, None)?;
            }
        }
    }

    add_undefined_to_globals(store, files, globals, undefined_symbol)?;
    let global_merge_completion = GlobalMergeCompletion::new(name_resolution_options);

    let declared_host = DeclaredTypeHost::from_registry(store, files, global_merge_completion)?;
    let global_types =
        initialize_global_library_types(store, &declared_host, globals, strict_bind_call_apply)?;

    Ok(GlobalInitialization {
        globals,
        global_types,
        pending_ambient_modules,
        pattern_ambient_modules,
    })
}

fn table_symbol(
    store: &CanonicalTypeMapperStore,
    file: FileId,
    table: SymbolTableId,
    name: &str,
) -> Result<Option<SemanticSymbolId>, CanonicalGlobalInitializationError> {
    Ok(store
        .symbol_table(table)
        .ok_or(CanonicalGlobalInitializationError::InvalidTable { file, table })?
        .get_source(name))
}

fn ordered_table_entries(
    store: &CanonicalTypeMapperStore,
    file: FileId,
    table: SymbolTableId,
) -> Result<Vec<(EscapedName, SemanticSymbolId)>, CanonicalGlobalInitializationError> {
    let mut entries = store
        .symbol_table(table)
        .ok_or(CanonicalGlobalInitializationError::InvalidTable { file, table })?
        .iter()
        .map(|(name, symbol)| (name.to_owned(), symbol))
        .collect::<Vec<_>>();
    entries.sort_unstable_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
    Ok(entries)
}

fn is_ambient_module_symbol_name(name: &[u8]) -> bool {
    name.len() >= 2 && name.first() == Some(&b'"') && name.last() == Some(&b'"')
}

fn validate_augmentation_name(
    arena: &NodeArena,
    bound: &BoundFile,
    file: FileId,
    name: NodeRef,
) -> Result<NodeRef, CanonicalGlobalInitializationError> {
    if !name.is_for(arena.id(), file) || !bound.contains(name) {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    }
    let Some(name_node) = arena.get(name.node) else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    let Some(module_id) = name_node.parent else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    let module = NodeRef::new(arena.id(), file, module_id);
    let Some(NodeData::ModuleDeclaration(module_data)) =
        arena.get(module_id).map(|node| &node.data)
    else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    if module_data.name != name.node || !bound.contains(module) {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    }
    Ok(module)
}

fn add_undefined_to_globals(
    store: &mut CanonicalTypeMapperStore,
    files: &ProductionAliasSourceRegistry<'_>,
    globals: SymbolTableId,
    undefined_symbol: SemanticSymbolId,
) -> Result<(), CanonicalGlobalInitializationError> {
    let existing = store
        .symbol_table(globals)
        .ok_or(CanonicalGlobalInitializationError::InvalidGlobals(globals))?
        .get_source("undefined");
    if let Some(existing) = existing {
        let record = store
            .symbol(existing)
            .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(existing))?;
        if let Some(declarations) = record.declarations() {
            for &declaration in declarations {
                if !is_type_declaration(files, declaration)? {
                    return Err(
                        CanonicalGlobalInitializationError::UndefinedValueDeclaration(declaration),
                    );
                }
            }
        }
        return Ok(());
    }

    match store.insert_symbol(globals, EscapedName::source("undefined"), undefined_symbol) {
        Some(None) => Ok(()),
        Some(Some(_)) => Err(CanonicalGlobalInitializationError::UnexpectedUndefinedCollision),
        None => Err(
            CanonicalGlobalInitializationError::InvalidUndefinedInsertion {
                globals,
                undefined_symbol,
            },
        ),
    }
}

fn is_type_declaration(
    files: &ProductionAliasSourceRegistry<'_>,
    declaration: NodeRef,
) -> Result<bool, CanonicalGlobalInitializationError> {
    let (arena, bound) = files
        .snapshot(declaration.file)
        .ok_or(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration))?;
    if !declaration.is_for(arena.id(), declaration.file) || !bound.contains(declaration) {
        return Err(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration));
    }
    let node = arena
        .get(declaration.node)
        .ok_or(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration))?;
    match node.kind {
        SyntaxKind::TypeParameter
        | SyntaxKind::ClassDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::JsTypeAliasDeclaration
        | SyntaxKind::EnumDeclaration => Ok(true),
        SyntaxKind::ImportClause => {
            let NodeData::ImportClause(clause) = &node.data else {
                return Err(
                    CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration),
                );
            };
            Ok(clause.phase_modifier == Some(SyntaxKind::TypeKeyword))
        }
        SyntaxKind::ImportSpecifier | SyntaxKind::ExportSpecifier => {
            let Some(parent) = node.parent.and_then(|parent| arena.get(parent)) else {
                return Err(
                    CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration),
                );
            };
            let Some(container) = parent.parent.and_then(|parent| arena.get(parent)) else {
                return Err(
                    CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration),
                );
            };
            match &container.data {
                NodeData::ImportClause(clause) => {
                    Ok(clause.phase_modifier == Some(SyntaxKind::TypeKeyword))
                }
                NodeData::ExportDeclaration(export) => Ok(export.is_type_only),
                _ => Err(
                    CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration),
                ),
            }
        }
        _ => Ok(false),
    }
}

fn preflight_program(
    symbols: &SymbolStore,
    bound_files: &BTreeMap<FileId, BoundFile>,
    ordered_arenas: &[(FileId, &NodeArena)],
) -> Result<(), CanonicalCheckerContextError> {
    let mut seen_files = BTreeSet::new();
    let mut seen_arenas = BTreeMap::new();

    // This entire pass is checker-mutation-free. Keep it that way: it is the
    // atomicity boundary between binder ownership and checker state.
    for &(file, arena) in ordered_arenas {
        if !seen_files.insert(file) {
            return Err(CanonicalCheckerContextError::DuplicateFileInOrder(file));
        }
        if let Some(first_file) = seen_arenas.insert(arena.id(), file) {
            return Err(CanonicalCheckerContextError::DuplicateArenaInOrder {
                arena: arena.id(),
                first_file,
                second_file: file,
            });
        }

        let Some(bound) = bound_files.get(&file) else {
            return Err(CanonicalCheckerContextError::ExtraOrderedFile(file));
        };
        if bound.node_arena_id() != arena.id() {
            return Err(CanonicalCheckerContextError::ArenaMismatch {
                file,
                expected: bound.node_arena_id(),
                actual: arena.id(),
            });
        }
        if bound.source_facts().is_none() {
            return Err(CanonicalCheckerContextError::MissingSourceFileFacts(file));
        }

        let source = bound.source_file();
        if !source.is_for(arena.id(), file) {
            return Err(CanonicalCheckerContextError::SourceFileProvenance { file, source });
        }
        let Some(root) = arena.get(source.node) else {
            return Err(CanonicalCheckerContextError::MissingSourceFileRoot(source));
        };
        if root.kind != SyntaxKind::SourceFile || !matches!(root.data, NodeData::SourceFile(_)) {
            return Err(CanonicalCheckerContextError::InvalidSourceFileRoot {
                source,
                kind: root.kind,
            });
        }
        if let Some(parent) = root.parent {
            return Err(CanonicalCheckerContextError::SourceFileHasParent { source, parent });
        }
        if !bound.contains(source) {
            return Err(CanonicalCheckerContextError::UnboundSourceFile(source));
        }

        // Binder traversal has intentional declaration-hoisting order, so the
        // production invariant is exact set equality rather than sequence
        // equality with a generic root walk.
        let bound_nodes = bound
            .traversal_order()
            .map(|node| node.node)
            .collect::<BTreeSet<_>>();
        let reachable = root_reachable_nodes(arena, source.node);
        if let Some(node) = bound
            .traversal_order()
            .find(|node| !reachable.contains(&node.node))
        {
            return Err(CanonicalCheckerContextError::BoundNodeNowUnreachable(node));
        }
        if let Some(node) = reachable
            .iter()
            .copied()
            .map(|node| NodeRef::new(arena.id(), file, node))
            .find(|node| !bound_nodes.contains(&node.node))
        {
            return Err(CanonicalCheckerContextError::NewlyReachableUnboundNode(
                node,
            ));
        }
        if bound.node_arena_revision() != arena.revision() {
            return Err(CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                expected: bound.node_arena_revision(),
                actual: arena.revision(),
            });
        }

        if let Some(unowned) = arena
            .iter()
            .map(|(node, _)| NodeRef::new(arena.id(), file, node))
            .find(|node| bound.contains(*node) && !symbols.contains_node_ref(*node))
        {
            return Err(CanonicalCheckerContextError::UnownedBoundNode(unowned));
        }
    }

    if let Some(missing) = bound_files
        .keys()
        .copied()
        .find(|file| !seen_files.contains(file))
    {
        return Err(CanonicalCheckerContextError::MissingOrderedFile(missing));
    }
    Ok(())
}

fn root_reachable_nodes(arena: &NodeArena, source_file: NodeId) -> BTreeSet<NodeId> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![source_file];
    while let Some(node_id) = pending.pop() {
        if !reachable.insert(node_id) {
            continue;
        }
        if let Some(node) = arena.get(node_id) {
            node.for_each_child(|child| pending.push(child));
        }
    }
    reachable
}

/// Why the supported `initializeChecker` global prefix could not complete.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalGlobalInitializationError {
    /// Intrinsic bootstrap was not present at the internal sequencing boundary.
    MissingBootstrap,
    /// Program order referred to a file missing from the prepared context.
    MissingFile(FileId),
    /// A prepared file unexpectedly lost its required source facts.
    MissingSourceFileFacts(FileId),
    /// A binder-owned symbol table failed store-provenance validation.
    InvalidTable { file: FileId, table: SymbolTableId },
    /// The bootstrap-owned globals table failed store-provenance validation.
    InvalidGlobals(SymbolTableId),
    /// A binder-owned symbol failed store-provenance validation.
    InvalidSymbol(SemanticSymbolId),
    /// A script declaration requires the pinned TS2397 diagnostic owner.
    ScriptGlobalThisDeclaration { file: FileId, declaration: NodeRef },
    /// `GlobalExports` existed without the external source-file symbol that
    /// owns its alias entries.
    MissingSourceFileSymbol(FileId),
    /// A UMD first-in-wins insertion failed store validation.
    InvalidUmdInsertion {
        file: FileId,
        symbol: SemanticSymbolId,
    },
    /// A UMD slot changed after the preceding absence check.
    UnexpectedUmdCollision {
        file: FileId,
        symbol: SemanticSymbolId,
    },
    /// A retained module-augmentation name has invalid AST/binder provenance.
    InvalidAugmentationName(NodeRef),
    /// A retained global augmentation has no canonical declaration symbol.
    MissingAugmentationSymbol(NodeRef),
    /// A global-augmentation symbol has no first declaration for the pinned
    /// combined-symbol once-only check.
    MissingAugmentationDeclaration(SemanticSymbolId),
    /// A declaration reached through a merged symbol is not readable from its
    /// exact registered file/arena snapshot.
    InvalidDeclarationProvenance(NodeRef),
    /// A value declaration of `undefined` requires the pinned TS2397
    /// diagnostic owner.
    UndefinedValueDeclaration(NodeRef),
    /// The `undefined` slot changed after the preceding absence check.
    UnexpectedUndefinedCollision,
    /// Installing the intrinsic `undefined` symbol failed store validation.
    InvalidUndefinedInsertion {
        globals: SymbolTableId,
        undefined_symbol: SemanticSymbolId,
    },
    /// The retained Program sources cannot construct an exact declared-type
    /// callback host at the post-global phase boundary.
    DeclaredTypeHost(DeclaredTypeHostError),
    /// Standard-library identity initialization rejected an invariant or an
    /// unsupported declared-type dependency.
    GlobalTypes(CanonicalGlobalTypeInitializationError),
    /// The exact symbol merge requires an unsupported dependency or rejected
    /// malformed provenance.
    Merge(SymbolMergeError),
}

impl std::fmt::Display for CanonicalGlobalInitializationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("checker global initialization ran before intrinsic bootstrap")
            }
            Self::MissingFile(file) => write!(
                formatter,
                "global initialization is missing prepared file {}",
                file.index()
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "global initialization file {} has no source facts",
                file.index()
            ),
            Self::InvalidTable { file, .. } => write!(
                formatter,
                "file {} references a foreign or missing symbol table",
                file.index()
            ),
            Self::InvalidGlobals(_) => {
                formatter.write_str("bootstrap globals table is foreign or missing")
            }
            Self::InvalidSymbol(symbol) => {
                write!(
                    formatter,
                    "global initialization cannot read symbol {symbol:?}"
                )
            }
            Self::ScriptGlobalThisDeclaration { file, declaration } => write!(
                formatter,
                "script file {} declares built-in globalThis at {declaration:?}",
                file.index()
            ),
            Self::MissingSourceFileSymbol(file) => write!(
                formatter,
                "file {} has UMD exports but no source-file symbol",
                file.index()
            ),
            Self::InvalidUmdInsertion { file, symbol } => write!(
                formatter,
                "file {} cannot install UMD symbol {symbol:?}",
                file.index()
            ),
            Self::UnexpectedUmdCollision { file, symbol } => write!(
                formatter,
                "file {} observed a late UMD collision for {symbol:?}",
                file.index()
            ),
            Self::InvalidAugmentationName(name) => {
                write!(formatter, "invalid module-augmentation name {name:?}")
            }
            Self::MissingAugmentationSymbol(module) => {
                write!(formatter, "global augmentation {module:?} has no symbol")
            }
            Self::MissingAugmentationDeclaration(symbol) => write!(
                formatter,
                "global-augmentation symbol {symbol:?} has no declaration"
            ),
            Self::InvalidDeclarationProvenance(declaration) => write!(
                formatter,
                "global declaration {declaration:?} has invalid provenance"
            ),
            Self::UndefinedValueDeclaration(declaration) => write!(
                formatter,
                "value declaration {declaration:?} conflicts with built-in undefined"
            ),
            Self::UnexpectedUndefinedCollision => {
                formatter.write_str("undefined appeared after the preceding absence check")
            }
            Self::InvalidUndefinedInsertion { .. } => {
                formatter.write_str("cannot install the intrinsic undefined global")
            }
            Self::DeclaredTypeHost(error) => write!(formatter, "{error}"),
            Self::GlobalTypes(error) => {
                write!(formatter, "global type initialization failed: {error}")
            }
            Self::Merge(error) => write!(formatter, "global symbol merge failed: {error}"),
        }
    }
}

impl std::error::Error for CanonicalGlobalInitializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::DeclaredTypeHost(error) => Some(error),
            Self::GlobalTypes(error) => Some(error),
            Self::Merge(error) => Some(error),
            _ => None,
        }
    }
}

impl From<SymbolMergeError> for CanonicalGlobalInitializationError {
    fn from(error: SymbolMergeError) -> Self {
        Self::Merge(error)
    }
}

impl From<DeclaredTypeHostError> for CanonicalGlobalInitializationError {
    fn from(error: DeclaredTypeHostError) -> Self {
        Self::DeclaredTypeHost(error)
    }
}

impl From<CanonicalGlobalTypeInitializationError> for CanonicalGlobalInitializationError {
    fn from(error: CanonicalGlobalTypeInitializationError) -> Self {
        Self::GlobalTypes(error)
    }
}

/// Why canonical binder output could not become a complete checker context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CanonicalCheckerContextError {
    /// At least one binder file has not completed declaration dispatch.
    Extraction(CanonicalExtractionError),
    /// The explicit Program order repeats a file slot.
    DuplicateFileInOrder(FileId),
    /// Two Program slots were paired with the same arena identity.
    DuplicateArenaInOrder {
        arena: NodeArenaId,
        first_file: FileId,
        second_file: FileId,
    },
    /// The explicit Program order names a file absent from binder output.
    ExtraOrderedFile(FileId),
    /// Binder output contains a file absent from the explicit Program order.
    MissingOrderedFile(FileId),
    /// A file slot was paired with an arena other than the one it was bound in.
    ArenaMismatch {
        file: FileId,
        expected: NodeArenaId,
        actual: NodeArenaId,
    },
    /// Declaration-complete binder output omitted required Program facts.
    MissingSourceFileFacts(FileId),
    /// A bound source root does not carry the supplied file/arena provenance.
    SourceFileProvenance { file: FileId, source: NodeRef },
    /// A bound source-root ID no longer exists in its exact arena.
    MissingSourceFileRoot(NodeRef),
    /// The root is not an exact `SourceFile` syntax/payload pair.
    InvalidSourceFileRoot { source: NodeRef, kind: SyntaxKind },
    /// The source-file root acquired an invalid parent backlink.
    SourceFileHasParent {
        source: NodeRef,
        parent: ts_ast::NodeId,
    },
    /// Binder side data does not mark its own source root as reached.
    UnboundSourceFile(NodeRef),
    /// A node visited by the binder is no longer reachable from the source root.
    BoundNodeNowUnreachable(NodeRef),
    /// A node now reachable from the source root was never visited by the binder.
    NewlyReachableUnboundNode(NodeRef),
    /// The arena changed after the binder captured its traversal side data.
    ArenaRevisionMismatch {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    /// The adopted binder symbol store does not own a reached bound node.
    UnownedBoundNode(NodeRef),
    /// Full source-tree validation or internal source registration failed.
    SourceRegistrationFailed(FileId),
    /// Intrinsic singleton initialization rejected the adopted store.
    Bootstrap(IntrinsicBootstrapError),
    /// The explicit checker-owned module-resolution manifest was invalid.
    ModuleResolutions(CanonicalModuleResolutionManifestError),
    /// The retained Program could not form its once-validated alias source registry.
    AliasTargetHost(ProductionAliasTargetHostError),
    /// The checker store already retained a conflicting query-session option.
    StrictBuiltinIteratorReturnClaim {
        established_strict_builtin_iterator_return: bool,
        requested_strict_builtin_iterator_return: bool,
    },
    /// The checker store already retained a conflicting function-variance mode.
    StrictFunctionTypesClaim {
        established_strict_function_types: bool,
        requested_strict_function_types: bool,
    },
    /// The supported `initializeChecker` global prefix could not complete.
    GlobalInitialization(CanonicalGlobalInitializationError),
}

impl std::fmt::Display for CanonicalCheckerContextError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Extraction(error) => write!(formatter, "{error}"),
            Self::DuplicateFileInOrder(file) => write!(
                formatter,
                "file {} occurs more than once in Program order",
                file.index()
            ),
            Self::DuplicateArenaInOrder {
                arena,
                first_file,
                second_file,
            } => write!(
                formatter,
                "arena {arena:?} is assigned to both files {} and {}",
                first_file.index(),
                second_file.index()
            ),
            Self::ExtraOrderedFile(file) => write!(
                formatter,
                "Program order contains unbound file {}",
                file.index()
            ),
            Self::MissingOrderedFile(file) => {
                write!(formatter, "Program order omits bound file {}", file.index())
            }
            Self::ArenaMismatch {
                file,
                expected,
                actual,
            } => write!(
                formatter,
                "file {} was bound in arena {expected:?}, not {actual:?}",
                file.index()
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "declaration-complete file {} has no retained source facts",
                file.index()
            ),
            Self::SourceFileProvenance { file, source } => write!(
                formatter,
                "source root {source:?} does not belong to file {} and its supplied arena",
                file.index()
            ),
            Self::MissingSourceFileRoot(source) => {
                write!(formatter, "source root {source:?} is absent from its arena")
            }
            Self::InvalidSourceFileRoot { source, kind } => write!(
                formatter,
                "source root {source:?} is not an exact SourceFile (found {kind:?})"
            ),
            Self::SourceFileHasParent { source, parent } => write!(
                formatter,
                "source root {source:?} has parent node {}",
                parent.index()
            ),
            Self::UnboundSourceFile(source) => {
                write!(formatter, "binder did not reach source root {source:?}")
            }
            Self::BoundNodeNowUnreachable(node) => write!(
                formatter,
                "binder-visited node {node:?} is no longer reachable from its source root"
            ),
            Self::NewlyReachableUnboundNode(node) => write!(
                formatter,
                "source-root-reachable node {node:?} was not visited by the binder"
            ),
            Self::ArenaRevisionMismatch { file, .. } => write!(
                formatter,
                "arena changed after canonical binding for file {}",
                file.index()
            ),
            Self::UnownedBoundNode(node) => {
                write!(
                    formatter,
                    "binder symbol store does not own reached node {node:?}"
                )
            }
            Self::SourceRegistrationFailed(file) => write!(
                formatter,
                "checker source registration failed for file {}",
                file.index()
            ),
            Self::Bootstrap(error) => {
                write!(formatter, "checker intrinsic bootstrap failed: {error:?}")
            }
            Self::ModuleResolutions(error) => {
                write!(formatter, "checker module resolutions are invalid: {error}")
            }
            Self::AliasTargetHost(error) => {
                write!(
                    formatter,
                    "checker alias source registry is invalid: {error}"
                )
            }
            Self::StrictBuiltinIteratorReturnClaim {
                established_strict_builtin_iterator_return,
                requested_strict_builtin_iterator_return,
            } => write!(
                formatter,
                "checker store retained strictBuiltinIteratorReturn={established_strict_builtin_iterator_return}, not the requested {requested_strict_builtin_iterator_return}"
            ),
            Self::StrictFunctionTypesClaim {
                established_strict_function_types,
                requested_strict_function_types,
            } => write!(
                formatter,
                "checker store retained strictFunctionTypes={established_strict_function_types}, not the requested {requested_strict_function_types}"
            ),
            Self::GlobalInitialization(error) => {
                write!(formatter, "checker global initialization failed: {error}")
            }
        }
    }
}

impl std::error::Error for CanonicalCheckerContextError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Extraction(error) => Some(error),
            Self::ModuleResolutions(error) => Some(error),
            Self::AliasTargetHost(error) => Some(error),
            Self::GlobalInitialization(error) => Some(error),
            _ => None,
        }
    }
}

impl From<CanonicalExtractionError> for CanonicalCheckerContextError {
    fn from(error: CanonicalExtractionError) -> Self {
        Self::Extraction(error)
    }
}

impl From<IntrinsicBootstrapError> for CanonicalCheckerContextError {
    fn from(error: IntrinsicBootstrapError) -> Self {
        Self::Bootstrap(error)
    }
}

impl From<CanonicalModuleResolutionManifestError> for CanonicalCheckerContextError {
    fn from(error: CanonicalModuleResolutionManifestError) -> Self {
        Self::ModuleResolutions(error)
    }
}

impl From<ProductionAliasTargetHostError> for CanonicalCheckerContextError {
    fn from(error: ProductionAliasTargetHostError) -> Self {
        Self::AliasTargetHost(error)
    }
}

impl From<CanonicalGlobalInitializationError> for CanonicalCheckerContextError {
    fn from(error: CanonicalGlobalInitializationError) -> Self {
        Self::GlobalInitialization(error)
    }
}

#[cfg(test)]
mod tests {
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, resolve_global_name,
    };
    use ts_core::{TextPos, TextRange};
    use ts_diagnostics::{Diagnostic, message_by_code};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasTargetState, CanonicalCheckerDiagnosticRange, CanonicalModuleResolutionEntry,
        CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
        CanonicalResolvedModuleInput, DeclaredTypeUnavailable, TypeData, TypeResolutionTarget,
        TypeResolutionTargetError, TypeSystemPropertyName,
        alias::{CanonicalAliasResolutionEvent, CanonicalAliasTargetUnavailable},
        type_records::TypeCacheState,
        types::ObjectFlags,
    };

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn source_facts(file: FileId) -> CanonicalSourceFileFacts {
        source_facts_with(file, false, CanonicalModuleState::Script)
    }

    fn source_facts_with(
        file: FileId,
        is_declaration_file: bool,
        module_state: CanonicalModuleState,
    ) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            is_declaration_file,
            module_state,
        )
    }

    fn completed_bindings(files: &[(FileId, &ParseResult)]) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts(file),
                )
                .unwrap();
        }
        for &(file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder.finish()
    }

    fn completed_bindings_with_facts(
        files: &[(FileId, &ParseResult, bool, CanonicalModuleState)],
    ) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, is_declaration_file, module_state) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts_with(file, is_declaration_file, module_state),
                )
                .unwrap();
        }
        for &(file, parsed, _, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder.finish()
    }

    fn external_context<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        module_resolutions: CanonicalModuleResolutionManifestInput,
    ) -> CanonicalCheckerContext<'arena> {
        let files_with_facts = files
            .iter()
            .map(|&(file, parsed)| (file, parsed, false, CanonicalModuleState::External))
            .collect::<Vec<_>>();
        CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings_with_facts(&files_with_facts),
            files
                .iter()
                .map(|&(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            module_resolutions,
        )
        .unwrap()
    }

    fn external_context_without_module_resolutions<'arena>(
        files: &[(FileId, &'arena ParseResult)],
    ) -> CanonicalCheckerContext<'arena> {
        let files_with_facts = files
            .iter()
            .map(|&(file, parsed)| (file, parsed, false, CanonicalModuleState::External))
            .collect::<Vec<_>>();
        CanonicalCheckerContext::new(
            completed_bindings_with_facts(&files_with_facts),
            files
                .iter()
                .map(|&(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn node_ref(parsed: &ParseResult, file: FileId, node: NodeId) -> NodeRef {
        NodeRef::new(parsed.arena.id(), file, node)
    }

    fn module_specifiers(parsed: &ParseResult) -> Vec<NodeId> {
        let mut specifiers = parsed
            .arena
            .iter()
            .filter_map(|(_, node)| match &node.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                NodeData::ExportDeclaration(export) => export.module_specifier,
                _ => None,
            })
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn module_export_name(arena: &NodeArena, name: NodeId) -> Option<&str> {
        match &arena.get(name)?.data {
            NodeData::Identifier(identifier) => Some(&identifier.text),
            NodeData::StringLiteral(literal) => Some(&literal.text),
            _ => None,
        }
    }

    fn alias_declaration_named(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, data)| {
                let name_node = match &data.data {
                    NodeData::ImportClause(clause) => clause.name,
                    NodeData::ImportSpecifier(specifier) => Some(specifier.name),
                    NodeData::ExportSpecifier(specifier) => Some(specifier.name),
                    NodeData::NamespaceImport(namespace) => Some(namespace.name),
                    _ => None,
                }?;
                (module_export_name(&parsed.arena, name_node) == Some(name))
                    .then_some(node_ref(parsed, file, node))
            })
            .unwrap_or_else(|| panic!("missing alias declaration {name}"))
    }

    fn alias_symbol(
        context: &CanonicalCheckerContext<'_>,
        declaration: NodeRef,
    ) -> SemanticSymbolId {
        context
            .file(declaration.file)
            .and_then(|(_, bound)| bound.symbol(declaration))
            .expect("alias declaration has a canonical symbol")
    }

    fn source_module(context: &CanonicalCheckerContext<'_>, file: FileId) -> SemanticSymbolId {
        let (_, bound) = context.file(file).expect("context retains source file");
        bound
            .symbol(bound.source_file())
            .expect("external source file has a canonical module symbol")
    }

    fn direct_export(
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
        name: &str,
    ) -> SemanticSymbolId {
        let module = source_module(context, file);
        let exports = context
            .store()
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .expect("module has an exports table");
        context
            .store()
            .symbol_table(exports)
            .and_then(|exports| exports.get_source(name))
            .unwrap_or_else(|| panic!("module has direct export {name}"))
    }

    fn esm(target: FileId) -> CanonicalResolvedModuleInput {
        CanonicalResolvedModuleInput::new(
            target,
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::Esm,
        )
    }

    fn alias_query_unavailable_reason(
        error: CanonicalAliasQueryError,
    ) -> CanonicalAliasTargetUnavailable {
        match error {
            CanonicalAliasQueryError::AliasResolution(
                CanonicalAliasResolutionError::TargetUnavailable { reason, .. },
            ) => reason,
            other => panic!("expected unavailable alias target, got {other:?}"),
        }
    }

    fn global_symbol(
        context: &CanonicalCheckerContext<'_>,
        name: &str,
    ) -> Option<SemanticSymbolId> {
        context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source(name)
    }

    fn interface_base_snapshot(
        context: &CanonicalCheckerContext<'_>,
        type_id: TypeId,
    ) -> (bool, Option<TypeId>, Option<Vec<TypeId>>, ObjectFlags) {
        let record = context.store().type_payload(type_id).unwrap();
        let TypeData::Interface(interface) = record.data() else {
            panic!("expected interface origin")
        };
        (
            interface.base_types_resolved,
            interface.resolved_base_constructor_type,
            interface.resolved_base_types.clone(),
            record.object_flags(),
        )
    }

    fn reinitialize_global_library_types(
        context: &mut CanonicalCheckerContext<'_>,
    ) -> Result<CanonicalGlobalTypes, CanonicalGlobalTypeInitializationError> {
        let globals = context.globals;
        let options = context.options;
        let CanonicalCheckerContext { files, store, .. } = context;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        initialize_global_library_types(store, &host, globals, options.strict_bind_call_apply)
    }

    fn minimal_global_library() -> ParseResult {
        parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             interface Object {}\n\
             declare var Object: { prototype: Object };\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        )
    }

    fn heritage_global_library() -> ParseResult {
        parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             interface ObjectBase {}\n\
             interface Object extends ObjectBase {}\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        )
    }

    fn type_alias_body(source: &ParseResult, file: FileId, name: &str) -> NodeRef {
        let body = source
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &source.arena.get(alias.name)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(alias.type_)
            })
            .unwrap_or_else(|| panic!("missing type alias {name}"));
        NodeRef::new(source.arena.id(), file, body)
    }

    type NormalizedGlobalSnapshot = Vec<(Vec<u8>, u32, usize)>;
    type NormalizedRedirectSnapshot = Vec<(usize, Vec<u8>, bool)>;

    fn normalized_global_and_redirect_snapshot(
        context: &CanonicalCheckerContext<'_>,
    ) -> (NormalizedGlobalSnapshot, NormalizedRedirectSnapshot) {
        let mut globals = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .iter()
            .map(|(name, symbol)| {
                let record = context.store().symbol(symbol).unwrap();
                (
                    name.as_bytes().to_vec(),
                    record.flags().bits(),
                    record.declarations().map_or(0, <[NodeRef]>::len),
                )
            })
            .collect::<Vec<_>>();
        globals.sort_unstable_by(|left, right| left.0.cmp(&right.0));

        let mut redirects = Vec::new();
        for &file in context.file_order() {
            let (_, bound) = context.file(file).unwrap();
            if let Some(locals) = bound.locals(bound.source_file()) {
                for (name, symbol) in context.store().symbol_table(locals).unwrap().iter() {
                    let merged = context.store().get_merged_symbol(symbol).unwrap();
                    redirects.push((file.index(), name.as_bytes().to_vec(), merged != symbol));
                }
            }
        }
        redirects.sort_unstable();
        (globals, redirects)
    }

    fn allocate_unattached_empty_statement(source: &mut ParseResult) -> NodeId {
        let empty = source
            .arena
            .iter()
            .find_map(|(node, data)| (data.kind == SyntaxKind::EmptyStatement).then_some(node))
            .expect("the test source contains an empty statement");
        let orphan = source
            .arena
            .get(empty)
            .expect("the empty statement came from this arena")
            .clone();
        source.arena.alloc(orphan)
    }

    fn source_statements_mut(source: &mut ParseResult) -> &mut Vec<NodeId> {
        let NodeData::SourceFile(data) = &mut source
            .arena
            .get_mut(source.source_file)
            .expect("the parser source root exists")
            .data
        else {
            panic!("the parser source root has SourceFile data");
        };
        &mut data.statements.nodes
    }

    #[test]
    fn checker_option_defaults_leave_retained_strict_options_disabled() {
        let defaults = CanonicalCheckerOptions::default();
        assert!(!defaults.strict_builtin_iterator_return);
        assert!(!defaults.strict_function_types);
        assert!(!defaults.no_implicit_any);
        assert!(!defaults.no_error_truncation);

        let intrinsic = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        };
        let options = CanonicalCheckerOptions::from(intrinsic);
        assert_eq!(options.intrinsic, intrinsic);
        assert!(!options.strict_builtin_iterator_return);
        assert!(!options.strict_function_types);
        assert!(!options.no_implicit_any);
        assert!(!options.no_error_truncation);
    }

    #[test]
    fn diagnostic_ownership_accepts_exact_subranges_and_rejects_poison() {
        let source = parsed("const target = 1;");
        let file = FileId::new(1);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (identifier, identifier_record) = source
            .arena
            .iter()
            .find(|(_, record)| record.kind == SyntaxKind::Identifier)
            .unwrap();
        let anchor = node_ref(&source, file, identifier);
        let source_range = source.arena.get(source.source_file).unwrap().range;
        let valid = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(
                identifier_record.range.start,
                TextPos::new(identifier_record.range.start.get() + 1),
            ),
        );
        let owner = context.files.source_file(file).unwrap();
        let diagnostic = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["target"]);
        let mut accepted = CanonicalCheckerDiagnostics::default();
        accepted.lookup_primary_or_issue(Some(anchor), Some(valid), diagnostic.clone());

        assert_eq!(
            diagnostic_owners(&context.files, owner, &accepted),
            Ok(vec![owner])
        );

        let empty = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(identifier_record.range.start, identifier_record.range.start),
        );
        let outside_anchor = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(
                TextPos::new(identifier_record.range.start.get() - 1),
                identifier_record.range.end,
            ),
        );
        let outside_source = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(source_range.end, TextPos::new(source_range.end.get() + 1)),
        );
        let foreign_anchor = NodeRef::new(source.arena.id(), FileId::new(99), identifier);
        let foreign = CanonicalCheckerDiagnosticRange::new(foreign_anchor, valid.range());

        for (node, range_override) in [
            (Some(anchor), empty),
            (Some(anchor), outside_anchor),
            (Some(anchor), outside_source),
            (Some(anchor), foreign),
            (None, valid),
        ] {
            let mut poisoned = CanonicalCheckerDiagnostics::default();
            poisoned.lookup_primary_or_issue(node, Some(range_override), diagnostic.clone());
            assert_eq!(
                diagnostic_owners(&context.files, owner, &poisoned),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::InvalidDiagnosticRange {
                        node,
                        range_override,
                    }
                ))
            );
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn context_query_facade_retains_options_and_diagnostics_across_retries() {
        let source = parsed(concat!(
            "type BuiltinIteratorReturn = intrinsic; ",
            "type Wrapper = BuiltinIteratorReturn; ",
            "type A = B; type B = A;",
        ));
        let file = FileId::new(2);
        let wrapper_body = type_alias_body(&source, file, "Wrapper");
        let options = CanonicalCheckerOptions {
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        };
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            options,
        )
        .unwrap();
        let cycle = global_symbol(&context, "A").unwrap();
        let wrapper = global_symbol(&context, "Wrapper").unwrap();
        let (error_type, undefined_type) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.undefined_type)
        };

        assert!(context.diagnostics().is_empty());
        assert_eq!(context.get_declared_type_of_symbol(cycle), Ok(error_type));
        assert_eq!(context.diagnostics().len(), 2);
        assert!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2456)
        );
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.arguments[0].as_str())
                .collect::<Vec<_>>(),
            ["B", "A"]
        );
        assert_eq!(context.get_declared_type_of_symbol(cycle), Ok(error_type));
        assert_eq!(context.diagnostics().len(), 2);

        assert_eq!(
            context.get_type_from_type_node(wrapper_body),
            Ok(undefined_type)
        );
        assert_eq!(
            context.get_declared_type_of_symbol(wrapper),
            Ok(undefined_type)
        );
        assert_eq!(
            context.store().claimed_strict_builtin_iterator_return(),
            Some(true)
        );
        assert_eq!(context.store().claimed_strict_function_types(), Some(true));
        assert!(context.options().strict_function_types);
        assert_eq!(context.diagnostics().len(), 2);
    }

    #[test]
    fn context_assignability_uses_one_immutable_function_variance_mode() {
        let source = parsed(concat!(
            "type Narrow = (value: string) => void; ",
            "type Wide = (value: string | number) => void;",
        ));
        let file = FileId::new(805);
        let narrow_node = type_alias_body(&source, file, "Narrow");
        let wide_node = type_alias_body(&source, file, "Wide");

        for (strict_function_types, narrow_to_wide) in [(true, false), (false, true)] {
            let mut context = CanonicalCheckerContext::new(
                completed_bindings(&[(file, &source)]),
                vec![(file, &source.arena)],
                CanonicalCheckerOptions {
                    strict_function_types,
                    ..CanonicalCheckerOptions::default()
                },
            )
            .unwrap();
            let narrow = context.get_type_from_type_node(narrow_node).unwrap();
            let wide = context.get_type_from_type_node(wide_node).unwrap();
            for node in [narrow_node, wide_node] {
                let signature = context
                    .store()
                    .signature_links(node)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap();
                context.get_return_type_of_signature(signature).unwrap();
            }

            assert_eq!(
                context.store().claimed_strict_function_types(),
                Some(strict_function_types)
            );
            assert_eq!(
                context.is_type_assignable_to(narrow, wide),
                Ok(narrow_to_wide)
            );
            assert_eq!(context.is_type_assignable_to(wide, narrow), Ok(true));
        }
    }

    #[test]
    fn context_queries_thread_the_authoritative_array_target() {
        let source = parsed("interface Array<T> {} type Values = number[];");
        let file = FileId::new(804);
        let body = type_alias_body(&source, file, "Values");
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let array_target = context.global_types().array_type;
        let number_type = context.store().intrinsic_bootstrap().unwrap().number_type;

        let array = context.get_type_from_type_node(body).unwrap();

        let TypeData::TypeReference(reference) =
            context.store().type_payload(array).unwrap().data()
        else {
            panic!("array syntax must resolve to the canonical Array reference")
        };
        assert_eq!(reference.object.target, Some(array_target));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[number_type][..])
        );
        assert!(
            context
                .store()
                .type_payload(array)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE)
        );
        let values = global_symbol(&context, "Values").unwrap();
        assert_eq!(context.get_declared_type_of_symbol(values), Ok(array));
    }

    #[test]
    fn context_type_reference_queries_borrow_the_once_validated_source_registry() {
        let first = parsed("type BaseOne = string; type UseOne = BaseOne;");
        let second = parsed("type BaseTwo = string; type UseTwo = BaseTwo;");
        let third = parsed("type BaseThree = string; type UseThree = BaseThree;");
        let first_file = FileId::new(801);
        let second_file = FileId::new(802);
        let third_file = FileId::new(803);
        let files = [
            (first_file, &first),
            (second_file, &second),
            (third_file, &third),
        ];
        let bodies = [
            type_alias_body(&first, first_file, "UseOne"),
            type_alias_body(&second, second_file, "UseTwo"),
            type_alias_body(&third, third_file, "UseThree"),
        ];
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&files),
            files
                .iter()
                .map(|&(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
        let baseline = context.files.instrumentation();

        assert_eq!(baseline.validation_passes, 1);
        assert_eq!(baseline.validated_sources, files.len());
        assert_eq!(baseline.snapshot_iterations, 0);

        for body in bodies {
            assert_eq!(context.get_type_from_type_node(body), Ok(string_type));
        }
        let after_uncached = context.files.instrumentation();
        assert_eq!(
            after_uncached.declared_type_views,
            baseline.declared_type_views + bodies.len()
        );
        assert_eq!(after_uncached.snapshot_iterations, 0);
        assert!(after_uncached.name_resolver_views >= baseline.name_resolver_views + bodies.len());

        for body in bodies {
            assert_eq!(context.get_type_from_type_node(body), Ok(string_type));
        }
        let after_cached = context.files.instrumentation();
        assert_eq!(
            after_cached.declared_type_views,
            after_uncached.declared_type_views + bodies.len()
        );
        assert_eq!(
            after_cached.name_resolver_views,
            after_uncached.name_resolver_views
        );
        assert_eq!(after_cached.snapshot_iterations, 0);

        for name in ["UseOne", "UseTwo", "UseThree"] {
            let symbol = global_symbol(&context, name).unwrap();
            assert_eq!(context.get_declared_type_of_symbol(symbol), Ok(string_type));
        }
        let after_declared = context.files.instrumentation();
        assert_eq!(
            after_declared.declared_type_views,
            after_cached.declared_type_views + bodies.len()
        );
        assert_eq!(after_declared.snapshot_iterations, 0);

        drop(
            context
                .name_resolver_host(CanonicalNameResolverOptions::default())
                .unwrap(),
        );
        drop(
            context
                .name_resolver_host(CanonicalNameResolverOptions::default())
                .unwrap(),
        );
        let after_resolver_hosts = context.files.instrumentation();
        assert_eq!(
            after_resolver_hosts.name_resolver_views,
            after_declared.name_resolver_views + 2
        );
        assert_eq!(after_resolver_hosts.validation_passes, 1);
        assert_eq!(after_resolver_hosts.snapshot_iterations, 0);

        for &(file, _) in &files {
            context.check_source_file(file).unwrap();
        }
        let after_source_checks = context.files.instrumentation();
        assert_eq!(
            after_source_checks.declared_type_views,
            after_resolver_hosts.declared_type_views + files.len()
        );
        assert_eq!(after_source_checks.validation_passes, 1);
        assert_eq!(after_source_checks.snapshot_iterations, 0);
    }

    #[test]
    fn borrowed_registry_views_preserve_the_registry_store_brand() {
        let source = parsed("type Value = string;");
        let file = FileId::new(804);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let mut foreign = CanonicalTypeMapperStore::new();
        foreign
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let expected = context.id();
        let actual = foreign.id();
        let baseline = context.files.instrumentation();

        let declared_error = DeclaredTypeHost::from_registry(
            &foreign,
            &context.files,
            GlobalMergeCompletion::new(CanonicalNameResolverOptions::default()),
        )
        .unwrap_err();
        assert_eq!(
            declared_error,
            DeclaredTypeHostError::RegistryStoreMismatch { expected, actual }
        );
        let resolver_error = ProductionNameResolverHost::from_registry(
            &foreign,
            &context.files,
            CanonicalNameResolverOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            resolver_error,
            ProductionNameResolverHostError::RegistryStoreMismatch { expected, actual }
        );
        assert_eq!(context.files.instrumentation(), baseline);
    }

    #[test]
    fn production_alias_queries_resolve_named_and_namespace_imports_and_combine_flags() {
        let importer = parsed(
            r#"
                import * as namespace from "./target";
                import { value as local } from "./target";
            "#,
        );
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(201);
        let target_file = FileId::new(202);
        let specifiers = module_specifiers(&importer);
        let entries = specifiers.iter().map(|specifier| {
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, *specifier),
                esm(target_file),
            )
        });
        let mut context = external_context(
            &[(importer_file, &importer), (target_file, &target)],
            CanonicalModuleResolutionManifestInput::new(entries),
        );
        let namespace_declaration = alias_declaration_named(&importer, importer_file, "namespace");
        let local_declaration = alias_declaration_named(&importer, importer_file, "local");
        let namespace_alias = alias_symbol(&context, namespace_declaration);
        let local_alias = alias_symbol(&context, local_declaration);
        let target_module = source_module(&context, target_file);
        let value = direct_export(&context, target_file, "value");
        let diagnostics_before = context.diagnostics().clone();

        let namespace_resolution = context.resolve_alias(namespace_alias).unwrap();
        assert_eq!(
            namespace_resolution.target,
            AliasTargetState::Resolved(target_module)
        );
        assert!(namespace_resolution.events.is_empty());

        let local_resolution = context.resolve_alias(local_alias).unwrap();
        assert_eq!(local_resolution.target, AliasTargetState::Resolved(value));
        assert!(local_resolution.events.is_empty());

        let local_flags = context.get_symbol_flags(local_alias).unwrap();
        let expected_flags = context.store().symbol(local_alias).unwrap().flags()
            | context.store().symbol(value).unwrap().flags();
        assert_eq!(local_flags.flags, expected_flags);
        assert!(local_flags.events.is_empty());

        let cached_namespace = context.resolve_alias(namespace_alias).unwrap();
        assert_eq!(cached_namespace.target, namespace_resolution.target);
        assert!(cached_namespace.events.is_empty());
        assert_eq!(context.diagnostics(), &diagnostics_before);
    }

    #[test]
    fn production_alias_queries_resolve_transitive_reexports_and_propagate_type_only_markers() {
        let base = parsed("export interface Value { field: string }");
        let middle = parsed("export type { Value as Mid } from './base';");
        let consumer = parsed(
            r#"
                import { Mid as Local } from "./middle";
                import type * as Types from "./base";
            "#,
        );
        let base_file = FileId::new(203);
        let middle_file = FileId::new(204);
        let consumer_file = FileId::new(205);
        let middle_specifier = node_ref(
            &middle,
            middle_file,
            module_specifiers(&middle).into_iter().next().unwrap(),
        );
        let consumer_specifiers = module_specifiers(&consumer);
        let entries = [
            CanonicalModuleResolutionEntry::resolved(middle_specifier, esm(base_file)),
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&consumer, consumer_file, consumer_specifiers[0]),
                esm(middle_file),
            ),
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&consumer, consumer_file, consumer_specifiers[1]),
                esm(base_file),
            ),
        ];
        let mut context = external_context(
            &[
                (base_file, &base),
                (middle_file, &middle),
                (consumer_file, &consumer),
            ],
            CanonicalModuleResolutionManifestInput::new(entries),
        );
        let middle_declaration = alias_declaration_named(&middle, middle_file, "Mid");
        let local_declaration = alias_declaration_named(&consumer, consumer_file, "Local");
        let namespace_declaration = alias_declaration_named(&consumer, consumer_file, "Types");
        let middle_alias = alias_symbol(&context, middle_declaration);
        let local_alias = alias_symbol(&context, local_declaration);
        let namespace_alias = alias_symbol(&context, namespace_declaration);
        let value = direct_export(&context, base_file, "Value");
        let base_module = source_module(&context, base_file);

        let resolution = context.resolve_alias(local_alias).unwrap();
        assert_eq!(resolution.target, AliasTargetState::Resolved(value));
        assert!(resolution.events.is_empty());
        assert_eq!(
            context
                .store()
                .alias_symbol_links(middle_alias)
                .unwrap()
                .type_only_declaration,
            Some(middle_declaration)
        );
        assert_eq!(
            context
                .store()
                .alias_symbol_links(local_alias)
                .unwrap()
                .type_only_declaration,
            Some(middle_declaration),
            "the transitive marker comes from the re-export declaration"
        );

        let namespace = context.resolve_alias(namespace_alias).unwrap();
        assert_eq!(namespace.target, AliasTargetState::Resolved(base_module));
        assert!(namespace.events.is_empty());
        assert_eq!(
            context
                .store()
                .alias_symbol_links(namespace_alias)
                .unwrap()
                .type_only_declaration,
            Some(namespace_declaration)
        );
        assert!(context.store().type_resolution_is_empty());
    }

    #[test]
    fn production_alias_queries_keep_manifest_failures_retryable_with_type_only_markers() {
        let importer = parsed(
            r#"
                import type * as UnavailableTypes from "./target";
                import { type value as AbsentValue } from "./target";
                import type { value as UnresolvedValue } from "./target";
            "#,
        );
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(206);
        let target_file = FileId::new(207);
        let specifiers = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| node_ref(&importer, importer_file, specifier))
            .collect::<Vec<_>>();
        let unavailable_declaration =
            alias_declaration_named(&importer, importer_file, "UnavailableTypes");

        let mut unavailable = external_context_without_module_resolutions(&[
            (importer_file, &importer),
            (target_file, &target),
        ]);
        let unavailable_alias = alias_symbol(&unavailable, unavailable_declaration);
        let unavailable_diagnostics = unavailable.diagnostics().clone();
        for _ in 0..2 {
            assert_eq!(
                alias_query_unavailable_reason(
                    unavailable.resolve_alias(unavailable_alias).unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(
                    specifiers[0]
                )
            );
            let links = unavailable
                .store()
                .alias_symbol_links(unavailable_alias)
                .unwrap();
            assert_eq!(links.immediate_target, None);
            assert_eq!(links.alias_target, AliasTargetState::Unresolved);
            assert_eq!(links.type_only_declaration, Some(unavailable_declaration));
            assert!(unavailable.store().type_resolution_is_empty());
            assert_eq!(unavailable.diagnostics(), &unavailable_diagnostics);
        }

        let mut available = external_context(
            &[(importer_file, &importer), (target_file, &target)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(specifiers[2]),
            ]),
        );
        let absent_declaration = alias_declaration_named(&importer, importer_file, "AbsentValue");
        let unresolved_declaration =
            alias_declaration_named(&importer, importer_file, "UnresolvedValue");
        let absent_alias = alias_symbol(&available, absent_declaration);
        let unresolved_alias = alias_symbol(&available, unresolved_declaration);
        let available_diagnostics = available.diagnostics().clone();

        for (alias, declaration, expected) in [
            (
                absent_alias,
                absent_declaration,
                CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(specifiers[1]),
            ),
            (
                unresolved_alias,
                unresolved_declaration,
                CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(specifiers[2]),
            ),
        ] {
            for _ in 0..2 {
                assert_eq!(
                    alias_query_unavailable_reason(available.resolve_alias(alias).unwrap_err()),
                    expected
                );
                let links = available.store().alias_symbol_links(alias).unwrap();
                assert_eq!(links.immediate_target, None);
                assert_eq!(links.alias_target, AliasTargetState::Unresolved);
                assert_eq!(links.type_only_declaration, Some(declaration));
                assert!(available.store().type_resolution_is_empty());
                assert_eq!(available.diagnostics(), &available_diagnostics);
            }
        }
    }

    #[test]
    fn production_alias_queries_preserve_foreign_and_non_alias_error_layers() {
        let target = parsed("export const value = 1;");
        let target_file = FileId::new(208);
        let mut context = external_context(
            &[(target_file, &target)],
            CanonicalModuleResolutionManifestInput::new([]),
        );
        let value = direct_export(&context, target_file, "value");

        let foreign = parsed("import { value as ForeignValue } from './foreign';");
        let foreign_file = FileId::new(209);
        let foreign_declaration = alias_declaration_named(&foreign, foreign_file, "ForeignValue");
        let foreign_alias = {
            let foreign_context =
                external_context_without_module_resolutions(&[(foreign_file, &foreign)]);
            alias_symbol(&foreign_context, foreign_declaration)
        };
        let diagnostics_before = context.diagnostics().clone();

        assert_eq!(
            context.resolve_alias(value),
            Err(CanonicalAliasQueryError::AliasResolution(
                CanonicalAliasResolutionError::SymbolIsNotAlias(value)
            ))
        );
        assert_eq!(
            context.resolve_alias(foreign_alias),
            Err(CanonicalAliasQueryError::AliasResolution(
                CanonicalAliasResolutionError::InvalidSymbol(foreign_alias)
            ))
        );
        assert_eq!(
            context.get_symbol_flags(foreign_alias),
            Err(CanonicalAliasQueryError::SymbolFlags(
                CanonicalSymbolFlagsError::InvalidSymbol(foreign_alias)
            ))
        );

        let expected_flags = context.store().symbol(value).unwrap().flags();
        let flags = context.get_symbol_flags(value).unwrap();
        assert_eq!(flags.flags, expected_flags);
        assert!(flags.events.is_empty());
        assert_eq!(context.diagnostics(), &diagnostics_before);
    }

    #[test]
    fn production_alias_cycle_events_are_returned_once_without_issuing_diagnostics() {
        let first = parsed("export { B as A } from './second';");
        let second = parsed("export { A as B } from './first';");
        let first_file = FileId::new(210);
        let second_file = FileId::new(211);
        let first_specifier = node_ref(
            &first,
            first_file,
            module_specifiers(&first).into_iter().next().unwrap(),
        );
        let second_specifier = node_ref(
            &second,
            second_file,
            module_specifiers(&second).into_iter().next().unwrap(),
        );
        let mut context = external_context(
            &[(first_file, &first), (second_file, &second)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(first_specifier, esm(second_file)),
                CanonicalModuleResolutionEntry::resolved(second_specifier, esm(first_file)),
            ]),
        );
        let first_declaration = alias_declaration_named(&first, first_file, "A");
        let second_declaration = alias_declaration_named(&second, second_file, "B");
        let first_alias = alias_symbol(&context, first_declaration);
        let second_alias = alias_symbol(&context, second_declaration);
        let diagnostics_before = context.diagnostics().clone();

        let initial = context.get_symbol_flags(first_alias).unwrap();
        assert_eq!(initial.flags, SymbolFlags::ALL);
        assert_eq!(
            initial.events,
            [
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias {
                    alias: second_alias,
                },
                CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias {
                    alias: first_alias,
                },
            ]
        );
        assert!(
            initial
                .events
                .iter()
                .all(|event| event.diagnostic_code() == 2303)
        );
        assert_eq!(context.diagnostics(), &diagnostics_before);

        let cached = context.resolve_alias(first_alias).unwrap();
        assert_eq!(cached.target, AliasTargetState::Unknown);
        assert!(cached.events.is_empty());
        assert_eq!(
            context
                .store()
                .alias_symbol_links(second_alias)
                .unwrap()
                .alias_target,
            AliasTargetState::Unknown
        );
        assert!(context.store().type_resolution_is_empty());
        assert_eq!(context.diagnostics(), &diagnostics_before);
    }

    #[test]
    fn alias_and_declared_errors_expose_nested_type_resolution_sources() {
        let importer = parsed("import { value as local } from './target';");
        let importer_file = FileId::new(212);
        let context = external_context_without_module_resolutions(&[(importer_file, &importer)]);
        let declaration = alias_declaration_named(&importer, importer_file, "local");
        let alias = alias_symbol(&context, declaration);
        let leaf = TypeResolutionTargetError {
            target: TypeResolutionTarget::Symbol(alias),
            property: TypeSystemPropertyName::AliasTarget,
        };
        let alias_error = CanonicalAliasResolutionError::TypeResolutionTarget(leaf);
        let flags_error = CanonicalSymbolFlagsError::AliasResolution(alias_error);
        let query_error = CanonicalAliasQueryError::SymbolFlags(flags_error);

        let flags_source = std::error::Error::source(&query_error).unwrap();
        assert_eq!(
            flags_source.downcast_ref::<CanonicalSymbolFlagsError>(),
            Some(&flags_error)
        );
        let alias_source = flags_source.source().unwrap();
        assert_eq!(
            alias_source.downcast_ref::<CanonicalAliasResolutionError>(),
            Some(&alias_error)
        );
        let leaf_source = alias_source.source().unwrap();
        assert_eq!(
            leaf_source.downcast_ref::<TypeResolutionTargetError>(),
            Some(&leaf)
        );
        assert!(leaf_source.source().is_none());

        let declared_error = DeclaredTypeError::TypeResolutionTarget(leaf);
        assert_eq!(declared_error.to_string(), leaf.to_string());
        assert_eq!(
            std::error::Error::source(&declared_error)
                .unwrap()
                .downcast_ref::<TypeResolutionTargetError>(),
            Some(&leaf)
        );
    }

    #[test]
    fn preserves_explicit_non_map_order_registers_all_roots_and_keeps_store_brand() {
        let low = parsed("interface Low { value: string }");
        let middle = parsed("interface Middle { value: number }");
        let high = parsed("interface High { value: boolean }");
        let low_file = FileId::new(3);
        let middle_file = FileId::new(11);
        let high_file = FileId::new(20);
        let bindings =
            completed_bindings(&[(low_file, &low), (middle_file, &middle), (high_file, &high)]);
        let binder_brand = bindings.symbol_store().id();
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        };

        let context = CanonicalCheckerContext::new(
            bindings,
            vec![
                (high_file, &high.arena),
                (low_file, &low.arena),
                (middle_file, &middle.arena),
            ],
            options,
        )
        .unwrap();

        assert_eq!(context.file_order(), &[high_file, low_file, middle_file]);
        assert_eq!(context.options(), options);
        assert_eq!(context.id(), binder_brand);
        assert_eq!(context.store().id(), binder_brand);

        for (file, arena) in [
            (high_file, &high.arena),
            (low_file, &low.arena),
            (middle_file, &middle.arena),
        ] {
            let (registered_arena, bound) = context.file(file).unwrap();
            assert_eq!(registered_arena.id(), arena.id());
            assert_eq!(bound.file_id(), file);
            assert!(bound.declarations_complete());
            assert!(bound.source_facts().is_some());
            assert_eq!(bound.node_arena_revision(), arena.revision());
            let source = context.source_file(file).unwrap();
            assert_eq!(source.node_ref(), bound.source_file());
            assert!(context.store().contains_source_file(source));
        }

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(bootstrap.options, options.intrinsic);
        assert!(context.store().symbol_table(bootstrap.globals).is_some());
        assert!(
            context
                .store()
                .symbol(bootstrap.global_this_symbol)
                .is_some()
        );
    }

    #[test]
    fn merges_script_globals_skips_external_locals_and_installs_undefined() {
        let first = parsed("interface Shared { left: string } interface Alpha { value: string }");
        let external = parsed("export interface Hidden { value: boolean }");
        let second = parsed("interface Shared { right: number } interface Alpha { other: number }");
        let first_file = FileId::new(101);
        let external_file = FileId::new(102);
        let second_file = FileId::new(103);
        let bindings = completed_bindings_with_facts(&[
            (first_file, &first, false, CanonicalModuleState::Script),
            (
                external_file,
                &external,
                false,
                CanonicalModuleState::External,
            ),
            (second_file, &second, false, CanonicalModuleState::Script),
        ]);
        let context = CanonicalCheckerContext::new(
            bindings,
            vec![
                (first_file, &first.arena),
                (external_file, &external.arena),
                (second_file, &second.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(context.globals(), bootstrap.globals);
        assert_eq!(
            global_symbol(&context, "undefined"),
            Some(bootstrap.undefined_symbol)
        );
        assert!(global_symbol(&context, "Hidden").is_none());

        for name in ["Alpha", "Shared"] {
            let merged = global_symbol(&context, name).unwrap();
            let record = context.store().symbol(merged).unwrap();
            assert!(record.flags().contains(SymbolFlags::INTERFACE));
            assert!(record.flags().contains(SymbolFlags::TRANSIENT));
            let declarations = record.declarations().unwrap();
            assert_eq!(declarations.len(), 2);
            assert_eq!(declarations[0].file, first_file);
            assert_eq!(declarations[1].file, second_file);
        }

        let mut resolver_host = context
            .name_resolver_host(CanonicalNameResolverOptions::default())
            .unwrap();
        assert_eq!(
            resolve_global_name(
                context.store().symbol_store(),
                &mut resolver_host,
                "Shared",
                SymbolFlags::TYPE,
                None,
                false,
                false,
            ),
            Ok(global_symbol(&context, "Shared"))
        );
    }

    #[test]
    fn defers_quoted_ambient_modules_and_retains_patterns_in_stable_order() {
        let source = parsed(
            r#"
declare module "z" { export interface Z {} }
declare module "*.css" { const classes: object; export = classes; }
declare module "a" { export interface A {} }
interface Visible {}
"#,
        );
        let file = FileId::new(104);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[(file, &source, true, CanonicalModuleState::Script)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        assert!(global_symbol(&context, "Visible").is_some());
        for name in ["\"*.css\"", "\"a\"", "\"z\""] {
            assert!(global_symbol(&context, name).is_none());
        }
        let pending_names = context
            .pending_ambient_modules()
            .iter()
            .map(|symbol| {
                context
                    .store()
                    .symbol(*symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned()
            })
            .collect::<Vec<_>>();
        assert_eq!(pending_names, ["\"*.css\"", "\"a\"", "\"z\""]);
        assert_eq!(context.pattern_ambient_modules().len(), 1);
        assert_eq!(context.pattern_ambient_modules()[0].pattern(), "*.css");
        assert_eq!(
            context.pattern_ambient_modules()[0].symbol(),
            context.pending_ambient_modules()[0]
        );
    }

    #[test]
    fn inserts_umd_exports_first_in_wins_without_overwriting_script_globals() {
        let script = parsed("interface Occupied { script: true }");
        let first =
            parsed("export as namespace SharedUmd; export as namespace Occupied; export {};");
        let second = parsed("export as namespace SharedUmd; export {};");
        let script_file = FileId::new(105);
        let first_file = FileId::new(106);
        let second_file = FileId::new(107);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[
                (script_file, &script, true, CanonicalModuleState::Script),
                (first_file, &first, true, CanonicalModuleState::External),
                (second_file, &second, true, CanonicalModuleState::External),
            ]),
            vec![
                (script_file, &script.arena),
                (first_file, &first.arena),
                (second_file, &second.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let (_, first_bound) = context.file(first_file).unwrap();
        let first_exports = context
            .store()
            .symbol_table(first_bound.global_exports().unwrap())
            .unwrap();
        assert_eq!(
            global_symbol(&context, "SharedUmd"),
            first_exports.get_source("SharedUmd")
        );
        assert_ne!(
            global_symbol(&context, "Occupied"),
            first_exports.get_source("Occupied")
        );
        assert!(
            context
                .store()
                .symbol(global_symbol(&context, "Occupied").unwrap())
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE)
        );
    }

    #[test]
    fn merges_global_augmentations_once_and_leaves_nonglobal_augmentations_pending() {
        let source = parsed(
            r#"
export {};
declare global { interface Augmented { first: string } }
declare module "pkg" { interface NotGlobal {} }
declare global { interface Augmented { second: number } }
"#,
        );
        let file = FileId::new(108);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[(file, &source, true, CanonicalModuleState::External)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let augmented = global_symbol(&context, "Augmented").unwrap();
        assert_eq!(
            context
                .store()
                .symbol(augmented)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2
        );
        assert!(global_symbol(&context, "NotGlobal").is_none());
        assert_eq!(
            context.file(file).unwrap().1.module_augmentations().len(),
            3
        );
    }

    #[test]
    fn undefined_preserves_type_only_globals_and_rejects_value_declarations() {
        // The grammar reports TS2427 for this reserved interface name, but the
        // pinned checker still classifies the recovered declaration as
        // type-only and must not add a second TS2397-style conflict.
        let type_only = parse_source_file("interface undefined { marker: true }");
        assert_eq!(
            type_only
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2427]
        );
        let type_file = FileId::new(109);
        let type_context = CanonicalCheckerContext::new(
            completed_bindings(&[(type_file, &type_only)]),
            vec![(type_file, &type_only.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let bootstrap_undefined = type_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_symbol;
        let global_undefined = global_symbol(&type_context, "undefined").unwrap();
        assert_ne!(global_undefined, bootstrap_undefined);
        assert!(
            type_context
                .store()
                .symbol(global_undefined)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE)
        );

        let value = parsed("var undefined: number;");
        let value_file = FileId::new(110);
        let error = CanonicalCheckerContext::new(
            completed_bindings(&[(value_file, &value)]),
            vec![(value_file, &value.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        let CanonicalCheckerContextError::GlobalInitialization(
            CanonicalGlobalInitializationError::UndefinedValueDeclaration(declaration),
        ) = error
        else {
            panic!("unexpected error: {error:?}");
        };
        assert_eq!(declaration.file, value_file);
        assert_eq!(
            value.arena.get(declaration.node).unwrap().kind,
            SyntaxKind::VariableDeclaration
        );

        let augmentation = parsed("export {}; declare global { var undefined: number; }");
        let augmentation_file = FileId::new(111);
        let augmentation_error = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[(
                augmentation_file,
                &augmentation,
                true,
                CanonicalModuleState::External,
            )]),
            vec![(augmentation_file, &augmentation.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(
            augmentation_error,
            CanonicalCheckerContextError::GlobalInitialization(
                CanonicalGlobalInitializationError::UndefinedValueDeclaration(_)
            )
        ));
    }

    #[test]
    fn script_global_this_requires_diagnostics_while_external_locals_are_ignored() {
        let script = parsed("var globalThis: number;");
        let script_file = FileId::new(112);
        let error = CanonicalCheckerContext::new(
            completed_bindings(&[(script_file, &script)]),
            vec![(script_file, &script.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        let CanonicalCheckerContextError::GlobalInitialization(
            CanonicalGlobalInitializationError::ScriptGlobalThisDeclaration { file, declaration },
        ) = error
        else {
            panic!("unexpected error: {error:?}");
        };
        assert_eq!(file, script_file);
        assert_eq!(declaration.file, script_file);

        let external = parsed("export {}; declare const globalThis: number;");
        let external_file = FileId::new(113);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[(
                external_file,
                &external,
                true,
                CanonicalModuleState::External,
            )]),
            vec![(external_file, &external.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        assert_eq!(
            global_symbol(&context, "globalThis"),
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .global_this_symbol
            )
        );
    }

    #[test]
    fn escaped_byte_iteration_deterministically_orders_transient_global_merges() {
        let first = parsed("interface z {} interface a {}");
        let second = parsed("interface z {} interface a {}");
        let first_file = FileId::new(114);
        let second_file = FileId::new(115);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &first.arena), (second_file, &second.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let repeated = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &first.arena), (second_file, &second.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        assert_eq!(
            normalized_global_and_redirect_snapshot(&context),
            normalized_global_and_redirect_snapshot(&repeated)
        );

        let a = global_symbol(&context, "a").unwrap();
        let z = global_symbol(&context, "z").unwrap();
        assert!(a.get() < z.get());
        assert!(
            context
                .store()
                .symbol(a)
                .unwrap()
                .flags()
                .contains(SymbolFlags::TRANSIENT)
        );
        assert!(
            context
                .store()
                .symbol(z)
                .unwrap()
                .flags()
                .contains(SymbolFlags::TRANSIENT)
        );
    }

    #[test]
    fn augmentation_name_mutation_is_rejected_by_the_bound_arena_revision() {
        let mut source = parsed("export {}; declare global { interface Stale {} }");
        let file = FileId::new(116);
        let bindings =
            completed_bindings_with_facts(&[(file, &source, true, CanonicalModuleState::External)]);
        let bound = bindings.file(file).unwrap();
        let expected = bound.node_arena_revision();
        let augmentation_name = bound.module_augmentations()[0].name();
        let NodeData::Identifier(identifier) = &mut source
            .arena
            .get_mut(augmentation_name.node)
            .expect("retained augmentation name exists")
            .data
        else {
            panic!("global augmentation name is an identifier");
        };
        identifier.text = "staleGlobal".to_owned();
        let actual = source.arena.revision();

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            error,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn initializes_real_bundled_es5_core_and_iterator_global_augmentation() {
        let es5 = parsed(include_str!("../../../ts_bundled/libs/lib.es5.d.ts"));
        let core = parsed(include_str!(
            "../../../ts_bundled/libs/lib.es2015.core.d.ts"
        ));
        let iterator = parsed(include_str!(
            "../../../ts_bundled/libs/lib.es2025.iterator.d.ts"
        ));
        let es5_file = FileId::new(117);
        let core_file = FileId::new(118);
        let iterator_file = FileId::new(119);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[
                (es5_file, &es5, true, CanonicalModuleState::Script),
                (core_file, &core, true, CanonicalModuleState::Script),
                (
                    iterator_file,
                    &iterator,
                    true,
                    CanonicalModuleState::External,
                ),
            ]),
            vec![
                (es5_file, &es5.arena),
                (core_file, &core.arena),
                (iterator_file, &iterator.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        for name in [
            "Array",
            "Function",
            "Object",
            "Promise",
            "IteratorObject",
            "Iterator",
        ] {
            assert!(global_symbol(&context, name).is_some(), "missing {name}");
        }
        assert_eq!(
            context
                .file(iterator_file)
                .unwrap()
                .1
                .module_augmentations()
                .len(),
            1
        );

        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = context.global_types();
        assert!(globals.diagnostics().is_empty());
        assert_eq!(
            store
                .value_symbol_links(bootstrap.arguments_symbol)
                .unwrap()
                .resolved_type,
            Some(globals.arguments_type)
        );
        assert_eq!(
            store
                .value_symbol_links(bootstrap.undefined_symbol)
                .unwrap()
                .resolved_type,
            Some(bootstrap.undefined_widening_type)
        );
        assert_eq!(
            store
                .value_symbol_links(bootstrap.unknown_symbol)
                .unwrap()
                .resolved_type,
            Some(bootstrap.error_type)
        );
        assert_eq!(
            store
                .value_symbol_links(bootstrap.global_this_symbol)
                .unwrap()
                .resolved_type,
            Some(globals.global_this_value_type)
        );
        let global_this = store.type_payload(globals.global_this_value_type).unwrap();
        assert_eq!(global_this.symbol(), Some(bootstrap.global_this_symbol));
        assert_eq!(global_this.object_flags(), ObjectFlags::ANONYMOUS);
        let TypeData::Interface(object) = store.type_payload(globals.object_type).unwrap().data()
        else {
            panic!("global Object must be an interface origin")
        };
        assert!(object.base_types_resolved);
        assert!(object.resolved_base_constructor_type.is_none());
        assert!(object.resolved_base_types.is_none());

        for (name, type_id) in [
            ("IArguments", globals.arguments_type),
            ("Array", globals.array_type),
            ("Object", globals.object_type),
            ("Function", globals.function_type),
            ("String", globals.string_type),
            ("Number", globals.number_type),
            ("Boolean", globals.boolean_type),
            ("RegExp", globals.regexp_type),
            ("ReadonlyArray", globals.readonly_array_type),
            ("ThisType", globals.this_type),
        ] {
            let symbol = global_symbol(&context, name).unwrap();
            assert_eq!(
                store.declared_type_links(symbol).unwrap().declared_type,
                Some(type_id),
                "wrong declared identity for {name}"
            );
        }
        assert_eq!(globals.callable_function_type, globals.function_type);
        assert_eq!(globals.newable_function_type, globals.function_type);
        assert!(
            store
                .declared_type_links(global_symbol(&context, "CallableFunction").unwrap())
                .is_none()
        );
        assert!(
            store
                .declared_type_links(global_symbol(&context, "NewableFunction").unwrap())
                .is_none()
        );

        let TypeData::TypeReference(any_array) =
            store.type_payload(globals.any_array_type).unwrap().data()
        else {
            panic!("Array<any> must be a canonical reference")
        };
        assert_eq!(any_array.object.target, Some(globals.array_type));
        assert_eq!(
            any_array.resolved_type_arguments.as_deref(),
            Some(&[bootstrap.any_type][..])
        );
        let TypeData::TypeReference(auto_array) =
            store.type_payload(globals.auto_array_type).unwrap().data()
        else {
            panic!("Array<auto> must be a canonical reference")
        };
        assert_eq!(auto_array.object.target, Some(globals.array_type));
        assert_eq!(
            auto_array.resolved_type_arguments.as_deref(),
            Some(&[bootstrap.auto_type][..])
        );
        assert!(
            store
                .type_payload(globals.auto_array_type)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::NON_INFERRABLE_TYPE)
        );
        let TypeData::Interface(array) = store.type_payload(globals.array_type).unwrap().data()
        else {
            panic!("global Array must be an interface origin")
        };
        let TypeCacheState::Allocated(array_instantiations) =
            &array.reference.object.instantiations
        else {
            panic!("global Array must own its instantiation cache")
        };
        assert!(
            array_instantiations
                .values()
                .any(|id| *id == globals.any_array_type)
        );
        assert!(
            array_instantiations
                .values()
                .any(|id| *id == globals.auto_array_type)
        );

        let TypeData::TypeReference(any_readonly_array) = store
            .type_payload(globals.any_readonly_array_type)
            .unwrap()
            .data()
        else {
            panic!("ReadonlyArray<any> must be a canonical reference")
        };
        assert_eq!(
            any_readonly_array.object.target,
            Some(globals.readonly_array_type)
        );
        assert_eq!(
            any_readonly_array.resolved_type_arguments.as_deref(),
            Some(&[bootstrap.any_type][..])
        );
    }

    #[test]
    fn strict_bind_call_apply_selects_distinct_es5_function_interfaces() {
        let es5 = parsed(include_str!("../../../ts_bundled/libs/lib.es5.d.ts"));
        let file = FileId::new(120);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[(file, &es5, true, CanonicalModuleState::Script)]),
            vec![(file, &es5.arena)],
            CanonicalCheckerOptions {
                strict_bind_call_apply: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let globals = context.global_types();
        assert!(globals.diagnostics().is_empty());
        assert_ne!(globals.callable_function_type, globals.function_type);
        assert_ne!(globals.newable_function_type, globals.function_type);
        assert_ne!(
            globals.callable_function_type,
            globals.newable_function_type
        );
        for (name, type_id) in [
            ("Function", globals.function_type),
            ("CallableFunction", globals.callable_function_type),
            ("NewableFunction", globals.newable_function_type),
        ] {
            let symbol = global_symbol(&context, name).unwrap();
            assert_eq!(
                context
                    .store()
                    .declared_type_links(symbol)
                    .unwrap()
                    .declared_type,
                Some(type_id)
            );
            let TypeData::Interface(interface) =
                context.store().type_payload(type_id).unwrap().data()
            else {
                panic!("{name} must be an interface identity")
            };
            assert!(interface.all_type_parameters.is_none());
            assert!(interface.this_type.is_none());
            assert!(!interface.base_types_resolved);
            assert!(interface.resolved_base_types.is_none());
        }
    }

    #[test]
    fn missing_optional_readonly_array_reuses_array_and_its_any_instantiation() {
        let source = parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             interface Object {}\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        );
        let file = FileId::new(123);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let globals = context.global_types();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert!(globals.diagnostics().is_empty());
        assert_eq!(globals.readonly_array_type, globals.array_type);
        assert_eq!(globals.any_readonly_array_type, globals.any_array_type);
        assert_eq!(globals.this_type, bootstrap.empty_generic_type);
    }

    #[test]
    fn merged_global_object_interfaces_without_heritage_publish_no_base_fact() {
        let core = parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             interface Object { first: string }\n\
             declare var Object: { prototype: Object };\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        );
        let augmentation = parsed("interface Object { second: number }");
        let core_file = FileId::new(124);
        let augmentation_file = FileId::new(125);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(core_file, &core), (augmentation_file, &augmentation)]),
            vec![
                (core_file, &core.arena),
                (augmentation_file, &augmentation.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let object_symbol = global_symbol(&context, "Object").unwrap();
        assert_eq!(
            context
                .store()
                .symbol(object_symbol)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            3
        );
        let object_type = context.global_types().object_type;
        let TypeData::Interface(object) = context.store().type_payload(object_type).unwrap().data()
        else {
            panic!("global Object must be an interface origin")
        };
        assert!(object.base_types_resolved);
        assert!(object.resolved_base_constructor_type.is_none());
        assert!(object.resolved_base_types.is_none());
    }

    #[test]
    fn non_generic_global_object_with_this_type_still_publishes_no_base_fact() {
        let source = parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             interface Object { identity(): this }\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        );
        let file = FileId::new(133);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let object_type = context.global_types().object_type;
        let snapshot = interface_base_snapshot(&context, object_type);
        assert!(snapshot.0);
        assert_eq!(snapshot.1, None);
        assert_eq!(snapshot.2, None);
        assert!(
            snapshot
                .3
                .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        );
    }

    #[test]
    fn global_object_interface_with_heritage_leaves_base_resolution_cold() {
        let source = heritage_global_library();
        let file = FileId::new(126);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let object_type = context.global_types().object_type;
        let TypeData::Interface(object) = context.store().type_payload(object_type).unwrap().data()
        else {
            panic!("global Object must be an interface origin")
        };
        assert!(!object.base_types_resolved);
        assert!(object.resolved_base_constructor_type.is_none());
        assert!(object.resolved_base_types.is_none());
    }

    #[test]
    fn heritage_object_warm_nil_base_cache_is_typed_and_mutation_free() {
        let source = heritage_global_library();
        let file = FileId::new(131);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let object_type = context.global_types().object_type;
        {
            let store = context.store_mut_for_test();
            assert!(store.set_interface_base_resolution(object_type, true, None, None));
            assert!(store.set_structured_type_members(object_type, None, None, None, None, None,));
        }
        let before = interface_base_snapshot(&context, object_type);
        assert!(before.0);
        assert_eq!(before.1, None);
        assert_eq!(before.2, None);
        assert!(before.3.contains(ObjectFlags::MEMBERS_RESOLVED));

        assert_eq!(
            reinitialize_global_library_types(&mut context),
            Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                )
            )
        );
        assert_eq!(interface_base_snapshot(&context, object_type), before);
    }

    #[test]
    fn resolved_heritage_object_with_nonempty_bases_is_preserved() {
        let source = heritage_global_library();
        let file = FileId::new(132);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let object_type = context.global_types().object_type;
        let base_symbol = global_symbol(&context, "ObjectBase").unwrap();
        let base_type = context.get_declared_type_of_symbol(base_symbol).unwrap();
        {
            let store = context.store_mut_for_test();
            assert!(store.set_interface_base_resolution(
                object_type,
                true,
                None,
                Some(vec![base_type]),
            ));
            assert!(store.set_structured_type_members(object_type, None, None, None, None, None,));
        }
        let before = interface_base_snapshot(&context, object_type);
        assert!(before.0);
        assert_eq!(before.1, None);
        assert_eq!(before.2.as_deref(), Some([base_type].as_slice()));
        assert!(before.3.contains(ObjectFlags::MEMBERS_RESOLVED));

        let globals = reinitialize_global_library_types(&mut context).unwrap();
        assert_eq!(globals.object_type, object_type);
        assert_eq!(interface_base_snapshot(&context, object_type), before);
    }

    #[test]
    fn global_object_class_is_not_used_as_no_base_interface_proof() {
        let source = parsed(
            "interface IArguments {}\n\
             interface Array<T> {}\n\
             class Object {}\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        );
        let file = FileId::new(130);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let object_type = context.global_types().object_type;
        let snapshot = interface_base_snapshot(&context, object_type);
        assert!(!snapshot.0);
        assert_eq!(snapshot.1, None);
        assert_eq!(snapshot.2, None);
        assert!(snapshot.3.contains(ObjectFlags::CLASS));
    }

    #[test]
    fn warm_global_object_no_base_cache_retains_resolved_members() {
        let source = minimal_global_library();
        let file = FileId::new(127);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let object_type = context.global_types().object_type;
        assert!(context.store_mut_for_test().set_structured_type_members(
            object_type,
            None,
            None,
            None,
            None,
            None,
        ));
        let before = interface_base_snapshot(&context, object_type);
        assert!(before.0);
        assert_eq!(before.1, None);
        assert_eq!(before.2, None);
        assert!(before.3.contains(ObjectFlags::MEMBERS_RESOLVED));

        let globals = reinitialize_global_library_types(&mut context).unwrap();
        assert_eq!(globals.object_type, object_type);
        assert_eq!(interface_base_snapshot(&context, object_type), before);
    }

    #[test]
    fn later_global_type_failure_does_not_publish_preflighted_object_bases() {
        let source = minimal_global_library();
        let file = FileId::new(128);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let object_type = context.global_types().object_type;
        let function_symbol = global_symbol(&context, "Function").unwrap();
        let any_type = context.store().intrinsic_bootstrap().unwrap().any_type;
        {
            let store = context.store_mut_for_test();
            assert!(store.set_interface_base_resolution(object_type, false, None, None));
            assert!(store.set_structured_type_members(object_type, None, None, None, None, None,));
            let mut links = store.declared_type_links(function_symbol).unwrap().clone();
            links.declared_type = Some(any_type);
            assert!(store.set_declared_type_links(function_symbol, links));
        }
        let before = interface_base_snapshot(&context, object_type);
        assert!(!before.0);
        assert_eq!(before.1, None);
        assert_eq!(before.2, None);
        assert!(before.3.contains(ObjectFlags::MEMBERS_RESOLVED));

        let error = reinitialize_global_library_types(&mut context).unwrap_err();
        assert_eq!(
            error,
            CanonicalGlobalTypeInitializationError::DeclaredType(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                    symbol: function_symbol,
                    declared_type: any_type,
                },
            ))
        );
        assert_eq!(interface_base_snapshot(&context, object_type), before);
    }

    #[test]
    fn allocated_empty_global_object_base_cache_is_typed_and_mutation_free() {
        let source = minimal_global_library();
        let file = FileId::new(129);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let object_type = context.global_types().object_type;
        assert!(context.store_mut_for_test().set_interface_base_resolution(
            object_type,
            true,
            None,
            Some(Vec::new()),
        ));
        let before = interface_base_snapshot(&context, object_type);
        assert_eq!(before.2, Some(Vec::new()));

        assert_eq!(
            reinitialize_global_library_types(&mut context),
            Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                )
            )
        );
        assert_eq!(interface_base_snapshot(&context, object_type), before);
    }

    #[test]
    fn missing_global_types_keep_exact_fallbacks_and_diagnostic_order() {
        let source = parsed("");
        let file = FileId::new(121);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = context.global_types();
        let missing = [
            "IArguments",
            "Array",
            "Object",
            "Function",
            "String",
            "Number",
            "Boolean",
            "RegExp",
        ];
        assert_eq!(globals.diagnostics().len(), missing.len());
        for (diagnostic, name) in globals.diagnostics().iter().zip(missing) {
            assert_eq!(diagnostic.node, None);
            assert_eq!(diagnostic.diagnostic.code(), 2318);
            if matches!(name, "Array" | "RegExp" | "String") {
                assert_eq!(diagnostic.diagnostic.arguments, [name, "es2015"]);
            } else {
                assert_eq!(diagnostic.diagnostic.arguments, [name]);
            }
        }
        assert_eq!(globals.arguments_type, bootstrap.empty_object_type);
        assert_eq!(globals.array_type, bootstrap.empty_generic_type);
        assert_eq!(globals.object_type, bootstrap.empty_object_type);
        assert_eq!(globals.function_type, bootstrap.empty_object_type);
        assert_eq!(globals.callable_function_type, globals.function_type);
        assert_eq!(globals.newable_function_type, globals.function_type);
        assert_eq!(globals.any_array_type, bootstrap.empty_object_type);
        assert_ne!(globals.auto_array_type, bootstrap.empty_object_type);
        assert_eq!(
            store
                .type_payload(globals.auto_array_type)
                .unwrap()
                .object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        assert_eq!(globals.readonly_array_type, globals.array_type);
        assert_eq!(globals.any_readonly_array_type, bootstrap.empty_object_type);
        assert_eq!(globals.this_type, bootstrap.empty_generic_type);
    }

    #[test]
    fn malformed_required_globals_report_wrong_kind_and_arity_at_declarations() {
        let source = parsed(
            "type IArguments = {};\n\
             interface Array {}\n\
             interface Object<T> {}\n\
             interface Function {}\n\
             interface String {}\n\
             interface Number {}\n\
             interface Boolean {}\n\
             interface RegExp {}",
        );
        let file = FileId::new(122);
        let context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();
        let diagnostics = context.global_types().diagnostics();
        assert_eq!(diagnostics.len(), 3);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2316, 2317, 2317]
        );
        assert_eq!(diagnostics[0].diagnostic.arguments, ["IArguments"]);
        assert_eq!(diagnostics[1].diagnostic.arguments, ["Array", "1"]);
        assert_eq!(diagnostics[2].diagnostic.arguments, ["Object", "0"]);
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.node.is_some())
        );
    }

    #[test]
    fn rejects_missing_duplicate_and_extra_order_entries() {
        let first = parsed("interface First {}");
        let second = parsed("interface Second {}");
        let foreign = parsed("interface Foreign {}");
        let first_file = FileId::new(1);
        let second_file = FileId::new(2);
        let foreign_file = FileId::new(99);

        let missing = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &first.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            missing,
            CanonicalCheckerContextError::MissingOrderedFile(second_file)
        );

        let duplicate = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first)]),
            vec![(first_file, &first.arena), (first_file, &first.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            duplicate,
            CanonicalCheckerContextError::DuplicateFileInOrder(first_file)
        );

        let extra = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first)]),
            vec![(first_file, &first.arena), (foreign_file, &foreign.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            extra,
            CanonicalCheckerContextError::ExtraOrderedFile(foreign_file)
        );
    }

    #[test]
    fn rejects_duplicate_swapped_and_foreign_arena_identities() {
        let first = parsed("interface First {}");
        let second = parsed("interface Second {}");
        let foreign = parsed("interface Foreign {}");
        let first_file = FileId::new(7);
        let second_file = FileId::new(8);

        let duplicate = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &first.arena), (second_file, &first.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            duplicate,
            CanonicalCheckerContextError::DuplicateArenaInOrder {
                arena: first.arena.id(),
                first_file,
                second_file,
            }
        );

        let swapped = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &second.arena), (second_file, &first.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            swapped,
            CanonicalCheckerContextError::ArenaMismatch {
                file: first_file,
                expected: first.arena.id(),
                actual: second.arena.id(),
            }
        );

        let foreign_error = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first)]),
            vec![(first_file, &foreign.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            foreign_error,
            CanonicalCheckerContextError::ArenaMismatch {
                file: first_file,
                expected: first.arena.id(),
                actual: foreign.arena.id(),
            }
        );
    }

    #[test]
    fn rejects_incomplete_declaration_extraction_before_checker_construction() {
        let source = parsed("interface Pending {}");
        let file = FileId::new(30);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                source_facts(file),
            )
            .unwrap();

        let error = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            error,
            CanonicalCheckerContextError::Extraction(
                CanonicalExtractionError::DeclarationsIncomplete
            )
        );
    }

    #[test]
    fn preflights_exact_source_root_kind_and_parent() {
        let mut wrong_kind = parsed("interface Kind {}");
        let kind_file = FileId::new(40);
        let kind_bindings = completed_bindings(&[(kind_file, &wrong_kind)]);
        wrong_kind
            .arena
            .get_mut(wrong_kind.source_file)
            .unwrap()
            .kind = SyntaxKind::Block;
        let kind_error = CanonicalCheckerContext::new(
            kind_bindings,
            vec![(kind_file, &wrong_kind.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            kind_error,
            CanonicalCheckerContextError::InvalidSourceFileRoot {
                source: NodeRef::new(wrong_kind.arena.id(), kind_file, wrong_kind.source_file),
                kind: SyntaxKind::Block,
            }
        );

        let mut parented = parsed("interface Parented {}");
        let parent_file = FileId::new(41);
        let parent_bindings = completed_bindings(&[(parent_file, &parented)]);
        let invalid_parent = parented.source_file;
        parented.arena.get_mut(parented.source_file).unwrap().parent = Some(invalid_parent);
        let parent_error = CanonicalCheckerContext::new(
            parent_bindings,
            vec![(parent_file, &parented.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            parent_error,
            CanonicalCheckerContextError::SourceFileHasParent {
                source: NodeRef::new(parented.arena.id(), parent_file, parented.source_file),
                parent: invalid_parent,
            }
        );
    }

    #[test]
    fn same_closure_parent_mutation_is_rejected_before_checker_construction() {
        let first = parsed("interface First { value: string }");
        let mut malformed = parsed("interface Malformed { value: number }");
        let first_file = FileId::new(50);
        let malformed_file = FileId::new(51);
        let bindings = completed_bindings(&[(first_file, &first), (malformed_file, &malformed)]);
        let expected = bindings.file(malformed_file).unwrap().node_arena_revision();
        let malformed_child = malformed
            .arena
            .iter()
            .find_map(|(node, data)| {
                (node != malformed.source_file && data.parent.is_some()).then_some(node)
            })
            .unwrap();
        malformed.arena.get_mut(malformed_child).unwrap().parent = None;
        let actual = malformed.arena.revision();

        let result = CanonicalCheckerContext::new(
            bindings,
            vec![
                (first_file, &first.arena),
                (malformed_file, &malformed.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        );

        assert_eq!(
            result.unwrap_err(),
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file: malformed_file,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn rejects_same_closure_identifier_text_mutation_after_binding() {
        let mut source = parsed("interface Before { value: string }");
        let file = FileId::new(60);
        let bindings = completed_bindings(&[(file, &source)]);
        let expected = bindings.file(file).unwrap().node_arena_revision();
        let identifier = source
            .arena
            .iter()
            .find_map(|(node, data)| {
                matches!(
                    &data.data,
                    NodeData::Identifier(identifier) if identifier.text == "Before"
                )
                .then_some(node)
            })
            .unwrap();
        let NodeData::Identifier(identifier_data) =
            &mut source.arena.get_mut(identifier).unwrap().data
        else {
            panic!("the selected node is an identifier");
        };
        identifier_data.text = "After".to_owned();
        let actual = source.arena.revision();

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            error,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn rejects_source_text_mutation_after_binding() {
        let mut source = parsed("interface Before {}");
        let file = FileId::new(61);
        let bindings = completed_bindings(&[(file, &source)]);
        let expected = bindings.file(file).unwrap().node_arena_revision();
        source.arena.set_source_text("interface After {}");
        let actual = source.arena.revision();

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            error,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn rejects_unreachable_allocation_after_binding() {
        let mut source = parsed("; interface Retained {}");
        let file = FileId::new(62);
        let bindings = completed_bindings(&[(file, &source)]);
        let expected = bindings.file(file).unwrap().node_arena_revision();
        let _unreachable = allocate_unattached_empty_statement(&mut source);
        let actual = source.arena.revision();

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            error,
            CanonicalCheckerContextError::ArenaRevisionMismatch {
                file,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn rejects_a_formerly_bound_statement_removed_from_the_root_closure() {
        let mut source = parsed("interface Removed {} interface Retained {}");
        let file = FileId::new(70);
        let removed = {
            let NodeData::SourceFile(data) = &source
                .arena
                .get(source.source_file)
                .expect("the parser source root exists")
                .data
            else {
                panic!("the parser source root has SourceFile data");
            };
            data.statements.nodes[0]
        };
        let bindings = completed_bindings(&[(file, &source)]);
        source_statements_mut(&mut source).retain(|statement| *statement != removed);

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            error,
            CanonicalCheckerContextError::BoundNodeNowUnreachable(NodeRef::new(
                source.arena.id(),
                file,
                removed,
            ))
        );
    }

    #[test]
    fn rejects_a_formerly_unreachable_valid_node_attached_to_the_root_closure() {
        let mut source = parsed("; interface Retained {}");
        let file = FileId::new(71);
        let formerly_unreachable = allocate_unattached_empty_statement(&mut source);
        let still_unreachable = allocate_unattached_empty_statement(&mut source);
        let bindings = completed_bindings(&[(file, &source)]);
        source_statements_mut(&mut source).push(formerly_unreachable);

        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap_err();

        assert_eq!(
            error,
            CanonicalCheckerContextError::NewlyReachableUnboundNode(NodeRef::new(
                source.arena.id(),
                file,
                formerly_unreachable,
            ))
        );
        assert_ne!(formerly_unreachable, still_unreachable);
    }

    #[test]
    fn permits_unreachable_arena_slots_outside_both_closures() {
        let mut source = parsed("; interface Retained {}");
        let file = FileId::new(72);
        let orphan = allocate_unattached_empty_statement(&mut source);
        let bindings = completed_bindings(&[(file, &source)]);

        let context = CanonicalCheckerContext::new(
            bindings,
            vec![(file, &source.arena)],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        assert!(
            context
                .store()
                .contains_node_ref(NodeRef::new(source.arena.id(), file, orphan))
        );
        assert!(!context.file(file).unwrap().1.contains(NodeRef::new(
            source.arena.id(),
            file,
            orphan,
        )));
    }
}
