//! Production construction boundary for the canonical checker core.
//!
//! This module adopts declaration-complete canonical binder output into one
//! checker-owned semantic store. Construction includes the dependency-closed
//! prefix of typescript-go's `initializeChecker`: ordered global merging,
//! post-library ambient-module merging, UMD globals, global-scope
//! augmentations, named ambient-module and star-reexport augmentations, the
//! built-in `undefined` conflict rule, intrinsic value links, and eager
//! standard-library type identities. Module merges use the existing alias
//! resolver and diagnostic host. Other unavailable module targets remain typed
//! boundaries.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

use ts_ast::{
    FileId, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalExtractionError, CanonicalNameResolverOptions,
    CanonicalPatternAmbientModule, CanonicalProgramBindings, CheckFlags, EscapedName,
    InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags, SymbolStore, SymbolTableId,
};

use super::{
    AssignabilityErrorDisplay, CanonicalCheckerDiagnostics, CanonicalEnumSemantics,
    CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes, CanonicalModuleResolutionLookup,
    CanonicalModuleResolutionManifest, CanonicalModuleResolutionManifestError,
    CanonicalModuleResolutionManifestInput, CanonicalTypeFormatFlags, CanonicalTypeMapperStore,
    CanonicalUnionPropertyError, ClassError, ClassMembers, ClassShells, DeclaredTypeError,
    DeclaredTypeHost, DeclaredTypeHostError, IntrinsicBootstrapError, IntrinsicBootstrapOptions,
    RelationUnavailable, ResolvedUnionProperty, SignatureId, SourceCheckError,
    SourceCheckProvenanceError, SourceFileRef, SymbolMergeError, TypeDisplayUnavailable, TypeId,
    alias::{
        CanonicalAliasResolution, CanonicalAliasResolutionError, CanonicalAliasResolver,
        CanonicalAliasTargetHost, CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
    alias_flags::{
        CanonicalSymbolFlagsError, CanonicalSymbolFlagsResolution, CanonicalSymbolFlagsResolver,
    },
    alias_provider::{
        ProductionAliasSourceRegistry, ProductionAliasTargetHost, ProductionAliasTargetHostError,
    },
    classes::{
        ClassTypeQueryContext, execute_nongeneric_class_member_query,
        execute_nongeneric_class_shells, plan_nongeneric_class,
        plan_nongeneric_class_member_query_with_type_context,
    },
    global_types::initialize_global_library_types,
    instantiate::{InstantiationLimits, InstantiationSession},
    merge::{
        CheckerDiagnosticMergeHost, DuplicatePrimaryArguments, SymbolMergeDiagnostic,
        SymbolMergeDiagnosticKind, SymbolMergeHost,
    },
    module_resolution::validate_module_resolution_manifest,
    name_resolution::{ProductionNameResolverHost, ProductionNameResolverHostError},
    relater::SourceRelationError,
    relation::RelationKind,
    source,
    source_imports::{SourceClassImportDemand, SourceClassImportPlan, resolve_source_class_import},
    symbol_display::{SymbolDisplayContext, SymbolDisplayError},
    type_nodes::CanonicalTypeQuery,
    types::{ObjectFlags, TypeFlags},
};

/// JSX runtime behavior retained from the compiler's emit setting.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CanonicalJsxRuntime {
    /// JSX stays unchanged and does not require a runtime factory.
    #[default]
    Preserve,
    /// Classic JSX requires the `React` factory to be in scope.
    Classic,
    /// Automatic JSX requires the `react/jsx-runtime` module.
    Automatic,
}

/// Exact per-source JSX runtime facts supplied by the compiler.
///
/// Names are borrowed only while the source is checked. A resolved automatic
/// module must be an external-module symbol owned by the checker context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalJsxRuntimeEvidence<'source> {
    /// JSX remains unchanged and does not require a runtime.
    Preserve,
    /// Classic element and fragment factories resolve independently.
    Classic {
        factory_namespace: &'source str,
        fragment_factory_namespace: &'source str,
        fragment_factory_required: bool,
        fragment_factory_pragma_required: bool,
    },
    /// The named automatic module is either resolved or proven absent.
    Automatic {
        module_specifier: &'source str,
        resolved_module: Option<SemanticSymbolId>,
    },
}

impl CanonicalJsxRuntimeEvidence<'_> {
    const fn mode(self) -> CanonicalJsxRuntime {
        match self {
            Self::Preserve => CanonicalJsxRuntime::Preserve,
            Self::Classic { .. } => CanonicalJsxRuntime::Classic,
            Self::Automatic { .. } => CanonicalJsxRuntime::Automatic,
        }
    }
}

/// Import-call forms allowed by the configured module emit kind.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CanonicalImportCallMode {
    Unsupported,
    #[default]
    Dynamic,
    DynamicWithAttributes,
    Deferred,
}

/// Compiler options consumed by the installed production-construction slice.
///
/// The intrinsic pair controls bootstrap identity. `strict_bind_call_apply`
/// selects the pinned `CallableFunction`/`NewableFunction` globals instead of
/// aliasing both fields to `Function`. `strict_builtin_iterator_return` is
/// retained for declared type-alias construction. `strict_function_types` is
/// retained as immutable context state for signature relation queries.
/// `strict_property_initialization` controls the narrow source class-field
/// admission check when intrinsic strict-null identity is also enabled.
/// `no_implicit_any` controls diagnostics and evolving inference for
/// unannotated declarations.
/// `no_implicit_this` retains the effective option for untyped `this` reads.
/// `no_unchecked_indexed_access` includes `undefined` in unchecked index
/// signature reads when strict null checking makes that distinction observable.
/// `no_unused_locals` enables diagnostics for unreferenced local declarations.
/// `no_unused_parameters` enables diagnostics for unread named parameters.
/// `allow_unreachable_code` preserves whether unreachable-code diagnostics were
/// explicitly enabled, explicitly suppressed, or left at their default.
/// `preserve_const_enums` retains const enums as executable declarations.
/// `isolated_modules` enables per-file module restrictions.
/// `jsx_runtime` retains classic or automatic JSX factory requirements.
/// `emit_common_js` and `no_emit` preserve the emission conditions needed for
/// module-scope reserved-name diagnostics.
/// `import_call_mode` retains dynamic and deferred import grammar restrictions.
/// `uses_wildcard_types` selects the upstream missing-type-definition message.
/// `no_error_truncation` raises semantic type display to the pinned hard output
/// cutoff.
/// `check_bigint_target` enables runtime bigint grammar and exponentiation
/// checks against the configured language target.
/// `use_unknown_in_catch_variables` retains the effective catch-variable option.
#[allow(clippy::struct_excessive_bools)] // Flat immutable compiler-option projection.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CanonicalCheckerOptions {
    pub intrinsic: IntrinsicBootstrapOptions,
    pub strict_bind_call_apply: bool,
    pub strict_builtin_iterator_return: bool,
    pub strict_function_types: bool,
    pub strict_property_initialization: bool,
    pub use_unknown_in_catch_variables: bool,
    pub no_implicit_any: bool,
    pub no_implicit_this: bool,
    pub no_unchecked_indexed_access: bool,
    pub no_unused_locals: bool,
    pub no_unused_parameters: bool,
    pub allow_unreachable_code: Option<bool>,
    pub preserve_const_enums: bool,
    pub isolated_modules: bool,
    pub jsx_runtime: CanonicalJsxRuntime,
    pub emit_common_js: bool,
    pub module_kind: ts_options::ModuleKind,
    pub import_call_mode: CanonicalImportCallMode,
    pub no_emit: bool,
    pub uses_wildcard_types: bool,
    pub no_error_truncation: bool,
    pub check_bigint_target: bool,
    pub name_resolution: CanonicalNameResolverOptions,
}

impl From<IntrinsicBootstrapOptions> for CanonicalCheckerOptions {
    fn from(intrinsic: IntrinsicBootstrapOptions) -> Self {
        Self {
            intrinsic,
            strict_bind_call_apply: false,
            strict_builtin_iterator_return: false,
            strict_function_types: false,
            strict_property_initialization: false,
            use_unknown_in_catch_variables: false,
            no_implicit_any: false,
            no_implicit_this: false,
            no_unchecked_indexed_access: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            allow_unreachable_code: None,
            preserve_const_enums: false,
            isolated_modules: false,
            jsx_runtime: CanonicalJsxRuntime::Preserve,
            emit_common_js: false,
            module_kind: ts_options::ModuleKind::None,
            import_call_mode: CanonicalImportCallMode::Dynamic,
            no_emit: false,
            uses_wildcard_types: false,
            no_error_truncation: false,
            check_bigint_target: false,
            name_resolution: CanonicalNameResolverOptions::default(),
        }
    }
}

impl CanonicalCheckerOptions {
    /// Uses the shared module rule with the checker's effective target.
    pub(super) fn effective_module_kind(self) -> ts_options::ModuleKind {
        self.module_kind
            .effective_for_target(self.name_resolution.emit_target)
    }

    pub(super) const fn should_preserve_const_enums(self) -> bool {
        self.preserve_const_enums
            || self.isolated_modules
            || self.name_resolution.isolated_modules
            || self.name_resolution.verbatim_module_syntax
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
    module_display_specifiers: BTreeMap<(FileId, SemanticSymbolId), String>,
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
            if bound
                .source_facts()
                .is_none_or(|facts| !store.register_source_file_facts(source_file, facts))
            {
                return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
            }
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

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut alias_host =
            ProductionAliasTargetHost::from_registry(&store, &files, &module_resolutions)
                .map_err(CanonicalCheckerContextError::AliasTargetHost)?;
        let initialized = initialize_globals(
            &mut store,
            &file_order,
            &files,
            options.strict_bind_call_apply,
            options.name_resolution,
            &mut alias_host,
            &mut diagnostics,
        )
        .map_err(CanonicalCheckerContextError::GlobalInitialization)?;
        merge_reexported_module_augmentations(
            &mut store,
            &file_order,
            &files,
            &module_resolutions,
            &mut alias_host,
            &mut diagnostics,
        )
        .map_err(CanonicalCheckerContextError::GlobalInitialization)?;
        if !store.finalize_native_ambient_module_exports(&files) {
            return Err(CanonicalCheckerContextError::GlobalInitialization(
                CanonicalGlobalInitializationError::InvalidGlobals(initialized.globals),
            ));
        }
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
            module_display_specifiers: BTreeMap::new(),
            diagnostics,
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
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::type_to_string_with_host_global_types_and_flags(
            &self.store,
            &host,
            &self.global_types,
            type_id,
            self.type_format_flags(CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT),
        )
    }

    /// Returns the validated intrinsic name of an `any` type.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign type or an invalid intrinsic payload.
    pub fn intrinsic_any_name(
        &self,
        type_id: TypeId,
    ) -> Result<Option<&str>, TypeDisplayUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(TypeDisplayUnavailable::Type(type_id))?;
        if !record.flags().intersects(TypeFlags::ANY) {
            return Ok(None);
        }
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(TypeDisplayUnavailable::MissingBootstrap)?;
        let expected = [
            (bootstrap.any_type, "any", ObjectFlags::NONE),
            (bootstrap.auto_type, "any", ObjectFlags::NON_INFERRABLE_TYPE),
            (bootstrap.wildcard_type, "any", ObjectFlags::NONE),
            (bootstrap.blocked_string_type, "any", ObjectFlags::NONE),
            (bootstrap.error_type, "error", ObjectFlags::NONE),
            (bootstrap.unresolved_type, "unresolved", ObjectFlags::NONE),
            (
                bootstrap.non_inferrable_any_type,
                "any",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            ),
            (
                bootstrap.intrinsic_marker_type,
                "intrinsic",
                ObjectFlags::NONE,
            ),
        ]
        .into_iter()
        .find_map(|(id, name, flags)| (id == type_id).then_some((name, flags)))
        .ok_or(TypeDisplayUnavailable::MalformedType(type_id))?;
        let super::TypeData::Intrinsic(intrinsic) = record.data() else {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        };
        if record.flags() != TypeFlags::ANY
            || record.object_flags() != expected.1
            || intrinsic.intrinsic_name != expected.0
            || record.symbol().is_some()
            || record.alias().is_some()
        {
            return Err(TypeDisplayUnavailable::MalformedType(type_id));
        }
        Ok(Some(&intrinsic.intrinsic_name))
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
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::type_to_string_with_host_global_types_and_flags(
            &self.store,
            &host,
            &self.global_types,
            type_id,
            self.type_format_flags(flags),
        )
    }

    /// Formats a type using names visible at one exact source location.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign nodes, invalid alias caches, or a type
    /// whose exact display is not supported.
    pub fn type_to_string_at_location(
        &mut self,
        type_id: TypeId,
        enclosing: NodeRef,
    ) -> Result<String, TypeDisplayUnavailable> {
        self.type_to_string_at_location_with_flags(
            type_id,
            enclosing,
            CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT,
        )
    }

    /// Formats a type with explicit flags and names visible at `enclosing`.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::type_to_string_at_location`].
    pub fn type_to_string_at_location_with_flags(
        &mut self,
        type_id: TypeId,
        enclosing: NodeRef,
        flags: CanonicalTypeFormatFlags,
    ) -> Result<String, TypeDisplayUnavailable> {
        self.with_display_alias_transaction(|context| {
            context.type_to_string_at_location_worker(type_id, enclosing, flags)
        })
    }

    fn type_to_string_at_location_worker(
        &mut self,
        type_id: TypeId,
        enclosing: NodeRef,
        flags: CanonicalTypeFormatFlags,
    ) -> Result<String, TypeDisplayUnavailable> {
        if self.store.type_payload(type_id).is_none() {
            return Err(TypeDisplayUnavailable::Type(type_id));
        }
        let location = self
            .symbol_display_context(enclosing)
            .map_err(TypeDisplayUnavailable::SymbolDisplay)?;
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(TypeDisplayUnavailable::SourceHost)?;
        super::formatter::type_to_string_at_location_with_flags(
            &self.store,
            &host,
            &self.global_types,
            type_id,
            self.type_format_flags(flags),
            location,
        )
    }

    pub(super) fn with_display_alias_transaction<T, E>(
        &mut self,
        query: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        let checkpoint = self.store.checkpoint_alias_symbol_links();
        let result = query(self);
        if result.is_err() {
            assert!(
                self.store.restore_alias_symbol_links(checkpoint),
                "display owns its alias checkpoint"
            );
        }
        result
    }

    /// Retains a module specifier resolved from one containing file by the Program.
    ///
    /// The checker validates the source module's identity. The Program owns
    /// package resolution and supplies the corresponding package-export name.
    /// This display fact does not change the module symbol or its exports.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign node, a non-module source, or an empty
    /// module specifier.
    pub fn set_module_display_specifier(
        &mut self,
        enclosing: NodeRef,
        source: NodeRef,
        specifier: String,
    ) -> Result<(), SymbolDisplayError> {
        let (arena, bound) = self
            .file(enclosing.file)
            .ok_or(SymbolDisplayError::InvalidLocation(enclosing))?;
        if !enclosing.is_for(arena.id(), bound.file_id())
            || !bound.contains(enclosing)
            || arena.revision() != bound.node_arena_revision()
            || !self.store.contains_node_ref(enclosing)
        {
            return Err(SymbolDisplayError::InvalidLocation(enclosing));
        }
        let (arena, bound) = self
            .file(source.file)
            .ok_or(SymbolDisplayError::InvalidLocation(source))?;
        if source != bound.source_file()
            || arena.revision() != bound.node_arena_revision()
            || !self.store.contains_node_ref(source)
            || !bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_external_or_common_js_module)
        {
            return Err(SymbolDisplayError::InvalidLocation(source));
        }
        if specifier.is_empty() || specifier.chars().any(char::is_control) {
            return Err(SymbolDisplayError::InvalidModuleSpecifier(source));
        }
        let symbol = bound
            .symbol(source)
            .and_then(|symbol| self.store.get_merged_symbol(symbol))
            .ok_or(SymbolDisplayError::InvalidLocation(source))?;
        self.module_display_specifiers
            .insert((enclosing.file, symbol), specifier);
        Ok(())
    }

    fn symbol_display_context(
        &mut self,
        enclosing: NodeRef,
    ) -> Result<SymbolDisplayContext, SymbolDisplayError> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(SymbolDisplayError::SourceHost)?;
        let mut alias_host = ProductionAliasTargetHost::from_registry(
            &self.store,
            &self.files,
            &self.module_resolutions,
        )
        .map_err(SymbolDisplayError::AliasHost)?;
        let mut context = SymbolDisplayContext::new(
            &mut self.store,
            &host,
            &mut alias_host,
            &self.module_resolutions,
            self.globals,
            &self.file_order,
            enclosing,
        )?;
        context.add_module_specifiers(&self.module_display_specifiers);
        Ok(context)
    }

    pub(super) fn artifact_symbol_chain(
        &mut self,
        symbol: SemanticSymbolId,
        enclosing: NodeRef,
    ) -> Result<Vec<SemanticSymbolId>, SymbolDisplayError> {
        let location = self.symbol_display_context(enclosing)?;
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(SymbolDisplayError::SourceHost)?;
        location.symbol_chain(&self.store, &host, symbol, SymbolFlags::NONE, false)
    }

    pub(super) fn written_default_symbol_name(
        &self,
        symbol: SemanticSymbolId,
        enclosing: NodeRef,
        initial: bool,
    ) -> Result<Option<String>, SymbolDisplayError> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(SymbolDisplayError::InvalidSymbol(symbol))?;
        if record.name() != InternalSymbolName::Default.as_ref()
            || !record
                .flags()
                .intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        {
            return Ok(None);
        }
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(SymbolDisplayError::SourceHost)?;
        super::symbol_display::written_default_name(
            &self.store,
            &host,
            symbol,
            enclosing,
            initial,
            false,
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
        .map(|host| host.with_program_file_order(&self.file_order))
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
        self.relate_types_with_current_session(source, target, RelationKind::Assignable)
    }

    /// Tests exact type identity using the context's authoritative global identities.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when either type is malformed or the
    /// identity relation requires a semantic family outside the installed checker cut.
    pub fn is_type_identical_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.relate_types_with_current_session(source, target, RelationKind::Identity)
    }

    /// Tests comparability using the context's authoritative global identities.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when either type is malformed or the
    /// comparable relation requires a semantic family outside the installed checker cut.
    pub fn is_type_comparable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.relate_types_with_current_session(source, target, RelationKind::Comparable)
    }

    fn relate_types_with_current_session(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    ) -> Result<bool, RelationUnavailable> {
        let Self {
            options,
            store,
            files,
            file_order,
            module_resolutions,
            global_types,
            instantiation_session,
            diagnostics,
            ..
        } = self;
        let limit_mark = instantiation_session.limit_event_mark();
        let result = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map_err(DeclaredTypeError::from)
        .map_err(SourceRelationError::Source)
        .and_then(|host| {
            let host = host
                .with_program_file_order(file_order)
                .with_module_resolutions(module_resolutions);
            super::source_properties::relate_source_types_with_global_this(
                store,
                &host,
                global_types,
                *options,
                source,
                target,
                relation,
                instantiation_session,
                diagnostics,
            )
        });
        if instantiation_session.limit_event_occurred_since(limit_mark) {
            return Err(RelationUnavailable::UnsupportedStructuredType(source));
        }
        result.map_err(|error| match error {
            SourceRelationError::Relation(error) => error,
            SourceRelationError::Source(error) => RelationUnavailable::CanonicalGlobalType(
                CanonicalGlobalTypeInitializationError::DeclaredType(error),
            ),
        })
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

    /// Returns eager and lazy global diagnostics independently of source replay.
    pub fn global_type_diagnostics(
        &self,
    ) -> impl Iterator<Item = &super::CanonicalGlobalTypeDiagnostic> {
        self.global_types.diagnostics().iter().chain(
            self.store
                .import_meta_global()
                .into_iter()
                .flat_map(super::global_types::ResolvedGlobalType::diagnostics),
        )
    }

    pub(super) fn import_meta_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, super::SourceMetaError> {
        let (arena, _) = self
            .files
            .snapshot(node.file)
            .ok_or(super::SourceMetaError::InvalidNode(node))?;
        if !super::source_meta::is_import_meta_artifact_node(arena, node) {
            return Ok(None);
        }
        let Self {
            store,
            files,
            options,
            module_resolutions,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        super::source_meta::import_meta_type_at_location(store, &host, node, *options)
    }

    pub(super) fn import_meta_artifact_symbol(
        &mut self,
        node: NodeRef,
        query: super::source_meta::ImportMetaSymbolQuery,
    ) -> Result<super::source_meta::ImportMetaSymbolResult, super::SourceMetaError> {
        let (arena, _) = self
            .files
            .snapshot(node.file)
            .ok_or(super::SourceMetaError::InvalidNode(node))?;
        if !super::source_meta::is_import_meta_artifact_node(arena, node) {
            return Ok(super::source_meta::ImportMetaSymbolResult::Unrelated);
        }
        let is_expression = matches!(
            arena.get(node.node).map(|record| &record.data),
            Some(NodeData::MetaProperty(_))
        );
        if is_expression != (query == super::source_meta::ImportMetaSymbolQuery::Expression) {
            return Ok(super::source_meta::ImportMetaSymbolResult::Unrelated);
        }
        let Self {
            store,
            files,
            options,
            module_resolutions,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        super::source_meta::import_meta_symbol_at_location(store, &host, node, *options)
    }

    pub(super) fn artifact_union_type(
        &mut self,
        types: &[TypeId],
    ) -> Result<TypeId, SourceCheckError> {
        self.store
            .expression_union_type_with_global_types(
                &self.global_types,
                types,
                super::bootstrap::UnionReduction::Literal,
            )
            .map_err(SourceCheckError::from)
    }

    pub(super) fn artifact_unresolved_type_symbol(
        &mut self,
        names: &[EscapedName],
    ) -> Result<SemanticSymbolId, super::store::UnresolvedTypeError> {
        self.store.get_or_create_unresolved_symbol(names)
    }

    pub(super) fn artifact_type_reference_identity(
        &mut self,
        node: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        self.instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            &mut self.store,
            &host,
            &self.global_types,
            self.options,
            &mut self.instantiation_session,
            &mut self.diagnostics,
        )?
        .get_type_identity_from_type_reference(node)
    }

    pub(super) fn artifact_interface_method_type(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        self.instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
        CanonicalTypeQuery::new_with_global_types_and_session(
            &mut self.store,
            &host,
            &self.global_types,
            self.options,
            &mut self.instantiation_session,
            &mut self.diagnostics,
        )?
        .get_type_of_interface_method(symbol)
    }

    pub(super) fn checked_source_method_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, SourceCheckError> {
        let Some((arena, _)) = self.files.snapshot(node.file) else {
            return Err(SourceCheckError::Property(node));
        };
        let Some(record) = arena.get(node.node) else {
            return Err(SourceCheckError::Property(node));
        };
        let property = matches!(record.data, NodeData::PropertyAccessExpression(_))
            || matches!(record.data, NodeData::Identifier(_))
                && record.parent.and_then(|parent| arena.get(parent)).is_some_and(|parent| {
                    matches!(&parent.data, NodeData::PropertyAccessExpression(access) if access.name == node.node)
                });
        if !property {
            return Ok(None);
        }
        self.instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(&self.module_resolutions);
        super::source::checked_source_method_property_type(
            &mut self.store,
            &host,
            &self.global_types,
            self.options,
            &mut self.instantiation_session,
            &mut self.diagnostics,
            node,
        )
    }

    pub(super) fn artifact_literal_type(
        &mut self,
        value: super::EvaluatorValue,
    ) -> Result<TypeId, SourceCheckError> {
        match value {
            super::EvaluatorValue::String(value) => self.store.regular_string_literal_type(value),
            super::EvaluatorValue::Number(value) => self.store.regular_number_literal_type(value),
        }
        .map_err(SourceCheckError::from)
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

    /// Looks up a source module export without resolving aliases or value types.
    ///
    /// Type-only aliases remain aliases. `None` requires a complete export search.
    ///
    /// # Errors
    ///
    /// Returns a typed error for unavailable star targets, unsupported module
    /// families, stale sources, or export tables that disagree with their sources.
    pub fn get_module_export_by_name(
        &self,
        module: SemanticSymbolId,
        name: &str,
    ) -> Result<Option<SemanticSymbolId>, super::CanonicalModuleExportQueryError> {
        let aliases = ProductionAliasTargetHost::from_registry(
            &self.store,
            &self.files,
            &self.module_resolutions,
        )?;
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
        super::module_exports::get_module_export_by_name(&self.store, &host, &aliases, module, name)
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

    /// Tests the effective call arity of a symbol's own function-like declarations.
    ///
    /// Cold declaration-file functions use the installed callable providers.
    /// Variables have no helper declaration signatures, even if their types
    /// are callable. This query does not read their annotations, check a source
    /// body, or demand a signature return.
    ///
    /// # Errors
    ///
    /// Returns a typed provider, provenance, or cache error instead of a
    /// negative answer when the exact callable set is unavailable.
    pub fn has_call_signature_with_arity_greater_than(
        &mut self,
        symbol: SemanticSymbolId,
        arity: usize,
    ) -> Result<bool, super::CanonicalHelperSignatureError> {
        self.instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
        super::helper_signatures::HelperSignatureQuery {
            store: &mut self.store,
            host: &host,
            global_types: &self.global_types,
            options: self.options,
            session: &mut self.instantiation_session,
            diagnostics: &mut self.diagnostics,
        }
        .has_arity_greater_than(symbol, arity)
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
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
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

    pub(super) fn preflight_enum_type(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<(), DeclaredTypeError> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
        super::enums::preflight_enum(&self.store, &host, symbol).map_err(DeclaredTypeError::from)
    }

    /// Returns a declared module's value type without checking its exports.
    ///
    /// Pure modules retain one anonymous identity. Namespace-only declarations
    /// return the canonical error type, as in the upstream value-symbol query.
    /// TypeScript source modules use the same lazy identity as namespace type queries.
    /// Bodyless ambient modules are not supported here.
    ///
    /// # Errors
    ///
    /// Rejects foreign declarations, changed caches, and modules merged with
    /// class, function, or enum values that require another value provider.
    pub fn get_type_of_module_value(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, SourceCheckError> {
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
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?;
        let module = store
            .get_merged_symbol(symbol)
            .ok_or(SourceCheckError::DeclaredType(
                DeclaredTypeError::Unavailable(super::DeclaredTypeUnavailable::SymbolNotOwned(
                    symbol,
                )),
            ))?;
        if let Some(declaration) = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .filter(|declaration| {
                store.source_node_kind(*declaration) == Some(SyntaxKind::SourceFile)
            })
        {
            return super::source_imports::prepare_source_file_namespace_identity(
                store, &host, module,
            )
            .map_err(|_| SourceCheckError::Import(declaration));
        }
        super::source_namespaces::get_type_of_module_value(store, &host, symbol)
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
            module_resolutions,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        let plan = plan_nongeneric_class(store, &host, symbol)?;
        execute_nongeneric_class_shells(store, &host, &plan)
    }

    /// Queries canonical class identities without checking or publishing members.
    ///
    /// This admits top-level nongeneric TypeScript declarations and named class expressions
    /// in top-level variable initializers. Heritage remains a separate query.
    /// Empty nongeneric classes in unmerged ambient namespaces also retain
    /// their exact source-owned instance and value shells.
    /// It does not mark a source checked or admit it to the class writers.
    ///
    /// # Errors
    ///
    /// Returns a typed source, binding, or cache error before query publication.
    pub fn get_class_query_shells(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<ClassShells, ClassError> {
        let Self {
            options,
            files,
            store,
            module_resolutions,
            ..
        } = self;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        let plan = super::classes::plan_class_query(store, &host, symbol)?;
        super::classes::execute_class_query_shells(store, &host, &plan)
    }

    /// Resolves one class member without publishing the class member tables.
    ///
    /// # Errors
    ///
    /// Rejects unsupported members and changed source bindings or caches.
    pub fn get_class_query_member_type(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, ClassError> {
        let Self {
            options,
            files,
            store,
            global_types,
            instantiation_session,
            diagnostics,
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        super::classes::ClassValueQuery {
            store,
            host: &host,
            global_types,
            options: *options,
            session: instantiation_session,
            diagnostics,
        }
        .member_type(symbol)
    }

    pub(super) fn get_class_query_type_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, ClassError> {
        let Self {
            options,
            files,
            store,
            global_types,
            instantiation_session,
            diagnostics,
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        super::classes::ClassValueQuery {
            store,
            host: &host,
            global_types,
            options: *options,
            session: instantiation_session,
            diagnostics,
        }
        .type_at_location(node)
    }

    /// Materializes exact primitive annotated members and the default
    /// construct signature for one local nongeneric class declaration.
    ///
    /// The admitted class has either no heritage or one direct local,
    /// nongeneric, property-only base. Constructor parameters may use primitive,
    /// interface-reference, and union annotations with the context's query
    /// options and global types. The operation
    /// preflights and reserves the entire graph before publishing a cold
    /// dependency or derived shell.
    /// Source-body constructors retain their real headers without checking
    /// field initializers or bodies.
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
            global_types,
            instantiation_session,
            diagnostics,
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
        let type_context = ClassTypeQueryContext::new(global_types, *options);
        super::classes::with_retained_source_class_annotation_scopes(
            store,
            &host,
            &type_context,
            symbol,
            |store| {
                if let Some(members) =
                    super::classes::completed_source_class_members(store, &host, symbol)?
                {
                    return Ok(members);
                }
                let overload_plan = loop {
                    match super::classes::plan_source_constructor_overload_class(
                        store,
                        &host,
                        symbol,
                        Some(&type_context),
                    ) {
                        Ok(plan) => break plan,
                        Err(error) => {
                            if !super::classes::prepare_source_constructor_overload_annotation(
                                store,
                                &host,
                                global_types,
                                *options,
                                instantiation_session,
                                diagnostics,
                                symbol,
                                error,
                            )? {
                                return Err(error);
                            }
                        }
                    }
                };
                if let Some(plan) = overload_plan {
                    return super::classes::prepare_source_class_constructor_header(
                        store,
                        &host,
                        global_types,
                        *options,
                        instantiation_session,
                        diagnostics,
                        &plan,
                    );
                }
                if let Some(plan) = super::classes::plan_source_single_constructor_class(
                    store,
                    &host,
                    symbol,
                    Some(&type_context),
                )? {
                    return super::classes::prepare_source_class_constructor_header(
                        store,
                        &host,
                        global_types,
                        *options,
                        instantiation_session,
                        diagnostics,
                        &plan,
                    );
                }
                if let Some(members) =
                    super::classes::completed_source_class_members(store, &host, symbol)?
                {
                    return Ok(members);
                }
                if store.source_class_provenance_for_symbol(symbol).is_some() {
                    return Err(super::classes::ClassError::Invariant(
                        super::classes::ClassInvariant::InvalidInstanceMembers(symbol),
                    ));
                }
                let plan = plan_nongeneric_class_member_query_with_type_context(
                    store,
                    &host,
                    symbol,
                    Some(&type_context),
                )?;
                execute_nongeneric_class_member_query(store, &host, &plan)
            },
        )
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
        )
        .map(|host| host.with_program_file_order(&self.file_order))?;
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
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?
        .with_module_resolutions(module_resolutions);
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
            module_resolutions,
            ..
        } = self;
        instantiation_session.reset_query();
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::new(options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))?
        .with_module_resolutions(module_resolutions);
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
    /// Already-diagnosed strict `arguments` collisions and authenticated
    /// parser-recovery sources use bounded recovery.
    ///
    /// # Errors
    ///
    /// Returns [`SourceCheckError`] for a foreign file, stale or malformed AST,
    /// unsupported source syntax, unavailable declared type or relation, type
    /// display boundary, or malformed literal cache.
    pub fn check_source_file(&mut self, file: FileId) -> Result<(), SourceCheckError> {
        let result = self.check_source_file_with_classic_jsx_factories(file, None);
        if let Err(SourceCheckError::RelationUnavailable(
            super::relation::RelationUnavailable::UnresolvedStructuredMembers(type_),
        )) = &result
        {
            let state = self.store.type_payload(*type_).map(|record| {
                let declaration = record
                    .symbol()
                    .and_then(|symbol| self.store.symbol(symbol))
                    .and_then(|symbol| symbol.declarations())
                    .and_then(|declarations| declarations.first().copied());
                let signatures = record
                    .data()
                    .structured()
                    .and_then(|structured| structured.signatures.as_ref())
                    .map(|signatures| {
                        signatures
                            .iter()
                            .take(4)
                            .map(|id| {
                                (
                                    *id,
                                    self.store.signature(*id).map(|signature| (
                                        signature.declaration(),
                                        signature.parameters().len(),
                                        signature.resolved_return_type(),
                                        signature.target(),
                                        signature.mapper(),
                                    )),
                                )
                            })
                            .collect::<Vec<_>>()
                    });
                (
                    std::mem::discriminant(record.data()),
                    record.flags(),
                    record.object_flags(),
                    record.symbol(),
                    declaration,
                    declaration.and_then(|node| self.store.source_node_kind(node)),
                    signatures,
                )
            });
            eprintln!("source.check-source-file file={file:?} error={result:?} state=(kind,flags,object_flags,owner,declaration,declaration_kind,signatures)={state:?}");
        }
        result
    }

    fn check_source_file_with_classic_jsx_factories(
        &mut self,
        file: FileId,
        classic_jsx_factories: Option<(&str, &str)>,
    ) -> Result<(), SourceCheckError> {
        self.check_source_file_with_class_imports(file, classic_jsx_factories, &mut Vec::new())
    }

    fn check_source_file_with_class_imports(
        &mut self,
        file: FileId,
        classic_jsx_factories: Option<(&str, &str)>,
        active: &mut Vec<SourceFileRef>,
    ) -> Result<(), SourceCheckError> {
        let source_file = self
            .files
            .source_file(file)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingFile(file),
            ))?;
        active
            .try_reserve(1)
            .map_err(|_| SourceCheckError::Import(source_file.node_ref()))?;
        active.push(source_file);
        let result = (|| {
            let mut imports = Vec::<SourceClassImportPlan>::new();
            loop {
                let request = RefCell::new(None);
                let result =
                    self.check_source_file_attempt(file, classic_jsx_factories, &imports, &request);
                let Some(demand) = request.into_inner() else {
                    return result;
                };
                let error = result
                    .err()
                    .ok_or(SourceCheckError::Import(demand.read.node))?;
                if imports.iter().any(|known| known.demand.read == demand.read) {
                    return Err(error);
                }
                let Some(imported) = self.resolve_source_class_import_demand(&demand)? else {
                    return Err(error);
                };
                if active.contains(&imported.owner.source) {
                    return Err(SourceCheckError::Unsupported(
                        source::UnsupportedSourceSyntax::Import(demand.read.node),
                    ));
                }
                self.check_source_file_with_class_imports(
                    imported.owner.source.file(),
                    None,
                    active,
                )?;
                let host = DeclaredTypeHost::from_registry(
                    &self.store,
                    &self.files,
                    GlobalMergeCompletion::new(self.options.name_resolution),
                )
                .map(|host| host.with_program_file_order(&self.file_order))
                .map_err(DeclaredTypeError::from)?
                .with_module_resolutions(&self.module_resolutions);
                if imported
                    .completed_value(&self.store, &host, &self.global_types, self.options)
                    .map_err(|error| source::source_class_import_error(demand.read.node, &error))?
                    .is_none()
                {
                    return Err(error);
                }
                imports
                    .try_reserve(1)
                    .map_err(|_| SourceCheckError::Import(demand.read.node))?;
                imports.push(imported);
            }
        })();
        if active.pop() != Some(source_file) {
            return Err(SourceCheckError::Import(source_file.node_ref()));
        }
        if let Err(SourceCheckError::RelationUnavailable(
            super::relater::RelationUnavailable::InvalidStructuredMembers(type_id),
        )) = &result
        {
            super::relater::observe_invalid_structured_members(
                &self.store,
                *type_id,
                "source.check_source_file_with_class_imports",
                None,
            );
        }
        result
    }

    fn resolve_source_class_import_demand(
        &mut self,
        demand: &SourceClassImportDemand,
    ) -> Result<Option<SourceClassImportPlan>, SourceCheckError> {
        let host = DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(&self.module_resolutions);
        let mut aliases = ProductionAliasTargetHost::from_registry(
            &self.store,
            &self.files,
            &self.module_resolutions,
        )
        .map_err(|_| SourceCheckError::Import(demand.read.node))?;
        resolve_source_class_import(&mut self.store, &host, &mut aliases, demand)
            .map_err(|error| source::source_class_import_error(demand.read.node, &error))
    }

    fn check_source_file_attempt(
        &mut self,
        file: FileId,
        classic_jsx_factories: Option<(&str, &str)>,
        class_imports: &[SourceClassImportPlan],
        class_import_demand: &RefCell<Option<SourceClassImportDemand>>,
    ) -> Result<(), SourceCheckError> {
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
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)?
        .with_module_resolutions(module_resolutions);
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
            classic_jsx_factories,
            instantiation_session,
            &mut staged,
            class_imports,
            class_import_demand,
        );
        let result = match result {
            Err(error) if class_import_demand.borrow().is_none() => {
                match source::recover_strict_arguments_source(
                    arena,
                    bound,
                    &host,
                    global_types,
                    store,
                    *options,
                    instantiation_session,
                    &mut staged,
                    error,
                ) {
                    Ok(true) => Ok(()),
                    Ok(false) => Err(error),
                    Err(recovery_error) => Err(recovery_error),
                }
            }
            result => result,
        };
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

    fn jsx_factory_alias_matches(&self, alias: SemanticSymbolId, target: SemanticSymbolId) -> bool {
        self.store.alias_symbol_links(alias).is_none_or(|links| {
            links.type_only_declaration.is_none()
                && links
                    .immediate_target
                    .is_none_or(|immediate| immediate == target)
                && match links.alias_target {
                    super::AliasTargetState::Unresolved => true,
                    super::AliasTargetState::Unknown => false,
                    super::AliasTargetState::Resolved(resolved) => resolved == target,
                }
        })
    }

    fn authenticated_module_jsx_namespace(
        &self,
        module: SemanticSymbolId,
        arena: &NodeArena,
        bound: &BoundFile,
    ) -> Option<SemanticSymbolId> {
        let source = bound.source_file();
        let export = self
            .store
            .symbol(module)?
            .exports()
            .and_then(|exports| self.store.symbol_table(exports))?
            .get_source("JSX")?;
        let export_record = self.store.symbol(export)?;
        let namespace = if export_record.flags() == SymbolFlags::ALIAS {
            let &[declaration] = export_record.declarations()? else {
                return None;
            };
            if !declaration.is_for(arena.id(), bound.file_id())
                || !bound.contains(declaration)
                || !self.store.contains_node_ref(declaration)
                || bound.symbol(declaration) != Some(export)
                || self.store.get_merged_symbol(export) != Some(export)
                || export_record.check_flags() != CheckFlags::NONE
                || export_record.value_declaration().is_some()
                || export_record.members().is_some()
                || export_record.exports().is_some()
                || export_record.parent() != Some(module)
                || export_record.export_symbol().is_some()
                || export_record.name().as_bytes() != b"JSX"
            {
                return None;
            }

            let declaration_record = arena.get(declaration.node)?;
            let NodeData::ExportSpecifier(specifier) = &declaration_record.data else {
                return None;
            };
            let clause = declaration_record.parent?;
            let clause_record = arena.get(clause)?;
            let NodeData::NamedExports(exports) = &clause_record.data else {
                return None;
            };
            let statement = clause_record.parent?;
            let statement_record = arena.get(statement)?;
            let NodeData::ExportDeclaration(export_declaration) = &statement_record.data else {
                return None;
            };
            let exported_name = arena.get(specifier.name)?;
            let NodeData::Identifier(exported_name) = &exported_name.data else {
                return None;
            };
            let local_name_id = specifier.property_name.unwrap_or(specifier.name);
            let local_name_record = arena.get(local_name_id)?;
            let NodeData::Identifier(local_name) = &local_name_record.data else {
                return None;
            };
            if declaration_record.kind != SyntaxKind::ExportSpecifier
                || declaration_record.flags.0 != 0
                || specifier.is_type_only
                || specifier.local_symbol.is_some()
                || specifier.symbol.is_some()
                || specifier.facts != 0
                || clause_record.kind != SyntaxKind::NamedExports
                || !exports.elements.nodes.contains(&declaration.node)
                || statement_record.kind != SyntaxKind::ExportDeclaration
                || statement_record.parent != Some(source.node)
                || export_declaration.export_clause != Some(clause)
                || export_declaration.module_specifier.is_some()
                || export_declaration.is_type_only
                || exported_name.text != "JSX"
                || local_name_record.parent != Some(declaration.node)
                || local_name.flow_node.is_some()
                || local_name.text.is_empty()
            {
                return None;
            }

            let namespace = bound
                .locals(source)
                .and_then(|locals| self.store.symbol_table(locals))?
                .get_source(&local_name.text)
                .and_then(|symbol| self.store.get_merged_symbol(symbol))?;
            if !self.jsx_factory_alias_matches(export, namespace) {
                return None;
            }
            namespace
        } else if export_record.flags().intersects(SymbolFlags::NAMESPACE) {
            export
        } else {
            return None;
        };

        let namespace_record = self.store.symbol(namespace)?;
        let namespace_name = namespace_record.name().as_utf8()?;
        if !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
            || self.store.get_merged_symbol(namespace) != Some(namespace)
            || !namespace_record.declarations()?.iter().any(|declaration| {
                let Some(record) = arena.get(declaration.node) else {
                    return false;
                };
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return false;
                };
                let Some(NodeData::Identifier(name)) =
                    arena.get(module.name).map(|record| &record.data)
                else {
                    return false;
                };
                declaration.is_for(arena.id(), bound.file_id())
                    && bound.contains(*declaration)
                    && self.store.contains_node_ref(*declaration)
                    && bound
                        .symbol(*declaration)
                        .and_then(|symbol| self.store.get_merged_symbol(symbol))
                        == Some(namespace)
                    && record.kind == SyntaxKind::ModuleDeclaration
                    && record.parent == Some(source.node)
                    && name.text == namespace_name
            })
        {
            return None;
        }
        Some(namespace)
    }

    fn authenticated_classic_jsx_factory_source(
        &self,
        arena: &NodeArena,
        bound: &BoundFile,
        factory_namespace: &str,
    ) -> Option<SourceFileRef> {
        let source = bound.source_file();
        let source_file = self.files.source_file(bound.file_id())?;
        if source_file.node_ref() != source || factory_namespace.is_empty() {
            return None;
        }

        let alias = bound
            .locals(source)
            .and_then(|locals| self.store.symbol_table(locals))?
            .get_source(factory_namespace)
            .and_then(|symbol| self.store.get_merged_symbol(symbol))?;
        let alias_record = self.store.symbol(alias)?;
        let &[declaration] = alias_record.declarations()? else {
            return None;
        };
        let declaration_record = arena.get(declaration.node)?;
        if !matches!(declaration_record.data, NodeData::NamespaceImport(_)) {
            return None;
        }
        let statement = arena.get(declaration_record.parent?)?.parent?;
        let statement = NodeRef::new(arena.id(), bound.file_id(), statement);
        let import = super::source_imports::plan_top_level_named_value_import(
            arena,
            bound,
            &self.store,
            statement,
        )
        .ok()?;
        if !import.bindings.iter().any(|binding| {
            binding.declaration == declaration
                && binding.alias_symbol == alias
                && binding.imported_text == "*"
                && binding.local_text == factory_namespace
        }) {
            return None;
        }

        let CanonicalModuleResolutionLookup::Resolved(resolved) =
            self.module_resolutions.lookup(import.module_specifier)
        else {
            return None;
        };
        if resolved.is_ambient_module() {
            return None;
        }
        let (target_arena, target_bound) = self.files.snapshot(resolved.target_file())?;
        let target_source = target_bound.source_file();
        let module = resolved.target_symbol();
        let module_record = self.store.symbol(module)?;
        if target_bound.symbol(target_source) != Some(module)
            || self.store.get_merged_symbol(module) != Some(module)
            || !module_record.flags().intersects(SymbolFlags::MODULE)
            || !module_record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&target_source))
            || !self.jsx_factory_alias_matches(alias, module)
            || self
                .authenticated_module_jsx_namespace(module, target_arena, target_bound)
                .is_none()
        {
            return None;
        }
        Some(source_file)
    }

    /// Checks one source using its exact, compiler-resolved JSX runtime.
    ///
    /// Automatic runtime availability and custom factory names are Program
    /// facts. The compiler supplies them per file so checker diagnostics never
    /// guess a module path or report a resolved module as missing.
    ///
    /// # Errors
    ///
    /// Returns [`SourceCheckError`] for invalid source or module provenance,
    /// conflicting runtime state, or any ordinary source-checking failure.
    pub fn check_source_file_with_jsx_runtime(
        &mut self,
        file: FileId,
        runtime: CanonicalJsxRuntimeEvidence<'_>,
    ) -> Result<(), SourceCheckError> {
        let (arena, bound) = self
            .files
            .snapshot(file)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingFile(file),
            ))?;
        let diagnostics =
            super::jsx::source_jsx_runtime_diagnostics(&self.store, arena, bound, runtime)?;
        if let CanonicalJsxRuntimeEvidence::Classic {
            factory_namespace, ..
        } = runtime
            && let Some(source) =
                self.authenticated_classic_jsx_factory_source(arena, bound, factory_namespace)
        {
            let mut links = self
                .store
                .source_file_links(source)
                .cloned()
                .unwrap_or_default();
            if !links.local_jsx_namespace.is_empty()
                && links.local_jsx_namespace != factory_namespace
            {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::SourceLinkPublication(source),
                ));
            }
            if links.local_jsx_namespace.is_empty() {
                factory_namespace.clone_into(&mut links.local_jsx_namespace);
                if !self.store.set_source_file_links(source, links) {
                    return Err(SourceCheckError::Provenance(
                        SourceCheckProvenanceError::SourceLinkPublication(source),
                    ));
                }
            }
        }
        let previous = self.options.jsx_runtime;
        self.options.jsx_runtime = runtime.mode();
        let classic_jsx_factories = match runtime {
            CanonicalJsxRuntimeEvidence::Classic {
                factory_namespace,
                fragment_factory_namespace,
                ..
            } => Some((factory_namespace, fragment_factory_namespace)),
            _ => None,
        };
        let checked =
            self.check_source_file_with_classic_jsx_factories(file, classic_jsx_factories);
        self.options.jsx_runtime = previous;
        checked?;
        source::merge_retry_diagnostics(&mut self.diagnostics, diagnostics);
        Ok(())
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
        self.clear_source_file_completion(file)?;
        self.check_source_file(file)
    }

    /// Forces source checking with the compiler's original JSX runtime facts.
    ///
    /// This retains canonical caches but clears the source completion flag.
    /// Automatic module symbols and classic factory names use the same checks
    /// as [`Self::check_source_file_with_jsx_runtime`].
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::check_source_file_with_jsx_runtime`]
    /// or a provenance error when `file` is not retained by this context.
    pub fn recheck_source_file_with_jsx_runtime(
        &mut self,
        file: FileId,
        runtime: CanonicalJsxRuntimeEvidence<'_>,
    ) -> Result<(), SourceCheckError> {
        self.clear_source_file_completion(file)?;
        self.check_source_file_with_jsx_runtime(file, runtime)
    }

    fn clear_source_file_completion(&mut self, file: FileId) -> Result<(), SourceCheckError> {
        let source = self.source_file(file).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingFile(file),
        ))?;
        if !self.store.contains_source_file(source) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::StoreSourceMismatch(source),
            ));
        }
        let Some(mut links) = self.store.source_file_links(source).cloned() else {
            // A retained source without completion links is already unchecked.
            return Ok(());
        };
        links.type_checked = false;
        if !self.store.set_source_file_links(source, links) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::StoreSourceMismatch(source),
            ));
        }
        Ok(())
    }

    /// Source ambient-module symbols collected before global library types exist.
    /// Their merged owners are installed after library initialization.
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

    /// Borrows this context's post-merge sources and name-resolution options.
    pub(super) fn declared_type_host(&self) -> Result<DeclaredTypeHost<'_>, DeclaredTypeError> {
        DeclaredTypeHost::from_registry(
            &self.store,
            &self.files,
            GlobalMergeCompletion::new(self.options.name_resolution),
        )
        .map(|host| host.with_program_file_order(&self.file_order))
        .map_err(DeclaredTypeError::from)
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
fn initialize_globals<'source, 'arena>(
    store: &mut CanonicalTypeMapperStore,
    file_order: &[FileId],
    files: &'source ProductionAliasSourceRegistry<'arena>,
    strict_bind_call_apply: bool,
    name_resolution_options: CanonicalNameResolverOptions,
    aliases: &mut ProductionAliasTargetHost<'source, 'arena, '_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
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
                    let mut host = ScriptGlobalMergeHost { files, diagnostics };
                    store.merge_global_symbol_with_host(&mut host, globals, symbol)?;
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

    // Global augmentations run before special global types are initialized.
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

    let declared_host = DeclaredTypeHost::from_registry(store, files, global_merge_completion)?
        .with_program_file_order(file_order);
    let global_types =
        initialize_global_library_types(store, &declared_host, globals, strict_bind_call_apply)?;

    // Pinned initializeChecker merges these only after the real library types exist.
    let mut ambient_host = AmbientModuleMergeHost {
        files,
        aliases,
        diagnostics,
        name_resolution_options,
        target_error: None,
    };
    for &symbol in &pending_ambient_modules {
        if let Err(error) = store.merge_global_symbol_with_host(&mut ambient_host, globals, symbol)
        {
            return Err(ambient_host.target_error.map_or_else(
                || CanonicalGlobalInitializationError::Merge(error),
                CanonicalGlobalInitializationError::ModuleAugmentationTarget,
            ));
        }
    }

    // Named module augmentation can depend on initialized global object types.
    for &file in file_order {
        let (arena, bound) = files
            .snapshot(file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        for augmentation in bound.module_augmentations() {
            let name = augmentation.name();
            let module = validate_augmentation_name(arena, bound, file, name)?;
            if matches!(
                arena.get(module.node).map(|node| &node.data),
                Some(NodeData::ModuleDeclaration(module))
                    if module.keyword == SyntaxKind::GlobalKeyword
            ) {
                continue;
            }
            if let Some(plan) = plan_named_ambient_module_augmentation(
                store,
                files,
                &pending_ambient_modules,
                arena,
                bound,
                file,
                module,
                name,
            )? {
                merge_named_ambient_module_augmentation(store, file, plan)?;
            }
        }
    }

    if !store.record_source_global_bindings_with_sources(globals, files) {
        return Err(CanonicalGlobalInitializationError::InvalidGlobals(globals));
    }

    Ok(GlobalInitialization {
        globals,
        global_types,
        pending_ambient_modules,
        pattern_ambient_modules,
    })
}

#[derive(Debug)]
struct NamedAmbientAugmentationPlan {
    namespace: SemanticSymbolId,
    augmentation: SemanticSymbolId,
    members: Vec<(EscapedName, SemanticSymbolId)>,
}

#[allow(clippy::too_many_arguments)] // Every input authenticates one retained augmentation.
fn plan_named_ambient_module_augmentation(
    store: &CanonicalTypeMapperStore,
    files: &ProductionAliasSourceRegistry<'_>,
    pending_ambient_modules: &[SemanticSymbolId],
    arena: &NodeArena,
    bound: &BoundFile,
    file: FileId,
    augmentation: NodeRef,
    name: NodeRef,
) -> Result<Option<NamedAmbientAugmentationPlan>, CanonicalGlobalInitializationError> {
    let Some(NodeData::StringLiteral(module_name)) = arena.get(name.node).map(|node| &node.data)
    else {
        return Ok(None);
    };
    if module_name.text.is_empty() || module_name.text.contains('*') {
        return Ok(None);
    }
    let quoted_name = EscapedName::source(format!("\"{}\"", module_name.text));
    let mut seen = BTreeSet::new();
    let mut candidates = pending_ambient_modules
        .iter()
        .filter_map(|candidate| store.get_merged_symbol(*candidate))
        .filter(|candidate| seen.insert(*candidate))
        .filter(|candidate| {
            store
                .symbol(*candidate)
                .is_some_and(|symbol| symbol.name().as_bytes() == quoted_name.as_bytes())
        });
    let Some(ambient_module) = candidates.next() else {
        return Ok(None);
    };
    if candidates.next().is_some() {
        return Ok(None);
    }

    let Some(augmentation_symbol) = bound.symbol(augmentation) else {
        return Err(CanonicalGlobalInitializationError::MissingAugmentationSymbol(augmentation));
    };
    let augmentation_record = store.symbol(augmentation_symbol).ok_or(
        CanonicalGlobalInitializationError::InvalidSymbol(augmentation_symbol),
    )?;
    if !augmentation_record.flags().intersects(SymbolFlags::MODULE)
        || augmentation_record.name().as_bytes() != quoted_name.as_bytes()
        || augmentation_record
            .declarations()
            .and_then(|declarations| declarations.first())
            .copied()
            != Some(augmentation)
        || store.get_merged_symbol(augmentation_symbol) != Some(augmentation_symbol)
    {
        return Ok(None);
    }
    let Some(augmentation_exports) = augmentation_record.exports() else {
        return Ok(None);
    };
    let members = ordered_table_entries(store, file, augmentation_exports)?;
    if members.is_empty() {
        return Ok(None);
    }

    let Some((namespace, namespace_exports)) =
        ambient_export_assignment_namespace(store, files, ambient_module, &module_name.text)?
    else {
        return Ok(None);
    };
    let augmentation_record = arena
        .get(augmentation.node)
        .ok_or(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(augmentation))?;
    let NodeData::ModuleDeclaration(module) = &augmentation_record.data else {
        return Ok(None);
    };
    let Some(body) = module.body else {
        return Ok(None);
    };
    if augmentation_record.parent != Some(bound.source_file().node)
        || !matches!(
            arena.get(body).map(|node| &node.data),
            Some(NodeData::ModuleBlock(_))
        )
    {
        return Ok(None);
    }

    let target_exports = store.symbol_table(namespace_exports).ok_or(
        CanonicalGlobalInitializationError::InvalidTable {
            file,
            table: namespace_exports,
        },
    )?;
    for (name, symbol) in &members {
        let source = store
            .symbol(*symbol)
            .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(*symbol))?;
        let Some(target) = target_exports
            .get(name.as_ref())
            .and_then(|target| store.get_merged_symbol(target))
        else {
            return Ok(None);
        };
        let target_record = store
            .symbol(target)
            .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(target))?;
        if store.get_merged_symbol(*symbol) != Some(*symbol)
            || source.flags() != SymbolFlags::INTERFACE
            || source.parent() != Some(augmentation_symbol)
            || !source.declarations().is_some_and(|declarations| {
                !declarations.is_empty()
                    && declarations.iter().all(|declaration| {
                        declaration.is_for(arena.id(), file)
                            && bound.contains(*declaration)
                            && store.contains_node_ref(*declaration)
                            && bound.symbol(*declaration) == Some(*symbol)
                            && arena.get(declaration.node).is_some_and(|node| {
                                node.kind == SyntaxKind::InterfaceDeclaration
                                    && node.parent == Some(body)
                            })
                    })
            })
            || !target_record.flags().contains(SymbolFlags::INTERFACE)
            || store.get_parent_of_symbol(target) != Some(namespace)
        {
            return Ok(None);
        }
    }

    Ok(Some(NamedAmbientAugmentationPlan {
        namespace,
        augmentation: augmentation_symbol,
        members,
    }))
}

fn ambient_export_assignment_namespace(
    store: &CanonicalTypeMapperStore,
    files: &ProductionAliasSourceRegistry<'_>,
    module: SemanticSymbolId,
    module_name: &str,
) -> Result<Option<(SemanticSymbolId, SymbolTableId)>, CanonicalGlobalInitializationError> {
    let module_record = store
        .symbol(module)
        .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(module))?;
    if !module_record.flags().intersects(SymbolFlags::MODULE)
        || store.get_merged_symbol(module) != Some(module)
    {
        return Ok(None);
    }
    let Some(module_exports) = module_record.exports() else {
        return Ok(None);
    };
    let Some(module_file) = module_record
        .declarations()
        .and_then(|declarations| declarations.first())
        .map(|declaration| declaration.file)
    else {
        return Ok(None);
    };
    let exports = store.symbol_table(module_exports).ok_or(
        CanonicalGlobalInitializationError::InvalidTable {
            file: module_file,
            table: module_exports,
        },
    )?;
    let Some(alias) = exports.get(InternalSymbolName::ExportEquals.as_ref()) else {
        return Ok(None);
    };
    let alias_record = store
        .symbol(alias)
        .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(alias))?;
    let Some([declaration]) = alias_record.declarations() else {
        return Ok(None);
    };
    let declaration = *declaration;
    if alias_record.flags() != SymbolFlags::ALIAS
        || alias_record.check_flags() != CheckFlags::NONE
        || alias_record.name() != InternalSymbolName::ExportEquals.as_ref()
        || alias_record.value_declaration() != Some(declaration)
        || alias_record.members().is_some()
        || alias_record.exports().is_some()
        || alias_record.parent() != Some(module)
        || alias_record.export_symbol().is_some()
        || store.get_merged_symbol(alias) != Some(alias)
    {
        return Ok(None);
    }

    let (arena, bound) = files
        .snapshot(declaration.file)
        .ok_or(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration))?;
    let Some(record) = arena.get(declaration.node) else {
        return Ok(None);
    };
    let NodeData::ExportAssignment(assignment) = &record.data else {
        return Ok(None);
    };
    let Some(block) = record.parent else {
        return Ok(None);
    };
    let Some(NodeData::ModuleBlock(module_block)) = arena.get(block).map(|node| &node.data) else {
        return Ok(None);
    };
    let Some(module_declaration) = arena.get(block).and_then(|node| node.parent) else {
        return Ok(None);
    };
    let module_declaration = NodeRef::new(arena.id(), bound.file_id(), module_declaration);
    let Some(module_node) = arena.get(module_declaration.node) else {
        return Ok(None);
    };
    let NodeData::ModuleDeclaration(ambient) = &module_node.data else {
        return Ok(None);
    };
    let Some(NodeData::StringLiteral(name)) = arena.get(ambient.name).map(|node| &node.data) else {
        return Ok(None);
    };
    let Some(expression) = arena.get(assignment.expression) else {
        return Ok(None);
    };
    let NodeData::Identifier(identifier) = &expression.data else {
        return Ok(None);
    };
    if record.kind != SyntaxKind::ExportAssignment
        || !assignment.is_export_equals
        || !declaration.is_for(arena.id(), bound.file_id())
        || !bound.contains(declaration)
        || !store.contains_node_ref(declaration)
        || bound.symbol(declaration) != Some(alias)
        || !module_block.statements.nodes.contains(&declaration.node)
        || ambient.body != Some(block)
        || name.text != module_name
        || module_node.parent != Some(bound.source_file().node)
        || bound.symbol(module_declaration) != Some(module)
        || expression.kind != SyntaxKind::Identifier
        || expression.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Ok(None);
    }

    let Some(local) = bound
        .locals(module_declaration)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text))
        .and_then(|local| store.get_merged_symbol(local))
    else {
        return Ok(None);
    };
    let Some(namespace) = store
        .symbol(local)
        .map(|record| record.export_symbol().unwrap_or(local))
        .and_then(|namespace| store.get_merged_symbol(namespace))
    else {
        return Ok(None);
    };
    let namespace_record = store
        .symbol(namespace)
        .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(namespace))?;
    let Some(namespace_exports) = namespace_record.exports() else {
        return Ok(None);
    };
    if !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.name().as_utf8() != Some(identifier.text.as_str())
        || !namespace_record.declarations().is_some_and(|declarations| {
            declarations.iter().any(|declaration| {
                declaration.is_for(arena.id(), bound.file_id())
                    && bound.contains(*declaration)
                    && store.contains_node_ref(*declaration)
                    && bound
                        .symbol(*declaration)
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        == Some(namespace)
                    && arena.get(declaration.node).is_some_and(|node| {
                        node.kind == SyntaxKind::ModuleDeclaration && node.parent == Some(block)
                    })
            })
        })
        || store.alias_symbol_links(alias).is_some_and(|links| {
            links.type_only_declaration.is_some()
                || links
                    .immediate_target
                    .is_some_and(|target| store.get_merged_symbol(target) != Some(namespace))
                || match links.alias_target {
                    super::AliasTargetState::Unresolved => false,
                    super::AliasTargetState::Unknown => true,
                    super::AliasTargetState::Resolved(target) => {
                        store.get_merged_symbol(target) != Some(namespace)
                    }
                }
        })
    {
        return Ok(None);
    }

    Ok(Some((namespace, namespace_exports)))
}

fn merge_named_ambient_module_augmentation(
    store: &mut CanonicalTypeMapperStore,
    file: FileId,
    plan: NamedAmbientAugmentationPlan,
) -> Result<(), CanonicalGlobalInitializationError> {
    let namespace = store.merge_symbol(plan.namespace, plan.augmentation, false)?;
    if store.get_merged_symbol(plan.namespace) != Some(namespace)
        || store.get_merged_symbol(plan.augmentation) != Some(namespace)
    {
        return Err(CanonicalGlobalInitializationError::InvalidSymbol(namespace));
    }
    let exports = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(namespace))?;
    for (name, source) in plan.members {
        let merged = store
            .symbol_table(exports)
            .and_then(|exports| exports.get(name.as_ref()))
            .ok_or(CanonicalGlobalInitializationError::InvalidTable {
                file,
                table: exports,
            })?;
        if store.get_merged_symbol(source) != Some(merged)
            || store.get_parent_of_symbol(merged) != Some(namespace)
        {
            return Err(CanonicalGlobalInitializationError::InvalidSymbol(merged));
        }
    }
    Ok(())
}

/// Reports authenticated TypeScript declaration names without querying types.
struct ScriptGlobalMergeHost<'borrow, 'arena> {
    files: &'borrow ProductionAliasSourceRegistry<'arena>,
    diagnostics: &'borrow mut CanonicalCheckerDiagnostics,
}

impl<'arena> ScriptGlobalMergeHost<'_, 'arena> {
    fn declaration_names(
        &self,
        store: &CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(Vec<NodeRef>, &'arena str), SymbolMergeError> {
        let unavailable = || SymbolMergeError::DiagnosticRequired {
            kind: diagnostic.kind,
            target: diagnostic.target,
            source: diagnostic.source,
        };
        let record = store
            .symbol(symbol)
            .ok_or(SymbolMergeError::InvalidSymbol(symbol))?;
        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
            .ok_or_else(unavailable)?;
        let symbol_name = record.name().as_utf8().ok_or_else(unavailable)?;
        let mut names = Vec::with_capacity(declarations.len());
        let mut spelling = None;
        for &declaration in declarations {
            let name = merge_declaration_name(self.files, store, declaration)?;
            if name == declaration {
                return Err(unavailable());
            }
            let (arena, bound) = self.files.snapshot(declaration.file).ok_or(
                SymbolMergeError::StoreInvariant("script merge declaration has no source"),
            )?;
            let facts = bound.source_facts().ok_or(SymbolMergeError::StoreInvariant(
                "script merge declaration has no source facts",
            ))?;
            if facts.is_javascript_file() {
                return Err(unavailable());
            }
            if ![bound.symbol(declaration), bound.local_symbol(declaration)]
                .into_iter()
                .flatten()
                .any(|owner| store.get_merged_symbol(owner) == Some(symbol))
            {
                return Err(SymbolMergeError::StoreInvariant(
                    "script merge declaration has a different symbol owner",
                ));
            }
            let name_record = arena.get(name.node).ok_or(SymbolMergeError::StoreInvariant(
                "script merge declaration has no name node",
            ))?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(unavailable());
            };
            if name_record.kind != SyntaxKind::Identifier {
                return Err(unavailable());
            }
            if identifier.text != symbol_name {
                return Err(SymbolMergeError::StoreInvariant(
                    "script merge declaration name differs from its symbol",
                ));
            }
            let invalid_text = || {
                SymbolMergeError::StoreInvariant(
                    "script merge declaration name has no source text",
                )
            };
            let declaration_record = arena.get(declaration.node).ok_or_else(invalid_text)?;
            if name_record.range.start.get() < declaration_record.range.start.get()
                || name_record.range.end.get() > declaration_record.range.end.get()
                || name_record.range.start.get() >= name_record.range.end.get()
            {
                return Err(invalid_text());
            }
            let start = usize::try_from(name_record.range.start.get())
                .map_err(|_| invalid_text())?;
            let end = usize::try_from(name_record.range.end.get()).map_err(|_| invalid_text())?;
            let written = arena
                .source_text()
                .and_then(|text| text.get(start..end))
                .ok_or_else(invalid_text)?;
            spelling.get_or_insert(written);
            names.push(name);
        }
        Ok((names, spelling.ok_or_else(unavailable)?))
    }
}

impl SymbolMergeHost<super::TypeRecord, super::TypeMapper> for ScriptGlobalMergeHost<'_, '_> {
    fn report_merge_diagnostic(
        &mut self,
        store: &CanonicalTypeMapperStore,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        if diagnostic.kind != SymbolMergeDiagnosticKind::IncompatibleDeclarations {
            return Err(SymbolMergeError::DiagnosticRequired {
                kind: diagnostic.kind,
                target: diagnostic.target,
                source: diagnostic.source,
            });
        }
        let target = store
            .symbol(diagnostic.target)
            .ok_or(SymbolMergeError::InvalidSymbol(diagnostic.target))?;
        let source = store
            .symbol(diagnostic.source)
            .ok_or(SymbolMergeError::InvalidSymbol(diagnostic.source))?;
        if self.files.store_id() != store.id() {
            return Err(SymbolMergeError::StoreInvariant(
                "script merge sources belong to a different store",
            ));
        }

        // Check both complete lists before the first diagnostic is issued.
        let (source_names, source_spelling) =
            self.declaration_names(store, diagnostic.source, diagnostic)?;
        let (target_names, _) = self.declaration_names(store, diagnostic.target, diagnostic)?;
        CheckerDiagnosticMergeHost::new(self.diagnostics).report_incompatible_at_nodes(
            target.flags() | source.flags(),
            source_spelling,
            &source_names,
            &target_names,
            DuplicatePrimaryArguments::NativeSourceSpelling,
        );
        Ok(())
    }
}

fn merge_declaration_name(
    files: &ProductionAliasSourceRegistry<'_>,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<NodeRef, SymbolMergeError> {
    let invalid = || SymbolMergeError::StoreInvariant("merge declaration has no source");
    let (arena, bound) = files.snapshot(declaration.file).ok_or_else(invalid)?;
    if !declaration.is_for(arena.id(), bound.file_id())
        || !bound.contains(declaration)
        || !store.contains_node_ref(declaration)
    {
        return Err(invalid());
    }
    let record = arena.get(declaration.node).ok_or_else(invalid)?;
    let name = match &record.data {
        NodeData::ClassDeclaration(data) => data.name,
        NodeData::ClassExpression(data) => data.name,
        NodeData::FunctionDeclaration(data) => data.name,
        NodeData::FunctionExpression(data) => data.name,
        NodeData::BindingElement(data) => data.name,
        NodeData::ImportClause(data) => data.name,
        NodeData::EnumDeclaration(data) => Some(data.name),
        NodeData::EnumMember(data) => Some(data.name),
        NodeData::InterfaceDeclaration(data) => Some(data.name),
        NodeData::ModuleDeclaration(data) => Some(data.name),
        NodeData::TypeAliasDeclaration(data) => Some(data.name),
        NodeData::TypeParameterDeclaration(data) => Some(data.name),
        NodeData::VariableDeclaration(data) => Some(data.name),
        NodeData::ParameterDeclaration(data) => Some(data.name),
        NodeData::PropertyDeclaration(data) => Some(data.name),
        NodeData::PropertySignatureDeclaration(data) => Some(data.name),
        NodeData::MethodDeclaration(data) => Some(data.name),
        NodeData::MethodSignatureDeclaration(data) => Some(data.name),
        NodeData::GetAccessorDeclaration(data) => Some(data.name),
        NodeData::SetAccessorDeclaration(data) => Some(data.name),
        NodeData::ExportSpecifier(data) => Some(data.name),
        NodeData::ImportSpecifier(data) => Some(data.name),
        NodeData::ImportEqualsDeclaration(data) => Some(data.name),
        NodeData::NamespaceImport(data) => Some(data.name),
        NodeData::NamespaceExport(data) => Some(data.name),
        _ => None,
    };
    let Some(name) = name else {
        return Ok(declaration);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    if !bound.contains(name)
        || !store.contains_node_ref(name)
        || arena
            .get(name.node)
            .is_none_or(|record| record.parent != Some(declaration.node))
    {
        return Err(invalid());
    }
    Ok(name)
}

struct ModuleAugmentationMergeHost<'borrow, 'arena> {
    files: &'borrow ProductionAliasSourceRegistry<'arena>,
    diagnostics: &'borrow mut CanonicalCheckerDiagnostics,
}

impl SymbolMergeHost<super::TypeRecord, super::TypeMapper> for ModuleAugmentationMergeHost<'_, '_> {
    fn report_merge_diagnostic(
        &mut self,
        store: &CanonicalTypeMapperStore,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        let mut reported = CanonicalCheckerDiagnostics::default();
        CheckerDiagnosticMergeHost::new(&mut reported)
            .report_merge_diagnostic(store, diagnostic)?;
        for mut diagnostic in reported.into_vec() {
            diagnostic.node = diagnostic
                .node
                .map(|node| merge_declaration_name(self.files, store, node))
                .transpose()?;
            for related in &mut diagnostic.related_information {
                related.node = related
                    .node
                    .map(|node| merge_declaration_name(self.files, store, node))
                    .transpose()?;
            }
            source::merge_retry_diagnostic(self.diagnostics, diagnostic);
        }
        Ok(())
    }
}

struct AmbientModuleMergeHost<'borrow, 'source, 'arena, 'manifest> {
    files: &'source ProductionAliasSourceRegistry<'arena>,
    aliases: &'borrow mut ProductionAliasTargetHost<'source, 'arena, 'manifest>,
    diagnostics: &'borrow mut CanonicalCheckerDiagnostics,
    name_resolution_options: CanonicalNameResolverOptions,
    target_error: Option<CanonicalAliasTargetUnavailable>,
}

impl CanonicalAliasTargetHost<super::TypeMapper> for AmbientModuleMergeHost<'_, '_, '_, '_> {
    fn get_target_of_alias_declaration(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
        if let Some(target) =
            super::source_namespaces::ambient_module_merge_alias_target(store, self.files, alias)?
        {
            return Ok(CanonicalImmediateAliasTarget::Resolved(target));
        }
        self.aliases.get_target_of_alias_declaration(store, alias)
    }
}

impl SymbolMergeHost<super::TypeRecord, super::TypeMapper>
    for AmbientModuleMergeHost<'_, '_, '_, '_>
{
    fn resolve_alias_for_merge(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        let queried = (|| {
            // Retain the real immediate edges for source replay in either file order.
            let mut current = symbol;
            let mut seen = BTreeSet::new();
            while seen.insert(current) {
                let record = store
                    .symbol(current)
                    .ok_or(CanonicalAliasResolutionError::InvalidSymbol(current))?;
                if !record.flags().intersects(SymbolFlags::ALIAS) {
                    break;
                }
                let Some(target) = CanonicalAliasResolver::new(store, &mut *self)
                    .get_immediate_aliased_symbol(current)?
                else {
                    break;
                };
                current = target;
            }
            CanonicalAliasResolver::new(store, &mut *self).resolve_alias(symbol)
        })();
        let resolution = queried.map_err(|error| match error {
            CanonicalAliasResolutionError::TargetUnavailable { alias, reason } => {
                self.target_error = Some(reason);
                SymbolMergeError::AliasResolutionRequired(alias)
            }
            CanonicalAliasResolutionError::InvalidSymbol(symbol)
            | CanonicalAliasResolutionError::SymbolIsNotAlias(symbol)
            | CanonicalAliasResolutionError::InvalidAliasLinks(symbol)
            | CanonicalAliasResolutionError::ResolutionStackInvariant(symbol) => {
                SymbolMergeError::InvalidSymbol(symbol)
            }
            CanonicalAliasResolutionError::InvalidTarget { target, .. } => {
                SymbolMergeError::InvalidSymbol(target)
            }
            CanonicalAliasResolutionError::TypeResolutionTarget(_) => {
                SymbolMergeError::StoreInvariant("ambient alias resolution stack is invalid")
            }
        })?;
        if !resolution.events.is_empty() {
            return Err(SymbolMergeError::AliasResolutionRequired(symbol));
        }
        match resolution.target {
            super::AliasTargetState::Resolved(target) => Ok(target),
            super::AliasTargetState::Unknown => store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.unknown_symbol)
                .ok_or(SymbolMergeError::StoreInvariant(
                    "ambient module merging requires intrinsic symbols",
                )),
            super::AliasTargetState::Unresolved => Err(SymbolMergeError::InvalidSymbol(symbol)),
        }
    }

    fn report_merge_diagnostic(
        &mut self,
        store: &CanonicalTypeMapperStore,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        let host = DeclaredTypeHost::from_registry(
            store,
            self.files,
            GlobalMergeCompletion::new(self.name_resolution_options),
        )
        .map_err(|_| SymbolMergeError::StoreInvariant("ambient module sources are invalid"))?;
        if super::source_namespaces::report_ambient_module_merge_diagnostic(
            store,
            &host,
            self.diagnostics,
            diagnostic,
        )
        .map_err(|_| SymbolMergeError::StoreInvariant("ambient module collision is invalid"))?
        {
            return Ok(());
        }
        ModuleAugmentationMergeHost {
            files: self.files,
            diagnostics: self.diagnostics,
        }
        .report_merge_diagnostic(store, diagnostic)
    }
}

/// Merges star-reexport targets before any source can cache their declared types.
fn merge_reexported_module_augmentations<'arena>(
    store: &mut CanonicalTypeMapperStore,
    file_order: &[FileId],
    files: &ProductionAliasSourceRegistry<'arena>,
    resolutions: &CanonicalModuleResolutionManifest,
    aliases: &mut ProductionAliasTargetHost<'_, 'arena, '_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<(), CanonicalGlobalInitializationError> {
    for &file in file_order {
        let (arena, bound) = files
            .snapshot(file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        for augmentation in bound.module_augmentations() {
            let name = augmentation.name();
            let declaration = validate_augmentation_name(arena, bound, file, name)?;
            let CanonicalModuleResolutionLookup::Resolved(resolved) = resolutions.lookup(name)
            else {
                continue;
            };
            if resolved.is_ambient_module() {
                continue;
            }
            let source = bound.symbol(declaration).ok_or(
                CanonicalGlobalInitializationError::MissingAugmentationSymbol(declaration),
            )?;
            let source_record = store
                .symbol(source)
                .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(source))?;
            if source_record
                .declarations()
                .and_then(|declarations| declarations.first())
                .copied()
                != Some(declaration)
                || store.get_merged_symbol(source) != Some(source)
            {
                continue;
            }
            let Some(source_exports) = source_record.exports() else {
                continue;
            };
            let target = store.get_merged_symbol(resolved.target_symbol()).ok_or(
                CanonicalGlobalInitializationError::InvalidSymbol(resolved.target_symbol()),
            )?;
            let target_record = store
                .symbol(target)
                .ok_or(CanonicalGlobalInitializationError::InvalidSymbol(target))?;
            let Some(target_exports) = target_record.exports() else {
                continue;
            };
            let exports = store.symbol_table(target_exports).ok_or(
                CanonicalGlobalInitializationError::InvalidTable {
                    file: resolved.target_file(),
                    table: target_exports,
                },
            )?;
            if exports
                .get(InternalSymbolName::ExportStar.as_ref())
                .is_none()
                || exports
                    .get(InternalSymbolName::ExportEquals.as_ref())
                    .is_some()
            {
                continue;
            }
            aliases
                .direct_source_module(store, declaration, resolved, true)
                .map_err(CanonicalGlobalInitializationError::ModuleAugmentationTarget)?;
            let members = ordered_table_entries(store, file, source_exports)?;
            let mut reexports = Vec::new();
            for (name, member) in members {
                if exports.get(name.as_ref()).is_some() {
                    continue;
                }
                let Some(name) = name.as_utf8() else {
                    continue;
                };
                match aliases.direct_export(store, declaration, target, name, true) {
                    Ok(previous) => reexports.push((previous, member)),
                    Err(CanonicalAliasTargetUnavailable::MissingExport { .. }) => {}
                    Err(error) => {
                        return Err(
                            CanonicalGlobalInitializationError::ModuleAugmentationTarget(error),
                        );
                    }
                }
            }
            let mut host = ModuleAugmentationMergeHost { files, diagnostics };
            for (previous, member) in reexports {
                store.merge_symbol_with_host(&mut host, previous, member, false)?;
            }
            store.merge_symbol_with_host(&mut host, target, source, false)?;
        }
    }
    Ok(())
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
    /// A star-reexport augmentation could not resolve its retained target.
    ModuleAugmentationTarget(CanonicalAliasTargetUnavailable),
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
            Self::ModuleAugmentationTarget(error) => {
                write!(
                    formatter,
                    "module augmentation target is unavailable: {error:?}"
                )
            }
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
        AliasTargetState, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange,
        CanonicalCheckerRelatedInformation, CanonicalModuleResolutionEntry,
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

    #[test]
    #[allow(clippy::too_many_lines)] // Damage and restore the real owner, selector, table, and Program order.
    fn global_this_member_proof_rechecks_source_owner_selector_and_order() {
        use crate::semantic::global_types::{
            prepare_global_this_members, source_global_this_value_type,
        };

        let library = minimal_global_library();
        let first = parsed(concat!(
            "declare var first: number; declare var shared: number; ",
            "declare class ExcludedMixed {} interface ExcludedMixed { member: number; }",
        ));
        let second = parsed("declare var second: string; declare var shared: number;");
        let consumer = parsed("export {}; declare const globalThis: { local: number };");
        let [lib_file, first_file, second_file, consumer_file] =
            [8_650, 8_690, 8_610, 8_630].map(FileId::new);
        let sources = [
            (lib_file, &library, true, CanonicalModuleState::Script),
            (first_file, &first, true, CanonicalModuleState::Script),
            (second_file, &second, true, CanonicalModuleState::Script),
            (
                consumer_file,
                &consumer,
                true,
                CanonicalModuleState::External,
            ),
        ];
        let mut context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&sources),
            sources
                .iter()
                .map(|(file, source, _, _)| (*file, &source.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let receiver = context.global_types.global_this_value_type;
        let symbol = context
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let first_symbol = global_symbol(&context, "first").unwrap();
        let second_symbol = global_symbol(&context, "second").unwrap();
        let excluded = global_symbol(&context, "ExcludedMixed").unwrap();
        let excluded = context.store.get_merged_symbol(excluded).unwrap();
        assert!(
            context
                .store
                .symbol(excluded)
                .unwrap()
                .flags()
                .contains(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        );
        let shared = global_symbol(&context, "shared").unwrap();
        let shared = context.store.get_merged_symbol(shared).unwrap();
        let local_declaration = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::VariableDeclaration).then_some(NodeRef::new(
                    consumer.arena.id(),
                    consumer_file,
                    node,
                ))
            })
            .unwrap();
        let local = context
            .file(consumer_file)
            .unwrap()
            .1
            .symbol(local_declaration)
            .unwrap();
        assert_ne!(local, symbol);
        let invalid_owner =
            DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidGlobalThisSymbol(symbol));
        let invalid_members =
            DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidGlobalThisMembers(receiver));
        let invalid_shared =
            DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidGlobalThisMember {
                receiver,
                symbol: shared,
            });
        let caller = format!("{:?}", context.instantiation_session);
        let diagnostics = context.diagnostics.clone();
        {
            let CanonicalCheckerContext {
                files,
                file_order,
                store,
                options,
                global_types,
                ..
            } = &mut context;
            let bare = DeclaredTypeHost::from_registry(
                store,
                files,
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let before = format!("{store:?}");
            assert_eq!(
                source_global_this_value_type(store, &bare, global_types, local),
                Ok(None)
            );
            assert_eq!(
                source_global_this_value_type(store, &bare, global_types, symbol),
                Ok(Some(receiver))
            );
            assert_eq!(
                prepare_global_this_members(store, &bare, global_types, receiver)
                    .map(|proof| proof.map(|proof| proof.receiver())),
                Err(DeclaredTypeUnavailable::GlobalThisProgramOrderUnavailable(receiver).into()),
            );
            assert_eq!(format!("{store:?}"), before);
            let host = bare.with_program_file_order(file_order);
            let owner = store.symbol(symbol).unwrap().clone();
            assert!(store.set_symbol_flags(symbol, owner.flags(), CheckFlags::NONE));
            let damaged = format!("{store:?}");
            assert_eq!(
                source_global_this_value_type(store, &host, global_types, symbol),
                Err(invalid_owner)
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert!(store.set_symbol_flags(symbol, owner.flags(), owner.check_flags()));
            assert_eq!(
                source_global_this_value_type(store, &host, global_types, symbol),
                Ok(Some(receiver))
            );

            let globals = store.intrinsic_bootstrap().unwrap().globals;
            assert_eq!(
                store.insert_symbol(globals, EscapedName::source("globalThis"), first_symbol),
                Some(Some(symbol))
            );
            let damaged = format!("{store:?}");
            assert_eq!(
                source_global_this_value_type(store, &host, global_types, symbol),
                Err(invalid_owner)
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert_eq!(
                store.insert_symbol(globals, EscapedName::source("globalThis"), symbol),
                Some(Some(first_symbol))
            );
            assert_eq!(
                source_global_this_value_type(store, &host, global_types, symbol),
                Ok(Some(receiver))
            );

            let shared_record = store.symbol(shared).unwrap().clone();
            let declarations = shared_record.declarations().unwrap().to_vec();
            assert_eq!(declarations.len(), 2);
            assert_eq!(declarations[0].file, first_file);
            assert_eq!(declarations[1].file, second_file);
            assert_eq!(shared_record.value_declaration(), Some(declarations[0]));
            assert!(store.set_symbol_declarations(
                shared,
                Some(declarations.clone()),
                Some(declarations[1])
            ));
            let damaged = format!("{store:?}");
            assert_eq!(
                prepare_global_this_members(store, &host, global_types, receiver)
                    .map(|proof| proof.map(|proof| proof.receiver())),
                Err(invalid_shared),
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert!(store.set_symbol_declarations(
                shared,
                Some(declarations),
                shared_record.value_declaration()
            ));

            let proof = prepare_global_this_members(store, &host, global_types, receiver)
                .unwrap()
                .unwrap();
            assert_eq!(proof.validate(store), Ok(()));
            assert_eq!(proof.get_source("first"), Some(first_symbol));
            assert_eq!(
                proof.export_source("ExcludedMixed").unwrap().symbol(),
                excluded
            );
            assert!(proof.get_source("ExcludedMixed").is_none());
            assert!(
                !proof
                    .members()
                    .iter()
                    .any(|(name, _)| name.as_utf8() == Some("ExcludedMixed"))
            );
            assert!(store.value_symbol_links(excluded).is_none());
            assert!(store.declared_type_links(excluded).is_none());
            let members = proof.members_table();
            let properties = proof.properties().to_vec();
            let first_index = properties
                .iter()
                .position(|symbol| *symbol == first_symbol)
                .unwrap();
            let second_index = properties
                .iter()
                .position(|symbol| *symbol == second_symbol)
                .unwrap();
            assert!(first_index < second_index);
            assert!(store.value_symbol_links(shared).is_none());
            let warm = format!("{store:?}");
            for _ in 0..2 {
                assert_eq!(proof.validate(store), Ok(()));
                assert_eq!(
                    source_global_this_value_type(store, &host, global_types, symbol),
                    Ok(Some(receiver))
                );
                let replay = prepare_global_this_members(store, &host, global_types, receiver)
                    .unwrap()
                    .unwrap();
                assert_eq!(replay.members_table(), members);
                assert_eq!(replay.properties(), properties);
            }
            assert_eq!(format!("{store:?}"), warm);

            let mut reordered = properties.clone();
            reordered.swap(first_index, second_index);
            assert!(store.set_structured_type_members(
                receiver,
                Some(members),
                Some(reordered),
                None,
                None,
                None
            ));
            let damaged = format!("{store:?}");
            assert_eq!(proof.validate(store), Err(invalid_members));
            assert_eq!(
                source_global_this_value_type(store, &host, global_types, symbol),
                Err(invalid_members)
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert!(store.set_structured_type_members(
                receiver,
                Some(members),
                Some(properties),
                None,
                None,
                None
            ));
            assert_eq!(proof.validate(store), Ok(()));

            assert_eq!(
                store.insert_symbol(members, EscapedName::source("first"), second_symbol),
                Some(Some(first_symbol))
            );
            let damaged = format!("{store:?}");
            assert_eq!(proof.validate(store), Err(invalid_members));
            assert_eq!(format!("{store:?}"), damaged);
            assert_eq!(
                store.insert_symbol(members, EscapedName::source("first"), first_symbol),
                Some(Some(second_symbol))
            );
            assert_eq!(proof.validate(store), Ok(()));

            let first_record = store.symbol(first_symbol).unwrap().clone();
            assert!(store.set_symbol_relationships(
                first_symbol,
                first_record.members(),
                first_record.exports(),
                Some(symbol),
                first_record.export_symbol()
            ));
            let damaged = format!("{store:?}");
            assert_eq!(
                proof.validate(store),
                Err(DeclaredTypeUnavailable::InvalidGlobalThisMember {
                    receiver,
                    symbol: first_symbol
                }
                .into())
            );
            assert_eq!(format!("{store:?}"), damaged);
            assert!(store.set_symbol_relationships(
                first_symbol,
                first_record.members(),
                first_record.exports(),
                first_record.parent(),
                first_record.export_symbol()
            ));
            assert_eq!(proof.validate(store), Ok(()));

            let bare = DeclaredTypeHost::from_registry(
                store,
                files,
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let warm = format!("{store:?}");
            assert_eq!(
                source_global_this_value_type(store, &bare, global_types, symbol),
                Err(DeclaredTypeUnavailable::GlobalThisProgramOrderUnavailable(receiver).into()),
            );
            assert_eq!(format!("{store:?}"), warm);
        }
        context.file_order.swap(1, 2);
        {
            let host = context.declared_type_host().unwrap();
            let damaged = format!("{:?}", context.store);
            assert_eq!(
                source_global_this_value_type(&context.store, &host, &context.global_types, symbol),
                Err(invalid_members)
            );
            assert_eq!(format!("{:?}", context.store), damaged);
        }
        context.file_order.swap(1, 2);
        let host = context.declared_type_host().unwrap();
        assert_eq!(
            source_global_this_value_type(&context.store, &host, &context.global_types, symbol),
            Ok(Some(receiver))
        );
        assert_eq!(format!("{:?}", context.instantiation_session), caller);
        assert_eq!(context.diagnostics, diagnostics);
    }

    #[test]
    fn global_this_unproved_alias_stays_cold_before_member_publication() {
        use crate::semantic::global_types::{
            prepare_global_this_members, source_global_this_value_type,
        };

        let library = minimal_global_library();
        let provider =
            parsed("export as namespace UnprovedGlobal; export declare const value: number;");
        let [library_file, provider_file] = [8_710, 8_700].map(FileId::new);
        let sources = [
            (library_file, &library, true, CanonicalModuleState::Script),
            (
                provider_file,
                &provider,
                true,
                CanonicalModuleState::External,
            ),
        ];
        let mut context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&sources),
            sources
                .iter()
                .map(|(file, source, _, _)| (*file, &source.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let alias = global_symbol(&context, "UnprovedGlobal").unwrap();
        let alias = context.store.get_merged_symbol(alias).unwrap();
        assert!(
            context
                .store
                .symbol(alias)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::ALIAS)
        );
        let CanonicalCheckerContext {
            store,
            files,
            file_order,
            global_types,
            options,
            ..
        } = &mut context;
        let host = DeclaredTypeHost::from_registry(
            store,
            files,
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap()
        .with_program_file_order(file_order);
        let receiver = global_types.global_this_value_type;
        let symbol = store.intrinsic_bootstrap().unwrap().global_this_symbol;
        let before = format!("{store:?}");
        assert_eq!(
            source_global_this_value_type(store, &host, global_types, symbol),
            Ok(Some(receiver))
        );
        assert_eq!(
            prepare_global_this_members(store, &host, global_types, receiver)
                .map(|proof| proof.map(|proof| proof.receiver())),
            Err(DeclaredTypeUnavailable::UnsupportedGlobalThisMember {
                receiver,
                symbol: alias
            }
            .into()),
        );
        assert_eq!(format!("{store:?}"), before);
        assert_eq!(
            store.type_payload(receiver).unwrap().object_flags(),
            ObjectFlags::ANONYMOUS
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each real export and member damage with its full restore.
    fn global_this_type_export_reads_reject_redirected_namespace_tables() {
        use crate::semantic::{
            global_types::{prepare_global_this_members, source_global_this_export},
            links::ModuleSymbolLinks,
        };

        #[derive(Clone, Copy, Debug)]
        enum Damage {
            Exports,
            ResolvedExports,
            TypeRow,
            SelfRow,
            ReadyRow,
            ReadyOrder,
        }

        let library = minimal_global_library();
        let provider = parsed(concat!(
            "interface VisibleType { marker: number } ",
            "declare namespace Alternate { export interface VisibleType { other: string } } ",
            "declare class BlockedType {} ",
            "declare var sleeping: { later: number };",
        ));
        let [library_file, provider_file] = [8_740, 8_720].map(FileId::new);
        let sources = [
            (library_file, &library, true, CanonicalModuleState::Script),
            (provider_file, &provider, true, CanonicalModuleState::Script),
        ];
        for ready in [false, true] {
            let mut context = CanonicalCheckerContext::new(
                completed_bindings_with_facts(&sources),
                sources
                    .iter()
                    .map(|(file, source, _, _)| (*file, &source.arena))
                    .collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let visible_raw = global_symbol(&context, "VisibleType").unwrap();
            let visible = context.store.get_merged_symbol(visible_raw).unwrap();
            let blocked_raw = global_symbol(&context, "BlockedType").unwrap();
            let blocked = context.store.get_merged_symbol(blocked_raw).unwrap();
            let sleeping_raw = global_symbol(&context, "sleeping").unwrap();
            let sleeping = context.store.get_merged_symbol(sleeping_raw).unwrap();
            let alternate = global_symbol(&context, "Alternate").unwrap();
            let alternate = context.store.get_merged_symbol(alternate).unwrap();
            let alternate_exports = context.store.symbol(alternate).unwrap().exports().unwrap();
            let injected_raw = context
                .store
                .symbol_table(alternate_exports)
                .unwrap()
                .get_source("VisibleType")
                .unwrap();
            let injected = context.store.get_merged_symbol(injected_raw).unwrap();
            assert_ne!(injected_raw, visible_raw);
            assert_ne!(injected, visible);
            assert!(
                context
                    .store
                    .symbol(injected)
                    .unwrap()
                    .flags()
                    .intersects(SymbolFlags::INTERFACE)
            );
            let sleeping_declaration = context
                .store
                .symbol(sleeping)
                .unwrap()
                .value_declaration()
                .unwrap();
            let NodeData::VariableDeclaration(variable) =
                &provider.arena.get(sleeping_declaration.node).unwrap().data
            else {
                panic!("sleeping must retain its real variable declaration");
            };
            let sleeping_annotation =
                NodeRef::new(provider.arena.id(), provider_file, variable.type_.unwrap());
            let CanonicalCheckerContext {
                files,
                file_order,
                store,
                global_types,
                options,
                instantiation_session,
                diagnostics,
                ..
            } = &mut context;
            let host = DeclaredTypeHost::from_registry(
                store,
                files,
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap()
            .with_program_file_order(file_order);
            let receiver = global_types.global_this_value_type;
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let symbol = bootstrap.global_this_symbol;
            let globals = bootstrap.globals;
            let wrong_receiver = bootstrap.empty_object_type;
            assert_ne!(wrong_receiver, receiver);
            assert!(!store.relation_read_observation_is_active());
            let caller_before = format!("{instantiation_session:?}");
            let diagnostics_before = diagnostics.clone();

            // Save a valid allocated link so every damage restores the same link state.
            let module = ModuleSymbolLinks {
                resolved_exports: Some(globals),
                ..ModuleSymbolLinks::default()
            };
            assert!(store.set_module_symbol_links(symbol, module.clone()));
            let ready_members = ready.then(|| {
                let proof = prepare_global_this_members(store, &host, global_types, receiver)
                    .unwrap()
                    .unwrap();
                assert_eq!(proof.validate(store), Ok(()));
                assert_eq!(proof.get_source("BlockedType"), None);
                (proof.members_table(), proof.properties().to_vec())
            });
            let owner = store.symbol(symbol).unwrap().clone();
            let snapshot = |store: &CanonicalTypeMapperStore| {
                assert!(!store.relation_read_observation_is_active());
                (
                    format!("{store:?}"),
                    (
                        [
                            store.type_len(),
                            store.type_alias_len(),
                            store.symbol_len(),
                            store.signature_len(),
                            store.mapper_len(),
                            store.index_info_len(),
                            store.symbol_store().symbol_table_len(),
                        ],
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                        store.type_resolution_internal_state(),
                    ),
                    (
                        format!("{:?}", store.type_payload(receiver)),
                        format!("{:?}", store.symbol(symbol)),
                        store.value_symbol_links(symbol).cloned(),
                        store.module_symbol_links(symbol).cloned(),
                        [globals, alternate_exports]
                            .into_iter()
                            .chain(ready_members.as_ref().map(|(table, _)| *table))
                            .map(|table| {
                                (
                                    table,
                                    store
                                        .symbol_table(table)
                                        .unwrap()
                                        .iter()
                                        .map(|(name, symbol)| (name.to_owned(), symbol))
                                        .collect::<Vec<_>>(),
                                )
                            })
                            .collect::<Vec<_>>(),
                    ),
                    [visible, injected, blocked, sleeping]
                        .into_iter()
                        .map(|symbol| {
                            (
                                store.declared_type_links(symbol).cloned(),
                                store.value_symbol_links(symbol).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    provider
                        .arena
                        .iter()
                        .map(|(node, _)| {
                            let node = NodeRef::new(provider.arena.id(), provider_file, node);
                            (
                                store.node_links(node).cloned(),
                                store.type_node_links(node).cloned(),
                                store.symbol_node_links(node).cloned(),
                                store.signature_links(node).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    (
                        format!("{instantiation_session:?}"),
                        instantiation_session.query_count(),
                        instantiation_session.total_count(),
                        instantiation_session.limit_event_count(),
                        diagnostics.clone(),
                    ),
                )
            };
            let read = |store: &CanonicalTypeMapperStore, name| {
                source_global_this_export(store, &host, global_types, receiver, name)
            };
            let before = snapshot(store);
            let expected = read(store, "VisibleType").unwrap().unwrap();
            assert_eq!(expected.table_symbol(), visible_raw);
            assert_eq!(expected.symbol(), visible);
            assert_eq!(expected.flags(), store.symbol(visible_raw).unwrap().flags());
            let expected_blocked = read(store, "BlockedType").unwrap().unwrap();
            assert_eq!(expected_blocked.table_symbol(), blocked_raw);
            assert_eq!(expected_blocked.symbol(), blocked);
            assert!(expected_blocked.flags().intersects(SymbolFlags::CLASS));
            let expected_self = read(store, "globalThis").unwrap().unwrap();
            assert_eq!(expected_self.table_symbol(), symbol);
            assert_eq!(expected_self.symbol(), symbol);
            assert_eq!(expected_self.builtin_value_type(), Some(receiver));
            assert_eq!(read(store, "MissingType"), Ok(None));
            assert_eq!(snapshot(store), before);
            let check_valid = |store: &CanonicalTypeMapperStore| {
                let before = snapshot(store);
                for _ in 0..2 {
                    assert_eq!(read(store, "VisibleType"), Ok(Some(expected.clone())));
                    assert_eq!(
                        read(store, "BlockedType"),
                        Ok(Some(expected_blocked.clone()))
                    );
                    assert_eq!(read(store, "globalThis"), Ok(Some(expected_self.clone())));
                    assert_eq!(read(store, "MissingType"), Ok(None));
                    assert_eq!(snapshot(store), before);
                }
                for symbol in [visible, injected, blocked, sleeping] {
                    assert!(store.declared_type_links(symbol).is_none());
                    assert!(store.value_symbol_links(symbol).is_none());
                }
                assert!(store.type_node_links(sleeping_annotation).is_none());
                if let Some((members, properties)) = &ready_members {
                    let structured = store
                        .type_payload(receiver)
                        .unwrap()
                        .data()
                        .structured()
                        .unwrap();
                    assert_eq!(structured.members, Some(*members));
                    assert_eq!(
                        structured.properties.as_deref(),
                        Some(properties.as_slice())
                    );
                } else {
                    assert_eq!(
                        store.type_payload(receiver).unwrap().object_flags(),
                        ObjectFlags::ANONYMOUS
                    );
                    assert_eq!(
                        store.type_payload(receiver).unwrap().data().structured(),
                        Some(&crate::semantic::type_records::StructuredTypeData::default())
                    );
                }
            };
            check_valid(store);
            let invalid_owner =
                DeclaredTypeError::from(DeclaredTypeUnavailable::InvalidGlobalThisSymbol(symbol));
            let invalid_members = DeclaredTypeError::from(
                DeclaredTypeUnavailable::InvalidGlobalThisMembers(receiver),
            );
            for damage in [
                Damage::Exports,
                Damage::ResolvedExports,
                Damage::TypeRow,
                Damage::SelfRow,
                Damage::ReadyRow,
                Damage::ReadyOrder,
            ] {
                if !ready && matches!(damage, Damage::ReadyRow | Damage::ReadyOrder) {
                    continue;
                }
                let before = snapshot(store);
                let error = match damage {
                    Damage::Exports => {
                        assert!(store.set_symbol_relationships(
                            symbol,
                            owner.members(),
                            Some(alternate_exports),
                            owner.parent(),
                            owner.export_symbol(),
                        ));
                        invalid_owner
                    }
                    Damage::ResolvedExports => {
                        let mut redirected = module.clone();
                        redirected.resolved_exports = Some(alternate_exports);
                        assert!(store.set_module_symbol_links(symbol, redirected));
                        invalid_owner
                    }
                    Damage::TypeRow => {
                        assert_eq!(
                            store.insert_symbol(
                                globals,
                                EscapedName::source("VisibleType"),
                                injected_raw
                            ),
                            Some(Some(visible_raw))
                        );
                        DeclaredTypeUnavailable::InvalidGlobalThisMember {
                            receiver,
                            symbol: injected_raw,
                        }
                        .into()
                    }
                    Damage::SelfRow => {
                        assert_eq!(
                            store.insert_symbol(
                                globals,
                                EscapedName::source("globalThis"),
                                injected_raw
                            ),
                            Some(Some(symbol))
                        );
                        invalid_owner
                    }
                    Damage::ReadyRow => {
                        let (members, _) = ready_members.as_ref().unwrap();
                        assert_eq!(
                            store.insert_symbol(
                                *members,
                                EscapedName::source("VisibleType"),
                                injected_raw
                            ),
                            Some(Some(visible_raw))
                        );
                        invalid_members
                    }
                    Damage::ReadyOrder => {
                        let (members, properties) = ready_members.as_ref().unwrap();
                        let mut reordered = properties.clone();
                        let sleeping_index = properties
                            .iter()
                            .position(|row| *row == sleeping_raw)
                            .unwrap();
                        let self_index = properties.iter().position(|row| *row == symbol).unwrap();
                        assert_ne!(sleeping_index, self_index);
                        reordered.swap(sleeping_index, self_index);
                        assert!(store.set_structured_type_members(
                            receiver,
                            Some(*members),
                            Some(reordered),
                            None,
                            None,
                            None,
                        ));
                        invalid_members
                    }
                };
                let damaged = snapshot(store);
                for _ in 0..2 {
                    for name in ["VisibleType", "MissingType", "globalThis"] {
                        assert_eq!(read(store, name), Err(error), "{damage:?}");
                        assert_eq!(snapshot(store), damaged, "{damage:?}");
                    }
                }
                match damage {
                    Damage::Exports => assert!(store.set_symbol_relationships(
                        symbol,
                        owner.members(),
                        owner.exports(),
                        owner.parent(),
                        owner.export_symbol(),
                    )),
                    Damage::ResolvedExports => {
                        assert!(store.set_module_symbol_links(symbol, module.clone()));
                    }
                    Damage::TypeRow => assert_eq!(
                        store.insert_symbol(
                            globals,
                            EscapedName::source("VisibleType"),
                            visible_raw
                        ),
                        Some(Some(injected_raw))
                    ),
                    Damage::SelfRow => assert_eq!(
                        store.insert_symbol(globals, EscapedName::source("globalThis"), symbol),
                        Some(Some(injected_raw))
                    ),
                    Damage::ReadyRow => assert_eq!(
                        store.insert_symbol(
                            ready_members.as_ref().unwrap().0,
                            EscapedName::source("VisibleType"),
                            visible_raw,
                        ),
                        Some(Some(injected_raw))
                    ),
                    Damage::ReadyOrder => {
                        let (members, properties) = ready_members.as_ref().unwrap();
                        assert!(store.set_structured_type_members(
                            receiver,
                            Some(*members),
                            Some(properties.clone()),
                            None,
                            None,
                            None,
                        ));
                    }
                }
                assert_eq!(snapshot(store), before, "{damage:?}");
                check_valid(store);
            }
            let before = snapshot(store);
            for _ in 0..2 {
                assert_eq!(
                    source_global_this_export(
                        store,
                        &host,
                        global_types,
                        wrong_receiver,
                        "VisibleType"
                    ),
                    Err(DeclaredTypeUnavailable::InvalidGlobalThisMembers(wrong_receiver).into()),
                );
                assert_eq!(snapshot(store), before);
            }
            check_valid(store);
            assert_eq!(format!("{instantiation_session:?}"), caller_before);
            assert_eq!(*diagnostics, diagnostics_before);
        }
    }

    #[test]
    fn intrinsic_any_names_preserve_identity_and_reject_forged_intrinsics() {
        let parsed = parsed("const value = 1;");
        let file = FileId::new(8_230);
        let make_context = || {
            CanonicalCheckerContext::new(
                completed_bindings(&[(file, &parsed)]),
                vec![(file, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap()
        };
        let mut context = make_context();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let intrinsic_names = [
            (bootstrap.any_type, "any"),
            (bootstrap.auto_type, "any"),
            (bootstrap.wildcard_type, "any"),
            (bootstrap.blocked_string_type, "any"),
            (bootstrap.error_type, "error"),
            (bootstrap.unresolved_type, "unresolved"),
            (bootstrap.non_inferrable_any_type, "any"),
            (bootstrap.intrinsic_marker_type, "intrinsic"),
        ];
        let error = bootstrap.error_type;
        let number = bootstrap.number_type;
        let counts = (
            context.store().type_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for (type_id, name) in intrinsic_names {
            assert_eq!(context.intrinsic_any_name(type_id), Ok(Some(name)));
        }
        assert_eq!(context.intrinsic_any_name(number), Ok(None));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths()
            ),
            counts,
        );
        let foreign = make_context();
        let foreign_any = foreign.store().intrinsic_bootstrap().unwrap().any_type;
        assert_eq!(
            context.intrinsic_any_name(foreign_any),
            Err(TypeDisplayUnavailable::Type(foreign_any)),
        );
        let forged = context
            .store_mut_for_test()
            .alloc_intrinsic_type(TypeFlags::ANY, "error")
            .unwrap();
        assert_eq!(
            context.intrinsic_any_name(forged),
            Err(TypeDisplayUnavailable::MalformedType(forged)),
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(error, ObjectFlags::NON_INFERRABLE_TYPE)
        );
        assert_eq!(
            context.intrinsic_any_name(error),
            Err(TypeDisplayUnavailable::MalformedType(error)),
        );
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

    const EXECUTABLE_IMPORT_BASE: &str =
        "export class Base { value = 1; constructor() {} read() { return this.value; } }";
    const EXECUTABLE_IMPORT_READ: &str =
        "import { Base as Imported } from './base'; const Saved = Imported;";

    fn executable_class_demand(
        context: &CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        file: FileId,
    ) -> SourceClassImportDemand {
        let bound = context.file(file).unwrap().1;
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration)
                    .then_some(node_ref(parsed, file, node))
            })
            .unwrap();
        let import = super::super::source_imports::plan_top_level_named_value_import(
            &parsed.arena,
            bound,
            context.store(),
            declaration,
        )
        .unwrap();
        let [binding] = import.bindings.as_slice() else {
            panic!("one real named import")
        };
        let read_node = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                (module_export_name(&parsed.arena, variable.name) == Some("Saved"))
                    .then(|| node_ref(parsed, file, variable.initializer.unwrap()))
            })
            .unwrap();
        let read = super::super::source_imports::plan_source_import_identifier_read(
            &parsed.arena,
            bound,
            context.store(),
            binding,
            read_node,
            &binding.local_text,
            binding.alias_symbol,
        )
        .unwrap();
        SourceClassImportDemand {
            binding: binding.clone(),
            read,
        }
    }

    fn prepare_executable_class_import(
        context: &mut CanonicalCheckerContext<'_>,
        demand: &SourceClassImportDemand,
    ) -> Result<
        super::super::source_imports::PreparedSourceImportValue,
        super::super::source_imports::SourceImportError,
    > {
        let host = DeclaredTypeHost::from_registry(
            &context.store,
            &context.files,
            GlobalMergeCompletion::new(context.options.name_resolution),
        )
        .unwrap()
        .with_module_resolutions(&context.module_resolutions);
        let mut aliases = ProductionAliasTargetHost::from_registry(
            &context.store,
            &context.files,
            &context.module_resolutions,
        )
        .unwrap();
        let resolved = super::super::source_imports::resolve_source_import_binding(
            &mut context.store,
            &mut aliases,
            &demand.binding,
        )?;
        super::super::source_imports::prepare_source_import_value(
            &mut context.store,
            &host,
            &context.global_types,
            context.options,
            &mut context.instantiation_session,
            &mut context.diagnostics,
            &resolved,
            &demand.read,
        )
    }

    fn preflight_executable_class_import(
        context: &CanonicalCheckerContext<'_>,
        prepared: &super::super::source_imports::PreparedSourceImportValue,
    ) -> Result<
        Vec<super::super::source_imports::PreparedSourceImportPublication>,
        super::super::source_imports::SourceImportError,
    > {
        let host = DeclaredTypeHost::from_registry(
            &context.store,
            &context.files,
            GlobalMergeCompletion::new(context.options.name_resolution),
        )
        .unwrap()
        .with_module_resolutions(&context.module_resolutions);
        super::super::source_imports::preflight_prepared_source_import_publications_with_context(
            context.store(),
            &host,
            &context.global_types,
            context.options,
            std::slice::from_ref(prepared),
        )
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Recheck the same import, manifest, target, and final batch before restoring them.
    fn executable_class_import_publication_rechecks_manifest_target_and_value() {
        use crate::semantic::{
            ValueSymbolLinks,
            source_imports::{SourceImportError, SourceImportInvariant},
        };

        let provider = parsed(EXECUTABLE_IMPORT_BASE);
        let other = parsed(EXECUTABLE_IMPORT_BASE);
        let consumer = parsed(EXECUTABLE_IMPORT_READ);
        let [provider_file, other_file, consumer_file] =
            [202_972, 202_973, 202_974].map(FileId::new);
        let files = [
            (provider_file, &provider),
            (other_file, &other),
            (consumer_file, &consumer),
        ];
        let specifier = node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]);
        let mut context = external_context(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, esm(provider_file)),
            ]),
        );
        let demand = executable_class_demand(&context, &consumer, consumer_file);
        let plan = context
            .resolve_source_class_import_demand(&demand)
            .unwrap()
            .unwrap();
        assert_eq!(
            plan.owner.symbol,
            direct_export(&context, provider_file, "Base")
        );
        assert_eq!(
            plan.owner.source,
            context.source_file(provider_file).unwrap()
        );
        assert!(prepare_executable_class_import(&mut context, &demand).is_err());
        assert!(
            context
                .store()
                .value_symbol_links(demand.binding.alias_symbol)
                .is_none()
        );
        context.check_source_file(provider_file).unwrap();
        let prepared = prepare_executable_class_import(&mut context, &demand).unwrap();
        let publication = preflight_executable_class_import(&context, &prepared).unwrap();
        let instance = context
            .store()
            .declared_type_links(plan.owner.symbol)
            .unwrap()
            .declared_type
            .unwrap();
        assert_ne!(prepared.type_, instance);
        assert_eq!(
            prepared.type_,
            context
                .store()
                .value_symbol_links(plan.owner.symbol)
                .unwrap()
                .resolved_type
                .unwrap()
        );
        assert!(
            context
                .store()
                .value_symbol_links(demand.binding.alias_symbol)
                .is_none()
        );
        assert!(context.store().type_node_links(demand.read.node).is_none());
        let other_owner = direct_export(&context, other_file, "Base");
        let alias_links = context
            .store()
            .alias_symbol_links(demand.binding.alias_symbol)
            .unwrap()
            .clone();
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
                context
                    .store()
                    .alias_symbol_links(demand.binding.alias_symbol)
                    .cloned(),
                context
                    .store()
                    .value_symbol_links(demand.binding.alias_symbol)
                    .cloned(),
                context.store().type_node_links(demand.read.node).cloned(),
                context.store().source_class_provenance(instance).cloned(),
                context.diagnostics().clone(),
            )
        };
        for missing in [true, false] {
            let wrong = if missing {
                CanonicalModuleResolutionManifest::unavailable()
            } else {
                validate_module_resolution_manifest(
                    CanonicalModuleResolutionManifestInput::new([
                        CanonicalModuleResolutionEntry::resolved(specifier, esm(other_file)),
                    ]),
                    context.store().symbol_store(),
                    files.iter().map(|(file, parsed)| {
                        (*file, &parsed.arena, context.file(*file).unwrap().1)
                    }),
                )
                .unwrap()
            };
            let correct = std::mem::replace(&mut context.module_resolutions, wrong);
            let before = snapshot(&context);
            for _ in 0..2 {
                assert!(preflight_executable_class_import(&context, &prepared).is_err());
                assert_eq!(snapshot(&context), before);
            }
            context.module_resolutions = correct;
            assert_eq!(
                preflight_executable_class_import(&context, &prepared),
                Ok(publication.clone())
            );
        }
        for change in 0..2 {
            let mut changed = alias_links.clone();
            if change == 0 {
                changed.immediate_target = Some(other_owner);
            } else {
                changed.alias_target = AliasTargetState::Resolved(other_owner);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_alias_symbol_links(demand.binding.alias_symbol, changed)
            );
            let before = snapshot(&context);
            for _ in 0..2 {
                assert!(preflight_executable_class_import(&context, &prepared).is_err());
                assert_eq!(snapshot(&context), before);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_alias_symbol_links(demand.binding.alias_symbol, alias_links.clone())
            );
        }
        let mut wrong_value = prepared.clone();
        wrong_value.type_ = instance;
        assert_eq!(
            preflight_executable_class_import(&context, &wrong_value),
            Err(SourceImportError::Invariant(
                SourceImportInvariant::PreparedStateChanged(demand.binding.alias_symbol)
            ))
        );
        let value_links = ValueSymbolLinks {
            resolved_type: Some(instance),
            ..ValueSymbolLinks::default()
        };
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(demand.binding.alias_symbol, value_links)
        );
        let before = snapshot(&context);
        assert!(preflight_executable_class_import(&context, &prepared).is_err());
        assert_eq!(snapshot(&context), before);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(demand.binding.alias_symbol, ValueSymbolLinks::default())
        );
        assert_eq!(
            preflight_executable_class_import(&context, &prepared),
            Ok(publication)
        );
        context.check_source_file(consumer_file).unwrap();
        let warm = snapshot(&context);
        for _ in 0..2 {
            context.recheck_source_file(consumer_file).unwrap();
            assert_eq!(snapshot(&context), warm);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // A real later provider failure must not grant its already completed class externally.
    fn executable_class_provider_failure_keeps_completed_class_and_diagnostics_private() {
        let provider = parsed(&format!(
            concat!(
                "interface Matcher {{ m<T extends string>(value: T): T; m<T extends number>(value: T): T; m(left: boolean, right: boolean): boolean; }} ",
                "declare const matcher: Matcher; {} const wrong: string = 0; const bad = matcher.m(true);",
            ),
            EXECUTABLE_IMPORT_BASE
        ));
        let consumer = parsed(EXECUTABLE_IMPORT_READ);
        let [provider_file, consumer_file] = [202_975, 202_976].map(FileId::new);
        let mut context = external_context(
            &[(provider_file, &provider), (consumer_file, &consumer)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]),
                    esm(provider_file),
                ),
            ]),
        );
        let demand = executable_class_demand(&context, &consumer, consumer_file);
        let owner = direct_export(&context, provider_file, "Base");
        let call = provider
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(node_ref(
                    &provider,
                    provider_file,
                    node,
                ))
            })
            .unwrap();
        let expected = SourceCheckError::Call(call);
        let provider_source = context.source_file(provider_file).unwrap();
        let consumer_source = context.source_file(consumer_file).unwrap();
        assert_eq!(context.check_source_file(consumer_file), Err(expected));
        let host = DeclaredTypeHost::from_registry(
            &context.store,
            &context.files,
            GlobalMergeCompletion::new(context.options.name_resolution),
        )
        .unwrap()
        .with_module_resolutions(&context.module_resolutions);
        assert!(
            super::super::classes::completed_source_class_members(context.store(), &host, owner,)
                .unwrap()
                .is_some()
        );
        assert!(
            !context
                .store()
                .source_file_links(provider_source)
                .is_some_and(|links| links.type_checked)
        );
        assert!(
            !context
                .store()
                .source_file_links(consumer_source)
                .is_some_and(|links| links.type_checked)
        );
        assert!(
            context
                .store()
                .value_symbol_links(demand.binding.alias_symbol)
                .is_none()
        );
        assert!(context.diagnostics().is_empty());
        let [diagnostic] = context
            .source_diagnostic_staging
            .get(&provider_source)
            .unwrap()
            .as_slice()
        else {
            panic!("one private provider diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node.unwrap().file, provider_file);
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
                context
                    .store()
                    .source_class_provenance_for_symbol(owner)
                    .cloned(),
                context
                    .store()
                    .value_symbol_links(demand.binding.alias_symbol)
                    .cloned(),
                context.store().source_file_links(provider_source).cloned(),
                context.store().source_file_links(consumer_source).cloned(),
                context.source_diagnostic_staging.clone(),
                context.diagnostics().clone(),
            )
        };
        let failed = snapshot(&context);
        for _ in 0..2 {
            assert!(prepare_executable_class_import(&mut context, &demand).is_err());
            assert_eq!(context.check_source_file(consumer_file), Err(expected));
            assert_eq!(snapshot(&context), failed);
        }
    }

    #[test]
    fn executable_class_imports_keep_the_real_public_constructor_overload_set() {
        let provider = parsed(concat!(
            "export class Base { constructor(value: number); constructor(value: string); ",
            "constructor(value: number | string) {} read() { return 1; } }",
        ));
        let consumer = parsed(EXECUTABLE_IMPORT_READ);
        let [provider_file, consumer_file] = [202_977, 202_978].map(FileId::new);
        let mut context = external_context(
            &[(provider_file, &provider), (consumer_file, &consumer)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]),
                    esm(provider_file),
                ),
            ]),
        );
        let demand = executable_class_demand(&context, &consumer, consumer_file);
        context.check_source_file(consumer_file).unwrap();
        let owner = direct_export(&context, provider_file, "Base");
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let value = context
            .store()
            .value_symbol_links(demand.binding.alias_symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(value, members.shells().value_type());
        let TypeData::Object(data) = context.store().type_payload(value).unwrap().data() else {
            panic!("constructor value")
        };
        let signatures = data.structured.signatures.clone().unwrap();
        assert_eq!(data.structured.call_signature_count, 0);
        assert_eq!(signatures.len(), 2);
        assert_eq!(members.default_construct_signature(), signatures[0]);
        let mut constructors = provider
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::ConstructorDeclaration(constructor) = &record.data else {
                    return None;
                };
                Some((
                    node_ref(&provider, provider_file, node),
                    constructor.body.is_some(),
                ))
            })
            .collect::<Vec<_>>();
        constructors.sort_by_key(|(node, _)| provider.arena.get(node.node).unwrap().range.start);
        let [first, second, implementation] = constructors.as_slice() else {
            panic!("two rows and their implementation")
        };
        assert!(!first.1 && !second.1 && implementation.1);
        for (&signature, declaration) in signatures.iter().zip([first.0, second.0]) {
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(
                record.resolved_return_type(),
                Some(members.shells().instance_type())
            );
            assert_eq!(record.parameters().len(), 1);
            assert_eq!(record.min_argument_count(), 1);
            assert!(record.type_parameters().is_empty());
        }
        let implementation_signature = context
            .store()
            .signature_links(implementation.0)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert!(!signatures.contains(&implementation_signature));
        let counts = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        );
        for _ in 0..2 {
            context.recheck_source_file(consumer_file).unwrap();
            context.recheck_source_file(provider_file).unwrap();
            assert_eq!(
                context.get_nongeneric_class_members(owner),
                Ok(members.clone())
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len()
                ),
                counts
            );
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The cold provider and the warm value reader share the caller's real budget.
    fn executable_class_imports_keep_provider_limits_and_the_spent_value_caller() {
        use crate::semantic::{
            array_types::CanonicalArrayTargets,
            instantiate::{InstantiationError, instantiate_type_with_vector_and_session},
        };

        let provider = parsed(&format!(
            "declare function keep<T>(value: T): T; {EXECUTABLE_IMPORT_BASE} const result = keep(1);",
        ));
        let consumer = parsed(EXECUTABLE_IMPORT_READ);
        let [provider_file, consumer_file] = [202_979, 202_980].map(FileId::new);
        let mut context = external_context(
            &[(provider_file, &provider), (consumer_file, &consumer)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]),
                    esm(provider_file),
                ),
            ]),
        );
        let demand = executable_class_demand(&context, &consumer, consumer_file);
        let call = provider
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(node_ref(
                    &provider,
                    provider_file,
                    node,
                ))
            })
            .unwrap();
        let function = provider
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(node_ref(
                    &provider,
                    provider_file,
                    node,
                ))
            })
            .unwrap();
        let keep = context
            .file(provider_file)
            .unwrap()
            .1
            .symbol(function)
            .unwrap();
        context.instantiation_session = InstantiationSession::new(InstantiationLimits {
            max_count: 0,
            ..InstantiationLimits::default()
        });
        let expected = SourceCheckError::Call(call);
        for _ in 0..2 {
            let mark = context.instantiation_session.limit_event_mark();
            assert_eq!(context.check_source_file(consumer_file), Err(expected));
            assert!(
                context
                    .instantiation_session
                    .limit_event_occurred_since(mark)
            );
            assert_eq!(
                (
                    context.instantiation_session.query_count(),
                    context.instantiation_session.total_count()
                ),
                (0, 0)
            );
            for file in [provider_file, consumer_file] {
                assert!(
                    !context
                        .store()
                        .source_file_links(context.source_file(file).unwrap())
                        .is_some_and(|links| links.type_checked)
                );
            }
            assert!(
                context
                    .store()
                    .value_symbol_links(demand.binding.alias_symbol)
                    .is_none()
            );
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert!(context.diagnostics().is_empty());
        }
        context.instantiation_session = InstantiationSession::new(InstantiationLimits::default());
        context.check_source_file(consumer_file).unwrap();
        assert!(context.instantiation_session.total_count() > 0);
        let prepared = prepare_executable_class_import(&mut context, &demand).unwrap();
        let counts = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.instantiation_session.total_count(),
        );
        for _ in 0..2 {
            context.recheck_source_file(consumer_file).unwrap();
            context.recheck_source_file(provider_file).unwrap();
            assert_eq!(
                prepare_executable_class_import(&mut context, &demand),
                Ok(prepared.clone())
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.instantiation_session.total_count()
                ),
                counts
            );
        }
        let callable = context
            .store()
            .source_callable_type_for_owner(keep)
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let parameter = context
            .store()
            .signature(signature)
            .unwrap()
            .type_parameters()[0];
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let arrays = CanonicalArrayTargets::from_global_types(context.global_types());
        context.instantiation_session = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut context.store,
                parameter,
                &[parameter],
                &[number],
                Some(arrays),
                &mut context.instantiation_session,
            ),
            Ok(number)
        );
        for _ in 0..2 {
            assert_eq!(
                prepare_executable_class_import(&mut context, &demand),
                Ok(prepared.clone())
            );
            preflight_executable_class_import(&context, &prepared).unwrap();
            assert_eq!(
                (
                    context.instantiation_session.query_count(),
                    context.instantiation_session.total_count(),
                    context.instantiation_session.limit_event_count()
                ),
                (1, 1, 0)
            );
        }
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut context.store,
                parameter,
                &[parameter],
                &[number],
                Some(arrays),
                &mut context.instantiation_session,
            ),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 })
        );
        assert_eq!(
            (
                context.instantiation_session.query_count(),
                context.instantiation_session.total_count(),
                context.instantiation_session.limit_event_count()
            ),
            (1, 1, 1)
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The imported base keeps separate lexical, constructor, and instance caches.
    fn executable_class_heritage_rechecks_its_alias_and_both_type_roles() {
        use crate::semantic::{SymbolNodeLinks, TypeNodeLinks};

        let provider = parsed(EXECUTABLE_IMPORT_BASE);
        let consumer = parsed(concat!(
            "import { Base as Imported } from './base'; ",
            "export class Derived extends Imported { readAgain(): number { return this.value; } }",
        ));
        let [provider_file, consumer_file] = [202_981, 202_982].map(FileId::new);
        let mut context = external_context(
            &[(provider_file, &provider), (consumer_file, &consumer)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]),
                    esm(provider_file),
                ),
            ]),
        );
        let (wrapper, expression) = consumer
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ExpressionWithTypeArguments(data) = &record.data else {
                    return None;
                };
                Some((
                    node_ref(&consumer, consumer_file, node),
                    node_ref(&consumer, consumer_file, data.expression),
                ))
            })
            .unwrap();
        let alias = alias_symbol(
            &context,
            alias_declaration_named(&consumer, consumer_file, "Imported"),
        );
        let base = direct_export(&context, provider_file, "Base");
        let derived = direct_export(&context, consumer_file, "Derived");
        context.check_source_file(consumer_file).unwrap();
        let members = context.get_nongeneric_class_members(derived).unwrap();
        let base_members = context.get_nongeneric_class_members(base).unwrap();
        let expression_symbol = context
            .store()
            .symbol_node_links(expression)
            .unwrap()
            .clone();
        let expression_type = context.store().type_node_links(expression).unwrap().clone();
        let wrapper_type = context.store().type_node_links(wrapper).unwrap().clone();
        let alias_value = context.store().value_symbol_links(alias).unwrap().clone();
        assert_eq!(expression_symbol.resolved_symbol, Some(alias));
        assert_eq!(
            expression_type.resolved_type,
            Some(base_members.shells().value_type())
        );
        assert_eq!(
            wrapper_type.resolved_type,
            Some(base_members.shells().instance_type())
        );
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().symbol_node_links(expression).cloned(),
                context.store().type_node_links(expression).cloned(),
                context.store().type_node_links(wrapper).cloned(),
                context.store().value_symbol_links(alias).cloned(),
                context
                    .store()
                    .source_class_provenance_for_symbol(derived)
                    .cloned(),
                context.diagnostics().clone(),
            )
        };
        let warm = snapshot(&context);
        for change in 0..4 {
            let store = context.store_mut_for_test();
            match change {
                0 => assert!(store.set_symbol_node_links(
                    expression,
                    SymbolNodeLinks {
                        resolved_symbol: Some(base)
                    }
                )),
                1 => assert!(store.set_type_node_links(
                    expression,
                    TypeNodeLinks {
                        resolved_type: Some(base_members.shells().instance_type()),
                        ..expression_type.clone()
                    }
                )),
                2 => assert!(store.set_type_node_links(
                    wrapper,
                    TypeNodeLinks {
                        resolved_type: Some(base_members.shells().value_type()),
                        ..wrapper_type.clone()
                    }
                )),
                3 => assert!(store.set_value_symbol_links(
                    alias,
                    super::super::ValueSymbolLinks {
                        resolved_type: Some(base_members.shells().instance_type()),
                        ..alias_value.clone()
                    }
                )),
                _ => unreachable!(),
            }
            let poisoned = snapshot(&context);
            for _ in 0..2 {
                let result = context.get_nongeneric_class_members(derived);
                if change == 3 {
                    assert_eq!(
                        result,
                        Err(ClassError::Invariant(
                            super::super::classes::ClassInvariant::InvalidHeritage(expression)
                        ))
                    );
                } else {
                    assert!(result.is_err());
                }
                assert_eq!(snapshot(&context), poisoned);
            }
            let store = context.store_mut_for_test();
            assert!(store.set_symbol_node_links(expression, expression_symbol.clone()));
            assert!(store.set_type_node_links(expression, expression_type.clone()));
            assert!(store.set_type_node_links(wrapper, wrapper_type.clone()));
            assert!(store.set_value_symbol_links(alias, alias_value.clone()));
            assert_eq!(
                context.get_nongeneric_class_members(derived),
                Ok(members.clone())
            );
            assert_eq!(snapshot(&context), warm);
        }
        let manifest = std::mem::replace(
            &mut context.module_resolutions,
            CanonicalModuleResolutionManifest::unavailable(),
        );
        assert!(context.get_nongeneric_class_members(derived).is_err());
        assert_eq!(snapshot(&context), warm);
        context.module_resolutions = manifest;
        assert_eq!(context.get_nongeneric_class_members(derived), Ok(members));
        assert_eq!(snapshot(&context), warm);
    }

    #[test]
    fn executable_class_imports_do_not_treat_legacy_only_headers_as_source_completion() {
        let provider = parsed("export class Base {}");
        let consumer = parsed(EXECUTABLE_IMPORT_READ);
        let [provider_file, consumer_file] = [202_983, 202_984].map(FileId::new);
        let mut context = external_context(
            &[(provider_file, &provider), (consumer_file, &consumer)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&consumer, consumer_file, module_specifiers(&consumer)[0]),
                    esm(provider_file),
                ),
            ]),
        );
        let demand = executable_class_demand(&context, &consumer, consumer_file);
        let owner = direct_export(&context, provider_file, "Base");
        let expected = SourceCheckError::Unsupported(source::UnsupportedSourceSyntax::Import(
            demand.read.node,
        ));
        for _ in 0..2 {
            assert_eq!(context.check_source_file(consumer_file), Err(expected));
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(provider_file).unwrap())
                    .unwrap()
                    .type_checked
            );
            assert!(
                !context
                    .store()
                    .source_file_links(context.source_file(consumer_file).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
            assert!(
                context
                    .store()
                    .source_class_provenance_for_symbol(owner)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(demand.binding.alias_symbol)
                    .is_none()
            );
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the earlier alias target and the final augmentation result together.
    fn native_ambient_export_receipts_follow_star_augmentations_and_finalize_once() {
        let parsed = [
            "export declare class Foo {}",
            "export * from './provider';",
            "declare module 'mymod' { import { Foo as foo } from 'barrel'; export { foo }; }",
            "declare module 'mymod' { export const foo: number; }",
            "export {}; declare module 'barrel' { interface Foo { extra: number; } }",
        ]
        .map(parsed);
        let files = [8_430, 8_431, 8_432, 8_433, 8_434].map(FileId::new);
        let declarations = |index: usize, kind| {
            parsed[index]
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then_some(node_ref(&parsed[index], files[index], node))
                })
                .unwrap()
        };
        let modules = [2, 3].map(|index| declarations(index, SyntaxKind::ModuleDeclaration));
        let augmentation = declarations(4, SyntaxKind::ModuleDeclaration);
        let NodeData::ModuleDeclaration(augmentation_data) =
            &parsed[4].arena.get(augmentation.node).unwrap().data
        else {
            unreachable!()
        };
        let facts = parsed
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    files[index],
                    parsed,
                    true,
                    if index == 2 || index == 3 {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
            })
            .collect::<Vec<_>>();
        let manifest = CanonicalModuleResolutionManifestInput::new([
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&parsed[1], files[1], module_specifiers(&parsed[1])[0]),
                esm(files[0]),
            ),
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&parsed[2], files[2], module_specifiers(&parsed[2])[0]),
                esm(files[1]),
            ),
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&parsed[4], files[4], augmentation_data.name),
                esm(files[1]),
            ),
        ]);
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            completed_bindings_with_facts(&facts),
            parsed
                .iter()
                .enumerate()
                .map(|(index, parsed)| (files[index], &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            manifest,
        )
        .unwrap();
        let raw_owner = alias_symbol(&context, modules[0]);
        let owner = context.store().get_merged_symbol(raw_owner).unwrap();
        let raw_class = alias_symbol(&context, declarations(0, SyntaxKind::ClassDeclaration));
        let interface = alias_symbol(&context, declarations(4, SyntaxKind::InterfaceDeclaration));
        let target = context.store().get_merged_symbol(raw_class).unwrap();
        assert_ne!(target, raw_class);
        assert_eq!(context.store().get_merged_symbol(interface), Some(target));
        assert_eq!(
            context.store().symbol(target).unwrap().declarations(),
            Some(
                [
                    declarations(0, SyntaxKind::ClassDeclaration),
                    declarations(4, SyntaxKind::InterfaceDeclaration),
                ]
                .as_slice()
            )
        );
        let saved = context
            .store()
            .native_ambient_module_exports(owner)
            .unwrap()
            .clone();
        assert_eq!(saved.owner, owner);
        let [losing] = saved.losing.as_ref() else {
            panic!("the native collision retains one losing reexport")
        };
        assert_eq!(losing.aliases.len(), 2);
        for edge in &losing.aliases {
            assert_eq!(edge.target, raw_class);
            assert_eq!(edge.canonical_target, target);
        }
        assert_eq!(losing.aliases[1].immediate, raw_class);
        assert_eq!(losing.aliases[1].canonical_immediate, target);
        assert_eq!(
            context
                .store()
                .source_global_bindings()
                .unwrap()
                .get(EscapedName::source("\"mymod\"").as_ref())
                .unwrap()
                .declarations(),
            Some(modules.as_slice())
        );
        assert!(context.store().value_symbol_links(target).is_none());
        assert!(
            context
                .store()
                .value_symbol_links(saved.selected.entries[0].symbol)
                .is_none()
        );

        let before = format!("{:?}", context.store);
        assert!(
            !context
                .store
                .finalize_native_ambient_module_exports(&context.files)
        );
        assert_eq!(format!("{:?}", context.store), before);
        let type_ = context.get_type_of_module_value(owner).unwrap();
        let warm = format!("{:?}", context.store);
        let diagnostics = context.diagnostics.clone();
        for _ in 0..2 {
            assert_eq!(context.get_type_of_module_value(owner), Ok(type_));
            assert_eq!(format!("{:?}", context.store), warm);
            assert_eq!(context.diagnostics, diagnostics);
        }
        assert!(
            !context
                .store
                .finalize_native_ambient_module_exports(&context.files)
        );
        assert_eq!(format!("{:?}", context.store), warm);
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
        assert!(!defaults.strict_property_initialization);
        assert!(!defaults.use_unknown_in_catch_variables);
        assert!(!defaults.no_implicit_any);
        assert!(!defaults.no_implicit_this);
        assert!(!defaults.no_unchecked_indexed_access);
        assert!(!defaults.no_unused_locals);
        assert!(!defaults.no_unused_parameters);
        assert_eq!(defaults.allow_unreachable_code, None);
        assert!(!defaults.preserve_const_enums);
        assert!(!defaults.should_preserve_const_enums());
        assert!(!defaults.isolated_modules);
        assert_eq!(defaults.jsx_runtime, CanonicalJsxRuntime::Preserve);
        assert!(!defaults.emit_common_js);
        assert!(!defaults.no_emit);
        assert!(!defaults.no_error_truncation);
        assert!(!defaults.check_bigint_target);

        let intrinsic = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        };
        let options = CanonicalCheckerOptions::from(intrinsic);
        assert_eq!(options.intrinsic, intrinsic);
        assert!(!options.strict_builtin_iterator_return);
        assert!(!options.strict_function_types);
        assert!(!options.strict_property_initialization);
        assert!(!options.use_unknown_in_catch_variables);
        assert!(!options.no_implicit_any);
        assert!(!options.no_implicit_this);
        assert!(!options.no_unchecked_indexed_access);
        assert!(!options.no_unused_locals);
        assert!(!options.no_unused_parameters);
        assert_eq!(options.allow_unreachable_code, None);
        assert!(!options.preserve_const_enums);
        assert!(!options.should_preserve_const_enums());
        assert!(!options.isolated_modules);
        assert_eq!(options.jsx_runtime, CanonicalJsxRuntime::Preserve);
        assert!(!options.emit_common_js);
        assert!(!options.no_emit);
        assert!(!options.no_error_truncation);
        assert!(!options.check_bigint_target);
    }

    #[test]
    fn const_enum_preservation_follows_explicit_and_isolated_module_options() {
        for options in [
            CanonicalCheckerOptions {
                preserve_const_enums: true,
                ..CanonicalCheckerOptions::default()
            },
            CanonicalCheckerOptions {
                isolated_modules: true,
                ..CanonicalCheckerOptions::default()
            },
            CanonicalCheckerOptions {
                name_resolution: CanonicalNameResolverOptions {
                    isolated_modules: true,
                    ..CanonicalNameResolverOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
            CanonicalCheckerOptions {
                name_resolution: CanonicalNameResolverOptions {
                    verbatim_module_syntax: true,
                    ..CanonicalNameResolverOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        ] {
            assert!(options.should_preserve_const_enums());
        }
    }

    #[test]
    fn classic_runtime_retains_authenticated_factory_namespaces_and_replays_warm() {
        let importer = parsed("import * as MyLib from './library';");
        let library = parsed(concat!(
            "namespace JSX { export interface IntrinsicElements {} } ",
            "export { JSX };",
        ));
        let importer_file = FileId::new(8_401);
        let library_file = FileId::new(8_402);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let mut context = external_context(
            &[(importer_file, &importer), (library_file, &library)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, esm(library_file)),
            ]),
        );
        let source = context.source_file(importer_file).unwrap();
        let options = context.options();
        let namespace_export = direct_export(&context, library_file, "JSX");
        let runtime = CanonicalJsxRuntimeEvidence::Classic {
            factory_namespace: "MyLib",
            fragment_factory_namespace: "MyLib",
            fragment_factory_required: false,
            fragment_factory_pragma_required: false,
        };
        assert!(context.store().source_file_links(source).is_none());
        assert!(
            context
                .store()
                .alias_symbol_links(namespace_export)
                .is_none()
        );

        context
            .check_source_file_with_jsx_runtime(importer_file, runtime)
            .unwrap();

        let links = context.store().source_file_links(source).unwrap();
        assert_eq!(links.local_jsx_namespace, "MyLib");
        assert!(links.type_checked);
        assert_eq!(context.options(), options);
        assert!(
            context
                .store()
                .alias_symbol_links(namespace_export)
                .is_none()
        );
        let warm = context.store().checker_link_allocated_lengths();

        context
            .check_source_file_with_jsx_runtime(importer_file, runtime)
            .unwrap();

        assert_eq!(context.store().checker_link_allocated_lengths(), warm);
        assert_eq!(
            context
                .store()
                .source_file_links(source)
                .unwrap()
                .local_jsx_namespace,
            "MyLib",
        );
        assert_eq!(context.options(), options);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn runtime_recheck_bypasses_completion_and_validates_retained_cache() {
        let source = parsed("const value: any = { nested: { missing: undefined } };");
        let file = FileId::new(8_405);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let object = source
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::VariableDeclaration(declaration) => declaration
                    .initializer
                    .map(|node| node_ref(&source, file, node)),
                _ => None,
            })
            .unwrap();
        let runtime = CanonicalJsxRuntimeEvidence::Preserve;
        context
            .check_source_file_with_jsx_runtime(file, runtime)
            .unwrap();
        let source_ref = context.source_file(file).unwrap();
        let type_id = context
            .store()
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let flags = context
            .store()
            .type_payload(type_id)
            .unwrap()
            .object_flags();
        assert!(flags.contains(ObjectFlags::CONTAINS_WIDENING_TYPE));
        let lengths = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(type_id, flags & !ObjectFlags::CONTAINS_WIDENING_TYPE)
        );
        context
            .check_source_file_with_jsx_runtime(file, runtime)
            .unwrap();

        assert!(matches!(
            context.recheck_source_file_with_jsx_runtime(file, runtime),
            Err(SourceCheckError::ObjectLiteral(
                crate::semantic::SourceObjectLiteralError::InvalidCache { node, type_: Some(cached) }
            )) if node == object && cached == type_id
        ));
        assert!(
            !context
                .store()
                .source_file_links(source_ref)
                .unwrap()
                .type_checked
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(type_id, flags)
        );
        context
            .recheck_source_file_with_jsx_runtime(file, runtime)
            .unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_ref)
                .unwrap()
                .type_checked
        );
        assert_eq!(
            context
                .store()
                .type_node_links(object)
                .and_then(|links| links.resolved_type),
            Some(type_id),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            lengths,
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep failed calls, staged diagnostics, and both recheck APIs together.
    fn never_completed_source_rechecks_preserve_failure_and_staged_diagnostics() {
        let source = parsed(concat!(
            "interface Matcher { ",
            "m<T extends string>(value: T): T; ",
            "m<T extends number>(value: T): T; ",
            "m(left: boolean, right: boolean): boolean; }\n",
            "declare const matcher: Matcher;\n",
            "const wrong: string = 0;\n",
            "const bad = matcher.m(true);\n",
        ));
        let file = FileId::new(8_406);
        let calls = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(node_ref(&source, file, node))
            })
            .collect::<Vec<_>>();
        let [call] = calls.as_slice() else {
            panic!("the source has one rejected overload call");
        };
        let (wrong, annotation) = source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(declaration) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &source.arena.get(declaration.name)?.data else {
                    return None;
                };
                (name.text == "wrong").then_some((
                    node_ref(&source, file, declaration.name),
                    node_ref(&source, file, declaration.type_?),
                ))
            })
            .unwrap();
        assert_eq!(
            source.arena.get(annotation.node).unwrap().kind,
            SyntaxKind::StringKeyword,
        );

        for with_runtime in [false, true] {
            let mut context = CanonicalCheckerContext::new(
                completed_bindings(&[(file, &source)]),
                vec![(file, &source.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let source_ref = context.source_file(file).unwrap();
            let cold_links = context.store().checker_link_allocated_lengths();
            assert!(context.store().source_file_links(source_ref).is_none());
            assert_eq!(context.clear_source_file_completion(file), Ok(()));
            assert_eq!(context.store().checker_link_allocated_lengths(), cold_links);
            assert!(context.store().source_file_links(source_ref).is_none());
            let check =
                |context: &mut CanonicalCheckerContext<'_>, force| match (with_runtime, force) {
                    (false, false) => context.check_source_file(file),
                    (false, true) => context.recheck_source_file(file),
                    (true, false) => context.check_source_file_with_jsx_runtime(
                        file,
                        CanonicalJsxRuntimeEvidence::Preserve,
                    ),
                    (true, true) => context.recheck_source_file_with_jsx_runtime(
                        file,
                        CanonicalJsxRuntimeEvidence::Preserve,
                    ),
                };
            assert_eq!(
                check(&mut context, false),
                Err(SourceCheckError::Call(*call))
            );
            assert!(context.diagnostics().is_empty());
            assert!(context.store().source_file_links(source_ref).is_none());
            let staged = context.source_diagnostic_staging.get(&source_ref).unwrap();
            let [diagnostic] = staged.as_slice() else {
                panic!("the earlier assignment error stays private until completion");
            };
            assert_eq!(diagnostic.node, Some(wrong));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert!(context.store().type_node_links(annotation).is_none());
            assert!(context.store().type_node_links(wrong).is_none());
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [
                        store.type_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                        store.type_alias_len(),
                        store.symbol_store().symbol_table_len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    source
                        .arena
                        .iter()
                        .map(|(node, _)| {
                            let node = node_ref(&source, file, node);
                            (
                                store.type_node_links(node).cloned(),
                                store.symbol_node_links(node).cloned(),
                                store.signature_links(node).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    store.source_file_links(source_ref).cloned(),
                    context.diagnostics().clone(),
                    context.source_diagnostic_staging.clone(),
                )
            };
            let failed = snapshot(&context);
            assert_eq!(context.get_type_from_type_node(annotation), Ok(string));
            assert_eq!(snapshot(&context), failed);
            for force in [false, true, true] {
                assert_eq!(
                    check(&mut context, force),
                    Err(SourceCheckError::Call(*call))
                );
                assert_eq!(snapshot(&context), failed);
                assert!(context.store().type_node_links(*call).is_none());
                assert!(context.store().signature_links(*call).is_none());
                assert!(context.store().type_resolution_is_empty());
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep foreign-store and replacement-source checks with their exact restores.
    fn source_recheck_rejects_foreign_and_replaced_source_ownership() {
        let source = parsed("declare const value: number;");
        let replacement = parsed("declare const value: string;");
        let file = FileId::new(8_407);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let mut replacement_context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &replacement)]),
            vec![(file, &replacement.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let original_source = context.source_file(file).unwrap();
        let replacement_source = replacement_context.source_file(file).unwrap();
        assert_ne!(
            original_source.node_ref().arena,
            replacement_source.node_ref().arena
        );
        assert!(context.store().source_file_links(original_source).is_none());
        assert!(
            replacement_context
                .store()
                .source_file_links(replacement_source)
                .is_none()
        );
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.options(),
                context.diagnostics().clone(),
                context.source_diagnostic_staging.clone(),
            )
        };
        let original = snapshot(&context);
        let replacement_state = snapshot(&replacement_context);
        for with_runtime in [false, true] {
            let recheck = |context: &mut CanonicalCheckerContext<'_>, file| {
                if with_runtime {
                    context.recheck_source_file_with_jsx_runtime(
                        file,
                        CanonicalJsxRuntimeEvidence::Preserve,
                    )
                } else {
                    context.recheck_source_file(file)
                }
            };
            let foreign_file = FileId::new(8_408);
            assert_eq!(
                recheck(&mut context, foreign_file),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingFile(foreign_file),
                )),
            );
            std::mem::swap(&mut context.store, &mut replacement_context.store);
            assert!(!context.store().contains_source_file(original_source));
            assert_eq!(
                recheck(&mut context, file),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::StoreSourceMismatch(original_source),
                )),
            );
            std::mem::swap(&mut context.store, &mut replacement_context.store);
            std::mem::swap(&mut context.files, &mut replacement_context.files);
            assert_eq!(context.source_file(file), Some(replacement_source));
            assert!(!context.store().contains_source_file(replacement_source));
            assert_eq!(
                recheck(&mut context, file),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::StoreSourceMismatch(replacement_source),
                )),
            );
            std::mem::swap(&mut context.files, &mut replacement_context.files);
            assert_eq!(snapshot(&context), original);
            assert_eq!(snapshot(&replacement_context), replacement_state);
            assert!(context.store().source_file_links(original_source).is_none());
        }
        context.recheck_source_file(file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(original_source)
                .unwrap()
                .type_checked
        );
        let value = global_symbol(&context, "value").unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(value)
                .unwrap()
                .resolved_type,
            Some(context.store().intrinsic_bootstrap().unwrap().number_type),
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn classic_runtime_does_not_cache_modules_without_a_binder_owned_jsx_namespace() {
        let importer = parsed("import * as MyLib from './library';");
        let library = parsed("export const JSX: number = 1;");
        let importer_file = FileId::new(8_403);
        let library_file = FileId::new(8_404);
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let mut context = external_context(
            &[(importer_file, &importer), (library_file, &library)],
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, esm(library_file)),
            ]),
        );
        let source = context.source_file(importer_file).unwrap();
        let options = context.options();

        context
            .check_source_file_with_jsx_runtime(
                importer_file,
                CanonicalJsxRuntimeEvidence::Classic {
                    factory_namespace: "MyLib",
                    fragment_factory_namespace: "MyLib",
                    fragment_factory_required: false,
                    fragment_factory_pragma_required: false,
                },
            )
            .unwrap();

        assert!(
            context
                .store()
                .source_file_links(source)
                .unwrap()
                .local_jsx_namespace
                .is_empty()
        );
        assert_eq!(context.options(), options);
        assert!(context.diagnostics().is_empty());
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
            no_unchecked_indexed_access: true,
            no_unused_locals: true,
            no_unused_parameters: true,
            allow_unreachable_code: Some(false),
            preserve_const_enums: true,
            isolated_modules: true,
            emit_common_js: true,
            no_emit: true,
            uses_wildcard_types: true,
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
        assert!(context.options().no_unchecked_indexed_access);
        assert!(context.options().no_unused_locals);
        assert!(context.options().no_unused_parameters);
        assert_eq!(context.options().allow_unreachable_code, Some(false));
        assert!(context.options().preserve_const_enums);
        assert!(context.options().should_preserve_const_enums());
        assert!(context.options().isolated_modules);
        assert!(context.options().emit_common_js);
        assert!(context.options().no_emit);
        assert!(context.options().uses_wildcard_types);
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
    fn context_relation_queries_share_the_current_instantiation_budget() {
        let source = parsed(concat!(
            "interface Wrapper<Value> { value: Value } ",
            "type First = { [Key in 'first']: Wrapper<Key> }; ",
            "type FirstTarget = { first: Wrapper<'first'> }; ",
            "type Second = { [Key in 'second']: Wrapper<Key> }; ",
            "type SecondTarget = { second: Wrapper<'second'> };",
        ));
        let file = FileId::new(806);
        for relation in [
            RelationKind::Assignable,
            RelationKind::Identity,
            RelationKind::Comparable,
        ] {
            let mut context = CanonicalCheckerContext::new(
                completed_bindings(&[(file, &source)]),
                vec![(file, &source.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            context.check_source_file(file).unwrap();
            let mut types = Vec::new();
            for name in ["First", "FirstTarget", "Second", "SecondTarget"] {
                types.push(
                    context
                        .get_type_from_type_node(type_alias_body(&source, file, name))
                        .unwrap(),
                );
            }
            let error = context.store().intrinsic_bootstrap().unwrap().error_type;
            context.instantiation_session = InstantiationSession::new_recovering(
                context.store(),
                InstantiationLimits {
                    max_depth: 100,
                    max_count: 2,
                },
                error,
            )
            .unwrap();
            assert_eq!(context.is_type_assignable_to(types[0], types[1]), Ok(true));
            assert_eq!(context.instantiation_session.total_count(), 2);
            let limit_mark = context.instantiation_session.limit_event_mark();
            let result = match relation {
                RelationKind::Assignable => context.is_type_assignable_to(types[2], types[3]),
                RelationKind::Identity => context.is_type_identical_to(types[2], types[3]),
                RelationKind::Comparable => context.is_type_comparable_to(types[2], types[3]),
                _ => unreachable!(),
            };
            assert_eq!(
                result,
                Err(RelationUnavailable::UnsupportedStructuredType(types[2]))
            );
            assert!(
                context
                    .instantiation_session
                    .limit_event_occurred_since(limit_mark)
            );
            assert_eq!(context.instantiation_session.total_count(), 2);
            assert!(context.diagnostics().is_empty());
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
            after_uncached.name_resolver_views + bodies.len()
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
    fn script_duplicate_capture_keeps_both_alias_query_identities() {
        let first = parsed("type Repeated = { first: number };");
        let second = parsed("type Repeated = { second: string };");
        let first_file = FileId::new(8_241);
        let second_file = FileId::new(8_242);
        let bodies = [
            type_alias_body(&first, first_file, "Repeated"),
            type_alias_body(&second, second_file, "Repeated"),
        ];
        let declarations = [(&first, bodies[0]), (&second, bodies[1])].map(|(parsed, body)| {
            NodeRef::new(
                body.arena,
                body.file,
                parsed.arena.get(body.node).unwrap().parent.unwrap(),
            )
        });
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(first_file, &first), (second_file, &second)]),
            vec![(first_file, &first.arena), (second_file, &second.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let aliases = declarations.map(|declaration| {
            context
                .file(declaration.file)
                .unwrap()
                .1
                .symbol(declaration)
                .unwrap()
        });
        assert_ne!(aliases[0], aliases[1]);
        assert_eq!(global_symbol(&context, "Repeated"), Some(aliases[0]));
        for (alias, declaration) in aliases.into_iter().zip(declarations) {
            assert_eq!(context.store().get_merged_symbol(alias), Some(alias));
            assert_eq!(
                context.store().symbol(alias).unwrap().declarations(),
                Some([declaration].as_slice()),
            );
        }

        let captured = |context: &CanonicalCheckerContext<'_>| {
            let bindings = context.store().source_global_bindings().unwrap();
            let binding = bindings
                .get(EscapedName::source("Repeated").as_ref())
                .unwrap();
            (
                bindings.table,
                binding.table_symbol,
                binding.symbol,
                binding.flags,
                binding.declarations().map(<[NodeRef]>::to_vec),
            )
        };
        let before = captured(&context);
        assert_eq!(
            before,
            (
                context.globals(),
                aliases[0],
                aliases[0],
                SymbolFlags::TYPE_ALIAS,
                Some(vec![declarations[0]]),
            ),
        );
        assert!(
            context
                .store()
                .source_global_bindings()
                .unwrap()
                .iter()
                .all(|binding| {
                    binding.symbol != aliases[1] && binding.table_symbol != aliases[1]
                })
        );
        let diagnostics = context.diagnostics().clone();
        assert_eq!(diagnostics.len(), 2);
        let types = bodies.map(|body| context.get_type_from_type_node(body).unwrap());
        assert_ne!(types[0], types[1]);
        for (alias, type_) in aliases.into_iter().zip(types) {
            assert_eq!(context.get_declared_type_of_symbol(alias), Ok(type_));
            let type_alias = context
                .store()
                .type_payload(type_)
                .unwrap()
                .alias()
                .unwrap();
            assert_eq!(
                context.store().type_alias(type_alias).unwrap().symbol(),
                Some(alias),
            );
        }
        assert_eq!(captured(&context), before);
        let allocations = (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().merged_symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            for ((alias, body), type_) in aliases.into_iter().zip(bodies).zip(types) {
                assert_eq!(context.get_type_from_type_node(body), Ok(type_));
                assert_eq!(context.get_declared_type_of_symbol(alias), Ok(type_));
                assert_eq!(context.store().get_merged_symbol(alias), Some(alias));
            }
            assert_eq!(captured(&context), before);
            assert_eq!(global_symbol(&context, "Repeated"), Some(aliases[0]));
            for (alias, declaration) in aliases.into_iter().zip(declarations) {
                assert_eq!(
                    context.store().symbol(alias).unwrap().declarations(),
                    Some([declaration].as_slice()),
                );
            }
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().type_alias_len(),
                    context.store().symbol_len(),
                    context.store().merged_symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                allocations,
            );
        }
    }

    #[test]
    fn script_duplicate_reporter_checks_names_limits_and_foreign_ownership() {
        fn declaration_names(
            parsed: &ParseResult,
            file: FileId,
            kind: SyntaxKind,
        ) -> Vec<(NodeRef, NodeRef)> {
            parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    if record.kind != kind {
                        return None;
                    }
                    let name = match &record.data {
                        NodeData::VariableDeclaration(data) => data.name,
                        NodeData::ClassDeclaration(data) => data.name?,
                        NodeData::EnumDeclaration(data) => data.name,
                        _ => return None,
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, name),
                    ))
                })
                .collect()
        }

        let primary = |node, code, arguments: Vec<String>, related_information| {
            CanonicalCheckerDiagnostic {
                node: Some(node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(message_by_code(code).unwrap(), arguments),
                related_information,
            }
        };
        let leading = |node, spelling: &str| CanonicalCheckerRelatedInformation {
            node: Some(node),
            diagnostic: Diagnostic::with_arguments(message_by_code(6203).unwrap(), [spelling]),
        };
        let variables = parsed(concat!(
            "declare var Item: number;\n",
            "declare var Item: number;\n",
            "declare var Item: number;\n",
            "declare var Item: number;\n",
            "declare var Item: number;\n",
            "declare var Item: number;\n",
        ));
        let class = parsed(r"declare class \u0049tem {}");
        let variable_file = FileId::new(8_243);
        let class_file = FileId::new(8_244);
        let variable_names =
            declaration_names(&variables, variable_file, SyntaxKind::VariableDeclaration);
        let class_names = declaration_names(&class, class_file, SyntaxKind::ClassDeclaration);
        assert_eq!(variable_names.len(), 6);
        let [(class_declaration, class_name)] = class_names.as_slice() else {
            panic!("expected the one named class");
        };
        let (class_declaration, class_name) = (*class_declaration, *class_name);
        assert_eq!(
            class.arena.get(class_name.node).unwrap().range,
            TextRange::new(TextPos::new(14), TextPos::new(23)),
        );
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(variable_file, &variables), (class_file, &class)]),
            vec![(variable_file, &variables.arena), (class_file, &class.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let target = global_symbol(&context, "Item").unwrap();
        let source = context
            .file(class_file)
            .unwrap()
            .1
            .symbol(class_declaration)
            .unwrap();
        let spelling = r"\u0049tem";
        let mut expected = vec![primary(
            class_name,
            2300,
            vec![spelling.to_owned()],
            variable_names
                .iter()
                .take(5)
                .enumerate()
                .map(|(index, &(_, name))| {
                    if index == 0 {
                        leading(name, spelling)
                    } else {
                        CanonicalCheckerRelatedInformation {
                            node: Some(name),
                            diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
                        }
                    }
                })
                .collect::<Vec<_>>(),
        )];
        expected.extend(variable_names.iter().map(|&(_, name)| {
            primary(
                name,
                2300,
                vec![spelling.to_owned()],
                vec![leading(class_name, spelling)],
            )
        }));
        assert_eq!(context.diagnostics().as_slice(), expected.as_slice());
        let original_diagnostics = context.diagnostics().clone();
        let diagnostic = SymbolMergeDiagnostic {
            kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
            target,
            source,
        };
        let allocations = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().merged_symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );
        let mut reported = CanonicalCheckerDiagnostics::default();
        ScriptGlobalMergeHost {
            files: &context.files,
            diagnostics: &mut reported,
        }
        .report_merge_diagnostic(context.store(), diagnostic)
        .unwrap();
        assert_eq!(reported, original_diagnostics);

        let foreign_class = parsed("declare class Item {}");
        let foreign = CanonicalCheckerContext::new(
            completed_bindings(&[(class_file, &foreign_class)]),
            vec![(class_file, &foreign_class.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let foreign_symbol = global_symbol(&foreign, "Item").unwrap();
        for invalid in [
            SymbolMergeDiagnostic {
                source: foreign_symbol,
                ..diagnostic
            },
            SymbolMergeDiagnostic {
                target: foreign_symbol,
                ..diagnostic
            },
        ] {
            assert_eq!(
                ScriptGlobalMergeHost {
                    files: &context.files,
                    diagnostics: &mut reported,
                }
                .report_merge_diagnostic(context.store(), invalid),
                Err(SymbolMergeError::InvalidSymbol(foreign_symbol)),
            );
            assert_eq!(reported, original_diagnostics);
        }
        let foreign_declaration = foreign
            .store()
            .symbol(foreign_symbol)
            .unwrap()
            .declarations()
            .unwrap()[0];
        assert_eq!(
            merge_declaration_name(&context.files, context.store(), foreign_declaration),
            Err(SymbolMergeError::StoreInvariant(
                "merge declaration has no source",
            )),
        );

        // A valid first name must not hide a later declaration with a different owner.
        for (symbol, wrong_declaration) in
            [(target, class_declaration), (source, variable_names[0].0)]
        {
            let record = context.store().symbol(symbol).unwrap();
            let original = record.declarations().unwrap().to_vec();
            let value = record.value_declaration();
            let mut invalid = original.clone();
            invalid.push(wrong_declaration);
            assert!(
                context.store.set_symbol_declarations(symbol, Some(invalid), value)
            );
            assert_eq!(
                ScriptGlobalMergeHost {
                    files: &context.files,
                    diagnostics: &mut reported,
                }
                .report_merge_diagnostic(context.store(), diagnostic),
                Err(SymbolMergeError::StoreInvariant(
                    "script merge declaration has a different symbol owner",
                )),
            );
            assert_eq!(reported, original_diagnostics);
            assert!(
                context.store.set_symbol_declarations(symbol, Some(original), value)
            );
        }
        assert_eq!(context.diagnostics(), &original_diagnostics);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().merged_symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            allocations,
        );

        let enum_source = parsed("enum Choice { First }");
        let block_source = parsed(r"let \u0043hoice = 1;");
        let enum_file = FileId::new(8_245);
        let block_file = FileId::new(8_246);
        let (enum_declaration, enum_name) =
            declaration_names(&enum_source, enum_file, SyntaxKind::EnumDeclaration)[0];
        let (block_declaration, block_name) =
            declaration_names(&block_source, block_file, SyntaxKind::VariableDeclaration)[0];
        let enum_context = CanonicalCheckerContext::new(
            completed_bindings(&[(enum_file, &enum_source), (block_file, &block_source)]),
            vec![
                (enum_file, &enum_source.arena),
                (block_file, &block_source.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let target = enum_context
            .file(enum_file)
            .unwrap()
            .1
            .symbol(enum_declaration)
            .unwrap();
        let source = enum_context
            .file(block_file)
            .unwrap()
            .1
            .symbol(block_declaration)
            .unwrap();
        let flags = enum_context.store().symbol(target).unwrap().flags()
            | enum_context.store().symbol(source).unwrap().flags();
        let spelling = r"\u0043hoice";
        let mut native = CanonicalCheckerDiagnostics::default();
        let mut compatibility = CanonicalCheckerDiagnostics::default();
        for (reported, mode) in [
            (&mut native, DuplicatePrimaryArguments::NativeSourceSpelling),
            (
                &mut compatibility,
                DuplicatePrimaryArguments::RawHostCompatibility,
            ),
        ] {
            CheckerDiagnosticMergeHost::new(reported).report_incompatible_at_nodes(
                flags,
                spelling,
                &[block_name],
                &[enum_name],
                mode,
            );
        }
        assert_eq!(enum_context.diagnostics(), &native);
        for (native, compatibility) in native.as_slice().iter().zip(compatibility.as_slice()) {
            assert_eq!(native.diagnostic.code(), 2567);
            assert_eq!(native.diagnostic.arguments, [spelling]);
            assert!(compatibility.diagnostic.arguments.is_empty());
            assert_eq!(native.node, compatibility.node);
            assert_eq!(native.range_override, compatibility.range_override);
            assert_eq!(native.related_information, compatibility.related_information);
            assert_eq!(native.diagnostic.render(), compatibility.diagnostic.render());
            assert_eq!(
                native.diagnostic.render().unwrap(),
                "Enum declarations can only merge with namespace or other enum declarations.",
            );
            assert_ne!(native, compatibility);
        }
        assert_eq!(
            native.as_slice(),
            &[
                primary(
                    block_name,
                    2567,
                    vec![spelling.to_owned()],
                    vec![leading(enum_name, spelling)],
                ),
                primary(
                    enum_name,
                    2567,
                    vec![spelling.to_owned()],
                    vec![leading(block_name, spelling)],
                ),
            ],
        );

        let mut raw = CanonicalCheckerDiagnostics::default();
        CheckerDiagnosticMergeHost::new(&mut raw)
            .report_merge_diagnostic(
                enum_context.store(),
                SymbolMergeDiagnostic {
                    kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
                    target,
                    source,
                },
            )
            .unwrap();
        assert_eq!(
            raw.as_slice(),
            &[
                primary(
                    block_declaration,
                    2567,
                    Vec::new(),
                    vec![leading(enum_declaration, "Choice")],
                ),
                primary(
                    enum_declaration,
                    2567,
                    Vec::new(),
                    vec![leading(block_declaration, "Choice")],
                ),
            ],
        );

        let mut isolated = CanonicalCheckerDiagnostics::default();
        let primaries = [
            native.as_slice()[0].diagnostic.clone(),
            compatibility.as_slice()[0].diagnostic.clone(),
        ];
        for primary in &primaries {
            isolated.lookup_or_issue(Some(block_name), primary.clone());
        }
        assert_eq!(isolated.len(), 2);
        assert!(
            isolated
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.related_information.is_empty())
        );
        for primary in primaries {
            isolated
                .lookup_or_issue(Some(block_name), primary)
                .append_related(leading(enum_name, spelling));
        }
        assert_eq!(isolated.len(), 2);
        assert_eq!(isolated.as_slice()[0], native.as_slice()[0]);
        assert_eq!(isolated.as_slice()[1], compatibility.as_slice()[0]);
        assert_ne!(isolated.as_slice()[0], isolated.as_slice()[1]);
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
    fn merges_quoted_ambient_modules_after_libraries_and_retains_pattern_order() {
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
            let symbol = global_symbol(&context, name).unwrap();
            let declaration = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ModuleDeclaration(module) = &record.data else {
                        return None;
                    };
                    let NodeData::StringLiteral(literal) = &source.arena.get(module.name)?.data
                    else {
                        return None;
                    };
                    (format!("\"{}\"", literal.text) == name)
                        .then_some(node_ref(&source, file, node))
                })
                .unwrap();
            let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
            assert_eq!(context.store().get_merged_symbol(raw), Some(symbol));
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!(record.name().as_utf8(), Some(name));
            assert_eq!(record.declarations(), Some([declaration].as_slice()));
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
    fn merges_named_ambient_augmentations_into_the_exported_namespace_in_program_order() {
        let library = parsed(concat!(
            "declare module \"react\" { ",
            "export = React; ",
            "namespace React { interface Attributes { key?: string; } } ",
            "}",
        ));
        let first = parsed(concat!(
            "export {}; ",
            "declare module \"react\" { interface Attributes { 'ns:thing'?: string; } } ",
            "declare module \"unknown\" { interface Attributes { ignored: string; } }",
        ));
        let second = parsed(concat!(
            "export {}; ",
            "declare module \"react\" { interface Attributes { extra?: number; } }",
        ));
        let library_file = FileId::new(8_451);
        let first_file = FileId::new(8_452);
        let second_file = FileId::new(8_453);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[
                (library_file, &library, true, CanonicalModuleState::Script),
                (first_file, &first, false, CanonicalModuleState::External),
                (second_file, &second, false, CanonicalModuleState::External),
            ]),
            vec![
                (library_file, &library.arena),
                (first_file, &first.arena),
                (second_file, &second.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let ambient = context.pending_ambient_modules()[0];
        let (_, library_bound) = context.file(library_file).unwrap();
        let namespace_declaration = library
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    library.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(identifier)) if identifier.text == "React"
                )
                .then_some(node_ref(&library, library_file, node))
            })
            .unwrap();
        let original_namespace = library_bound.symbol(namespace_declaration).unwrap();
        let namespace = context
            .store()
            .get_merged_symbol(original_namespace)
            .unwrap();
        assert_ne!(namespace, original_namespace);
        let namespace_exports = context
            .store()
            .symbol(namespace)
            .unwrap()
            .exports()
            .unwrap();
        let ambient_exports = context.store().symbol(ambient).unwrap().exports().unwrap();
        let attributes = context
            .store()
            .symbol_table(namespace_exports)
            .unwrap()
            .get_source("Attributes")
            .unwrap();
        assert!(
            context
                .store()
                .symbol_table(ambient_exports)
                .unwrap()
                .get_source("Attributes")
                .is_none()
        );
        assert!(
            context
                .store()
                .symbol_table(ambient_exports)
                .unwrap()
                .get(InternalSymbolName::ExportEquals.as_ref())
                .is_some()
        );
        for (file, parsed) in [(first_file, &first), (second_file, &second)] {
            let (_, bound) = context.file(file).unwrap();
            let name = bound.module_augmentations()[0].name();
            let declaration = validate_augmentation_name(&parsed.arena, bound, file, name).unwrap();
            let augmentation = bound.symbol(declaration).unwrap();
            assert_eq!(
                context.store().get_merged_symbol(augmentation),
                Some(namespace)
            );
        }
        let record = context.store().symbol(attributes).unwrap();
        assert!(record.flags().contains(SymbolFlags::INTERFACE));
        assert!(record.flags().contains(SymbolFlags::TRANSIENT));
        assert_eq!(record.parent(), Some(namespace));
        assert_eq!(
            record
                .declarations()
                .unwrap()
                .iter()
                .map(|declaration| declaration.file)
                .collect::<Vec<_>>(),
            [library_file, first_file, second_file],
        );
        let members = context
            .store()
            .symbol_table(record.members().unwrap())
            .unwrap();
        for name in ["key", "ns:thing", "extra"] {
            assert!(members.get_source(name).is_some(), "missing {name}");
        }
        assert!(global_symbol(&context, "Attributes").is_none());
        assert_eq!(
            context
                .file(first_file)
                .unwrap()
                .1
                .module_augmentations()
                .len(),
            2
        );

        let (_, first_bound) = context.file(first_file).unwrap();
        let name = first_bound.module_augmentations()[0].name();
        let module =
            validate_augmentation_name(&first.arena, first_bound, first_file, name).unwrap();
        let warm = (
            context.store().symbol_len(),
            context.store().merged_symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        assert!(
            plan_named_ambient_module_augmentation(
                context.store(),
                &context.files,
                context.pending_ambient_modules(),
                &first.arena,
                first_bound,
                first_file,
                module,
                name,
            )
            .unwrap()
            .is_none()
        );
        assert_eq!(
            (
                context.store().symbol_len(),
                context.store().merged_symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            warm,
        );
    }

    #[test]
    fn named_ambient_augmentations_reject_non_namespace_export_assignments() {
        let library = parsed("declare module \"react\" { export = React; const React: number; }");
        let augmentation = parsed(concat!(
            "export {}; ",
            "declare module \"react\" { interface Attributes { 'ns:thing'?: string; } }",
        ));
        let library_file = FileId::new(8_454);
        let augmentation_file = FileId::new(8_455);
        let context = CanonicalCheckerContext::new(
            completed_bindings_with_facts(&[
                (library_file, &library, true, CanonicalModuleState::Script),
                (
                    augmentation_file,
                    &augmentation,
                    false,
                    CanonicalModuleState::External,
                ),
            ]),
            vec![
                (library_file, &library.arena),
                (augmentation_file, &augmentation.arena),
            ],
            IntrinsicBootstrapOptions::default(),
        )
        .unwrap();

        let ambient = context.pending_ambient_modules()[0];
        let exports = context.store().symbol(ambient).unwrap().exports().unwrap();
        assert!(
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("Attributes")
                .is_none()
        );
        let (_, bound) = context.file(augmentation_file).unwrap();
        let name = bound.module_augmentations()[0].name();
        let module =
            validate_augmentation_name(&augmentation.arena, bound, augmentation_file, name)
                .unwrap();
        let symbol = bound.symbol(module).unwrap();
        let attributes = context
            .store()
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        assert_eq!(
            context.store().get_merged_symbol(attributes),
            Some(attributes)
        );
        assert!(global_symbol(&context, "Attributes").is_none());
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
