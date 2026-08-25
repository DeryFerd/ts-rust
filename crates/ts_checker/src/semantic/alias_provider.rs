//! Production syntax and module-resolution host for canonical alias targets.
//!
//! This host accepts TypeScript namespace imports, explicit default imports,
//! named imports, named exports, external import-equals declarations, and
//! source-owned `JSDoc` import-type module specifiers. ESM and `CommonJS` emit
//! modes retain the same direct module symbols when both sides agree. Alias
//! recursion and type-only propagation belong to the canonical alias kernel.

use std::collections::BTreeMap;

#[cfg(test)]
use std::cell::Cell;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CheckFlags, EscapedName, InternalSymbolName, SemanticStoreId, SemanticSymbolId,
    SymbolData, SymbolFlags,
};

use super::{
    AliasSymbolLinks, AliasTargetState, CanonicalModuleResolutionLookup,
    CanonicalModuleResolutionManifest, CanonicalModuleResolutionMode, CanonicalResolvedModule,
    CanonicalSemanticStore, SourceFileRef,
    alias::{
        CanonicalAliasTargetHost, CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
    links::ExportTypeLinks,
};

#[derive(Clone, Copy, Debug)]
struct ProductionAliasTargetSource<'arena> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
}

#[derive(Debug)]
struct ProductionAliasRegistrySource<'arena> {
    arena: &'arena NodeArena,
    bound: BoundFile,
    source_file: SourceFileRef,
}

/// Context-owned, once-validated Program sources for production alias queries.
///
/// The registry is the sole owner of retained binder side data. Query hosts
/// borrow this registry instead of rebuilding and revalidating a source map.
#[derive(Debug)]
pub(super) struct ProductionAliasSourceRegistry<'arena> {
    store: SemanticStoreId,
    sources: BTreeMap<FileId, ProductionAliasRegistrySource<'arena>>,
    #[cfg(test)]
    instrumentation: ProductionAliasSourceRegistryInstrumentation,
}

#[cfg(test)]
#[derive(Debug)]
struct ProductionAliasSourceRegistryInstrumentation {
    validation_passes: usize,
    validated_sources: usize,
    snapshot_iterations: Cell<usize>,
    declared_type_views: Cell<usize>,
    name_resolver_views: Cell<usize>,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ProductionAliasSourceRegistryInstrumentationSnapshot {
    pub(super) validation_passes: usize,
    pub(super) validated_sources: usize,
    pub(super) snapshot_iterations: usize,
    pub(super) declared_type_views: usize,
    pub(super) name_resolver_views: usize,
}

#[derive(Debug)]
enum ProductionAliasTargetSources<'source, 'arena> {
    Retained(BTreeMap<FileId, ProductionAliasTargetSource<'arena>>),
    Registry(&'source ProductionAliasSourceRegistry<'arena>),
}

/// Store-free production alias-target provider over exact retained Program
/// AST/binder snapshots and the immutable compiler module-resolution manifest.
#[derive(Debug)]
pub struct ProductionAliasTargetHost<'source, 'arena, 'manifest> {
    store: SemanticStoreId,
    sources: ProductionAliasTargetSources<'source, 'arena>,
    module_resolutions: &'manifest CanonicalModuleResolutionManifest,
}

/// Why a source set cannot back production alias-target resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProductionAliasTargetHostError {
    ArenaMismatch {
        file: FileId,
        expected: NodeArenaId,
        actual: NodeArenaId,
    },
    ArenaRevisionMismatch {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    DeclarationsIncomplete(FileId),
    MissingSourceFileFacts(FileId),
    InvalidSourceFile(NodeRef),
    InvalidRegisteredSourceFile {
        file: FileId,
        expected: NodeRef,
        actual: SourceFileRef,
    },
    InvalidSymbolStore(FileId),
    DuplicateFile(FileId),
    RegistryStoreMismatch {
        expected: SemanticStoreId,
        actual: SemanticStoreId,
    },
}

impl std::fmt::Display for ProductionAliasTargetHostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ArenaMismatch { file, .. } => write!(
                formatter,
                "alias-target source {} uses a different AST arena",
                file.index()
            ),
            Self::ArenaRevisionMismatch { file, .. } => write!(
                formatter,
                "alias-target source {} changed after canonical binding",
                file.index()
            ),
            Self::DeclarationsIncomplete(file) => write!(
                formatter,
                "alias-target source {} has incomplete declaration bindings",
                file.index()
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "alias-target source {} has no canonical source facts",
                file.index()
            ),
            Self::InvalidSourceFile(source) => write!(
                formatter,
                "alias-target source {} has an invalid source-file root",
                source.file.index()
            ),
            Self::InvalidRegisteredSourceFile { file, .. } => write!(
                formatter,
                "alias-target source {} has an invalid checker source registration",
                file.index()
            ),
            Self::InvalidSymbolStore(file) => write!(
                formatter,
                "alias-target source {} belongs to another symbol store",
                file.index()
            ),
            Self::DuplicateFile(file) => write!(
                formatter,
                "alias-target source {} was supplied more than once",
                file.index()
            ),
            Self::RegistryStoreMismatch { .. } => {
                formatter.write_str("alias-target source registry belongs to another symbol store")
            }
        }
    }
}

impl std::error::Error for ProductionAliasTargetHostError {}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SupportedAliasDeclaration {
    NamespaceImport {
        specifier: NodeRef,
        type_only: bool,
    },
    NamespaceExport {
        specifier: NodeRef,
        type_only: bool,
    },
    DefaultModuleMember {
        specifier: NodeRef,
        type_only: bool,
    },
    NamedModuleMember {
        specifier: NodeRef,
        name: String,
        type_only: bool,
    },
    ExternalImportEquals {
        specifier: NodeRef,
        type_only: bool,
    },
    LocalModuleMember {
        target: SemanticSymbolId,
        type_only: bool,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CommonJsAssignmentExportName<'name> {
    ExportEquals,
    Named(&'name str),
}

impl<'arena> ProductionAliasSourceRegistry<'arena> {
    /// Adopts and validates the complete retained Program source set once.
    pub(super) fn new<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        sources: impl IntoIterator<Item = (&'arena NodeArena, BoundFile, SourceFileRef)>,
    ) -> Result<Self, ProductionAliasTargetHostError> {
        let mut retained = BTreeMap::new();
        for (arena, bound, source_file) in sources {
            let file = validate_source(store, arena, &bound)?;
            if source_file.node_ref() != bound.source_file()
                || !store.contains_source_file(source_file)
            {
                return Err(
                    ProductionAliasTargetHostError::InvalidRegisteredSourceFile {
                        file,
                        expected: bound.source_file(),
                        actual: source_file,
                    },
                );
            }
            if retained
                .insert(
                    file,
                    ProductionAliasRegistrySource {
                        arena,
                        bound,
                        source_file,
                    },
                )
                .is_some()
            {
                return Err(ProductionAliasTargetHostError::DuplicateFile(file));
            }
        }
        Ok(Self {
            store: store.id(),
            #[cfg(test)]
            instrumentation: ProductionAliasSourceRegistryInstrumentation {
                validation_passes: 1,
                validated_sources: retained.len(),
                snapshot_iterations: Cell::new(0),
                declared_type_views: Cell::new(0),
                name_resolver_views: Cell::new(0),
            },
            sources: retained,
        })
    }

    /// Returns the semantic-store brand validated when the registry adopted
    /// its Program sources.
    pub(super) const fn store_id(&self) -> SemanticStoreId {
        self.store
    }

    /// Looks up one retained AST/binder snapshot without exposing the registry
    /// representation.
    pub(super) fn snapshot(&self, file: FileId) -> Option<(&'arena NodeArena, &BoundFile)> {
        self.sources
            .get(&file)
            .map(|source| (source.arena, &source.bound))
    }

    /// Returns the checker source-root identity registered for one file.
    pub(super) fn source_file(&self, file: FileId) -> Option<SourceFileRef> {
        self.sources.get(&file).map(|source| source.source_file)
    }

    /// Iterates retained AST/binder snapshots without allocating or cloning
    /// binder side data.
    #[cfg(test)]
    pub(super) fn snapshots(&self) -> impl Iterator<Item = (&'arena NodeArena, &BoundFile)> + '_ {
        self.instrumentation
            .snapshot_iterations
            .set(self.instrumentation.snapshot_iterations.get() + 1);
        self.sources
            .values()
            .map(|source| (source.arena, &source.bound))
    }

    /// Records an allocation-free declared-type query view in test builds.
    #[cfg(test)]
    #[inline]
    pub(super) fn note_declared_type_view(&self) {
        self.instrumentation
            .declared_type_views
            .set(self.instrumentation.declared_type_views.get() + 1);
    }

    /// Records an allocation-free name-resolver query view in test builds.
    #[cfg(test)]
    #[inline]
    pub(super) fn note_name_resolver_view(&self) {
        self.instrumentation
            .name_resolver_views
            .set(self.instrumentation.name_resolver_views.get() + 1);
    }

    #[cfg(test)]
    pub(super) fn instrumentation(&self) -> ProductionAliasSourceRegistryInstrumentationSnapshot {
        ProductionAliasSourceRegistryInstrumentationSnapshot {
            validation_passes: self.instrumentation.validation_passes,
            validated_sources: self.instrumentation.validated_sources,
            snapshot_iterations: self.instrumentation.snapshot_iterations.get(),
            declared_type_views: self.instrumentation.declared_type_views.get(),
            name_resolver_views: self.instrumentation.name_resolver_views.get(),
        }
    }

    fn target_source(&self, file: FileId) -> Option<ProductionAliasTargetSource<'_>> {
        self.sources
            .get(&file)
            .map(|source| ProductionAliasTargetSource {
                arena: source.arena,
                bound: &source.bound,
            })
    }
}

impl ProductionAliasTargetSources<'_, '_> {
    fn get(&self, file: FileId) -> Option<ProductionAliasTargetSource<'_>> {
        match self {
            Self::Retained(sources) => sources.get(&file).copied(),
            Self::Registry(sources) => sources.target_source(file),
        }
    }
}

impl<'arena, 'manifest> ProductionAliasTargetHost<'arena, 'arena, 'manifest> {
    /// Validates and retains the exact declaration-complete Program sources.
    ///
    /// The checker store is used only to validate provenance and capture its
    /// brand. It is not borrowed by the resulting host, so the alias kernel
    /// can continue to own its mutable store session.
    ///
    /// # Errors
    ///
    /// Returns a typed construction error before retaining any source set when
    /// an AST/binder snapshot is stale, incomplete, foreign, or duplicated.
    pub fn new<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        sources: impl IntoIterator<Item = (&'arena NodeArena, &'arena BoundFile)>,
        module_resolutions: &'manifest CanonicalModuleResolutionManifest,
    ) -> Result<Self, ProductionAliasTargetHostError> {
        let mut retained = BTreeMap::new();
        for (arena, bound) in sources {
            let file = validate_source(store, arena, bound)?;
            if retained
                .insert(file, ProductionAliasTargetSource { arena, bound })
                .is_some()
            {
                return Err(ProductionAliasTargetHostError::DuplicateFile(file));
            }
        }

        Ok(Self {
            store: store.id(),
            sources: ProductionAliasTargetSources::Retained(retained),
            module_resolutions,
        })
    }
}

impl<'source, 'arena, 'manifest> ProductionAliasTargetHost<'source, 'arena, 'manifest> {
    /// Creates an allocation-free query view over a context-owned, validated
    /// source registry.
    pub(super) fn from_registry<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        sources: &'source ProductionAliasSourceRegistry<'arena>,
        module_resolutions: &'manifest CanonicalModuleResolutionManifest,
    ) -> Result<Self, ProductionAliasTargetHostError> {
        if sources.store != store.id() {
            return Err(ProductionAliasTargetHostError::RegistryStoreMismatch {
                expected: sources.store,
                actual: store.id(),
            });
        }
        Ok(Self {
            store: sources.store,
            sources: ProductionAliasTargetSources::Registry(sources),
            module_resolutions,
        })
    }

    fn checked_source<'host, MapperPayload>(
        &'host self,
        store: &CanonicalSemanticStore<MapperPayload>,
        reference: NodeRef,
    ) -> Result<ProductionAliasTargetSource<'host>, CanonicalAliasTargetUnavailable> {
        let source = self.sources.get(reference.file).ok_or(
            CanonicalAliasTargetUnavailable::ForeignDeclaration(reference),
        )?;
        if source.bound.node_arena_revision() != source.arena.revision() {
            return Err(CanonicalAliasTargetUnavailable::StaleSourceFile(
                reference.file,
            ));
        }
        if !reference.is_for(source.arena.id(), source.bound.file_id())
            || !source.bound.contains(reference)
            || !store.contains_node_ref(reference)
        {
            return Err(CanonicalAliasTargetUnavailable::ForeignDeclaration(
                reference,
            ));
        }
        Ok(source)
    }

    fn checked_node<'host, MapperPayload>(
        &'host self,
        store: &CanonicalSemanticStore<MapperPayload>,
        reference: NodeRef,
    ) -> Result<(&'host Node, ProductionAliasTargetSource<'host>), CanonicalAliasTargetUnavailable>
    {
        let source = self.checked_source(store, reference)?;
        let node = source
            .arena
            .get(reference.node)
            .filter(|node| node.data.matches_syntax_kind(node.kind))
            .ok_or(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                reference,
            ))?;
        Ok((node, source))
    }

    fn alias_declaration<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
    ) -> Result<NodeRef, CanonicalAliasTargetUnavailable> {
        let symbol = store
            .symbol(alias)
            .ok_or(CanonicalAliasTargetUnavailable::ForeignStore {
                expected: self.store,
                actual: store.id(),
            })?;
        let declarations = symbol
            .declarations()
            .ok_or(CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily)?;

        for &declaration in declarations.iter().rev() {
            let (node, source) = self.checked_node(store, declaration)?;
            let commonjs_javascript = source
                .bound
                .source_facts()
                .is_some_and(|facts| facts.is_javascript_file() && facts.is_common_js_module());
            if !is_alias_symbol_declaration(source.arena, node, commonjs_javascript) {
                continue;
            }
            let owned = source
                .bound
                .symbol(declaration)
                .into_iter()
                .chain(source.bound.local_symbol(declaration))
                .any(|owner| {
                    owner == alias
                        || store
                            .get_merged_symbol(owner)
                            .is_some_and(|owner| owner == alias)
                });
            if !owned {
                return Err(
                    CanonicalAliasTargetUnavailable::AliasDeclarationOwnerMismatch {
                        alias,
                        declaration,
                    },
                );
            }
            return Ok(declaration);
        }
        Err(CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily)
    }

    fn supported_declaration<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
    ) -> Result<SupportedAliasDeclaration, CanonicalAliasTargetUnavailable> {
        let (node, source) = self.checked_node(store, declaration)?;
        let facts = source.bound.source_facts().ok_or(
            CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
        )?;
        if facts.is_javascript_file() && !facts.is_external_or_common_js_module() {
            return Err(
                CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                    declaration,
                    file: declaration.file,
                },
            );
        }
        if facts.is_common_js_module() && !facts.is_javascript_file() {
            return Err(CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration,
                file: declaration.file,
            });
        }
        if facts.is_javascript_file()
            && facts.is_common_js_module()
            && matches!(node.data, NodeData::BinaryExpression(_))
        {
            let NodeData::BinaryExpression(binary) = &node.data else {
                return Err(
                    CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                        declaration,
                        file: declaration.file,
                    },
                );
            };
            let target =
                Self::commonjs_assignment_alias_target(store, source, declaration, binary)?;
            return Ok(SupportedAliasDeclaration::LocalModuleMember {
                target,
                type_only: false,
            });
        }
        if facts.is_javascript_file() && !facts.is_external_module() {
            return Err(
                CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                    declaration,
                    file: declaration.file,
                },
            );
        }

        match (node.kind, &node.data) {
            (SyntaxKind::ImportClause, NodeData::ImportClause(clause)) if clause.name.is_some() => {
                let (specifier, clause) = default_import_context(source.arena, declaration)?;
                Ok(SupportedAliasDeclaration::DefaultModuleMember {
                    specifier,
                    type_only: clause.phase_modifier == Some(SyntaxKind::TypeKeyword),
                })
            }
            (SyntaxKind::NamespaceImport, NodeData::NamespaceImport(_)) => {
                let (specifier, clause) = namespace_import_context(source.arena, declaration)?;
                Ok(SupportedAliasDeclaration::NamespaceImport {
                    specifier,
                    type_only: clause.phase_modifier == Some(SyntaxKind::TypeKeyword),
                })
            }
            (SyntaxKind::NamespaceExport, NodeData::NamespaceExport(_)) => {
                let (specifier, type_only) = namespace_export_context(source.arena, declaration)?;
                Ok(SupportedAliasDeclaration::NamespaceExport {
                    specifier,
                    type_only,
                })
            }
            (SyntaxKind::NamespaceExportDeclaration, NodeData::NamespaceExportDeclaration(_)) => {
                if node.parent != Some(source.bound.source_file().node) {
                    return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ));
                }
                let module = source.bound.symbol(source.bound.source_file()).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let target =
                    Self::export_equals_target(store, declaration, module)?.unwrap_or(module);
                Ok(SupportedAliasDeclaration::LocalModuleMember {
                    target,
                    type_only: false,
                })
            }
            (SyntaxKind::ImportEqualsDeclaration, NodeData::ImportEqualsDeclaration(import)) => {
                match source
                    .arena
                    .get(import.module_reference)
                    .map(|node| &node.data)
                {
                    Some(NodeData::ExternalModuleReference(_)) => {
                        let specifier = import_equals_context(source.arena, declaration)?;
                        Ok(SupportedAliasDeclaration::ExternalImportEquals {
                            specifier,
                            type_only: import.is_type_only,
                        })
                    }
                    Some(NodeData::Identifier(_) | NodeData::QualifiedName(_)) => {
                        let target = Self::local_module_entity(
                            store,
                            source,
                            declaration,
                            import.module_reference,
                        )?;
                        Ok(SupportedAliasDeclaration::LocalModuleMember {
                            target,
                            type_only: import.is_type_only,
                        })
                    }
                    _ => Err(
                        CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration),
                    ),
                }
            }
            (SyntaxKind::ImportSpecifier, NodeData::ImportSpecifier(import)) => {
                let (specifier, clause) = import_specifier_context(source.arena, declaration)?;
                let name =
                    module_export_name(source.arena, import.property_name.unwrap_or(import.name))
                        .ok_or(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ))?;
                let type_only =
                    import.is_type_only || clause.phase_modifier == Some(SyntaxKind::TypeKeyword);
                if name == "default" {
                    Ok(SupportedAliasDeclaration::DefaultModuleMember {
                        specifier,
                        type_only,
                    })
                } else {
                    Ok(SupportedAliasDeclaration::NamedModuleMember {
                        specifier,
                        name: name.to_owned(),
                        type_only,
                    })
                }
            }
            (SyntaxKind::ExportSpecifier, NodeData::ExportSpecifier(export)) => {
                let (specifier, declaration_type_only) =
                    export_specifier_context(source.arena, declaration)?;
                module_export_name(source.arena, export.name).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let imported_name = export.property_name.unwrap_or(export.name);
                let name = module_export_name(source.arena, imported_name).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let type_only = export.is_type_only || declaration_type_only;
                let Some(specifier) = specifier else {
                    let target =
                        Self::local_module_member(store, source, declaration, imported_name)?;
                    return Ok(SupportedAliasDeclaration::LocalModuleMember { target, type_only });
                };
                if name == "default" {
                    Ok(SupportedAliasDeclaration::DefaultModuleMember {
                        specifier,
                        type_only,
                    })
                } else {
                    Ok(SupportedAliasDeclaration::NamedModuleMember {
                        specifier,
                        name: name.to_owned(),
                        type_only,
                    })
                }
            }
            (SyntaxKind::ExportAssignment, NodeData::ExportAssignment(export)) => {
                let target =
                    Self::alias_expression_target(store, source, declaration, export.expression)?;
                Ok(SupportedAliasDeclaration::LocalModuleMember {
                    target,
                    type_only: false,
                })
            }
            _ => Err(CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration)),
        }
    }

    fn local_module_member<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        source: ProductionAliasTargetSource<'_>,
        declaration: NodeRef,
        name: NodeId,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let Some(Node {
            kind: SyntaxKind::Identifier,
            data: NodeData::Identifier(identifier),
            ..
        }) = source.arena.get(name)
        else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                declaration,
            ));
        };
        let unavailable = || CanonicalAliasTargetUnavailable::UnsupportedLocalExport(declaration);
        let source_file = source.bound.source_file();
        let mut scope = source.bound.container(declaration);
        while let Some(namespace) = scope {
            if namespace == source_file {
                break;
            }
            if !namespace.is_for(source.arena.id(), declaration.file)
                || !source.bound.contains(namespace)
                || !store.contains_node_ref(namespace)
            {
                return Err(unavailable());
            }
            let record = source
                .arena
                .get(namespace.node)
                .filter(|record| record.data.matches_syntax_kind(record.kind))
                .ok_or_else(unavailable)?;
            if record.kind == SyntaxKind::ModuleDeclaration {
                let owner = source
                    .bound
                    .symbol(namespace)
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .and_then(|symbol| store.symbol(symbol))
                    .filter(|symbol| symbol.flags().intersects(SymbolFlags::NAMESPACE))
                    .ok_or_else(unavailable)?;

                if let Some(locals) = source.bound.locals(namespace) {
                    let locals = store.symbol_table(locals).ok_or_else(unavailable)?;
                    if let Some(symbol) = locals.get_source(&identifier.text) {
                        let symbol = store.get_merged_symbol(symbol).ok_or_else(unavailable)?;
                        let target = store
                            .symbol(symbol)
                            .ok_or_else(unavailable)?
                            .export_symbol()
                            .unwrap_or(symbol);
                        return store.get_merged_symbol(target).ok_or_else(unavailable);
                    }
                }

                if let Some(exports) = owner.exports() {
                    let exports = store.symbol_table(exports).ok_or_else(unavailable)?;
                    if let Some(symbol) = exports.get_source(&identifier.text) {
                        return store.get_merged_symbol(symbol).ok_or_else(unavailable);
                    }
                }
            }
            scope = source.bound.container(namespace);
        }
        let Some(locals) = source.bound.locals(source.bound.source_file()) else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                declaration,
            ));
        };
        let Some(target) = store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source(&identifier.text))
            .and_then(|symbol| store.get_merged_symbol(symbol))
        else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                declaration,
            ));
        };
        let target = store
            .symbol(target)
            .ok_or_else(unavailable)?
            .export_symbol()
            .unwrap_or(target);
        store.get_merged_symbol(target).ok_or_else(unavailable)
    }

    fn local_module_entity<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        source: ProductionAliasTargetSource<'_>,
        declaration: NodeRef,
        entity: NodeId,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let Some(record) = source.arena.get(entity) else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        };
        match &record.data {
            NodeData::Identifier(_) if record.kind == SyntaxKind::Identifier => {
                Self::local_module_member(store, source, declaration, entity)
            }
            NodeData::QualifiedName(qualified) if record.kind == SyntaxKind::QualifiedName => {
                let left = source.arena.get(qualified.left).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let right = source.arena.get(qualified.right).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let NodeData::Identifier(name) = &right.data else {
                    return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                        declaration,
                    ));
                };
                if left.parent != Some(entity)
                    || right.parent != Some(entity)
                    || right.kind != SyntaxKind::Identifier
                    || name.flow_node.is_some()
                {
                    return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ));
                }
                let mut namespace =
                    Self::local_module_entity(store, source, declaration, qualified.left)?;
                if store
                    .symbol(namespace)
                    .is_some_and(|record| record.flags() == SymbolFlags::ALIAS)
                {
                    namespace = store
                        .alias_symbol_links(namespace)
                        .and_then(|links| links.alias_target.symbol())
                        .ok_or(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                            declaration,
                        ))?;
                }
                let record = store.symbol(namespace).ok_or(
                    CanonicalAliasTargetUnavailable::UnsupportedLocalExport(declaration),
                )?;
                if !record.flags().intersects(SymbolFlags::NAMESPACE) {
                    return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                        declaration,
                    ));
                }
                store
                    .module_symbol_links(namespace)
                    .and_then(|links| links.resolved_exports)
                    .or_else(|| record.exports())
                    .and_then(|exports| store.symbol_table(exports))
                    .and_then(|exports| exports.get_source(&name.text))
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .ok_or(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                        declaration,
                    ))
            }
            _ => Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                declaration,
            )),
        }
    }

    fn alias_expression_target<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        source: ProductionAliasTargetSource<'_>,
        declaration: NodeRef,
        expression: NodeId,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let Some(record) = source.arena.get(expression) else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        };
        match &record.data {
            NodeData::Identifier(_) => {
                Self::local_module_member(store, source, declaration, expression)
            }
            NodeData::ClassExpression(_) if record.kind == SyntaxKind::ClassExpression => {
                let reference = NodeRef::new(declaration.arena, declaration.file, expression);
                let Some(symbol) = source
                    .bound
                    .symbol(reference)
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                else {
                    return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ));
                };
                let valid = record.parent == Some(declaration.node)
                    && source.bound.contains(reference)
                    && store.contains_node_ref(reference)
                    && store.symbol(symbol).is_some_and(|symbol| {
                        symbol.flags().intersects(SymbolFlags::CLASS)
                            && symbol
                                .declarations()
                                .is_some_and(|declarations| declarations.contains(&reference))
                    });
                if valid {
                    Ok(symbol)
                } else {
                    Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ))
                }
            }
            _ => Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                declaration,
            )),
        }
    }

    fn commonjs_assignment_alias_target<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        source: ProductionAliasTargetSource<'_>,
        declaration: NodeRef,
        assignment: &ts_ast::BinaryExpressionData,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        if !source
            .arena
            .get(assignment.operator_token)
            .is_some_and(|operator| {
                operator.kind == SyntaxKind::EqualsToken
                    && operator.parent == Some(declaration.node)
                    && matches!(operator.data, NodeData::Token(_))
            })
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        }
        let Some(name) = commonjs_assignment_export_name(source.arena, assignment.left) else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration));
        };
        let source_file = source.bound.source_file();
        let module = source.bound.symbol(source_file).ok_or(
            CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
        )?;
        let module_record = store
            .symbol(module)
            .filter(|record| {
                record.flags() == SymbolFlags::VALUE_MODULE
                    && store.get_merged_symbol(module) == Some(module)
                    && record
                        .declarations()
                        .is_some_and(|declarations| declarations.contains(&source_file))
            })
            .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            })?;
        let exports = module_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            })?;
        let actual = match name {
            CommonJsAssignmentExportName::ExportEquals => {
                exports.get(InternalSymbolName::ExportEquals.as_ref())
            }
            CommonJsAssignmentExportName::Named(name) => exports.get_source(name),
        };
        let Some(alias) = source.bound.symbol(declaration) else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        };
        let Some(alias_record) = store.symbol(alias) else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        };
        let export_equals = matches!(name, CommonJsAssignmentExportName::ExportEquals);
        let promoted_type_exports = alias_record.flags().contains(SymbolFlags::NAMESPACE_MODULE);
        let expected_alias_flags = if promoted_type_exports {
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE
        } else {
            SymbolFlags::ALIAS
        };
        if actual != Some(alias)
            || !alias_record.flags().intersects(SymbolFlags::ALIAS)
            || alias_record.parent() != Some(module)
            || !alias_record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&declaration))
            || export_equals
                && (alias_record.flags() != expected_alias_flags
                    || alias_record.check_flags() != CheckFlags::NONE
                    || alias_record.name() != InternalSymbolName::ExportEquals.as_ref()
                    || alias_record.value_declaration() != Some(declaration)
                    || alias_record
                        .declarations()
                        .is_none_or(|declarations| declarations != [declaration].as_slice())
                    || alias_record.members().is_some()
                    || alias_record.exports().is_some() != promoted_type_exports
                    || alias_record.export_symbol().is_some()
                    || store.get_merged_symbol(alias) != Some(alias))
            || export_equals
                && alias_record.exports().is_some_and(|promoted| {
                    store.symbol_table(promoted).is_none_or(|promoted| {
                        promoted.is_empty()
                            || promoted.iter().any(|(name, symbol)| {
                                name == InternalSymbolName::ExportEquals.as_ref()
                                    || exports.get(name) != Some(symbol)
                                    || store.symbol(symbol).is_none_or(|record| {
                                        !record
                                            .flags()
                                            .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                                    })
                            })
                    })
                })
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        }

        if export_equals {
            let Some(left) = source.arena.get(assignment.left) else {
                return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                    declaration,
                ));
            };
            let receiver = match &left.data {
                NodeData::PropertyAccessExpression(access) => access.expression,
                NodeData::ElementAccessExpression(access) => access.expression,
                _ => {
                    return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ));
                }
            };
            let receiver = NodeRef::new(declaration.arena, declaration.file, receiver);
            let implicit_module = source
                .bound
                .locals(source_file)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source("module"))
                .and_then(|module| store.symbol(module).map(|record| (module, record)));
            let implicit_exports = implicit_module
                .and_then(|(_, record)| record.members())
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("exports"))
                .and_then(|exports| store.symbol(exports).map(|record| (exports, record)));
            let implicit_module_valid = implicit_module.is_some_and(|(implicit, record)| {
                record.flags()
                    == (SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS)
                    && record.check_flags() == CheckFlags::NONE
                    && record.name().as_bytes() == b"module"
                    && record.declarations() == Some(&[source_file])
                    && record.value_declaration() == Some(source_file)
                    && record.exports().is_none()
                    && record.parent().is_none()
                    && record.export_symbol().is_none()
                    && store.get_merged_symbol(implicit) == Some(implicit)
                    && store
                        .symbol_node_links(receiver)
                        .and_then(|links| links.resolved_symbol)
                        .is_none_or(|cached| cached == implicit)
            });
            let implicit_exports_valid = implicit_exports.is_some_and(|(exports, record)| {
                record.flags() == (SymbolFlags::PROPERTY | SymbolFlags::MODULE_EXPORTS)
                    && record.check_flags() == CheckFlags::NONE
                    && record.name().as_bytes() == b"exports"
                    && record.declarations() == Some(&[source_file])
                    && record.value_declaration() == Some(source_file)
                    && record.members().is_none()
                    && record.exports().is_none()
                    && record.parent() == implicit_module.map(|(module, _)| module)
                    && record.export_symbol().is_none()
                    && store.get_merged_symbol(exports) == Some(exports)
            });
            if left.parent != Some(declaration.node)
                || !source.bound.contains(receiver)
                || !store.contains_node_ref(receiver)
                || source
                    .arena
                    .get(receiver.node)
                    .is_none_or(|receiver| receiver.parent != Some(assignment.left))
                || !implicit_module_valid
                || !implicit_exports_valid
            {
                return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                    declaration,
                ));
            }
        }

        let target = Self::alias_expression_target(store, source, declaration, assignment.right)?;
        if export_equals
            && let Some(Node {
                kind: SyntaxKind::Identifier,
                data: NodeData::Identifier(identifier),
                parent,
                flags,
                ..
            }) = source.arena.get(assignment.right)
        {
            let right = NodeRef::new(declaration.arena, declaration.file, assignment.right);
            let Some(record) = store.symbol(target) else {
                return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                    declaration,
                ));
            };
            let local_declaration =
                record
                    .declarations()
                    .and_then(|declarations| match declarations {
                        [declaration] => Some(*declaration),
                        _ => None,
                    });
            if *parent != Some(declaration.node)
                || flags.0 != 0
                || identifier.flow_node.is_some()
                || !source.bound.contains(right)
                || !store.contains_node_ref(right)
                || record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
                || record.check_flags() != CheckFlags::NONE
                || record.members().is_some()
                || record.exports().is_some()
                || record.parent().is_some()
                || record.export_symbol().is_some()
                || record.name().as_bytes() != identifier.text.as_bytes()
                || store.get_merged_symbol(target) != Some(target)
                || local_declaration.is_none_or(|local| {
                    !local.is_for(source.arena.id(), declaration.file)
                        || source.bound.symbol(local) != Some(target)
                        || source.bound.local_symbol(local).is_some()
                        || record.value_declaration() != Some(local)
                        || source
                            .arena
                            .get(local.node)
                            .is_none_or(|node| node.kind != SyntaxKind::VariableDeclaration)
                })
                || store
                    .symbol_node_links(right)
                    .and_then(|links| links.resolved_symbol)
                    .is_some_and(|cached| cached != target)
            {
                return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                    declaration,
                ));
            }
        }
        Ok(target)
    }

    fn resolved_module<MapperPayload>(
        &self,
        declaration: NodeRef,
        specifier: NodeRef,
        store: &CanonicalSemanticStore<MapperPayload>,
    ) -> Result<CanonicalResolvedModule, CanonicalAliasTargetUnavailable> {
        let (node, _) = self.checked_node(store, specifier)?;
        if !matches!(
            (node.kind, &node.data),
            (SyntaxKind::StringLiteral, NodeData::StringLiteral(_))
                | (
                    SyntaxKind::NoSubstitutionTemplateLiteral,
                    NodeData::NoSubstitutionTemplateLiteral(_)
                )
        ) {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        }
        match self.module_resolutions.lookup(specifier) {
            CanonicalModuleResolutionLookup::Unavailable => Err(
                CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(specifier),
            ),
            CanonicalModuleResolutionLookup::EntryAbsent => {
                Err(CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(specifier))
            }
            CanonicalModuleResolutionLookup::Unresolved => Err(
                CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(specifier),
            ),
            CanonicalModuleResolutionLookup::Resolved(resolved) => Ok(resolved),
        }
    }

    /// Resolves the exact string argument of a source-owned `JSDoc` import type.
    pub(super) fn resolve_jsdoc_import_type_module<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        import_type: NodeRef,
        module_specifier: NodeRef,
    ) -> Result<(CanonicalResolvedModule, SemanticSymbolId), CanonicalAliasTargetUnavailable> {
        if store.id() != self.store {
            return Err(CanonicalAliasTargetUnavailable::ForeignStore {
                expected: self.store,
                actual: store.id(),
            });
        }
        let (record, source) = self.checked_node(store, import_type)?;
        let NodeData::ImportTypeNode(import) = &record.data else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                import_type,
            ));
        };
        let argument = NodeRef::new(import_type.arena, import_type.file, import.argument);
        let (argument_record, _) = self.checked_node(store, argument)?;
        let NodeData::LiteralTypeNode(literal) = &argument_record.data else {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                import_type,
            ));
        };
        let (specifier, _) = self.checked_node(store, module_specifier)?;
        let valid_specifier = matches!(
            &specifier.data,
            NodeData::StringLiteral(literal) if literal.token_flags.0 == 0
        );
        if record.kind != SyntaxKind::ImportType
            || record.flags.0 != 0
            || import.attributes.is_some()
            || import.is_type_of
            || import.type_arguments.is_some()
            || argument_record.kind != SyntaxKind::LiteralType
            || argument_record.flags.0 != 0
            || argument_record.parent != Some(import_type.node)
            || literal.literal != module_specifier.node
            || !module_specifier.is_for(import_type.arena, import_type.file)
            || specifier.kind != SyntaxKind::StringLiteral
            || specifier.flags.0 != 0
            || specifier.parent != Some(argument.node)
            || !valid_specifier
            || source
                .bound
                .source_facts()
                .is_none_or(|facts| !facts.is_javascript_file())
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                import_type,
            ));
        }

        let resolved = self.resolved_module(import_type, module_specifier, store)?;
        let module = self.direct_source_module(store, import_type, resolved, true)?;
        Ok((resolved, module))
    }

    fn direct_source_module<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
        allow_mixed_module_modes: bool,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let target = self.sources.get(resolved.target_file()).ok_or(
            CanonicalAliasTargetUnavailable::ForeignModuleTarget {
                declaration,
                file: resolved.target_file(),
            },
        )?;
        if target.bound.node_arena_revision() != target.arena.revision() {
            return Err(CanonicalAliasTargetUnavailable::StaleSourceFile(
                resolved.target_file(),
            ));
        }
        let facts = target.bound.source_facts().ok_or(
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module: resolved.target_symbol(),
            },
        )?;
        let commonjs_javascript = facts.is_javascript_file() && facts.is_common_js_module();
        if facts.is_javascript_file() && !facts.is_external_or_common_js_module() {
            return Err(
                CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                    declaration,
                    file: resolved.target_file(),
                },
            );
        }
        if facts.is_common_js_module() && !commonjs_javascript {
            return Err(CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration,
                file: resolved.target_file(),
            });
        }
        if commonjs_javascript && resolved.target_mode() != CanonicalModuleResolutionMode::CommonJs
        {
            return Err(CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration,
                file: resolved.target_file(),
            });
        }

        let source = target.bound.source_file();
        let valid_target = if resolved.is_ambient_module() {
            !facts.is_external_or_common_js_module()
                && store
                    .symbol(resolved.target_symbol())
                    .and_then(|module| module.declarations())
                    .is_some_and(|declarations| {
                        declarations.iter().copied().any(|module| {
                            target.bound.symbol(module) == Some(resolved.target_symbol())
                                && target.arena.get(module.node).is_some_and(|record| {
                                    record.kind == SyntaxKind::ModuleDeclaration
                                        && record.parent == Some(source.node)
                                })
                        })
                    })
        } else {
            target.bound.symbol(source) == Some(resolved.target_symbol())
                && store
                    .symbol(resolved.target_symbol())
                    .and_then(ts_binder::semantic::Symbol::declarations)
                    .is_some_and(|declarations| declarations.contains(&source))
        };
        if !store.contains_node_ref(source) || !valid_target {
            return Err(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module: resolved.target_symbol(),
            });
        }
        let module = store.get_merged_symbol(resolved.target_symbol()).ok_or(
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module: resolved.target_symbol(),
            },
        )?;
        let module_record =
            store
                .symbol(module)
                .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                })?;
        if !resolved.is_ambient_module()
            && !module_record
                .declarations()
                .is_some_and(|declarations| declarations.contains(&source))
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            });
        }
        let modes = (resolved.usage_mode(), resolved.target_mode());
        let matching_modes = matches!(
            modes,
            (
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm
            ) | (
                CanonicalModuleResolutionMode::CommonJs,
                CanonicalModuleResolutionMode::CommonJs
            )
        );
        let allowed_mixed_modes = allow_mixed_module_modes
            && matches!(
                modes,
                (
                    CanonicalModuleResolutionMode::CommonJs,
                    CanonicalModuleResolutionMode::Esm
                ) | (
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::CommonJs
                )
            );
        if !(matching_modes || allowed_mixed_modes) {
            if resolved.usage_mode() == CanonicalModuleResolutionMode::CommonJs
                || resolved.target_mode() == CanonicalModuleResolutionMode::CommonJs
            {
                return Err(CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                    declaration,
                    file: resolved.target_file(),
                });
            }
            return Err(
                CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                    declaration,
                    module,
                },
            );
        }
        if !module_record.flags().intersects(SymbolFlags::MODULE)
            || module_record
                .flags()
                .intersects(SymbolFlags::MODULE_EXPORTS)
        {
            return Err(
                CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                    declaration,
                    module,
                },
            );
        }
        Ok(module)
    }

    fn export_equals_target<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        module: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalAliasTargetUnavailable> {
        let module_record =
            store
                .symbol(module)
                .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                })?;
        let Some(exports) = module_record.exports() else {
            return Ok(None);
        };
        let exports = store.symbol_table(exports).ok_or(
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            },
        )?;
        let Some(target) = exports.get(InternalSymbolName::ExportEquals.as_ref()) else {
            return Ok(None);
        };
        store
            .symbol(target)
            .is_some()
            .then_some(Some(target))
            .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            })
    }

    fn runtime_namespace_export_equals_target<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
        module: SemanticSymbolId,
        assignment: SemanticSymbolId,
    ) -> Result<bool, CanonicalAliasTargetUnavailable> {
        if resolved.is_ambient_module() {
            return Ok(false);
        }

        let malformed = || CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
            declaration,
            module,
        };
        let source = self
            .sources
            .get(resolved.target_file())
            .ok_or_else(malformed)?;
        if source.bound.source_facts().is_none_or(|facts| {
            facts.is_declaration_file() || !facts.is_external_module() || facts.is_javascript_file()
        }) {
            return Ok(false);
        }

        let assignment_record = store.symbol(assignment).ok_or_else(malformed)?;
        if assignment_record.flags() != SymbolFlags::ALIAS {
            return Ok(false);
        }
        let Some([assignment_declaration]) = assignment_record.declarations() else {
            return Err(malformed());
        };
        let assignment_declaration = *assignment_declaration;
        let assignment_node = source
            .arena
            .get(assignment_declaration.node)
            .ok_or_else(malformed)?;
        let NodeData::ExportAssignment(export) = &assignment_node.data else {
            return Err(malformed());
        };
        if assignment_record.check_flags() != CheckFlags::NONE
            || assignment_record.name() != InternalSymbolName::ExportEquals.as_ref()
            || assignment_record.value_declaration() != Some(assignment_declaration)
            || assignment_record.members().is_some()
            || assignment_record.exports().is_some()
            || assignment_record.export_symbol().is_some()
            || store.get_parent_of_symbol(assignment) != Some(module)
            || store.get_merged_symbol(assignment) != Some(assignment)
            || !assignment_declaration.is_for(source.arena.id(), resolved.target_file())
            || !source.bound.contains(assignment_declaration)
            || !store.contains_node_ref(assignment_declaration)
            || source.bound.symbol(assignment_declaration) != Some(assignment)
            || assignment_node.kind != SyntaxKind::ExportAssignment
            || assignment_node.parent != Some(source.bound.source_file().node)
            || assignment_node.flags.0 != 0
            || !export.is_export_equals
            || export.flow_node.is_some()
            || export.symbol.is_some()
            || export.type_.is_some()
            || export.facts != 0
            || export.modifiers.is_some()
        {
            return Err(malformed());
        }

        let expression = NodeRef::new(
            assignment_declaration.arena,
            assignment_declaration.file,
            export.expression,
        );
        let expression_node = source.arena.get(expression.node).ok_or_else(malformed)?;
        let NodeData::Identifier(expression_name) = &expression_node.data else {
            return Ok(false);
        };
        if expression_node.kind != SyntaxKind::Identifier
            || expression_node.parent != Some(assignment_declaration.node)
            || expression_node.flags.0 != 0
            || expression_name.flow_node.is_some()
            || expression_name.text.is_empty()
            || !source.bound.contains(expression)
            || !store.contains_node_ref(expression)
        {
            return Err(malformed());
        }

        let original =
            Self::alias_expression_target(store, source, assignment_declaration, export.expression)
                .map_err(|_| malformed())?;
        let original_record = store.symbol(original).ok_or_else(malformed)?;
        if original_record.flags() != SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE {
            return Ok(false);
        }
        let Some([function, namespace]) = original_record.declarations() else {
            return Ok(false);
        };
        let function = *function;
        let namespace = *namespace;
        let function_node = source.arena.get(function.node).ok_or_else(malformed)?;
        let NodeData::FunctionDeclaration(function_data) = &function_node.data else {
            return Err(malformed());
        };
        let namespace_node = source.arena.get(namespace.node).ok_or_else(malformed)?;
        let NodeData::ModuleDeclaration(namespace_data) = &namespace_node.data else {
            return Err(malformed());
        };
        let function_name = function_data
            .name
            .and_then(|name| source.arena.get(name))
            .ok_or_else(malformed)?;
        let namespace_name = source
            .arena
            .get(namespace_data.name)
            .ok_or_else(malformed)?;
        let source_node = source
            .arena
            .get(source.bound.source_file().node)
            .ok_or_else(malformed)?;
        let NodeData::SourceFile(source_file) = &source_node.data else {
            return Err(malformed());
        };
        let exports = original_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .ok_or_else(malformed)?;

        if original_record.check_flags() != CheckFlags::NONE
            || original_record.name().as_utf8() != Some(expression_name.text.as_str())
            || original_record.value_declaration() != Some(function)
            || original_record.members().is_some()
            || original_record.parent().is_some()
            || original_record.export_symbol().is_some()
            || store.get_merged_symbol(original) != Some(original)
            || source.bound.symbol(function) != Some(original)
            || source.bound.symbol(namespace) != Some(original)
            || source
                .bound
                .locals(source.bound.source_file())
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get(original_record.name()))
                != Some(original)
            || source_file.statements.nodes.as_slice()
                != [function.node, namespace.node, assignment_declaration.node]
            || function_node.kind != SyntaxKind::FunctionDeclaration
            || function_node.parent != Some(source.bound.source_file().node)
            || function_node.flags.0 != 0
            || function_data.body.is_none()
            || function_data.modifiers.is_some()
            || namespace_node.kind != SyntaxKind::ModuleDeclaration
            || namespace_node.parent != Some(source.bound.source_file().node)
            || namespace_node.flags.0 != 0
            || namespace_data.keyword != SyntaxKind::NamespaceKeyword
            || namespace_data.body.is_none()
            || namespace_data.modifiers.is_some()
            || !matches!(
                &function_name.data,
                NodeData::Identifier(name)
                    if function_name.kind == SyntaxKind::Identifier
                        && function_name.parent == Some(function.node)
                        && function_name.flags.0 == 0
                        && name.flow_node.is_none()
                        && name.text == expression_name.text
            )
            || !matches!(
                &namespace_name.data,
                NodeData::Identifier(name)
                    if namespace_name.kind == SyntaxKind::Identifier
                        && namespace_name.parent == Some(namespace.node)
                        && namespace_name.flags.0 == 0
                        && name.flow_node.is_none()
                        && name.text == expression_name.text
            )
            || exports.is_empty()
            || exports.iter().any(|(_, member)| {
                store.symbol(member).is_none_or(|record| {
                    record.parent() != Some(original)
                        || store.get_merged_symbol(member) != Some(member)
                })
            })
            || store.alias_symbol_links(assignment).is_some_and(|links| {
                links.type_only_declaration.is_some()
                    || links
                        .immediate_target
                        .is_some_and(|target| target != original)
                    || matches!(links.alias_target, AliasTargetState::Unknown)
                    || links
                        .alias_target
                        .symbol()
                        .is_some_and(|target| target != original)
            })
        {
            return Err(malformed());
        }

        Ok(true)
    }

    fn synthetic_namespace_export_equals_target<MapperPayload>(
        &self,
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
        module: SemanticSymbolId,
        assignment: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalAliasTargetUnavailable> {
        if resolved.is_ambient_module() || resolved.usage_mode() != resolved.target_mode() {
            return Ok(None);
        }

        let malformed = || CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
            declaration,
            module,
        };
        let source = self
            .sources
            .get(resolved.target_file())
            .ok_or_else(malformed)?;
        let assignment_record = store.symbol(assignment).ok_or_else(malformed)?;
        if assignment_record.flags() != SymbolFlags::ALIAS {
            return Ok(None);
        }
        let Some([assignment_declaration]) = assignment_record.declarations() else {
            return Err(malformed());
        };
        let assignment_declaration = *assignment_declaration;
        if assignment_record.check_flags() != CheckFlags::NONE
            || assignment_record.name() != InternalSymbolName::ExportEquals.as_ref()
            || assignment_record.value_declaration() != Some(assignment_declaration)
            || assignment_record.members().is_some()
            || assignment_record.exports().is_some()
            || assignment_record.export_symbol().is_some()
            || store.get_parent_of_symbol(assignment) != Some(module)
            || store.get_merged_symbol(assignment) != Some(assignment)
            || !assignment_declaration.is_for(source.arena.id(), resolved.target_file())
            || !source.bound.contains(assignment_declaration)
            || !store.contains_node_ref(assignment_declaration)
            || source.bound.symbol(assignment_declaration) != Some(assignment)
        {
            return Err(malformed());
        }
        let assignment_node = source
            .arena
            .get(assignment_declaration.node)
            .ok_or_else(malformed)?;
        let NodeData::ExportAssignment(export) = &assignment_node.data else {
            return Err(malformed());
        };
        if assignment_node.kind != SyntaxKind::ExportAssignment
            || assignment_node.parent != Some(source.bound.source_file().node)
            || assignment_node.flags.0 != 0
            || !export.is_export_equals
            || export.flow_node.is_some()
            || export.symbol.is_some()
            || export.type_.is_some()
            || export.facts != 0
            || export.modifiers.is_some()
        {
            return Err(malformed());
        }
        let expression = NodeRef::new(
            assignment_declaration.arena,
            assignment_declaration.file,
            export.expression,
        );
        let expression_node = source.arena.get(expression.node).ok_or_else(malformed)?;
        let NodeData::Identifier(expression_name) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.kind != SyntaxKind::Identifier
            || expression_node.parent != Some(assignment_declaration.node)
            || expression_node.flags.0 != 0
            || expression_name.flow_node.is_some()
            || expression_name.text.is_empty()
            || !source.bound.contains(expression)
            || !store.contains_node_ref(expression)
        {
            return Err(malformed());
        }

        let original =
            Self::alias_expression_target(store, source, assignment_declaration, export.expression)
                .map_err(|_| malformed())?;
        let original_record = store.symbol(original).ok_or_else(malformed)?;
        if original_record.flags() != SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE
            && original_record.flags() != SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE
        {
            return Ok(None);
        }
        let Some([function, namespace]) = original_record.declarations() else {
            return Ok(None);
        };
        let function = *function;
        let namespace = *namespace;
        let source_node = source
            .arena
            .get(source.bound.source_file().node)
            .ok_or_else(malformed)?;
        let NodeData::SourceFile(source_file) = &source_node.data else {
            return Err(malformed());
        };
        if source_file.statements.nodes.as_slice()
            != [function.node, namespace.node, assignment_declaration.node]
        {
            return Ok(None);
        }
        if source.bound.source_facts().is_none_or(|facts| {
            !facts.is_declaration_file()
                || !facts.is_external_module()
                || facts.is_javascript_file()
        }) || original_record.check_flags() != CheckFlags::NONE
            || original_record.name().as_utf8() != Some(expression_name.text.as_str())
            || original_record.value_declaration() != Some(function)
            || original_record.members().is_some()
            || original_record.parent().is_some()
            || original_record.export_symbol().is_some()
            || store.get_merged_symbol(original) != Some(original)
            || source.bound.symbol(function) != Some(original)
            || source.bound.symbol(namespace) != Some(original)
            || source
                .bound
                .locals(source.bound.source_file())
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get(original_record.name()))
                != Some(original)
            || store
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .is_none_or(|exports| {
                    exports.len() != 1
                        || exports.get(InternalSymbolName::ExportEquals.as_ref())
                            != Some(assignment)
                })
        {
            return Err(malformed());
        }

        let function_node = source.arena.get(function.node).ok_or_else(malformed)?;
        let NodeData::FunctionDeclaration(function_data) = &function_node.data else {
            return Err(malformed());
        };
        let namespace_node = source.arena.get(namespace.node).ok_or_else(malformed)?;
        let NodeData::ModuleDeclaration(namespace_data) = &namespace_node.data else {
            return Err(malformed());
        };
        let function_name = function_data
            .name
            .and_then(|name| source.arena.get(name))
            .ok_or_else(malformed)?;
        let namespace_name = source
            .arena
            .get(namespace_data.name)
            .ok_or_else(malformed)?;
        let return_type = function_data
            .type_
            .and_then(|node| source.arena.get(node))
            .ok_or_else(malformed)?;
        let block = namespace_data
            .body
            .and_then(|node| source.arena.get(node))
            .ok_or_else(malformed)?;
        let NodeData::ModuleBlock(block_data) = &block.data else {
            return Err(malformed());
        };
        let exact_declare = |owner: NodeRef, modifiers: Option<&ts_ast::ModifierList>| {
            let Some(modifiers) = modifiers else {
                return false;
            };
            let [modifier] = modifiers.list.nodes.as_slice() else {
                return false;
            };
            modifiers.flags.0 == 0
                && !modifiers.list.has_trailing_comma
                && source.arena.get(*modifier).is_some_and(|record| {
                    record.kind == SyntaxKind::DeclareKeyword
                        && record.flags.0 == 0
                        && record.parent == Some(owner.node)
                        && matches!(record.data, NodeData::Token(_))
                })
        };
        if function_data.body.is_some()
            || !function_data.parameters.nodes.is_empty()
            || function_data.parameters.has_trailing_comma
            || function_data.type_parameters.is_some()
            || return_type.kind != SyntaxKind::VoidKeyword
            || namespace_data.keyword != SyntaxKind::NamespaceKeyword
            || !exact_declare(function, function_data.modifiers.as_ref())
            || !exact_declare(namespace, namespace_data.modifiers.as_ref())
        {
            return Ok(None);
        }
        if function_node.kind != SyntaxKind::FunctionDeclaration
            || function_node.parent != Some(source.bound.source_file().node)
            || function_node.flags.0 != 0
            || function_data.asterisk_token.is_some()
            || function_data.body.is_some()
            || function_data.end_flow_node.is_some()
            || function_data.flow_node.is_some()
            || function_data.full_signature.is_some()
            || function_data.local_symbol.is_some()
            || function_data.next_container.is_some()
            || !function_data.parameters.nodes.is_empty()
            || function_data.parameters.has_trailing_comma
            || function_data.return_flow_node.is_some()
            || function_data.symbol.is_some()
            || function_data.type_parameters.is_some()
            || function_data.facts != 0
            || !exact_declare(function, function_data.modifiers.as_ref())
            || !matches!(
                &function_name.data,
                NodeData::Identifier(name)
                    if function_name.kind == SyntaxKind::Identifier
                        && function_name.parent == Some(function.node)
                        && function_name.flags.0 == 0
                        && name.flow_node.is_none()
                        && name.text == expression_name.text
            )
            || return_type.kind != SyntaxKind::VoidKeyword
            || return_type.parent != Some(function.node)
            || return_type.flags.0 != 0
            || !matches!(return_type.data, NodeData::KeywordTypeNode(_))
            || namespace_node.kind != SyntaxKind::ModuleDeclaration
            || namespace_node.parent != Some(source.bound.source_file().node)
            || namespace_node.flags.0 != 0
            || namespace_data.asterisk_token.is_some()
            || namespace_data.end_flow_node.is_some()
            || namespace_data.flow_node.is_some()
            || namespace_data.keyword != SyntaxKind::NamespaceKeyword
            || namespace_data.local_symbol.is_some()
            || namespace_data.next_container.is_some()
            || namespace_data.symbol.is_some()
            || namespace_data.facts != 0
            || !exact_declare(namespace, namespace_data.modifiers.as_ref())
            || !matches!(
                &namespace_name.data,
                NodeData::Identifier(name)
                    if namespace_name.kind == SyntaxKind::Identifier
                        && namespace_name.parent == Some(namespace.node)
                        && namespace_name.flags.0 == 0
                        && name.flow_node.is_none()
                        && name.text == expression_name.text
            )
            || block.kind != SyntaxKind::ModuleBlock
            || block.parent != Some(namespace.node)
            || block.flags.0 != 0
            || block_data.flow_node.is_some()
            || block_data.statements.has_trailing_comma
            || block_data.facts != 0
            || store.alias_symbol_links(assignment).is_some_and(|links| {
                links.type_only_declaration.is_some()
                    || links
                        .immediate_target
                        .is_some_and(|target| target != original)
                    || matches!(links.alias_target, AliasTargetState::Unknown)
                    || links
                        .alias_target
                        .symbol()
                        .is_some_and(|target| target != original)
            })
        {
            return Err(malformed());
        }

        let original_exports = original_record
            .exports()
            .map(|exports| store.symbol_table(exports).ok_or_else(malformed))
            .transpose()?;
        let mut exported_members = Vec::new();
        match block_data.statements.nodes.as_slice() {
            [] if original_exports.is_none()
                && original_record.flags()
                    == SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE => {}
            [statement]
                if original_record.flags() == SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE =>
            {
                let exports = original_exports.ok_or_else(malformed)?;
                if exports.len() != 1 {
                    return Ok(None);
                }
                let statement_node = source.arena.get(*statement).ok_or_else(malformed)?;
                let NodeData::VariableStatement(statement_data) = &statement_node.data else {
                    return Ok(None);
                };
                let list = source
                    .arena
                    .get(statement_data.declaration_list)
                    .ok_or_else(malformed)?;
                let NodeData::VariableDeclarationList(list_data) = &list.data else {
                    return Err(malformed());
                };
                let [member] = list_data.declarations.nodes.as_slice() else {
                    return Ok(None);
                };
                let member_node = source.arena.get(*member).ok_or_else(malformed)?;
                let NodeData::VariableDeclaration(member_data) = &member_node.data else {
                    return Err(malformed());
                };
                let member_name = source.arena.get(member_data.name).ok_or_else(malformed)?;
                let NodeData::Identifier(identifier) = &member_name.data else {
                    return Ok(None);
                };
                let annotation = member_data
                    .type_
                    .and_then(|node| source.arena.get(node))
                    .ok_or_else(malformed)?;
                let modifiers = statement_data.modifiers.as_ref().ok_or_else(malformed)?;
                let [modifier] = modifiers.list.nodes.as_slice() else {
                    return Ok(None);
                };
                let modifier = source.arena.get(*modifier).ok_or_else(malformed)?;
                let member_ref = NodeRef::new(namespace.arena, namespace.file, *member);
                let member_symbol = source.bound.symbol(member_ref).ok_or_else(malformed)?;
                let member_record = store.symbol(member_symbol).ok_or_else(malformed)?;
                if statement_node.kind != SyntaxKind::VariableStatement
                    || statement_node.parent != namespace_data.body
                    || statement_node.flags.0 != 0
                    || statement_data.flow_node.is_some()
                    || statement_data.facts != 0
                    || modifiers.flags.0 != 0
                    || modifiers.list.has_trailing_comma
                    || modifier.kind != SyntaxKind::ExportKeyword
                    || modifier.flags.0 != 0
                    || modifier.parent != Some(*statement)
                    || !matches!(modifier.data, NodeData::Token(_))
                    || list.kind != SyntaxKind::VariableDeclarationList
                    || list.parent != Some(*statement)
                    || list.flags.0 != 1 << 1
                    || list_data.facts != 0
                    || member_node.kind != SyntaxKind::VariableDeclaration
                    || member_node.parent != Some(statement_data.declaration_list)
                    || member_node.flags.0 != 0
                    || member_data.exclamation_token.is_some()
                    || member_data.initializer.is_some()
                    || member_data.local_symbol.is_some()
                    || member_data.symbol.is_some()
                    || member_data.facts != 0
                    || member_name.kind != SyntaxKind::Identifier
                    || member_name.parent != Some(*member)
                    || member_name.flags.0 != 0
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                    || annotation.parent != Some(*member)
                    || annotation.flags.0 != 0
                    || member_record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
                    || member_record.check_flags() != CheckFlags::NONE
                    || member_record.declarations() != Some(&[member_ref])
                    || member_record.value_declaration() != Some(member_ref)
                    || member_record.members().is_some()
                    || member_record.exports().is_some()
                    || member_record.parent() != Some(original)
                    || member_record.export_symbol().is_some()
                    || member_record.name().as_utf8() != Some(identifier.text.as_str())
                    || store.get_merged_symbol(member_symbol) != Some(member_symbol)
                    || exports.get_source(&identifier.text) != Some(member_symbol)
                {
                    return Err(malformed());
                }
                exported_members
                    .push((EscapedName::source(identifier.text.clone()), member_symbol));
            }
            _ => return Ok(None),
        }

        let importer = self.checked_source(store, declaration)?;
        let namespace_import = importer.arena.get(declaration.node).ok_or_else(malformed)?;
        let NodeData::NamespaceImport(namespace_import_data) = &namespace_import.data else {
            return Err(malformed());
        };
        let clause_id = namespace_import.parent.ok_or_else(malformed)?;
        let clause = importer.arena.get(clause_id).ok_or_else(malformed)?;
        let NodeData::ImportClause(clause_data) = &clause.data else {
            return Err(malformed());
        };
        let import_id = clause.parent.ok_or_else(malformed)?;
        let import = importer.arena.get(import_id).ok_or_else(malformed)?;
        let NodeData::ImportDeclaration(import_data) = &import.data else {
            return Err(malformed());
        };
        let originating_import = NodeRef::new(declaration.arena, declaration.file, import_id);
        let import_name = importer
            .arena
            .get(namespace_import_data.name)
            .ok_or_else(malformed)?;
        let NodeData::Identifier(import_name_data) = &import_name.data else {
            return Err(malformed());
        };
        if clause_data.name.is_some() || import_name_data.text != expression_name.text {
            return Ok(None);
        }
        if namespace_import.kind != SyntaxKind::NamespaceImport
            || namespace_import.flags.0 != 0
            || namespace_import_data.local_symbol.is_some()
            || namespace_import_data.symbol.is_some()
            || clause.kind != SyntaxKind::ImportClause
            || clause.flags.0 != 0
            || clause_data.name.is_some()
            || clause_data.named_bindings != Some(declaration.node)
            || clause_data.phase_modifier.is_some()
            || clause_data.local_symbol.is_some()
            || clause_data.symbol.is_some()
            || clause_data.facts != 0
            || import.kind != SyntaxKind::ImportDeclaration
            || import.flags.0 != 0
            || import_data.import_clause != Some(clause_id)
            || import_data.attributes.is_some()
            || import_data.flow_node.is_some()
            || import_data.symbol.is_some()
            || import_data.facts != 0
            || import_data.modifiers.is_some()
            || importer.bound.symbol(declaration) != Some(alias)
            || !importer.bound.contains(originating_import)
            || !store.contains_node_ref(originating_import)
            || !matches!(
                &import_name.data,
                NodeData::Identifier(name)
                    if import_name.kind == SyntaxKind::Identifier
                        && import_name.parent == Some(declaration.node)
                        && import_name.flags.0 == 0
                        && name.flow_node.is_none()
                        && name.text == expression_name.text
            )
        {
            return Err(malformed());
        }

        if import.parent != Some(importer.bound.source_file().node) {
            let Some(block_id) = import.parent else {
                return Err(malformed());
            };
            let Some(block) = importer.arena.get(block_id) else {
                return Err(malformed());
            };
            let NodeData::ModuleBlock(block_data) = &block.data else {
                return Err(malformed());
            };
            let Some(module_id) = block.parent else {
                return Err(malformed());
            };
            let Some(ambient) = importer.arena.get(module_id) else {
                return Err(malformed());
            };
            let NodeData::ModuleDeclaration(ambient_data) = &ambient.data else {
                return Err(malformed());
            };
            let Some(ambient_name) = importer.arena.get(ambient_data.name) else {
                return Err(malformed());
            };
            let NodeData::StringLiteral(module_name) = &ambient_name.data else {
                return Err(malformed());
            };
            let ambient_ref = NodeRef::new(declaration.arena, declaration.file, module_id);
            let Some(ambient_owner) = importer
                .bound
                .symbol(ambient_ref)
                .and_then(|owner| store.get_merged_symbol(owner))
            else {
                return Err(malformed());
            };
            let Some(ambient_owner_record) = store.symbol(ambient_owner) else {
                return Err(malformed());
            };
            let Some(alias_record) = store.symbol(alias) else {
                return Err(malformed());
            };
            if importer.bound.source_facts().is_none_or(|facts| {
                !facts.is_declaration_file()
                    || facts.is_external_or_common_js_module()
                    || facts.is_javascript_file()
            }) || block.kind != SyntaxKind::ModuleBlock
                || block.flags.0 != 0
                || block_data.flow_node.is_some()
                || block_data.facts != 0
                || block_data
                    .statements
                    .nodes
                    .iter()
                    .filter(|statement| **statement == import_id)
                    .count()
                    != 1
                || ambient.kind != SyntaxKind::ModuleDeclaration
                || ambient.flags.0 != 0
                || ambient.parent != Some(importer.bound.source_file().node)
                || ambient_data.keyword != SyntaxKind::ModuleKeyword
                || ambient_data.body != Some(block_id)
                || ambient_name.kind != SyntaxKind::StringLiteral
                || ambient_name.flags.0 != 0
                || ambient_name.parent != Some(module_id)
                || module_name.token_flags.0 != 0
                || module_name.text.is_empty()
                || !ambient_owner_record.flags().intersects(SymbolFlags::MODULE)
                || ambient_owner_record
                    .declarations()
                    .is_none_or(|declarations| !declarations.contains(&ambient_ref))
                || store.get_merged_symbol(ambient_owner) != Some(ambient_owner)
                || importer.bound.container(declaration) != Some(ambient_ref)
                || importer
                    .bound
                    .locals(ambient_ref)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&import_name_data.text))
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    != Some(alias)
                || alias_record.flags() != SymbolFlags::ALIAS
                || alias_record.check_flags() != CheckFlags::NONE
                || alias_record.declarations() != Some(&[declaration])
                || alias_record.value_declaration().is_some()
                || alias_record.members().is_some()
                || alias_record.exports().is_some()
                || alias_record.parent().is_some()
                || alias_record.export_symbol().is_some()
                || store.get_merged_symbol(alias) != Some(alias)
            {
                return Err(malformed());
            }

            return Ok(None);
        }

        if let Some(cached) = store
            .alias_symbol_links(alias)
            .and_then(|links| links.immediate_target.or(links.alias_target.symbol()))
        {
            if cached == assignment {
                return Ok(None);
            }
            let Some(cached_record) = store.symbol(cached) else {
                return Err(malformed());
            };
            let Some(exports) = cached_record
                .exports()
                .and_then(|exports| store.symbol_table(exports))
            else {
                return Err(malformed());
            };
            let Some(default) = exports.get(InternalSymbolName::Default.as_ref()) else {
                return Err(malformed());
            };
            if exports.len() != 1 + exported_members.len()
                || cached_record.flags() != original_record.flags()
                || cached_record.check_flags() != CheckFlags::NONE
                || cached_record.name() != original_record.name()
                || cached_record.declarations() != original_record.declarations()
                || cached_record.value_declaration() != original_record.value_declaration()
                || cached_record.members().is_some()
                || cached_record.parent() != original_record.parent()
                || cached_record.export_symbol().is_some()
                || store.export_type_links(cached)
                    != Some(&ExportTypeLinks {
                        target: Some(original),
                        originating_import: Some(originating_import),
                    })
                || store.symbol(default).is_none_or(|default_record| {
                    default_record.flags() != SymbolFlags::ALIAS
                        || default_record.check_flags() != CheckFlags::NONE
                        || default_record.name() != InternalSymbolName::Default.as_ref()
                        || default_record.declarations().is_some()
                        || default_record.value_declaration().is_some()
                        || default_record.members().is_some()
                        || default_record.exports().is_some()
                        || default_record.parent() != Some(module)
                        || default_record.export_symbol().is_some()
                })
                || store.alias_symbol_links(default)
                    != Some(&AliasSymbolLinks {
                        immediate_target: Some(original),
                        alias_target: AliasTargetState::Resolved(original),
                        ..AliasSymbolLinks::default()
                    })
                || exported_members
                    .iter()
                    .any(|(name, symbol)| exports.get(name.as_ref()) != Some(*symbol))
            {
                return Err(malformed());
            }
            return Ok(Some(cached));
        }

        let original_name = original_record
            .name()
            .as_utf8()
            .ok_or_else(malformed)?
            .to_owned();
        let original_flags = original_record.flags();
        let original_parent = original_record.parent();
        if !store.try_reserve_checker_symbol_allocations(2, 1)
            || !store.ensure_alias_symbol_links(alias)
        {
            return Err(malformed());
        }
        let exports = store.alloc_symbol_table();
        let default = store
            .alloc_symbol(SymbolData {
                parent: Some(module),
                ..SymbolData::new(
                    SymbolFlags::ALIAS,
                    EscapedName::internal(InternalSymbolName::Default),
                )
            })
            .ok_or_else(malformed)?;
        if !store.set_alias_symbol_links(
            default,
            AliasSymbolLinks {
                immediate_target: Some(original),
                alias_target: AliasTargetState::Resolved(original),
                ..AliasSymbolLinks::default()
            },
        ) || store.insert_symbol(
            exports,
            EscapedName::internal(InternalSymbolName::Default),
            default,
        ) != Some(None)
        {
            return Err(malformed());
        }
        for (name, symbol) in exported_members {
            if store.insert_symbol(exports, name, symbol) != Some(None) {
                return Err(malformed());
            }
        }
        let synthetic = store
            .alloc_symbol(SymbolData {
                declarations: Some(vec![function, namespace]),
                value_declaration: Some(function),
                exports: Some(exports),
                parent: original_parent,
                ..SymbolData::new(original_flags, EscapedName::source(original_name))
            })
            .ok_or_else(malformed)?;
        if !store.set_export_type_links(
            synthetic,
            ExportTypeLinks {
                target: Some(original),
                originating_import: Some(originating_import),
            },
        ) {
            return Err(malformed());
        }
        let mut alias_links = store
            .alias_symbol_links(alias)
            .cloned()
            .ok_or_else(malformed)?;
        alias_links.immediate_target = Some(synthetic);
        if !store.set_alias_symbol_links(alias, alias_links) {
            return Err(malformed());
        }
        Ok(Some(synthetic))
    }

    fn can_have_synthetic_default<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
        module: SemanticSymbolId,
        export_equals: Option<SemanticSymbolId>,
    ) -> Result<bool, CanonicalAliasTargetUnavailable> {
        let source = self.sources.get(resolved.target_file()).ok_or(
            CanonicalAliasTargetUnavailable::ForeignModuleTarget {
                declaration,
                file: resolved.target_file(),
            },
        )?;
        let facts = source.bound.source_facts().ok_or(
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            },
        )?;
        let exports = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .map(|exports| {
                store.symbol_table(exports).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                        declaration,
                        module,
                    },
                )
            })
            .transpose()?;

        if facts.is_declaration_file() || resolved.is_ambient_module() {
            if exports.is_some_and(|exports| exports.get_source("__esModule").is_some()) {
                return Ok(false);
            }
            if let Some(default) =
                exports.and_then(|exports| exports.get(InternalSymbolName::Default.as_ref()))
            {
                let default = store.symbol(default).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                        declaration,
                        module,
                    },
                )?;
                if default.declarations().is_some_and(|declarations| {
                    declarations.iter().copied().any(|declaration| {
                        is_syntactic_default_declaration(source.arena, declaration)
                    })
                }) {
                    return Ok(false);
                }
            }
            return Ok(resolved.is_ambient_module()
                || export_equals.is_some()
                || resolved.usage_mode() != CanonicalModuleResolutionMode::Esm
                || resolved.target_mode() != CanonicalModuleResolutionMode::Esm);
        }

        if facts.is_javascript_file() {
            return Ok(facts.is_common_js_module()
                && exports.is_none_or(|exports| exports.get_source("__esModule").is_none()));
        }

        Ok(export_equals.is_some())
    }

    fn direct_export<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        module: SemanticSymbolId,
        name: &str,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let module_record =
            store
                .symbol(module)
                .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                })?;
        let Some(exports) = module_record.exports() else {
            return Err(CanonicalAliasTargetUnavailable::MissingExport {
                declaration,
                module,
            });
        };
        let exports = store.symbol_table(exports).ok_or(
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration,
                module,
            },
        )?;
        if let Some(target) = exports.get_source(name) {
            return store.symbol(target).is_some().then_some(target).ok_or(
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                },
            );
        }
        if name != "default"
            && exports
                .get(InternalSymbolName::ExportStar.as_ref())
                .is_some()
        {
            return Err(
                CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported {
                    declaration,
                    module,
                },
            );
        }
        Err(CanonicalAliasTargetUnavailable::MissingExport {
            declaration,
            module,
        })
    }

    fn ambient_export_equals_member<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
        module: SemanticSymbolId,
        assignment: SemanticSymbolId,
        name: &str,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let malformed = || CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
            declaration,
            module,
        };
        let source = self
            .sources
            .get(resolved.target_file())
            .ok_or_else(malformed)?;
        let assignment_record = store.symbol(assignment).ok_or_else(malformed)?;
        let Some([assignment_declaration]) = assignment_record.declarations() else {
            return Err(malformed());
        };
        let assignment_declaration = *assignment_declaration;
        if assignment_record.flags() != SymbolFlags::ALIAS
            || assignment_record.check_flags() != CheckFlags::NONE
            || assignment_record.name() != InternalSymbolName::ExportEquals.as_ref()
            || assignment_record.value_declaration() != Some(assignment_declaration)
            || assignment_record.members().is_some()
            || assignment_record.exports().is_some()
            || assignment_record.export_symbol().is_some()
            || store.get_parent_of_symbol(assignment) != Some(module)
            || store.get_merged_symbol(assignment) != Some(assignment)
            || !assignment_declaration.is_for(source.arena.id(), resolved.target_file())
            || !source.bound.contains(assignment_declaration)
            || !store.contains_node_ref(assignment_declaration)
            || source
                .bound
                .symbol(assignment_declaration)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(assignment)
        {
            return Err(malformed());
        }

        let assignment_node = source
            .arena
            .get(assignment_declaration.node)
            .ok_or_else(malformed)?;
        let NodeData::ExportAssignment(export) = &assignment_node.data else {
            return Err(malformed());
        };
        let block = assignment_node.parent.ok_or_else(malformed)?;
        let block_node = source.arena.get(block).ok_or_else(malformed)?;
        let NodeData::ModuleBlock(module_block) = &block_node.data else {
            return Err(malformed());
        };
        let module_declaration = NodeRef::new(
            source.arena.id(),
            resolved.target_file(),
            block_node.parent.ok_or_else(malformed)?,
        );
        let module_node = source
            .arena
            .get(module_declaration.node)
            .ok_or_else(malformed)?;
        let NodeData::ModuleDeclaration(ambient) = &module_node.data else {
            return Err(malformed());
        };
        let expression = NodeRef::new(
            assignment_declaration.arena,
            assignment_declaration.file,
            export.expression,
        );
        let expression_node = source.arena.get(expression.node).ok_or_else(malformed)?;
        let NodeData::Identifier(identifier) = &expression_node.data else {
            return Err(malformed());
        };
        if assignment_node.kind != SyntaxKind::ExportAssignment
            || !export.is_export_equals
            || block_node.kind != SyntaxKind::ModuleBlock
            || !module_block
                .statements
                .nodes
                .contains(&assignment_declaration.node)
            || module_node.kind != SyntaxKind::ModuleDeclaration
            || module_node.parent != Some(source.bound.source_file().node)
            || ambient.body != Some(block)
            || !matches!(
                source.arena.get(ambient.name).map(|node| &node.data),
                Some(NodeData::StringLiteral(_))
            )
            || source
                .bound
                .symbol(module_declaration)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(module)
            || expression_node.kind != SyntaxKind::Identifier
            || expression_node.parent != Some(assignment_declaration.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || !source.bound.contains(expression)
            || !store.contains_node_ref(expression)
        {
            return Err(malformed());
        }

        let namespace =
            Self::alias_expression_target(store, source, assignment_declaration, export.expression)
                .map_err(|_| malformed())?;
        let namespace_record = store.symbol(namespace).ok_or_else(malformed)?;
        let namespace_exports = namespace_record.exports().ok_or_else(malformed)?;
        if !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
            || namespace_record.name().as_utf8() != Some(identifier.text.as_str())
            || !namespace_record.declarations().is_some_and(|declarations| {
                declarations.iter().copied().any(|namespace_declaration| {
                    namespace_declaration.is_for(source.arena.id(), resolved.target_file())
                        && source.bound.contains(namespace_declaration)
                        && store.contains_node_ref(namespace_declaration)
                        && source
                            .bound
                            .symbol(namespace_declaration)
                            .and_then(|symbol| store.get_merged_symbol(symbol))
                            == Some(namespace)
                        && source
                            .arena
                            .get(namespace_declaration.node)
                            .is_some_and(|node| {
                                node.kind == SyntaxKind::ModuleDeclaration
                                    && node.parent == Some(block)
                            })
                })
            })
            || store.alias_symbol_links(assignment).is_some_and(|links| {
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
            return Err(malformed());
        }

        let exports = store
            .symbol_table(namespace_exports)
            .ok_or_else(malformed)?;
        let target =
            exports
                .get_source(name)
                .ok_or(CanonicalAliasTargetUnavailable::MissingExport {
                    declaration,
                    module,
                })?;
        let target = store.get_merged_symbol(target).ok_or_else(malformed)?;
        if store.get_parent_of_symbol(target) != Some(namespace) {
            return Err(malformed());
        }
        Ok(target)
    }

    fn direct_namespace_target<MapperPayload>(
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        module: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let module_record =
            store
                .symbol(module)
                .ok_or(CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                })?;
        if let Some(exports) = module_record.exports() {
            store.symbol_table(exports).ok_or(
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                },
            )?;
        }
        Ok(module)
    }

    fn mark_type_only<MapperPayload>(
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
        declaration: NodeRef,
    ) -> Result<(), CanonicalAliasTargetUnavailable> {
        let mut links = store
            .alias_symbol_links(alias)
            .cloned()
            .ok_or(CanonicalAliasTargetUnavailable::InvalidAliasLinks(alias))?;
        if links.type_only_declaration.is_none() {
            links.type_only_declaration = Some(declaration);
            if !store.set_alias_symbol_links(alias, links) {
                return Err(CanonicalAliasTargetUnavailable::InvalidAliasLinks(alias));
            }
        }
        Ok(())
    }

    /// Re-derives one immediate target and exposes the declaration only when
    /// that exact alias hop is syntactically type-only. The ordinary alias
    /// provider uses the same path, while source import validation retains the
    /// marker to prove transitive warm-cache propagation independently.
    pub(super) fn get_target_and_type_only_of_alias_declaration<MapperPayload>(
        &mut self,
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
    ) -> Result<(CanonicalImmediateAliasTarget, Option<NodeRef>), CanonicalAliasTargetUnavailable>
    {
        if store.id() != self.store {
            return Err(CanonicalAliasTargetUnavailable::ForeignStore {
                expected: self.store,
                actual: store.id(),
            });
        }
        let declaration = self.alias_declaration(store, alias)?;
        let supported = self.supported_declaration(store, declaration)?;
        let type_only = match &supported {
            SupportedAliasDeclaration::NamespaceImport { type_only, .. }
            | SupportedAliasDeclaration::NamespaceExport { type_only, .. }
            | SupportedAliasDeclaration::DefaultModuleMember { type_only, .. }
            | SupportedAliasDeclaration::NamedModuleMember { type_only, .. }
            | SupportedAliasDeclaration::ExternalImportEquals { type_only, .. }
            | SupportedAliasDeclaration::LocalModuleMember { type_only, .. } => *type_only,
        };
        if type_only {
            Self::mark_type_only(store, alias, declaration)?;
        }
        if let SupportedAliasDeclaration::LocalModuleMember { target, .. } = &supported {
            return Ok((
                CanonicalImmediateAliasTarget::Resolved(*target),
                type_only.then_some(declaration),
            ));
        }
        let specifier = match &supported {
            SupportedAliasDeclaration::NamespaceImport { specifier, .. }
            | SupportedAliasDeclaration::NamespaceExport { specifier, .. }
            | SupportedAliasDeclaration::DefaultModuleMember { specifier, .. }
            | SupportedAliasDeclaration::NamedModuleMember { specifier, .. }
            | SupportedAliasDeclaration::ExternalImportEquals { specifier, .. } => *specifier,
            SupportedAliasDeclaration::LocalModuleMember { .. } => {
                unreachable!("local aliases return before resolving an external module")
            }
        };
        let resolved = self.resolved_module(declaration, specifier, store)?;
        let commonjs_javascript_target = self
            .sources
            .get(resolved.target_file())
            .and_then(|target| target.bound.source_facts())
            .is_some_and(|facts| facts.is_javascript_file() && facts.is_common_js_module());
        let allow_mixed_module_modes = matches!(
            supported,
            SupportedAliasDeclaration::NamespaceImport { .. }
                | SupportedAliasDeclaration::ExternalImportEquals { .. }
                | SupportedAliasDeclaration::NamedModuleMember {
                    type_only: true,
                    ..
                }
        ) || commonjs_javascript_target
            && matches!(
                supported,
                SupportedAliasDeclaration::DefaultModuleMember { .. }
                    | SupportedAliasDeclaration::NamedModuleMember { .. }
                    | SupportedAliasDeclaration::NamespaceExport { .. }
            );
        let module =
            self.direct_source_module(store, declaration, resolved, allow_mixed_module_modes)?;
        let export_equals = Self::export_equals_target(store, declaration, module)?;
        let declaration_target = self
            .sources
            .get(resolved.target_file())
            .and_then(|target| target.bound.source_facts())
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file);
        let synthetic_default = matches!(
            supported,
            SupportedAliasDeclaration::DefaultModuleMember { .. }
        ) && self.can_have_synthetic_default(
            store,
            declaration,
            resolved,
            module,
            export_equals,
        )?;
        let runtime_namespace_export_equals =
            if matches!(supported, SupportedAliasDeclaration::NamespaceImport { .. })
                && !declaration_target
            {
                export_equals
                    .map(|assignment| {
                        self.runtime_namespace_export_equals_target(
                            store,
                            declaration,
                            resolved,
                            module,
                            assignment,
                        )
                    })
                    .transpose()?
                    .unwrap_or(false)
            } else {
                false
            };
        if export_equals.is_some() {
            let supported_export_equals = match &supported {
                SupportedAliasDeclaration::ExternalImportEquals { .. } => true,
                SupportedAliasDeclaration::NamespaceImport { .. }
                    if declaration_target || runtime_namespace_export_equals =>
                {
                    true
                }
                SupportedAliasDeclaration::DefaultModuleMember { .. } => synthetic_default,
                SupportedAliasDeclaration::NamedModuleMember { .. }
                    if commonjs_javascript_target || resolved.is_ambient_module() =>
                {
                    true
                }
                _ => false,
            };
            if !supported_export_equals {
                return Err(
                    CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported {
                        declaration,
                        module,
                    },
                );
            }
        }
        let target = match &supported {
            SupportedAliasDeclaration::NamespaceImport { type_only, .. }
                if declaration_target && export_equals.is_some() =>
            {
                let assignment =
                    export_equals.expect("declaration namespace export-equals was preflighted");
                if *type_only {
                    assignment
                } else {
                    self.synthetic_namespace_export_equals_target(
                        store,
                        alias,
                        declaration,
                        resolved,
                        module,
                        assignment,
                    )?
                    .unwrap_or(assignment)
                }
            }
            SupportedAliasDeclaration::NamespaceImport { .. }
                if runtime_namespace_export_equals =>
            {
                export_equals.expect("runtime namespace export-equals was authenticated")
            }
            SupportedAliasDeclaration::NamespaceImport { .. } => {
                Self::direct_namespace_target(store, declaration, module)?
            }
            SupportedAliasDeclaration::NamespaceExport { .. } => module,
            SupportedAliasDeclaration::DefaultModuleMember { .. } if synthetic_default => {
                export_equals.unwrap_or(module)
            }
            SupportedAliasDeclaration::DefaultModuleMember { .. } => {
                Self::direct_export(store, declaration, module, "default")?
            }
            SupportedAliasDeclaration::NamedModuleMember { name, .. }
                if resolved.is_ambient_module() && export_equals.is_some() =>
            {
                self.ambient_export_equals_member(
                    store,
                    declaration,
                    resolved,
                    module,
                    export_equals.expect("ambient export-equals was preflighted"),
                    name,
                )?
            }
            SupportedAliasDeclaration::NamedModuleMember { name, .. } => {
                Self::direct_export(store, declaration, module, name)?
            }
            SupportedAliasDeclaration::ExternalImportEquals { .. } => {
                export_equals.unwrap_or(module)
            }
            SupportedAliasDeclaration::LocalModuleMember { .. } => {
                unreachable!("local aliases return before resolving an external module")
            }
        };
        Ok((
            CanonicalImmediateAliasTarget::Resolved(target),
            type_only.then_some(declaration),
        ))
    }
}

fn validate_source<MapperPayload>(
    store: &CanonicalSemanticStore<MapperPayload>,
    arena: &NodeArena,
    bound: &BoundFile,
) -> Result<FileId, ProductionAliasTargetHostError> {
    let file = bound.file_id();
    if arena.id() != bound.node_arena_id() {
        return Err(ProductionAliasTargetHostError::ArenaMismatch {
            file,
            expected: bound.node_arena_id(),
            actual: arena.id(),
        });
    }
    if !bound.declarations_complete() {
        return Err(ProductionAliasTargetHostError::DeclarationsIncomplete(file));
    }
    if bound.source_facts().is_none() {
        return Err(ProductionAliasTargetHostError::MissingSourceFileFacts(file));
    }

    let source = bound.source_file();
    if !source.is_for(arena.id(), file)
        || !bound.contains(source)
        || !matches!(
            arena.get(source.node),
            Some(Node {
                kind: SyntaxKind::SourceFile,
                parent: None,
                data: NodeData::SourceFile(_),
                ..
            })
        )
    {
        return Err(ProductionAliasTargetHostError::InvalidSourceFile(source));
    }
    if bound.node_arena_revision() != arena.revision() {
        return Err(ProductionAliasTargetHostError::ArenaRevisionMismatch {
            file,
            expected: bound.node_arena_revision(),
            actual: arena.revision(),
        });
    }
    if !store.contains_node_ref(source)
        || bound.traversal_order().any(|node| {
            !store.contains_node_ref(node)
                || bound
                    .symbol(node)
                    .into_iter()
                    .chain(bound.local_symbol(node))
                    .any(|symbol| store.get_merged_symbol(symbol).is_none())
                || bound
                    .locals(node)
                    .is_some_and(|table| store.symbol_table(table).is_none())
        })
    {
        return Err(ProductionAliasTargetHostError::InvalidSymbolStore(file));
    }
    Ok(file)
}

impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload>
    for ProductionAliasTargetHost<'_, '_, '_>
{
    fn get_target_of_alias_declaration(
        &mut self,
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
        self.get_target_and_type_only_of_alias_declaration(store, alias)
            .map(|(target, _)| target)
    }
}

fn is_alias_symbol_declaration(arena: &NodeArena, node: &Node, commonjs_javascript: bool) -> bool {
    match (node.kind, &node.data) {
        (SyntaxKind::ImportClause, NodeData::ImportClause(clause)) => clause.name.is_some(),
        (
            SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::NamespaceExportDeclaration
            | SyntaxKind::NamespaceImport
            | SyntaxKind::NamespaceExport
            | SyntaxKind::ImportSpecifier
            | SyntaxKind::ExportSpecifier,
            _,
        ) => true,
        (SyntaxKind::ExportAssignment, NodeData::ExportAssignment(assignment)) => {
            expression_is_alias(arena, assignment.expression)
        }
        (SyntaxKind::BinaryExpression, NodeData::BinaryExpression(assignment))
            if commonjs_javascript =>
        {
            arena
                .get(assignment.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken)
                && commonjs_assignment_export_name(arena, assignment.left).is_some()
                && expression_is_alias(arena, assignment.right)
        }
        // JavaScript require bindings need their own exact declaration
        // predicate. Accepting every variable or binary expression could make
        // reverse declaration lookup select an unrelated merged declaration.
        _ => false,
    }
}

fn is_syntactic_default_declaration(arena: &NodeArena, declaration: NodeRef) -> bool {
    let Some(record) = arena.get(declaration.node) else {
        return false;
    };
    match &record.data {
        NodeData::ExportAssignment(assignment) => !assignment.is_export_equals,
        NodeData::ExportSpecifier(_) | NodeData::NamespaceExport(_) => true,
        _ => {
            let mut has_default_modifier = false;
            record.for_each_child(|child| {
                has_default_modifier |= arena.get(child).is_some_and(|child| {
                    child.kind == SyntaxKind::DefaultKeyword
                        && child.parent == Some(declaration.node)
                });
            });
            has_default_modifier
        }
    }
}

fn commonjs_assignment_export_name(
    arena: &NodeArena,
    assignment: NodeId,
) -> Option<CommonJsAssignmentExportName<'_>> {
    if is_commonjs_module_exports_access(arena, assignment) {
        return Some(CommonJsAssignmentExportName::ExportEquals);
    }
    let (receiver, name) = match arena.get(assignment).map(|node| &node.data)? {
        NodeData::PropertyAccessExpression(access) => (access.expression, access.name),
        NodeData::ElementAccessExpression(access) => {
            (access.expression, access.argument_expression)
        }
        _ => return None,
    };
    if !is_commonjs_identifier(arena, receiver, "exports")
        && !is_commonjs_module_exports_access(arena, receiver)
    {
        return None;
    }
    module_export_name(arena, name).map(CommonJsAssignmentExportName::Named)
}

fn is_commonjs_module_exports_access(arena: &NodeArena, node: NodeId) -> bool {
    let (receiver, name) = match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access)) => (access.expression, access.name),
        Some(NodeData::ElementAccessExpression(access)) => {
            (access.expression, access.argument_expression)
        }
        _ => return false,
    };
    is_commonjs_identifier(arena, receiver, "module")
        && module_export_name(arena, name) == Some("exports")
}

fn is_commonjs_identifier(arena: &NodeArena, node: NodeId, expected: &str) -> bool {
    matches!(
        arena.get(node),
        Some(Node {
            kind: SyntaxKind::Identifier,
            data: NodeData::Identifier(identifier),
            ..
        }) if identifier.text == expected
    )
}

fn expression_is_alias(arena: &NodeArena, expression: NodeId) -> bool {
    match arena.get(expression).map(|node| &node.data) {
        Some(NodeData::Identifier(_) | NodeData::ClassExpression(_)) => true,
        Some(NodeData::PropertyAccessExpression(access)) => {
            arena
                .get(access.name)
                .is_some_and(|name| name.kind == SyntaxKind::Identifier)
                && expression_is_alias(arena, access.expression)
        }
        _ => false,
    }
}

fn default_import_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<(NodeRef, &ts_ast::ImportClauseData), CanonicalAliasTargetUnavailable> {
    let Some(Node {
        kind: SyntaxKind::ImportClause,
        data: NodeData::ImportClause(clause),
        parent: Some(import_id),
        ..
    }) = arena.get(declaration.node)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if clause.name.is_none() {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(Node {
        kind: SyntaxKind::ImportDeclaration | SyntaxKind::JsImportDeclaration,
        data: NodeData::ImportDeclaration(import),
        ..
    }) = arena.get(*import_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if import.import_clause != Some(declaration.node) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    Ok((
        NodeRef::new(declaration.arena, declaration.file, import.module_specifier),
        clause,
    ))
}

fn import_equals_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<NodeRef, CanonicalAliasTargetUnavailable> {
    let Some(Node {
        kind: SyntaxKind::ImportEqualsDeclaration,
        data: NodeData::ImportEqualsDeclaration(import),
        ..
    }) = arena.get(declaration.node)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    let Some(Node {
        kind: SyntaxKind::ExternalModuleReference,
        data: NodeData::ExternalModuleReference(reference),
        parent: Some(parent),
        ..
    }) = arena.get(import.module_reference)
    else {
        return Err(CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration));
    };
    if *parent != declaration.node {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(specifier) = arena.get(reference.expression) else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if specifier.parent != Some(import.module_reference) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    Ok(NodeRef::new(
        declaration.arena,
        declaration.file,
        reference.expression,
    ))
}

fn namespace_import_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<(NodeRef, &ts_ast::ImportClauseData), CanonicalAliasTargetUnavailable> {
    let clause_id = exact_parent(arena, declaration)?;
    let Some(Node {
        kind: SyntaxKind::ImportClause,
        data: NodeData::ImportClause(clause),
        parent: Some(import_id),
        ..
    }) = arena.get(clause_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if clause.named_bindings != Some(declaration.node) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(Node {
        kind: SyntaxKind::ImportDeclaration | SyntaxKind::JsImportDeclaration,
        data: NodeData::ImportDeclaration(import),
        ..
    }) = arena.get(*import_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if import.import_clause != Some(clause_id) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    Ok((
        NodeRef::new(declaration.arena, declaration.file, import.module_specifier),
        clause,
    ))
}

fn namespace_export_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<(NodeRef, bool), CanonicalAliasTargetUnavailable> {
    let export_id = exact_parent(arena, declaration)?;
    let Some(Node {
        kind: SyntaxKind::ExportDeclaration,
        data: NodeData::ExportDeclaration(export),
        ..
    }) = arena.get(export_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if export.export_clause != Some(declaration.node) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(specifier) = export.module_specifier else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    Ok((
        NodeRef::new(declaration.arena, declaration.file, specifier),
        export.is_type_only,
    ))
}

fn import_specifier_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<(NodeRef, &ts_ast::ImportClauseData), CanonicalAliasTargetUnavailable> {
    let named_id = exact_parent(arena, declaration)?;
    let Some(Node {
        kind: SyntaxKind::NamedImports,
        data: NodeData::NamedImports(named),
        parent: Some(clause_id),
        ..
    }) = arena.get(named_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if !named.elements.nodes.contains(&declaration.node) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(Node {
        kind: SyntaxKind::ImportClause,
        data: NodeData::ImportClause(clause),
        parent: Some(import_id),
        ..
    }) = arena.get(*clause_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if clause.named_bindings != Some(named_id) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(Node {
        kind: SyntaxKind::ImportDeclaration | SyntaxKind::JsImportDeclaration,
        data: NodeData::ImportDeclaration(import),
        ..
    }) = arena.get(*import_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if import.import_clause != Some(*clause_id) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    Ok((
        NodeRef::new(declaration.arena, declaration.file, import.module_specifier),
        clause,
    ))
}

fn export_specifier_context(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<(Option<NodeRef>, bool), CanonicalAliasTargetUnavailable> {
    let named_id = exact_parent(arena, declaration)?;
    let Some(Node {
        kind: SyntaxKind::NamedExports,
        data: NodeData::NamedExports(named),
        parent: Some(export_id),
        ..
    }) = arena.get(named_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if !named.elements.nodes.contains(&declaration.node) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    let Some(Node {
        kind: SyntaxKind::ExportDeclaration,
        data: NodeData::ExportDeclaration(export),
        ..
    }) = arena.get(*export_id)
    else {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    };
    if export.export_clause != Some(named_id) {
        return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ));
    }
    Ok((
        export
            .module_specifier
            .map(|specifier| NodeRef::new(declaration.arena, declaration.file, specifier)),
        export.is_type_only,
    ))
}

fn exact_parent(
    arena: &NodeArena,
    declaration: NodeRef,
) -> Result<NodeId, CanonicalAliasTargetUnavailable> {
    arena
        .get(declaration.node)
        .and_then(|node| node.parent)
        .ok_or(CanonicalAliasTargetUnavailable::MalformedDeclaration(
            declaration,
        ))
}

fn module_export_name(arena: &NodeArena, name: NodeId) -> Option<&str> {
    match &arena.get(name)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        NodeData::StringLiteral(literal) => Some(&literal.text),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::NodeData;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SymbolData,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, SymbolNodeLinks,
        alias::{CanonicalAliasResolutionError, CanonicalAliasResolver},
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalResolvedModuleInput, validate_module_resolution_manifest,
        },
    };

    type TestStore = CanonicalSemanticStore<()>;

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn source_facts(
        file: FileId,
        state: CanonicalModuleState,
        declaration_file: bool,
    ) -> CanonicalSourceFileFacts {
        let javascript = matches!(
            state,
            CanonicalModuleState::CommonJs | CanonicalModuleState::ExternalAndCommonJs
        );
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!(
                "\"/project/{}.{}\"",
                file.index(),
                if javascript {
                    "js"
                } else if declaration_file {
                    "d.ts"
                } else {
                    "ts"
                }
            )),
            if javascript {
                CanonicalSourceLanguage::JavaScript
            } else {
                CanonicalSourceLanguage::TypeScript
            },
            declaration_file,
            state,
        )
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
                NodeData::ImportEqualsDeclaration(import) => {
                    match parsed
                        .arena
                        .get(import.module_reference)
                        .map(|node| &node.data)
                    {
                        Some(NodeData::ExternalModuleReference(reference)) => {
                            Some(reference.expression)
                        }
                        _ => None,
                    }
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        specifiers.sort_unstable_by_key(|node| parsed.arena.get(*node).unwrap().range.start);
        specifiers
    }

    fn alias_declaration_named(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, data)| {
                let name_node = match &data.data {
                    NodeData::ImportClause(clause) => clause.name,
                    NodeData::ImportEqualsDeclaration(import) => Some(import.name),
                    NodeData::ImportSpecifier(specifier) => Some(specifier.name),
                    NodeData::ExportSpecifier(specifier) => Some(specifier.name),
                    NodeData::NamespaceImport(namespace) => Some(namespace.name),
                    NodeData::NamespaceExport(namespace) => Some(namespace.name),
                    NodeData::NamespaceExportDeclaration(namespace) => Some(namespace.name),
                    _ => None,
                }?;
                (module_export_name(&parsed.arena, name_node) == Some(name))
                    .then_some(node_ref(parsed, file, node))
            })
            .unwrap_or_else(|| panic!("missing alias declaration {name}"))
    }

    fn esm(target: FileId) -> CanonicalResolvedModuleInput {
        CanonicalResolvedModuleInput::new(
            target,
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::Esm,
        )
    }

    fn bindings(
        files: &[(FileId, &ParseResult, CanonicalModuleState)],
    ) -> (ts_binder::SymbolStore, BTreeMap<FileId, BoundFile>) {
        bindings_with_declaration_files(files, &[])
    }

    fn bindings_with_declaration_files(
        files: &[(FileId, &ParseResult, CanonicalModuleState)],
        declaration_files: &[FileId],
    ) -> (ts_binder::SymbolStore, BTreeMap<FileId, BoundFile>) {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, state) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts(file, state, declaration_files.contains(&file)),
                )
                .unwrap();
        }
        for &(file, parsed, state) in files {
            if matches!(
                state,
                CanonicalModuleState::CommonJs | CanonicalModuleState::ExternalAndCommonJs
            ) {
                binder
                    .bind_javascript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            } else {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
        }
        binder.finish().try_into_parts().unwrap()
    }

    fn fixture(
        files: &[(FileId, &ParseResult, CanonicalModuleState)],
        input: CanonicalModuleResolutionManifestInput,
    ) -> (
        TestStore,
        BTreeMap<FileId, BoundFile>,
        CanonicalModuleResolutionManifest,
    ) {
        fixture_with_declaration_files(files, input, &[])
    }

    fn fixture_with_declaration_files(
        files: &[(FileId, &ParseResult, CanonicalModuleState)],
        input: CanonicalModuleResolutionManifestInput,
        declaration_files: &[FileId],
    ) -> (
        TestStore,
        BTreeMap<FileId, BoundFile>,
        CanonicalModuleResolutionManifest,
    ) {
        let (symbols, bound_files) = if declaration_files.is_empty() {
            bindings(files)
        } else {
            bindings_with_declaration_files(files, declaration_files)
        };
        let manifest = validate_module_resolution_manifest(
            input,
            &symbols,
            files.iter().map(|(file, parsed, _)| {
                (
                    *file,
                    &parsed.arena,
                    bound_files.get(file).expect("fixture bound every source"),
                )
            }),
        )
        .unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        for &(file, parsed, _) in files {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        (store, bound_files, manifest)
    }

    fn sources<'arena, 'bound>(
        files: &'arena [(FileId, &'arena ParseResult, CanonicalModuleState)],
        bound_files: &'bound BTreeMap<FileId, BoundFile>,
    ) -> impl Iterator<Item = (&'arena NodeArena, &'bound BoundFile)> {
        files.iter().map(|(file, parsed, _)| {
            (
                &parsed.arena,
                bound_files.get(file).expect("fixture bound every source"),
            )
        })
    }

    fn alias(bound_files: &BTreeMap<FileId, BoundFile>, declaration: NodeRef) -> SemanticSymbolId {
        bound_files
            .get(&declaration.file)
            .and_then(|bound| bound.symbol(declaration))
            .expect("alias declaration has a canonical symbol")
    }

    fn source_module(bound_files: &BTreeMap<FileId, BoundFile>, file: FileId) -> SemanticSymbolId {
        let bound = bound_files.get(&file).unwrap();
        bound.symbol(bound.source_file()).unwrap()
    }

    fn direct_export(
        store: &TestStore,
        bound_files: &BTreeMap<FileId, BoundFile>,
        file: FileId,
        name: &str,
    ) -> SemanticSymbolId {
        let module = source_module(bound_files, file);
        let exports = store.symbol(module).unwrap().exports().unwrap();
        store
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    fn unavailable_reason(error: CanonicalAliasResolutionError) -> CanonicalAliasTargetUnavailable {
        match error {
            CanonicalAliasResolutionError::TargetUnavailable { reason, .. } => reason,
            other => panic!("expected unavailable target, got {other:?}"),
        }
    }

    #[test]
    fn named_imports_follow_bound_javascript_commonjs_export_assignments() {
        let importer = parsed(
            r#"
                import { direct as value, aliased as forwarded } from "./target.js";
                export { direct as exposed } from "./target.js";
            "#,
        );
        let javascript = parse_javascript_source_file(
            "const local = 1; exports.direct = 2; exports.aliased = local;",
        );
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(80);
        let target_file = FileId::new(81);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let direct = direct_export(&store, &bound_files, target_file, "direct");
        let assigned_alias = direct_export(&store, &bound_files, target_file, "aliased");
        let target_bound = bound_files.get(&target_file).unwrap();
        let target_locals = target_bound.locals(target_bound.source_file()).unwrap();
        let local = store
            .symbol_table(target_locals)
            .unwrap()
            .get_source("local")
            .unwrap();

        for (name, immediate, final_target) in [
            ("value", direct, direct),
            ("forwarded", assigned_alias, local),
            ("exposed", direct, direct),
        ] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let alias_symbol = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(alias_symbol)
                    .unwrap(),
                Some(immediate)
            );
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias_symbol)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(final_target)
            );
        }
    }

    #[test]
    fn import_equals_resolves_real_javascript_module_exports_alias() {
        let importer = parsed(concat!(
            "import required = require('./target.js'); ",
            "import selected from './target.js';",
        ));
        let javascript = parse_javascript_source_file("const local = 1; module.exports = local;");
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(82);
        let target_file = FileId::new(83);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .enumerate()
            .map(|(index, specifier)| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        if index == 0 {
                            CanonicalModuleResolutionMode::CommonJs
                        } else {
                            CanonicalModuleResolutionMode::Esm
                        },
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let required_declaration = alias_declaration_named(&importer, importer_file, "required");
        let required = alias(&bound_files, required_declaration);
        let selected = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "selected"),
        );
        let module = source_module(&bound_files, target_file);
        let module_exports = store.symbol(module).unwrap().exports().unwrap();
        let assignment = store
            .symbol_table(module_exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let target_bound = bound_files.get(&target_file).unwrap();
        let target_locals = target_bound.locals(target_bound.source_file()).unwrap();
        let local = store
            .symbol_table(target_locals)
            .unwrap()
            .get_source("local")
            .unwrap();

        for imported in [required, selected] {
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(imported)
                    .unwrap(),
                Some(assignment)
            );
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(imported)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(local)
            );
        }
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(assignment)
                .unwrap(),
            Some(local)
        );
        assert_eq!(
            store.alias_symbol_links(assignment),
            Some(&AliasSymbolLinks {
                immediate_target: Some(local),
                alias_target: AliasTargetState::Resolved(local),
                ..AliasSymbolLinks::default()
            })
        );

        let symbols = [required, selected, assignment];
        let warm = symbols.map(|symbol| store.alias_symbol_links(symbol).cloned());
        for symbol in symbols {
            let resolved = CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(symbol)
                .unwrap();
            assert_eq!(resolved.target, AliasTargetState::Resolved(local));
            assert!(resolved.events.is_empty());
        }
        assert_eq!(
            symbols.map(|symbol| store.alias_symbol_links(symbol).cloned()),
            warm
        );
    }

    #[test]
    fn commonjs_export_equals_preserves_named_exports_and_missing_export_errors() {
        let importer = parsed(concat!(
            "import { present, missing as absent } from './target.js'; ",
            "export { missing as forwarded } from './target.js';",
        ));
        let javascript = parse_javascript_source_file(concat!(
            "const local = 1; ",
            "module.exports = local; ",
            "exports.present = local;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(100);
        let target_file = FileId::new(101);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let entries = module_specifiers(&importer).into_iter().map(|specifier| {
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, specifier),
                CanonicalResolvedModuleInput::new(
                    target_file,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::CommonJs,
                ),
            )
        });
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, target_file);
        let exported = direct_export(&store, &bound_files, target_file, "present");
        let target_bound = bound_files.get(&target_file).unwrap();
        let locals = target_bound.locals(target_bound.source_file()).unwrap();
        let local = store
            .symbol_table(locals)
            .unwrap()
            .get_source("local")
            .unwrap();
        let present = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "present"),
        );

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(present)
                .unwrap(),
            Some(exported)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(present)
                .unwrap()
                .target,
            AliasTargetState::Resolved(local)
        );

        for name in ["absent", "forwarded"] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let missing = alias(&bound_files, declaration);
            for _ in 0..2 {
                assert_eq!(
                    unavailable_reason(
                        CanonicalAliasResolver::new(&mut store, &mut host)
                            .resolve_alias(missing)
                            .unwrap_err()
                    ),
                    CanonicalAliasTargetUnavailable::MissingExport {
                        declaration,
                        module,
                    }
                );
                assert_eq!(
                    store.alias_symbol_links(missing),
                    Some(&AliasSymbolLinks::default())
                );
                assert!(store.type_resolution_is_empty());
            }
        }
    }

    #[test]
    fn commonjs_export_equals_with_promoted_types_resolves_its_exact_rhs() {
        let mut javascript = parsed(concat!(
            "type Exported = number; ",
            "const local = 1; module.exports = local;",
        ));
        let type_alias = javascript
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(node)
            })
            .unwrap();
        javascript.arena.get_mut(type_alias).unwrap().kind = SyntaxKind::JsTypeAliasDeclaration;
        let file = FileId::new(112);
        let files = [(file, &javascript, CanonicalModuleState::CommonJs)];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new([]));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, file);
        let exports = store.symbol(module).unwrap().exports().unwrap();
        let assignment = store
            .symbol_table(exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let assignment_record = store.symbol(assignment).unwrap();
        assert_eq!(
            assignment_record.flags(),
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE
        );
        let promoted = assignment_record.exports().unwrap();
        let exported = store
            .symbol_table(promoted)
            .unwrap()
            .get_source("Exported")
            .unwrap();
        let bound = bound_files.get(&file).unwrap();
        let locals = bound.locals(bound.source_file()).unwrap();
        let local = store
            .symbol_table(locals)
            .unwrap()
            .get_source("local")
            .unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(assignment)
                .unwrap(),
            Some(local)
        );
        for _ in 0..2 {
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(assignment)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(local)
            );
            assert_eq!(
                store.symbol_table(promoted).unwrap().get_source("Exported"),
                Some(exported)
            );
        }
    }

    #[test]
    fn commonjs_export_equals_rejects_invalid_ownership_and_wrong_cached_rhs() {
        #[derive(Clone, Copy, Debug)]
        enum InvalidAssignment {
            ValueDeclaration,
            Parent,
            ShadowedModule,
            CachedModule,
            Local,
            CachedLocal,
        }

        for (index, invalid) in [
            InvalidAssignment::ValueDeclaration,
            InvalidAssignment::Parent,
            InvalidAssignment::ShadowedModule,
            InvalidAssignment::CachedModule,
            InvalidAssignment::Local,
            InvalidAssignment::CachedLocal,
        ]
        .into_iter()
        .enumerate()
        {
            let importer = parsed("import required = require('./target.js');");
            let javascript = parse_javascript_source_file(concat!(
                "const local = 1; ",
                "const other = 2; ",
                "module.exports = local;",
            ));
            assert!(
                javascript.diagnostics.is_empty(),
                "{:?}",
                javascript.diagnostics
            );
            let index = u32::try_from(index).unwrap();
            let importer_file = FileId::new(102 + index * 2);
            let target_file = FileId::new(103 + index * 2);
            let files = [
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &javascript, CanonicalModuleState::CommonJs),
            ];
            let specifier = module_specifiers(&importer)[0];
            let (mut store, bound_files, manifest) = fixture(
                &files,
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        node_ref(&importer, importer_file, specifier),
                        CanonicalResolvedModuleInput::new(
                            target_file,
                            CanonicalModuleResolutionMode::CommonJs,
                            CanonicalModuleResolutionMode::CommonJs,
                        ),
                    ),
                ]),
            );
            let mut host =
                ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                    .unwrap();
            let required = alias(
                &bound_files,
                alias_declaration_named(&importer, importer_file, "required"),
            );
            let module = source_module(&bound_files, target_file);
            let module_exports = store.symbol(module).unwrap().exports().unwrap();
            let assignment = store
                .symbol_table(module_exports)
                .unwrap()
                .get(InternalSymbolName::ExportEquals.as_ref())
                .unwrap();
            let declaration = store
                .symbol(assignment)
                .unwrap()
                .value_declaration()
                .unwrap();
            let NodeData::BinaryExpression(binary) =
                &javascript.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected a CommonJS assignment declaration")
            };
            let NodeData::PropertyAccessExpression(left) =
                &javascript.arena.get(binary.left).unwrap().data
            else {
                panic!("expected a CommonJS property access")
            };
            let receiver = node_ref(&javascript, target_file, left.expression);
            let right = node_ref(&javascript, target_file, binary.right);
            let target_bound = bound_files.get(&target_file).unwrap();
            let locals = target_bound.locals(target_bound.source_file()).unwrap();
            let implicit_module = store
                .symbol_table(locals)
                .unwrap()
                .get_source("module")
                .unwrap();
            let local = store
                .symbol_table(locals)
                .unwrap()
                .get_source("local")
                .unwrap();
            let other = store
                .symbol_table(locals)
                .unwrap()
                .get_source("other")
                .unwrap();

            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(required)
                    .unwrap(),
                Some(assignment)
            );

            match invalid {
                InvalidAssignment::ValueDeclaration => assert!(store.set_symbol_declarations(
                    assignment,
                    Some(vec![declaration]),
                    None,
                )),
                InvalidAssignment::Parent => {
                    let record = store.symbol(assignment).unwrap();
                    let relationships =
                        (record.members(), record.exports(), record.export_symbol());
                    assert!(store.set_symbol_relationships(
                        assignment,
                        relationships.0,
                        relationships.1,
                        Some(source_module(&bound_files, importer_file)),
                        relationships.2,
                    ));
                }
                InvalidAssignment::ShadowedModule => assert_eq!(
                    store.insert_symbol(locals, EscapedName::source("module"), other),
                    Some(Some(implicit_module))
                ),
                InvalidAssignment::CachedModule => assert!(store.set_symbol_node_links(
                    receiver,
                    SymbolNodeLinks {
                        resolved_symbol: Some(other),
                    },
                )),
                InvalidAssignment::Local => assert_eq!(
                    store.insert_symbol(locals, EscapedName::source("local"), other),
                    Some(Some(local))
                ),
                InvalidAssignment::CachedLocal => assert!(store.set_symbol_node_links(
                    right,
                    SymbolNodeLinks {
                        resolved_symbol: Some(other),
                    },
                )),
            }

            for _ in 0..2 {
                assert_eq!(
                    unavailable_reason(
                        CanonicalAliasResolver::new(&mut store, &mut host)
                            .resolve_alias(required)
                            .unwrap_err()
                    ),
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                    "{invalid:?}"
                );
                assert_eq!(
                    store.alias_symbol_links(required),
                    Some(&AliasSymbolLinks {
                        immediate_target: Some(assignment),
                        ..AliasSymbolLinks::default()
                    })
                );
                assert_eq!(
                    store.alias_symbol_links(assignment),
                    Some(&AliasSymbolLinks::default())
                );
                assert!(store.type_resolution_is_empty());
            }

            match invalid {
                InvalidAssignment::ValueDeclaration => assert!(store.set_symbol_declarations(
                    assignment,
                    Some(vec![declaration]),
                    Some(declaration),
                )),
                InvalidAssignment::Parent => {
                    let record = store.symbol(assignment).unwrap();
                    let relationships =
                        (record.members(), record.exports(), record.export_symbol());
                    assert!(store.set_symbol_relationships(
                        assignment,
                        relationships.0,
                        relationships.1,
                        Some(module),
                        relationships.2,
                    ));
                }
                InvalidAssignment::ShadowedModule => assert_eq!(
                    store.insert_symbol(locals, EscapedName::source("module"), implicit_module),
                    Some(Some(other))
                ),
                InvalidAssignment::CachedModule => assert!(store.set_symbol_node_links(
                    receiver,
                    SymbolNodeLinks {
                        resolved_symbol: Some(implicit_module),
                    },
                )),
                InvalidAssignment::Local => assert_eq!(
                    store.insert_symbol(locals, EscapedName::source("local"), local),
                    Some(Some(other))
                ),
                InvalidAssignment::CachedLocal => assert!(store.set_symbol_node_links(
                    right,
                    SymbolNodeLinks {
                        resolved_symbol: Some(local),
                    },
                )),
            }

            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(required)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(local),
                "{invalid:?}"
            );
        }
    }

    #[test]
    fn commonjs_imports_recheck_source_module_declaration_identity() {
        let importer = parsed("import required = require('./target.js');");
        let javascript = parse_javascript_source_file("const local = 1; module.exports = local;");
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(110);
        let target_file = FileId::new(111);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let required_declaration = alias_declaration_named(&importer, importer_file, "required");
        let required = alias(&bound_files, required_declaration);
        let target_bound = bound_files.get(&target_file).unwrap();
        let source = target_bound.source_file();
        let module = source_module(&bound_files, target_file);
        let module_record = store.symbol(module).unwrap();
        let exports = module_record.exports().unwrap();
        let source_value_declaration = module_record.value_declaration();
        let assignment = store
            .symbol_table(exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let assignment_declaration = store
            .symbol(assignment)
            .unwrap()
            .value_declaration()
            .unwrap();
        let locals = target_bound.locals(source).unwrap();
        let local = store
            .symbol_table(locals)
            .unwrap()
            .get_source("local")
            .unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(required)
                .unwrap(),
            Some(assignment)
        );
        assert!(store.set_symbol_declarations(
            module,
            Some(vec![assignment_declaration]),
            source_value_declaration,
        ));

        for _ in 0..2 {
            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(required)
                        .unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration: required_declaration,
                    module,
                }
            );
            assert_eq!(
                store.alias_symbol_links(required),
                Some(&AliasSymbolLinks {
                    immediate_target: Some(assignment),
                    ..AliasSymbolLinks::default()
                })
            );
            assert!(store.type_resolution_is_empty());
        }

        assert!(store.set_symbol_declarations(
            module,
            Some(vec![source]),
            source_value_declaration,
        ));
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(required)
                .unwrap()
                .target,
            AliasTargetState::Resolved(local)
        );
    }

    #[test]
    fn exported_class_expressions_preserve_their_bound_class_symbols() {
        let scenarios = [
            (
                r#"import required = require("./target");"#,
                "export = class Named {};",
                "required",
                CanonicalModuleState::External,
                CanonicalModuleResolutionMode::CommonJs,
            ),
            (
                r#"import { A as selected } from "./target";"#,
                "module.exports.A = class Named {};",
                "selected",
                CanonicalModuleState::CommonJs,
                CanonicalModuleResolutionMode::Esm,
            ),
        ];
        for (index, (importer_text, target_text, name, target_state, usage_mode)) in
            scenarios.into_iter().enumerate()
        {
            let importer = parsed(importer_text);
            let target = if target_state == CanonicalModuleState::CommonJs {
                parse_javascript_source_file(target_text)
            } else {
                parsed(target_text)
            };
            assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
            let index = u32::try_from(index).unwrap();
            let importer_file = FileId::new(86 + index * 2);
            let target_file = FileId::new(87 + index * 2);
            let files = [
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, target_state),
            ];
            let specifier = module_specifiers(&importer)[0];
            let (mut store, bound_files, manifest) = fixture(
                &files,
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        node_ref(&importer, importer_file, specifier),
                        CanonicalResolvedModuleInput::new(
                            target_file,
                            usage_mode,
                            CanonicalModuleResolutionMode::CommonJs,
                        ),
                    ),
                ]),
            );
            let mut host =
                ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                    .unwrap();
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let alias_symbol = alias(&bound_files, declaration);
            let class = target
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ClassExpression).then_some(node_ref(
                        &target,
                        target_file,
                        node,
                    ))
                })
                .unwrap();
            let expected = bound_files
                .get(&target_file)
                .and_then(|bound| bound.symbol(class))
                .unwrap();

            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias_symbol)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(expected),
                "class-expression alias {name}"
            );
            assert!(
                store
                    .symbol(expected)
                    .unwrap()
                    .flags()
                    .intersects(SymbolFlags::CLASS)
            );
        }
    }

    #[test]
    fn javascript_commonjs_defaults_use_the_module_and_missing_names_stay_explicit() {
        let importer = parsed(
            r#"
                import selected from "./target.js";
                import { missing } from "./target.js";
            "#,
        );
        let javascript = parse_javascript_source_file("exports.value = 1;");
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(84);
        let target_file = FileId::new(85);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, target_file);
        let default_declaration = alias_declaration_named(&importer, importer_file, "selected");
        let missing_declaration = alias_declaration_named(&importer, importer_file, "missing");
        let default_alias = alias(&bound_files, default_declaration);
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(default_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module)
        );

        let missing_alias = alias(&bound_files, missing_declaration);
        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(missing_alias)
                    .unwrap_err()
            ),
            CanonicalAliasTargetUnavailable::MissingExport {
                declaration: missing_declaration,
                module,
            }
        );
        assert_eq!(
            store
                .alias_symbol_links(missing_alias)
                .unwrap()
                .alias_target,
            AliasTargetState::Unresolved
        );
    }

    #[test]
    fn declaration_modules_synthesize_defaults_without_explicit_esm_markers() {
        let importer = parsed(r#"import selected from "./target";"#);
        let declaration = parsed("export declare function value(): number;");
        let importer_file = FileId::new(90);
        let declaration_file = FileId::new(91);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        declaration_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
            &[declaration_file],
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "selected"),
        );
        let module = source_module(&bound_files, declaration_file);

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module)
        );
    }

    #[test]
    fn declaration_esmodule_marker_blocks_synthetic_default() {
        let importer = parsed(r#"import selected from "./target";"#);
        let declaration = parsed(concat!(
            "export declare const __esModule: boolean; ",
            "export declare function value(): number;",
        ));
        let importer_file = FileId::new(92);
        let declaration_file = FileId::new(93);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        declaration_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
            &[declaration_file],
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected_declaration = alias_declaration_named(&importer, importer_file, "selected");
        let selected = alias(&bound_files, selected_declaration);
        let module = source_module(&bound_files, declaration_file);

        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(selected)
                    .unwrap_err()
            ),
            CanonicalAliasTargetUnavailable::MissingExport {
                declaration: selected_declaration,
                module,
            }
        );
        assert_eq!(
            store.alias_symbol_links(selected).unwrap().alias_target,
            AliasTargetState::Unresolved
        );
    }

    #[test]
    fn typescript_export_equals_supplies_a_synthetic_default() {
        let importer = parsed(r#"import selected from "./target";"#);
        let target = parsed("const value: number = 1; export = value;");
        let importer_file = FileId::new(94);
        let target_file = FileId::new(95);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "selected"),
        );
        let module = source_module(&bound_files, target_file);
        let module_exports = store.symbol(module).unwrap().exports().unwrap();
        let assignment = store
            .symbol_table(module_exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let target_bound = bound_files.get(&target_file).unwrap();
        let target_locals = target_bound.locals(target_bound.source_file()).unwrap();
        let value = store
            .symbol_table(target_locals)
            .unwrap()
            .get_source("value")
            .unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(selected)
                .unwrap(),
            Some(assignment)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(value)
        );
    }

    #[test]
    fn declaration_export_equals_keeps_namespace_and_default_aliases_aligned() {
        let importer = parsed(concat!(
            "import * as Imported from './target'; ",
            "import Selected from './target';",
        ));
        let declaration = parsed(concat!(
            "declare namespace React { export interface Model { value: number; } } ",
            "export = React; ",
            "export as namespace GlobalReact;",
        ));
        let importer_file = FileId::new(98);
        let declaration_file = FileId::new(99);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new(entries),
            &[declaration_file],
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let target_bound = bound_files.get(&declaration_file).unwrap();
        let locals = target_bound.locals(target_bound.source_file()).unwrap();
        let namespace = store
            .symbol_table(locals)
            .unwrap()
            .get_source("React")
            .unwrap();

        for (file, parsed, name) in [
            (importer_file, &importer, "Imported"),
            (importer_file, &importer, "Selected"),
            (declaration_file, &declaration, "GlobalReact"),
        ] {
            let declaration = alias_declaration_named(parsed, file, name);
            let alias_symbol = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias_symbol)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(namespace),
                "namespace alias {name}"
            );
        }
    }

    #[test]
    fn runtime_namespace_import_follows_the_merged_export_equals_alias() {
        let importer = parsed(concat!(
            "import * as renamed from './target'; ",
            "import required = require('./target');",
        ));
        let target = parsed(concat!(
            "function callable() {} ",
            "namespace callable { export var value = 1; } ",
            "export = callable;",
        ));
        let importer_file = FileId::new(5_230);
        let target_file = FileId::new(5_231);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer).into_iter().map(|specifier| {
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, specifier),
                esm(target_file),
            )
        });
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let target_bound = bound_files.get(&target_file).unwrap();
        let original = store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("callable")
            .unwrap();
        let module = source_module(&bound_files, target_file);
        let assignment = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        for name in ["renamed", "required"] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let imported = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(imported)
                    .unwrap(),
                Some(assignment),
            );
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(imported)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(original),
            );
            assert_eq!(
                store.alias_symbol_links(imported),
                Some(&AliasSymbolLinks {
                    immediate_target: Some(assignment),
                    alias_target: AliasTargetState::Resolved(original),
                    ..AliasSymbolLinks::default()
                }),
            );
        }

        let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
        let imported = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "renamed"),
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(imported)
                .unwrap()
                .target,
            AliasTargetState::Resolved(original),
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations,
        );
        assert!(store.value_symbol_links(original).is_none());
    }

    #[test]
    fn runtime_namespace_import_rejects_forged_export_equals_ownership() {
        for poison_assignment in [true, false] {
            let importer = parsed("import * as renamed from './target';");
            let target = parsed(concat!(
                "function callable() {} ",
                "namespace callable { export var value = 1; } ",
                "export = callable;",
            ));
            let importer_file = FileId::new(5_232 + u32::from(poison_assignment) * 2);
            let target_file = FileId::new(5_233 + u32::from(poison_assignment) * 2);
            let files = [
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ];
            let specifier = module_specifiers(&importer)[0];
            let (mut store, bound_files, manifest) = fixture(
                &files,
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        node_ref(&importer, importer_file, specifier),
                        esm(target_file),
                    ),
                ]),
            );
            let declaration = alias_declaration_named(&importer, importer_file, "renamed");
            let imported = alias(&bound_files, declaration);
            let module = source_module(&bound_files, target_file);
            let assignment = store
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
                .unwrap();
            let target_bound = bound_files.get(&target_file).unwrap();
            let original = store
                .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
                .unwrap()
                .get_source("callable")
                .unwrap();
            if poison_assignment {
                assert!(store.set_symbol_relationships(assignment, None, None, None, None));
            } else {
                let member = store
                    .symbol(original)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| store.symbol_table(exports))
                    .and_then(|exports| exports.get_source("value"))
                    .unwrap();
                assert!(store.set_symbol_relationships(member, None, None, Some(module), None));
            }
            let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
            let mut host =
                ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                    .unwrap();

            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(imported)
                        .unwrap_err(),
                ),
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                },
            );
            assert_eq!(
                (store.symbol_len(), store.symbol_store().symbol_table_len()),
                allocations,
            );
            assert!(store.value_symbol_links(original).is_none());
        }
    }

    #[test]
    fn declaration_namespace_import_wraps_exact_merged_ambient_callable() {
        let importer = parsed(r#"import * as foo from "./foo";"#);
        let declaration = parsed(concat!(
            "declare function foo(): void; ",
            "declare namespace foo {} ",
            "export = foo;",
        ));
        let importer_file = FileId::new(5_200);
        let declaration_file = FileId::new(5_201);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                ),
            ]),
            &[declaration_file],
        );
        let binding = alias_declaration_named(&importer, importer_file, "foo");
        let import_alias = alias(&bound_files, binding);
        let target_bound = bound_files.get(&declaration_file).unwrap();
        let original = store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("foo")
            .unwrap();
        let module = source_module(&bound_files, declaration_file);
        let originating_import = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(node_ref(
                    &importer,
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        let synthetic = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(import_alias)
            .unwrap()
            .target
            .symbol()
            .unwrap();

        assert_ne!(synthetic, original);
        assert_eq!(
            store.export_type_links(synthetic),
            Some(&ExportTypeLinks {
                target: Some(original),
                originating_import: Some(originating_import),
            })
        );
        let namespace = store.symbol(synthetic).unwrap();
        assert_eq!(
            namespace.flags(),
            SymbolFlags::FUNCTION | SymbolFlags::NAMESPACE_MODULE
        );
        assert_eq!(
            namespace.declarations(),
            store.symbol(original).unwrap().declarations()
        );
        let exports = store.symbol_table(namespace.exports().unwrap()).unwrap();
        assert_eq!(exports.len(), 1);
        let default = exports.get(InternalSymbolName::Default.as_ref()).unwrap();
        assert_eq!(store.symbol(default).unwrap().parent(), Some(module));
        assert_eq!(
            store.alias_symbol_links(default),
            Some(&AliasSymbolLinks {
                immediate_target: Some(original),
                alias_target: AliasTargetState::Resolved(original),
                ..AliasSymbolLinks::default()
            })
        );
        assert!(store.symbol(original).unwrap().exports().is_none());

        let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(import_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(synthetic)
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations
        );
    }

    #[test]
    fn declaration_namespace_import_preserves_merged_ambient_const_exports() {
        let importer = parsed(r#"import * as foo from "./foo";"#);
        let declaration = parsed(concat!(
            "declare function foo(): void; ",
            "declare namespace foo { export const items: string[]; } ",
            "export = foo;",
        ));
        let importer_file = FileId::new(5_204);
        let declaration_file = FileId::new(5_205);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                ),
            ]),
            &[declaration_file],
        );
        let binding = alias_declaration_named(&importer, importer_file, "foo");
        let import_alias = alias(&bound_files, binding);
        let target_bound = bound_files.get(&declaration_file).unwrap();
        let original = store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("foo")
            .unwrap();
        let original_exports = store.symbol(original).unwrap().exports().unwrap();
        let items = store
            .symbol_table(original_exports)
            .unwrap()
            .get_source("items")
            .unwrap();
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        let synthetic = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(import_alias)
            .unwrap()
            .target
            .symbol()
            .unwrap();

        assert_ne!(synthetic, original);
        let exports = store
            .symbol(synthetic)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .unwrap();
        assert_eq!(exports.len(), 2);
        assert!(exports.get(InternalSymbolName::Default.as_ref()).is_some());
        assert_eq!(exports.get_source("items"), Some(items));
        assert_eq!(
            store
                .symbol(original)
                .and_then(ts_binder::semantic::Symbol::exports),
            Some(original_exports),
        );

        let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(import_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(synthetic),
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations,
        );
    }

    #[test]
    fn nested_ambient_namespace_import_preserves_merged_export_equals_target() {
        let importer = parsed(concat!(
            "declare module 'mymod' { ",
            "import * as foo from 'foo'; ",
            "export { foo }; ",
            "}",
        ));
        let declaration = parsed(concat!(
            "declare function foo(): void; ",
            "declare namespace foo { export const items: string[]; } ",
            "export = foo;",
        ));
        let importer_file = FileId::new(5_208);
        let declaration_file = FileId::new(5_209);
        let files = [
            (importer_file, &importer, CanonicalModuleState::Script),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                ),
            ]),
            &[importer_file, declaration_file],
        );
        let binding = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NamespaceImport).then_some(node_ref(
                    &importer,
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        let import_alias = alias(&bound_files, binding);
        let target_bound = bound_files.get(&declaration_file).unwrap();
        let original = store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("foo")
            .unwrap();
        let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(import_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(original),
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations,
        );
        assert!(store.export_type_links(original).is_none());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(import_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(original),
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations,
        );
    }

    #[test]
    fn declaration_namespace_import_rejects_forged_merged_const_ownership() {
        let importer = parsed(r#"import * as foo from "./foo";"#);
        let declaration = parsed(concat!(
            "declare function foo(): void; ",
            "declare namespace foo { export const items: string[]; } ",
            "export = foo;",
        ));
        let importer_file = FileId::new(5_206);
        let declaration_file = FileId::new(5_207);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                ),
            ]),
            &[declaration_file],
        );
        let binding = alias_declaration_named(&importer, importer_file, "foo");
        let import_alias = alias(&bound_files, binding);
        let target_bound = bound_files.get(&declaration_file).unwrap();
        let module = target_bound.symbol(target_bound.source_file()).unwrap();
        let original = store
            .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
            .unwrap()
            .get_source("foo")
            .unwrap();
        let items = store
            .symbol(original)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("items"))
            .unwrap();
        assert!(store.set_symbol_relationships(items, None, None, Some(module), None));
        let symbols = store.symbol_len();
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(import_alias)
                    .unwrap_err(),
            ),
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration: binding,
                module,
            },
        );
        assert_eq!(store.symbol_len(), symbols);
    }

    #[test]
    fn declaration_namespace_import_rejects_forged_export_equals_ownership() {
        let importer = parsed(r#"import * as foo from "./foo";"#);
        let declaration = parsed(concat!(
            "declare function foo(): void; ",
            "declare namespace foo {} ",
            "export = foo;",
        ));
        let importer_file = FileId::new(5_202);
        let declaration_file = FileId::new(5_203);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (
                declaration_file,
                &declaration,
                CanonicalModuleState::External,
            ),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(declaration_file),
                ),
            ]),
            &[declaration_file],
        );
        let binding = alias_declaration_named(&importer, importer_file, "foo");
        let import_alias = alias(&bound_files, binding);
        let module = source_module(&bound_files, declaration_file);
        let assignment = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        assert!(store.set_symbol_relationships(assignment, None, None, None, None));
        let allocations = (store.symbol_len(), store.symbol_store().symbol_table_len());
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(import_alias)
                    .unwrap_err()
            ),
            CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                declaration: binding,
                module,
            }
        );
        assert_eq!(
            (store.symbol_len(), store.symbol_store().symbol_table_len()),
            allocations
        );
        assert!(store.value_symbol_links(import_alias).is_none());
    }

    #[test]
    fn other_merged_ambient_namespace_imports_keep_their_original_target() {
        for (index, importer_text, declaration_text, imported_name) in [
            (
                0,
                r#"import * as foo from "./foo";"#,
                "declare function foo(value: number): void; declare namespace foo {} export = foo;",
                "foo",
            ),
            (
                1,
                r#"import * as foo from "./foo";"#,
                "declare function foo(): number; declare namespace foo {} export = foo;",
                "foo",
            ),
            (
                2,
                r#"import * as foo from "./foo";"#,
                concat!(
                    "declare function foo(): void; ",
                    "declare namespace foo { export interface Model {} } ",
                    "export = foo;",
                ),
                "foo",
            ),
            (
                3,
                r#"import * as renamed from "./foo";"#,
                "declare function foo(): void; declare namespace foo {} export = foo;",
                "renamed",
            ),
        ] {
            let importer = parsed(importer_text);
            let declaration = parsed(declaration_text);
            let importer_file = FileId::new(5_210 + index * 2);
            let declaration_file = FileId::new(5_211 + index * 2);
            let files = [
                (importer_file, &importer, CanonicalModuleState::External),
                (
                    declaration_file,
                    &declaration,
                    CanonicalModuleState::External,
                ),
            ];
            let specifier = module_specifiers(&importer)[0];
            let (mut store, bound_files, manifest) = fixture_with_declaration_files(
                &files,
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        node_ref(&importer, importer_file, specifier),
                        esm(declaration_file),
                    ),
                ]),
                &[declaration_file],
            );
            let binding = alias_declaration_named(&importer, importer_file, imported_name);
            let import_alias = alias(&bound_files, binding);
            let target_bound = bound_files.get(&declaration_file).unwrap();
            let original = store
                .symbol_table(target_bound.locals(target_bound.source_file()).unwrap())
                .unwrap()
                .get_source("foo")
                .unwrap();
            let mut host =
                ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                    .unwrap();

            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(import_alias)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(original)
            );
            assert!(store.export_type_links(original).is_none());
        }
    }

    #[test]
    fn javascript_esmodule_marker_preserves_the_explicit_default_alias() {
        let importer = parsed(r#"import selected from "./target.js";"#);
        let javascript = parse_javascript_source_file(concat!(
            "const value = 1; ",
            "exports.__esModule = true; ",
            "exports.default = value;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let importer_file = FileId::new(96);
        let target_file = FileId::new(97);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &javascript, CanonicalModuleState::CommonJs),
        ];
        let specifier = module_specifiers(&importer)[0];
        let (mut store, bound_files, manifest) = fixture(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
        );
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "selected"),
        );
        let exported_default = direct_export(&store, &bound_files, target_file, "default");
        let target_bound = bound_files.get(&target_file).unwrap();
        let target_locals = target_bound.locals(target_bound.source_file()).unwrap();
        let value = store
            .symbol_table(target_locals)
            .unwrap()
            .get_source("value")
            .unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(selected)
                .unwrap(),
            Some(exported_default)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(value)
        );
    }

    #[test]
    fn resolves_direct_namespace_named_and_string_named_esm_members() {
        let importer = parsed(
            r#"
                import * as ns from "./target";
                import { value as local, "sp ace" as quoted } from "./target";
                export { value as forwarded } from "./target";
            "#,
        );
        let target = parsed(
            r#"
                export const value = 1;
                const quoted = 2;
                export { quoted as "sp ace" };
            "#,
        );
        let importer_file = FileId::new(1);
        let target_file = FileId::new(2);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(target_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        let ns = alias_declaration_named(&importer, importer_file, "ns");
        let local = alias_declaration_named(&importer, importer_file, "local");
        let quoted = alias_declaration_named(&importer, importer_file, "quoted");
        let forwarded = alias_declaration_named(&importer, importer_file, "forwarded");
        let module = source_module(&bound_files, target_file);
        let value = direct_export(&store, &bound_files, target_file, "value");
        let string_named = direct_export(&store, &bound_files, target_file, "sp ace");

        for (declaration, expected) in [
            (ns, module),
            (local, value),
            (quoted, string_named),
            (forwarded, value),
        ] {
            let alias = alias(&bound_files, declaration);
            let found = CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(alias)
                .unwrap();
            assert_eq!(found, Some(expected));
        }
    }

    #[test]
    fn namespace_reexports_keep_module_identity_and_type_only_markers() {
        let exporter = parsed(
            r#"
                export * as values from "./target";
                export type * as Types from "./target";
            "#,
        );
        let target = parsed("export const value = 1; export default value;");
        let exporter_file = FileId::new(3);
        let target_file = FileId::new(4);
        let files = [
            (exporter_file, &exporter, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&exporter)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&exporter, exporter_file, specifier),
                    esm(target_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, target_file);

        for (name, type_only) in [("values", false), ("Types", true)] {
            let declaration = alias_declaration_named(&exporter, exporter_file, name);
            let namespace = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(namespace)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(module)
            );
            assert_eq!(
                store
                    .alias_symbol_links(namespace)
                    .unwrap()
                    .type_only_declaration,
                type_only.then_some(declaration)
            );
        }
    }

    #[test]
    fn local_import_equals_chains_preserve_module_identity_and_type_only_markers() {
        let importer = parsed(
            r#"
                import Required = require("./target");
                import Forwarded = Required;
                import Again = Forwarded;
                import type * as TypeNamespace from "./target";
                import TypeAlias = TypeNamespace;
            "#,
        );
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(9);
        let target_file = FileId::new(10);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let specifiers = module_specifiers(&importer);
        let entries = [
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, specifiers[0]),
                CanonicalResolvedModuleInput::new(
                    target_file,
                    CanonicalModuleResolutionMode::CommonJs,
                    CanonicalModuleResolutionMode::CommonJs,
                ),
            ),
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, specifiers[1]),
                esm(target_file),
            ),
        ];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, target_file);
        let required_declaration = alias_declaration_named(&importer, importer_file, "Required");
        let forwarded_declaration = alias_declaration_named(&importer, importer_file, "Forwarded");
        let repeated_declaration = alias_declaration_named(&importer, importer_file, "Again");
        let type_namespace_declaration =
            alias_declaration_named(&importer, importer_file, "TypeNamespace");
        let type_alias_declaration = alias_declaration_named(&importer, importer_file, "TypeAlias");
        let required = alias(&bound_files, required_declaration);
        let forwarded = alias(&bound_files, forwarded_declaration);
        let repeated = alias(&bound_files, repeated_declaration);
        let type_alias = alias(&bound_files, type_alias_declaration);

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(forwarded)
                .unwrap(),
            Some(required)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(repeated)
                .unwrap(),
            Some(forwarded)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(repeated)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(type_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module)
        );
        assert_eq!(
            store
                .alias_symbol_links(type_alias)
                .unwrap()
                .type_only_declaration,
            Some(type_namespace_declaration)
        );
    }

    #[test]
    fn qualified_local_import_equals_resolves_exported_namespace_members() {
        let source = parsed(concat!(
            "namespace Outer { export namespace Inner { export const value = 1; } } ",
            "import Selected = Outer.Inner; export {};",
        ));
        let file = FileId::new(14);
        let files = [(file, &source, CanonicalModuleState::External)];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new([]));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected_declaration = alias_declaration_named(&source, file, "Selected");
        let selected = alias(&bound_files, selected_declaration);
        let inner = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    source.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "Inner"
                )
                .then_some(node_ref(&source, file, node))
            })
            .unwrap();
        let target = bound_files.get(&file).unwrap().symbol(inner).unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(target),
        );
    }

    #[test]
    fn cold_namespace_import_equals_follows_exported_namespace_aliases() {
        let source = parsed(concat!(
            "namespace M { export namespace N {} export import X = N; } ",
            "import r = M.X;",
        ));
        let file = FileId::new(98);
        let files = [(file, &source, CanonicalModuleState::Script)];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new([]));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected = alias(&bound_files, alias_declaration_named(&source, file, "r"));
        let forwarded = alias(&bound_files, alias_declaration_named(&source, file, "X"));
        let namespace = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    source.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "N"
                )
                .then_some(node_ref(&source, file, node))
            })
            .unwrap();
        let target = bound_files.get(&file).unwrap().symbol(namespace).unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(target),
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(selected)
                .unwrap(),
            Some(forwarded),
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(forwarded)
                .unwrap(),
            Some(target),
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(target),
        );
    }

    #[test]
    fn namespace_aliases_find_private_outer_members_without_exporting_them() {
        let source = parsed(concat!(
            "namespace Outer { namespace Private {} ",
            "export namespace Nested { export import Forwarded = Private; } } ",
            "import Selected = Outer.Nested.Forwarded; ",
            "import Hidden = Outer.Private;",
        ));
        let file = FileId::new(99);
        let files = [(file, &source, CanonicalModuleState::Script)];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new([]));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let selected = alias(
            &bound_files,
            alias_declaration_named(&source, file, "Selected"),
        );
        let forwarded = alias(
            &bound_files,
            alias_declaration_named(&source, file, "Forwarded"),
        );
        let hidden_declaration = alias_declaration_named(&source, file, "Hidden");
        let hidden = alias(&bound_files, hidden_declaration);
        let namespace = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    source.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "Private"
                )
                .then_some(node_ref(&source, file, node))
            })
            .unwrap();
        let target = bound_files.get(&file).unwrap().symbol(namespace).unwrap();

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(selected)
                .unwrap()
                .target,
            AliasTargetState::Resolved(target),
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(selected)
                .unwrap(),
            Some(forwarded),
        );
        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(hidden)
                    .unwrap_err(),
            ),
            CanonicalAliasTargetUnavailable::UnsupportedLocalExport(hidden_declaration),
        );
    }

    #[test]
    fn ambient_script_modules_supply_named_and_required_alias_targets() {
        let importer = parsed(concat!(
            "import { value } from 'ambient'; ",
            "import required = require('ambient');",
        ));
        let ambient = parsed("declare module 'ambient' { export const value: number; }");
        let importer_file = FileId::new(15);
        let ambient_file = FileId::new(16);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (ambient_file, &ambient, CanonicalModuleState::Script),
        ];
        let entries = module_specifiers(&importer).into_iter().map(|specifier| {
            CanonicalModuleResolutionEntry::resolved(
                node_ref(&importer, importer_file, specifier),
                CanonicalResolvedModuleInput::new(
                    ambient_file,
                    CanonicalModuleResolutionMode::CommonJs,
                    CanonicalModuleResolutionMode::CommonJs,
                ),
            )
        });
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let declaration = ambient
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(node_ref(
                    &ambient,
                    ambient_file,
                    node,
                ))
            })
            .unwrap();
        let module = bound_files
            .get(&ambient_file)
            .unwrap()
            .symbol(declaration)
            .unwrap();
        let value = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("value"))
            .unwrap();

        for (name, expected) in [("value", value), ("required", module)] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let alias = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(expected),
            );
        }
    }

    #[test]
    fn ambient_export_equals_namespace_supplies_named_import_targets() {
        let declarations = parsed(concat!(
            "declare module 'react' { ",
            "namespace React { export interface Model {} } ",
            "interface React {} ",
            "export = React; ",
            "} ",
            "declare module 'consumer' { ",
            "import { Model as Selected } from 'react'; ",
            "import type { Model as TypeOnly } from 'react'; ",
            "}",
        ));
        let file = FileId::new(114);
        let files = [(file, &declarations, CanonicalModuleState::Script)];
        let entries = module_specifiers(&declarations)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&declarations, file, specifier),
                    CanonicalResolvedModuleInput::new(
                        file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                )
            });
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new(entries),
            &[file],
        );
        let bound = bound_files.get(&file).unwrap();
        let module_declaration = declarations
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    declarations.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::StringLiteral(name)) if name.text == "react"
                )
                .then_some(node_ref(&declarations, file, node))
            })
            .unwrap();
        let module = bound.symbol(module_declaration).unwrap();
        let module_exports = store.symbol(module).unwrap().exports().unwrap();
        let assignment = store
            .symbol_table(module_exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let namespace_declaration = declarations
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    declarations.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "React"
                )
                .then_some(node_ref(&declarations, file, node))
            })
            .unwrap();
        let namespace = bound
            .symbol(namespace_declaration)
            .and_then(|namespace| store.get_merged_symbol(namespace))
            .unwrap();
        assert_eq!(
            store.get_parent_of_symbol(namespace),
            None,
            "the export-assignment target remains a module-local namespace",
        );
        let namespace_exports = store.symbol(namespace).unwrap().exports().unwrap();
        let model = store
            .symbol_table(namespace_exports)
            .unwrap()
            .get_source("Model")
            .unwrap();
        assert!(
            store
                .symbol(namespace)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE)
        );
        assert_eq!(store.get_parent_of_symbol(model), Some(namespace));
        let assignment_links = store.alias_symbol_links(assignment).cloned();
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        for (name, type_only) in [("Selected", false), ("TypeOnly", true)] {
            let declaration = alias_declaration_named(&declarations, file, name);
            let imported = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(imported)
                    .unwrap(),
                Some(model)
            );
            for _ in 0..2 {
                let resolution = CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(imported)
                    .unwrap();
                assert_eq!(resolution.target, AliasTargetState::Resolved(model));
                assert!(resolution.events.is_empty());
                assert_eq!(
                    store.alias_symbol_links(imported).unwrap(),
                    &AliasSymbolLinks {
                        immediate_target: Some(model),
                        alias_target: AliasTargetState::Resolved(model),
                        type_only_declaration: type_only.then_some(declaration),
                        ..AliasSymbolLinks::default()
                    }
                );
            }
        }
        assert_eq!(
            store.alias_symbol_links(assignment).cloned(),
            assignment_links
        );
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn ambient_export_equals_named_imports_reject_missing_or_forged_members() {
        let declarations = parsed(concat!(
            "declare module 'react' { ",
            "namespace React { export interface Model {} } ",
            "export = React; ",
            "} ",
            "declare module 'consumer' { ",
            "import { Model as Selected, Missing as Absent } from 'react'; ",
            "}",
        ));
        let file = FileId::new(115);
        let files = [(file, &declarations, CanonicalModuleState::Script)];
        let specifier = module_specifiers(&declarations)[0];
        let (mut store, bound_files, manifest) = fixture_with_declaration_files(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&declarations, file, specifier),
                    CanonicalResolvedModuleInput::new(
                        file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::CommonJs,
                    ),
                ),
            ]),
            &[file],
        );
        let module_declaration = declarations
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    declarations.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::StringLiteral(name)) if name.text == "react"
                )
                .then_some(node_ref(&declarations, file, node))
            })
            .unwrap();
        let module = bound_files
            .get(&file)
            .unwrap()
            .symbol(module_declaration)
            .unwrap();
        let module_exports = store.symbol(module).unwrap().exports().unwrap();
        let namespace_declaration = declarations
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    declarations.arena.get(module.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "React"
                )
                .then_some(node_ref(&declarations, file, node))
            })
            .unwrap();
        let namespace = bound_files
            .get(&file)
            .unwrap()
            .symbol(namespace_declaration)
            .and_then(|namespace| store.get_merged_symbol(namespace))
            .unwrap();
        let namespace_exports = store.symbol(namespace).unwrap().exports().unwrap();
        let model = store
            .symbol_table(namespace_exports)
            .unwrap()
            .get_source("Model")
            .unwrap();
        let assignment = store
            .symbol_table(module_exports)
            .unwrap()
            .get(InternalSymbolName::ExportEquals.as_ref())
            .unwrap();
        let selected_declaration = alias_declaration_named(&declarations, file, "Selected");
        let selected = alias(&bound_files, selected_declaration);
        let absent_declaration = alias_declaration_named(&declarations, file, "Absent");
        let absent = alias(&bound_files, absent_declaration);
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        for _ in 0..2 {
            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(absent)
                        .unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::MissingExport {
                    declaration: absent_declaration,
                    module,
                }
            );
            assert_eq!(
                store.alias_symbol_links(absent),
                Some(&AliasSymbolLinks::default())
            );
        }

        assert_eq!(
            store.insert_symbol(namespace_exports, EscapedName::source("Model"), module),
            Some(Some(model))
        );
        for _ in 0..2 {
            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(selected)
                        .unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration: selected_declaration,
                    module,
                }
            );
            assert_eq!(
                store.alias_symbol_links(selected),
                Some(&AliasSymbolLinks::default())
            );
        }
        assert_eq!(
            store.insert_symbol(namespace_exports, EscapedName::source("Model"), model),
            Some(Some(module))
        );

        let assignment_record = store.symbol(assignment).unwrap();
        let relationships = (
            assignment_record.members(),
            assignment_record.exports(),
            assignment_record.export_symbol(),
        );
        assert!(store.set_symbol_relationships(
            assignment,
            relationships.0,
            relationships.1,
            Some(namespace),
            relationships.2,
        ));
        for _ in 0..2 {
            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(selected)
                        .unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration: selected_declaration,
                    module,
                }
            );
            assert_eq!(
                store.alias_symbol_links(selected),
                Some(&AliasSymbolLinks::default())
            );
        }
        assert!(store.set_symbol_relationships(
            assignment,
            relationships.0,
            relationships.1,
            Some(module),
            relationships.2,
        ));
        let resolution = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(selected)
            .unwrap();
        assert_eq!(resolution.target, AliasTargetState::Resolved(model));
        assert!(resolution.events.is_empty());
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn require_and_type_only_imports_can_resolve_an_esm_target() {
        let importer = parsed(
            r#"
                import Required = require("./target");
                import type { Model as TypeOnlyModel } from "./target";
                import { Model as ValueModel } from "./target";
            "#,
        );
        let target = parsed("export interface Model { value: number }");
        let importer_file = FileId::new(12);
        let target_file = FileId::new(13);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::CommonJs,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, target_file);
        let model = direct_export(&store, &bound_files, target_file, "Model");

        let require_declaration = alias_declaration_named(&importer, importer_file, "Required");
        let require_alias = alias(&bound_files, require_declaration);
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(require_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module)
        );

        let type_declaration = alias_declaration_named(&importer, importer_file, "TypeOnlyModel");
        let type_alias = alias(&bound_files, type_declaration);
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(type_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(model)
        );
        assert_eq!(
            store
                .alias_symbol_links(type_alias)
                .unwrap()
                .type_only_declaration,
            Some(type_declaration)
        );

        let value_declaration = alias_declaration_named(&importer, importer_file, "ValueModel");
        let value_alias = alias(&bound_files, value_declaration);
        assert_eq!(
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(value_alias)
                    .unwrap_err()
            ),
            CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration: value_declaration,
                file: target_file,
            }
        );
    }

    #[test]
    fn namespace_imports_preserve_module_identity_across_authenticated_module_modes() {
        for (index, usage_mode, target_mode, declaration_file) in [
            (
                0,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::CommonJs,
                false,
            ),
            (
                1,
                CanonicalModuleResolutionMode::CommonJs,
                CanonicalModuleResolutionMode::Esm,
                false,
            ),
            (
                2,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::CommonJs,
                true,
            ),
            (
                3,
                CanonicalModuleResolutionMode::CommonJs,
                CanonicalModuleResolutionMode::Esm,
                true,
            ),
        ] {
            let importer = parsed(r#"import * as values from "./target";"#);
            let target = if declaration_file {
                parsed("export declare const value: number;")
            } else {
                parsed("export const value: number = 1;")
            };
            let importer_file = FileId::new(5_220 + index * 2);
            let target_file = FileId::new(5_221 + index * 2);
            let files = [
                (importer_file, &importer, CanonicalModuleState::External),
                (target_file, &target, CanonicalModuleState::External),
            ];
            let specifier = module_specifiers(&importer)[0];
            let declaration_files = if declaration_file {
                vec![target_file]
            } else {
                Vec::new()
            };
            let (mut store, bound_files, manifest) = fixture_with_declaration_files(
                &files,
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        node_ref(&importer, importer_file, specifier),
                        CanonicalResolvedModuleInput::new(target_file, usage_mode, target_mode),
                    ),
                ]),
                &declaration_files,
            );
            let mut host =
                ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                    .unwrap();
            let declaration = alias_declaration_named(&importer, importer_file, "values");
            let namespace = alias(&bound_files, declaration);
            let module = source_module(&bound_files, target_file);
            let symbols = (store.symbol_len(), store.symbol_store().symbol_table_len());

            let resolved = CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(namespace)
                .unwrap();

            assert_eq!(resolved.target, AliasTargetState::Resolved(module));
            assert!(resolved.events.is_empty());
            assert_eq!(
                store.alias_symbol_links(namespace),
                Some(&AliasSymbolLinks {
                    alias_target: AliasTargetState::Resolved(module),
                    ..AliasSymbolLinks::default()
                }),
            );
            assert_eq!(
                (store.symbol_len(), store.symbol_store().symbol_table_len()),
                symbols,
            );
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(namespace)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(module),
            );
            assert_eq!(
                store
                    .alias_symbol_links(namespace)
                    .and_then(|links| links.immediate_target),
                None,
            );
            assert_eq!(
                (store.symbol_len(), store.symbol_store().symbol_table_len()),
                symbols,
            );
        }
    }

    #[test]
    fn circular_local_import_equals_aliases_keep_canonical_cycle_events() {
        let source = parsed("import First = Second; import Second = First; export {};");
        let file = FileId::new(11);
        let files = [(file, &source, CanonicalModuleState::External)];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new([]));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let first = alias(
            &bound_files,
            alias_declaration_named(&source, file, "First"),
        );
        let second = alias(
            &bound_files,
            alias_declaration_named(&source, file, "Second"),
        );

        let resolution = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(first)
            .unwrap();
        assert_eq!(resolution.target, AliasTargetState::Unknown);
        assert!(!resolution.events.is_empty());
        assert!(
            resolution
                .events
                .iter()
                .all(|event| event.diagnostic_code() == 2303)
        );
        assert_eq!(
            store.alias_symbol_links(first).unwrap().alias_target,
            AliasTargetState::Unknown
        );
        assert_eq!(
            store.alias_symbol_links(second).unwrap().alias_target,
            AliasTargetState::Unknown
        );
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn explicit_default_imports_and_reexports_use_the_direct_default_symbol() {
        let importer = parsed(
            r#"
                import DefaultValue from "./target";
                import { default as namedDefault } from "./target";
                export { default as forwardedDefault } from "./target";
                export { default } from "./target";
            "#,
        );
        let target =
            parsed("export default function value(input: number): number { return input; }");
        let importer_file = FileId::new(5);
        let target_file = FileId::new(6);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(target_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let default = direct_export(&store, &bound_files, target_file, "default");

        for name in [
            "DefaultValue",
            "namedDefault",
            "forwardedDefault",
            "default",
        ] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let alias = alias(&bound_files, declaration);
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .get_immediate_aliased_symbol(alias)
                    .unwrap(),
                Some(default),
                "default alias {name} must retain the direct export symbol"
            );
            assert_eq!(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias)
                    .unwrap()
                    .target,
                AliasTargetState::Resolved(default)
            );
        }
    }

    #[test]
    fn export_star_never_supplies_a_missing_default_export() {
        let importer = parsed(
            r#"
                import DefaultValue from "./star";
                import { default as namedDefault } from "./star";
                export { default as forwardedDefault } from "./star";
            "#,
        );
        let star = parsed("export * from './target';");
        let importer_file = FileId::new(7);
        let star_file = FileId::new(8);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (star_file, &star, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(star_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let module = source_module(&bound_files, star_file);

        for name in ["DefaultValue", "namedDefault", "forwardedDefault"] {
            let declaration = alias_declaration_named(&importer, importer_file, name);
            let alias = alias(&bound_files, declaration);
            assert_eq!(
                unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(alias)
                        .unwrap_err()
                ),
                CanonicalAliasTargetUnavailable::MissingExport {
                    declaration,
                    module,
                }
            );
            assert_eq!(
                store.alias_symbol_links(alias),
                Some(&AliasSymbolLinks::default())
            );
        }
    }

    #[test]
    fn namespace_import_retains_modules_with_default_and_named_exports() {
        let importer = parsed(
            r#"
                import * as ns from "./target";
                import { value as local } from "./target";
            "#,
        );
        let target = parsed(
            r"
                export default 0;
                export const value = 1;
            ",
        );
        let importer_file = FileId::new(3);
        let target_file = FileId::new(4);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(target_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let namespace_declaration = alias_declaration_named(&importer, importer_file, "ns");
        let named_declaration = alias_declaration_named(&importer, importer_file, "local");
        let namespace_alias = alias(&bound_files, namespace_declaration);
        let named_alias = alias(&bound_files, named_declaration);
        let module = source_module(&bound_files, target_file);
        let value = direct_export(&store, &bound_files, target_file, "value");
        assert!(
            store
                .symbol_table(store.symbol(module).unwrap().exports().unwrap())
                .unwrap()
                .get(InternalSymbolName::Default.as_ref())
                .is_some()
        );

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(namespace_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(module),
        );
        assert!(store.type_resolution_is_empty());
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(named_alias)
                .unwrap(),
            Some(value)
        );
    }

    #[test]
    fn resolves_live_reexport_chain_and_propagates_only_syntactic_type_markers() {
        let base = parsed("export interface Value { field: string }");
        let middle = parsed("export type { Value as Mid } from './base';");
        let consumer = parsed(
            r#"
                import { Mid as Local } from "./middle";
                import type * as Types from "./base";
            "#,
        );
        let base_file = FileId::new(10);
        let middle_file = FileId::new(11);
        let consumer_file = FileId::new(12);
        let files = [
            (base_file, &base, CanonicalModuleState::External),
            (middle_file, &middle, CanonicalModuleState::External),
            (consumer_file, &consumer, CanonicalModuleState::External),
        ];
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
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let middle_declaration = alias_declaration_named(&middle, middle_file, "Mid");
        let local_declaration = alias_declaration_named(&consumer, consumer_file, "Local");
        let namespace_declaration = alias_declaration_named(&consumer, consumer_file, "Types");
        let middle_alias = alias(&bound_files, middle_declaration);
        let local_alias = alias(&bound_files, local_declaration);
        let namespace_alias = alias(&bound_files, namespace_declaration);
        let value = direct_export(&store, &bound_files, base_file, "Value");

        let resolution = CanonicalAliasResolver::new(&mut store, &mut host)
            .resolve_alias(local_alias)
            .unwrap();
        assert_eq!(resolution.target, AliasTargetState::Resolved(value));
        assert_eq!(
            store
                .alias_symbol_links(middle_alias)
                .unwrap()
                .type_only_declaration,
            Some(middle_declaration)
        );
        assert_eq!(
            store
                .alias_symbol_links(local_alias)
                .unwrap()
                .type_only_declaration,
            Some(middle_declaration),
            "transitive propagation remains owned by the alias kernel"
        );

        let namespace = CanonicalAliasResolver::new(&mut store, &mut host)
            .get_immediate_aliased_symbol(namespace_alias)
            .unwrap();
        assert_eq!(namespace, Some(source_module(&bound_files, base_file)));
        assert_eq!(
            store
                .alias_symbol_links(namespace_alias)
                .unwrap()
                .type_only_declaration,
            Some(namespace_declaration)
        );
    }

    #[test]
    fn distinguishes_all_manifest_states_without_caching_unavailability() {
        let importer = parsed(
            r#"
                import { value as unavailable } from "./target";
                import { value as absent } from "./target";
                import { value as unresolved } from "./target";
                import { value as resolved } from "./target";
            "#,
        );
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(20);
        let target_file = FileId::new(21);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let specifiers = module_specifiers(&importer)
            .into_iter()
            .map(|node| node_ref(&importer, importer_file, node))
            .collect::<Vec<_>>();
        let entries = [
            CanonicalModuleResolutionEntry::unresolved(specifiers[2]),
            CanonicalModuleResolutionEntry::resolved(specifiers[3], esm(target_file)),
        ];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let unavailable_manifest = CanonicalModuleResolutionManifest::unavailable();
        let declarations = ["unavailable", "absent", "unresolved", "resolved"]
            .map(|name| alias_declaration_named(&importer, importer_file, name));
        let aliases = declarations.map(|declaration| alias(&bound_files, declaration));

        let mut unavailable_host = ProductionAliasTargetHost::new(
            &store,
            sources(&files, &bound_files),
            &unavailable_manifest,
        )
        .unwrap();
        let reason = unavailable_reason(
            CanonicalAliasResolver::new(&mut store, &mut unavailable_host)
                .resolve_alias(aliases[0])
                .unwrap_err(),
        );
        assert_eq!(
            reason,
            CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(specifiers[0])
        );

        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        for (alias, expected) in [
            (
                aliases[1],
                CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(specifiers[1]),
            ),
            (
                aliases[2],
                CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(specifiers[2]),
            ),
        ] {
            for _ in 0..2 {
                let reason = unavailable_reason(
                    CanonicalAliasResolver::new(&mut store, &mut host)
                        .resolve_alias(alias)
                        .unwrap_err(),
                );
                assert_eq!(reason, expected);
                let links = store.alias_symbol_links(alias).unwrap();
                assert_eq!(links.immediate_target, None);
                assert_eq!(links.alias_target, AliasTargetState::Unresolved);
            }
        }
        let value = direct_export(&store, &bound_files, target_file, "value");
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(aliases[3])
                .unwrap()
                .target,
            AliasTargetState::Resolved(value)
        );
    }

    #[test]
    fn syntactic_type_only_markers_publish_before_unresolved_and_missing_targets() {
        let importer = parsed(
            r#"
                import type * as UnresolvedTypes from "./target";
                import { type MissingImport } from "./target";
                export type { MissingExport } from "./target";
            "#,
        );
        let target = parsed("export const present = 1;");
        let importer_file = FileId::new(22);
        let target_file = FileId::new(23);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let specifiers = module_specifiers(&importer)
            .into_iter()
            .map(|node| node_ref(&importer, importer_file, node))
            .collect::<Vec<_>>();
        let entries = [
            CanonicalModuleResolutionEntry::unresolved(specifiers[0]),
            CanonicalModuleResolutionEntry::resolved(specifiers[1], esm(target_file)),
            CanonicalModuleResolutionEntry::resolved(specifiers[2], esm(target_file)),
        ];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let declarations = ["UnresolvedTypes", "MissingImport", "MissingExport"]
            .map(|name| alias_declaration_named(&importer, importer_file, name));
        let aliases = declarations.map(|declaration| alias(&bound_files, declaration));
        let module = source_module(&bound_files, target_file);
        let expected = [
            CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(specifiers[0]),
            CanonicalAliasTargetUnavailable::MissingExport {
                declaration: declarations[1],
                module,
            },
            CanonicalAliasTargetUnavailable::MissingExport {
                declaration: declarations[2],
                module,
            },
        ];

        for ((alias, declaration), expected) in aliases.into_iter().zip(declarations).zip(expected)
        {
            for _ in 0..2 {
                assert_eq!(
                    unavailable_reason(
                        CanonicalAliasResolver::new(&mut store, &mut host)
                            .resolve_alias(alias)
                            .unwrap_err()
                    ),
                    expected
                );
                let links = store.alias_symbol_links(alias).unwrap();
                assert_eq!(links.immediate_target, None);
                assert_eq!(links.alias_target, AliasTargetState::Unresolved);
                assert_eq!(links.type_only_declaration, Some(declaration));
                assert!(store.type_resolution_is_empty());
            }
        }
    }

    #[test]
    fn resolves_local_exports_and_rejects_unsupported_module_paths() {
        let importer = parsed(
            r#"
                import DefaultThing from "./plain";
                const value = 1;
                export { value };
                import { missing } from "./star";
                import { value as legacy } from "./equals";
                import { value as cjs } from "./plain";
                import { value as synthetic } from "./plain";
            "#,
        );
        let plain = parsed("export const value = 1;");
        let star = parsed("export * from './deep';");
        let equals = parsed("const value = 1; export = value;");
        let importer_file = FileId::new(30);
        let plain_file = FileId::new(31);
        let star_file = FileId::new(32);
        let equals_file = FileId::new(33);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (plain_file, &plain, CanonicalModuleState::External),
            (star_file, &star, CanonicalModuleState::External),
            (equals_file, &equals, CanonicalModuleState::External),
        ];
        let specifiers = module_specifiers(&importer)
            .into_iter()
            .map(|node| node_ref(&importer, importer_file, node))
            .collect::<Vec<_>>();
        let entries = [
            CanonicalModuleResolutionEntry::resolved(specifiers[0], esm(plain_file)),
            CanonicalModuleResolutionEntry::resolved(specifiers[1], esm(star_file)),
            CanonicalModuleResolutionEntry::resolved(specifiers[2], esm(equals_file)),
            CanonicalModuleResolutionEntry::resolved(
                specifiers[3],
                CanonicalResolvedModuleInput::new(
                    plain_file,
                    CanonicalModuleResolutionMode::CommonJs,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ),
            CanonicalModuleResolutionEntry::resolved(
                specifiers[4],
                CanonicalResolvedModuleInput::new(
                    plain_file,
                    CanonicalModuleResolutionMode::None,
                    CanonicalModuleResolutionMode::None,
                ),
            ),
        ];
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let local_declaration = alias_declaration_named(&importer, importer_file, "value");
        let local_alias = alias(&bound_files, local_declaration);
        let importer_bound = bound_files.get(&importer_file).unwrap();
        let locals = importer_bound.locals(importer_bound.source_file()).unwrap();
        let local_target = store
            .symbol_table(locals)
            .unwrap()
            .get_source("value")
            .unwrap();
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(local_alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(local_target)
        );

        let declarations = ["DefaultThing", "missing", "legacy", "cjs", "synthetic"]
            .map(|name| alias_declaration_named(&importer, importer_file, name));
        let aliases = declarations.map(|declaration| alias(&bound_files, declaration));

        let expected = [
            CanonicalAliasTargetUnavailable::MissingExport {
                declaration: declarations[0],
                module: source_module(&bound_files, plain_file),
            },
            CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported {
                declaration: declarations[1],
                module: source_module(&bound_files, star_file),
            },
            CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported {
                declaration: declarations[2],
                module: source_module(&bound_files, equals_file),
            },
            CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration: declarations[3],
                file: plain_file,
            },
            CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                declaration: declarations[4],
                module: source_module(&bound_files, plain_file),
            },
        ];
        for (alias, expected) in aliases.into_iter().zip(expected) {
            let reason = unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias)
                    .unwrap_err(),
            );
            assert_eq!(reason, expected);
            let links = store.alias_symbol_links(alias).unwrap();
            assert_eq!(links.alias_target, AliasTargetState::Unresolved);
            assert_eq!(links.type_only_declaration, None);
        }
    }

    #[test]
    fn follows_exactly_one_module_merge_redirect_and_keeps_member_aliases_immediate() {
        let importer = parsed(
            r#"
                import * as ns from "./target";
                import { value as local } from "./target";
            "#,
        );
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(40);
        let target_file = FileId::new(41);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let entries = module_specifiers(&importer)
            .into_iter()
            .map(|specifier| {
                CanonicalModuleResolutionEntry::resolved(
                    node_ref(&importer, importer_file, specifier),
                    esm(target_file),
                )
            })
            .collect::<Vec<_>>();
        let (mut store, bound_files, manifest) =
            fixture(&files, CanonicalModuleResolutionManifestInput::new(entries));
        let raw_module = source_module(&bound_files, target_file);
        let raw_record = store.symbol(raw_module).unwrap();
        let exports = raw_record.exports();
        let source = bound_files.get(&target_file).unwrap().source_file();

        let mut merged_data =
            SymbolData::new(SymbolFlags::VALUE_MODULE, EscapedName::source("merged"));
        merged_data.declarations = Some(vec![source]);
        merged_data.exports = exports;
        let merged = store.alloc_symbol(merged_data).unwrap();
        let mut final_data =
            SymbolData::new(SymbolFlags::VALUE_MODULE, EscapedName::source("final"));
        final_data.declarations = Some(vec![source]);
        final_data.exports = exports;
        let final_module = store.alloc_symbol(final_data).unwrap();
        assert!(store.record_merged_symbol(merged, raw_module).is_ok());
        assert!(store.record_merged_symbol(final_module, merged).is_ok());

        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();
        let namespace = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "ns"),
        );
        let local = alias(
            &bound_files,
            alias_declaration_named(&importer, importer_file, "local"),
        );
        let value = direct_export(&store, &bound_files, target_file, "value");
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(namespace)
                .unwrap(),
            Some(merged),
            "the upstream consumer performs one map lookup, not a redirect walk"
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(local)
                .unwrap(),
            Some(value),
            "a direct export entry remains an immediate unresolved alias symbol"
        );
    }

    #[test]
    fn find_last_ownership_missing_export_retry_and_foreign_failures_are_atomic() {
        let importer =
            parsed("import DefaultThing, { wanted } from './target'; const unrelated = 0;");
        let target = parsed("export const present = 1;");
        let importer_file = FileId::new(50);
        let target_file = FileId::new(51);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let specifier = node_ref(&importer, importer_file, module_specifiers(&importer)[0]);
        let (mut store, bound_files, manifest) = fixture(
            &files,
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(specifier, esm(target_file)),
            ]),
        );
        let declaration = alias_declaration_named(&importer, importer_file, "wanted");
        let alias = alias(&bound_files, declaration);
        let unrelated = importer
            .arena
            .iter()
            .find_map(|(node, data)| {
                (data.kind == SyntaxKind::VariableDeclaration).then_some(node_ref(
                    &importer,
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        assert!(store.set_symbol_declarations(alias, Some(vec![declaration, unrelated]), None));
        let mut host =
            ProductionAliasTargetHost::new(&store, sources(&files, &bound_files), &manifest)
                .unwrap();

        for _ in 0..2 {
            let reason = unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(alias)
                    .unwrap_err(),
            );
            assert_eq!(
                reason,
                CanonicalAliasTargetUnavailable::MissingExport {
                    declaration,
                    module: source_module(&bound_files, target_file),
                }
            );
            assert_eq!(
                store.alias_symbol_links(alias),
                Some(&AliasSymbolLinks::default())
            );
        }

        let wanted = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("wanted"),
            ))
            .unwrap();
        let module = source_module(&bound_files, target_file);
        let exports = store.symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            store.insert_symbol(exports, EscapedName::source("wanted"), wanted),
            Some(None)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(alias)
                .unwrap()
                .target,
            AliasTargetState::Resolved(wanted)
        );

        assert!(store.set_alias_symbol_links(alias, AliasSymbolLinks::default()));
        let default_declaration = alias_declaration_named(&importer, importer_file, "DefaultThing");
        assert!(store.set_symbol_declarations(
            alias,
            Some(vec![declaration, default_declaration]),
            None,
        ));
        let reason = unavailable_reason(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(alias)
                .unwrap_err(),
        );
        assert_eq!(
            reason,
            CanonicalAliasTargetUnavailable::AliasDeclarationOwnerMismatch {
                alias,
                declaration: default_declaration,
            }
        );
        assert_eq!(
            store.alias_symbol_links(alias),
            Some(&AliasSymbolLinks::default())
        );

        let namespace = parsed("import * as other from './target';");
        let foreign_file = FileId::new(52);
        assert!(
            store
                .register_source_file(&namespace.arena, namespace.source_file, foreign_file)
                .is_some()
        );
        let foreign = node_ref(&namespace, foreign_file, namespace.source_file);
        assert!(store.set_symbol_declarations(alias, Some(vec![declaration, foreign]), None));
        let reason = unavailable_reason(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(alias)
                .unwrap_err(),
        );
        assert_eq!(
            reason,
            CanonicalAliasTargetUnavailable::ForeignDeclaration(foreign)
        );
        assert_eq!(
            store.alias_symbol_links(alias),
            Some(&AliasSymbolLinks::default())
        );

        let mut foreign_store = TestStore::from_symbol_store(ts_binder::SymbolStore::new());
        let reason = host
            .get_target_of_alias_declaration(&mut foreign_store, alias)
            .unwrap_err();
        assert!(matches!(
            reason,
            CanonicalAliasTargetUnavailable::ForeignStore { expected, actual }
                if expected == store.id() && actual == foreign_store.id()
        ));
    }

    #[test]
    fn registry_rejects_a_source_registration_from_another_retained_file() {
        let first = parsed("export const first = 1;");
        let second = parsed("export const second = 2;");
        let first_file = FileId::new(56);
        let second_file = FileId::new(57);
        let files = [
            (first_file, &first, CanonicalModuleState::External),
            (second_file, &second, CanonicalModuleState::External),
        ];
        let (symbols, mut bound_files) = bindings(&files);
        let mut store = TestStore::from_symbol_store(symbols);
        let first_source = store
            .register_source_file(&first.arena, first.source_file, first_file)
            .unwrap();
        let second_source = store
            .register_source_file(&second.arena, second.source_file, second_file)
            .unwrap();
        let expected = bound_files.get(&first_file).unwrap().source_file();

        let error = ProductionAliasSourceRegistry::new(
            &store,
            [
                (
                    &first.arena,
                    bound_files.remove(&first_file).unwrap(),
                    second_source,
                ),
                (
                    &second.arena,
                    bound_files.remove(&second_file).unwrap(),
                    first_source,
                ),
            ],
        )
        .unwrap_err();
        assert_eq!(
            error,
            ProductionAliasTargetHostError::InvalidRegisteredSourceFile {
                file: first_file,
                expected,
                actual: second_source,
            }
        );
    }

    #[test]
    fn registry_rejects_a_same_root_source_token_from_another_store() {
        let source = parsed("export const value = 1;");
        let file = FileId::new(62);
        let files = [(file, &source, CanonicalModuleState::External)];
        let (symbols, mut bound_files) = bindings(&files);
        let mut store = TestStore::from_symbol_store(symbols);
        let local_source = store
            .register_source_file(&source.arena, source.source_file, file)
            .unwrap();
        let mut other_store = TestStore::new();
        let foreign_source = other_store
            .register_source_file(&source.arena, source.source_file, file)
            .unwrap();
        let expected = bound_files.get(&file).unwrap().source_file();

        assert_eq!(local_source.node_ref(), foreign_source.node_ref());
        assert_ne!(local_source, foreign_source);
        let error = ProductionAliasSourceRegistry::new(
            &store,
            [(
                &source.arena,
                bound_files.remove(&file).unwrap(),
                foreign_source,
            )],
        )
        .unwrap_err();
        assert_eq!(
            error,
            ProductionAliasTargetHostError::InvalidRegisteredSourceFile {
                file,
                expected,
                actual: foreign_source,
            }
        );
    }

    #[test]
    fn registry_validates_once_and_query_hosts_borrow_its_owned_sources() {
        let importer = parsed("import { value } from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(58);
        let target_file = FileId::new(59);
        let files = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let (symbols, mut bound_files) = bindings(&files);
        let mut store = TestStore::from_symbol_store(symbols);
        let mut retained = Vec::new();
        for &(file, parsed, _) in &files {
            let source_file = store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
            retained.push((
                &parsed.arena,
                bound_files.remove(&file).unwrap(),
                source_file,
            ));
        }
        let registry = ProductionAliasSourceRegistry::new(&store, retained).unwrap();
        assert!(bound_files.is_empty());
        assert_eq!(registry.snapshots().count(), files.len());

        let unavailable = CanonicalModuleResolutionManifest::unavailable();
        let host =
            ProductionAliasTargetHost::from_registry(&store, &registry, &unavailable).unwrap();
        assert!(matches!(
            host.sources,
            ProductionAliasTargetSources::Registry(_)
        ));
    }

    #[test]
    fn registry_rejects_stale_sources_before_retaining_program_state() {
        let mut importer = parsed("import { value } from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(60);
        let target_file = FileId::new(61);
        let files_before_mutation = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let (symbols, mut bound_files) = bindings(&files_before_mutation);
        importer.arena.set_source_text("stale");
        let mut store = TestStore::from_symbol_store(symbols);
        let importer_source = store
            .register_source_file(&importer.arena, importer.source_file, importer_file)
            .unwrap();
        let target_source = store
            .register_source_file(&target.arena, target.source_file, target_file)
            .unwrap();
        let error = ProductionAliasSourceRegistry::new(
            &store,
            [
                (
                    &importer.arena,
                    bound_files.remove(&importer_file).unwrap(),
                    importer_source,
                ),
                (
                    &target.arena,
                    bound_files.remove(&target_file).unwrap(),
                    target_source,
                ),
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            ProductionAliasTargetHostError::ArenaRevisionMismatch { file, .. }
                if file == importer_file
        ));
    }
}
