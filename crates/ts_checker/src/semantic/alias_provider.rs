//! Production syntax and module-resolution host for canonical alias targets.
//!
//! This host accepts TypeScript namespace imports, explicit default imports,
//! named imports, named exports, and external import-equals declarations. ESM
//! and `CommonJS` emit modes retain the same direct module symbols when both
//! sides agree. Alias recursion and type-only propagation belong to the
//! canonical alias kernel.

use std::collections::BTreeMap;

#[cfg(test)]
use std::cell::Cell;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{BoundFile, InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalModuleResolutionLookup, CanonicalModuleResolutionManifest,
    CanonicalModuleResolutionMode, CanonicalResolvedModule, CanonicalSemanticStore, SourceFileRef,
    alias::{
        CanonicalAliasTargetHost, CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
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
                    Some(NodeData::Identifier(_)) => {
                        let target = Self::local_module_member(
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
        Ok(target)
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
            .is_some_and(|operator| operator.kind == SyntaxKind::EqualsToken)
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        }
        let Some(name) = commonjs_assignment_export_name(source.arena, assignment.left) else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration));
        };
        let module = source.bound.symbol(source.bound.source_file()).ok_or(
            CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
        )?;
        let exports = store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
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
        if actual != Some(alias)
            || !store
                .symbol(alias)
                .is_some_and(|record| record.flags().intersects(SymbolFlags::ALIAS))
        {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                declaration,
            ));
        }
        Self::alias_expression_target(store, source, declaration, assignment.right)
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
        if !store.contains_node_ref(source)
            || target.bound.symbol(source) != Some(resolved.target_symbol())
        {
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

        if facts.is_declaration_file() {
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
            return Ok(export_equals.is_some()
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
            let exports = store.symbol_table(exports).ok_or(
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                },
            )?;
            if exports.get(InternalSymbolName::Default.as_ref()).is_some() {
                return Err(
                    CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                        declaration,
                        module,
                    },
                );
            }
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
            SupportedAliasDeclaration::ExternalImportEquals { .. }
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
        if export_equals.is_some() {
            let supported_export_equals = match &supported {
                SupportedAliasDeclaration::ExternalImportEquals { .. } => true,
                SupportedAliasDeclaration::NamespaceImport { .. } if declaration_target => true,
                SupportedAliasDeclaration::DefaultModuleMember { .. } => synthetic_default,
                SupportedAliasDeclaration::NamedModuleMember { name, .. }
                    if commonjs_javascript_target =>
                {
                    Self::direct_export(store, declaration, module, name).is_ok()
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
            SupportedAliasDeclaration::NamespaceImport { .. }
                if declaration_target && export_equals.is_some() =>
            {
                export_equals.expect("declaration namespace export-equals was preflighted")
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
        AliasSymbolLinks, AliasTargetState,
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
        let importer = parsed(r#"import required = require("./target.js");"#);
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

        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .get_immediate_aliased_symbol(required)
                .unwrap(),
            Some(assignment)
        );
        assert_eq!(
            CanonicalAliasResolver::new(&mut store, &mut host)
                .resolve_alias(required)
                .unwrap()
                .target,
            AliasTargetState::Resolved(local)
        );
        assert_eq!(
            store.alias_symbol_links(assignment).unwrap().alias_target,
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
    fn namespace_import_rejects_default_export_wrapper_while_named_member_stays_direct() {
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
            unavailable_reason(
                CanonicalAliasResolver::new(&mut store, &mut host)
                    .resolve_alias(namespace_alias)
                    .unwrap_err()
            ),
            CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                declaration: namespace_declaration,
                module,
            }
        );
        assert_eq!(
            store.alias_symbol_links(namespace_alias),
            Some(&AliasSymbolLinks::default())
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
