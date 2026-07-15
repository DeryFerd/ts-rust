//! Production syntax and module-resolution host for canonical alias targets.
//!
//! This first dependency-closed slice intentionally accepts only direct plain
//! TypeScript ESM namespace imports, named non-default imports, and named
//! non-default re-exports with a module specifier. The host returns immediate
//! symbols and never follows an alias target: live recursion and transitive
//! type-only propagation remain owned by the canonical alias kernel.

use std::collections::BTreeMap;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{BoundFile, InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalModuleResolutionLookup, CanonicalModuleResolutionManifest,
    CanonicalModuleResolutionMode, CanonicalResolvedModule, CanonicalSemanticStore,
    alias::{
        CanonicalAliasTargetHost, CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
};

#[derive(Clone, Copy, Debug)]
struct ProductionAliasTargetSource<'arena> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
}

/// Store-free production alias-target provider over exact retained Program
/// AST/binder snapshots and the immutable compiler module-resolution manifest.
#[derive(Debug)]
pub struct ProductionAliasTargetHost<'arena, 'manifest> {
    store: SemanticStoreId,
    sources: BTreeMap<FileId, ProductionAliasTargetSource<'arena>>,
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
    InvalidSymbolStore(FileId),
    DuplicateFile(FileId),
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
    NamedModuleMember {
        specifier: NodeRef,
        name: String,
        type_only: bool,
    },
}

impl<'arena, 'manifest> ProductionAliasTargetHost<'arena, 'manifest> {
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
            if retained
                .insert(file, ProductionAliasTargetSource { arena, bound })
                .is_some()
            {
                return Err(ProductionAliasTargetHostError::DuplicateFile(file));
            }
        }

        Ok(Self {
            store: store.id(),
            sources: retained,
            module_resolutions,
        })
    }

    fn checked_source<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        reference: NodeRef,
    ) -> Result<ProductionAliasTargetSource<'arena>, CanonicalAliasTargetUnavailable> {
        let source = self.sources.get(&reference.file).copied().ok_or(
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

    fn checked_node<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        reference: NodeRef,
    ) -> Result<(&'arena Node, ProductionAliasTargetSource<'arena>), CanonicalAliasTargetUnavailable>
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
            if !is_alias_symbol_declaration(source.arena, source.bound, node) {
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
        if facts.is_javascript_file() {
            return Err(
                CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                    declaration,
                    file: declaration.file,
                },
            );
        }
        if facts.is_common_js_module() {
            return Err(CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration,
                file: declaration.file,
            });
        }

        match (node.kind, &node.data) {
            (SyntaxKind::ImportClause, NodeData::ImportClause(clause)) if clause.name.is_some() => {
                Err(CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(
                    declaration,
                ))
            }
            (SyntaxKind::NamespaceImport, NodeData::NamespaceImport(_)) => {
                let (specifier, clause) = namespace_import_context(source.arena, declaration)?;
                Ok(SupportedAliasDeclaration::NamespaceImport {
                    specifier,
                    type_only: clause.phase_modifier == Some(SyntaxKind::TypeKeyword),
                })
            }
            (SyntaxKind::ImportSpecifier, NodeData::ImportSpecifier(import)) => {
                let (specifier, clause) = import_specifier_context(source.arena, declaration)?;
                let name =
                    module_export_name(source.arena, import.property_name.unwrap_or(import.name))
                        .ok_or(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ))?;
                if name == "default" {
                    return Err(CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(
                        declaration,
                    ));
                }
                Ok(SupportedAliasDeclaration::NamedModuleMember {
                    specifier,
                    name: name.to_owned(),
                    type_only: import.is_type_only
                        || clause.phase_modifier == Some(SyntaxKind::TypeKeyword),
                })
            }
            (SyntaxKind::ExportSpecifier, NodeData::ExportSpecifier(export)) => {
                let (specifier, declaration_type_only) =
                    export_specifier_context(source.arena, declaration)?;
                let Some(specifier) = specifier else {
                    return Err(CanonicalAliasTargetUnavailable::UnsupportedLocalExport(
                        declaration,
                    ));
                };
                let exported_name = module_export_name(source.arena, export.name).ok_or(
                    CanonicalAliasTargetUnavailable::MalformedDeclaration(declaration),
                )?;
                let name =
                    module_export_name(source.arena, export.property_name.unwrap_or(export.name))
                        .ok_or(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                        declaration,
                    ))?;
                if exported_name == "default" || name == "default" {
                    return Err(CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(
                        declaration,
                    ));
                }
                Ok(SupportedAliasDeclaration::NamedModuleMember {
                    specifier,
                    name: name.to_owned(),
                    type_only: export.is_type_only || declaration_type_only,
                })
            }
            _ => Err(CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(declaration)),
        }
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

    fn plain_esm_module<MapperPayload>(
        &self,
        store: &CanonicalSemanticStore<MapperPayload>,
        declaration: NodeRef,
        resolved: CanonicalResolvedModule,
    ) -> Result<SemanticSymbolId, CanonicalAliasTargetUnavailable> {
        let target = self.sources.get(&resolved.target_file()).copied().ok_or(
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
        if facts.is_javascript_file() {
            return Err(
                CanonicalAliasTargetUnavailable::JavaScriptModuleUnsupported {
                    declaration,
                    file: resolved.target_file(),
                },
            );
        }
        if facts.is_common_js_module()
            || resolved.usage_mode() == CanonicalModuleResolutionMode::CommonJs
            || resolved.target_mode() == CanonicalModuleResolutionMode::CommonJs
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
        if resolved.usage_mode() != CanonicalModuleResolutionMode::Esm
            || resolved.target_mode() != CanonicalModuleResolutionMode::Esm
            || !module_record.flags().intersects(SymbolFlags::MODULE)
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
        if let Some(exports) = module_record.exports() {
            let exports = store.symbol_table(exports).ok_or(
                CanonicalAliasTargetUnavailable::MalformedModuleSymbol {
                    declaration,
                    module,
                },
            )?;
            if exports
                .get(InternalSymbolName::ExportEquals.as_ref())
                .is_some()
            {
                return Err(
                    CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported {
                        declaration,
                        module,
                    },
                );
            }
        }
        Ok(module)
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
        if exports
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
}

impl<MapperPayload> CanonicalAliasTargetHost<MapperPayload> for ProductionAliasTargetHost<'_, '_> {
    fn get_target_of_alias_declaration(
        &mut self,
        store: &mut CanonicalSemanticStore<MapperPayload>,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
        if store.id() != self.store {
            return Err(CanonicalAliasTargetUnavailable::ForeignStore {
                expected: self.store,
                actual: store.id(),
            });
        }
        let declaration = self.alias_declaration(store, alias)?;
        let supported = self.supported_declaration(store, declaration)?;
        let (specifier, type_only) = match &supported {
            SupportedAliasDeclaration::NamespaceImport {
                specifier,
                type_only,
            }
            | SupportedAliasDeclaration::NamedModuleMember {
                specifier,
                type_only,
                ..
            } => (*specifier, *type_only),
        };
        let resolved = self.resolved_module(declaration, specifier, store)?;
        let module = self.plain_esm_module(store, declaration, resolved)?;
        let target = match &supported {
            SupportedAliasDeclaration::NamespaceImport { .. } => module,
            SupportedAliasDeclaration::NamedModuleMember { name, .. } => {
                Self::direct_export(store, declaration, module, name)?
            }
        };

        if type_only {
            Self::mark_type_only(store, alias, declaration)?;
        }
        Ok(CanonicalImmediateAliasTarget::Resolved(target))
    }
}

fn is_alias_symbol_declaration(arena: &NodeArena, bound: &BoundFile, node: &Node) -> bool {
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
        (
            SyntaxKind::VariableDeclaration
            | SyntaxKind::BindingElement
            | SyntaxKind::BinaryExpression,
            _,
        ) => bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_javascript_file),
        _ => false,
    }
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
    use ts_parser::{ParseResult, parse_source_file};

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

    fn facts(file: FileId, state: CanonicalModuleState) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
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
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, state) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    facts(file, state),
                )
                .unwrap();
        }
        for &(file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
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
        let (symbols, bound_files) = bindings(files);
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
    fn rejects_default_local_star_export_equals_commonjs_and_synthetic_paths() {
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
        let declarations = [
            "DefaultThing",
            "value",
            "missing",
            "legacy",
            "cjs",
            "synthetic",
        ]
        .map(|name| alias_declaration_named(&importer, importer_file, name));
        let aliases = declarations.map(|declaration| alias(&bound_files, declaration));

        let expected = [
            CanonicalAliasTargetUnavailable::UnsupportedDefaultAlias(declarations[0]),
            CanonicalAliasTargetUnavailable::UnsupportedLocalExport(declarations[1]),
            CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported {
                declaration: declarations[2],
                module: source_module(&bound_files, star_file),
            },
            CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported {
                declaration: declarations[3],
                module: source_module(&bound_files, equals_file),
            },
            CanonicalAliasTargetUnavailable::CommonJsModuleUnsupported {
                declaration: declarations[4],
                file: plain_file,
            },
            CanonicalAliasTargetUnavailable::SyntheticModuleResolutionUnsupported {
                declaration: declarations[5],
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
        let importer = parsed("import DefaultThing, { wanted } from './target';");
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
        let source_file = bound_files.get(&importer_file).unwrap().source_file();
        assert!(store.set_symbol_declarations(alias, Some(vec![declaration, source_file]), None));
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
    fn constructor_rejects_stale_sources_before_retaining_a_host() {
        let mut importer = parsed("import { value } from './target';");
        let target = parsed("export const value = 1;");
        let importer_file = FileId::new(60);
        let target_file = FileId::new(61);
        let files_before_mutation = [
            (importer_file, &importer, CanonicalModuleState::External),
            (target_file, &target, CanonicalModuleState::External),
        ];
        let (symbols, bound_files) = bindings(&files_before_mutation);
        importer.arena.set_source_text("stale");
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&importer.arena, importer.source_file, importer_file)
                .is_some()
        );
        assert!(
            store
                .register_source_file(&target.arena, target.source_file, target_file)
                .is_some()
        );
        let unavailable = CanonicalModuleResolutionManifest::unavailable();
        let error = ProductionAliasTargetHost::new(
            &store,
            [
                (&importer.arena, bound_files.get(&importer_file).unwrap()),
                (&target.arena, bound_files.get(&target_file).unwrap()),
            ],
            &unavailable,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            ProductionAliasTargetHostError::ArenaRevisionMismatch { file, .. }
                if file == importer_file
        ));
    }
}
