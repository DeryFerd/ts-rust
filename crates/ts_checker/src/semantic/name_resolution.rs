//! Production host callbacks for canonical name resolution.
//!
//! The binder resolver deliberately delegates checker semantics for merged
//! symbols and aliases. Declaration and table entries follow exactly one
//! validated merge redirect before their flags are observed. Resolved alias
//! links can supply their target meaning, while unresolved aliases remain
//! explicit capability errors.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashSet},
};

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalNameResolverHost,
    CanonicalNameResolverOptions, CanonicalResolutionLocation, EscapedNameRef, InternalSymbolName,
    SemanticStoreId, SemanticSymbolId, SymbolFlags, SymbolStore, SymbolTableId,
    canonical_has_syntactic_modifier,
};

use super::{
    AliasTargetState, CanonicalTypeMapperStore, alias_provider::ProductionAliasSourceRegistry,
    spelling::get_spelling_suggestion,
};

#[derive(Clone, Copy, Debug)]
struct ProductionNameResolverSource<'arena> {
    arena: &'arena NodeArena,
    bound: &'arena BoundFile,
}

#[derive(Debug)]
enum ProductionNameResolverSources<'arena> {
    Retained(BTreeMap<FileId, ProductionNameResolverSource<'arena>>),
    Registry(&'arena ProductionAliasSourceRegistry<'arena>),
}

impl<'arena> ProductionNameResolverSources<'arena> {
    fn get(&self, file: FileId) -> Option<ProductionNameResolverSource<'arena>> {
        match self {
            Self::Retained(sources) => sources.get(&file).copied(),
            Self::Registry(sources) => (*sources)
                .snapshot(file)
                .map(|(arena, bound)| ProductionNameResolverSource { arena, bound }),
        }
    }
}

/// A validated production implementation of the checker callbacks required
/// by [`ts_binder::CanonicalNameResolver`].
///
/// AST sources are retained by exact borrowed identity. The semantic store
/// must already own their binder graph and have completed intrinsic bootstrap,
/// which supplies the canonical globals and `arguments` identities.
/// Direct construction is checker-internal. Production construction mints it
/// through a private declared-type capability after ordered globals are
/// merged; a completed [`super::CanonicalCheckerContext`] can mint additional
/// hosts after all eager global initialization completes.
///
/// The constructor deliberately does not escape through the crate's public
/// API before that phase boundary exists:
///
/// ```compile_fail
/// # use ts_ast::NodeArena;
/// # use ts_binder::{BoundFile, CanonicalNameResolverOptions};
/// # use ts_checker::semantic::{CanonicalTypeMapperStore, name_resolution::ProductionNameResolverHost};
/// # fn construct<'a>(
/// #     store: &'a CanonicalTypeMapperStore,
/// #     arena: &'a NodeArena,
/// #     bound: &'a BoundFile,
/// # ) {
/// let _ = ProductionNameResolverHost::new(
///     store,
///     [(arena, bound)],
///     CanonicalNameResolverOptions::default(),
/// );
/// # }
/// ```
#[derive(Debug)]
pub struct ProductionNameResolverHost<'store, 'arena> {
    store: &'store CanonicalTypeMapperStore,
    sources: ProductionNameResolverSources<'arena>,
    options: CanonicalNameResolverOptions,
    spelling_suggestions: bool,
    validate_class_enum_sources: bool,
}

/// Why a source set cannot back production name resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProductionNameResolverHostError {
    IntrinsicBootstrapNotInitialized,
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
    RegistryStoreMismatch {
        expected: SemanticStoreId,
        actual: SemanticStoreId,
    },
}

impl std::fmt::Display for ProductionNameResolverHostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IntrinsicBootstrapNotInitialized => {
                formatter.write_str("production name resolution requires intrinsic bootstrap")
            }
            Self::ArenaMismatch { file, .. } => write!(
                formatter,
                "name-resolution source {} uses a different AST arena",
                file.index()
            ),
            Self::ArenaRevisionMismatch { file, .. } => write!(
                formatter,
                "name-resolution source {} changed after canonical binding",
                file.index()
            ),
            Self::DeclarationsIncomplete(file) => write!(
                formatter,
                "name-resolution source {} has incomplete declaration bindings",
                file.index()
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "name-resolution source {} has no canonical source facts",
                file.index()
            ),
            Self::InvalidSourceFile(source) => write!(
                formatter,
                "name-resolution source {} has an invalid source-file root",
                source.file.index()
            ),
            Self::InvalidSymbolStore(file) => write!(
                formatter,
                "name-resolution source {} belongs to another symbol store",
                file.index()
            ),
            Self::DuplicateFile(file) => write!(
                formatter,
                "name-resolution source {} was supplied more than once",
                file.index()
            ),
            Self::RegistryStoreMismatch { .. } => formatter
                .write_str("name-resolution source registry belongs to another symbol store"),
        }
    }
}

impl std::error::Error for ProductionNameResolverHostError {}

impl<'store, 'arena> ProductionNameResolverHost<'store, 'arena> {
    /// Validates and retains one complete Program source set.
    ///
    /// An empty source set remains useful for the pinned nil-location global
    /// resolver. Bound declaration lookup additionally requires the exact
    /// source that owns the requested node.
    // Only production construction and completed CanonicalCheckerContext
    // entry points reach this constructor. The declared-type path is guarded
    // by its private post-global-merge capability.
    pub(super) fn new(
        store: &'store CanonicalTypeMapperStore,
        sources: impl IntoIterator<Item = (&'arena NodeArena, &'arena BoundFile)>,
        options: CanonicalNameResolverOptions,
    ) -> Result<Self, ProductionNameResolverHostError> {
        if store.intrinsic_bootstrap().is_none() {
            return Err(ProductionNameResolverHostError::IntrinsicBootstrapNotInitialized);
        }

        let mut retained = BTreeMap::new();
        for (arena, bound) in sources {
            let file = bound.file_id();
            if arena.id() != bound.node_arena_id() {
                return Err(ProductionNameResolverHostError::ArenaMismatch {
                    file,
                    expected: bound.node_arena_id(),
                    actual: arena.id(),
                });
            }
            if !bound.declarations_complete() {
                return Err(ProductionNameResolverHostError::DeclarationsIncomplete(
                    file,
                ));
            }
            if bound.source_facts().is_none() {
                return Err(ProductionNameResolverHostError::MissingSourceFileFacts(
                    file,
                ));
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
                return Err(ProductionNameResolverHostError::InvalidSourceFile(source));
            }
            if bound.node_arena_revision() != arena.revision() {
                return Err(ProductionNameResolverHostError::ArenaRevisionMismatch {
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
                return Err(ProductionNameResolverHostError::InvalidSymbolStore(file));
            }
            if retained
                .insert(file, ProductionNameResolverSource { arena, bound })
                .is_some()
            {
                return Err(ProductionNameResolverHostError::DuplicateFile(file));
            }
        }

        Ok(Self {
            store,
            sources: ProductionNameResolverSources::Retained(retained),
            options,
            spelling_suggestions: false,
            validate_class_enum_sources: false,
        })
    }

    /// Creates an allocation-free query view over a context-owned,
    /// once-validated Program source registry.
    pub(super) fn from_registry(
        store: &'store CanonicalTypeMapperStore,
        sources: &'arena ProductionAliasSourceRegistry<'arena>,
        options: CanonicalNameResolverOptions,
    ) -> Result<Self, ProductionNameResolverHostError> {
        if store.intrinsic_bootstrap().is_none() {
            return Err(ProductionNameResolverHostError::IntrinsicBootstrapNotInitialized);
        }
        if sources.store_id() != store.id() {
            return Err(ProductionNameResolverHostError::RegistryStoreMismatch {
                expected: sources.store_id(),
                actual: store.id(),
            });
        }
        #[cfg(test)]
        sources.note_name_resolver_view();
        Ok(Self {
            store,
            sources: ProductionNameResolverSources::Registry(sources),
            options,
            spelling_suggestions: false,
            validate_class_enum_sources: false,
        })
    }

    /// Enables upstream spelling lookup without changing ordinary resolution.
    pub(super) const fn with_spelling_suggestions(mut self) -> Self {
        self.spelling_suggestions = true;
        self
    }

    /// Checks class and enum sources before their flags can filter a name lookup.
    pub(super) const fn with_class_enum_source_validation(mut self) -> Self {
        self.validate_class_enum_sources = true;
        self
    }

    /// Pinned checker `getSymbolOfDeclaration`: read the binder-owned node
    /// symbol and follow exactly one merged-symbol redirect.
    #[must_use]
    pub fn symbol_of_declaration(&self, declaration: NodeRef) -> Option<SemanticSymbolId> {
        let raw = self.source(declaration)?.bound.symbol(declaration)?;
        self.store.get_merged_symbol(raw)
    }

    /// Pinned checker table lookup with already-resolved alias meanings.
    ///
    /// An absent or wrong-meaning symbol is an ordinary miss. A resolved alias
    /// is returned as its alias identity when its target has the requested
    /// meaning, matching upstream `getSymbol`. An unresolved alias returns an
    /// explicit capability error.
    ///
    /// # Errors
    ///
    /// Returns a provenance error for an invalid table or symbol, or
    /// [`CanonicalNameResolutionError::AliasResolutionUnavailable`] when
    /// determining the requested meaning requires the unported alias resolver.
    pub fn lookup_name(
        &self,
        symbols: SymbolTableId,
        name: EscapedNameRef<'_>,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let table = self
            .store
            .symbol_table(symbols)
            .ok_or(CanonicalNameResolutionError::InvalidHostTable(symbols))?;
        if !meaning.intersects(SymbolFlags::ALL) {
            return Ok(None);
        }
        let Some(raw) = table.get(name) else {
            return Ok(None);
        };
        let symbol = self
            .store
            .get_merged_symbol(raw)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(raw))?;
        let record = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?;
        let flags = record.flags();
        if self.validate_class_enum_sources
            && (flags
                | self
                    .store
                    .source_symbol_flags(symbol)
                    .unwrap_or(SymbolFlags::NONE))
            .intersects(SymbolFlags::CLASS | SymbolFlags::ENUM)
            && (record.name() != name
                || !self.store.source_symbol_declarations_match(symbol)
                || !self.store.source_merged_symbol_declarations_match(symbol))
        {
            return Err(CanonicalNameResolutionError::InvalidHostSymbol(symbol));
        }
        if flags.intersects(meaning) {
            return Ok(Some(symbol));
        }
        if flags.contains(SymbolFlags::ALIAS) {
            let Some(target) = self.resolved_alias_target(symbol)? else {
                return Ok(None);
            };
            let target_flags = self
                .store
                .symbol(target)
                .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(target))?
                .flags();
            return Ok(target_flags.intersects(meaning).then_some(symbol));
        }
        Ok(None)
    }

    fn spelling_candidate_name(
        &self,
        symbol: SemanticSymbolId,
        meaning: SymbolFlags,
    ) -> Option<&str> {
        let symbol = self.store.get_merged_symbol(symbol)?;
        let record = self.store.symbol(symbol)?;
        let name = record.name();
        let text = name.as_utf8()?;
        if name.is_internal() || text.starts_with('"') {
            return None;
        }
        if record.flags().intersects(meaning) {
            return Some(text);
        }
        if !record.flags().contains(SymbolFlags::ALIAS) {
            return None;
        }
        let target = self.resolved_alias_target(symbol).ok().flatten()?;
        self.store
            .symbol(target)
            .is_some_and(|target| target.flags().intersects(meaning))
            .then_some(text)
    }

    fn compare_spelling_candidates(
        &self,
        left: SemanticSymbolId,
        right: SemanticSymbolId,
    ) -> Ordering {
        if left == right {
            return Ordering::Equal;
        }
        let Some(left_record) = self.store.symbol(left) else {
            return Ordering::Greater;
        };
        let Some(right_record) = self.store.symbol(right) else {
            return Ordering::Less;
        };
        let left_declaration = left_record
            .declarations()
            .and_then(|declarations| declarations.first())
            .copied();
        let right_declaration = right_record
            .declarations()
            .and_then(|declarations| declarations.first())
            .copied();
        let declaration_order = match (left_declaration, right_declaration) {
            (Some(left), Some(right)) => left.file.cmp(&right.file).then_with(|| {
                self.node(left)
                    .map(|record| record.range.start)
                    .cmp(&self.node(right).map(|record| record.range.start))
            }),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => Ordering::Equal,
        };
        declaration_order
            .then_with(|| {
                left_record
                    .name()
                    .as_bytes()
                    .cmp(right_record.name().as_bytes())
            })
            .then_with(|| left.cmp(&right))
    }

    /// Resolves one identifier, qualified name, or property-access entity.
    ///
    /// Namespace segments follow merged export tables. Warm import aliases
    /// retain their alias identity during lexical lookup and resolve only
    /// after the requested meaning has been proven.
    ///
    /// # Errors
    ///
    /// Returns a provenance error for invalid syntax, symbols, or tables. An
    /// alias without an exact cached target remains an explicit capability
    /// error.
    pub fn resolve_entity_name(
        &mut self,
        entity: NodeRef,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let source = self
            .source(entity)
            .ok_or(CanonicalNameResolutionError::UnboundLocation(entity))?;
        let record = source
            .arena
            .get(entity.node)
            .ok_or(CanonicalNameResolutionError::UnboundLocation(entity))?;
        match &record.data {
            NodeData::Identifier(identifier) if record.kind == SyntaxKind::Identifier => {
                let store = self.store;
                let mut symbol = CanonicalNameResolver::new(
                    source.arena,
                    source.bound,
                    store.symbol_store(),
                    self,
                )?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(entity)),
                    &identifier.text,
                    meaning,
                    None,
                    true,
                    false,
                )?;
                if symbol.is_none() && meaning == SymbolFlags::NAMESPACE {
                    let alias = CanonicalNameResolver::new(
                        source.arena,
                        source.bound,
                        store.symbol_store(),
                        self,
                    )?
                    .resolve(
                        Some(CanonicalResolutionLocation::Bound(entity)),
                        &identifier.text,
                        SymbolFlags::ALIAS,
                        None,
                        true,
                        false,
                    )?;
                    symbol = alias
                        .map(|alias| self.export_equals_import_namespace(alias))
                        .transpose()?
                        .flatten();
                }
                self.resolve_entity_symbol(symbol, meaning)
            }
            NodeData::QualifiedName(qualified) if record.kind == SyntaxKind::QualifiedName => self
                .resolve_qualified_entity_name(
                    entity,
                    NodeRef::new(entity.arena, entity.file, qualified.left),
                    NodeRef::new(entity.arena, entity.file, qualified.right),
                    meaning,
                ),
            NodeData::PropertyAccessExpression(access)
                if record.kind == SyntaxKind::PropertyAccessExpression =>
            {
                self.resolve_qualified_entity_name(
                    entity,
                    NodeRef::new(entity.arena, entity.file, access.expression),
                    NodeRef::new(entity.arena, entity.file, access.name),
                    meaning,
                )
            }
            _ => Err(CanonicalNameResolutionError::UnboundLocation(entity)),
        }
    }

    fn resolve_qualified_entity_name(
        &mut self,
        entity: NodeRef,
        left: NodeRef,
        right: NodeRef,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let left_record = self
            .node(left)
            .ok_or(CanonicalNameResolutionError::UnboundLocation(left))?;
        let right_record = self
            .node(right)
            .ok_or(CanonicalNameResolutionError::UnboundLocation(right))?;
        if left_record.parent != Some(entity.node) || right_record.parent != Some(entity.node) {
            return Err(CanonicalNameResolutionError::UnboundLocation(entity));
        }
        let NodeData::Identifier(identifier) = &right_record.data else {
            return Err(CanonicalNameResolutionError::UnboundLocation(right));
        };
        if right_record.kind != SyntaxKind::Identifier {
            return Err(CanonicalNameResolutionError::UnboundLocation(right));
        }
        let name = identifier.text.clone();

        let Some(namespace) = self.resolve_entity_name(left, SymbolFlags::NAMESPACE)? else {
            return Ok(None);
        };
        let record = self
            .store
            .symbol(namespace)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(namespace))?;
        if !record.flags().intersects(SymbolFlags::NAMESPACE) {
            return Ok(None);
        }
        let Some(exports) = self
            .store
            .module_symbol_links(namespace)
            .and_then(|links| links.resolved_exports)
            .or_else(|| record.exports())
        else {
            return Ok(None);
        };
        let symbol = self.lookup_name(exports, EscapedNameRef::source(&name), meaning)?;
        self.resolve_entity_symbol(symbol, meaning)
    }

    fn export_equals_import_namespace(
        &self,
        alias: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let Some(alias_record) = self.store.symbol(alias) else {
            return Err(CanonicalNameResolutionError::InvalidHostSymbol(alias));
        };
        let Some([declaration]) = alias_record.declarations() else {
            return Ok(None);
        };
        let Some(source) = self.source(*declaration) else {
            return Ok(None);
        };
        let Some(NodeData::ImportEqualsDeclaration(import)) = source
            .arena
            .get(declaration.node)
            .map(|record| &record.data)
        else {
            return Ok(None);
        };
        if source.bound.symbol(*declaration) != Some(alias)
            || !matches!(
                source
                    .arena
                    .get(import.module_reference)
                    .map(|record| &record.data),
                Some(NodeData::ExternalModuleReference(_))
            )
        {
            return Ok(None);
        }

        let Some(target) = self.resolved_alias_target(alias)? else {
            return Ok(None);
        };
        let Some(record) = self.store.symbol(target) else {
            return Err(CanonicalNameResolutionError::InvalidHostSymbol(target));
        };
        if record.name() != InternalSymbolName::ExportEquals.as_ref()
            || record.flags() != SymbolFlags::PROPERTY
                && record.flags() != SymbolFlags::PROPERTY | SymbolFlags::NAMESPACE_MODULE
        {
            return Ok(None);
        }
        let Some(module) = self.store.get_parent_of_symbol(target) else {
            return Ok(None);
        };
        let Some(module_record) = self.store.symbol(module) else {
            return Err(CanonicalNameResolutionError::InvalidHostSymbol(module));
        };
        let Some(exports) = module_record
            .exports()
            .and_then(|exports| self.store.symbol_table(exports))
        else {
            return Ok(None);
        };
        Ok((module_record.flags().intersects(SymbolFlags::NAMESPACE)
            && exports.get(InternalSymbolName::ExportEquals.as_ref()) == Some(target))
        .then_some(module))
    }

    fn resolve_entity_symbol(
        &self,
        symbol: Option<SemanticSymbolId>,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let Some(mut symbol) = symbol else {
            return Ok(None);
        };
        let mut seen = HashSet::new();
        loop {
            let flags = self
                .store
                .symbol(symbol)
                .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?
                .flags();
            if flags.intersects(meaning) {
                return Ok(Some(symbol));
            }
            if !flags.contains(SymbolFlags::ALIAS) {
                return Ok(None);
            }
            if !seen.insert(symbol) {
                return Err(CanonicalNameResolutionError::AliasResolutionUnavailable(
                    symbol,
                ));
            }
            let Some(target) = self.resolved_alias_target(symbol)? else {
                return Ok(None);
            };
            symbol = target;
        }
    }

    fn resolved_alias_target(
        &self,
        alias: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let links = self.store.alias_symbol_links(alias).ok_or(
            CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
        )?;
        match links.alias_target {
            AliasTargetState::Unknown => Ok(None),
            AliasTargetState::Unresolved => Err(
                CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
            ),
            AliasTargetState::Resolved(target) => self
                .store
                .get_merged_symbol(target)
                .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(target))
                .map(Some),
        }
    }

    fn source(&self, reference: NodeRef) -> Option<ProductionNameResolverSource<'arena>> {
        let source = self.sources.get(reference.file)?;
        (reference.is_for(source.arena.id(), source.bound.file_id())
            && source.bound.contains(reference))
        .then_some(source)
    }

    fn node(&self, reference: NodeRef) -> Option<&'arena Node> {
        let source = self.source(reference)?;
        source
            .arena
            .get(reference.node)
            .filter(|node| node.data.matches_syntax_kind(node.kind))
    }
}

impl CanonicalNameResolverHost for ProductionNameResolverHost<'_, '_> {
    fn compiler_options(&self) -> CanonicalNameResolverOptions {
        self.options
    }

    fn get_symbol_of_declaration(&mut self, declaration: NodeRef) -> Option<SemanticSymbolId> {
        self.symbol_of_declaration(declaration)
    }

    fn get_local_symbol_of_declaration(
        &mut self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        let source = self.source(declaration)?;
        let symbol = source.bound.local_symbol(declaration)?;
        self.store.get_merged_symbol(symbol)
    }

    fn lookup(
        &mut self,
        store: &SymbolStore,
        symbols: SymbolTableId,
        name: EscapedNameRef<'_>,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        if store.id() != self.store.id() {
            return Err(CanonicalNameResolutionError::InvalidHostTable(symbols));
        }
        let resolved = self.lookup_name(symbols, name, meaning)?;
        if resolved.is_some() || !self.spelling_suggestions {
            return Ok(resolved);
        }
        let Some(requested) = name.as_utf8() else {
            return Ok(None);
        };
        let table = self
            .store
            .symbol_table(symbols)
            .ok_or(CanonicalNameResolutionError::InvalidHostTable(symbols))?;
        let suggestion = get_spelling_suggestion(
            requested,
            table.iter().map(|(_, symbol)| symbol),
            |symbol| self.spelling_candidate_name(*symbol, meaning),
            |left, right| self.compare_spelling_candidates(*left, *right),
        );
        suggestion
            .map(|symbol| {
                self.store
                    .get_merged_symbol(symbol)
                    .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))
            })
            .transpose()
    }

    fn globals(&self) -> Option<SymbolTableId> {
        self.store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.globals)
    }

    fn arguments_symbol(&mut self, store: &SymbolStore) -> Option<SemanticSymbolId> {
        if store.id() != self.store.id() {
            return None;
        }
        self.store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.arguments_symbol)
    }

    fn require_symbol(&mut self, store: &SymbolStore) -> Option<SemanticSymbolId> {
        if store.id() != self.store.id() {
            return None;
        }
        self.store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.require_symbol)
    }

    fn foreign_declaration_kind(&mut self, declaration: NodeRef) -> Option<SyntaxKind> {
        self.node(declaration).map(|node| node.kind)
    }

    fn foreign_declaration_parent(&mut self, declaration: NodeRef) -> Option<NodeRef> {
        let source = self.source(declaration)?;
        let parent = self.node(declaration)?.parent?;
        let parent = NodeRef::new(declaration.arena, declaration.file, parent);
        source.bound.contains(parent).then_some(parent)
    }

    fn foreign_declaration_has_syntactic_modifier(
        &mut self,
        declaration: NodeRef,
        modifier: SyntaxKind,
    ) -> Option<bool> {
        let source = self.source(declaration)?;
        self.node(declaration)?;
        Some(canonical_has_syntactic_modifier(
            source.arena,
            declaration.node,
            modifier,
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{NodeArena, NodeData, NodeId};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        CheckFlags, EscapedName, resolve_global_name,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, DeclaredTypeHost, IntrinsicBootstrapOptions, TypeData, TypeMapper,
        TypeRecord, types::ObjectFlags,
    };

    type TestStore = super::super::SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: BTreeMap<FileId, ParseResult>,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(sources: &[(FileId, &str, CanonicalModuleState)]) -> Fixture {
        let parsed = sources
            .iter()
            .map(|(file, source, _)| {
                let parsed = parse_source_file(source);
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                (*file, parsed)
            })
            .collect::<BTreeMap<_, _>>();
        let mut binder = CanonicalBinder::new();
        for &(file, _, module_state) in sources {
            let source = &parsed[&file];
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        module_state,
                    ),
                )
                .unwrap();
        }
        for &(file, _, _) in sources {
            binder
                .bind_typescript_declaration_slice(&parsed[&file].arena, file)
                .unwrap();
        }
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        for &(file, _, _) in sources {
            let source = &parsed[&file];
            assert!(
                store
                    .register_source_file(&source.arena, source.source_file, file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        Fixture {
            parsed,
            files,
            store,
        }
    }

    fn identifier_text(arena: &NodeArena, identifier: NodeId) -> Option<&str> {
        let NodeData::Identifier(identifier) = &arena.get(identifier)?.data else {
            return None;
        };
        Some(&identifier.text)
    }

    fn declaration_name<'a>(arena: &'a NodeArena, node: &Node) -> Option<&'a str> {
        let name = match &node.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::ImportEqualsDeclaration(data) => data.name,
            NodeData::ModuleDeclaration(data) => data.name,
            _ => return None,
        };
        identifier_text(arena, name)
    }

    fn named_declaration(fixture: &Fixture, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
        let parsed = &fixture.parsed[&file];
        let node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == kind && declaration_name(&parsed.arena, record) == Some(name))
                    .then_some(node)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} named {name}"));
        NodeRef::new(parsed.arena.id(), file, node)
    }

    fn declaration_symbol(fixture: &Fixture, declaration: NodeRef) -> SemanticSymbolId {
        fixture.files[&declaration.file]
            .symbol(declaration)
            .unwrap()
    }

    fn type_alias_entity_name(fixture: &Fixture, file: FileId, expected: &str) -> NodeRef {
        let parsed = &fixture.parsed[&file];
        parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                if name.text != expected {
                    return None;
                }
                let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(alias.type_)?.data
                else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, reference.type_name))
            })
            .unwrap_or_else(|| panic!("missing type alias reference {expected}"))
    }

    fn script_namespace_symbol(fixture: &Fixture, file: FileId, name: &str) -> SemanticSymbolId {
        let bound = &fixture.files[&file];
        bound
            .locals(bound.source_file())
            .and_then(|locals| fixture.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
            .unwrap_or_else(|| panic!("missing namespace {name}"))
    }

    fn production_host(fixture: &Fixture) -> ProductionNameResolverHost<'_, '_> {
        ProductionNameResolverHost::new(
            &fixture.store,
            fixture.parsed.iter().map(|(file, parsed)| {
                (&parsed.arena, fixture.files.get(file).expect("bound file"))
            }),
            CanonicalNameResolverOptions::default(),
        )
        .unwrap()
    }

    fn declared_host<'fixture>(
        parsed: &'fixture BTreeMap<FileId, ParseResult>,
        files: &'fixture BTreeMap<FileId, BoundFile>,
    ) -> DeclaredTypeHost<'fixture> {
        DeclaredTypeHost::new(
            parsed
                .iter()
                .map(|(file, parsed)| (&parsed.arena, files.get(file).expect("bound file"))),
        )
        .unwrap()
    }

    fn merge_globals(fixture: &mut Fixture, symbols: &[SemanticSymbolId]) -> SemanticSymbolId {
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let mut merged = symbols[0];
        for symbol in symbols {
            merged = fixture.store.merge_global_symbol(globals, *symbol).unwrap();
        }
        merged
    }

    #[test]
    fn spelling_lookup_is_opt_in_and_uses_source_declaration_order() {
        for (index, (source, expected)) in [
            ("const valueA = 1; const valueB = 2;", "valueA"),
            ("const valueB = 1; const valueA = 2;", "valueB"),
        ]
        .into_iter()
        .enumerate()
        {
            let file = FileId::new(8_920 + u32::try_from(index).unwrap());
            let fixture = fixture(&[(file, source, CanonicalModuleState::Script)]);
            let bound = &fixture.files[&file];
            let locals = bound.locals(bound.source_file()).unwrap();
            let expected = fixture
                .store
                .symbol_table(locals)
                .and_then(|locals| locals.get_source(expected))
                .unwrap();

            let mut ordinary = production_host(&fixture);
            assert_eq!(
                ordinary.lookup(
                    fixture.store.symbol_store(),
                    locals,
                    EscapedNameRef::source("valueC"),
                    SymbolFlags::VALUE,
                ),
                Ok(None),
            );

            let mut suggestions = production_host(&fixture).with_spelling_suggestions();
            assert_eq!(
                suggestions.lookup(
                    fixture.store.symbol_store(),
                    locals,
                    EscapedNameRef::source("valueC"),
                    SymbolFlags::VALUE,
                ),
                Ok(Some(expected)),
            );
        }
    }

    #[test]
    fn spelling_resolution_prefers_the_innermost_visible_scope() {
        let file = FileId::new(8_922);
        let fixture = fixture(&[(
            file,
            "const valueA = 1; function read(valueB: number): number { return valueC; }",
            CanonicalModuleState::Script,
        )]);
        let parsed = &fixture.parsed[&file];
        let bound = &fixture.files[&file];
        let reference = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "valueC")
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::Parameter).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let expected = bound.symbol(parameter).unwrap();
        let mut suggestions = production_host(&fixture).with_spelling_suggestions();

        assert_eq!(
            CanonicalNameResolver::new(
                &parsed.arena,
                bound,
                fixture.store.symbol_store(),
                &mut suggestions,
            )
            .unwrap()
            .resolve(
                Some(CanonicalResolutionLocation::Bound(reference)),
                "valueC",
                SymbolFlags::VALUE,
                None,
                false,
                false,
            ),
            Ok(Some(expected)),
        );
    }

    #[test]
    fn merged_class_and_interface_share_one_canonical_declared_cache() {
        let class_file = FileId::new(701);
        let interface_file = FileId::new(702);
        let mut fixture = fixture(&[
            (
                class_file,
                "class Shared<T> { value!: T }",
                CanonicalModuleState::Script,
            ),
            (
                interface_file,
                "interface Shared<U> { other: U }",
                CanonicalModuleState::Script,
            ),
        ]);
        let class_declaration =
            named_declaration(&fixture, class_file, SyntaxKind::ClassDeclaration, "Shared");
        let interface_declaration = named_declaration(
            &fixture,
            interface_file,
            SyntaxKind::InterfaceDeclaration,
            "Shared",
        );
        let class_symbol = declaration_symbol(&fixture, class_declaration);
        let interface_symbol = declaration_symbol(&fixture, interface_declaration);
        let canonical = merge_globals(&mut fixture, &[class_symbol, interface_symbol]);

        assert_ne!(canonical, class_symbol);
        assert_ne!(canonical, interface_symbol);
        assert_eq!(
            fixture.store.get_merged_symbol(class_symbol),
            Some(canonical)
        );
        assert_eq!(
            fixture.store.get_merged_symbol(interface_symbol),
            Some(canonical)
        );
        assert!(
            fixture
                .store
                .symbol(canonical)
                .unwrap()
                .flags()
                .contains(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        );

        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        assert!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("Shared"), class_symbol)
                .is_some()
        );
        {
            let mut host = production_host(&fixture);
            assert_eq!(
                host.symbol_of_declaration(class_declaration),
                Some(canonical)
            );
            assert_eq!(
                host.symbol_of_declaration(interface_declaration),
                Some(canonical)
            );
            assert_eq!(
                resolve_global_name(
                    fixture.store.symbol_store(),
                    &mut host,
                    "Shared",
                    SymbolFlags::TYPE,
                    None,
                    false,
                    false,
                ),
                Ok(Some(canonical))
            );
        }

        let host = declared_host(&fixture.parsed, &fixture.files);
        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class_symbol)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&host, interface_symbol),
            Ok(declared_type)
        );
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, canonical),
            Ok(declared_type)
        );
        assert_eq!(
            fixture.store.type_payload(declared_type).unwrap().symbol(),
            Some(canonical)
        );
        assert!(
            fixture
                .store
                .type_payload(declared_type)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::CLASS)
        );
        assert!(fixture.store.declared_type_links(class_symbol).is_none());
        assert!(
            fixture
                .store
                .declared_type_links(interface_symbol)
                .is_none()
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(canonical)
                .and_then(|links| links.declared_type),
            Some(declared_type)
        );
    }

    #[test]
    fn merged_interfaces_share_one_canonical_declared_cache() {
        let first_file = FileId::new(703);
        let second_file = FileId::new(704);
        let mut fixture = fixture(&[
            (
                first_file,
                "interface Combined<T> { first: T }",
                CanonicalModuleState::Script,
            ),
            (
                second_file,
                "interface Combined<U> { second: U }",
                CanonicalModuleState::Script,
            ),
        ]);
        let first = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                first_file,
                SyntaxKind::InterfaceDeclaration,
                "Combined",
            ),
        );
        let second = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                second_file,
                SyntaxKind::InterfaceDeclaration,
                "Combined",
            ),
        );
        let canonical = merge_globals(&mut fixture, &[first, second]);
        let host = declared_host(&fixture.parsed, &fixture.files);

        let declared_type = fixture
            .store
            .get_declared_type_of_symbol(&host, second)
            .unwrap();
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, first),
            Ok(declared_type)
        );
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&host, canonical),
            Ok(declared_type)
        );
        assert!(matches!(
            fixture.store.type_payload(declared_type).unwrap().data(),
            TypeData::Interface(_)
        ));
        assert!(fixture.store.declared_type_links(first).is_none());
        assert!(fixture.store.declared_type_links(second).is_none());
        assert!(fixture.store.declared_type_links(canonical).is_some());
    }

    #[test]
    fn alias_dependent_lookup_is_an_explicit_error_after_redirect() {
        let file = FileId::new(707);
        let mut fixture = fixture(&[(
            file,
            "import { Imported } from 'pkg';",
            CanonicalModuleState::External,
        )]);
        let bound = &fixture.files[&file];
        let raw = fixture
            .store
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap();
        let raw = raw.get_source("Imported").unwrap();
        let canonical = fixture.store.alloc_transient_symbol(
            SymbolFlags::ALIAS,
            EscapedName::source("Imported"),
            CheckFlags::NONE,
        );
        fixture.store.record_merged_symbol(canonical, raw).unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture
            .store
            .insert_symbol(globals, EscapedName::source("Imported"), raw)
            .unwrap();
        let mut host = production_host(&fixture);

        assert_eq!(
            resolve_global_name(
                fixture.store.symbol_store(),
                &mut host,
                "Imported",
                SymbolFlags::TYPE,
                None,
                false,
                false,
            ),
            Err(CanonicalNameResolutionError::AliasResolutionUnavailable(
                canonical
            ))
        );
        assert_eq!(
            host.lookup_name(
                globals,
                EscapedNameRef::source("Imported"),
                SymbolFlags::ALIAS,
            ),
            Ok(Some(canonical))
        );
        assert_eq!(
            host.lookup_name(
                globals,
                EscapedNameRef::source("Missing"),
                SymbolFlags::TYPE,
            ),
            Ok(None)
        );
    }

    #[test]
    fn qualified_entity_names_follow_nested_namespace_exports() {
        let file = FileId::new(708);
        let mut fixture = fixture(&[(
            file,
            concat!(
                "namespace Outer { export namespace Inner { export interface Shape {} } } ",
                "type Value = Outer.Inner.Shape;",
            ),
            CanonicalModuleState::Script,
        )]);
        let outer = script_namespace_symbol(&fixture, file, "Outer");
        merge_globals(&mut fixture, &[outer]);
        let target = declaration_symbol(
            &fixture,
            named_declaration(&fixture, file, SyntaxKind::InterfaceDeclaration, "Shape"),
        );
        let entity = type_alias_entity_name(&fixture, file, "Value");
        let mut host = production_host(&fixture);

        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(Some(target)),
        );
    }

    #[test]
    fn qualified_entity_names_do_not_expose_private_namespace_members() {
        let file = FileId::new(709);
        let mut fixture = fixture(&[(
            file,
            "namespace Outer { interface Hidden {} } type Value = Outer.Hidden;",
            CanonicalModuleState::Script,
        )]);
        let outer = script_namespace_symbol(&fixture, file, "Outer");
        merge_globals(&mut fixture, &[outer]);
        let entity = type_alias_entity_name(&fixture, file, "Value");
        let mut host = production_host(&fixture);

        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(None)
        );
    }

    #[test]
    fn qualified_entity_names_follow_reopened_namespace_redirects() {
        let first_file = FileId::new(710);
        let second_file = FileId::new(711);
        let mut fixture = fixture(&[
            (
                first_file,
                "declare namespace Shared { interface First {} }",
                CanonicalModuleState::Script,
            ),
            (
                second_file,
                "declare namespace Shared { interface Last {} } type Value = Shared.Last;",
                CanonicalModuleState::Script,
            ),
        ]);
        let first = script_namespace_symbol(&fixture, first_file, "Shared");
        let second = script_namespace_symbol(&fixture, second_file, "Shared");
        merge_globals(&mut fixture, &[first, second]);
        let target = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                second_file,
                SyntaxKind::InterfaceDeclaration,
                "Last",
            ),
        );
        let entity = type_alias_entity_name(&fixture, second_file, "Value");
        let mut host = production_host(&fixture);

        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(Some(target)),
        );
    }

    #[test]
    fn resolved_namespace_import_keeps_alias_lookup_and_resolves_qualified_type() {
        let target_file = FileId::new(712);
        let source_file = FileId::new(713);
        let mut fixture = fixture(&[
            (
                target_file,
                "export interface Shape {}",
                CanonicalModuleState::External,
            ),
            (
                source_file,
                "import * as NS from './target'; type Value = NS.Shape;",
                CanonicalModuleState::External,
            ),
        ]);
        let target_bound = &fixture.files[&target_file];
        let target_module = target_bound.symbol(target_bound.source_file()).unwrap();
        let target = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                target_file,
                SyntaxKind::InterfaceDeclaration,
                "Shape",
            ),
        );
        let parsed = &fixture.parsed[&source_file];
        let import = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NamespaceImport).then_some(NodeRef::new(
                    parsed.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        let alias = fixture.files[&source_file].symbol(import).unwrap();
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(target_module),
                alias_target: AliasTargetState::Resolved(target_module),
                ..AliasSymbolLinks::default()
            },
        ));
        let entity = type_alias_entity_name(&fixture, source_file, "Value");
        let locals = fixture.files[&source_file]
            .locals(fixture.files[&source_file].source_file())
            .unwrap();
        let mut host = production_host(&fixture);

        assert_eq!(
            host.lookup_name(locals, EscapedNameRef::source("NS"), SymbolFlags::NAMESPACE,),
            Ok(Some(alias)),
        );
        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(Some(target)),
        );
    }

    #[test]
    fn import_equals_object_exports_resolve_only_their_modules_exported_types() {
        let target_file = FileId::new(716);
        let source_file = FileId::new(717);
        let mut fixture = fixture(&[
            (
                target_file,
                concat!(
                    "export interface Shape {} ",
                    "export namespace Deep { export interface Item {} } ",
                    "interface Hidden {} ",
                    "export = { value: 1 };",
                ),
                CanonicalModuleState::External,
            ),
            (
                source_file,
                concat!(
                    "import selected = require('./target'); ",
                    "type Shape = selected.Shape; ",
                    "type Item = selected.Deep.Item; ",
                    "type Hidden = selected.Hidden;",
                ),
                CanonicalModuleState::External,
            ),
        ]);
        let alias = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                source_file,
                SyntaxKind::ImportEqualsDeclaration,
                "selected",
            ),
        );
        let module = fixture.files[&target_file]
            .symbol(fixture.files[&target_file].source_file())
            .unwrap();
        let export = fixture
            .store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            .unwrap();
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(export),
                alias_target: AliasTargetState::Resolved(export),
                ..AliasSymbolLinks::default()
            },
        ));
        let shape = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                target_file,
                SyntaxKind::InterfaceDeclaration,
                "Shape",
            ),
        );
        let item = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                target_file,
                SyntaxKind::InterfaceDeclaration,
                "Item",
            ),
        );
        let mut host = production_host(&fixture);

        for _ in 0..2 {
            assert_eq!(
                host.resolve_entity_name(
                    type_alias_entity_name(&fixture, source_file, "Shape"),
                    SymbolFlags::TYPE,
                ),
                Ok(Some(shape)),
            );
            assert_eq!(
                host.resolve_entity_name(
                    type_alias_entity_name(&fixture, source_file, "Item"),
                    SymbolFlags::TYPE,
                ),
                Ok(Some(item)),
            );
            assert_eq!(
                host.resolve_entity_name(
                    type_alias_entity_name(&fixture, source_file, "Hidden"),
                    SymbolFlags::TYPE,
                ),
                Ok(None),
            );
        }

        drop(host);
        let source_module = fixture.files[&source_file]
            .symbol(fixture.files[&source_file].source_file())
            .unwrap();
        assert!(fixture.store.set_symbol_relationships(
            export,
            None,
            None,
            Some(source_module),
            None,
        ));
        assert_eq!(
            production_host(&fixture).resolve_entity_name(
                type_alias_entity_name(&fixture, source_file, "Shape"),
                SymbolFlags::TYPE,
            ),
            Ok(None),
        );
    }

    #[test]
    fn qualified_entity_names_follow_exported_namespace_import_equals_aliases() {
        let file = FileId::new(714);
        let mut fixture = fixture(&[(
            file,
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export interface Shape {} } ",
                "export import Visible = Inner; ",
                "} ",
                "type Value = Outer.Visible.Shape;",
            ),
            CanonicalModuleState::Script,
        )]);
        let outer = script_namespace_symbol(&fixture, file, "Outer");
        let outer = merge_globals(&mut fixture, &[outer]);
        let exports = fixture.store.symbol(outer).unwrap().exports().unwrap();
        let inner = fixture
            .store
            .symbol_table(exports)
            .unwrap()
            .get_source("Inner")
            .unwrap();
        let alias = declaration_symbol(
            &fixture,
            named_declaration(
                &fixture,
                file,
                SyntaxKind::ImportEqualsDeclaration,
                "Visible",
            ),
        );
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(inner),
                alias_target: AliasTargetState::Resolved(inner),
                ..AliasSymbolLinks::default()
            },
        ));
        let target = declaration_symbol(
            &fixture,
            named_declaration(&fixture, file, SyntaxKind::InterfaceDeclaration, "Shape"),
        );
        let entity = type_alias_entity_name(&fixture, file, "Value");
        let mut host = production_host(&fixture);

        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(Some(target)),
        );
    }

    #[test]
    fn qualified_entity_names_follow_private_namespace_import_equals_aliases() {
        let file = FileId::new(715);
        let mut fixture = fixture(&[(
            file,
            concat!(
                "namespace Outer { ",
                "namespace Hidden { export interface Shape {} } ",
                "import Local = Hidden; ",
                "type Value = Local.Shape; ",
                "}",
            ),
            CanonicalModuleState::Script,
        )]);
        let outer = script_namespace_symbol(&fixture, file, "Outer");
        merge_globals(&mut fixture, &[outer]);
        let hidden = declaration_symbol(
            &fixture,
            named_declaration(&fixture, file, SyntaxKind::ModuleDeclaration, "Hidden"),
        );
        let alias = declaration_symbol(
            &fixture,
            named_declaration(&fixture, file, SyntaxKind::ImportEqualsDeclaration, "Local"),
        );
        assert!(fixture.store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                immediate_target: Some(hidden),
                alias_target: AliasTargetState::Resolved(hidden),
                ..AliasSymbolLinks::default()
            },
        ));
        let target = declaration_symbol(
            &fixture,
            named_declaration(&fixture, file, SyntaxKind::InterfaceDeclaration, "Shape"),
        );
        let entity = type_alias_entity_name(&fixture, file, "Value");
        let mut host = production_host(&fixture);

        assert_eq!(
            host.resolve_entity_name(entity, SymbolFlags::TYPE),
            Ok(Some(target)),
        );
    }

    #[test]
    fn declaration_callbacks_canonicalize_export_and_local_symbols() {
        let file = FileId::new(705);
        let mut fixture = fixture(&[(
            file,
            "export interface Exported { value: string }",
            CanonicalModuleState::External,
        )]);
        let declaration =
            named_declaration(&fixture, file, SyntaxKind::InterfaceDeclaration, "Exported");
        let bound = &fixture.files[&file];
        let export = bound.symbol(declaration).unwrap();
        let local = bound.local_symbol(declaration).unwrap();
        let canonical = fixture.store.alloc_transient_symbol(
            SymbolFlags::INTERFACE,
            EscapedName::source("Exported"),
            CheckFlags::NONE,
        );
        fixture
            .store
            .record_merged_symbol(canonical, export)
            .unwrap();
        fixture
            .store
            .record_merged_symbol(canonical, local)
            .unwrap();
        let mut host = production_host(&fixture);

        assert_eq!(host.get_symbol_of_declaration(declaration), Some(canonical));
        assert_eq!(
            host.get_local_symbol_of_declaration(declaration),
            Some(canonical)
        );
    }

    #[test]
    fn redirect_consumers_are_one_hop_and_host_provenance_fails_closed() {
        let file = FileId::new(706);
        let mut fixture = fixture(&[(
            file,
            "interface OneHop { value: string }",
            CanonicalModuleState::Script,
        )]);
        let declaration =
            named_declaration(&fixture, file, SyntaxKind::InterfaceDeclaration, "OneHop");
        let raw = declaration_symbol(&fixture, declaration);
        let middle = fixture.store.alloc_transient_symbol(
            SymbolFlags::FUNCTION,
            EscapedName::source("OneHop"),
            CheckFlags::NONE,
        );
        let final_symbol = fixture.store.alloc_transient_symbol(
            SymbolFlags::INTERFACE,
            EscapedName::source("OneHop"),
            CheckFlags::NONE,
        );
        fixture.store.record_merged_symbol(middle, raw).unwrap();
        fixture
            .store
            .record_merged_symbol(final_symbol, middle)
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture
            .store
            .insert_symbol(globals, EscapedName::source("OneHop"), raw)
            .unwrap();
        let host = production_host(&fixture);

        assert_eq!(fixture.store.get_merged_symbol(raw), Some(middle));
        assert_eq!(host.symbol_of_declaration(declaration), Some(middle));
        assert_eq!(
            host.lookup_name(globals, EscapedNameRef::source("OneHop"), SymbolFlags::TYPE,),
            Ok(None)
        );
        drop(host);
        let declared_host = declared_host(&fixture.parsed, &fixture.files);
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            fixture
                .store
                .get_declared_type_of_symbol(&declared_host, raw),
            Ok(error_type)
        );
        assert!(fixture.store.declared_type_links(raw).is_none());
        assert!(fixture.store.declared_type_links(middle).is_none());
        assert!(fixture.store.declared_type_links(final_symbol).is_none());

        let parsed = &fixture.parsed[&file];
        let mut foreign_binder = CanonicalBinder::new();
        foreign_binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/foreign.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        foreign_binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (_, foreign_files) = foreign_binder.finish().try_into_parts().unwrap();
        assert_eq!(
            ProductionNameResolverHost::new(
                &fixture.store,
                [(&parsed.arena, &foreign_files[&file])],
                CanonicalNameResolverOptions::default(),
            )
            .unwrap_err(),
            ProductionNameResolverHostError::InvalidSymbolStore(file)
        );
    }
}
