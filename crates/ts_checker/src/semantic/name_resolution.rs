//! Production host callbacks for canonical name resolution.
//!
//! The binder resolver deliberately delegates checker semantics for merged
//! symbols and aliases. This host supplies the dependency-closed production
//! portion: declaration and table entries follow exactly one validated merge
//! redirect before their flags are observed. Alias resolution is not yet in
//! the port, so a lookup that actually needs alias target flags fails with an
//! explicit capability error instead of becoming an ordinary missing name.

use std::collections::BTreeMap;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolverHost,
    CanonicalNameResolverOptions, EscapedNameRef, SemanticStoreId, SemanticSymbolId, SymbolFlags,
    SymbolStore, SymbolTableId, canonical_has_syntactic_modifier,
};

use super::{CanonicalTypeMapperStore, alias_provider::ProductionAliasSourceRegistry};

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
        })
    }

    /// Pinned checker `getSymbolOfDeclaration`: read the binder-owned node
    /// symbol and follow exactly one merged-symbol redirect.
    #[must_use]
    pub fn symbol_of_declaration(&self, declaration: NodeRef) -> Option<SemanticSymbolId> {
        let raw = self.source(declaration)?.bound.symbol(declaration)?;
        self.store.get_merged_symbol(raw)
    }

    /// Pinned checker table lookup for the currently dependency-closed alias
    /// surface.
    ///
    /// An absent or wrong-meaning non-alias is an ordinary miss. A symbol whose
    /// alias target flags are required returns an explicit capability error.
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
        let flags = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?
            .flags();
        if flags.intersects(meaning) {
            return Ok(Some(symbol));
        }
        if flags.contains(SymbolFlags::ALIAS) {
            return Err(CanonicalNameResolutionError::AliasResolutionUnavailable(
                symbol,
            ));
        }
        Ok(None)
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
        self.lookup_name(symbols, name, meaning)
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
        DeclaredTypeHost, IntrinsicBootstrapOptions, TypeData, TypeMapper, TypeRecord,
        types::ObjectFlags,
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
