//! Production construction boundary for the canonical checker core.
//!
//! This module adopts declaration-complete canonical binder output into one
//! checker-owned semantic store. Construction includes the dependency-closed
//! prefix of typescript-go's `initializeChecker`: ordered global merging,
//! deferred ambient-module collection, UMD globals, global-scope
//! augmentations, and the built-in `undefined` conflict rule. Alias-dependent
//! merging, checker diagnostics, global library types, and non-global module
//! augmentations remain explicit typed boundaries.

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
    CanonicalTypeMapperStore, IntrinsicBootstrapError, IntrinsicBootstrapOptions, SourceFileRef,
    SymbolMergeError,
    name_resolution::{ProductionNameResolverHost, ProductionNameResolverHostError},
};

#[derive(Debug)]
struct CanonicalCheckerFile<'arena> {
    arena: &'arena NodeArena,
    bound: BoundFile,
    source_file: SourceFileRef,
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
    file_order: Vec<FileId>,
    files: BTreeMap<FileId, CanonicalCheckerFile<'arena>>,
    store: CanonicalTypeMapperStore,
    globals: SymbolTableId,
    pending_ambient_modules: Vec<SemanticSymbolId>,
    pattern_ambient_modules: Vec<CanonicalPatternAmbientModule>,
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
        bootstrap_options: IntrinsicBootstrapOptions,
    ) -> Result<Self, CanonicalCheckerContextError> {
        let (symbols, mut bound_files) = bindings
            .try_into_parts()
            .map_err(CanonicalCheckerContextError::Extraction)?;

        preflight_program(&symbols, &bound_files, &ordered_arenas)?;

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
            .initialize_intrinsic_bootstrap(bootstrap_options)
            .map_err(CanonicalCheckerContextError::Bootstrap)?;

        let mut files = BTreeMap::new();
        for (file, arena, source_file) in registered {
            let Some(bound) = bound_files.remove(&file) else {
                return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
            };
            files.insert(
                file,
                CanonicalCheckerFile {
                    arena,
                    bound,
                    source_file,
                },
            );
        }
        if let Some(file) = bound_files.keys().next().copied() {
            return Err(CanonicalCheckerContextError::SourceRegistrationFailed(file));
        }

        let initialized = initialize_globals(&mut store, &file_order, &files)
            .map_err(CanonicalCheckerContextError::GlobalInitialization)?;

        Ok(Self {
            file_order,
            files,
            store,
            globals: initialized.globals,
            pending_ambient_modules: initialized.pending_ambient_modules,
            pattern_ambient_modules: initialized.pattern_ambient_modules,
        })
    }

    /// The exact caller-supplied Program order used for source registration.
    #[must_use]
    pub fn file_order(&self) -> &[FileId] {
        &self.file_order
    }

    /// Returns the exact AST arena and completed binder side data for `file`.
    #[must_use]
    pub fn file(&self, file: FileId) -> Option<(&'arena NodeArena, &BoundFile)> {
        self.files
            .get(&file)
            .map(|entry| (entry.arena, &entry.bound))
    }

    /// Returns the checker-validated source-root identity for `file`.
    #[must_use]
    pub fn source_file(&self, file: FileId) -> Option<SourceFileRef> {
        self.files.get(&file).map(|entry| entry.source_file)
    }

    /// The canonical checker store, preserving the binder symbol-store brand.
    #[must_use]
    pub const fn store(&self) -> &CanonicalTypeMapperStore {
        &self.store
    }

    /// The bootstrap-owned global symbol table after the supported
    /// `initializeChecker` prefix completed.
    #[must_use]
    pub const fn globals(&self) -> SymbolTableId {
        self.globals
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
        ProductionNameResolverHost::new(
            &self.store,
            self.files.values().map(|file| (file.arena, &file.bound)),
            options,
        )
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
    pending_ambient_modules: Vec<SemanticSymbolId>,
    pattern_ambient_modules: Vec<CanonicalPatternAmbientModule>,
}

#[allow(clippy::too_many_lines)] // Preserves pinned initializeChecker phase order visibly.
fn initialize_globals(
    store: &mut CanonicalTypeMapperStore,
    file_order: &[FileId],
    files: &BTreeMap<FileId, CanonicalCheckerFile<'_>>,
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
        let entry = files
            .get(&file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        let facts = entry.bound.source_facts().ok_or(
            CanonicalGlobalInitializationError::MissingSourceFileFacts(file),
        )?;

        if !facts.is_external_or_common_js_module()
            && let Some(locals) = entry.bound.locals(entry.bound.source_file())
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

        pattern_ambient_modules.extend_from_slice(entry.bound.pattern_ambient_modules());

        if let Some(global_exports) = entry.bound.global_exports() {
            if entry.bound.symbol(entry.bound.source_file()).is_none() {
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
        let entry = files
            .get(&file)
            .ok_or(CanonicalGlobalInitializationError::MissingFile(file))?;
        for &augmentation_name in entry.bound.module_augmentations() {
            let module = validate_augmentation_name(entry, file, augmentation_name)?;
            let Some(NodeData::ModuleDeclaration(module_data)) =
                entry.arena.get(module.node).map(|node| &node.data)
            else {
                return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
                    augmentation_name,
                ));
            };
            if module_data.keyword != SyntaxKind::GlobalKeyword {
                continue;
            }
            let symbol = entry
                .bound
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

    Ok(GlobalInitialization {
        globals,
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
    entry: &CanonicalCheckerFile<'_>,
    file: FileId,
    name: NodeRef,
) -> Result<NodeRef, CanonicalGlobalInitializationError> {
    if !name.is_for(entry.arena.id(), file) || !entry.bound.contains(name) {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    }
    let Some(name_node) = entry.arena.get(name.node) else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    let Some(module_id) = name_node.parent else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    let module = NodeRef::new(entry.arena.id(), file, module_id);
    let Some(NodeData::ModuleDeclaration(module_data)) =
        entry.arena.get(module_id).map(|node| &node.data)
    else {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    };
    if module_data.name != name.node || !entry.bound.contains(module) {
        return Err(CanonicalGlobalInitializationError::InvalidAugmentationName(
            name,
        ));
    }
    Ok(module)
}

fn add_undefined_to_globals(
    store: &mut CanonicalTypeMapperStore,
    files: &BTreeMap<FileId, CanonicalCheckerFile<'_>>,
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
    files: &BTreeMap<FileId, CanonicalCheckerFile<'_>>,
    declaration: NodeRef,
) -> Result<bool, CanonicalGlobalInitializationError> {
    let entry = files
        .get(&declaration.file)
        .ok_or(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration))?;
    if !declaration.is_for(entry.arena.id(), declaration.file) || !entry.bound.contains(declaration)
    {
        return Err(CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration));
    }
    let node = entry
        .arena
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
            let Some(parent) = node.parent.and_then(|parent| entry.arena.get(parent)) else {
                return Err(
                    CanonicalGlobalInitializationError::InvalidDeclarationProvenance(declaration),
                );
            };
            let Some(container) = parent.parent.and_then(|parent| entry.arena.get(parent)) else {
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
            Self::Merge(error) => write!(formatter, "global symbol merge failed: {error}"),
        }
    }
}

impl std::error::Error for CanonicalGlobalInitializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
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
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;

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
        let options = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
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
        assert_eq!(bootstrap.options, options);
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
        let augmentation_name = bound.module_augmentations()[0];
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
