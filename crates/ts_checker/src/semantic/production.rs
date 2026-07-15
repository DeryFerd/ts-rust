//! Production construction boundary for the canonical checker core.
//!
//! This module adopts declaration-complete canonical binder output into one
//! checker-owned semantic store. Construction stops immediately after ordered
//! source-file registration and intrinsic bootstrap. In particular, this is
//! intentionally before typescript-go's `initializeChecker` global merge,
//! alias resolution, and compiler-host adapter work.

use std::collections::{BTreeMap, BTreeSet};

use ts_ast::{
    FileId, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalExtractionError, CanonicalProgramBindings, SemanticStoreId, SymbolStore,
};

use super::{
    CanonicalTypeMapperStore, IntrinsicBootstrapError, IntrinsicBootstrapOptions, SourceFileRef,
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
}

impl<'arena> CanonicalCheckerContext<'arena> {
    /// Atomically adopts completed binder state, registers every source root
    /// in the supplied Program order, and initializes intrinsic checker state.
    ///
    /// Binder extraction, exact Program correspondence, and source-root
    /// validation run before a checker store is created. Full-tree source
    /// registration and bootstrap then write only to a local store, which is
    /// dropped on failure, so callers can never observe a partial context.
    ///
    /// # Errors
    ///
    /// Returns [`CanonicalCheckerContextError`] when declaration extraction,
    /// the exact file/arena correspondence, source-root provenance, source
    /// registration, or intrinsic bootstrap fails.
    pub fn new(
        bindings: CanonicalProgramBindings,
        ordered_arenas: Vec<(FileId, &'arena NodeArena)>,
        bootstrap_options: IntrinsicBootstrapOptions,
    ) -> Result<Self, CanonicalCheckerContextError> {
        let (symbols, mut bound_files) = bindings
            .try_into_parts()
            .map_err(CanonicalCheckerContextError::Extraction)?;

        preflight_program(&symbols, &bound_files, &ordered_arenas)?;

        let file_order = ordered_arenas.iter().map(|(file, _)| *file).collect();
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

        Ok(Self {
            file_order,
            files,
            store,
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

    /// The brand shared by adopted binder symbols and checker-owned records.
    #[must_use]
    pub fn id(&self) -> SemanticStoreId {
        self.store.id()
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
        }
    }
}

impl std::error::Error for CanonicalCheckerContextError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Extraction(error) => Some(error),
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

#[cfg(test)]
mod tests {
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn source_facts(file: FileId) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
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
