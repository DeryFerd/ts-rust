//! TypeScript syntax model.

mod ast_generated;
mod flow;
mod syntax_kind;

pub use ast_generated::*;
pub use flow::*;
pub use syntax_kind::SyntaxKind;

/// Stable identifier for one source-file arena during the lifetime of one
/// compiler `Program`.
///
/// `NodeId` is intentionally dense and file-local. Pair it with `FileId` before
/// storing a node identity in program-wide semantic state. File IDs are not
/// persistent identities: rebuilding a Program may assign a different ID to
/// the same path.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileId(u32);

impl FileId {
    #[must_use]
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Unambiguous identity for an AST node in a compiler Program.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeRef {
    pub file: FileId,
    pub node: NodeId,
}

impl NodeRef {
    #[must_use]
    pub const fn new(file: FileId, node: NodeId) -> Self {
        Self { file, node }
    }
}

#[cfg(test)]
mod tests {
    use ts_core::TextRange;

    use super::{FileId, Node, NodeArena, NodeData, NodeFlags, NodeRef, SyntaxKind, TokenData};

    #[test]
    fn arena_assigns_stable_dense_node_ids() {
        assert_eq!(NodeData::SCHEMA_NODE_COUNT, 192);
        assert_eq!(NodeData::SCHEMA_BASE_COUNT, 35);
        assert_eq!(NodeData::SCHEMA_NODE_ALIAS_COUNT, 72);
        assert_eq!(NodeData::SCHEMA_LIST_ALIAS_COUNT, 23);

        let mut arena = NodeArena::new();
        arena.set_source_text("const value = 1;");
        let first = arena.alloc(Node {
            kind: SyntaxKind::EndOfFile,
            flags: NodeFlags::default(),
            range: TextRange::default(),
            parent: None,
            data: NodeData::Token(Box::new(TokenData)),
        });
        let second = arena.alloc(Node {
            kind: SyntaxKind::EndOfFile,
            flags: NodeFlags::default(),
            range: TextRange::default(),
            parent: None,
            data: NodeData::Token(Box::new(TokenData)),
        });

        assert_eq!(first.index(), 0);
        assert_eq!(second.index(), 1);
        assert_eq!(arena.get(first).unwrap().kind, SyntaxKind::EndOfFile);
        assert_eq!(arena.iter().count(), 2);
        assert_eq!(arena.source_text(), Some("const value = 1;"));
    }

    #[test]
    fn arena_identity_survives_moves_and_changes_across_clones() {
        let arena = NodeArena::new();
        let identity = arena.id();
        let moved = arena;
        assert_eq!(moved.id(), identity);

        let cloned = moved.clone();
        assert_ne!(cloned.id(), identity);
        assert_ne!(NodeArena::default().id(), identity);

        let mut clone_target = NodeArena::new();
        let clone_target_identity = clone_target.id();
        clone_target.clone_from(&moved);
        assert_ne!(clone_target.id(), clone_target_identity);
        assert_ne!(clone_target.id(), identity);
        assert_eq!(format!("{identity:?}"), "NodeArenaId");
    }

    #[test]
    fn arena_identity_allocation_fails_permanently_before_wrapping() {
        use std::sync::atomic::{AtomicU64, Ordering};

        let counter = AtomicU64::new(u64::MAX - 1);
        let _last_identity = super::ast_generated::allocate_node_arena_id_from(&counter);
        assert_eq!(counter.load(Ordering::Relaxed), u64::MAX);

        for _ in 0..2 {
            assert!(
                std::panic::catch_unwind(|| {
                    super::ast_generated::allocate_node_arena_id_from(&counter)
                })
                .is_err()
            );
            assert_eq!(counter.load(Ordering::Relaxed), u64::MAX);
        }
    }

    #[test]
    fn node_refs_disambiguate_file_local_node_ids() {
        let node = super::NodeId::new(7);
        let first = NodeRef::new(FileId::new(0), node);
        let second = NodeRef::new(FileId::new(1), node);

        assert_ne!(first, second);
        assert_eq!(first.node, second.node);
    }
}
