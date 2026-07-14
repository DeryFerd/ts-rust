//! TypeScript syntax model.

mod ast_generated;
mod syntax_kind;

pub use ast_generated::*;
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
    fn node_refs_disambiguate_file_local_node_ids() {
        let node = super::NodeId::new(7);
        let first = NodeRef::new(FileId::new(0), node);
        let second = NodeRef::new(FileId::new(1), node);

        assert_ne!(first, second);
        assert_eq!(first.node, second.node);
    }
}
