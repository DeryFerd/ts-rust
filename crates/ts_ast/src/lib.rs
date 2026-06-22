//! TypeScript syntax model.

mod ast_generated;
mod syntax_kind;

pub use ast_generated::*;
pub use syntax_kind::SyntaxKind;

#[cfg(test)]
mod tests {
    use ts_core::TextRange;

    use super::{Node, NodeArena, NodeData, NodeFlags, SyntaxKind, TokenData};

    #[test]
    fn arena_assigns_stable_dense_node_ids() {
        assert_eq!(NodeData::SCHEMA_NODE_COUNT, 192);
        assert_eq!(NodeData::SCHEMA_BASE_COUNT, 35);
        assert_eq!(NodeData::SCHEMA_NODE_ALIAS_COUNT, 72);
        assert_eq!(NodeData::SCHEMA_LIST_ALIAS_COUNT, 23);

        let mut arena = NodeArena::new();
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
    }
}
