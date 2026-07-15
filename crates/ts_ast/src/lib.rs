//! TypeScript syntax model.

mod ast_generated;
mod flow;
mod syntax_kind;

pub use ast_generated::*;
pub use flow::*;
pub use syntax_kind::SyntaxKind;

impl NodeData {
    /// Whether this generated node payload is structurally compatible with a
    /// syntax kind. Most schema names match directly; shared payloads and the
    /// handful of public kind aliases are listed explicitly.
    #[must_use]
    pub fn matches_syntax_kind(&self, kind: SyntaxKind) -> bool {
        match self {
            Self::Token(_) => kind.is_token(),
            Self::KeywordExpression(_) => kind.is_keyword_expression(),
            Self::KeywordTypeNode(_) => kind.is_keyword_type(),
            Self::ForInOrOfStatement(_) => {
                matches!(
                    kind,
                    SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement
                )
            }
            Self::CaseOrDefaultClause(_) => {
                matches!(kind, SyntaxKind::CaseClause | SyntaxKind::DefaultClause)
            }
            Self::BindingPattern(_) => matches!(
                kind,
                SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern
            ),
            Self::JsDocParameterOrPropertyTag(_) => matches!(
                kind,
                SyntaxKind::JsDocParameterTag | SyntaxKind::JsDocPropertyTag
            ),
            Self::TypeAliasDeclaration(_) => matches!(
                kind,
                SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration
            ),
            Self::ImportDeclaration(_) => matches!(
                kind,
                SyntaxKind::ImportDeclaration | SyntaxKind::JsImportDeclaration
            ),
            Self::ParameterDeclaration(_) => kind == SyntaxKind::Parameter,
            Self::CallSignatureDeclaration(_) => kind == SyntaxKind::CallSignature,
            Self::ConstructSignatureDeclaration(_) => kind == SyntaxKind::ConstructSignature,
            Self::ConstructorDeclaration(_) => kind == SyntaxKind::Constructor,
            Self::GetAccessorDeclaration(_) => kind == SyntaxKind::GetAccessor,
            Self::SetAccessorDeclaration(_) => kind == SyntaxKind::SetAccessor,
            Self::IndexSignatureDeclaration(_) => kind == SyntaxKind::IndexSignature,
            Self::MethodSignatureDeclaration(_) => kind == SyntaxKind::MethodSignature,
            Self::PropertySignatureDeclaration(_) => kind == SyntaxKind::PropertySignature,
            Self::TypeParameterDeclaration(_) => kind == SyntaxKind::TypeParameter,
            Self::TypeAssertion(_) => kind == SyntaxKind::TypeAssertionExpression,
            Self::UnionTypeNode(_) => kind == SyntaxKind::UnionType,
            Self::IntersectionTypeNode(_) => kind == SyntaxKind::IntersectionType,
            Self::ConditionalTypeNode(_) => kind == SyntaxKind::ConditionalType,
            Self::TypeOperatorNode(_) => kind == SyntaxKind::TypeOperator,
            Self::InferTypeNode(_) => kind == SyntaxKind::InferType,
            Self::ArrayTypeNode(_) => kind == SyntaxKind::ArrayType,
            Self::IndexedAccessTypeNode(_) => kind == SyntaxKind::IndexedAccessType,
            Self::TypeReferenceNode(_) => kind == SyntaxKind::TypeReference,
            Self::LiteralTypeNode(_) => kind == SyntaxKind::LiteralType,
            Self::ThisTypeNode(_) => kind == SyntaxKind::ThisType,
            Self::TypePredicateNode(_) => kind == SyntaxKind::TypePredicate,
            Self::TypeQueryNode(_) => kind == SyntaxKind::TypeQuery,
            Self::MappedTypeNode(_) => kind == SyntaxKind::MappedType,
            Self::TypeLiteralNode(_) => kind == SyntaxKind::TypeLiteral,
            Self::TupleTypeNode(_) => kind == SyntaxKind::TupleType,
            Self::OptionalTypeNode(_) => kind == SyntaxKind::OptionalType,
            Self::RestTypeNode(_) => kind == SyntaxKind::RestType,
            Self::ParenthesizedTypeNode(_) => kind == SyntaxKind::ParenthesizedType,
            Self::FunctionTypeNode(_) => kind == SyntaxKind::FunctionType,
            Self::ConstructorTypeNode(_) => kind == SyntaxKind::ConstructorType,
            Self::TemplateLiteralTypeNode(_) => kind == SyntaxKind::TemplateLiteralType,
            Self::ImportTypeNode(_) => kind == SyntaxKind::ImportType,
            Self::JsxText(_) => {
                matches!(
                    kind,
                    SyntaxKind::JsxText | SyntaxKind::JsxTextAllWhiteSpaces
                )
            }
            _ => self.schema_name() == kind.as_str(),
        }
    }
}

impl NodeFlags {
    /// The parser synthesized this node while representing source grammar.
    pub const REPARSED: Self = Self(1 << 3);

    /// The node was parsed in JavaScript source context.
    pub const JAVASCRIPT_FILE: Self = Self(1 << 16);
}

impl ModifierFlags {
    /// An `export` declaration modifier.
    pub const EXPORT: Self = Self(1 << 5);
}

/// Stable source-file slot during the lifetime of one compiler `Program`.
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
///
/// The arena identity prevents a reference from another Program with the same
/// file slot and dense node index from aliasing this Program's node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeRef {
    pub arena: NodeArenaId,
    pub file: FileId,
    pub node: NodeId,
}

impl NodeRef {
    #[must_use]
    pub const fn new(arena: NodeArenaId, file: FileId, node: NodeId) -> Self {
        Self { arena, file, node }
    }

    #[must_use]
    pub fn is_for(self, arena: NodeArenaId, file: FileId) -> bool {
        self.arena == arena && self.file == file
    }
}

#[cfg(test)]
mod tests {
    use std::ops::ControlFlow;

    use ts_core::TextRange;

    use super::{
        ConditionalExpressionData, DoStatementData, FileId, ImportDeclarationData,
        JsDocParameterOrPropertyTagData, ModifierFlags, ModifierList, Node, NodeArena, NodeData,
        NodeFlags, NodeId, NodeList, NodeRef, SourceFileData, SymbolTable, SyntaxKind,
        SyntaxListData, TokenData,
    };

    fn node_list(nodes: &[u32]) -> NodeList {
        NodeList {
            range: TextRange::default(),
            nodes: nodes.iter().copied().map(NodeId::new).collect(),
            has_trailing_comma: false,
        }
    }

    fn modifier_list(nodes: &[u32]) -> ModifierList {
        ModifierList {
            list: node_list(nodes),
            flags: ModifierFlags::default(),
        }
    }

    fn direct_children(data: NodeData) -> Vec<NodeId> {
        let node = Node {
            kind: SyntaxKind::Unknown,
            flags: NodeFlags::default(),
            range: TextRange::default(),
            parent: None,
            data,
        };
        let mut children = Vec::new();
        node.for_each_child(|child| children.push(child));
        children
    }

    fn node_ids(nodes: &[u32]) -> Vec<NodeId> {
        nodes.iter().copied().map(NodeId::new).collect()
    }

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
    fn reparsed_node_flag_matches_upstream_bit() {
        assert_eq!(NodeFlags::REPARSED, NodeFlags(1 << 3));
        assert_eq!(ModifierFlags::EXPORT, ModifierFlags(1 << 5));
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
        let first_arena = NodeArena::new();
        let second_arena = NodeArena::new();
        let first = NodeRef::new(first_arena.id(), FileId::new(0), node);
        let second = NodeRef::new(second_arena.id(), FileId::new(1), node);

        assert_ne!(first, second);
        assert_eq!(first.node, second.node);
        assert!(!first.is_for(second_arena.id(), FileId::new(0)));
    }

    #[test]
    fn direct_children_preserve_upstream_field_and_list_order() {
        let cases = vec![
            (
                "do statement visits its body before its condition",
                NodeData::DoStatement(Box::new(DoStatementData {
                    expression: NodeId::new(2),
                    flow_node: None,
                    statement: NodeId::new(1),
                    facts: 0,
                })),
                node_ids(&[1, 2]),
            ),
            (
                "conditional expression includes punctuation tokens",
                NodeData::ConditionalExpression(Box::new(ConditionalExpressionData {
                    colon_token: NodeId::new(4),
                    condition: NodeId::new(1),
                    question_token: NodeId::new(2),
                    when_false: NodeId::new(5),
                    when_true: NodeId::new(3),
                    facts: 0,
                })),
                node_ids(&[1, 2, 3, 4, 5]),
            ),
            (
                "modifier and node lists flatten in place",
                NodeData::ImportDeclaration(Box::new(ImportDeclarationData {
                    attributes: Some(NodeId::new(6)),
                    flow_node: None,
                    import_clause: Some(NodeId::new(3)),
                    module_specifier: NodeId::new(5),
                    symbol: None,
                    facts: 0,
                    modifiers: Some(modifier_list(&[1, 2])),
                })),
                node_ids(&[1, 2, 3, 5, 6]),
            ),
            (
                "source-file statements precede end-of-file",
                NodeData::SourceFile(Box::new(SourceFileData {
                    end_of_file_token: NodeId::new(4),
                    locals: SymbolTable,
                    next_container: None,
                    statements: node_list(&[1, 2, 3]),
                    symbol: None,
                    facts: 0,
                })),
                node_ids(&[1, 2, 3, 4]),
            ),
            (
                "raw syntax-list children retain their order",
                NodeData::SyntaxList(Box::new(SyntaxListData {
                    children: node_ids(&[3, 1, 2]),
                })),
                node_ids(&[3, 1, 2]),
            ),
        ];

        for (description, data, expected) in cases {
            assert_eq!(direct_children(data), expected, "{description}");
        }
    }

    #[test]
    fn jsdoc_parameter_child_order_uses_runtime_name_position() {
        for (is_name_first, expected) in [
            (true, node_ids(&[1, 2, 3, 4, 5])),
            (false, node_ids(&[1, 3, 2, 4, 5])),
        ] {
            let data =
                NodeData::JsDocParameterOrPropertyTag(Box::new(JsDocParameterOrPropertyTagData {
                    comment: Some(node_list(&[4, 5])),
                    is_bracketed: false,
                    is_name_first,
                    tag_name: NodeId::new(1),
                    type_expression: Some(NodeId::new(3)),
                    name: NodeId::new(2),
                }));
            assert_eq!(direct_children(data), expected);
        }
    }

    #[test]
    fn try_for_each_child_stops_at_the_first_break() {
        let node = Node {
            kind: SyntaxKind::SourceFile,
            flags: NodeFlags::default(),
            range: TextRange::default(),
            parent: None,
            data: NodeData::SourceFile(Box::new(SourceFileData {
                end_of_file_token: NodeId::new(4),
                locals: SymbolTable,
                next_container: None,
                statements: node_list(&[1, 2, 3]),
                symbol: None,
                facts: 0,
            })),
        };
        let mut visited = Vec::new();
        let result = node.try_for_each_child(|child| {
            visited.push(child);
            if child == NodeId::new(2) {
                ControlFlow::Break(child)
            } else {
                ControlFlow::Continue(())
            }
        });

        assert_eq!(result, ControlFlow::Break(NodeId::new(2)));
        assert_eq!(visited, node_ids(&[1, 2]));
    }
}
