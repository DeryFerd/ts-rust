//! Exact syntax and symbol plan for the first interface-heritage slice.
//!
//! This module admits direct identifier bases on nongeneric interfaces. It
//! resolves every base before publication so the member resolver never has to
//! guess at an alias, qualified name, or generic instantiation boundary.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolver, CanonicalResolutionLocation, SemanticSymbolId, SymbolFlags,
};

use super::{CanonicalTypeMapperStore, DeclaredTypeHost, declared::preflight_node};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceBasePlan {
    #[allow(dead_code)] // Retained as provenance for generic heritage expansion.
    pub node: NodeRef,
    #[allow(dead_code)] // Retained as the future instantiation diagnostic anchor.
    pub expression: NodeRef,
    pub symbol: SemanticSymbolId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceHeritagePlan {
    pub clause: NodeRef,
    pub bases: Vec<DirectInterfaceBasePlan>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceHeritageError {
    Invalid,
    Unsupported { node: NodeRef, kind: SyntaxKind },
}

pub(super) fn plan_direct_interface_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &NodeList,
) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: declaration,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    };
    let clause = NodeRef::new(declaration.arena, declaration.file, *clause_id);
    let clause_record =
        preflight_node(store, host, clause).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::HeritageClause(clause_data) = &clause_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || clause_data.token != SyntaxKind::ExtendsKeyword
        || clause_data.facts != 0
        || clause_data.types.nodes.is_empty()
        || clause_data.types.has_trailing_comma
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut bases = Vec::with_capacity(clause_data.types.nodes.len());
    let mut seen_nodes = HashSet::with_capacity(clause_data.types.nodes.len());
    let mut seen_symbols = HashSet::with_capacity(clause_data.types.nodes.len());
    let mut previous_end = clause_data.types.range.start;
    for base_id in &clause_data.types.nodes {
        let node = NodeRef::new(declaration.arena, declaration.file, *base_id);
        let node_record =
            preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::ExpressionWithTypeArguments(base) = &node_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node,
                kind: node_record.kind,
            });
        };
        if node_record.kind != SyntaxKind::ExpressionWithTypeArguments
            || node_record.parent != Some(clause.node)
            || node_record.range.start < previous_end
            || node_record.range.start < clause_data.types.range.start
            || node_record.range.end > clause_data.types.range.end
            || base.facts != 0
            || !seen_nodes.insert(node)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        if base.type_arguments.is_some() {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node,
                kind: SyntaxKind::ExpressionWithTypeArguments,
            });
        }
        previous_end = node_record.range.end;

        let expression = NodeRef::new(declaration.arena, declaration.file, base.expression);
        let expression_record = preflight_node(store, host, expression)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::Identifier(identifier) = &expression_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: expression_record.kind,
            });
        };
        if expression_record.kind != SyntaxKind::Identifier
            || expression_record.parent != Some(node.node)
            || expression_record.range.start < node_record.range.start
            || expression_record.range.end > node_record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }

        let resolved = {
            let (arena, bound) = host
                .source(expression)
                .ok_or(DirectInterfaceHeritageError::Invalid)?;
            let mut callback_host = host
                .name_resolver_host(store)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(expression)),
                    &identifier.text,
                    SymbolFlags::TYPE,
                    None,
                    false,
                    false,
                )
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?
        };
        let raw = resolved.ok_or(DirectInterfaceHeritageError::Invalid)?;
        let symbol = store
            .get_merged_symbol(raw)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let symbol_record = store
            .symbol(symbol)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let Some([base_declaration]) = symbol_record.declarations() else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        };
        let base_declaration_record = preflight_node(store, host, *base_declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::InterfaceDeclaration(base_interface) = &base_declaration_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: expression_record.kind,
            });
        };
        if symbol == owner
            || symbol_record.flags() != SymbolFlags::INTERFACE
            || base_declaration_record.kind != SyntaxKind::InterfaceDeclaration
            || base_interface.type_parameters.is_some()
            || !host.symbol_matches(store, *base_declaration, symbol)
            || !seen_symbols.insert(symbol)
        {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        }
        bases.push(DirectInterfaceBasePlan {
            node,
            expression,
            symbol,
        });
    }

    Ok(DirectInterfaceHeritagePlan { clause, bases })
}
