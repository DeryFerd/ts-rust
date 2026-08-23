//! Exact syntax and symbol plan for the first interface-heritage slice.
//!
//! This module admits one or two direct identifier bases on nongeneric
//! interfaces, including bases assembled from merged interface declarations.
//! It resolves every base before publication so the member resolver never has
//! to guess at an alias, qualified name, or generic instantiation boundary.

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
    if clause_data.types.nodes.len() > 2 {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: clause,
            kind: SyntaxKind::HeritageClause,
        });
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
        let Some(base_declarations) = symbol_record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        };
        if symbol == owner
            || symbol_record.flags() != SymbolFlags::INTERFACE
            || !seen_symbols.insert(symbol)
        {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        }
        let mut seen_declarations = HashSet::with_capacity(base_declarations.len());
        for &base_declaration in base_declarations {
            let base_declaration_record = preflight_node(store, host, base_declaration)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            let NodeData::InterfaceDeclaration(base_interface) = &base_declaration_record.data
            else {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            };
            if base_declaration_record.kind != SyntaxKind::InterfaceDeclaration
                || base_interface.type_parameters.is_some()
                || base_interface.heritage_clauses.is_some()
                || !host.symbol_matches(store, base_declaration, symbol)
            {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: SyntaxKind::Identifier,
                });
            }
            if !seen_declarations.insert(base_declaration) {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
        }
        bases.push(DirectInterfaceBasePlan {
            node,
            expression,
            symbol,
        });
    }

    Ok(DirectInterfaceHeritagePlan { clause, bases })
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeData,
    };

    fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/merged-interface-heritage.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn interface_symbol(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        context.store().get_merged_symbol(symbol).unwrap()
    }

    #[test]
    fn merged_interface_bases_preserve_member_order_and_warm_state() {
        let parsed = parse_source_file(concat!(
            "interface Base { first: string; shared: number }\n",
            "interface Base { shared: number; second: boolean }\n",
            "interface Derived extends Base { own: string }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_401);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let derived = interface_symbol(&parsed, file, &context, "Derived");

        context.check_source_file(file).unwrap();

        let base_type = context
            .store()
            .declared_type_links(base)
            .and_then(|links| links.declared_type)
            .unwrap();
        let derived_type = context
            .store()
            .declared_type_links(derived)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            context.store().type_payload(derived_type).unwrap().data()
        else {
            panic!("a derived interface must retain its interface type");
        };
        assert_eq!(
            interface.resolved_base_types.as_deref(),
            Some(&[base_type][..])
        );
        let property_names = interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap()
            .iter()
            .map(|property| {
                context
                    .store()
                    .symbol(*property)
                    .and_then(|property| property.name().as_utf8())
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(property_names, ["own", "first", "shared", "second"]);
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }

    #[test]
    fn merged_generic_interface_bases_remain_unsupported_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { first: T }\n",
            "interface Base<T> { second: T }\n",
            "interface Derived extends Base<number> { own: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_402);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let derived = interface_symbol(&parsed, file, &context, "Derived");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(_))
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
        assert!(context.store().declared_type_links(base).is_none());
        assert!(context.store().declared_type_links(derived).is_none());
        assert!(context.diagnostics().is_empty());
    }
}
