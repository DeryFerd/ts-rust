//! Exact syntax and symbol plan for the first interface-heritage slice.
//!
//! This module admits one or two direct identifier bases on nongeneric
//! interfaces, including bases assembled from merged interface declarations.
//! It also authenticates the exact `Record<string, any>` mapped-alias base.
//! Every base is resolved before publication so member construction retains
//! its declaration identity and, for mapped bases, its source type arguments.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolver, CanonicalResolutionLocation, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, declared::preflight_node,
    mapped_types::plan_mapped_type_declaration,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceBaseKind {
    Interface,
    RecordMappedAlias,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceBasePlan {
    pub node: NodeRef,
    #[allow(dead_code)] // Retained as the instantiation diagnostic anchor.
    pub expression: NodeRef,
    pub symbol: SemanticSymbolId,
    pub kind: DirectInterfaceBaseKind,
    pub type_arguments: Vec<NodeRef>,
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

        let type_arguments = match base.type_arguments.as_ref() {
            None => Vec::new(),
            Some(arguments) => {
                if identifier.text != "Record" || clause_data.types.nodes.len() != 1 {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node,
                        kind: SyntaxKind::ExpressionWithTypeArguments,
                    });
                }
                plan_record_type_arguments(store, host, node, arguments)?
            }
        };

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
        if symbol == owner || !seen_symbols.insert(symbol) {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        }
        if !type_arguments.is_empty() {
            if symbol_record.flags() != SymbolFlags::TYPE_ALIAS
                || !authenticate_record_mapped_alias(store, host, symbol, base_declarations)?
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
                kind: DirectInterfaceBaseKind::RecordMappedAlias,
                type_arguments,
            });
            continue;
        }
        if symbol_record.flags() != SymbolFlags::INTERFACE {
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
            kind: DirectInterfaceBaseKind::Interface,
            type_arguments,
        });
    }

    Ok(DirectInterfaceHeritagePlan { clause, bases })
}

fn plan_record_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    arguments: &NodeList,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression = NodeRef::new(node.arena, node.file, base.expression);
    let expression_record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.nodes.len() != 2 {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node,
            kind: SyntaxKind::ExpressionWithTypeArguments,
        });
    }
    if arguments.has_trailing_comma
        || arguments.range.start < expression_record.range.end
        || arguments.range.end != record.range.end
        || arguments.range.start >= arguments.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut nodes = Vec::with_capacity(arguments.nodes.len());
    let mut previous_end = expression_record.range.end;
    for (argument, expected_kind) in arguments
        .nodes
        .iter()
        .zip([SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword])
    {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || argument_record.range.start <= arguments.range.start
            || argument_record.range.end >= arguments.range.end
            || argument_record.range.start < record.range.start
            || argument_record.range.end > record.range.end
            || nodes.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        if argument_record.kind != expected_kind {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: argument,
                kind: argument_record.kind,
            });
        }
        previous_end = argument_record.range.end;
        nodes.push(argument);
    }
    Ok(nodes)
}

fn authenticate_record_mapped_alias(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<bool, DirectInterfaceHeritageError> {
    let [declaration] = declarations else {
        return Ok(false);
    };
    let record = preflight_node(store, host, *declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
        return Ok(false);
    };
    let Some(parameters) = alias.type_parameters.as_ref() else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::TypeAliasDeclaration
        || !host.symbol_matches(store, *declaration, symbol)
        || parameters.nodes.len() != 2
        || parameters.has_trailing_comma
    {
        return Ok(false);
    }
    let name = NodeRef::new(declaration.arena, declaration.file, alias.name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if name_record.parent != Some(declaration.node)
        || !matches!(&name_record.data, NodeData::Identifier(name) if name.text == "Record")
    {
        return Ok(false);
    }

    let mut parameter_symbols = Vec::with_capacity(parameters.nodes.len());
    let mut key_constraint = None;
    for (index, parameter) in parameters.nodes.iter().enumerate() {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let parameter_record = preflight_node(store, host, parameter)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
            return Ok(false);
        };
        let parameter_symbol = host
            .bound_file(parameter)
            .and_then(|bound| bound.symbol(parameter))
            .and_then(|parameter_symbol| store.get_merged_symbol(parameter_symbol));
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.parent != Some(declaration.node)
            || data.default_type.is_some()
            || data.expression.is_some()
            || parameter_symbol.is_none_or(|parameter_symbol| {
                !host.symbol_matches(store, parameter, parameter_symbol)
                    || store.symbol(parameter_symbol).is_none_or(|record| {
                        record.flags() != SymbolFlags::TYPE_PARAMETER
                            || record.declarations() != Some(std::slice::from_ref(&parameter))
                    })
            })
        {
            return Ok(false);
        }
        match (index, data.constraint) {
            (0, Some(constraint)) => {
                key_constraint = Some(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    constraint,
                ));
            }
            (1, None) => {}
            _ => return Ok(false),
        }
        parameter_symbols.push(parameter_symbol.expect("a parameter symbol was authenticated"));
    }
    if parameter_symbols[0] == parameter_symbols[1] {
        return Ok(false);
    }

    let constraint = key_constraint.expect("the first parameter constraint was authenticated");
    let constraint_record = preflight_node(store, host, constraint)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeOperatorNode(operator) = &constraint_record.data else {
        return Ok(false);
    };
    let key_parameter = NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
    let operand = NodeRef::new(constraint.arena, constraint.file, operator.type_);
    let operand_record =
        preflight_node(store, host, operand).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if constraint_record.kind != SyntaxKind::TypeOperator
        || constraint_record.parent != Some(key_parameter.node)
        || operator.operator != SyntaxKind::KeyOfKeyword
        || operand_record.kind != SyntaxKind::AnyKeyword
        || operand_record.parent != Some(constraint.node)
    {
        return Ok(false);
    }

    let mapped_node = NodeRef::new(declaration.arena, declaration.file, alias.type_);
    let mapped_record = preflight_node(store, host, mapped_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if mapped_record.parent != Some(declaration.node) {
        return Ok(false);
    }
    let Ok(mapped) = plan_mapped_type_declaration(store, host, mapped_node) else {
        return Ok(false);
    };
    let Some(template) = mapped.template() else {
        return Ok(false);
    };
    if mapped.name_type().is_some()
        || mapped.modifiers_source().is_some()
        || mapped.modifiers().bits() != 0
    {
        return Ok(false);
    }
    for (reference, expected) in [
        (mapped.constraint(), parameter_symbols[0]),
        (template, parameter_symbols[1]),
    ] {
        let reference_record = preflight_node(store, host, reference)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::TypeReferenceNode(data) = &reference_record.data else {
            return Ok(false);
        };
        let reference_name = NodeRef::new(reference.arena, reference.file, data.type_name);
        let reference_name_record = preflight_node(store, host, reference_name)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if reference_record.kind != SyntaxKind::TypeReference
            || data.type_arguments.is_some()
            || reference_name_record.parent != Some(reference.node)
            || !matches!(reference_name_record.data, NodeData::Identifier(_))
        {
            return Ok(false);
        }
        let mut callback_host = host
            .name_resolver_host(store)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let resolved = callback_host
            .resolve_entity_name(reference_name, SymbolFlags::TYPE)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?
            .and_then(|resolved| store.get_merged_symbol(resolved));
        if resolved != Some(expected) {
            return Ok(false);
        }
    }
    Ok(true)
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
        production::GlobalMergeCompletion,
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

    fn heritage_plan(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
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
        let NodeData::InterfaceDeclaration(interface) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!("the declaration was selected by its interface payload")
        };
        let (arena, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        plan_direct_interface_heritage(
            context.store(),
            &host,
            declaration,
            interface_symbol(parsed, file, context, expected),
            interface.heritage_clauses.as_ref().unwrap(),
        )
    }

    #[test]
    fn record_mapped_alias_base_retains_authenticated_type_arguments() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T };\n",
            "declare namespace JSX {\n",
            "  interface IntrinsicElements extends Record<string, any> {}\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_403);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = heritage_plan(&parsed, file, &context, "IntrinsicElements").unwrap();
        let [base] = plan.bases.as_slice() else {
            panic!("the mapped alias must remain the only direct base")
        };
        assert_eq!(base.kind, DirectInterfaceBaseKind::RecordMappedAlias);
        assert_eq!(
            base.type_arguments
                .iter()
                .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword]
        );
        assert_eq!(
            context.store().symbol(base.symbol).unwrap().flags(),
            SymbolFlags::TYPE_ALIAS
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
    }

    #[test]
    fn record_mapped_alias_lookalikes_remain_unsupported() {
        let cases = [
            concat!(
                "type Record<K extends string, T> = { [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T = number> = { [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { readonly [P in K]: T };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: K };\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
            concat!(
                "type Record<K extends keyof any, T> = { [P in K]: T };\n",
                "interface Derived extends Record<string, number> {}\n",
            ),
            concat!(
                "interface Record<K, T> {}\n",
                "interface Derived extends Record<string, any> {}\n",
            ),
        ];

        for (index, source) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_410 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: {source}"
            );
        }
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
