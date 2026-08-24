//! Exact syntax and symbol plan for the first interface-heritage slice.
//!
//! This module admits one or two interface bases, including merged
//! declarations, authenticated namespace exports, forwarded generic type
//! parameters, concrete generic instantiations, bounded base chains, and
//! merged default-library DOM interface/value identities.
//! It also authenticates the exact `Record<string, any>` mapped-alias base.
//! Every base is resolved before publication so member construction retains
//! its declaration identity and, for mapped bases, its source type arguments.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolver, CanonicalResolutionLocation, CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, TypeData,
    declared::{explicit_type_parameter_symbols, preflight_node},
    mapped_types::plan_mapped_type_declaration,
    types::ObjectFlags,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectInterfaceBaseKind {
    Interface,
    DefaultLibraryInterface,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HeritageTypeParameterAnnotations {
    Reject,
    Defer,
}

const MAX_INTERFACE_HERITAGE_DEPTH: usize = 16;

pub(super) fn plan_direct_interface_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &NodeList,
) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
    plan_direct_interface_heritage_inner(
        store,
        host,
        declaration,
        owner,
        clauses,
        &mut HashSet::from([owner]),
        0,
    )
}

fn plan_direct_interface_heritage_inner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    clauses: &NodeList,
    active: &mut HashSet<SemanticSymbolId>,
    depth: usize,
) -> Result<DirectInterfaceHeritagePlan, DirectInterfaceHeritageError> {
    if !active.contains(&owner) {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: declaration,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    }
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
        let identifier = match &expression_record.data {
            NodeData::Identifier(identifier)
                if expression_record.kind == SyntaxKind::Identifier =>
            {
                Some(identifier)
            }
            NodeData::PropertyAccessExpression(_)
                if expression_record.kind == SyntaxKind::PropertyAccessExpression =>
            {
                None
            }
            NodeData::QualifiedName(_) if expression_record.kind == SyntaxKind::QualifiedName => {
                None
            }
            _ => {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
        };
        if expression_record.parent != Some(node.node)
            || expression_record.range.start < node_record.range.start
            || expression_record.range.end > node_record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }

        let resolved = if let Some(identifier) = identifier {
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
        } else {
            Some(resolve_qualified_interface_base(store, host, expression)?)
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
        if active.contains(&symbol) || !seen_symbols.insert(symbol) {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: expression_record.kind,
            });
        }
        let type_arguments = match base.type_arguments.as_ref() {
            None => Vec::new(),
            Some(arguments) if symbol_record.flags() == SymbolFlags::TYPE_ALIAS => {
                if identifier.is_none_or(|identifier| identifier.text != "Record")
                    || clause_data.types.nodes.len() != 1
                    || !authenticate_record_mapped_alias(store, host, symbol, base_declarations)?
                {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node: expression,
                        kind: expression_record.kind,
                    });
                }
                plan_record_type_arguments(store, host, node, arguments)?
            }
            Some(arguments)
                if symbol_record.flags().without(SymbolFlags::TRANSIENT)
                    == SymbolFlags::INTERFACE =>
            {
                let owner_record = preflight_node(store, host, declaration)
                    .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
                let NodeData::InterfaceDeclaration(owner_interface) = &owner_record.data else {
                    return Err(DirectInterfaceHeritageError::Invalid);
                };
                if owner_interface.type_parameters.is_some() {
                    plan_forwarded_interface_type_arguments(
                        store,
                        host,
                        declaration,
                        owner,
                        node,
                        symbol,
                        base_declarations,
                        arguments,
                    )?
                } else {
                    plan_concrete_interface_type_arguments(
                        store,
                        host,
                        declaration,
                        owner,
                        node,
                        symbol,
                        base_declarations,
                        arguments,
                    )?
                }
            }
            Some(_) => {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node,
                    kind: SyntaxKind::ExpressionWithTypeArguments,
                });
            }
        };
        if symbol_record.flags() == SymbolFlags::TYPE_ALIAS {
            if type_arguments.is_empty() {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
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
        if symbol_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE {
            if authenticate_default_library_interface_base(store, host, symbol, base_declarations)?
            {
                bases.push(DirectInterfaceBasePlan {
                    node,
                    expression,
                    symbol,
                    kind: DirectInterfaceBaseKind::DefaultLibraryInterface,
                    type_arguments,
                });
                continue;
            }
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: expression_record.kind,
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
                || base_interface.type_parameters.is_some() == type_arguments.is_empty()
                || !host.symbol_matches(store, base_declaration, symbol)
            {
                return Err(DirectInterfaceHeritageError::Unsupported {
                    node: expression,
                    kind: expression_record.kind,
                });
            }
            if !seen_declarations.insert(base_declaration) {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
            if let Some(inherited) = base_interface.heritage_clauses.as_ref() {
                if !active.insert(symbol) {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node: expression,
                        kind: expression_record.kind,
                    });
                }
                let planned = plan_direct_interface_heritage_inner(
                    store,
                    host,
                    base_declaration,
                    symbol,
                    inherited,
                    active,
                    depth + 1,
                );
                assert!(active.remove(&symbol));
                let planned = planned?;
                if planned
                    .bases
                    .iter()
                    .any(|base| base.kind != DirectInterfaceBaseKind::Interface)
                {
                    return Err(DirectInterfaceHeritageError::Unsupported {
                        node: expression,
                        kind: expression_record.kind,
                    });
                }
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

#[allow(clippy::too_many_arguments)] // Both interface owners and their exact syntax remain explicit.
fn plan_forwarded_interface_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    node: NodeRef,
    base: SemanticSymbolId,
    base_declarations: &[NodeRef],
    arguments: &NodeList,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let owner_record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &owner_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let Some(parameters) = interface.type_parameters.as_ref() else {
        return Err(unsupported());
    };
    let owner_symbol = store
        .symbol(owner)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if owner_record.kind != SyntaxKind::InterfaceDeclaration
        || owner_record.flags.0 != 0
        || !host.symbol_matches(store, declaration, owner)
        || owner_symbol.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_symbol.check_flags() != CheckFlags::NONE
        || parameters.nodes.is_empty()
        || parameters.has_trailing_comma
        || arguments.has_trailing_comma
        || arguments.nodes.is_empty()
        || arguments.nodes.len() > parameters.nodes.len()
    {
        return Err(unsupported());
    }

    let mut checked_parameters = HashSet::new();
    let owner_parameters = explicit_type_parameter_symbols(
        store,
        host,
        declaration,
        Some(parameters),
        &mut checked_parameters,
    )
    .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if owner_parameters.len() != parameters.nodes.len() {
        return Err(unsupported());
    }

    let mut shared_base_parameters: Option<Vec<SemanticSymbolId>> = None;
    for &base_declaration in base_declarations {
        let record = preflight_node(store, host, base_declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(unsupported());
        };
        let Some(base_parameters) = interface.type_parameters.as_ref() else {
            return Err(unsupported());
        };
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, base_declaration, base)
            || base_parameters.has_trailing_comma
            || base_parameters.nodes.len() != arguments.nodes.len()
        {
            return Err(unsupported());
        }
        let symbols = explicit_type_parameter_symbols(
            store,
            host,
            base_declaration,
            Some(base_parameters),
            &mut checked_parameters,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if symbols.len() != arguments.nodes.len()
            || shared_base_parameters
                .as_ref()
                .is_some_and(|expected| expected != &symbols)
        {
            return Err(unsupported());
        }
        for (parameter, symbol) in base_parameters.nodes.iter().zip(&symbols) {
            let parameter = NodeRef::new(base_declaration.arena, base_declaration.file, *parameter);
            authenticate_heritage_type_parameter(
                store,
                host,
                base_declaration,
                base,
                parameter,
                *symbol,
                node,
                HeritageTypeParameterAnnotations::Reject,
            )?;
        }
        if shared_base_parameters.is_none() {
            shared_base_parameters = Some(symbols);
        }
    }

    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression_node = NodeRef::new(node.arena, node.file, expression.expression);
    let expression_record = preflight_node(store, host, expression_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.range.start < expression_record.range.end
        || arguments.range.end != record.range.end
        || arguments.range.start >= arguments.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut planned = Vec::with_capacity(arguments.nodes.len());
    let mut previous_end = expression_record.range.end;
    let mut previous_parameter = None;
    for argument in &arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::TypeReferenceNode(reference) = &argument_record.data else {
            return Err(unsupported());
        };
        if argument_record.kind != SyntaxKind::TypeReference
            || argument_record.flags.0 != 0
            || argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || argument_record.range.start <= arguments.range.start
            || argument_record.range.end >= arguments.range.end
            || planned.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        if reference.type_arguments.is_some() {
            return Err(unsupported());
        }

        let name = NodeRef::new(argument.arena, argument.file, reference.type_name);
        let name_record =
            preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported());
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(argument.node)
            || identifier.flow_node.is_some()
        {
            return Err(unsupported());
        }

        let mut callback_host = host
            .name_resolver_host(store)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let resolved = callback_host
            .resolve_entity_name(name, SymbolFlags::TYPE)
            .map_err(|_| unsupported())?
            .and_then(|symbol| store.get_merged_symbol(symbol));
        let Some(position) = owner_parameters
            .iter()
            .position(|symbol| Some(*symbol) == resolved)
        else {
            return Err(unsupported());
        };
        if previous_parameter.is_some_and(|previous| position <= previous) {
            return Err(unsupported());
        }
        previous_parameter = Some(position);
        let expected = owner_parameters[position];
        let parameter = parameters.nodes[position];

        let parameter = NodeRef::new(declaration.arena, declaration.file, parameter);
        let parameter_name = authenticate_heritage_type_parameter(
            store,
            host,
            declaration,
            owner,
            parameter,
            expected,
            node,
            HeritageTypeParameterAnnotations::Defer,
        )?;
        let parameter_name_record = preflight_node(store, host, parameter_name)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::Identifier(parameter_name_data) = &parameter_name_record.data else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        if identifier.text != parameter_name_data.text {
            return Err(unsupported());
        }
        previous_end = argument_record.range.end;
        planned.push(argument);
    }
    Ok(planned)
}

#[allow(clippy::too_many_arguments)] // Concrete instantiation retains both canonical owners.
fn plan_concrete_interface_type_arguments(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    node: NodeRef,
    base: SemanticSymbolId,
    base_declarations: &[NodeRef],
    arguments: &NodeList,
) -> Result<Vec<NodeRef>, DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let owner_record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::InterfaceDeclaration(interface) = &owner_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let owner_symbol = store
        .symbol(owner)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if owner_record.kind != SyntaxKind::InterfaceDeclaration
        || owner_record.flags.0 != 0
        || interface.type_parameters.is_some()
        || !host.symbol_matches(store, declaration, owner)
        || owner_symbol.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_symbol.check_flags() != CheckFlags::NONE
        || arguments.nodes.is_empty()
        || arguments.has_trailing_comma
    {
        return Err(unsupported());
    }

    let mut checked_parameters = HashSet::new();
    let mut shared_base_parameters: Option<Vec<SemanticSymbolId>> = None;
    for &base_declaration in base_declarations {
        let record = preflight_node(store, host, base_declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(unsupported());
        };
        let Some(parameters) = interface.type_parameters.as_ref() else {
            return Err(unsupported());
        };
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, base_declaration, base)
            || parameters.has_trailing_comma
            || parameters.nodes.len() != arguments.nodes.len()
        {
            return Err(unsupported());
        }
        let symbols = explicit_type_parameter_symbols(
            store,
            host,
            base_declaration,
            Some(parameters),
            &mut checked_parameters,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if symbols.len() != arguments.nodes.len()
            || shared_base_parameters
                .as_ref()
                .is_some_and(|expected| expected != &symbols)
        {
            return Err(unsupported());
        }
        for (parameter, symbol) in parameters.nodes.iter().zip(&symbols) {
            authenticate_heritage_type_parameter(
                store,
                host,
                base_declaration,
                base,
                NodeRef::new(base_declaration.arena, base_declaration.file, *parameter),
                *symbol,
                node,
                HeritageTypeParameterAnnotations::Defer,
            )?;
        }
        if shared_base_parameters.is_none() {
            shared_base_parameters = Some(symbols);
        }
    }

    let record =
        preflight_node(store, host, node).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let expression_node = NodeRef::new(node.arena, node.file, expression.expression);
    let expression_record = preflight_node(store, host, expression_node)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if arguments.range.start < expression_record.range.end
        || arguments.range.end != record.range.end
        || arguments.range.start >= arguments.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let mut planned = Vec::with_capacity(arguments.nodes.len());
    let mut previous_end = expression_record.range.end;
    for argument in &arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument);
        let argument_record = preflight_node(store, host, argument)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if argument_record.parent != Some(node.node)
            || argument_record.range.start < previous_end
            || argument_record.range.start <= arguments.range.start
            || argument_record.range.end >= arguments.range.end
            || planned.contains(&argument)
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        authenticate_concrete_interface_type_argument(store, host, argument, 0)?;
        previous_end = argument_record.range.end;
        planned.push(argument);
    }
    Ok(planned)
}

fn authenticate_concrete_interface_type_argument(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: NodeRef,
    depth: usize,
) -> Result<(), DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: argument,
        kind: store
            .source_node_kind(argument)
            .unwrap_or(SyntaxKind::ExpressionWithTypeArguments),
    };
    if depth >= MAX_INTERFACE_HERITAGE_DEPTH {
        return Err(unsupported());
    }
    let record =
        preflight_node(store, host, argument).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if record.flags.0 != 0 {
        return Err(DirectInterfaceHeritageError::Invalid);
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return if record.kind.is_keyword_type()
            && matches!(record.data, NodeData::KeywordTypeNode(_))
        {
            Ok(())
        } else {
            Err(unsupported())
        };
    };
    if record.kind != SyntaxKind::TypeReference {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let name = NodeRef::new(argument.arena, argument.file, reference.type_name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let valid_name = match &name_record.data {
        NodeData::Identifier(identifier) => {
            name_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty()
        }
        NodeData::QualifiedName(qualified) => {
            name_record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0
        }
        _ => false,
    };
    if name_record.flags.0 != 0 || name_record.parent != Some(argument.node) || !valid_name {
        return Err(unsupported());
    }
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| unsupported())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(unsupported)?;
    let owner = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    if !owner.flags().intersects(SymbolFlags::TYPE) {
        return Err(unsupported());
    }

    if let Some(arguments) = reference.type_arguments.as_ref() {
        let declarations = owner.declarations().ok_or_else(unsupported)?;
        let Some(declaration) = declarations.iter().find_map(|declaration| {
            let record = host.node(*declaration)?;
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            Some((*declaration, interface.type_parameters.as_ref()?))
        }) else {
            return Err(unsupported());
        };
        if arguments.nodes.is_empty()
            || arguments.has_trailing_comma
            || declaration.1.nodes.len() != arguments.nodes.len()
            || !host.symbol_matches(store, declaration.0, symbol)
            || arguments.range.start < name_record.range.end
            || arguments.range.end != record.range.end
        {
            return Err(unsupported());
        }
        let mut checked_parameters = HashSet::new();
        let parameters = explicit_type_parameter_symbols(
            store,
            host,
            declaration.0,
            Some(declaration.1),
            &mut checked_parameters,
        )
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if parameters.len() != arguments.nodes.len() {
            return Err(unsupported());
        }
        for (parameter, parameter_symbol) in declaration.1.nodes.iter().zip(&parameters) {
            authenticate_heritage_type_parameter(
                store,
                host,
                declaration.0,
                symbol,
                NodeRef::new(declaration.0.arena, declaration.0.file, *parameter),
                *parameter_symbol,
                argument,
                HeritageTypeParameterAnnotations::Defer,
            )?;
        }
        let mut previous_end = name_record.range.end;
        for nested in &arguments.nodes {
            let nested = NodeRef::new(argument.arena, argument.file, *nested);
            let nested_record = preflight_node(store, host, nested)
                .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
            if nested_record.parent != Some(argument.node)
                || nested_record.range.start < previous_end
                || nested_record.range.start <= arguments.range.start
                || nested_record.range.end >= arguments.range.end
            {
                return Err(DirectInterfaceHeritageError::Invalid);
            }
            authenticate_concrete_interface_type_argument(store, host, nested, depth + 1)?;
            previous_end = nested_record.range.end;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)] // The declaration, canonical owner, and failure anchor differ.
fn authenticate_heritage_type_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    parameter: NodeRef,
    symbol: SemanticSymbolId,
    heritage: NodeRef,
    annotations: HeritageTypeParameterAnnotations,
) -> Result<NodeRef, DirectInterfaceHeritageError> {
    let unsupported = || DirectInterfaceHeritageError::Unsupported {
        node: heritage,
        kind: SyntaxKind::ExpressionWithTypeArguments,
    };
    let record = preflight_node(store, host, parameter)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::TypeParameterDeclaration(data) = &record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let name = NodeRef::new(parameter.arena, parameter.file, data.name);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(DirectInterfaceHeritageError::Invalid);
    };
    let symbol_record = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members));
    if record.kind != SyntaxKind::TypeParameter
        || record.flags.0 != 0
        || record.parent != Some(declaration.node)
        || annotations == HeritageTypeParameterAnnotations::Reject
            && (data.constraint.is_some() || data.default_type.is_some())
        || data.expression.is_some()
        || data.modifiers.is_some()
        || data.symbol.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(parameter.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || symbol_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || !host.symbol_matches(store, parameter, symbol)
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || members
            .and_then(|members| members.get(symbol_record.name()))
            .and_then(|member| store.get_merged_symbol(member))
            != Some(symbol)
    {
        return Err(unsupported());
    }
    for annotation in [data.constraint, data.default_type].into_iter().flatten() {
        let annotation = NodeRef::new(parameter.arena, parameter.file, annotation);
        let annotation_record = preflight_node(store, host, annotation)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if annotation_record.parent != Some(parameter.node)
            || annotation_record.range.start < record.range.start
            || annotation_record.range.end > record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
    }
    Ok(name)
}

fn authenticate_default_library_interface_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<bool, DirectInterfaceHeritageError> {
    let owner = store
        .symbol(symbol)
        .ok_or(DirectInterfaceHeritageError::Invalid)?;
    let Some(name) = owner.name().as_utf8() else {
        return Ok(false);
    };
    let flags = owner.flags().without(SymbolFlags::TRANSIENT);
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get(owner.name()))
        .and_then(|global| store.get_merged_symbol(global));
    if !(name.starts_with("HTML") || name.starts_with("SVG"))
        || !name.ends_with("Element")
        || flags != SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || owner.check_flags() != CheckFlags::NONE
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || global != Some(symbol)
    {
        return Ok(false);
    }

    let mut seen = HashSet::with_capacity(declarations.len());
    let mut has_interface = false;
    let mut value_declaration = None;
    for &declaration in declarations {
        let bound = host
            .bound_file(declaration)
            .ok_or(DirectInterfaceHeritageError::Invalid)?;
        let Some(facts) = bound.source_facts() else {
            return Err(DirectInterfaceHeritageError::Invalid);
        };
        let record = preflight_node(store, host, declaration)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if !seen.insert(declaration)
            || !facts.is_default_library()
            || !facts.is_declaration_file()
            || facts.is_javascript_file()
            || facts.is_external_or_common_js_module()
            || !host.symbol_matches(store, declaration, symbol)
        {
            return Ok(false);
        }

        let declaration_name = match &record.data {
            NodeData::InterfaceDeclaration(interface)
                if record.kind == SyntaxKind::InterfaceDeclaration
                    && record.flags.0 == 0
                    && record.parent == Some(bound.source_file().node)
                    && interface.type_parameters.is_none()
                    && interface.flow_node.is_none()
                    && interface.local_symbol.is_none()
                    && interface.symbol.is_none()
                    && !interface.members.has_trailing_comma =>
            {
                has_interface = true;
                interface.name
            }
            NodeData::VariableDeclaration(variable)
                if record.kind == SyntaxKind::VariableDeclaration
                    && record.flags.0 == 0
                    && variable.initializer.is_none()
                    && variable.exclamation_token.is_none()
                    && variable.local_symbol.is_none()
                    && variable.symbol.is_none()
                    && variable.facts == 0
                    && value_declaration.replace(declaration).is_none() =>
            {
                if !authenticated_default_library_value_declaration(
                    store,
                    host,
                    declaration,
                    bound.source_file(),
                )? {
                    return Ok(false);
                }
                variable.name
            }
            _ => return Ok(false),
        };
        let declaration_name = NodeRef::new(declaration.arena, declaration.file, declaration_name);
        let declaration_name_record = preflight_node(store, host, declaration_name)
            .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        if declaration_name_record.kind != SyntaxKind::Identifier
            || declaration_name_record.flags.0 != 0
            || declaration_name_record.parent != Some(declaration.node)
            || !matches!(
                &declaration_name_record.data,
                NodeData::Identifier(identifier)
                    if identifier.flow_node.is_none() && identifier.text == name
            )
        {
            return Ok(false);
        }
    }
    if !has_interface
        || value_declaration.is_none()
        || owner.value_declaration() != value_declaration
    {
        return Ok(false);
    }

    if let Some(links) = store.declared_type_links(symbol) {
        let Some(type_) = links.declared_type else {
            return Ok(false);
        };
        let Some(record) = store.type_payload(type_) else {
            return Ok(false);
        };
        let TypeData::Interface(interface) = record.data() else {
            return Ok(false);
        };
        if !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record.object_flags().contains(ObjectFlags::CLASS)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || interface.outer_type_parameter_count != 0
            || interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .is_some_and(|arguments| !arguments.is_empty())
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn authenticated_default_library_value_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    source: NodeRef,
) -> Result<bool, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, declaration)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let Some(list) = record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
    else {
        return Ok(false);
    };
    let list_record =
        preflight_node(store, host, list).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::VariableDeclarationList(variables) = &list_record.data else {
        return Ok(false);
    };
    let Some(statement) = list_record
        .parent
        .map(|parent| NodeRef::new(list.arena, list.file, parent))
    else {
        return Ok(false);
    };
    let statement_record = preflight_node(store, host, statement)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::VariableStatement(variable_statement) = &statement_record.data else {
        return Ok(false);
    };
    let Some(modifiers) = variable_statement.modifiers.as_ref() else {
        return Ok(false);
    };
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
    let modifier_record =
        preflight_node(store, host, modifier).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    Ok(list_record.kind == SyntaxKind::VariableDeclarationList
        && list_record.flags.0 == 0
        && variables
            .declarations
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count()
            == 1
        && statement_record.kind == SyntaxKind::VariableStatement
        && statement_record.flags.0 == 0
        && statement_record.parent == Some(source.node)
        && variable_statement.declaration_list == list.node
        && modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && modifier_record.kind == SyntaxKind::DeclareKeyword
        && modifier_record.flags.0 == 0
        && modifier_record.parent == Some(statement.node))
}

fn resolve_qualified_interface_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
) -> Result<SemanticSymbolId, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let (namespace_id, name_id) = match &record.data {
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            (access.expression, access.name)
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            (qualified.left, qualified.right)
        }
        _ => return Err(DirectInterfaceHeritageError::Invalid),
    };
    let namespace_expression = NodeRef::new(expression.arena, expression.file, namespace_id);
    let namespace_record = preflight_node(store, host, namespace_expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let name = NodeRef::new(expression.arena, expression.file, name_id);
    let name_record =
        preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: name,
            kind: name_record.kind,
        });
    };
    if record.flags.0 != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(expression.node)
        || identifier.flow_node.is_some()
        || namespace_record.range.end > name_record.range.start
        || name_record.range.end > record.range.end
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let namespace = authenticate_namespace_expression(
        store,
        host,
        namespace_expression,
        expression,
        &mut HashSet::new(),
    )?;
    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(expression, SymbolFlags::TYPE)
        .map_err(|_| DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?;
    if !authenticated_namespace_export(store, namespace, &identifier.text, symbol) {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        });
    }
    Ok(symbol)
}

fn authenticate_namespace_expression(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: NodeRef,
    parent: NodeRef,
    visited: &mut HashSet<NodeRef>,
) -> Result<SemanticSymbolId, DirectInterfaceHeritageError> {
    let record = preflight_node(store, host, expression)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let parent_record =
        preflight_node(store, host, parent).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    if record.parent != Some(parent.node)
        || record.flags.0 != 0
        || record.range.start < parent_record.range.start
        || record.range.end > parent_record.range.end
        || !visited.insert(expression)
    {
        return Err(DirectInterfaceHeritageError::Invalid);
    }

    let segment = match &record.data {
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier && identifier.flow_node.is_none() =>
        {
            None
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            Some((access.expression, access.name))
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            Some((qualified.left, qualified.right))
        }
        _ => {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: expression,
                kind: record.kind,
            });
        }
    };
    let prefix = if let Some((left, name)) = segment {
        let left = NodeRef::new(expression.arena, expression.file, left);
        let left_record =
            preflight_node(store, host, left).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let name = NodeRef::new(expression.arena, expression.file, name);
        let name_record =
            preflight_node(store, host, name).map_err(|_| DirectInterfaceHeritageError::Invalid)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(DirectInterfaceHeritageError::Unsupported {
                node: name,
                kind: name_record.kind,
            });
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(expression.node)
            || identifier.flow_node.is_some()
            || left_record.range.end > name_record.range.start
            || name_record.range.end > record.range.end
        {
            return Err(DirectInterfaceHeritageError::Invalid);
        }
        Some((
            authenticate_namespace_expression(store, host, left, expression, visited)?,
            identifier.text.as_str(),
        ))
    } else {
        None
    };

    let mut callback_host = host
        .name_resolver_host(store)
        .map_err(|_| DirectInterfaceHeritageError::Invalid)?;
    let symbol = callback_host
        .resolve_entity_name(expression, SymbolFlags::NAMESPACE)
        .map_err(|_| DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        })?;
    if store
        .symbol(symbol)
        .is_none_or(|namespace| !namespace.flags().intersects(SymbolFlags::MODULE))
        || prefix.is_some_and(|(owner, name)| {
            !authenticated_namespace_export(store, owner, name, symbol)
        })
    {
        return Err(DirectInterfaceHeritageError::Unsupported {
            node: expression,
            kind: record.kind,
        });
    }
    Ok(symbol)
}

fn authenticated_namespace_export(
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    name: &str,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(owner) = store.symbol(namespace) else {
        return false;
    };
    let exports = store
        .module_symbol_links(namespace)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner.exports());
    exports
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(name))
        .and_then(|export| store.get_merged_symbol(export))
        == Some(symbol)
        && store.get_parent_of_symbol(symbol) == Some(namespace)
        && store
            .symbol(symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            == Some(name)
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
        let sources = context
            .file_order()
            .iter()
            .map(|file| context.file(*file).unwrap())
            .collect::<Vec<_>>();
        let host = DeclaredTypeHost::new_after_global_merge(
            sources,
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

    fn default_library_heritage_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        default_library: bool,
    ) -> (CanonicalCheckerContext<'arena>, FileId, FileId) {
        let library_file = FileId::new(8_470);
        let source_file = FileId::new(8_471);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, is_default_library) in [
            (library, library_file, default_library),
            (source, source_file, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/dom-heritage-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        is_default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(library_file, &library.arena), (source_file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        (context, library_file, source_file)
    }

    #[test]
    fn default_library_dom_interface_value_bases_remain_cold_and_canonical() {
        let library = parse_source_file(concat!(
            "interface DomRoot { root: string }\n",
            "interface DomExtra {}\n",
            "interface DomMore {}\n",
            "interface HTMLElement extends DomRoot, DomExtra, DomMore {\n",
            "  addEventListener(value: string): void;\n",
            "}\n",
            "declare var HTMLElement: unknown;\n",
        ));
        let source = parse_source_file("interface HTMLWebViewElement extends HTMLElement {}\n");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let (mut context, library_file, source_file) =
            default_library_heritage_context(&library, &source, true);
        let base = interface_symbol(&library, library_file, &context, "HTMLElement");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("the default-library DOM interface must remain the sole direct base")
        };
        assert_eq!(inherited.symbol, base);
        assert_eq!(
            inherited.kind,
            DirectInterfaceBaseKind::DefaultLibraryInterface
        );
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            context.store().symbol(base).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        );
        assert!(context.store().declared_type_links(base).is_none());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
        assert_eq!(
            heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap(),
            planned
        );

        assert!(context.store_mut_for_test().set_symbol_flags(
            base,
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let transient_state = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(
            heritage_plan(&source, source_file, &context, "HTMLWebViewElement").unwrap(),
            planned
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            transient_state
        );
    }

    #[test]
    fn default_library_dom_interface_bases_reject_forged_provenance() {
        let library = parse_source_file(concat!(
            "interface HTMLElement { value: string }\n",
            "declare var HTMLElement: unknown;\n",
        ));
        let source = parse_source_file("interface HTMLWebViewElement extends HTMLElement {}\n");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);

        for corruption in 0..4 {
            let (mut context, library_file, source_file) =
                default_library_heritage_context(&library, &source, corruption != 0);
            let base = interface_symbol(&library, library_file, &context, "HTMLElement");
            match corruption {
                0 => {}
                1 => {
                    assert!(context.store_mut_for_test().set_symbol_flags(
                        base,
                        SymbolFlags::INTERFACE
                            | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                            | SymbolFlags::CLASS,
                        CheckFlags::NONE,
                    ));
                }
                2 => {
                    let declarations = context
                        .store()
                        .symbol(base)
                        .unwrap()
                        .declarations()
                        .unwrap()
                        .to_vec();
                    assert!(context.store_mut_for_test().set_symbol_declarations(
                        base,
                        Some(declarations),
                        None,
                    ));
                }
                3 => {
                    let declarations = context
                        .store()
                        .symbol(base)
                        .unwrap()
                        .declarations()
                        .unwrap()
                        .iter()
                        .copied()
                        .filter(|declaration| {
                            context.store().source_node_kind(*declaration)
                                == Some(SyntaxKind::InterfaceDeclaration)
                        })
                        .collect::<Vec<_>>();
                    assert!(context.store_mut_for_test().set_symbol_declarations(
                        base,
                        Some(declarations),
                        None,
                    ));
                }
                _ => unreachable!("the provenance matrix has four cases"),
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(
                matches!(
                    heritage_plan(&source, source_file, &context, "HTMLWebViewElement"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "corruption {corruption} accepted a forged DOM base"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "corruption {corruption} published checker state"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_preserve_export_ownership_and_warm_state() {
        let cases = [
            (
                concat!(
                    "namespace Types { export interface Base { value: number } }\n",
                    "interface Derived extends Types.Base { own: number }\n",
                ),
                "Types",
            ),
            (
                concat!(
                    "namespace Outer { export namespace Inner { ",
                    "export interface Base { value: number } } }\n",
                    "interface Derived extends Outer.Inner.Base { own: number }\n",
                ),
                "Inner",
            ),
            (
                concat!(
                    "namespace Types { export interface Base<Value> { value: Value } }\n",
                    "interface Derived extends Types.Base<number> { own: number }\n",
                ),
                "Types",
            ),
        ];

        for (index, (source, expected_owner)) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_430 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            let first = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let [base] = first.bases.as_slice() else {
                panic!("{index}: a qualified interface has one authenticated base")
            };
            assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(base.type_arguments.len(), usize::from(index == 2));
            assert_eq!(
                parsed.arena.get(base.expression.node).unwrap().kind,
                SyntaxKind::QualifiedName
            );
            assert_eq!(
                base.symbol,
                interface_symbol(&parsed, file, &context, "Base")
            );
            assert_eq!(
                context
                    .store()
                    .get_parent_of_symbol(base.symbol)
                    .and_then(|owner| context.store().symbol(owner))
                    .and_then(|owner| owner.name().as_utf8()),
                Some(expected_owner)
            );
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived").unwrap(),
                first
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: qualified heritage planning published checker state"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_reject_private_and_class_exports() {
        let cases = [
            concat!(
                "namespace Types { interface Hidden { value: number } }\n",
                "interface Derived extends Types.Hidden { own: number }\n",
            ),
            concat!(
                "namespace Types { export class Base {} }\n",
                "interface Derived extends Types.Base { own: number }\n",
            ),
        ];

        for (index, source) in cases.into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_440 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            assert!(
                matches!(
                    heritage_plan(&parsed, file, &context, "Derived"),
                    Err(DirectInterfaceHeritageError::Unsupported { .. })
                ),
                "{index}: {source}"
            );
        }
    }

    #[test]
    fn qualified_namespace_bases_reject_forged_export_owners() {
        let parsed = parse_source_file(concat!(
            "namespace Types { export interface Base { value: number } }\n",
            "namespace Other { export interface Foreign { value: number } }\n",
            "interface Derived extends Types.Base { own: number }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_450);
        let mut context = checker_context(&parsed, file);
        let original = interface_symbol(&parsed, file, &context, "Base");
        let foreign = interface_symbol(&parsed, file, &context, "Foreign");
        let namespace = context.store().get_parent_of_symbol(original).unwrap();
        let exports = context
            .store()
            .symbol(namespace)
            .unwrap()
            .exports()
            .unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("Base"),
                foreign
            ),
            Some(Some(original))
        );

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Derived"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
    }

    #[test]
    fn transitive_interface_bases_are_planned_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Root { first: number }\n",
            "interface Middle extends Root { second: string }\n",
            "interface Leaf extends Middle { third: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_451);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = heritage_plan(&parsed, file, &context, "Leaf").unwrap();
        let [base] = plan.bases.as_slice() else {
            panic!("a transitive chain retains only its direct base")
        };
        assert_eq!(
            base.symbol,
            interface_symbol(&parsed, file, &context, "Middle")
        );
        assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
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
    fn forward_interface_bases_preserve_named_method_symbols_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base { method(...args: any[]): void; }\n",
            "interface Base { method(...args: any[]): void; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_453);
        let context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("a forward-declared interface must retain its one direct base")
        };
        let method = context
            .store()
            .symbol(base)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("method"))
            .unwrap();
        assert_eq!(inherited.symbol, base);
        assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            context.store().symbol(method).unwrap().flags(),
            SymbolFlags::METHOD
        );
        assert_eq!(context.store().get_parent_of_symbol(method), Some(base));
        assert_eq!(
            heritage_plan(&parsed, file, &context, "Derived").unwrap(),
            planned,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn forwarded_generic_interface_bases_preserve_ordered_type_arguments() {
        for (index, (source, expected_arguments)) in [
            (
                concat!(
                    "interface Derived<Value> extends Base<Value> { own: Value }\n",
                    "interface Base<Item> { inherited: Item }\n",
                ),
                &["Value"][..],
            ),
            (
                concat!(
                    "interface Derived<First, Second> extends Base<First, Second> {}\n",
                    "interface Base<Left, Right> { left: Left; right: Right }\n",
                ),
                &["First", "Second"][..],
            ),
            (
                concat!(
                    "interface Derived<Value extends string, Extra> extends Base<Value> {}\n",
                    "interface Base<Item> { inherited: Item }\n",
                ),
                &["Value"][..],
            ),
            (
                concat!(
                    "interface Derived<Value> extends Base<Value> { own: Value }\n",
                    "interface Base<Item> { first: Item }\n",
                    "interface Base<Item> { second: Item }\n",
                ),
                &["Value"][..],
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_454 + u32::try_from(index).unwrap());
            let context = checker_context(&parsed, file);
            let base = interface_symbol(&parsed, file, &context, "Base");
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );

            let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
            let [inherited] = planned.bases.as_slice() else {
                panic!("{index}: a generic interface must retain one direct base")
            };
            assert_eq!(inherited.symbol, base);
            assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
            assert_eq!(
                inherited
                    .type_arguments
                    .iter()
                    .map(|argument| {
                        let NodeData::TypeReferenceNode(reference) =
                            &parsed.arena.get(argument.node).unwrap().data
                        else {
                            panic!("{index}: a generic argument must retain its type reference")
                        };
                        let NodeData::Identifier(name) =
                            &parsed.arena.get(reference.type_name).unwrap().data
                        else {
                            panic!("{index}: a forwarded argument must retain its parameter name")
                        };
                        name.text.as_str()
                    })
                    .collect::<Vec<_>>(),
                expected_arguments,
            );
            assert_eq!(
                heritage_plan(&parsed, file, &context, "Derived").unwrap(),
                planned,
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: generic heritage planning published checker state",
            );
        }
    }

    #[test]
    fn reopened_generic_interface_bases_keep_multiple_heritage_bases_and_recursion_lazy() {
        let parsed = parse_source_file(concat!(
            "interface Array<Value> { length: number }\n",
            "type ReactNode = string | ReactNodeArray;\n",
            "interface ReactNodeArray extends Array<ReactNode> {}\n",
            "declare namespace React {\n",
            "  interface AriaAttributes { label?: string }\n",
            "  interface DOMAttributes<T> { children?: ReactNode; target?: T }\n",
            "  interface HTMLAttributes<T> ",
            "extends AriaAttributes, DOMAttributes<T> { id?: string }\n",
            "  interface HTMLAttributes<T> { title?: string }\n",
            "  interface InputHTMLAttributes<T> extends HTMLAttributes<T> { value?: string }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_480);
        let context = checker_context(&parsed, file);
        let html_attributes = interface_symbol(&parsed, file, &context, "HTMLAttributes");
        let aria_attributes = interface_symbol(&parsed, file, &context, "AriaAttributes");
        let dom_attributes = interface_symbol(&parsed, file, &context, "DOMAttributes");
        let array = interface_symbol(&parsed, file, &context, "Array");
        let initial_array_links = context.store().declared_type_links(array).cloned();
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let input = heritage_plan(&parsed, file, &context, "InputHTMLAttributes").unwrap();
        let [input_base] = input.bases.as_slice() else {
            panic!("a reopened generic interface must retain its canonical direct base")
        };
        assert_eq!(input_base.symbol, html_attributes);
        assert_eq!(input_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(input_base.type_arguments.len(), 1);

        let html = heritage_plan(&parsed, file, &context, "HTMLAttributes").unwrap();
        assert_eq!(
            html.bases
                .iter()
                .map(|base| (base.symbol, base.kind, base.type_arguments.len()))
                .collect::<Vec<_>>(),
            [
                (aria_attributes, DirectInterfaceBaseKind::Interface, 0),
                (dom_attributes, DirectInterfaceBaseKind::Interface, 1),
            ],
        );

        let recursive = heritage_plan(&parsed, file, &context, "ReactNodeArray").unwrap();
        let [recursive_base] = recursive.bases.as_slice() else {
            panic!("a recursive ReactNode argument must retain its direct array base")
        };
        assert_eq!(recursive_base.symbol, array);
        assert_eq!(recursive_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(recursive_base.type_arguments.len(), 1);

        assert_eq!(
            heritage_plan(&parsed, file, &context, "InputHTMLAttributes").unwrap(),
            input,
        );
        assert_eq!(
            heritage_plan(&parsed, file, &context, "HTMLAttributes").unwrap(),
            html,
        );
        assert_eq!(
            heritage_plan(&parsed, file, &context, "ReactNodeArray").unwrap(),
            recursive,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
        assert!(
            context
                .store()
                .declared_type_links(html_attributes)
                .is_none()
        );
        assert_eq!(
            context.store().declared_type_links(array),
            initial_array_links.as_ref(),
        );
    }

    #[test]
    fn reopened_generic_interface_heritage_cycles_remain_unsupported_without_publication() {
        let parsed = parse_source_file(concat!(
            "interface Left<T> extends Right<T> {}\n",
            "interface Left<T> { value?: T }\n",
            "interface Right<T> extends Left<T> {}\n",
            "interface Derived<T> extends Left<T> {}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_481);
        let context = checker_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Derived"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
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
    }

    #[test]
    fn forwarded_generic_interface_bases_reject_unverified_substitutions() {
        for (index, source) in [
            concat!(
                "interface Derived<Value> extends Base<string> {}\n",
                "interface Base<Item> { inherited: Item }\n",
            ),
            concat!(
                "interface Derived<Value> extends Base<Value[]> {}\n",
                "interface Base<Item> { inherited: Item }\n",
            ),
            concat!(
                "interface Derived<First, Second> extends Base<Second, First> {}\n",
                "interface Base<Left, Right> { left: Left; right: Right }\n",
            ),
            concat!(
                "interface Derived<Value> extends Base<Value> {}\n",
                "interface Base<Item extends string> { inherited: Item }\n",
            ),
            concat!(
                "interface Derived<Value> extends Base<Value, Value> {}\n",
                "interface Base<Left, Right> { left: Left; right: Right }\n",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_456 + u32::try_from(index).unwrap());
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
                "{index}: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: rejected generic heritage published checker state",
            );
        }
    }

    #[test]
    fn merged_transient_interface_bases_retain_their_canonical_identity() {
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base { own: string }\n",
            "interface Base { first: number }\n",
            "interface Base { second: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_462);
        let mut context = checker_context(&parsed, file);
        let base = interface_symbol(&parsed, file, &context, "Base");
        assert!(context.store_mut_for_test().set_symbol_flags(
            base,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let planned = heritage_plan(&parsed, file, &context, "Derived").unwrap();
        let [inherited] = planned.bases.as_slice() else {
            panic!("a merged transient interface must retain one direct base")
        };
        assert_eq!(inherited.symbol, base);
        assert_eq!(inherited.kind, DirectInterfaceBaseKind::Interface);
        assert!(inherited.type_arguments.is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn concrete_namespace_interface_bases_keep_react_svg_arguments_lazy() {
        let parsed = parse_source_file(concat!(
            "interface Element {}\n",
            "interface SVGElement extends Element {}\n",
            "declare namespace React {\n",
            "  interface ReactElement<Props> { props: Props; }\n",
            "  interface SVGAttributes<T extends Element> { element?: T; }\n",
            "  interface DOMElement<Props extends SVGAttributes<T>, T extends Element> ",
            "extends ReactElement<Props> { type: string; }\n",
            "  interface ReactSVGElement ",
            "extends DOMElement<SVGAttributes<SVGElement>, SVGElement> { type: string; }\n",
            "  interface ReactPortal extends ReactElement<any> { children: string; }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_463);
        let context = checker_context(&parsed, file);
        let dom_element = interface_symbol(&parsed, file, &context, "DOMElement");
        let react_element = interface_symbol(&parsed, file, &context, "ReactElement");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let svg = heritage_plan(&parsed, file, &context, "ReactSVGElement").unwrap();
        let [svg_base] = svg.bases.as_slice() else {
            panic!("ReactSVGElement must retain its instantiated DOMElement base")
        };
        assert_eq!(svg_base.symbol, dom_element);
        assert_eq!(svg_base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(
            svg_base
                .type_arguments
                .iter()
                .map(|argument| parsed.arena.get(argument.node).unwrap().kind)
                .collect::<Vec<_>>(),
            [SyntaxKind::TypeReference, SyntaxKind::TypeReference],
        );

        let portal = heritage_plan(&parsed, file, &context, "ReactPortal").unwrap();
        let [portal_base] = portal.bases.as_slice() else {
            panic!("ReactPortal must retain its instantiated ReactElement base")
        };
        assert_eq!(portal_base.symbol, react_element);
        assert_eq!(portal_base.type_arguments.len(), 1);
        assert_eq!(
            parsed
                .arena
                .get(portal_base.type_arguments[0].node)
                .unwrap()
                .kind,
            SyntaxKind::AnyKeyword,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn concrete_interface_bases_reject_unresolved_and_malformed_type_arguments() {
        for (index, source) in [
            concat!(
                "interface Derived extends Base<Missing> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Derived extends Base<number, string> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Wrapped<Value> { value: Value }\n",
                "interface Derived extends Base<Wrapped<number, string>> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
            concat!(
                "interface Wrapped {}\n",
                "interface Derived extends Base<Wrapped<number>> {}\n",
                "interface Base<Value> { value: Value }\n",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{index}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(8_464 + u32::try_from(index).unwrap());
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
                "{index}: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
                "{index}: rejected concrete heritage published checker state",
            );
        }
    }

    #[test]
    fn transitive_interface_cycles_remain_unsupported() {
        let parsed = parse_source_file(concat!(
            "interface Left extends Right { first: number }\n",
            "interface Right extends Left { second: string }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_452);
        let context = checker_context(&parsed, file);

        assert!(matches!(
            heritage_plan(&parsed, file, &context, "Left"),
            Err(DirectInterfaceHeritageError::Unsupported { .. })
        ));
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
