//! Selected class members use canonical values without publishing a class member table.

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalNameResolver, CanonicalResolutionLocation, CanonicalTypeMapperStore,
    CanonicalTypeQuery, CheckFlags, ClassError, ClassInvariant, ClassMethodPlan, ClassPropertyPlan,
    ClassQueryPlan, ClassUnsupported, DeclaredTypeError, DeclaredTypeHost, HashSet,
    LiteralTypeCacheError, NodeData, NodeRef, PreparedClassMethodSignatures, SemanticSymbolId,
    SignatureFlags, SignatureLinks, StaticShellState, Symbol, SymbolFlags, SymbolNodeLinks,
    SyntaxKind, TypeId, TypeNodeLinks, TypeRecord, ValueSymbolLinks,
    authenticated_private_class_symbol_name, bound_symbol, class_member_symbol_name_matches,
    class_property_modifiers, class_query_shell_state, exact_class_instance_identity,
    exact_method_callable, exact_method_value, execute_class_query_shells, invariant,
    method_return_type, plan_class_query, plan_method, plan_property, plan_type_literal,
    planned_property_type, preflight_class_or_interface_reference, preflight_node,
    prepare_class_method_signature, primitive_keyword_type, property_initializer_number,
    publish_class_method_callable, publish_class_method_identity, publish_class_property,
    unsupported, validate_method_cache_state, validate_query_property_cache_state,
};

mod values;
pub(in crate::semantic) use values::ClassValueQuery;

fn enclosing_query_class(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<(ClassQueryPlan, NodeRef)>, ClassError> {
    let mut current = node;
    let mut seen = HashSet::new();
    while seen.insert(current) {
        let record = preflight_node(store, host, current)?;
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(node.arena, node.file, parent);
        match preflight_node(store, host, parent)?.kind {
            SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression => {
                let owner = bound_symbol(store, host, parent)
                    .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(parent)))?;
                let plan = plan_class_query(store, host, owner)?;
                return Ok((plan.members.contains(&current.node)
                    && matches!(
                        record.kind,
                        SyntaxKind::PropertyDeclaration | SyntaxKind::MethodDeclaration
                    ))
                .then_some((plan, current)));
            }
            SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ComputedPropertyName => return Ok(None),
            _ => current = parent,
        }
    }
    Err(invariant(ClassInvariant::InvalidDeclaration(node)))
}

fn lexical_class_query_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    meaning: SymbolFlags,
) -> Result<SemanticSymbolId, ClassError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::Identifier(identifier) = &record.data else {
        return Err(invariant(ClassInvariant::InvalidName(node)));
    };
    if record.kind != SyntaxKind::Identifier
        || record.flags.0 != 0
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(invariant(ClassInvariant::InvalidName(node)));
    }
    let (arena, bound) = host
        .source(node)
        .ok_or_else(|| invariant(ClassInvariant::InvalidName(node)))?;
    let mut callbacks = host.name_resolver_host(store)?;
    let raw = CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callbacks)
        .map_err(DeclaredTypeError::from)?
        .resolve(
            Some(CanonicalResolutionLocation::Bound(node)),
            &identifier.text,
            meaning,
            None,
            true,
            false,
        )
        .map_err(DeclaredTypeError::from)?
        .ok_or_else(|| unsupported(ClassUnsupported::PropertyInitializer(node)))?;
    let local = store
        .get_merged_symbol(raw)
        .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(raw)))?;
    let record = store
        .symbol(local)
        .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(local)))?;
    store
        .get_merged_symbol(record.export_symbol().unwrap_or(local))
        .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(local)))
}

fn validate_query_reference_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), ClassError> {
    if store.symbol_node_links(node).is_some_and(|links| {
        links != &SymbolNodeLinks::default()
            && links
                != &SymbolNodeLinks {
                    resolved_symbol: Some(symbol),
                }
    }) {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(node)));
    }
    Ok(())
}

/// Resolves a reference from its class binding without publishing expression caches.
pub(in crate::semantic) fn class_query_reference_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<SemanticSymbolId>, ClassError> {
    let Some((class, member)) = enclosing_query_class(store, host, node)? else {
        return Ok(None);
    };
    let record = preflight_node(store, host, node)?;
    let property = if record.kind == SyntaxKind::PropertyAccessExpression {
        Some(node)
    } else if let Some(parent) = record.parent {
        let parent = NodeRef::new(node.arena, node.file, parent);
        matches!(&preflight_node(store, host, parent)?.data,
            NodeData::PropertyAccessExpression(access) if access.name == node.node)
        .then_some(parent)
    } else {
        None
    };
    let symbol = if let Some(property) = property {
        let record = preflight_node(store, host, property)?;
        let NodeData::PropertyAccessExpression(access) = &record.data else {
            return Err(invariant(ClassInvariant::InvalidProperty(property)));
        };
        let receiver = NodeRef::new(node.arena, node.file, access.expression);
        let name = NodeRef::new(node.arena, node.file, access.name);
        let receiver_record = preflight_node(store, host, receiver)?;
        let name_record = preflight_node(store, host, name)?;
        let (text, private) = match &name_record.data {
            NodeData::Identifier(name)
                if name_record.kind == SyntaxKind::Identifier && name.flow_node.is_none() =>
            {
                (name.text.as_str(), false)
            }
            NodeData::PrivateIdentifier(name)
                if name_record.kind == SyntaxKind::PrivateIdentifier
                    && name.text.starts_with('#')
                    && name.text.len() > 1 =>
            {
                (name.text.as_str(), true)
            }
            _ => return Err(invariant(ClassInvariant::InvalidName(name))),
        };
        if record.flags.0 != 0
            || access.flow_node.is_some()
            || access.facts != 0
            || access.question_dot_token.is_some()
            || name_record.flags.0 != 0
            || text.is_empty()
            || receiver_record.parent != Some(property.node)
            || name_record.parent != Some(property.node)
        {
            return Err(unsupported(ClassUnsupported::PropertyInitializer(property)));
        }
        let symbol = if receiver_record.kind == SyntaxKind::ThisKeyword {
            if !matches!(&receiver_record.data, NodeData::KeywordExpression(keyword) if keyword.flow_node.is_none())
                || receiver_record.flags.0 != 0
            {
                return Err(invariant(ClassInvariant::InvalidProperty(receiver)));
            }
            let (arena, _) = host.source(member)
                .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(member)))?;
            let owner = store.symbol(class.symbol)
                .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(class.symbol)))?;
            let table = if ts_binder::canonical_has_syntactic_modifier(arena, member.node, SyntaxKind::StaticKeyword) {
                owner.exports()
            } else {
                owner.members()
            };
            let table = table.and_then(|table| store.symbol_table(table))
                .ok_or_else(|| unsupported(ClassUnsupported::PropertyInitializer(property)))?;
            if private {
                table.iter().find_map(|(_, symbol)| {
                    (authenticated_private_class_symbol_name(store, class.symbol, symbol) == Some(text))
                        .then_some(symbol)
                })
            } else {
                table.get_source(text)
            }
        } else if !private && receiver_record.kind == SyntaxKind::Identifier {
            let target = lexical_class_query_symbol(store, host, receiver,
                SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS)?;
            validate_query_reference_cache(store, receiver, target)?;
            let target_record = store.symbol(target)
                .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(target)))?;
            if target_record.flags().intersects(SymbolFlags::ENUM) {
                super::super::enums::preflight_enum(store, host, target)
                    .map_err(DeclaredTypeError::from)?;
                target_record.exports().and_then(|table| store.symbol_table(table))
                    .and_then(|table| table.get_source(text))
            } else if target_record.flags() == SymbolFlags::CLASS {
                plan_class_query(store, host, target)?;
                target_record.exports().and_then(|table| store.symbol_table(table))
                    .and_then(|table| table.get_source(text))
            } else {
                let declaration = target_record.value_declaration()
                    .ok_or_else(|| unsupported(ClassUnsupported::PropertyInitializer(property)))?;
                if !matches!(target_record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE)
                    || !matches!(&preflight_node(store, host, declaration)?.data,
                        NodeData::VariableDeclaration(variable) if variable.type_.is_some() && variable.initializer.is_none())
                {
                    return Err(unsupported(ClassUnsupported::PropertyInitializer(property)));
                }
                let value = super::super::declared_values::plan_declared_value(store, host, target)?;
                let object = plan_type_literal(store, host, value.annotation, None)
                    .map_err(|_| unsupported(ClassUnsupported::PropertyInitializer(property)))?;
                object.properties.iter().find_map(|property| {
                    (property.name.as_utf8() == Some(text)).then_some(property.symbol)
                })
            }
        } else {
            return Err(unsupported(ClassUnsupported::PropertyInitializer(property)));
        }.ok_or_else(|| unsupported(ClassUnsupported::PropertyInitializer(property)))?;
        validate_query_reference_cache(store, property, symbol)?;
        validate_query_reference_cache(store, name, symbol)?;
        symbol
    } else if record.kind == SyntaxKind::ThisKeyword {
        if !matches!(&record.data, NodeData::KeywordExpression(keyword) if keyword.flow_node.is_none())
            || record.flags.0 != 0
        {
            return Err(invariant(ClassInvariant::InvalidProperty(node)));
        }
        class.symbol
    } else if record.kind == SyntaxKind::Identifier {
        lexical_class_query_symbol(
            store,
            host,
            node,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
        )?
    } else {
        return Ok(None);
    };
    validate_query_reference_cache(store, node, symbol)?;
    Ok(Some(symbol))
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::large_enum_variant)] // Keep owned plans without adding per-selection allocations.
enum SelectedMember {
    Property(ClassPropertyPlan),
    Method(ClassMethodPlan),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct ClassSelectedMemberPlan {
    class: ClassQueryPlan,
    member: SelectedMember,
    type_: TypeId,
}

pub(in crate::semantic) fn plan_selected_class_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassSelectedMemberPlan, ClassError> {
    let invalid = || invariant(ClassInvariant::InvalidPropertyValueCache(symbol));
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let owner = record.parent().ok_or_else(invalid)?;
    let class = plan_class_query(store, host, owner)?;
    class_query_shell_state(store, &class)?;
    let declaration = record.value_declaration().ok_or_else(|| {
        unsupported(ClassUnsupported::Member {
            node: class.declaration,
            kind: SyntaxKind::ClassDeclaration,
        })
    })?;
    if record
        .declarations()
        .is_some_and(|declarations| declarations.len() > 1)
        || preflight_node(store, host, declaration)?.kind == SyntaxKind::Parameter
    {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: preflight_node(store, host, declaration)?.kind,
        }));
    }
    if declaration.arena != class.declaration.arena
        || declaration.file != class.declaration.file
        || !class.members.contains(&declaration.node)
        || record.declarations() != Some(&[declaration])
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(invalid());
    }
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let exports = owner_record.exports().ok_or_else(invalid)?;
    let (member, type_) = match preflight_node(store, host, declaration)?.kind {
        SyntaxKind::PropertyDeclaration => {
            let property = plan_property(
                store,
                host,
                owner,
                declaration,
                owner_record.members(),
                exports,
            )?;
            let type_ = planned_property_type(store, host, &property)?;
            validate_query_property_cache_state(store, &property, type_)?;
            (SelectedMember::Property(property), type_)
        }
        SyntaxKind::MethodDeclaration => {
            let method = plan_method(
                store,
                host,
                owner,
                declaration,
                owner_record.members(),
                exports,
                class.ambient,
            )?;
            if let Some(return_) = method.private_return {
                plan_selected_class_member(store, host, return_.field)?;
            }
            if method.private_tagged_call.is_some() {
                return Err(unsupported(ClassUnsupported::Member {
                    node: declaration,
                    kind: SyntaxKind::MethodDeclaration,
                }));
            }
            let type_ = method_return_type(store, host, &method)?;
            validate_method_cache_state(store, &method, type_)?;
            (SelectedMember::Method(method), type_)
        }
        kind => {
            return Err(unsupported(ClassUnsupported::Member {
                node: declaration,
                kind,
            }));
        }
    };
    Ok(ClassSelectedMemberPlan {
        class,
        member,
        type_,
    })
}

pub(in crate::semantic) fn execute_selected_class_member(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassSelectedMemberPlan,
) -> Result<TypeId, ClassError> {
    let symbol = match &plan.member {
        SelectedMember::Property(property) => property.symbol,
        SelectedMember::Method(method) => method.symbol,
    };
    if plan_selected_class_member(store, host, symbol)? != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(
            plan.class.declaration,
        )));
    }
    if let Some(type_) = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
    {
        return Ok(type_);
    }
    let capacity = || invariant(ClassInvariant::Capacity(plan.class.declaration));
    let parameter_count = match &plan.member {
        SelectedMember::Property(_) => 0,
        SelectedMember::Method(method) => method
            .parameters
            .len()
            .checked_add(usize::from(method.rest_parameter.is_some()))
            .ok_or_else(capacity)?,
    };
    if !store.try_reserve_types(4)
        || !store
            .try_reserve_value_symbol_links(parameter_count.checked_add(1).ok_or_else(capacity)?)
        || !store.try_reserve_type_node_links(parameter_count.checked_add(8).ok_or_else(capacity)?)
        || !store.try_reserve_symbol_node_links(1)
        || !store.try_reserve_signature_links(1)
        || !store.try_reserve_signatures(1)
    {
        return Err(capacity());
    }
    match &plan.member {
        SelectedMember::Property(property) => {
            let numbers = property_initializer_number(property)
                .into_iter()
                .collect::<Vec<_>>();
            let strings = property
                .initializer_string
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            store
                .prepare_regular_literal_types(&strings, &numbers, &[])
                .map_err(|error| {
                    if error == LiteralTypeCacheError::Capacity {
                        capacity()
                    } else {
                        invariant(ClassInvariant::InvalidPropertyTypeCache(property.type_node))
                    }
                })?;
            publish_class_property(store, property, plan.type_);
        }
        SelectedMember::Method(method) => {
            let prepared = prepare_class_method_signature(method)?;
            publish_class_method_callable(store, method, &plan.type_, prepared);
        }
    }
    plan_selected_class_member(store, host, symbol)?;
    store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .ok_or_else(|| invariant(ClassInvariant::Publication(plan.class.declaration)))
}

pub(in crate::semantic) fn selected_class_method_return_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
) -> Result<Option<TypeId>, ClassError> {
    let Some(symbol) = store.type_payload(type_).and_then(TypeRecord::symbol) else {
        return Ok(None);
    };
    let Some(record) = store.symbol(symbol) else {
        return Ok(None);
    };
    if record.flags() != SymbolFlags::METHOD
        || record
            .parent()
            .and_then(|owner| store.symbol(owner))
            .is_none_or(|owner| !owner.flags().contains(SymbolFlags::CLASS))
    {
        return Ok(None);
    }
    let plan = match plan_selected_class_member(store, host, symbol) {
        Ok(plan) => plan,
        Err(ClassError::Unsupported(_)) => {
            return values::annotated_method_return_type(store, host, type_);
        }
        Err(error) => return Err(error),
    };
    let SelectedMember::Method(method) = &plan.member else {
        return Ok(None);
    };
    if !method.parameters.is_empty() || method.rest_parameter.is_some() {
        return Ok(None);
    }
    if exact_method_callable(store, method, plan.type_).map(|(value, _)| value) != Some(type_) {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    Ok(Some(plan.type_))
}
