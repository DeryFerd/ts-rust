//! Read-only source and cache checks for ordinary property-object aliases.
//!
//! The type-literal symbol owns the properties. The alias symbol owns the
//! ordered type parameters. Instances retain both identities and a mapper
//! from those original parameters to their effective arguments. Member and
//! property-value publication has separate validation in `instantiated_members`.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId, TypeMapperId,
    declared::cached_ordinary_type_parameter_owner,
    instantiate::PropertyObjectAliasRecovery,
    links::{SourceFileRef, SymbolNodeLinks, TypeAliasLinks, TypeNodeLinks},
    mapper::TypeMapperKind,
    object_members::PlannedProperty,
    relater::RelationUnavailable,
    store::{SemanticStore, SourceNodeParent},
    type_nodes::type_alias_instantiation_cache_key,
    type_records::{
        CacheHashKey, ObjectTypeData, TypeCacheState, TypeData, TypeRecord, type_list_key,
    },
    types::{ObjectFlags, TypeFlags},
};

/// A source template has `type_ == target` and no mapper. Parameters and
/// arguments describe the original property map. Identity fields retain
/// the visible alias, which can have different parameters and argument order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectAliasProjection {
    pub(super) type_: TypeId,
    pub(super) target: TypeId,
    pub(super) declaration: NodeRef,
    pub(super) source_symbol: SemanticSymbolId,
    pub(super) alias_symbol: SemanticSymbolId,
    pub(super) parameters: Vec<TypeId>,
    pub(super) arguments: Vec<TypeId>,
    pub(super) identity_symbol: SemanticSymbolId,
    pub(super) identity_arguments: Vec<TypeId>,
    pub(super) mapper: Option<TypeMapperId>,
    pub(super) properties: Vec<PlannedProperty>,
}

/// Source ownership before any alias parameter or object type is allocated.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectAliasSourceHeader {
    pub(super) alias_declaration: NodeRef,
    pub(super) alias_symbol: SemanticSymbolId,
    pub(super) parameters: Vec<(NodeRef, SemanticSymbolId)>,
}

struct SourceSyntax {
    declaration: NodeRef,
    alias_declaration: NodeRef,
    wrappers: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
    properties: Vec<NodeRef>,
}

struct SourceObject {
    syntax: SourceSyntax,
    source_symbol: SemanticSymbolId,
    alias_symbol: SemanticSymbolId,
    parameters: Vec<TypeId>,
    properties: Vec<PlannedProperty>,
}

/// The first alias slice maps its own parameters, not captured outer ones.
/// This source-only check also runs before parameter or object allocation.
pub(super) fn property_object_alias_has_enclosing_type_parameters<M>(
    store: &SemanticStore<TypeRecord, M>,
    rhs: NodeRef,
) -> Result<bool, RelationUnavailable> {
    let Some(syntax) = source_syntax(store, rhs) else {
        return Ok(false);
    };
    let Some((_, alias)) = source_symbols(store, &syntax)? else {
        return Ok(false);
    };
    alias_has_enclosing_type_parameters(store, syntax.alias_declaration, alias)
}

fn alias_has_enclosing_type_parameters<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<bool, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(alias);
    let mut node = declaration;
    let mut visited = HashSet::from([node]);
    let mut has_parameters = false;
    loop {
        let kind = store.source_node_kind(node).ok_or_else(invalid)?;
        match store.source_node_parent(node).ok_or_else(invalid)? {
            SourceNodeParent::Root => {
                if kind != SyntaxKind::SourceFile
                    || !store.contains_source_file(SourceFileRef::new(store.id(), node))
                {
                    return Err(invalid());
                }
                return Ok(has_parameters);
            }
            SourceNodeParent::Parent(parent) => {
                if parent.arena != declaration.arena
                    || parent.file != declaration.file
                    || !visited.insert(parent)
                    || store.source_node_kind(parent).is_none()
                {
                    return Err(invalid());
                }
                let children = store.source_direct_children(parent).ok_or_else(invalid)?;
                if children.iter().filter(|&&child| child == node).count() != 1 {
                    return Err(invalid());
                }
                for child in children {
                    if store.source_node_parent(child) != Some(SourceNodeParent::Parent(parent)) {
                        return Err(invalid());
                    }
                    has_parameters |= store.source_node_kind(child).ok_or_else(invalid)?
                        == SyntaxKind::TypeParameter;
                }
                node = parent;
            }
        }
    }
}

/// Checks a visible alias owner without requiring its RHS result to exist yet.
pub(super) fn property_object_alias_identity_source_header(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<PropertyObjectAliasSourceHeader, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let [declaration] = record.declarations().ok_or_else(invalid)? else {
        return Err(invalid());
    };
    let declaration = *declaration;
    let body = store
        .source_direct_type_annotation(declaration)
        .ok_or_else(invalid)?;
    let name = store
        .source_child_with_kind(declaration, SyntaxKind::Identifier)
        .ok_or_else(invalid)?;
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || bound_declaration_symbol(store, declaration) != Some(symbol)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || !store.source_declaration_belongs_to_symbol(declaration, symbol)
        || !store.source_symbol_declarations_match(symbol)
        || record.flags() != SymbolFlags::TYPE_ALIAS
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || store.source_identifier_text(name) != record.name().as_utf8()
        || store.source_node_parent(name) != Some(SourceNodeParent::Parent(declaration))
        || store.source_node_parent(body) != Some(SourceNodeParent::Parent(declaration))
        || body.arena != declaration.arena
        || body.file != declaration.file
    {
        return Err(invalid());
    }
    validate_alias_binding(store, declaration, symbol)?;
    if alias_has_enclosing_type_parameters(store, declaration, symbol)? {
        return Err(invalid());
    }
    let mut parameters = store
        .source_direct_children(declaration)
        .ok_or_else(invalid)?
        .into_iter()
        .filter(|&node| store.source_node_kind(node) == Some(SyntaxKind::TypeParameter))
        .collect::<Vec<_>>();
    parameters.sort_by_key(|&node| store.source_node_start(node));
    let mut seen = HashSet::new();
    let parameters = parameters
        .into_iter()
        .map(|node| {
            let parameter = source_parameter_binding(store, node, symbol)?;
            if store.source_node_parent(node) != Some(SourceNodeParent::Parent(declaration))
                || store
                    .symbol(parameter)
                    .is_none_or(|record| record.parent().is_some())
                || !seen.insert(parameter)
            {
                return Err(invalid());
            }
            Ok((node, parameter))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PropertyObjectAliasSourceHeader {
        alias_declaration: declaration,
        alias_symbol: symbol,
        parameters,
    })
}

struct IdentitySourceReference {
    body: NodeRef,
    node: NodeRef,
    wrappers: Vec<NodeRef>,
    name: NodeRef,
    arguments: Vec<NodeRef>,
}

fn identity_source_reference(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
) -> Result<IdentitySourceReference, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(header.alias_symbol);
    let body = store
        .source_direct_type_annotation(header.alias_declaration)
        .ok_or_else(invalid)?;
    let (node, wrappers) = source_parentheses(store, body, header.alias_symbol)?;
    if store.source_node_kind(node) != Some(SyntaxKind::TypeReference) {
        return Err(invalid());
    }
    let children = store.source_direct_children(node).ok_or_else(invalid)?;
    let Some((&name, arguments)) = children.split_first() else {
        return Err(invalid());
    };
    if store.source_node_kind(name) != Some(SyntaxKind::Identifier)
        || store.source_identifier_text(name).is_none_or(str::is_empty)
        || children.iter().any(|&child| {
            child.arena != node.arena
                || child.file != node.file
                || store.source_node_parent(child) != Some(SourceNodeParent::Parent(node))
        })
        || arguments
            .iter()
            .any(|&argument| store.source_node_kind(argument) == Some(SyntaxKind::Identifier))
    {
        return Err(invalid());
    }
    Ok(IdentitySourceReference {
        body,
        node,
        wrappers,
        name,
        arguments: arguments.to_vec(),
    })
}

fn source_parentheses(
    store: &CanonicalTypeMapperStore,
    root: NodeRef,
    owner: SemanticSymbolId,
) -> Result<(NodeRef, Vec<NodeRef>), RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(owner);
    let mut node = root;
    let mut wrappers = Vec::new();
    let mut seen = HashSet::from([root]);
    while store.source_node_kind(node) == Some(SyntaxKind::ParenthesizedType) {
        let children = store.source_direct_children(node).ok_or_else(invalid)?;
        let [child] = children.as_slice() else {
            return Err(invalid());
        };
        if child.arena != root.arena
            || child.file != root.file
            || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(node))
            || !seen.insert(*child)
        {
            return Err(invalid());
        }
        wrappers.push(node);
        node = *child;
    }
    Ok((node, wrappers))
}

#[derive(Clone)]
enum IdentitySourceArgument {
    Parameter(usize),
    Fixed(TypeId),
    RecoveredError(TypeId),
}

/// Proves an original, already-queried RHS argument, not its mapped result.
pub(super) fn validate_property_object_alias_source_argument(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
    node: NodeRef,
    expected: TypeId,
) -> Result<(), RelationUnavailable> {
    if property_object_alias_identity_source_header(store, header.alias_symbol)? != *header
        || !identity_source_reference(store, header)?
            .arguments
            .contains(&node)
    {
        return Err(RelationUnavailable::Symbol(header.alias_symbol));
    }
    identity_source_argument(store, header, node, expected).map(|_| ())
}

fn identity_source_argument(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
    node: NodeRef,
    expected: TypeId,
) -> Result<IdentitySourceArgument, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(header.alias_symbol);
    let (node, wrappers) = source_parentheses(store, node, header.alias_symbol)?;
    for wrapper in wrappers {
        if store.type_node_links(wrapper).is_some_and(|links| {
            links.resolved_type.is_some_and(|type_| type_ != expected)
                || links.outer_type_parameters.is_some()
        }) || store
            .symbol_node_links(wrapper)
            .is_some_and(|links| links != &SymbolNodeLinks::default())
        {
            return Err(invalid());
        }
    }
    if store.type_node_links(node).is_some_and(|links| {
        links.resolved_type.is_some_and(|type_| type_ != expected)
            || links.outer_type_parameters.is_some()
    }) {
        return Err(invalid());
    }
    if store.source_node_kind(node) == Some(SyntaxKind::TypeReference) {
        let children = store.source_direct_children(node).ok_or_else(invalid)?;
        if let [name] = children.as_slice()
            && store.source_node_kind(*name) == Some(SyntaxKind::Identifier)
        {
            let text = store.source_identifier_text(*name).ok_or_else(invalid)?;
            if let Some((index, &(declaration, symbol))) = header
                .parameters
                .iter()
                .enumerate()
                .find(|(_, (_, symbol))| {
                    store
                        .symbol(*symbol)
                        .and_then(|record| record.name().as_utf8())
                        == Some(text)
                })
            {
                if store.source_node_parent(*name) != Some(SourceNodeParent::Parent(node))
                    || source_parameter(store, declaration, header.alias_symbol)? != expected
                    || cached_ordinary_type_parameter_owner(store, expected) != Some(symbol)
                    || store.type_node_links(node)
                        != Some(&TypeNodeLinks {
                            resolved_type: Some(expected),
                            outer_type_parameters: None,
                        })
                    || store.symbol_node_links(node)
                        != Some(&SymbolNodeLinks {
                            resolved_symbol: Some(symbol),
                        })
                    || store.type_node_links(*name).is_some_and(|links| {
                        links.resolved_type.is_some_and(|type_| type_ != expected)
                            || links.outer_type_parameters.is_some()
                    })
                    || store.symbol_node_links(*name).is_some_and(|links| {
                        links.resolved_symbol.is_some_and(|cached| cached != symbol)
                    })
                {
                    return Err(invalid());
                }
                return Ok(IdentitySourceArgument::Parameter(index));
            }
        }
    }
    if argument_contains_variables(store, expected, &mut HashSet::new())?
        || !store.source_type_node_result_is_exact(node, expected, &[])
    {
        return Err(RelationUnavailable::UnsupportedStructuredType(expected));
    }
    Ok(IdentitySourceArgument::Fixed(expected))
}

/// Proves the cold source family and every parameter slot before mutable work.
/// An enclosing generic scope is outside this slice. Warm caches stay exact.
pub(super) fn property_object_alias_source_header(
    store: &CanonicalTypeMapperStore,
    rhs: NodeRef,
) -> Result<Option<PropertyObjectAliasSourceHeader>, RelationUnavailable> {
    let Some(syntax) = source_syntax(store, rhs) else {
        return Ok(None);
    };
    let Some((source_symbol, alias_symbol)) = source_symbols(store, &syntax)? else {
        return Ok(None);
    };
    if property_object_alias_has_enclosing_type_parameters(store, rhs)? {
        return Ok(None);
    }
    source_properties(store, &syntax, source_symbol)?;
    let invalid = || RelationUnavailable::Symbol(alias_symbol);
    let mut parameters = Vec::with_capacity(syntax.parameters.len());
    let mut seen = HashSet::new();
    for &declaration in &syntax.parameters {
        let symbol = source_parameter_binding(store, declaration, alias_symbol)?;
        if store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(syntax.alias_declaration))
            || store
                .symbol(symbol)
                .is_none_or(|record| record.parent().is_some())
            || !seen.insert(symbol)
        {
            return Err(invalid());
        }
        parameters.push((declaration, symbol));
    }
    if let Some(target) = store
        .type_node_links(rhs)
        .and_then(|links| links.resolved_type)
    {
        let projection = property_object_alias_projection(store, target)?.ok_or_else(invalid)?;
        if projection.type_ != projection.target
            || projection.declaration != rhs
            || projection.source_symbol != source_symbol
            || projection.alias_symbol != alias_symbol
        {
            return Err(invalid());
        }
    } else {
        for node in std::iter::once(rhs).chain(syntax.wrappers.iter().copied()) {
            if store
                .type_node_links(node)
                .is_some_and(|links| links != &TypeNodeLinks::default())
                || store
                    .symbol_node_links(node)
                    .is_some_and(|links| links.resolved_symbol.is_some())
            {
                return Err(invalid());
            }
        }
        if store
            .type_alias_links(alias_symbol)
            .is_some_and(|links| links != &TypeAliasLinks::default())
        {
            return Err(invalid());
        }
    }
    Ok(Some(PropertyObjectAliasSourceHeader {
        alias_declaration: syntax.alias_declaration,
        alias_symbol,
        parameters,
    }))
}

/// Reads source-owned parameters before the alias declared-type cache is set.
/// Property annotations stay cold. Existing caches must still be exact.
pub(super) fn property_object_alias_source_parameters(
    store: &CanonicalTypeMapperStore,
    rhs: NodeRef,
) -> Result<Option<(SemanticSymbolId, Vec<TypeId>)>, RelationUnavailable> {
    let Some(syntax) = source_syntax(store, rhs) else {
        return Ok(None);
    };
    let Some(source) = source_object(store, syntax)? else {
        return Ok(None);
    };
    if let Some(target) = store
        .type_node_links(rhs)
        .and_then(|links| links.resolved_type)
    {
        validate_source_header(store, &source, target)?;
        validate_target_cache(store, &source, target)?;
        validate_alias_links(store, &source, Some(target))?;
    } else {
        validate_source_node_links(store, &source, None)?;
        validate_alias_links(store, &source, None)?;
    }
    Ok(Some((source.alias_symbol, source.parameters)))
}

/// Proves only an original property-alias template. Instance mappers remain
/// the responsibility of the canonical projection and instantiation readers.
pub(super) fn property_object_alias_template_matches<M>(
    store: &SemanticStore<TypeRecord, M>,
    alias: SemanticSymbolId,
    body: NodeRef,
    target: TypeId,
    parameters: &[TypeId],
) -> Result<bool, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(alias);
    let mut rhs = body;
    let mut visited = HashSet::from([body]);
    while store.source_node_kind(rhs) == Some(SyntaxKind::ParenthesizedType) {
        let children = store.source_direct_children(rhs).ok_or_else(invalid)?;
        let [child] = children.as_slice() else {
            return Err(invalid());
        };
        if child.arena != body.arena
            || child.file != body.file
            || !visited.insert(*child)
            || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(rhs))
        {
            return Err(invalid());
        }
        rhs = *child;
    }
    if store.source_node_kind(rhs) != Some(SyntaxKind::TypeLiteral) {
        return Ok(false);
    }
    let properties = store.source_direct_children(rhs).ok_or_else(invalid)?;
    if properties.is_empty()
        || properties.iter().any(|property| {
            !matches!(
                store.source_node_kind(*property),
                Some(SyntaxKind::PropertySignature | SyntaxKind::PropertyDeclaration)
            ) || store
                .source_child_with_kind(*property, SyntaxKind::ComputedPropertyName)
                .is_some()
        })
    {
        return Ok(false);
    }
    let Some(SourceNodeParent::Parent(declaration)) = store.source_node_parent(body) else {
        return Err(invalid());
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || store.source_direct_type_annotation(declaration) != Some(body)
    {
        return Err(invalid());
    }
    if !store
        .source_direct_children(declaration)
        .ok_or_else(invalid)?
        .iter()
        .any(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypeParameter))
    {
        return Ok(false);
    }
    let syntax = source_syntax(store, rhs).ok_or_else(invalid)?;
    if syntax.alias_declaration != declaration {
        return Err(invalid());
    }
    if property_object_alias_has_enclosing_type_parameters(store, rhs)? {
        return Err(RelationUnavailable::UnsupportedStructuredType(target));
    }
    let source = source_object(store, syntax)?.ok_or_else(invalid)?;
    if source.alias_symbol != alias || source.parameters != parameters {
        return Err(invalid());
    }
    validate_source_header(store, &source, target)?;
    validate_alias_identity(store, &source, Some(target))?.ok_or_else(invalid)?;
    validate_target_identity_seed(store, &source, target)?;
    Ok(true)
}

/// Distinguishes unrelated objects from malformed claims to this family.
/// This operation does not allocate a semantic identity or resolve a member.
pub(super) fn property_object_alias_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<PropertyObjectAliasProjection>, RelationUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let Some(syntax) = source_syntax_for_record(store, record).or_else(|| {
        let target = match record.data() {
            TypeData::Object(object) => object.target,
            _ => None,
        };
        target
            .and_then(|target| store.type_payload(target))
            .and_then(|target| source_syntax_for_record(store, target))
    }) else {
        return Ok(None);
    };
    if property_object_alias_has_enclosing_type_parameters(store, syntax.declaration)? {
        return Err(RelationUnavailable::UnsupportedStructuredType(type_));
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let source = source_object(store, syntax)?.ok_or_else(invalid)?;
    let target = store
        .type_node_links(source.syntax.declaration)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    validate_source_header(store, &source, target)?;
    let (arguments, mapper, identity_symbol, identity_arguments) = if type_ == target {
        (
            source.parameters.clone(),
            None,
            source.alias_symbol,
            source.parameters.clone(),
        )
    } else {
        let header = validate_instance_header(store, &source, target, type_)?;
        let key = object_identity_cache_key(
            store,
            &header.arguments,
            header.identity_symbol,
            &header.identity_arguments,
        )?;
        if cached_instantiation(&target_object(store, target)?.instantiations, key) != Some(type_) {
            return Err(invalid());
        }
        (
            header.arguments,
            Some(header.mapper),
            header.identity_symbol,
            header.identity_arguments,
        )
    };
    validate_target_cache(store, &source, target)?;
    validate_alias_links(store, &source, Some(target))?;
    Ok(Some(PropertyObjectAliasProjection {
        type_,
        target,
        declaration: source.syntax.declaration,
        source_symbol: source.source_symbol,
        alias_symbol: source.alias_symbol,
        parameters: source.parameters,
        arguments,
        identity_symbol,
        identity_arguments,
        mapper,
        properties: source.properties,
    }))
}

/// Keeps legacy empty aliases outside consumers of the nonempty family.
/// The full proof runs first so conflicting source, alias, or target claims
/// cannot hide behind an empty-looking source symbol.
pub(super) fn property_object_alias_nonempty_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<PropertyObjectAliasProjection>, RelationUnavailable> {
    let projection = property_object_alias_projection(store, type_)?;
    Ok(projection.filter(|projection| !projection.properties.is_empty()))
}

/// Reads physical edges for the member-cycle guard without entering another
/// graph walk. Full source mapping, recovery, and member proofs run afterward.
pub(super) fn cached_property_object_alias_physical_arguments(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<Vec<TypeId>>, RelationUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let Some(syntax) = source_syntax_for_record(store, record).or_else(|| {
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        object
            .target
            .and_then(|target| store.type_payload(target))
            .and_then(|target| source_syntax_for_record(store, target))
    }) else {
        return Ok(None);
    };
    if property_object_alias_has_enclosing_type_parameters(store, syntax.declaration)? {
        return Err(RelationUnavailable::UnsupportedStructuredType(type_));
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let source = source_object(store, syntax)?.ok_or_else(invalid)?;
    let target = store
        .type_node_links(source.syntax.declaration)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    validate_source_header(store, &source, target)?;
    validate_alias_identity(store, &source, Some(target))?;
    validate_target_identity_seed(store, &source, target)?;
    if type_ == target {
        return Ok(Some(source.parameters));
    }
    let header = validate_raw_instance_fields(store, &source, target, type_)?;
    let key = object_identity_cache_key(
        store,
        &header.arguments,
        header.identity_symbol,
        &header.identity_arguments,
    )?;
    if cached_instantiation(&target_object(store, target)?.instantiations, key) != Some(type_) {
        return Err(invalid());
    }
    Ok(Some(header.arguments))
}

fn source_syntax_for_record(
    store: &CanonicalTypeMapperStore,
    record: &TypeRecord,
) -> Option<SourceSyntax> {
    let from_symbol = record
        .symbol()
        .and_then(|symbol| store.symbol(symbol))
        .and_then(|symbol| symbol.declarations())
        .and_then(|declarations| {
            declarations
                .iter()
                .find_map(|&declaration| source_syntax(store, declaration))
        });
    from_symbol.or_else(|| {
        let alias = store.type_alias(record.alias()?)?;
        let owner = store.symbol(alias.symbol()?)?;
        owner.declarations()?.iter().find_map(|&declaration| {
            if store.source_node_kind(declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
                return None;
            }
            let mut rhs = store.source_direct_type_annotation(declaration)?;
            let mut seen = HashSet::from([rhs]);
            while store.source_node_kind(rhs) == Some(SyntaxKind::ParenthesizedType) {
                let children = store.source_direct_children(rhs)?;
                let [child] = children.as_slice() else {
                    return None;
                };
                if !seen.insert(*child)
                    || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(rhs))
                {
                    return None;
                }
                rhs = *child;
            }
            source_syntax(store, rhs)
        })
    })
}

/// Recognition uses source syntax, not mutable type or alias cache metadata.
fn source_syntax<M>(store: &SemanticStore<TypeRecord, M>, rhs: NodeRef) -> Option<SourceSyntax> {
    if store.source_node_kind(rhs) != Some(SyntaxKind::TypeLiteral) {
        return None;
    }
    let mut root = rhs;
    let mut wrappers = Vec::new();
    let mut seen = HashSet::from([rhs]);
    let alias_declaration = loop {
        let SourceNodeParent::Parent(parent) = store.source_node_parent(root)? else {
            return None;
        };
        if parent.arena != rhs.arena || parent.file != rhs.file || !seen.insert(parent) {
            return None;
        }
        match store.source_node_kind(parent)? {
            SyntaxKind::ParenthesizedType => {
                if store.source_direct_children(parent)?.as_slice() != [root] {
                    return None;
                }
                wrappers.push(parent);
                root = parent;
            }
            SyntaxKind::TypeAliasDeclaration => break parent,
            _ => return None,
        }
    };
    if store.source_direct_type_annotation(alias_declaration) != Some(root) {
        return None;
    }
    let mut parameters = store
        .source_direct_children(alias_declaration)?
        .into_iter()
        .filter(|&child| store.source_node_kind(child) == Some(SyntaxKind::TypeParameter))
        .collect::<Vec<_>>();
    if parameters.is_empty() {
        return None;
    }
    parameters.sort_by_key(|&parameter| store.source_node_start(parameter));
    let mut properties = store.source_direct_children(rhs)?;
    if properties.iter().any(|&property| {
        !matches!(
            store.source_node_kind(property),
            Some(SyntaxKind::PropertySignature | SyntaxKind::PropertyDeclaration)
        ) || store
            .source_child_with_kind(property, SyntaxKind::ComputedPropertyName)
            .is_some()
    }) {
        return None;
    }
    properties.sort_by_key(|&property| store.source_node_start(property));
    Some(SourceSyntax {
        declaration: rhs,
        alias_declaration,
        wrappers,
        parameters,
        properties,
    })
}

fn bound_declaration_symbol<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
) -> Option<SemanticSymbolId> {
    match store.symbol_store().source_binding_symbols(declaration) {
        Some([Some(symbol), _]) => store.get_merged_symbol(symbol),
        Some([None, _]) => None,
        None => store.source_declaration_symbol(declaration),
    }
}

fn source_object<M>(
    store: &SemanticStore<TypeRecord, M>,
    syntax: SourceSyntax,
) -> Result<Option<SourceObject>, RelationUnavailable> {
    let Some((source_symbol, alias_symbol)) = source_symbols(store, &syntax)? else {
        return Ok(None);
    };
    let invalid = || RelationUnavailable::Symbol(source_symbol);
    let mut parameters = Vec::with_capacity(syntax.parameters.len());
    for &declaration in &syntax.parameters {
        if store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(syntax.alias_declaration))
        {
            return Err(invalid());
        }
        let parameter = source_parameter(store, declaration, alias_symbol)?;
        if parameters.contains(&parameter) {
            return Err(invalid());
        }
        parameters.push(parameter);
    }
    let properties = source_properties(store, &syntax, source_symbol)?;
    Ok(Some(SourceObject {
        syntax,
        source_symbol,
        alias_symbol,
        parameters,
        properties,
    }))
}

fn source_symbols<M>(
    store: &SemanticStore<TypeRecord, M>,
    syntax: &SourceSyntax,
) -> Result<Option<(SemanticSymbolId, SemanticSymbolId)>, RelationUnavailable> {
    let Some(source_symbol) = bound_declaration_symbol(store, syntax.declaration) else {
        if let Some(alias) = bound_declaration_symbol(store, syntax.alias_declaration) {
            return Err(RelationUnavailable::Symbol(alias));
        }
        return Ok(None);
    };
    let invalid = || RelationUnavailable::Symbol(source_symbol);
    let alias_symbol =
        bound_declaration_symbol(store, syntax.alias_declaration).ok_or_else(invalid)?;
    let source = store.symbol(source_symbol).ok_or_else(invalid)?;
    let alias = store.symbol(alias_symbol).ok_or_else(invalid)?;
    let alias_name = store
        .source_child_with_kind(syntax.alias_declaration, SyntaxKind::Identifier)
        .ok_or_else(invalid)?;
    if store.get_merged_symbol(source_symbol) != Some(source_symbol)
        || store.source_declaration_symbol(syntax.declaration) != Some(source_symbol)
        || !store.source_symbol_declarations_match(source_symbol)
        || source.flags() != SymbolFlags::TYPE_LITERAL
        || source.check_flags() != CheckFlags::NONE
        || source.name() != InternalSymbolName::Type.as_ref()
        || source.declarations() != Some(&[syntax.declaration])
        || source.value_declaration().is_some()
        || source.parent().is_some()
        || source.exports().is_some()
        || source.export_symbol().is_some()
        || store.get_merged_symbol(alias_symbol) != Some(alias_symbol)
        || !store.source_declaration_belongs_to_symbol(syntax.alias_declaration, alias_symbol)
        || !store.source_symbol_declarations_match(alias_symbol)
        || alias.flags() != SymbolFlags::TYPE_ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.declarations() != Some(&[syntax.alias_declaration])
        || alias.value_declaration().is_some()
        || alias.members().is_some()
        || alias.exports().is_some()
        || alias.export_symbol().is_some()
        || store.source_identifier_text(alias_name) != alias.name().as_utf8()
    {
        return Err(invalid());
    }
    validate_alias_binding(store, syntax.alias_declaration, alias_symbol)?;
    Ok(Some((source_symbol, alias_symbol)))
}

fn validate_alias_binding<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<(), RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(alias);
    let record = store.symbol(alias).ok_or_else(invalid)?;
    if let Some(raw_parent) = record.parent() {
        let parent = store.get_merged_symbol(raw_parent).ok_or_else(invalid)?;
        let Some(SourceNodeParent::Parent(mut container)) = store.source_node_parent(declaration)
        else {
            return Err(invalid());
        };
        if store.source_node_kind(container) == Some(SyntaxKind::ModuleBlock) {
            let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(container) else {
                return Err(invalid());
            };
            container = module;
        }
        if !matches!(
            store.source_node_kind(container),
            Some(SyntaxKind::SourceFile | SyntaxKind::ModuleDeclaration)
        ) || bound_declaration_symbol(store, container) != Some(parent)
            || !store.source_merged_symbol_declarations_match(parent)
            || store
                .symbol(parent)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get(record.name()))
                != Some(alias)
        {
            return Err(invalid());
        }
    }
    if let Some([_, Some(local)]) = store.symbol_store().source_binding_symbols(declaration) {
        let local_record = store.symbol(local).ok_or_else(invalid)?;
        if store.get_merged_symbol(local) != Some(local)
            || !store.source_symbol_declarations_match(local)
            || local_record.flags() != SymbolFlags::NONE
            || local_record.check_flags() != CheckFlags::NONE
            || local_record.name() != record.name()
            || local_record.declarations() != Some(&[declaration])
            || local_record.value_declaration().is_some()
            || local_record.members().is_some()
            || local_record.exports().is_some()
            || local_record.parent().is_some()
            || local_record.export_symbol() != Some(alias)
            || record.parent().is_none()
        {
            return Err(invalid());
        }
    }
    Ok(())
}

fn source_parameter<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
) -> Result<TypeId, RelationUnavailable> {
    let symbol = source_parameter_binding(store, declaration, owner)?;
    store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .ok_or(RelationUnavailable::Symbol(symbol))
}

/// Missing type identities are cold, but present parameter caches must agree.
fn source_parameter_binding<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
) -> Result<SemanticSymbolId, RelationUnavailable> {
    let symbol =
        bound_declaration_symbol(store, declaration).ok_or(RelationUnavailable::Symbol(owner))?;
    let invalid = || RelationUnavailable::Symbol(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let type_ = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type);
    let name = store
        .source_child_with_kind(declaration, SyntaxKind::Identifier)
        .ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(container)) = store.source_node_parent(declaration) else {
        return Err(invalid());
    };
    let parent = if matches!(
        store.source_node_kind(container),
        Some(
            SyntaxKind::ClassDeclaration
                | SyntaxKind::ClassExpression
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::TypeLiteral
        )
    ) {
        Some(bound_declaration_symbol(store, container).ok_or_else(invalid)?)
    } else {
        None
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_declaration_symbol(declaration) != Some(symbol)
        || !store.source_symbol_declarations_match(symbol)
        || type_
            .is_some_and(|type_| cached_ordinary_type_parameter_owner(store, type_) != Some(symbol))
        || record.flags() != SymbolFlags::TYPE_PARAMETER
        || record.check_flags() != CheckFlags::NONE
        || record.declarations() != Some(&[declaration])
        || record.value_declaration().is_some()
        || record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != parent
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || store.source_identifier_text(name) != record.name().as_utf8()
    {
        return Err(invalid());
    }
    for node in [declaration, name] {
        if store.type_node_links(node).is_some_and(|links| {
            links
                .resolved_type
                .is_some_and(|cached| Some(cached) != type_)
                || links.outer_type_parameters.is_some()
        }) || store
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|cached| cached != symbol))
        {
            return Err(invalid());
        }
    }
    Ok(symbol)
}

fn source_properties<M>(
    store: &SemanticStore<TypeRecord, M>,
    syntax: &SourceSyntax,
    owner: SemanticSymbolId,
) -> Result<Vec<PlannedProperty>, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidSymbolMembers(owner);
    let members = store.symbol(owner).ok_or_else(invalid)?.members();
    let table = members
        .map(|members| store.symbol_table(members).ok_or_else(invalid))
        .transpose()?;
    if table.map_or(0, ts_binder::semantic::SymbolTable::len) != syntax.properties.len()
        || members.is_some() == syntax.properties.is_empty()
    {
        return Err(invalid());
    }
    let mut properties = Vec::with_capacity(syntax.properties.len());
    let mut seen = HashSet::new();
    for &declaration in &syntax.properties {
        let symbol = bound_declaration_symbol(store, declaration).ok_or_else(invalid)?;
        let record = store.symbol(symbol).ok_or_else(invalid)?;
        let annotation = store
            .source_direct_type_annotation(declaration)
            .ok_or(RelationUnavailable::UnsupportedProperty(symbol))?;
        let children = store
            .source_direct_children(declaration)
            .ok_or_else(invalid)?;
        let mut name = None;
        let mut optional = false;
        let mut readonly = false;
        for &child in &children {
            if child == annotation {
                continue;
            }
            match store.source_node_kind(child) {
                Some(
                    SyntaxKind::Identifier | SyntaxKind::StringLiteral | SyntaxKind::NumericLiteral,
                ) if name.is_none() => name = Some(child),
                Some(SyntaxKind::QuestionToken) if !optional => optional = true,
                Some(SyntaxKind::ReadonlyKeyword) if !readonly => readonly = true,
                _ => return Err(RelationUnavailable::UnsupportedProperty(symbol)),
            }
        }
        let name_node = name.ok_or_else(invalid)?;
        let expected_flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        if store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(syntax.declaration))
            || store.source_declaration_symbol(declaration) != Some(symbol)
            || !store.source_symbol_declarations_match(symbol)
            || store.get_merged_symbol(symbol) != Some(symbol)
            || record.flags() != expected_flags
            || record.check_flags() != CheckFlags::NONE
                && (!readonly || record.check_flags() != CheckFlags::READONLY)
            || record.declarations() != Some(&[declaration])
            || record.value_declaration() != Some(declaration)
            || record.parent() != Some(owner)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || table.and_then(|table| table.get(record.name())) != Some(symbol)
            || !seen.insert(symbol)
            || store.source_node_kind(name_node) == Some(SyntaxKind::Identifier)
                && store.source_identifier_text(name_node) != record.name().as_utf8()
        {
            return Err(invalid());
        }
        // Literal property names come from the original binder symbol. A
        // symbol's name cannot change after allocation.
        properties.push(PlannedProperty {
            declaration,
            symbol,
            name_node,
            type_node: annotation,
            optional,
            readonly,
            name: record.name().to_owned(),
        });
    }
    Ok(properties)
}

fn validate_source_node_links<M>(
    store: &SemanticStore<TypeRecord, M>,
    source: &SourceObject,
    target: Option<TypeId>,
) -> Result<(), RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(source.alias_symbol);
    for node in
        std::iter::once(source.syntax.declaration).chain(source.syntax.wrappers.iter().copied())
    {
        if store.type_node_links(node).is_some_and(|links| {
            links.resolved_type.is_some() && links.resolved_type != target
                || links
                    .outer_type_parameters
                    .as_deref()
                    .is_some_and(|parameters| {
                        target.is_none()
                            || node != source.syntax.declaration
                            || parameters != source.parameters
                    })
        }) || store
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return Err(invalid());
        }
    }
    Ok(())
}

fn target_object<M>(
    store: &SemanticStore<TypeRecord, M>,
    type_: TypeId,
) -> Result<&ObjectTypeData, RelationUnavailable> {
    match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::Object(object)) => Ok(object),
        _ => Err(RelationUnavailable::MalformedStructuredType(type_)),
    }
}

fn validate_source_header<M>(
    store: &SemanticStore<TypeRecord, M>,
    source: &SourceObject,
    target: TypeId,
) -> Result<(), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(target);
    let record = store.type_payload(target).ok_or_else(invalid)?;
    let object = target_object(store, target)?;
    let alias = record
        .alias()
        .and_then(|alias| store.type_alias(alias))
        .ok_or_else(invalid)?;
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(source.source_symbol)
        || !valid_original_object_flags(record.object_flags())
        || object.target.is_some()
        || object.mapper.is_some()
        || alias.symbol() != Some(source.alias_symbol)
        || alias.type_arguments() != Some(source.parameters.as_slice())
        || store
            .type_node_links(source.syntax.declaration)
            .and_then(|links| links.resolved_type)
            != Some(target)
    {
        return Err(invalid());
    }
    validate_source_node_links(store, source, Some(target))
}

struct PropertyObjectAliasInstanceHeader {
    arguments: Vec<TypeId>,
    mapper: TypeMapperId,
    identity_symbol: SemanticSymbolId,
    identity_arguments: Vec<TypeId>,
}

/// Reads scalar instance fields without following argument or recovery edges.
fn validate_raw_instance_fields(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    type_: TypeId,
) -> Result<PropertyObjectAliasInstanceHeader, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let object = target_object(store, type_)?;
    let alias = record
        .alias()
        .and_then(|alias| store.type_alias(alias))
        .ok_or_else(invalid)?;
    let identity_symbol = alias.symbol().ok_or_else(invalid)?;
    let identity_arguments = alias.type_arguments().unwrap_or_default();
    let mapper = object.mapper.ok_or_else(invalid)?;
    if !matches!(
        store.mapper_kind(mapper),
        Some(TypeMapperKind::Simple | TypeMapperKind::Array)
    ) {
        return Err(invalid());
    }
    let arguments = source
        .parameters
        .iter()
        .map(|&parameter| store.map_type(mapper, parameter).ok_or_else(invalid))
        .collect::<Result<Vec<_>, _>>()?;
    if type_ == target
        || record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(source.source_symbol)
        || !valid_instance_object_flag_header(store, record.object_flags(), identity_arguments)?
        || object.target != Some(target)
        || object.instantiations != TypeCacheState::Unallocated
        || alias.type_arguments().is_some() == identity_arguments.is_empty()
        || arguments == source.parameters
            && identity_symbol == source.alias_symbol
            && identity_arguments == arguments
        || store.type_mapper_has_exact_endpoints(mapper, &source.parameters, &arguments)
            != Some(true)
    {
        return Err(invalid());
    }
    validate_property_object_alias_arguments(store, &arguments).map_err(|_| invalid())?;
    validate_property_object_alias_arguments(store, identity_arguments).map_err(|_| invalid())?;
    Ok(PropertyObjectAliasInstanceHeader {
        arguments,
        mapper,
        identity_symbol,
        identity_arguments: identity_arguments.to_vec(),
    })
}

/// Adds computed flags and recovery checks to the scalar instance header.
fn validate_raw_instance_header(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    type_: TypeId,
) -> Result<PropertyObjectAliasInstanceHeader, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let header = validate_raw_instance_fields(store, source, target, type_)?;
    let flags = store
        .type_payload(type_)
        .ok_or_else(invalid)?
        .object_flags();
    if !valid_instance_variable_flags(store, flags, &header.arguments)? {
        return Err(invalid());
    }
    validated_property_object_alias_recovery(store, type_)?;
    Ok(header)
}

/// The source proof reads headers and exact rows, never a full projection.
fn validate_instance_header_without_request(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    type_: TypeId,
) -> Result<PropertyObjectAliasInstanceHeader, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let header = validate_raw_instance_header(store, source, target, type_)?;
    if header.identity_symbol == source.alias_symbol {
        if header.identity_arguments.len() != source.parameters.len() {
            return Err(invalid());
        }
        let arguments = (0..source.parameters.len())
            .map(IdentitySourceArgument::Parameter)
            .collect::<Vec<_>>();
        validate_identity_argument_agreement(
            store,
            type_,
            &arguments,
            &header.arguments,
            &header.identity_arguments,
        )?;
    } else {
        let mapping = identity_source_mapping(store, source, target, header.identity_symbol)?;
        if mapping.parameters.len() != header.identity_arguments.len() {
            return Err(invalid());
        }
        validate_identity_argument_agreement(
            store,
            type_,
            &mapping.arguments,
            &header.arguments,
            &header.identity_arguments,
        )?;
    }
    Ok(header)
}

fn validate_instance_header(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    type_: TypeId,
) -> Result<PropertyObjectAliasInstanceHeader, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let header = validate_instance_header_without_request(store, source, target, type_)?;
    if header.identity_symbol != source.alias_symbol {
        let recovery = validated_property_object_alias_recovery(store, type_)?;
        if recovery.is_some_and(|recovery| {
            (0..header.identity_arguments.len()).any(|slot| recovery.identity_slot_recovered(slot))
        }) {
            return Ok(header);
        }
        let links = store
            .type_alias_links(header.identity_symbol)
            .ok_or_else(invalid)?;
        let key = type_alias_instantiation_cache_key(&header.identity_arguments, None);
        let cached = links
            .instantiations
            .as_ref()
            .and_then(|entries| entries.get(&key))
            .copied();
        validate_source_request_recovery(store, header.identity_symbol, key, cached)
            .map_err(|_| invalid())?;
        if let Some(cached) = cached
            && cached != type_
            && !recovered_alias_request_results_agree(store, source, target, type_, cached, false)?
        {
            return Err(invalid());
        }
    }
    Ok(header)
}

/// An inferred request row can select either exact result after limit recovery.
/// Validate each header without re-entering the inferred request lookup.
fn recovered_alias_request_results_agree(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    expected: TypeId,
    cached: TypeId,
    same_physical_arguments: bool,
) -> Result<bool, RelationUnavailable> {
    if expected == cached {
        return Ok(true);
    }
    if expected == target || cached == target {
        return Ok(false);
    }
    let left = validate_instance_header_without_request(store, source, target, expected)?;
    let right = validate_instance_header_without_request(store, source, target, cached)?;
    let left_recovery = validated_property_object_alias_recovery(store, expected)?;
    let right_recovery = validated_property_object_alias_recovery(store, cached)?;
    if left.identity_symbol != right.identity_symbol
        || left_recovery.is_none() && right_recovery.is_none()
        || same_physical_arguments && left.arguments != right.arguments
    {
        return Ok(false);
    }
    for (type_, header) in [(expected, &left), (cached, &right)] {
        let key = object_identity_cache_key(
            store,
            &header.arguments,
            header.identity_symbol,
            &header.identity_arguments,
        )?;
        if cached_instantiation(&target_object(store, target)?.instantiations, key) != Some(type_) {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_));
        }
    }
    Ok(recovered_argument_lists_match(
        &left.arguments,
        &right.arguments,
        left_recovery,
        right_recovery,
        PropertyObjectAliasRecovery::physical_slot_recovered,
    ) && recovered_argument_lists_match(
        &left.identity_arguments,
        &right.identity_arguments,
        left_recovery,
        right_recovery,
        PropertyObjectAliasRecovery::identity_slot_recovered,
    ))
}

fn recovered_argument_lists_match(
    left: &[TypeId],
    right: &[TypeId],
    left_recovery: Option<&PropertyObjectAliasRecovery>,
    right_recovery: Option<&PropertyObjectAliasRecovery>,
    slot_recovered: fn(&PropertyObjectAliasRecovery, usize) -> bool,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .enumerate()
            .all(|(slot, (&left, &right))| {
                left == right
                    || left_recovery.is_some_and(|recovery| {
                        slot_recovered(recovery, slot) && left == recovery.error_type()
                    })
                    || right_recovery.is_some_and(|recovery| {
                        slot_recovered(recovery, slot) && right == recovery.error_type()
                    })
            })
}

struct IdentitySourceMapping {
    parameters: Vec<TypeId>,
    arguments: Vec<IdentitySourceArgument>,
}

struct IdentitySourceFrame {
    parameters: Vec<TypeId>,
    arguments: Vec<IdentitySourceArgument>,
    declared_arguments: Vec<TypeId>,
    declared_type: TypeId,
}

fn validated_property_object_alias_recovery(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<&PropertyObjectAliasRecovery>, RelationUnavailable> {
    let recovery = store.property_object_alias_recovery(type_);
    if recovery.is_some_and(|recovery| {
        recovery.result() != type_ || !recovery.matches_current_result(store)
    }) {
        return Err(RelationUnavailable::InvalidStructuredMembers(type_));
    }
    Ok(recovery)
}

/// Every read source row to a witnessed result needs its exact request record.
fn validate_source_request_recovery(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    key: CacheHashKey,
    result: Option<TypeId>,
) -> Result<bool, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(symbol);
    let binding = store.property_object_alias_request_recovery(symbol, key);
    let Some(result) = result else {
        return if binding.is_some() {
            Err(invalid())
        } else {
            Ok(false)
        };
    };
    let Some(binding) = binding else {
        return if store.property_object_alias_recovery(result).is_some() {
            Err(invalid())
        } else {
            Ok(false)
        };
    };
    if binding.cache_key() != (symbol, key)
        || binding.result() != result
        || !binding.matches_current_row(store)
    {
        return Err(invalid());
    }
    Ok(true)
}

/// A source-dependent slot can differ only at its own recorded recovery step.
fn validate_identity_argument_agreement(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    source_arguments: &[IdentitySourceArgument],
    physical: &[TypeId],
    identity: &[TypeId],
) -> Result<(), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    if source_arguments.len() != physical.len() {
        return Err(invalid());
    }
    let recovery = validated_property_object_alias_recovery(store, type_)?;
    for (slot, (source, &actual)) in source_arguments.iter().zip(physical).enumerate() {
        let valid = match source {
            IdentitySourceArgument::Parameter(index) => {
                let expected = *identity.get(*index).ok_or_else(invalid)?;
                actual == expected
                    || recovery.is_some_and(|recovery| {
                        recovery.physical_slot_recovered(slot) && actual == recovery.error_type()
                            || recovery.identity_slot_recovered(*index)
                                && expected == recovery.error_type()
                    })
            }
            IdentitySourceArgument::Fixed(expected) => {
                actual == *expected
                    && recovery.is_none_or(|recovery| !recovery.physical_slot_recovered(slot))
            }
            IdentitySourceArgument::RecoveredError(error) => {
                actual == *error
                    && recovery.is_some_and(|recovery| {
                        recovery.error_type() == *error && recovery.physical_slot_recovered(slot)
                    })
            }
        };
        if !valid {
            return Err(invalid());
        }
    }
    Ok(())
}

fn identity_source_parameters(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
) -> Result<Vec<TypeId>, RelationUnavailable> {
    header
        .parameters
        .iter()
        .map(|&(node, _)| source_parameter(store, node, header.alias_symbol))
        .collect()
}

fn identity_source_declared_type(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
    parameters: &[TypeId],
) -> Result<TypeId, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(header.alias_symbol);
    let links = store
        .type_alias_links(header.alias_symbol)
        .ok_or_else(invalid)?;
    let declared = links.declared_type.ok_or_else(invalid)?;
    if links.is_constructor_declared_property {
        return Err(invalid());
    }
    if parameters.is_empty() {
        if links.type_parameters.is_some() || links.instantiations.is_some() {
            return Err(invalid());
        }
    } else {
        let entries = links.instantiations.as_ref().ok_or_else(invalid)?;
        let request = type_alias_instantiation_cache_key(parameters, None);
        let cached = entries.get(&request).copied();
        if links.type_parameters.as_deref() != Some(parameters)
            || entries.get(&type_list_key(parameters)) != Some(&declared)
            || cached.is_some_and(|cached| cached != declared)
        {
            return Err(invalid());
        }
        validate_source_request_recovery(store, header.alias_symbol, request, cached)?;
    }
    Ok(declared)
}

fn original_identity_source_argument(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
    node: NodeRef,
) -> Result<(TypeId, IdentitySourceArgument), RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(header.alias_symbol);
    let (inner, _) = source_parentheses(store, node, header.alias_symbol)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let intrinsic = match store.source_node_kind(inner) {
        Some(SyntaxKind::AnyKeyword) => Some(bootstrap.any_type),
        Some(SyntaxKind::UnknownKeyword) => Some(bootstrap.unknown_type),
        Some(SyntaxKind::StringKeyword) => Some(bootstrap.string_type),
        Some(SyntaxKind::NumberKeyword) => Some(bootstrap.number_type),
        Some(SyntaxKind::BigIntKeyword) => Some(bootstrap.bigint_type),
        Some(SyntaxKind::BooleanKeyword) => Some(bootstrap.boolean_type),
        Some(SyntaxKind::SymbolKeyword) => Some(bootstrap.es_symbol_type),
        Some(SyntaxKind::VoidKeyword) => Some(bootstrap.void_type),
        Some(SyntaxKind::UndefinedKeyword) => Some(bootstrap.undefined_type),
        Some(SyntaxKind::NullKeyword) => Some(bootstrap.null_type),
        Some(SyntaxKind::NeverKeyword) => Some(bootstrap.never_type),
        Some(SyntaxKind::ObjectKeyword) => Some(bootstrap.non_primitive_type),
        Some(SyntaxKind::IntrinsicKeyword) => Some(bootstrap.intrinsic_marker_type),
        _ => None,
    };
    let expected = intrinsic
        .or_else(|| {
            store
                .type_node_links(inner)
                .and_then(|links| links.resolved_type)
        })
        .ok_or_else(invalid)?;
    Ok((
        expected,
        identity_source_argument(store, header, node, expected)?,
    ))
}

/// Wrapper RHS references form one chain. Fold it from the original source
/// without recursively validating a projection or any instantiation map.
#[allow(clippy::too_many_lines)] // Keep source, header, and exact cache-row checks together.
fn identity_source_mapping(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
    identity_symbol: SemanticSymbolId,
) -> Result<IdentitySourceMapping, RelationUnavailable> {
    let mut symbol = identity_symbol;
    let mut seen = HashSet::new();
    let mut frames = Vec::new();
    while symbol != source.alias_symbol {
        let invalid = || RelationUnavailable::Symbol(symbol);
        if !seen.insert(symbol) {
            return Err(invalid());
        }
        let header = property_object_alias_identity_source_header(store, symbol)?;
        let parameters = identity_source_parameters(store, &header)?;
        let declared_type = identity_source_declared_type(store, &header, &parameters)?;
        let declared = validate_raw_instance_header(store, source, target, declared_type)?;
        if declared.identity_symbol != symbol || declared.identity_arguments != parameters {
            return Err(invalid());
        }
        let declared_key =
            object_identity_cache_key(store, &declared.arguments, symbol, &parameters)?;
        if cached_instantiation(&target_object(store, target)?.instantiations, declared_key)
            != Some(declared_type)
        {
            return Err(invalid());
        }
        let reference = identity_source_reference(store, &header)?;
        let referenced = store
            .symbol_node_links(reference.node)
            .and_then(|links| links.resolved_symbol)
            .ok_or_else(invalid)?;
        let referenced_header = property_object_alias_identity_source_header(store, referenced)?;
        if store.type_node_links(reference.node)
            != Some(&TypeNodeLinks {
                resolved_type: Some(declared_type),
                outer_type_parameters: None,
            })
            || store.source_identifier_text(reference.name)
                != store
                    .symbol(referenced)
                    .and_then(|record| record.name().as_utf8())
            || header.parameters.iter().any(|(_, parameter)| {
                store
                    .symbol(*parameter)
                    .and_then(|record| record.name().as_utf8())
                    == store.source_identifier_text(reference.name)
            })
            || reference.arguments.len() != referenced_header.parameters.len()
            || store
                .type_node_links(reference.name)
                .is_some_and(|links| links != &TypeNodeLinks::default())
            || store
                .symbol_node_links(reference.name)
                .is_some_and(|links| {
                    links
                        .resolved_symbol
                        .is_some_and(|cached| cached != referenced)
                })
        {
            return Err(invalid());
        }
        for wrapper in &reference.wrappers {
            if store.type_node_links(*wrapper).is_some_and(|links| {
                links
                    .resolved_type
                    .is_some_and(|type_| type_ != declared_type)
                    || links.outer_type_parameters.is_some()
            }) || store
                .symbol_node_links(*wrapper)
                .is_some_and(|links| links != &SymbolNodeLinks::default())
            {
                return Err(invalid());
            }
        }
        if store.source_direct_type_annotation(header.alias_declaration) != Some(reference.body) {
            return Err(invalid());
        }
        let mut arguments = Vec::with_capacity(reference.arguments.len());
        let mut original_arguments = Vec::with_capacity(reference.arguments.len());
        for argument in &reference.arguments {
            let (type_, source_argument) =
                original_identity_source_argument(store, &header, *argument)?;
            original_arguments.push(type_);
            arguments.push(source_argument);
        }
        let request = object_identity_cache_key(store, &original_arguments, symbol, &parameters)?;
        if store
            .type_alias_links(referenced)
            .and_then(|links| links.instantiations.as_ref())
            .and_then(|entries| entries.get(&request))
            != Some(&declared_type)
        {
            return Err(invalid());
        }
        validate_source_request_recovery(store, referenced, request, Some(declared_type))
            .map_err(|_| invalid())?;
        frames.push(IdentitySourceFrame {
            parameters,
            arguments,
            declared_arguments: declared.arguments,
            declared_type,
        });
        symbol = referenced;
    }
    validate_alias_identity(store, source, Some(target))?
        .ok_or(RelationUnavailable::Symbol(source.alias_symbol))?;
    let mut mapping = IdentitySourceMapping {
        parameters: source.parameters.clone(),
        arguments: (0..source.parameters.len())
            .map(IdentitySourceArgument::Parameter)
            .collect(),
    };
    for frame in frames.into_iter().rev() {
        let invalid = || RelationUnavailable::InvalidStructuredMembers(frame.declared_type);
        if frame.arguments.len() != mapping.parameters.len() {
            return Err(invalid());
        }
        let recovery = validated_property_object_alias_recovery(store, frame.declared_type)?;
        let arguments = mapping
            .arguments
            .into_iter()
            .enumerate()
            .map(|(slot, argument)| match argument {
                IdentitySourceArgument::Parameter(index) => {
                    let forwarded = frame.arguments.get(index).cloned().ok_or_else(invalid)?;
                    Ok(recovery
                        .filter(|recovery| recovery.physical_slot_recovered(slot))
                        .map_or(forwarded, |recovery| {
                            IdentitySourceArgument::RecoveredError(recovery.error_type())
                        }))
                }
                IdentitySourceArgument::Fixed(type_) => Ok(IdentitySourceArgument::Fixed(type_)),
                IdentitySourceArgument::RecoveredError(error) => {
                    Ok(IdentitySourceArgument::RecoveredError(error))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        validate_identity_argument_agreement(
            store,
            frame.declared_type,
            &arguments,
            &frame.declared_arguments,
            &frame.parameters,
        )?;
        mapping = IdentitySourceMapping {
            parameters: frame.parameters,
            arguments,
        };
    }
    Ok(mapping)
}

/// Shares the instance argument proof with the producer before allocation.
pub(super) fn validate_property_object_alias_arguments(
    store: &CanonicalTypeMapperStore,
    arguments: &[TypeId],
) -> Result<(), RelationUnavailable> {
    for &argument in arguments {
        let invalid = || RelationUnavailable::Type(argument);
        let record = store.type_payload(argument).ok_or_else(invalid)?;
        if let TypeData::TypeParameter(_) = record.data() {
            let symbol =
                cached_ordinary_type_parameter_owner(store, argument).ok_or_else(invalid)?;
            let [declaration] = store
                .symbol(symbol)
                .and_then(|symbol| symbol.declarations())
                .ok_or_else(invalid)?
            else {
                return Err(invalid());
            };
            if source_parameter(store, *declaration, symbol)? != argument {
                return Err(invalid());
            }
        }
    }
    Ok(())
}

fn object_cache_key<M>(
    store: &SemanticStore<TypeRecord, M>,
    source: &SourceObject,
    arguments: &[TypeId],
) -> Result<CacheHashKey, RelationUnavailable> {
    object_identity_cache_key(store, arguments, source.alias_symbol, arguments)
}

fn object_identity_cache_key<M>(
    store: &SemanticStore<TypeRecord, M>,
    arguments: &[TypeId],
    identity_symbol: SemanticSymbolId,
    identity_arguments: &[TypeId],
) -> Result<CacheHashKey, RelationUnavailable> {
    let alias = store
        .symbol_store()
        .assigned_global_symbol_id(identity_symbol)
        .ok_or(RelationUnavailable::Symbol(identity_symbol))?;
    Ok(type_alias_instantiation_cache_key(
        arguments,
        Some((alias, identity_arguments)),
    ))
}

fn validate_target_cache(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: TypeId,
) -> Result<(), RelationUnavailable> {
    if store.property_object_alias_recovery(target).is_some() {
        return Err(RelationUnavailable::InvalidStructuredMembers(target));
    }
    validate_target_identity_seed(store, source, target)?;
    let object = target_object(store, target)?;
    let TypeCacheState::Allocated(entries) = &object.instantiations else {
        return Ok(());
    };
    let invalid = || RelationUnavailable::InvalidStructuredMembers(target);
    let identity = object_cache_key(store, source, &source.parameters)?;
    for (&key, &type_) in entries {
        if type_ == target {
            if key != identity {
                return Err(invalid());
            }
        } else {
            let header = validate_instance_header(store, source, target, type_)?;
            if key
                != object_identity_cache_key(
                    store,
                    &header.arguments,
                    header.identity_symbol,
                    &header.identity_arguments,
                )?
            {
                return Err(invalid());
            }
        }
    }
    Ok(())
}

fn validate_target_identity_seed<M>(
    store: &SemanticStore<TypeRecord, M>,
    source: &SourceObject,
    target: TypeId,
) -> Result<(), RelationUnavailable> {
    if let TypeCacheState::Allocated(entries) = &target_object(store, target)?.instantiations
        && entries.get(&object_cache_key(store, source, &source.parameters)?) != Some(&target)
    {
        return Err(RelationUnavailable::InvalidStructuredMembers(target));
    }
    Ok(())
}

fn validate_alias_identity<'store, M>(
    store: &'store SemanticStore<TypeRecord, M>,
    source: &SourceObject,
    target: Option<TypeId>,
) -> Result<Option<&'store TypeAliasLinks>, RelationUnavailable> {
    let Some(links) = store.type_alias_links(source.alias_symbol) else {
        return Ok(None);
    };
    if links == &TypeAliasLinks::default() {
        return Ok(None);
    }
    let invalid = || RelationUnavailable::Symbol(source.alias_symbol);
    let target = target.ok_or_else(invalid)?;
    let entries = links.instantiations.as_ref().ok_or_else(invalid)?;
    let seed = type_list_key(&source.parameters);
    if links.declared_type != Some(target)
        || links.type_parameters.as_deref() != Some(source.parameters.as_slice())
        || links.is_constructor_declared_property
        || entries.get(&seed) != Some(&target)
    {
        return Err(invalid());
    }
    let identity_request = type_alias_instantiation_cache_key(&source.parameters, None);
    if entries
        .get(&identity_request)
        .is_some_and(|&cached| cached != target)
    {
        return Err(invalid());
    }
    Ok(Some(links))
}

fn validate_alias_links(
    store: &CanonicalTypeMapperStore,
    source: &SourceObject,
    target: Option<TypeId>,
) -> Result<(), RelationUnavailable> {
    let Some(links) = validate_alias_identity(store, source, target)? else {
        return Ok(());
    };
    let invalid = || RelationUnavailable::Symbol(source.alias_symbol);
    let target = target.ok_or_else(invalid)?;
    let entries = links.instantiations.as_ref().ok_or_else(invalid)?;
    let seed = type_list_key(&source.parameters);
    let target_cache = &target_object(store, target)?.instantiations;
    for (&key, &type_) in entries {
        if key == seed {
            continue;
        }
        let (arguments, identity_symbol, identity_arguments) = if type_ == target {
            (
                source.parameters.clone(),
                source.alias_symbol,
                source.parameters.clone(),
            )
        } else {
            let header = validate_instance_header(store, source, target, type_)?;
            if cached_instantiation(
                target_cache,
                object_identity_cache_key(
                    store,
                    &header.arguments,
                    header.identity_symbol,
                    &header.identity_arguments,
                )?,
            ) != Some(type_)
            {
                return Err(invalid());
            }
            (
                header.arguments,
                header.identity_symbol,
                header.identity_arguments,
            )
        };
        let native = identity_symbol == source.alias_symbol;
        let identity = store
            .symbol_store()
            .assigned_global_symbol_id(identity_symbol)
            .ok_or_else(invalid)?;
        let branded = Some((identity, identity_arguments.as_slice()));
        let ordinary_request = (0..=arguments.len()).any(|count| {
            native && key == type_alias_instantiation_cache_key(&arguments[..count], None)
                || key == type_alias_instantiation_cache_key(&arguments[..count], branded)
        });
        let recovered_request =
            validate_source_request_recovery(store, source.alias_symbol, key, Some(type_))?;
        if !ordinary_request && !recovered_request {
            return Err(invalid());
        }
        let branded_request = type_alias_instantiation_cache_key(&arguments, branded);
        let branded_result = entries.get(&branded_request).copied();
        validate_source_request_recovery(
            store,
            source.alias_symbol,
            branded_request,
            branded_result,
        )?;
        if branded_result.is_some_and(|cached| cached != type_) {
            return Err(invalid());
        }
        if native {
            let native_request = type_alias_instantiation_cache_key(&arguments, None);
            let cached = entries.get(&native_request).copied();
            validate_source_request_recovery(store, source.alias_symbol, native_request, cached)?;
            if let Some(cached) = cached
                && cached != type_
                && !recovered_alias_request_results_agree(
                    store, source, target, type_, cached, true,
                )?
            {
                return Err(invalid());
            }
        }
    }
    if let TypeCacheState::Allocated(instantiations) = target_cache {
        for &type_ in instantiations.values() {
            let arguments = if type_ == target {
                Some(source.parameters.clone())
            } else {
                let header = validate_instance_header(store, source, target, type_)?;
                (header.identity_symbol == source.alias_symbol).then_some(header.arguments)
            };
            if let Some(arguments) = arguments {
                let request = type_alias_instantiation_cache_key(&arguments, None);
                let cached = entries.get(&request).copied();
                validate_source_request_recovery(store, source.alias_symbol, request, cached)?;
                if let Some(cached) = cached
                    && cached != type_
                    && !recovered_alias_request_results_agree(
                        store, source, target, type_, cached, true,
                    )?
                {
                    return Err(invalid());
                }
            }
        }
    }
    // The request key uses supplied arguments. Defaults can make that vector
    // shorter than the result's arguments. The caller proves omitted defaults.
    Ok(())
}

fn cached_instantiation(cache: &TypeCacheState, key: CacheHashKey) -> Option<TypeId> {
    match cache {
        TypeCacheState::Unallocated => None,
        TypeCacheState::Allocated(entries) => entries.get(&key).copied(),
    }
}

fn valid_original_object_flags(flags: ObjectFlags) -> bool {
    let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    let mutable = ObjectFlags::MEMBERS_RESOLVED | variable_flags;
    flags & !mutable == ObjectFlags::ANONYMOUS
        && (flags & variable_flags == ObjectFlags::NONE || flags & variable_flags == variable_flags)
}

fn valid_instance_object_flag_header(
    store: &CanonicalTypeMapperStore,
    flags: ObjectFlags,
    identity_arguments: &[TypeId],
) -> Result<bool, RelationUnavailable> {
    let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    let contains = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    let mut kind = ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED;
    for &argument in identity_arguments {
        kind |= store
            .type_payload(argument)
            .ok_or(RelationUnavailable::Type(argument))?
            .object_flags()
            & ObjectFlags::PROPAGATING_FLAGS;
    }
    let mutable = ObjectFlags::MEMBERS_RESOLVED | computed | contains;
    Ok(flags & !mutable == kind && (!flags.contains(contains) || flags.contains(computed)))
}

fn valid_instance_variable_flags(
    store: &CanonicalTypeMapperStore,
    flags: ObjectFlags,
    arguments: &[TypeId],
) -> Result<bool, RelationUnavailable> {
    let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    let contains = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if flags.contains(computed) {
        let mut seen = HashSet::new();
        let mut expected = false;
        for &argument in arguments {
            expected |= argument_contains_variables(store, argument, &mut seen)?;
        }
        if flags.contains(contains) != expected {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Reads type edges only. Calling another family validator here can re-enter
/// this target while its whole map is being checked.
fn argument_contains_variables(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> Result<bool, RelationUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    if !active.insert(type_) {
        return Ok(true);
    }
    let mut children = Vec::new();
    let constant = match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Some(true),
        TypeData::TemplateLiteral(template) => {
            if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
                return Err(RelationUnavailable::Type(type_));
            }
            children.extend_from_slice(&template.types);
            None
        }
        TypeData::StringMapping(mapping) => {
            children.push(mapping.target);
            None
        }
        TypeData::Union(union) => {
            children.extend_from_slice(&union.union.types);
            children.extend(union.origin);
            append_alias_arguments(store, record, &mut children)?;
            None
        }
        TypeData::Intersection(intersection) => {
            children.extend_from_slice(&intersection.intersection.types);
            append_alias_arguments(store, record, &mut children)?;
            None
        }
        TypeData::TypeReference(reference) => {
            children.extend_from_slice(reference.resolved_type_arguments.as_deref().ok_or(
                RelationUnavailable::RelationKeyTypeReferenceArguments(type_),
            )?);
            None
        }
        TypeData::Interface(interface) => {
            children.extend_from_slice(
                interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            None
        }
        TypeData::Object(_) if source_syntax_for_record(store, record).is_some() => {
            append_alias_arguments(store, record, &mut children)?;
            None
        }
        TypeData::Object(_)
            if store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| type_ == bootstrap.empty_type_literal_type) =>
        {
            Some(true)
        }
        _ => Some(false),
    };
    let mut contains = constant == Some(false);
    for child in children {
        contains |= argument_contains_variables(store, child, active)?;
    }
    active.remove(&type_);
    Ok(contains)
}

fn append_alias_arguments(
    store: &CanonicalTypeMapperStore,
    record: &TypeRecord,
    arguments: &mut Vec<TypeId>,
) -> Result<(), RelationUnavailable> {
    if let Some(alias) = record.alias() {
        let alias = store
            .type_alias(alias)
            .ok_or(RelationUnavailable::Type(record.id()))?;
        if alias.symbol().is_none() {
            return Err(RelationUnavailable::Type(record.id()));
        }
        arguments.extend_from_slice(alias.type_arguments().unwrap_or_default());
    }
    Ok(())
}

#[cfg(test)]
mod template_flag_tests {
    use super::*;

    #[test]
    fn original_alias_variable_flags_are_absent_or_complete() {
        let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
        let contains = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
        for members in [ObjectFlags::NONE, ObjectFlags::MEMBERS_RESOLVED] {
            let flags = ObjectFlags::ANONYMOUS | members;
            assert!(valid_original_object_flags(flags));
            assert!(valid_original_object_flags(flags | computed | contains));
            assert!(!valid_original_object_flags(flags | computed));
            assert!(!valid_original_object_flags(flags | contains));
            assert!(!valid_original_object_flags(
                flags | ObjectFlags::INSTANTIATED
            ));
        }
    }
}
