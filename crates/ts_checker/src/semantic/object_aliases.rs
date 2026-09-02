//! Read-only source and cache checks for ordinary property-object types.
//!
//! The type-literal symbol owns the properties. The alias symbol owns the
//! ordered type parameters. Direct aliases retain a display identity. Inline
//! literals retain only a mapper from lexical parameters to arguments. Member and
//! property-value publication has separate validation in `instantiated_members`.

use std::collections::{BTreeMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    declared::{cached_ordinary_type_parameter_owner, preflight_node},
    functions::{self, FunctionTypePlan, FunctionTypeState},
    indexed_access_types::SourceAliasIndexedBoundPlan,
    instantiate::PropertyObjectAliasRecovery,
    links::{SourceFileRef, SymbolNodeLinks, TypeAliasLinks, TypeNodeLinks, ValueSymbolLinks},
    mapper::TypeMapperKind,
    object_members::{
        PlannedProperty, PropertyObjectPlan, SourceAliasClosedObject, cached_planned_type_identity,
        source_alias_closed_object,
    },
    relater::RelationUnavailable,
    source_imports::SourcePropertyTypeImportPlan,
    store::{SemanticStore, SourceNodeParent},
    type_nodes::{
        SourceAliasOperandSource, normalize_bigint_literal, normalize_numeric_separators,
        type_alias_instantiation_cache_key,
    },
    type_records::{
        CacheHashKey, LiteralValue, ObjectTypeData, TypeCacheState, TypeData, TypeRecord,
        type_list_key,
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

/// The enclosing alias supplies parameters, but does not name this literal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct InlinePropertyObjectSourceHeader {
    pub(super) declaration: NodeRef,
    pub(super) source_symbol: SemanticSymbolId,
    pub(super) alias_declaration: NodeRef,
    pub(super) parameter_owner: SemanticSymbolId,
    pub(super) parameters: Vec<(NodeRef, SemanticSymbolId)>,
    pub(super) properties: Vec<PlannedProperty>,
}

/// Physical identity of an unaliased literal inside a generic intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct InlinePropertyObjectProjection {
    pub(super) type_: TypeId,
    pub(super) target: TypeId,
    pub(super) declaration: NodeRef,
    pub(super) source_symbol: SemanticSymbolId,
    pub(super) parameter_owner: SemanticSymbolId,
    pub(super) parameters: Vec<TypeId>,
    pub(super) arguments: Vec<TypeId>,
    pub(super) mapper: Option<TypeMapperId>,
    pub(super) properties: Vec<PlannedProperty>,
}

/// Shared physical operations keep the two source proofs distinct.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourcePropertyObjectProjection {
    DirectAlias(PropertyObjectAliasProjection),
    Inline(InlinePropertyObjectProjection),
}

impl SourcePropertyObjectProjection {
    pub(super) fn type_(&self) -> TypeId {
        match self {
            Self::DirectAlias(source) => source.type_,
            Self::Inline(source) => source.type_,
        }
    }

    pub(super) fn target(&self) -> TypeId {
        match self {
            Self::DirectAlias(source) => source.target,
            Self::Inline(source) => source.target,
        }
    }

    pub(super) fn declaration(&self) -> NodeRef {
        match self {
            Self::DirectAlias(source) => source.declaration,
            Self::Inline(source) => source.declaration,
        }
    }

    pub(super) fn source_symbol(&self) -> SemanticSymbolId {
        match self {
            Self::DirectAlias(source) => source.source_symbol,
            Self::Inline(source) => source.source_symbol,
        }
    }

    pub(super) fn parameter_owner(&self) -> SemanticSymbolId {
        match self {
            Self::DirectAlias(source) => source.alias_symbol,
            Self::Inline(source) => source.parameter_owner,
        }
    }

    pub(super) fn parameters(&self) -> &[TypeId] {
        match self {
            Self::DirectAlias(source) => &source.parameters,
            Self::Inline(source) => &source.parameters,
        }
    }

    pub(super) fn arguments(&self) -> &[TypeId] {
        match self {
            Self::DirectAlias(source) => &source.arguments,
            Self::Inline(source) => &source.arguments,
        }
    }

    pub(super) fn mapper(&self) -> Option<TypeMapperId> {
        match self {
            Self::DirectAlias(source) => source.mapper,
            Self::Inline(source) => source.mapper,
        }
    }

    pub(super) fn properties(&self) -> &[PlannedProperty] {
        match self {
            Self::DirectAlias(source) => &source.properties,
            Self::Inline(source) => &source.properties,
        }
    }

    pub(super) fn display_identity(&self) -> Option<(SemanticSymbolId, &[TypeId])> {
        match self {
            Self::DirectAlias(source) => Some((source.identity_symbol, &source.identity_arguments)),
            Self::Inline(_) => None,
        }
    }

    pub(super) fn identity_arguments(&self) -> &[TypeId] {
        self.display_identity()
            .map_or(&[], |(_, arguments)| arguments)
    }

    pub(super) fn as_direct_alias(&self) -> Option<&PropertyObjectAliasProjection> {
        match self {
            Self::DirectAlias(source) => Some(source),
            Self::Inline(_) => None,
        }
    }
}

/// A direct nongeneric alias body with no captured source parameters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClosedTypeAliasSourceHeader {
    pub(super) declaration: NodeRef,
    pub(super) source_symbol: SemanticSymbolId,
    pub(super) alias_declaration: NodeRef,
    pub(super) alias_symbol: SemanticSymbolId,
}

/// A query-local proof of one real alias bound or default and its consumed children.
#[derive(Clone, Debug)]
pub(super) struct SourceAliasOperandGraph {
    source: SourceAliasOperandSource,
    node: NodeRef,
    type_: TypeId,
    path: Vec<(NodeRef, NodeRef)>,
    nodes: BTreeMap<NodeRef, SourceAliasOperandNode>,
}

#[derive(Clone, Debug)]
struct SourceAliasOperandNode {
    type_: TypeId,
    kind: SyntaxKind,
    parent: SourceNodeParent,
    children: Vec<NodeRef>,
    closed: bool,
    proof: SourceAliasOperandProof,
}

#[derive(Clone, Debug)]
enum SourceAliasOperandProof {
    Intrinsic,
    Literal(LiteralValue),
    Parameter(SemanticSymbolId),
    Parenthesized(NodeRef),
    Named {
        symbol: SemanticSymbolId,
        body: NodeRef,
        import: Option<SourcePropertyTypeImportPlan>,
    },
    Object {
        object: Box<SourceAliasClosedObject>,
        children: Vec<NodeRef>,
        alias: Option<SemanticSymbolId>,
    },
    Function(Box<FunctionTypePlan>),
    Union {
        children: Vec<NodeRef>,
        alias: Option<SemanticSymbolId>,
    },
    Array {
        element: NodeRef,
        named_target: Option<SemanticSymbolId>,
        readonly: bool,
    },
    StringMapping {
        symbol: SemanticSymbolId,
        argument: NodeRef,
    },
    Template {
        texts: Vec<String>,
        placeholders: Vec<NodeRef>,
        spans: Vec<(NodeRef, NodeRef, NodeRef)>,
    },
    Indexed(Box<SourceAliasIndexedBoundPlan>),
}

impl SourceAliasOperandGraph {
    pub(super) fn source(&self) -> &SourceAliasOperandSource {
        &self.source
    }

    pub(super) fn validate_retained(
        &self,
        store: &CanonicalTypeMapperStore,
        source_type: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), RelationUnavailable> {
        let invalid = || RelationUnavailable::InvalidStructuredMembers(source_type);
        self.source
            .validate_retained(store)
            .map_err(|_| invalid())?;
        if source_type != self.type_
            || source_alias_operand_path(store, &self.source, self.node)? != self.path
        {
            return Err(invalid());
        }
        self.validate_node(store, self.node, array_targets, &mut HashSet::new())
    }

    /// The source indexed reader can check its object before its own result exists.
    pub(super) fn validate_closed_object(
        &self,
        store: &CanonicalTypeMapperStore,
        node: NodeRef,
        type_: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), RelationUnavailable> {
        let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
        self.source
            .validate_retained(store)
            .map_err(|_| invalid())?;
        let row = self.nodes.get(&node).ok_or_else(invalid)?;
        if row.type_ != type_
            || !row.closed
            || !matches!(
                store.type_payload(type_).map(TypeRecord::data),
                Some(TypeData::Object(_))
            )
        {
            return Err(invalid());
        }
        self.validate_node(store, node, array_targets, &mut HashSet::new())
    }

    /// Only source results and their canonical union constituents enter this mapper.
    pub(super) fn mapping_type_is_closed(
        &self,
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<bool, RelationUnavailable> {
        self.validate_retained(store, self.type_, array_targets)?;
        if self.nodes.values().any(|row| row.type_ == type_) {
            return self.closed_semantic_child(store, type_, &mut HashSet::new());
        }
        for row in self.nodes.values() {
            let mut pending = vec![row.type_];
            let mut seen = HashSet::new();
            while let Some(parent) = pending.pop() {
                if !seen.insert(parent) {
                    continue;
                }
                let Some(TypeData::Union(union)) = store.type_payload(parent).map(TypeRecord::data)
                else {
                    continue;
                };
                if union.union.types.contains(&type_) || union.origin == Some(type_) {
                    return self.closed_semantic_child(store, type_, &mut HashSet::new());
                }
                pending.extend_from_slice(&union.union.types);
                pending.extend(union.origin);
            }
        }
        Err(RelationUnavailable::InvalidStructuredMembers(type_))
    }

    fn closed_semantic_child(
        &self,
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, RelationUnavailable> {
        let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
        if !active.insert(type_) {
            return Err(invalid());
        }
        let closed = match store.type_payload(type_).ok_or_else(invalid)?.data() {
            TypeData::Intrinsic(_) | TypeData::Literal(_) => true,
            TypeData::TypeParameter(_) => {
                if !self.nodes.values().any(|row| {
                    row.type_ == type_ && matches!(row.proof, SourceAliasOperandProof::Parameter(_))
                }) {
                    return Err(invalid());
                }
                false
            }
            TypeData::Union(union) => {
                let mut closed = true;
                for child in &union.union.types {
                    closed &= self.closed_semantic_child(store, *child, active)?;
                }
                closed
            }
            TypeData::TypeReference(reference) => {
                if !self.nodes.values().any(|row| {
                    row.type_ == type_ && matches!(row.proof, SourceAliasOperandProof::Array { .. })
                }) {
                    return Err(invalid());
                }
                let Some([element]) = reference.resolved_type_arguments.as_deref() else {
                    return Err(invalid());
                };
                self.closed_semantic_child(store, *element, active)?
            }
            _ => self
                .nodes
                .values()
                .find(|row| row.type_ == type_)
                .filter(|row| row.closed)
                .map(|_| true)
                .ok_or_else(invalid)?,
        };
        active.remove(&type_);
        Ok(closed)
    }

    fn child_type(&self, node: NodeRef) -> Result<TypeId, RelationUnavailable> {
        self.nodes
            .get(&node)
            .map(|row| row.type_)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(self.type_))
    }

    #[allow(clippy::too_many_lines)] // Each source form rechecks its own existing result reader.
    fn validate_node(
        &self,
        store: &CanonicalTypeMapperStore,
        node: NodeRef,
        array_targets: Option<CanonicalArrayTargets>,
        active: &mut HashSet<NodeRef>,
    ) -> Result<(), RelationUnavailable> {
        let row = self
            .nodes
            .get(&node)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(self.type_))?;
        let invalid = || RelationUnavailable::InvalidStructuredMembers(row.type_);
        if !active.insert(node)
            || store.source_node_kind(node) != Some(row.kind)
            || store.source_node_parent(node) != Some(row.parent)
            || store.source_direct_children(node).as_deref() != Some(row.children.as_slice())
            || row.children.iter().any(|&child| {
                store.source_node_parent(child) != Some(SourceNodeParent::Parent(node))
            })
            || !source_alias_node_result_matches(store, node, row.type_)
        {
            return Err(invalid());
        }
        let mut children = Vec::new();
        let valid = match &row.proof {
            SourceAliasOperandProof::Intrinsic => {
                store.source_type_node_result_is_exact(node, row.type_, &[])
                    || row.kind == SyntaxKind::LiteralType
                        && store
                            .source_child_with_kind(node, SyntaxKind::NullKeyword)
                            .is_some()
            }
            SourceAliasOperandProof::Literal(value) => {
                source_alias_literal_matches(store, row.type_, value)
                    && store
                        .symbol_node_links(node)
                        .is_none_or(|links| links == &SymbolNodeLinks::default())
            }
            SourceAliasOperandProof::Parameter(symbol) => {
                source_alias_parameter_matches(store, &self.source, node, row.type_, *symbol)
            }
            SourceAliasOperandProof::Parenthesized(child) => {
                children.push(*child);
                row.children.as_slice() == [*child]
                    && self.child_type(*child)? == row.type_
                    && store
                        .symbol_node_links(node)
                        .is_none_or(|links| links == &SymbolNodeLinks::default())
            }
            SourceAliasOperandProof::Named {
                symbol,
                body,
                import,
            } => {
                children.push(*body);
                let header = property_object_alias_identity_source_header(store, *symbol)?;
                header.parameters.is_empty()
                    && store.source_direct_type_annotation(header.alias_declaration) == Some(*body)
                    && self.child_type(*body)? == row.type_
                    && source_alias_reference_matches(store, node, *symbol, import.as_ref())
                    && super::object_members::cached_alias_reference_annotation_matches(
                        store,
                        *symbol,
                        &[],
                        row.type_,
                    )
            }
            SourceAliasOperandProof::Object {
                object,
                children: object_children,
                alias,
            } => {
                children.extend_from_slice(object_children);
                object.validate_retained(store).map_err(|_| invalid())?;
                source_alias_direct_owner(store, node)? == *alias
                    && children
                        .iter()
                        .all(|child| self.nodes.get(child).is_some_and(|row| row.closed))
            }
            SourceAliasOperandProof::Function(function) => {
                children.push(function.return_type);
                let expected_return = self.child_type(function.return_type)?;
                let FunctionTypeState::Resolved { type_, signature } =
                    functions::function_type_state(store, function, false)
                        .map_err(|_| invalid())?
                else {
                    return Err(invalid());
                };
                row.children.as_slice() == [function.return_type]
                    && type_ == row.type_
                    && store.source_declaration_belongs_to_symbol(node, function.symbol)
                    && store.source_symbol_declarations_match(function.symbol)
                    && store.source_declaration_belongs_to_symbol(node, function.call_symbol)
                    && store.source_symbol_declarations_match(function.call_symbol)
                    && source_alias_direct_owner(store, node)? == function.alias_symbol
                    && !store.signature_has_circular_return_type(signature)
                    && store.signature(signature).is_some_and(|signature| {
                        signature
                            .resolved_return_type()
                            .is_none_or(|actual| actual == expected_return)
                    })
                    && self
                        .nodes
                        .get(&function.return_type)
                        .is_some_and(|row| row.closed)
            }
            SourceAliasOperandProof::Union {
                children: union_children,
                alias,
            } => {
                children.extend_from_slice(union_children);
                for child in &children {
                    self.validate_node(store, *child, array_targets, active)?;
                }
                let types = children
                    .iter()
                    .map(|&child| self.child_type(child))
                    .collect::<Result<Vec<_>, _>>()?;
                children.clear();
                source_alias_direct_owner(store, node)? == *alias
                    && store
                        .cached_annotation_union_type(&types, alias.map(|symbol| (symbol, &[][..])))
                        .map_err(|_| invalid())?
                        == Some(row.type_)
            }
            SourceAliasOperandProof::Array {
                element,
                named_target,
                readonly,
            } => {
                children.push(*element);
                let targets = array_targets.ok_or(
                    RelationUnavailable::UnavailableCanonicalArrayTarget(row.type_),
                )?;
                let reference = store
                    .canonical_array_reference_with_targets(targets, row.type_)
                    .map_err(|_| invalid())?
                    .ok_or_else(invalid)?;
                let syntax = match named_target {
                    None => {
                        row.kind == SyntaxKind::ArrayType && row.children.as_slice() == [*element]
                    }
                    Some(symbol) => {
                        let target = if *readonly {
                            targets.readonly_array_type()
                        } else {
                            targets.array_type()
                        };
                        store.type_payload(target).and_then(TypeRecord::symbol) == Some(*symbol)
                            && store
                                .symbol_node_links(node)
                                .and_then(|links| links.resolved_symbol)
                                == Some(*symbol)
                            && matches!(row.children.as_slice(), [name, argument]
                                if *argument == *element
                                    && store.source_node_kind(*name) == Some(SyntaxKind::Identifier)
                                    && store.source_identifier_text(*name) == store.symbol(*symbol).and_then(|record| record.name().as_utf8())
                                    && store.symbol_node_links(*name).and_then(|links| links.resolved_symbol).is_none_or(|cached| cached == *symbol))
                    }
                };
                syntax
                    && reference.element_type == self.child_type(*element)?
                    && reference.readonly == *readonly
                    && !reference.array_literal
            }
            SourceAliasOperandProof::StringMapping { symbol, argument } => {
                children.push(*argument);
                source_alias_string_mapping_matches(store, node, *symbol)
                    && store
                        .cached_resolved_string_mapping_type(*symbol, self.child_type(*argument)?)
                        .map_err(|_| invalid())?
                        == Some(row.type_)
            }
            SourceAliasOperandProof::Template {
                texts,
                placeholders,
                spans,
            } => {
                children.extend_from_slice(placeholders);
                let types = placeholders
                    .iter()
                    .map(|&child| self.child_type(child))
                    .collect::<Result<Vec<_>, _>>()?;
                spans.iter().all(|&(span, placeholder, literal)| {
                    store.source_node_kind(span) == Some(SyntaxKind::TemplateLiteralTypeSpan)
                        && store.source_node_parent(span) == Some(SourceNodeParent::Parent(node))
                        && store.source_node_parent(placeholder)
                            == Some(SourceNodeParent::Parent(span))
                        && store.source_node_parent(literal) == Some(SourceNodeParent::Parent(span))
                        && store.source_direct_children(span).as_deref()
                            == Some(&[placeholder, literal][..])
                }) && store
                    .cached_resolved_template_literal_type(texts, &types)
                    .map_err(|_| invalid())?
                    == Some(row.type_)
            }
            SourceAliasOperandProof::Indexed(plan) => {
                children.extend([plan.object(), plan.index()]);
                super::indexed_access_types::cached_source_alias_indexed_bound(
                    store,
                    plan,
                    self,
                    self.child_type(plan.object())?,
                    self.child_type(plan.index())?,
                    array_targets,
                )
                .map_err(|_| invalid())?
                    == Some(row.type_)
            }
        };
        if !valid {
            return Err(invalid());
        }
        for child in children {
            self.validate_node(store, child, array_targets, active)?;
        }
        active.remove(&node);
        Ok(())
    }
}

fn source_alias_operand_path(
    store: &CanonicalTypeMapperStore,
    source: &SourceAliasOperandSource,
    mut child: NodeRef,
) -> Result<Vec<(NodeRef, NodeRef)>, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(source.alias());
    let mut path = Vec::new();
    let mut seen = HashSet::new();
    while child != source.root() {
        if !seen.insert(child) {
            return Err(invalid());
        }
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(child) else {
            return Err(invalid());
        };
        let children = store.source_direct_children(parent).ok_or_else(invalid)?;
        let valid = match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType | SyntaxKind::ArrayType) => {
                children.as_slice() == [child]
            }
            Some(SyntaxKind::UnionType) => children.len() >= 2 && children.contains(&child),
            Some(SyntaxKind::IndexedAccessType) => children.len() == 2 && children.contains(&child),
            _ => false,
        };
        if !valid || parent.arena != source.root().arena || parent.file != source.root().file {
            return Err(invalid());
        }
        path.push((child, parent));
        child = parent;
    }
    Ok(path)
}

fn source_alias_direct_owner(
    store: &CanonicalTypeMapperStore,
    mut node: NodeRef,
) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
    let mut seen = HashSet::new();
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) {
        if !seen.insert(node) {
            return Err(RelationUnavailable::MissingBootstrap);
        }
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType)
                if store.source_direct_children(parent).as_deref() == Some(&[node][..]) =>
            {
                node = parent
            }
            Some(SyntaxKind::TypeAliasDeclaration)
                if store.source_direct_type_annotation(parent) == Some(node) =>
            {
                let alias = bound_declaration_symbol(store, parent)
                    .ok_or(RelationUnavailable::MissingBootstrap)?;
                let header = property_object_alias_identity_source_header(store, alias)?;
                if header.alias_declaration != parent || !header.parameters.is_empty() {
                    return Err(RelationUnavailable::Symbol(alias));
                }
                return Ok(Some(alias));
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

fn source_alias_parameter_matches(
    store: &CanonicalTypeMapperStore,
    source: &SourceAliasOperandSource,
    node: NodeRef,
    type_: TypeId,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(index) = source
        .parameters()
        .iter()
        .position(|pair| *pair == source.parameter())
    else {
        return false;
    };
    source.parameters()[..index]
        .iter()
        .any(|&(declaration, parameter)| {
            parameter == symbol
                && cached_ordinary_type_parameter_owner(store, type_) == Some(symbol)
                && store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type)
                    == Some(type_)
                && store.source_declaration_symbol(declaration) == Some(symbol)
        })
        && source_alias_reference_matches(store, node, symbol, None)
}

fn source_alias_reference_matches(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
    import: Option<&SourcePropertyTypeImportPlan>,
) -> bool {
    let Some(children) = store.source_direct_children(node) else {
        return false;
    };
    let [name] = children.as_slice() else {
        return false;
    };
    if store.source_node_kind(node) != Some(SyntaxKind::TypeReference)
        || store.source_node_kind(*name) != Some(SyntaxKind::Identifier)
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return false;
    }
    if let Some(import) = import {
        return import.annotation() == node
            && import.target_symbol() == symbol
            && import.validate_retained(store).is_ok();
    }
    store
        .symbol_node_links(node)
        .and_then(|links| links.resolved_symbol)
        == Some(symbol)
        && store
            .symbol_node_links(*name)
            .and_then(|links| links.resolved_symbol)
            .is_none_or(|cached| cached == symbol)
        && store.symbol(symbol).is_some_and(|record| {
            record.name().as_utf8() == store.source_identifier_text(*name)
                && record.declarations().is_some_and(|declarations| {
                    declarations.iter().all(|declaration| {
                        declaration.file == node.file && declaration.arena == node.arena
                    })
                })
        })
}

fn source_alias_string_mapping_matches(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let Some([declaration]) = record.declarations() else {
        return false;
    };
    let Some(body) = store.source_direct_type_annotation(*declaration) else {
        return false;
    };
    store.source_node_kind(body) == Some(SyntaxKind::IntrinsicKeyword)
        && store.string_mapping_kind(symbol).is_ok()
        && record.flags() == SymbolFlags::TYPE_ALIAS
        && record.check_flags() == CheckFlags::NONE
        && store.source_declaration_belongs_to_symbol(*declaration, symbol)
        && store.source_symbol_declarations_match(symbol)
        && store.source_global_bindings().and_then(|bindings| bindings.get(record.name())).is_some_and(|binding| binding.symbol == symbol)
        && store.symbol_node_links(node).and_then(|links| links.resolved_symbol) == Some(symbol)
        && store.source_direct_children(node).is_some_and(|children| {
            matches!(children.as_slice(), [name, _]
                if store.source_identifier_text(*name) == record.name().as_utf8()
                    && store.symbol_node_links(*name).and_then(|links| links.resolved_symbol).is_none_or(|cached| cached == symbol))
        })
}

fn source_alias_literal_matches(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    value: &LiteralValue,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let TypeData::Literal(literal) = record.data() else {
        return false;
    };
    let (cached, flags) = match value {
        LiteralValue::String(value) => (
            bootstrap.cached_string_literal_type(value),
            TypeFlags::STRING_LITERAL,
        ),
        LiteralValue::Number(value) => (
            bootstrap.cached_number_literal_type(*value),
            TypeFlags::NUMBER_LITERAL,
        ),
        LiteralValue::Boolean(value) => (
            Some(if *value {
                bootstrap.regular_true_type
            } else {
                bootstrap.regular_false_type
            }),
            TypeFlags::BOOLEAN_LITERAL,
        ),
        LiteralValue::BigInt(value) => (
            bootstrap.cached_bigint_literal_type(value),
            TypeFlags::BIG_INT_LITERAL,
        ),
        LiteralValue::ComputedEnum => return false,
    };
    cached == Some(type_)
        && literal.value == *value
        && literal.regular_type == type_
        && record.flags() == flags
        && record.object_flags() == ObjectFlags::NONE
        && record.symbol().is_none()
        && record.alias().is_none()
}

#[allow(clippy::too_many_arguments)] // The current query owns all source and child capabilities.
pub(super) fn build_source_alias_operand_graph(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    operand: &SourceAliasOperandSource,
    node: NodeRef,
    source_type: TypeId,
    objects: &[PropertyObjectPlan],
    imports: &[SourcePropertyTypeImportPlan],
    indexed: &[SourceAliasIndexedBoundPlan],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceAliasOperandGraph, RelationUnavailable> {
    operand
        .validate_retained(store)
        .map_err(|_| RelationUnavailable::Symbol(operand.alias()))?;
    let mut graph = SourceAliasOperandGraph {
        source: operand.clone(),
        node,
        type_: source_type,
        path: source_alias_operand_path(store, operand, node)?,
        nodes: BTreeMap::new(),
    };
    SourceAliasOperandGraphBuilder {
        store,
        host,
        objects,
        imports,
        indexed,
        array_targets,
        active: HashSet::new(),
        graph: &mut graph,
    }
    .read(node, source_type, false)?;
    graph.validate_retained(store, source_type, array_targets)?;
    Ok(graph)
}

struct SourceAliasOperandGraphBuilder<'a, 'host> {
    store: &'a CanonicalTypeMapperStore,
    host: &'a DeclaredTypeHost<'host>,
    objects: &'a [PropertyObjectPlan],
    imports: &'a [SourcePropertyTypeImportPlan],
    indexed: &'a [SourceAliasIndexedBoundPlan],
    array_targets: Option<CanonicalArrayTargets>,
    active: HashSet<NodeRef>,
    graph: &'a mut SourceAliasOperandGraph,
}

impl SourceAliasOperandGraphBuilder<'_, '_> {
    fn read_child(&mut self, node: NodeRef, closed: bool) -> Result<TypeId, RelationUnavailable> {
        let type_ = source_alias_cached_child(self.store, node).ok_or(
            RelationUnavailable::InvalidStructuredMembers(self.graph.type_),
        )?;
        self.read(node, type_, closed)?;
        Ok(type_)
    }

    #[allow(clippy::too_many_lines)] // This records existing source results without another evaluator.
    fn read(
        &mut self,
        node: NodeRef,
        type_: TypeId,
        closed: bool,
    ) -> Result<(), RelationUnavailable> {
        let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
        if let Some(row) = self.graph.nodes.get(&node) {
            return if row.type_ == type_ && (!closed || row.closed) {
                Ok(())
            } else {
                Err(invalid())
            };
        }
        if !self.active.insert(node) {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_));
        }
        let record = preflight_node(self.store, self.host, node).map_err(|_| invalid())?;
        let children = self
            .store
            .source_direct_children(node)
            .ok_or_else(invalid)?;
        let parent = self.store.source_node_parent(node).ok_or_else(invalid)?;
        if self.store.source_node_kind(node) != Some(record.kind)
            || !source_alias_node_result_matches(self.store, node, type_)
            || children.iter().any(|&child| {
                self.store.source_node_parent(child) != Some(SourceNodeParent::Parent(node))
            })
        {
            return Err(invalid());
        }
        let mut row_closed = true;
        let proof = match &record.data {
            NodeData::KeywordTypeNode(_) if record.kind != SyntaxKind::IntrinsicKeyword => {
                SourceAliasOperandProof::Intrinsic
            }
            NodeData::LiteralTypeNode(literal) => {
                let literal = NodeRef::new(node.arena, node.file, literal.literal);
                if self.store.source_node_parent(literal) != Some(SourceNodeParent::Parent(node)) {
                    return Err(invalid());
                }
                match source_alias_literal_value(self.store, self.host, literal)
                    .map_err(|_| invalid())?
                {
                    Some(value) => SourceAliasOperandProof::Literal(value),
                    None => SourceAliasOperandProof::Intrinsic,
                }
            }
            NodeData::ParenthesizedTypeNode(inner) => {
                let child = NodeRef::new(node.arena, node.file, inner.type_);
                if self.read_child(child, closed)? != type_ {
                    return Err(invalid());
                }
                row_closed = self.graph.nodes[&child].closed;
                SourceAliasOperandProof::Parenthesized(child)
            }
            NodeData::TypeReferenceNode(reference) => {
                let name = NodeRef::new(node.arena, node.file, reference.type_name);
                let symbol = self
                    .store
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol)
                    .ok_or_else(invalid)?;
                let arguments = reference
                    .type_arguments
                    .as_ref()
                    .map_or(&[][..], |arguments| arguments.nodes.as_slice());
                let import = self
                    .imports
                    .iter()
                    .find(|plan| plan.annotation() == node)
                    .cloned();
                if let Some(import) = &import {
                    import
                        .validate_retained(self.store)
                        .map_err(|_| invalid())?;
                } else {
                    let mut resolver = self
                        .host
                        .name_resolver_host(self.store)
                        .map_err(|_| invalid())?;
                    let resolved = resolver
                        .resolve_entity_name(name, SymbolFlags::TYPE)
                        .map_err(|_| invalid())?;
                    if resolved.and_then(|symbol| self.store.get_merged_symbol(symbol))
                        != Some(symbol)
                    {
                        return Err(invalid());
                    }
                }
                if arguments.is_empty()
                    && cached_ordinary_type_parameter_owner(self.store, type_) == Some(symbol)
                {
                    if closed
                        || !source_alias_parameter_matches(
                            self.store,
                            &self.graph.source,
                            node,
                            type_,
                            symbol,
                        )
                    {
                        return Err(invalid());
                    }
                    row_closed = false;
                    SourceAliasOperandProof::Parameter(symbol)
                } else if arguments.len() == 1
                    && import.is_none()
                    && source_alias_string_mapping_matches(self.store, node, symbol)
                {
                    let argument = NodeRef::new(node.arena, node.file, arguments[0]);
                    self.read_child(argument, true)?;
                    SourceAliasOperandProof::StringMapping { symbol, argument }
                } else if arguments.len() == 1
                    && import.is_none()
                    && let Some(targets) = self.array_targets
                    && let Some(array) = self
                        .store
                        .canonical_array_reference_with_targets(targets, type_)
                        .map_err(|_| invalid())?
                {
                    let element = NodeRef::new(node.arena, node.file, arguments[0]);
                    if self.read_child(element, closed)? != array.element_type {
                        return Err(invalid());
                    }
                    row_closed = self.graph.nodes[&element].closed;
                    SourceAliasOperandProof::Array {
                        element,
                        named_target: Some(symbol),
                        readonly: array.readonly,
                    }
                } else {
                    if !arguments.is_empty() {
                        return Err(RelationUnavailable::UnsupportedStructuredType(type_));
                    }
                    let symbol = import
                        .as_ref()
                        .map_or(symbol, SourcePropertyTypeImportPlan::target_symbol);
                    let header = property_object_alias_identity_source_header(self.store, symbol)?;
                    if !header.parameters.is_empty() {
                        return Err(RelationUnavailable::UnsupportedStructuredType(type_));
                    }
                    let body = self
                        .store
                        .source_direct_type_annotation(header.alias_declaration)
                        .ok_or_else(invalid)?;
                    if self.read_child(body, true)? != type_ {
                        return Err(invalid());
                    }
                    SourceAliasOperandProof::Named {
                        symbol,
                        body,
                        import,
                    }
                }
            }
            NodeData::TypeLiteralNode(_) => {
                let plans = self
                    .objects
                    .iter()
                    .filter(|plan| plan.node == node)
                    .collect::<Vec<_>>();
                let [plan] = plans.as_slice() else {
                    return Err(invalid());
                };
                let plan = (**plan).clone();
                let alias = source_alias_direct_owner(self.store, node)?;
                if plan.alias_symbol != alias {
                    return Err(invalid());
                }
                let mut object_children = Vec::new();
                let mut properties = Vec::new();
                for property in &plan.properties {
                    properties.push(self.read_child(property.type_node, true)?);
                    object_children.push(property.type_node);
                }
                let mut indexes = Vec::new();
                for index in &plan.indexes {
                    indexes.push((
                        self.read_child(index.key_type_node, true)?,
                        self.read_child(index.value_type_node, true)?,
                    ));
                    object_children.extend([index.key_type_node, index.value_type_node]);
                }
                let object = source_alias_closed_object(
                    self.store, self.host, &plan, type_, properties, indexes,
                )
                .map_err(|_| invalid())?;
                SourceAliasOperandProof::Object {
                    object: Box::new(object),
                    children: object_children,
                    alias,
                }
            }
            NodeData::FunctionTypeNode(_) => {
                let function = functions::plan_function_type(
                    self.store,
                    self.host,
                    node,
                    source_alias_direct_owner(self.store, node)?,
                    false,
                    self.array_targets,
                )
                .map_err(|_| invalid())?;
                if !function.alias_parameters.is_empty()
                    || !function.type_parameters.is_empty()
                    || !function.parameters.is_empty()
                    || function.type_predicate.is_some()
                {
                    return Err(RelationUnavailable::UnsupportedStructuredType(type_));
                }
                self.read_child(function.return_type, true)?;
                SourceAliasOperandProof::Function(Box::new(function))
            }
            NodeData::UnionTypeNode(union) => {
                let mut union_children = Vec::new();
                for &child in &union.types.nodes {
                    let child = NodeRef::new(node.arena, node.file, child);
                    self.read_child(child, closed)?;
                    row_closed &= self.graph.nodes[&child].closed;
                    union_children.push(child);
                }
                if union_children != children || union_children.len() < 2 {
                    return Err(invalid());
                }
                SourceAliasOperandProof::Union {
                    children: union_children,
                    alias: source_alias_direct_owner(self.store, node)?,
                }
            }
            NodeData::ArrayTypeNode(array) => {
                let element = NodeRef::new(node.arena, node.file, array.element_type);
                self.read_child(element, closed)?;
                row_closed = self.graph.nodes[&element].closed;
                SourceAliasOperandProof::Array {
                    element,
                    named_target: None,
                    readonly: false,
                }
            }
            NodeData::TemplateLiteralTypeNode(template) => {
                let head = NodeRef::new(node.arena, node.file, template.head);
                let NodeData::TemplateHead(head_data) =
                    &preflight_node(self.store, self.host, head)
                        .map_err(|_| invalid())?
                        .data
                else {
                    return Err(invalid());
                };
                if self.store.source_node_parent(head) != Some(SourceNodeParent::Parent(node))
                    || template.template_spans.nodes.is_empty()
                {
                    return Err(invalid());
                }
                let mut texts = vec![head_data.text.clone()];
                let mut placeholders = Vec::new();
                let mut spans = Vec::new();
                for (index, &span) in template.template_spans.nodes.iter().enumerate() {
                    let span = NodeRef::new(node.arena, node.file, span);
                    let NodeData::TemplateLiteralTypeSpan(data) =
                        &preflight_node(self.store, self.host, span)
                            .map_err(|_| invalid())?
                            .data
                    else {
                        return Err(invalid());
                    };
                    let placeholder = NodeRef::new(node.arena, node.file, data.type_);
                    let literal = NodeRef::new(node.arena, node.file, data.literal);
                    let text = match &preflight_node(self.store, self.host, literal)
                        .map_err(|_| invalid())?
                        .data
                    {
                        NodeData::TemplateMiddle(data)
                            if index + 1 < template.template_spans.nodes.len() =>
                        {
                            &data.text
                        }
                        NodeData::TemplateTail(data)
                            if index + 1 == template.template_spans.nodes.len() =>
                        {
                            &data.text
                        }
                        _ => return Err(invalid()),
                    };
                    texts.push(text.clone());
                    self.read_child(placeholder, true)?;
                    placeholders.push(placeholder);
                    spans.push((span, placeholder, literal));
                }
                SourceAliasOperandProof::Template {
                    texts,
                    placeholders,
                    spans,
                }
            }
            NodeData::IndexedAccessTypeNode(_) => {
                let plans = self
                    .indexed
                    .iter()
                    .filter(|plan| plan.node() == node)
                    .collect::<Vec<_>>();
                let [plan] = plans.as_slice() else {
                    return Err(invalid());
                };
                let plan = (**plan).clone();
                if plan.source() != &self.graph.source {
                    return Err(invalid());
                }
                self.read_child(plan.object(), true)?;
                self.read_child(plan.index(), true)?;
                SourceAliasOperandProof::Indexed(Box::new(plan))
            }
            _ => return Err(RelationUnavailable::UnsupportedStructuredType(type_)),
        };
        self.graph.nodes.insert(
            node,
            SourceAliasOperandNode {
                type_,
                kind: record.kind,
                parent,
                children,
                closed: row_closed,
                proof,
            },
        );
        self.active.remove(&node);
        self.graph
            .validate_node(self.store, node, self.array_targets, &mut HashSet::new())
    }
}

fn source_alias_node_result_matches(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> bool {
    if store.source_node_kind(node) == Some(SyntaxKind::ParenthesizedType) {
        source_alias_cached_child(store, node) == Some(type_)
    } else {
        store.source_direct_type_annotation_is_exact(node, type_)
    }
}

fn source_alias_cached_child(store: &CanonicalTypeMapperStore, node: NodeRef) -> Option<TypeId> {
    let mut child = node;
    let mut wrappers = Vec::new();
    while store.source_node_kind(child) == Some(SyntaxKind::ParenthesizedType) {
        if wrappers.contains(&child) {
            return None;
        }
        let children = store.source_direct_children(child)?;
        let [inner] = children.as_slice() else {
            return None;
        };
        if store.source_node_parent(*inner) != Some(SourceNodeParent::Parent(child)) {
            return None;
        }
        wrappers.push(child);
        child = *inner;
    }
    let type_ = if store.source_node_kind(child) == Some(SyntaxKind::LiteralType)
        && store
            .source_child_with_kind(child, SyntaxKind::NullKeyword)
            .is_some()
    {
        store.intrinsic_bootstrap()?.null_type
    } else {
        cached_planned_type_identity(store, child)?
    };
    let exact = TypeNodeLinks {
        resolved_type: Some(type_),
        outer_type_parameters: None,
    };
    wrappers
        .iter()
        .all(|&wrapper| {
            store
                .type_node_links(wrapper)
                .is_none_or(|links| links == &TypeNodeLinks::default() || links == &exact)
                && store
                    .symbol_node_links(wrapper)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
        })
        .then_some(type_)
}

fn source_alias_literal_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<LiteralValue>, ()> {
    let record = preflight_node(store, host, node).map_err(|_| ())?;
    let value = match &record.data {
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::NullKeyword => {
            return Ok(None);
        }
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::TrueKeyword => {
            LiteralValue::Boolean(true)
        }
        NodeData::KeywordExpression(_) if record.kind == SyntaxKind::FalseKeyword => {
            LiteralValue::Boolean(false)
        }
        NodeData::StringLiteral(data) if data.token_flags.0 == 0 => {
            LiteralValue::String(data.text.clone())
        }
        NodeData::NoSubstitutionTemplateLiteral(data)
            if data.token_flags.0 == 0 && data.template_flags.0 == 0 =>
        {
            LiteralValue::String(data.text.clone())
        }
        NodeData::NumericLiteral(data) if data.token_flags.0 == 0 => {
            let value = ts_jsnum::from_string(&normalize_numeric_separators(&data.text).ok_or(())?);
            if value.is_nan() {
                return Err(());
            }
            LiteralValue::Number(value)
        }
        NodeData::BigIntLiteral(data) if data.token_flags.0 == 0 => LiteralValue::BigInt(
            ts_jsnum::PseudoBigInt::parse_valid(&normalize_bigint_literal(&data.text).ok_or(())?),
        ),
        NodeData::PrefixUnaryExpression(prefix) if prefix.operator == SyntaxKind::MinusToken => {
            let operand = NodeRef::new(node.arena, node.file, prefix.operand);
            if store.source_node_parent(operand) != Some(SourceNodeParent::Parent(node)) {
                return Err(());
            }
            match source_alias_literal_value(store, host, operand)? {
                Some(LiteralValue::Number(value)) => LiteralValue::Number(-value),
                Some(LiteralValue::BigInt(value)) => {
                    LiteralValue::BigInt(ts_jsnum::PseudoBigInt::new(&value.base10_value, true))
                }
                _ => return Err(()),
            }
        }
        _ => return Err(()),
    };
    Ok(Some(value))
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

pub(super) fn source_property_object_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<SourcePropertyObjectProjection>, RelationUnavailable> {
    if let Some(source) = property_object_alias_projection(store, type_)? {
        return Ok(Some(SourcePropertyObjectProjection::DirectAlias(source)));
    }
    Ok(
        inline_property_object_projection(store, type_)?
            .map(SourcePropertyObjectProjection::Inline),
    )
}

/// Reads the literal and its lexical parameter scope before semantic allocation.
pub(super) fn inline_property_object_source_header(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<Option<InlinePropertyObjectSourceHeader>, RelationUnavailable> {
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeLiteral) {
        return Ok(None);
    }
    let Some(syntax) = inline_source_syntax(store, declaration) else {
        if source_syntax(store, declaration).is_none()
            && let Some(links) = store.type_node_links(declaration)
            && links.outer_type_parameters.is_some()
            && let Some(type_) = links.resolved_type
        {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_));
        }
        return Ok(None);
    };
    let Some((source_symbol, parameter_owner)) = source_symbols(store, &syntax)? else {
        return Ok(None);
    };
    if alias_has_enclosing_type_parameters(store, syntax.alias_declaration, parameter_owner)? {
        return Ok(None);
    }
    let owner = property_object_alias_identity_source_header(store, parameter_owner)?;
    let invalid = || RelationUnavailable::Symbol(source_symbol);
    if owner.alias_declaration != syntax.alias_declaration
        || owner.parameters.is_empty()
        || !owner
            .parameters
            .iter()
            .map(|(declaration, _)| *declaration)
            .eq(syntax.parameters.iter().copied())
    {
        return Err(invalid());
    }
    let header = InlinePropertyObjectSourceHeader {
        declaration,
        source_symbol,
        alias_declaration: syntax.alias_declaration,
        parameter_owner,
        parameters: owner.parameters,
        properties: source_properties(store, &syntax, source_symbol)?,
    };
    if let Some(target) = store
        .type_node_links(declaration)
        .and_then(|links| links.resolved_type)
    {
        let parameters = inline_source_parameters(store, &header)?;
        validate_inline_template_fields(store, &syntax, &header, target, &parameters)?;
    } else {
        for node in std::iter::once(declaration).chain(syntax.wrappers.iter().copied()) {
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
    }
    Ok(Some(header))
}

fn inline_source_parameters(
    store: &CanonicalTypeMapperStore,
    source: &InlinePropertyObjectSourceHeader,
) -> Result<Vec<TypeId>, RelationUnavailable> {
    source
        .parameters
        .iter()
        .map(|&(declaration, symbol)| {
            let parameter = source_parameter(store, declaration, source.parameter_owner)?;
            if cached_ordinary_type_parameter_owner(store, parameter) != Some(symbol) {
                return Err(RelationUnavailable::Symbol(symbol));
            }
            Ok(parameter)
        })
        .collect()
}

/// This check does not enter instance caches, recovery records, or member values.
pub(super) fn inline_property_object_template_matches(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    target: TypeId,
    parameter_owner: SemanticSymbolId,
    parameters: &[TypeId],
) -> Result<bool, RelationUnavailable> {
    let Some(syntax) = inline_source_syntax(store, declaration) else {
        return Ok(false);
    };
    let Some((source_symbol, owner)) = source_symbols(store, &syntax)? else {
        return Ok(false);
    };
    if owner != parameter_owner
        || alias_has_enclosing_type_parameters(store, syntax.alias_declaration, owner)?
    {
        return Ok(false);
    }
    let scope = property_object_alias_identity_source_header(store, owner)?;
    let header = InlinePropertyObjectSourceHeader {
        declaration,
        source_symbol,
        alias_declaration: syntax.alias_declaration,
        parameter_owner: owner,
        parameters: scope.parameters,
        properties: source_properties(store, &syntax, source_symbol)?,
    };
    if inline_source_parameters(store, &header)? != parameters {
        return Ok(false);
    }
    validate_inline_template_fields(store, &syntax, &header, target, parameters)?;
    Ok(true)
}

fn validate_inline_template_fields(
    store: &CanonicalTypeMapperStore,
    syntax: &SourceSyntax,
    source: &InlinePropertyObjectSourceHeader,
    target: TypeId,
    parameters: &[TypeId],
) -> Result<(), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(target);
    let record = store.type_payload(target).ok_or_else(invalid)?;
    let object = target_object(store, target)?;
    if parameters.is_empty()
        || record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(source.source_symbol)
        || record.alias().is_some()
        || !valid_original_object_flags(record.object_flags())
        || object.target.is_some()
        || object.mapper.is_some()
        || store.property_object_alias_recovery(target).is_some()
        || store.inline_property_object_recovery(target).is_some()
        || store.type_node_links(source.declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(target),
                outer_type_parameters: Some(parameters.to_vec()),
            })
        || store
            .type_alias_links(source.parameter_owner)
            .is_some_and(|links| {
                links.is_constructor_declared_property
                    || links.declared_type == Some(target)
                    || links
                        .type_parameters
                        .as_deref()
                        .is_some_and(|actual| actual != parameters)
            })
    {
        return Err(invalid());
    }
    for node in std::iter::once(source.declaration).chain(syntax.wrappers.iter().copied()) {
        if store
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
            || node != source.declaration
                && store.type_node_links(node).is_some_and(|links| {
                    links.outer_type_parameters.is_some()
                        || links.resolved_type.is_some_and(|cached| cached != target)
                })
        {
            return Err(invalid());
        }
    }
    if let TypeCacheState::Allocated(entries) = &object.instantiations
        && entries.get(&type_alias_instantiation_cache_key(parameters, None)) != Some(&target)
    {
        return Err(invalid());
    }
    Ok(())
}

/// Reads only original source fields and an instance's physical mapper edges.
fn inline_instance_fields(
    store: &CanonicalTypeMapperStore,
    source: &InlinePropertyObjectSourceHeader,
    target: TypeId,
    parameters: &[TypeId],
    type_: TypeId,
) -> Result<(Vec<TypeId>, TypeMapperId), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let object = target_object(store, type_)?;
    let mapper = object.mapper.ok_or_else(invalid)?;
    if !matches!(
        store.mapper_kind(mapper),
        Some(TypeMapperKind::Simple | TypeMapperKind::Array)
    ) {
        return Err(invalid());
    }
    let arguments = parameters
        .iter()
        .map(|&parameter| store.map_type(mapper, parameter).ok_or_else(invalid))
        .collect::<Result<Vec<_>, _>>()?;
    if type_ == target
        || record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(source.source_symbol)
        || record.alias().is_some()
        || object.target != Some(target)
        || object.instantiations != TypeCacheState::Unallocated
        || arguments == parameters
        || !valid_instance_object_flag_header(store, record.object_flags(), &arguments)?
        || store.type_mapper_has_exact_endpoints(mapper, parameters, &arguments) != Some(true)
        || store.property_object_alias_recovery(type_).is_some()
    {
        return Err(invalid());
    }
    validate_property_object_alias_arguments(store, &arguments).map_err(|_| invalid())?;
    Ok((arguments, mapper))
}

fn inline_source_for_record(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<InlinePropertyObjectSourceHeader>, RelationUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let target = match record.data() {
        TypeData::Object(object) => object.target,
        _ => None,
    };
    for candidate in std::iter::once(type_).chain(target) {
        let Some(symbol) = store.type_payload(candidate).and_then(TypeRecord::symbol) else {
            continue;
        };
        let Some(declarations) = store
            .symbol(symbol)
            .and_then(|symbol| symbol.declarations())
        else {
            continue;
        };
        for &declaration in declarations {
            if let Some(source) = inline_property_object_source_header(store, declaration)? {
                return Ok(Some(source));
            }
        }
    }
    if store.inline_property_object_recovery(type_).is_some() {
        return Err(RelationUnavailable::InvalidStructuredMembers(type_));
    }
    Ok(None)
}

pub(super) fn inline_property_object_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<InlinePropertyObjectProjection>, RelationUnavailable> {
    let Some(source) = inline_source_for_record(store, type_)? else {
        return Ok(None);
    };
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let target = store
        .type_node_links(source.declaration)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    let parameters = inline_source_parameters(store, &source)?;
    let (arguments, mapper) = if type_ == target {
        (parameters.clone(), None)
    } else {
        let (arguments, mapper) =
            inline_instance_fields(store, &source, target, &parameters, type_)?;
        if !valid_instance_variable_flags(
            store,
            store
                .type_payload(type_)
                .ok_or_else(invalid)?
                .object_flags(),
            &arguments,
        )? || cached_instantiation(
            &target_object(store, target)?.instantiations,
            type_alias_instantiation_cache_key(&arguments, None),
        ) != Some(type_)
        {
            return Err(invalid());
        }
        (arguments, Some(mapper))
    };
    if let TypeCacheState::Allocated(entries) = &target_object(store, target)?.instantiations {
        for (&key, &cached) in entries {
            if cached == target {
                if key != type_alias_instantiation_cache_key(&parameters, None) {
                    return Err(invalid());
                }
                continue;
            }
            let (arguments, _) =
                inline_instance_fields(store, &source, target, &parameters, cached)?;
            if key != type_alias_instantiation_cache_key(&arguments, None)
                || !valid_instance_variable_flags(
                    store,
                    store
                        .type_payload(cached)
                        .ok_or_else(invalid)?
                        .object_flags(),
                    &arguments,
                )?
                || store
                    .inline_property_object_recovery(cached)
                    .is_some_and(|recovery| {
                        recovery.result() != cached || !recovery.matches_current_result(store)
                    })
            {
                return Err(invalid());
            }
        }
    }
    if store
        .inline_property_object_recovery(type_)
        .is_some_and(|recovery| {
            recovery.result() != type_ || !recovery.matches_current_result(store)
        })
    {
        return Err(invalid());
    }
    Ok(Some(InlinePropertyObjectProjection {
        type_,
        target,
        declaration: source.declaration,
        source_symbol: source.source_symbol,
        parameter_owner: source.parameter_owner,
        parameters,
        arguments,
        mapper,
        properties: source.properties,
    }))
}

fn cached_inline_property_object_physical_arguments(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<Vec<TypeId>>, RelationUnavailable> {
    let Some(source) = inline_source_for_record(store, type_)? else {
        return Ok(None);
    };
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let target = store
        .type_node_links(source.declaration)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    let parameters = inline_source_parameters(store, &source)?;
    if type_ == target {
        return Ok(Some(parameters));
    }
    let (arguments, _) = inline_instance_fields(store, &source, target, &parameters, type_)?;
    if cached_instantiation(
        &target_object(store, target)?.instantiations,
        type_alias_instantiation_cache_key(&arguments, None),
    ) != Some(type_)
    {
        return Err(invalid());
    }
    Ok(Some(arguments))
}

/// Parent proof for literals in an intersection, never for a direct alias RHS.
fn inline_source_syntax<M>(
    store: &SemanticStore<TypeRecord, M>,
    rhs: NodeRef,
) -> Option<SourceSyntax> {
    if store.source_node_kind(rhs) != Some(SyntaxKind::TypeLiteral) {
        return None;
    }
    let mut root = rhs;
    let mut wrappers = Vec::new();
    let mut seen = HashSet::from([rhs]);
    let mut intersection = false;
    let alias_declaration = loop {
        let SourceNodeParent::Parent(parent) = store.source_node_parent(root)? else {
            return None;
        };
        if parent.arena != rhs.arena || parent.file != rhs.file || !seen.insert(parent) {
            return None;
        }
        let children = store.source_direct_children(parent)?;
        if children.iter().filter(|&&child| child == root).count() != 1
            || children.iter().any(|child| {
                child.arena != rhs.arena
                    || child.file != rhs.file
                    || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(parent))
            })
        {
            return None;
        }
        match store.source_node_kind(parent)? {
            SyntaxKind::ParenthesizedType if children.as_slice() == [root] => {
                if !intersection {
                    wrappers.push(parent);
                }
                root = parent;
            }
            kind @ (SyntaxKind::IntersectionType | SyntaxKind::UnionType)
                if children.len() >= 2
                    && (intersection || kind == SyntaxKind::IntersectionType) =>
            {
                let mut previous = None;
                for child in children {
                    let start = store.source_node_start(child)?;
                    if previous.is_some_and(|previous| previous >= start) {
                        return None;
                    }
                    previous = Some(start);
                }
                intersection = true;
                root = parent;
            }
            SyntaxKind::TypeAliasDeclaration if intersection => break parent,
            _ => return None,
        }
    };
    if store.source_direct_type_annotation(alias_declaration) != Some(root) {
        return None;
    }
    let mut parameters = store
        .source_direct_children(alias_declaration)?
        .into_iter()
        .filter(|child| store.source_node_kind(*child) == Some(SyntaxKind::TypeParameter))
        .collect::<Vec<_>>();
    if parameters.is_empty() {
        return None;
    }
    parameters.sort_by_key(|parameter| store.source_node_start(*parameter));
    let mut properties = store.source_direct_children(rhs)?;
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
        return None;
    }
    properties.sort_by_key(|property| store.source_node_start(*property));
    Some(SourceSyntax {
        declaration: rhs,
        alias_declaration,
        wrappers,
        parameters,
        properties,
    })
}

/// Proves a closed alias body from source without evaluating its annotations.
pub(super) fn closed_type_alias_source_header(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<Option<ClosedTypeAliasSourceHeader>, RelationUnavailable> {
    if !matches!(
        store.source_node_kind(declaration),
        Some(SyntaxKind::TypeLiteral | SyntaxKind::FunctionType)
    ) {
        return Ok(None);
    }
    let mut root = declaration;
    let mut wrappers = Vec::new();
    let mut seen = HashSet::from([root]);
    let alias_declaration = loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(root) else {
            return Ok(None);
        };
        if parent.arena != declaration.arena
            || parent.file != declaration.file
            || !seen.insert(parent)
        {
            return Ok(None);
        }
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType)
                if store.source_direct_children(parent).as_deref() == Some(&[root]) =>
            {
                wrappers.push(parent);
                root = parent;
            }
            Some(SyntaxKind::TypeAliasDeclaration) => break parent,
            _ => return Ok(None),
        }
    };
    if store.source_direct_type_annotation(alias_declaration) != Some(root)
        || store
            .source_direct_children(declaration)
            .is_none_or(|children| {
                children
                    .iter()
                    .any(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypeParameter))
            })
    {
        return Ok(None);
    }
    let Some(alias_symbol) = bound_declaration_symbol(store, alias_declaration) else {
        return Ok(None);
    };
    if alias_has_enclosing_type_parameters(store, alias_declaration, alias_symbol)? {
        return Ok(None);
    }
    let owner = property_object_alias_identity_source_header(store, alias_symbol)?;
    if !owner.parameters.is_empty() {
        return Ok(None);
    }
    let source_symbol = if store.source_node_kind(declaration) == Some(SyntaxKind::FunctionType) {
        closed_function_type_source_symbol(store, declaration, alias_symbol)?
    } else {
        let syntax = SourceSyntax {
            declaration,
            alias_declaration,
            wrappers,
            parameters: Vec::new(),
            properties: Vec::new(),
        };
        let Some((source_symbol, actual_alias)) = source_symbols(store, &syntax)? else {
            return Ok(None);
        };
        if actual_alias != alias_symbol {
            return Err(RelationUnavailable::Symbol(alias_symbol));
        }
        source_symbol
    };
    Ok(Some(ClosedTypeAliasSourceHeader {
        declaration,
        source_symbol,
        alias_declaration,
        alias_symbol,
    }))
}

fn closed_function_type_source_symbol(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<SemanticSymbolId, RelationUnavailable> {
    let symbol =
        bound_declaration_symbol(store, declaration).ok_or(RelationUnavailable::Symbol(alias))?;
    let invalid = || RelationUnavailable::Symbol(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let members = record
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    let call = members
        .get(InternalSymbolName::Call.as_ref())
        .ok_or_else(invalid)?;
    let call_record = store.symbol(call).ok_or_else(invalid)?;
    if store.get_merged_symbol(symbol) != Some(symbol)
        || !store.source_declaration_belongs_to_symbol(declaration, symbol)
        || !store.source_symbol_declarations_match(symbol)
        || record.flags() != SymbolFlags::TYPE_LITERAL
        || record.check_flags() != CheckFlags::NONE
        || record.name() != InternalSymbolName::Type.as_ref()
        || record.declarations() != Some(&[declaration])
        || record.value_declaration().is_some()
        || record.parent().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || members.len() != 1
        || store.get_merged_symbol(call) != Some(call)
        || !store.source_declaration_belongs_to_symbol(declaration, call)
        || !store.source_symbol_declarations_match(call)
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record.declarations() != Some(&[declaration])
        || call_record.value_declaration().is_some()
        || call_record.parent().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.export_symbol().is_some()
    {
        return Err(invalid());
    }
    Ok(symbol)
}

/// Reads only source and identity fields, without entering member or signature proofs.
fn closed_declared_object_source_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<ClosedTypeAliasSourceHeader>, RelationUnavailable> {
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let TypeData::Object(object) = record.data() else {
        return Ok(None);
    };
    let Some(symbol) = record.symbol() else {
        return Ok(None);
    };
    let Some([declaration]) = store
        .symbol(symbol)
        .and_then(|symbol| symbol.declarations())
    else {
        return Ok(None);
    };
    let Some(header) = closed_type_alias_source_header(store, *declaration)? else {
        return Ok(None);
    };
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let alias = record
        .alias()
        .and_then(|alias| store.type_alias(alias))
        .ok_or_else(invalid)?;
    let mutable =
        ObjectFlags::MEMBERS_RESOLVED | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    if record.flags() != TypeFlags::OBJECT
        || symbol != header.source_symbol
        || record.object_flags() & !mutable != ObjectFlags::ANONYMOUS
        || alias.symbol() != Some(header.alias_symbol)
        || alias.type_arguments().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || store.property_object_alias_recovery(type_).is_some()
        || store.inline_property_object_recovery(type_).is_some()
        || store.type_node_links(*declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
        || store
            .type_alias_links(header.alias_symbol)
            .is_some_and(|links| {
                links.declared_type.is_some_and(|cached| cached != type_)
                    || links.type_parameters.is_some()
                    || links.instantiations.is_some()
                    || links.is_constructor_declared_property
            })
    {
        return Err(invalid());
    }
    let root = store
        .source_direct_type_annotation(header.alias_declaration)
        .ok_or_else(invalid)?;
    let (inner, wrappers) = source_parentheses(store, root, header.alias_symbol)?;
    if inner != *declaration {
        return Err(invalid());
    }
    for wrapper in wrappers {
        if store.type_node_links(wrapper).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) || store
            .symbol_node_links(wrapper)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return Err(invalid());
        }
    }
    Ok(Some(header))
}

/// Mapping a closed declared object preserves its identity and leaves values lazy.
#[allow(clippy::too_many_lines)] // The source record and all present cache edges form one proof.
pub(super) fn closed_declared_property_object_is_mapping_invariant(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, RelationUnavailable> {
    let Some(header) = closed_declared_object_source_identity(store, type_)? else {
        return Ok(false);
    };
    if store.source_node_kind(header.declaration) != Some(SyntaxKind::TypeLiteral) {
        return Ok(false);
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let object = target_object(store, type_)?;
    let syntax = SourceSyntax {
        declaration: header.declaration,
        alias_declaration: header.alias_declaration,
        wrappers: Vec::new(),
        parameters: Vec::new(),
        properties: store
            .source_direct_children(header.declaration)
            .ok_or_else(invalid)?,
    };
    let properties = source_properties(store, &syntax, header.source_symbol)?;
    let ready = record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED);
    let expected = if ready {
        super::type_records::StructuredTypeData {
            members: store
                .symbol(header.source_symbol)
                .ok_or_else(invalid)?
                .members(),
            properties: (!properties.is_empty())
                .then(|| properties.iter().map(|property| property.symbol).collect()),
            ..super::type_records::StructuredTypeData::default()
        }
    } else {
        super::type_records::StructuredTypeData::default()
    };
    if object.structured != expected {
        return Err(invalid());
    }
    for property in properties {
        if ready
            && store
                .value_symbol_links(property.symbol)
                .is_none_or(|links| links.resolved_type.is_none())
        {
            return Err(invalid());
        }
        if let Some(links) = store.value_symbol_links(property.symbol)
            && (links
                != &ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    ..ValueSymbolLinks::default()
                }
                || links.resolved_type.is_some_and(|value| {
                    store.type_payload(value).is_none()
                        || store.symbol(property.symbol).is_none_or(|symbol| {
                            symbol.check_flags()
                                != if property.readonly {
                                    CheckFlags::READONLY
                                } else {
                                    CheckFlags::NONE
                                }
                        })
                        || !closed_property_annotation_value_matches(
                            store,
                            property.type_node,
                            value,
                            &mut HashSet::new(),
                        )
                }))
        {
            return Err(invalid());
        }
        if store
            .type_node_links(property.type_node)
            .is_some_and(|links| {
                links.resolved_type.is_some_and(|value| {
                    store.type_payload(value).is_none()
                        || !closed_property_annotation_value_matches(
                            store,
                            property.type_node,
                            value,
                            &mut HashSet::new(),
                        )
                })
            })
        {
            return Err(invalid());
        }
        if store
            .type_node_links(property.type_node)
            .is_none_or(|links| links.resolved_type.is_none())
            && (store
                .type_node_links(property.type_node)
                .is_some_and(|links| links != &TypeNodeLinks::default())
                || store
                    .symbol_node_links(property.type_node)
                    .is_some_and(|links| links != &SymbolNodeLinks::default()))
        {
            return Err(invalid());
        }
    }
    Ok(true)
}

/// Checks stored annotation results. Name resolution and import authority stay with the query.
fn closed_property_annotation_value_matches(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    value: TypeId,
    active: &mut HashSet<NodeRef>,
) -> bool {
    if !active.insert(node) {
        return false;
    }
    let valid = closed_property_annotation_value_matches_worker(store, node, value, active);
    active.remove(&node);
    valid
}

#[allow(clippy::too_many_lines)] // Keep the source form, original provider, and alias row together.
fn closed_property_annotation_value_matches_worker(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    value: TypeId,
    active: &mut HashSet<NodeRef>,
) -> bool {
    if store.source_type_node_result_is_exact(node, value, &[]) {
        return true;
    }
    if !store.source_direct_type_annotation_is_exact(node, value) {
        return false;
    }
    let Some(children) = store.source_direct_children(node) else {
        return false;
    };
    if children.iter().any(|child| {
        child.arena != node.arena
            || child.file != node.file
            || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(node))
    }) {
        return false;
    }
    match store.source_node_kind(node) {
        Some(SyntaxKind::ParenthesizedType) => {
            matches!(children.as_slice(), [child]
                if store.symbol_node_links(node).is_none_or(|links| links == &SymbolNodeLinks::default())
                    && closed_property_annotation_value_matches(store, *child, value, active))
        }
        Some(SyntaxKind::FunctionType) => {
            matches!(
                super::functions::validate_stored_function_type(store, value),
                super::functions::StoredFunctionTypeValidation::Valid(_)
            ) && store
                .type_payload(value)
                .and_then(TypeRecord::symbol)
                .is_some_and(|symbol| {
                    store
                        .symbol(symbol)
                        .is_some_and(|record| record.declarations() == Some(&[node]))
                        && store.source_declaration_belongs_to_symbol(node, symbol)
                })
        }
        Some(SyntaxKind::TypeLiteral) => {
            matches!(closed_declared_object_source_identity(store, value), Ok(Some(source))
                if source.declaration == node)
        }
        Some(SyntaxKind::TypeReference) => {
            let Some(owner) = store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol)
            else {
                return false;
            };
            let Ok(source) = property_object_alias_identity_source_header(store, owner) else {
                return false;
            };
            let [name, argument_nodes @ ..] = children.as_slice() else {
                return false;
            };
            if !super::object_members::source_resolved_constructor_name_cache_is_exact(
                store, *name, owner,
            ) {
                return false;
            }
            let Some(arguments) = argument_nodes
                .iter()
                .map(|&argument| {
                    let value =
                        super::object_members::cached_planned_type_identity(store, argument)?;
                    closed_property_annotation_value_matches(store, argument, value, active)
                        .then_some(value)
                })
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            if !super::object_members::cached_alias_reference_annotation_matches(
                store, owner, &arguments, value,
            ) {
                return false;
            }
            if let Ok(Some(projection)) = property_object_alias_projection(store, value) {
                return projection.identity_symbol == owner
                    && projection.identity_arguments.starts_with(&arguments);
            }
            if !source.parameters.is_empty() || !arguments.is_empty() {
                return false;
            }
            store
                .source_direct_type_annotation(source.alias_declaration)
                .is_some_and(|body| {
                    closed_property_annotation_value_matches(store, body, value, active)
                })
        }
        _ => false,
    }
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
        return cached_inline_property_object_physical_arguments(store, type_);
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

/// Checks the primary source binding and its complete local/export relation.
pub(super) fn validate_source_alias_binding<M>(
    store: &SemanticStore<TypeRecord, M>,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<(), RelationUnavailable> {
    if bound_declaration_symbol(store, declaration) != Some(alias)
        || !store.source_declaration_belongs_to_symbol(declaration, alias)
    {
        return Err(RelationUnavailable::Symbol(alias));
    }
    validate_alias_binding(store, declaration, alias)
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
        || alias.imported_body().is_some()
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
        || identity_symbol == source.alias_symbol && alias.imported_body().is_some()
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
    let identity = store
        .type_payload(type_)
        .and_then(TypeRecord::alias)
        .ok_or_else(invalid)?;
    if let Some(proof) = store
        .type_alias(identity)
        .and_then(|alias| alias.imported_body())
    {
        proof
            .validate_wrapper_identity(store, identity)
            .map_err(|_| invalid())?;
    }
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

fn identity_source_default_argument(
    store: &CanonicalTypeMapperStore,
    header: &PropertyObjectAliasSourceHeader,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(TypeId, IdentitySourceArgument), RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(symbol);
    if !header.parameters.contains(&(declaration, symbol))
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(header.alias_declaration))
    {
        return Err(invalid());
    }
    let annotations = store
        .source_alias_type_parameter_annotations(declaration)
        .ok_or_else(invalid)?;
    let default_node = annotations.default_type.ok_or_else(invalid)?;
    let (default_type, argument) = original_identity_source_argument(store, header, default_node)?;
    if !matches!(argument, IdentitySourceArgument::Fixed(_)) {
        return Err(RelationUnavailable::UnsupportedStructuredType(default_type));
    }
    let parameter = source_parameter(store, declaration, header.alias_symbol)?;
    let Some(TypeData::TypeParameter(data)) = store.type_payload(parameter).map(TypeRecord::data)
    else {
        return Err(invalid());
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let constraint = annotations
        .constraint
        .map(|node| {
            original_identity_source_argument(store, header, node).map(|(type_, _)| {
                if type_ == bootstrap.any_type {
                    bootstrap.unknown_type
                } else {
                    type_
                }
            })
        })
        .transpose()?;
    if data.is_this_type
        || data.target.is_some()
        || data.mapper.is_some()
        || data
            .resolved_default_type
            .is_some_and(|cached| cached != default_type)
        || match constraint {
            Some(expected) => data.constraint != Some(expected),
            None => data
                .constraint
                .is_some_and(|cached| cached != bootstrap.no_constraint_type),
        }
    {
        return Err(invalid());
    }
    Ok((default_type, argument))
}

/// Checks filled slots against closed defaults on the referenced alias's own parameters.
/// This read-only proof does not check the provider declaration's diagnostics.
pub(super) fn validate_property_object_alias_source_defaults(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    supplied_count: usize,
    effective_arguments: &[TypeId],
) -> Result<(), RelationUnavailable> {
    let header = property_object_alias_identity_source_header(store, symbol)?;
    if supplied_count > header.parameters.len()
        || effective_arguments.len() != header.parameters.len()
    {
        return Err(RelationUnavailable::Symbol(symbol));
    }
    for (index, &(declaration, parameter)) in
        header.parameters.iter().enumerate().skip(supplied_count)
    {
        let (expected, _) =
            identity_source_default_argument(store, &header, declaration, parameter)?;
        if effective_arguments[index] != expected {
            return Err(RelationUnavailable::Symbol(parameter));
        }
    }
    Ok(())
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
        let identity = store
            .type_payload(declared_type)
            .and_then(TypeRecord::alias)
            .ok_or_else(invalid)?;
        let imported = super::source_imports::validate_stored_alias_body_wrapper_import(
            store,
            identity,
            symbol,
            header.alias_declaration,
            reference.node,
            referenced,
        )
        .map_err(|_| invalid())?;
        if store.type_node_links(reference.node)
            != Some(&TypeNodeLinks {
                resolved_type: Some(declared_type),
                outer_type_parameters: None,
            })
            || !imported
                && store.source_identifier_text(reference.name)
                    != store
                        .symbol(referenced)
                        .and_then(|record| record.name().as_utf8())
            || header.parameters.iter().any(|(_, parameter)| {
                store
                    .symbol(*parameter)
                    .and_then(|record| record.name().as_utf8())
                    == store.source_identifier_text(reference.name)
            })
            || reference.arguments.len() > referenced_header.parameters.len()
            || store
                .type_node_links(reference.name)
                .is_some_and(|links| links != &TypeNodeLinks::default())
            || store
                .symbol_node_links(reference.name)
                .is_some_and(|links| {
                    links
                        .resolved_symbol
                        .is_some_and(|cached| cached != referenced && !imported)
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
        let mut arguments = Vec::with_capacity(referenced_header.parameters.len());
        let mut original_arguments = Vec::with_capacity(reference.arguments.len());
        for argument in &reference.arguments {
            let (type_, source_argument) =
                original_identity_source_argument(store, &header, *argument)?;
            original_arguments.push(type_);
            arguments.push(source_argument);
        }
        // Defaults fill physical slots. The request key keeps only written arguments.
        for &(declaration, parameter) in referenced_header
            .parameters
            .iter()
            .skip(reference.arguments.len())
        {
            let (_, argument) = identity_source_default_argument(
                store,
                &referenced_header,
                declaration,
                parameter,
            )?;
            arguments.push(argument);
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

/// Checks inline instance flags without entering its projection or recovery proof.
pub(super) fn source_property_object_instance_flags_match(
    store: &CanonicalTypeMapperStore,
    flags: ObjectFlags,
    physical_arguments: &[TypeId],
) -> Result<bool, RelationUnavailable> {
    Ok(
        valid_instance_object_flag_header(store, flags, physical_arguments)?
            && valid_instance_variable_flags(store, flags, physical_arguments)?,
    )
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
        TypeData::Object(_) => {
            if let Some(arguments) = cached_inline_property_object_physical_arguments(store, type_)?
            {
                children.extend(arguments);
                None
            } else if closed_declared_object_source_identity(store, type_)?.is_some() {
                Some(true)
            } else {
                Some(false)
            }
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
pub(super) mod source_alias_bound_test_support {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
        CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
        CanonicalResolvedModuleInput, IntrinsicBootstrapOptions, links::AliasTargetState,
        object_members::plan_type_literal, source_imports::plan_source_property_type_import,
        type_nodes::plan_source_alias_operand_source,
    };
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    pub(in crate::semantic) const SOURCE: FileId = FileId::new(48_930);
    const STATUS: FileId = FileId::new(48_931);
    const OTHER_STATUS: FileId = FileId::new(48_932);
    const ES5: FileId = FileId::new(48_933);
    const DECORATORS: FileId = FileId::new(48_934);
    const LEGACY: FileId = FileId::new(48_935);

    // The closed declarations retain the original Hono source. Only the final
    // alias uses select the bound and default operations under test.
    const SOURCE_TEXT: &str = r#"import type { StatusCode } from './utils/http-status'

export type Bindings = object
export type Variables = object

export type BlankEnv = {}
export type Env = {
  Bindings?: Bindings
  Variables?: Variables
}

export type Input = {
  in?: {}
  out?: {}
  outputFormat?: ResponseFormat
}

export type Schema = {
  [Path: string]: {
    [Method: `$${Lowercase<string>}`]: Endpoint
  }
}

export type Endpoint = {
  input: any
  output: any
  outputFormat: ResponseFormat
  status: StatusCode
}

export type KnownResponseFormat = 'json' | 'text' | 'redirect'
export type ResponseFormat = KnownResponseFormat | string

type EnvBound<T extends Env = Env> = unknown;
type SchemaBound<T extends Schema = Schema> = unknown;
type InputBound<T extends Input | Input['in'] = Input> = unknown;
type OutputBound<T extends Input['out']> = unknown;
type Dependent<T extends Env, U extends T = T> = U;
type ArrayDefault<T extends Env, U = T[]> = U;
type WrappedEnv = (Env);
type WrappedProperty = { value: (WrappedEnv) };
type WrappedBound<T extends ((WrappedProperty))> = unknown;
"#;

    const STATUS_TEXT: &str = r#"/**
 * @module
 * HTTP Status utility.
 */

export type InfoStatusCode = 100 | 101 | 102 | 103
export type SuccessStatusCode = 200 | 201 | 202 | 203 | 204 | 205 | 206 | 207 | 208 | 226
export type DeprecatedStatusCode = 305 | 306
export type RedirectStatusCode = 300 | 301 | 302 | 303 | 304 | DeprecatedStatusCode | 307 | 308
export type ClientErrorStatusCode =
  | 400
  | 401
  | 402
  | 403
  | 404
  | 405
  | 406
  | 407
  | 408
  | 409
  | 410
  | 411
  | 412
  | 413
  | 414
  | 415
  | 416
  | 417
  | 418
  | 421
  | 422
  | 423
  | 424
  | 425
  | 426
  | 428
  | 429
  | 431
  | 451
export type ServerErrorStatusCode = 500 | 501 | 502 | 503 | 504 | 505 | 506 | 507 | 508 | 510 | 511

/**
 * `UnofficialStatusCode` can be used to specify an unofficial status code.
 * @example
 *
 * ```ts
 * app.get('/unknown', (c) => {
 *   return c.text("Unknown Error", 520 as UnofficialStatusCode)
 * })
 * ```
 */
export type UnofficialStatusCode = -1

/**
 * @deprecated
 * Use `UnofficialStatusCode` instead.
 */
export type UnOfficalStatusCode = UnofficialStatusCode

/**
 * If you want to use an unofficial status, use `UnofficialStatusCode`.
 */
export type StatusCode =
  | InfoStatusCode
  | SuccessStatusCode
  | RedirectStatusCode
  | ClientErrorStatusCode
  | ServerErrorStatusCode
  | UnofficialStatusCode

export type ContentlessStatusCode = 101 | 204 | 205 | 304
export type ContentfulStatusCode = Exclude<StatusCode, ContentlessStatusCode>
"#;

    pub(in crate::semantic) type Sources<'a> = [(FileId, &'a ParseResult, &'a str, bool)];

    pub(in crate::semantic) fn with_fixture(
        work: impl FnOnce(&mut CanonicalCheckerContext<'_>, &Sources<'_>),
    ) {
        let source = parse_source_file(SOURCE_TEXT);
        let status = parse_source_file(STATUS_TEXT);
        let other = parse_source_file(STATUS_TEXT);
        let es5 = parse_source_file(include_str!("../../../ts_bundled/libs/lib.es5.d.ts"));
        let decorators =
            parse_source_file(include_str!("../../../ts_bundled/libs/lib.decorators.d.ts"));
        let legacy = parse_source_file(include_str!(
            "../../../ts_bundled/libs/lib.decorators.legacy.d.ts"
        ));
        let files = [
            (SOURCE, &source, "\"/project/types.ts\"", false),
            (STATUS, &status, "\"/project/utils/http-status.ts\"", false),
            (OTHER_STATUS, &other, "\"/other/http-status.ts\"", false),
            (ES5, &es5, "\"/lib/lib.es5.d.ts\"", true),
            (
                DECORATORS,
                &decorators,
                "\"/lib/lib.decorators.d.ts\"",
                true,
            ),
            (LEGACY, &legacy, "\"/lib/lib.decorators.legacy.d.ts\"", true),
        ];
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, path, library) in &files {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        library,
                        library,
                        if library {
                            CanonicalModuleState::Script
                        } else {
                            CanonicalModuleState::External
                        },
                    ),
                )
                .unwrap();
        }
        for &(file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let specifier = source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    source.arena.id(),
                    SOURCE,
                    import.module_specifier,
                ))
            })
            .unwrap();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .iter()
                .map(|&(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: true,
                },
                name_resolution: CanonicalNameResolverOptions {
                    emit_target: ts_options::ScriptTarget::Es2022,
                    ..CanonicalNameResolverOptions::default()
                },
                module_kind: ts_options::ModuleKind::Es2020,
                ..CanonicalCheckerOptions::default()
            },
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        STATUS,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
            ]),
        )
        .unwrap();
        work(&mut context, &files);
    }

    pub(in crate::semantic) fn alias(files: &Sources<'_>, file: FileId, name: &str) -> NodeRef {
        let parsed = files.iter().find(|row| row.0 == file).unwrap().1;
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(data) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(data.name)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    pub(in crate::semantic) fn operand(
        context: &CanonicalCheckerContext<'_>,
        files: &Sources<'_>,
        name: &str,
        index: usize,
        default: bool,
    ) -> NodeRef {
        let owner = alias(files, SOURCE, name);
        let parameter = context
            .store()
            .source_direct_children(owner)
            .unwrap()
            .into_iter()
            .filter(|&node| {
                context.store().source_node_kind(node) == Some(SyntaxKind::TypeParameter)
            })
            .nth(index)
            .unwrap();
        let annotation = context
            .store()
            .source_alias_type_parameter_annotations(parameter)
            .unwrap();
        if default {
            annotation.default_type.unwrap()
        } else {
            annotation.constraint.unwrap()
        }
    }

    pub(in crate::semantic) fn graph(
        context: &CanonicalCheckerContext<'_>,
        files: &Sources<'_>,
        node: NodeRef,
        type_: TypeId,
    ) -> SourceAliasOperandGraph {
        let store = context.store();
        let host = context
            .declared_type_host()
            .unwrap()
            .with_module_resolutions(context.module_resolutions());
        let source = plan_source_alias_operand_source(store, &host, node)
            .unwrap()
            .unwrap();
        let mut objects = Vec::new();
        for &(file, parsed, _, library) in files {
            if library {
                continue;
            }
            for (id, record) in parsed.arena.iter() {
                let node = NodeRef::new(parsed.arena.id(), file, id);
                if record.kind == SyntaxKind::TypeLiteral
                    && store
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type)
                        .is_some()
                {
                    objects.push(
                        plan_type_literal(
                            store,
                            &host,
                            node,
                            source_alias_direct_owner(store, node).unwrap(),
                        )
                        .unwrap(),
                    );
                }
            }
        }
        let imports = objects
            .iter()
            .flat_map(|plan| &plan.properties)
            .filter_map(|property| {
                plan_source_property_type_import(store, &host, property.type_node).unwrap()
            })
            .collect::<Vec<_>>();
        let parsed = files.iter().find(|row| row.0 == node.file).unwrap().1;
        let indexed = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let child = NodeRef::new(parsed.arena.id(), node.file, id);
                if record.kind != SyntaxKind::IndexedAccessType
                    || source_alias_operand_path(store, &source, child).is_err()
                {
                    return None;
                }
                Some(
                    super::super::indexed_access_types::plan_source_alias_indexed_bound(
                        store, &host, &source, child,
                    )
                    .unwrap(),
                )
            })
            .collect::<Vec<_>>();
        build_source_alias_operand_graph(
            store,
            &host,
            &source,
            node,
            type_,
            &objects,
            &imports,
            &indexed,
            Some(CanonicalArrayTargets::from_global_types(
                context.global_types(),
            )),
        )
        .unwrap()
    }

    pub(in crate::semantic) fn prepare_graph(
        context: &mut CanonicalCheckerContext<'_>,
        files: &Sources<'_>,
        node: NodeRef,
    ) -> (TypeId, SourceAliasOperandGraph) {
        let type_ = context.get_type_from_type_node(node).unwrap();
        (type_, graph(context, files, node, type_))
    }

    pub(in crate::semantic) fn without_closed_object(
        graph: &SourceAliasOperandGraph,
    ) -> SourceAliasOperandGraph {
        let mut changed = graph.clone();
        let node = changed
            .nodes
            .iter()
            .find_map(|(&node, row)| {
                matches!(row.proof, SourceAliasOperandProof::Object { .. }).then_some(node)
            })
            .unwrap();
        changed.nodes.remove(&node);
        changed
    }

    fn assert_rejected_without_writes(
        store: &CanonicalTypeMapperStore,
        graph: &SourceAliasOperandGraph,
        targets: CanonicalArrayTargets,
    ) {
        let before = format!("{store:?}");
        let error = graph
            .validate_retained(store, graph.type_, Some(targets))
            .unwrap_err();
        assert!(matches!(
            error,
            RelationUnavailable::InvalidStructuredMembers(_) | RelationUnavailable::Symbol(_)
        ));
        for _ in 0..2 {
            assert_eq!(
                graph.validate_retained(store, graph.type_, Some(targets)),
                Err(error)
            );
            assert_eq!(format!("{store:?}"), before);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep both real index levels, their closed leaves, and the same source query.
    fn source_alias_bound_graph_keeps_schema_indexes_and_input_empty_leaves() {
        with_fixture(|context, files| {
            let schema_node = operand(context, files, "SchemaBound", 0, false);
            let (schema, schema_graph) = prepare_graph(context, files, schema_node);
            let targets = CanonicalArrayTargets::from_global_types(context.global_types());
            let indexes =
                schema_graph
                    .nodes
                    .iter()
                    .filter_map(|(&node, row)| {
                        let data = context
                            .store()
                            .type_payload(row.type_)?
                            .data()
                            .structured()?;
                        (row.kind == SyntaxKind::TypeLiteral && data.index_infos.is_some())
                            .then_some((node, row.type_, data.index_infos.clone().unwrap()))
                    })
                    .collect::<Vec<_>>();
            assert_eq!(indexes.len(), 2);
            let schema_owner =
                bound_declaration_symbol(context.store(), alias(files, SOURCE, "Schema")).unwrap();
            let record = context.store().type_payload(schema).unwrap();
            assert_eq!(
                context
                    .store()
                    .type_alias(record.alias().unwrap())
                    .unwrap()
                    .symbol(),
                Some(schema_owner)
            );
            for (node, object, infos) in &indexes {
                let [id] = infos.as_slice() else {
                    panic!("one source index stays one slot");
                };
                let info = context.store().index_info(*id).unwrap();
                let declaration = info.declaration().unwrap();
                assert_eq!(
                    context.store().source_node_parent(declaration),
                    Some(SourceNodeParent::Parent(*node))
                );
                assert_eq!(
                    context.store().source_node_kind(declaration),
                    Some(SyntaxKind::IndexSignature)
                );
                assert_eq!(info.index_symbol(), None);
                assert!(!info.is_readonly());
                assert!(info.components().is_empty());
                let parameter = context
                    .store()
                    .source_child_with_kind(declaration, SyntaxKind::Parameter)
                    .unwrap();
                let symbol = context
                    .store()
                    .source_declaration_symbol(parameter)
                    .unwrap();
                assert_eq!(
                    context.store().symbol(symbol).unwrap().flags(),
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE
                );
                assert_ne!(symbol, schema_graph.source.parameter().1);
                let key = context
                    .store()
                    .source_direct_type_annotation(parameter)
                    .unwrap();
                let value = context
                    .store()
                    .source_direct_type_annotation(declaration)
                    .unwrap();
                assert_eq!(schema_graph.child_type(key), Ok(info.key_type()));
                assert_eq!(schema_graph.child_type(value), Ok(info.value_type()));
                if *object != schema {
                    assert_eq!(context.store().type_payload(*object).unwrap().alias(), None);
                }
            }
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let mapping = schema_graph
                .nodes
                .values()
                .find(|row| matches!(row.proof, SourceAliasOperandProof::StringMapping { .. }))
                .unwrap();
            let TypeData::StringMapping(data) =
                context.store().type_payload(mapping.type_).unwrap().data()
            else {
                panic!("the key keeps its real mapping");
            };
            assert_eq!(data.target, string);
            assert_eq!(
                context
                    .store()
                    .type_payload(mapping.type_)
                    .unwrap()
                    .symbol(),
                bound_declaration_symbol(context.store(), alias(files, ES5, "Lowercase"))
            );
            let template = schema_graph
                .nodes
                .values()
                .find(|row| matches!(row.proof, SourceAliasOperandProof::Template { .. }))
                .unwrap();
            let TypeData::TemplateLiteral(data) =
                context.store().type_payload(template.type_).unwrap().data()
            else {
                panic!("the key keeps its real template");
            };
            assert_eq!(data.texts, ["$", ""]);
            assert_eq!(data.types, [mapping.type_]);
            let response_body = context
                .store()
                .source_direct_type_annotation(alias(files, SOURCE, "ResponseFormat"))
                .unwrap();
            assert_eq!(schema_graph.child_type(response_body), Ok(string));
            assert!(matches!(
                schema_graph.nodes[&response_body].proof,
                SourceAliasOperandProof::Union { .. }
            ));
            let import = schema_graph
                .nodes
                .values()
                .find_map(|row| match &row.proof {
                    SourceAliasOperandProof::Named {
                        import: Some(import),
                        ..
                    } => Some(import),
                    _ => None,
                })
                .unwrap();
            assert_eq!(
                import.target_symbol(),
                bound_declaration_symbol(context.store(), alias(files, STATUS, "StatusCode"))
                    .unwrap()
            );
            import.validate_retained(context.store()).unwrap();
            let status = context
                .store()
                .type_alias_links(import.target_symbol())
                .unwrap()
                .declared_type
                .unwrap();
            let TypeData::Union(status_union) =
                context.store().type_payload(status).unwrap().data()
            else {
                panic!("all original numeric status members remain");
            };
            assert_eq!(status_union.union.types.len(), 64);
            let input_node = operand(context, files, "InputBound", 0, false);
            let (input, input_graph) = prepare_graph(context, files, input_node);
            let empty = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .empty_type_literal_type;
            let empty_nodes = input_graph
                .nodes
                .iter()
                .filter(|(_, row)| row.kind == SyntaxKind::TypeLiteral && row.type_ == empty)
                .map(|(&node, _)| node)
                .collect::<Vec<_>>();
            assert_eq!(empty_nodes.len(), 2);
            for node in &empty_nodes {
                input_graph
                    .validate_closed_object(context.store(), *node, empty, Some(targets))
                    .unwrap();
            }
            let snapshot = format!("{:?}", context.store());
            for _ in 0..2 {
                schema_graph
                    .validate_retained(context.store(), schema, Some(targets))
                    .unwrap();
                input_graph
                    .validate_retained(context.store(), input, Some(targets))
                    .unwrap();
                assert!(
                    schema_graph
                        .mapping_type_is_closed(context.store(), schema, Some(targets))
                        .unwrap()
                );
                assert_eq!(format!("{:?}", context.store()), snapshot);
            }
            assert!(context.diagnostics().is_empty());
        });
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each damaged consumed row is restored before the next read-only check.
    fn source_alias_bound_graph_rejects_changed_import_union_and_index_rows() {
        with_fixture(|context, files| {
            let node = operand(context, files, "SchemaBound", 0, false);
            let (_, graph) = prepare_graph(context, files, node);
            let targets = CanonicalArrayTargets::from_global_types(context.global_types());
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let object_rows =
                graph
                    .nodes
                    .iter()
                    .filter_map(|(&node, row)| {
                        let data = context
                            .store()
                            .type_payload(row.type_)?
                            .data()
                            .structured()?;
                        (row.kind == SyntaxKind::TypeLiteral && data.index_infos.is_some())
                            .then_some((node, row.type_, data.clone()))
                    })
                    .collect::<Vec<_>>();
            assert_eq!(object_rows.len(), 2);
            for (_, object, members) in &object_rows {
                let original = members.index_infos.as_deref().unwrap()[0];
                let info = context.store().index_info(original).unwrap();
                let (key, value, readonly, declaration) = (
                    info.key_type(),
                    info.value_type(),
                    info.is_readonly(),
                    info.declaration(),
                );
                for changed in 0..5 {
                    let store = context.store_mut_for_test();
                    let replacement = store
                        .alloc_index_info(
                            if changed == 0 { number } else { key },
                            if changed == 1 { number } else { value },
                            if changed == 2 { !readonly } else { readonly },
                            if changed == 3 { None } else { declaration },
                            Vec::new(),
                        )
                        .unwrap();
                    assert!(store.set_structured_type_members(
                        *object,
                        members.members,
                        members.properties.clone(),
                        None,
                        None,
                        Some(vec![replacement])
                    ));
                    assert_rejected_without_writes(store, &graph, targets);
                    assert!(store.set_structured_type_members(
                        *object,
                        members.members,
                        members.properties.clone(),
                        None,
                        None,
                        members.index_infos.clone()
                    ));
                    graph
                        .validate_retained(store, graph.type_, Some(targets))
                        .unwrap();
                }
            }
            let nested = object_rows
                .iter()
                .find(|(_, type_, _)| *type_ != graph.type_)
                .unwrap()
                .0;
            let mapping_argument = graph
                .nodes
                .values()
                .find_map(|row| match row.proof {
                    SourceAliasOperandProof::StringMapping { argument, .. } => Some(argument),
                    _ => None,
                })
                .unwrap();
            let removed_literal = graph.nodes.iter().find_map(|(&node, row)| matches!(&row.proof, SourceAliasOperandProof::Literal(LiteralValue::String(value)) if value == "json").then_some(node)).unwrap();
            for changed in [nested, mapping_argument, removed_literal] {
                let store = context.store_mut_for_test();
                let original = store.type_node_links(changed).cloned().unwrap_or_default();
                assert!(store.set_type_node_links(
                    changed,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        outer_type_parameters: None
                    }
                ));
                assert_rejected_without_writes(store, &graph, targets);
                assert!(store.set_type_node_links(changed, original));
                graph
                    .validate_retained(store, graph.type_, Some(targets))
                    .unwrap();
            }
            let import = graph
                .nodes
                .values()
                .find_map(|row| match &row.proof {
                    SourceAliasOperandProof::Named {
                        import: Some(import),
                        ..
                    } => Some(import.clone()),
                    _ => None,
                })
                .unwrap();
            let other =
                bound_declaration_symbol(context.store(), alias(files, OTHER_STATUS, "StatusCode"))
                    .unwrap();
            let other_type = context.get_declared_type_of_symbol(other).unwrap();
            let original_type = context
                .store()
                .type_alias_links(import.target_symbol())
                .unwrap()
                .declared_type
                .unwrap();
            let (TypeData::Union(original_union), TypeData::Union(other_union)) = (
                context.store().type_payload(original_type).unwrap().data(),
                context.store().type_payload(other_type).unwrap().data(),
            ) else {
                panic!("both real providers have the same complete numeric shape");
            };
            assert_eq!(original_union.union.types, other_union.union.types);
            assert_ne!(other, import.target_symbol());
            let store = context.store_mut_for_test();
            let original = store
                .alias_symbol_links(import.alias_symbol())
                .unwrap()
                .clone();
            let mut changed = original.clone();
            changed.alias_target = AliasTargetState::Resolved(other);
            changed.immediate_target = Some(other);
            assert!(store.set_alias_symbol_links(import.alias_symbol(), changed));
            assert_rejected_without_writes(store, &graph, targets);
            assert!(store.set_alias_symbol_links(import.alias_symbol(), original));
            graph
                .validate_retained(store, graph.type_, Some(targets))
                .unwrap();
            assert_rejected_without_writes(store, &without_closed_object(&graph), targets);

            let wrapped_node = operand(context, files, "WrappedBound", 0, false);
            let (wrapped, wrapped_graph) = prepare_graph(context, files, wrapped_node);
            let wrappers = wrapped_graph
                .nodes
                .iter()
                .filter_map(|(&node, row)| {
                    (row.kind == SyntaxKind::ParenthesizedType).then_some((node, row.type_))
                })
                .collect::<Vec<_>>();
            assert_eq!(wrappers.len(), 4);
            let before = format!("{:?}", context.store());
            for &(node, type_) in &wrappers {
                assert!(
                    context
                        .store()
                        .type_node_links(node)
                        .is_none_or(|links| links == &TypeNodeLinks::default())
                );
                assert_eq!(
                    source_alias_cached_child(context.store(), node),
                    Some(type_)
                );
            }
            wrapped_graph
                .validate_retained(context.store(), wrapped, Some(targets))
                .unwrap();
            assert_eq!(format!("{:?}", context.store()), before);
            let store = context.store_mut_for_test();
            for (node, type_) in wrappers {
                assert!(store.set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        outer_type_parameters: None
                    }
                ));
                wrapped_graph
                    .validate_retained(store, wrapped, Some(targets))
                    .unwrap();
                for changed in [
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        outer_type_parameters: None,
                    },
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        outer_type_parameters: Some(Vec::new()),
                    },
                ] {
                    assert!(store.set_type_node_links(node, changed));
                    assert_eq!(source_alias_cached_child(store, node), None);
                    assert_rejected_without_writes(store, &wrapped_graph, targets);
                }
                assert!(store.set_type_node_links(node, TypeNodeLinks::default()));
                wrapped_graph
                    .validate_retained(store, wrapped, Some(targets))
                    .unwrap();
            }
            assert!(context.diagnostics().is_empty());
        });
    }
}

#[cfg(test)]
mod inline_source_tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeHost,
        object_members::{
            PropertyObjectState, ensure_type_literal_shell, plan_type_literal,
            preflight_inline_type_literal_shell_cache, publish_property_members,
        },
        production::GlobalMergeCompletion,
    };

    const FILE: FileId = FileId::new(29_840);

    fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        context_with_module_state(parsed, CanonicalModuleState::Script)
    }

    fn context_with_module_state(
        parsed: &ParseResult,
        module_state: CanonicalModuleState,
    ) -> CanonicalCheckerContext<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                FILE,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/inline-source.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, FILE)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(FILE, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn alias_body(context: &CanonicalCheckerContext<'_>, name: &str) -> NodeRef {
        let store = context.store();
        let symbol = store
            .symbol_table(context.globals())
            .unwrap()
            .get_source(name)
            .unwrap();
        let symbol = store.get_merged_symbol(symbol).unwrap();
        let declaration = store.symbol(symbol).unwrap().declarations().unwrap()[0];
        store.source_direct_type_annotation(declaration).unwrap()
    }

    fn literal_under(store: &CanonicalTypeMapperStore, node: NodeRef) -> NodeRef {
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            if store.source_node_kind(node) == Some(SyntaxKind::TypeLiteral) {
                return node;
            }
            pending.extend(store.source_direct_children(node).unwrap());
        }
        panic!("the test alias must contain a literal")
    }

    fn counts(store: &CanonicalTypeMapperStore) -> ([usize; 6], [usize; 26]) {
        (
            [
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.type_alias_len(),
            ],
            store.checker_link_allocated_lengths(),
        )
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the original source, poison, and restored proof together.
    fn inline_source_keeps_lexical_parameters_and_original_literal_identity() {
        let parsed = parse_source_file(concat!(
            "type Observer<T> = { next: (value: T) => void; }; ",
            "type Subject<T> = ({ readonly observers: Observer<T>[]; ",
            "subscribe: (value: Observer<T>) => number; }) & Observer<T>;",
        ));
        let mut context = context(&parsed);
        let observer = alias_body(&context, "Observer");
        let subject_body = alias_body(&context, "Subject");
        let literal = literal_under(context.store(), subject_body);
        let before = counts(context.store());
        let source = inline_property_object_source_header(context.store(), literal)
            .unwrap()
            .unwrap();
        let observer_source = property_object_alias_source_header(context.store(), observer)
            .unwrap()
            .unwrap();
        assert_eq!(source.declaration, literal);
        assert_eq!(source.parameters.len(), 1);
        assert_eq!(source.properties.len(), 2);
        assert!(source.properties[0].readonly);
        assert!(!source.properties[1].readonly);
        assert_ne!(source.parameters[0].1, observer_source.parameters[0].1);
        assert_ne!(source.parameter_owner, observer_source.alias_symbol);
        assert!(
            property_object_alias_source_header(context.store(), literal)
                .unwrap()
                .is_none()
        );
        for property in &source.properties {
            assert_eq!(
                context.store().symbol(property.symbol).unwrap().parent(),
                Some(source.source_symbol)
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(property.symbol)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .type_node_links(property.type_node)
                    .is_none()
            );
        }
        for _ in 0..2 {
            assert_eq!(
                inline_property_object_source_header(context.store(), literal).unwrap(),
                Some(source.clone())
            );
            assert_eq!(counts(context.store()), before);
        }

        let parameter = context
            .get_declared_type_of_symbol(source.parameters[0].1)
            .unwrap();
        let other_parameter = context
            .get_declared_type_of_symbol(observer_source.parameters[0].1)
            .unwrap();
        assert_ne!(parameter, other_parameter);
        let bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let plan = plan_type_literal(store, &host, literal, None).unwrap();
        let state = ensure_type_literal_shell(store, &plan).unwrap();
        let PropertyObjectState::Shell(target) = state else {
            panic!("a new inline object must have a cold shell")
        };
        assert!(store.type_payload(target).unwrap().alias().is_none());
        assert_eq!(
            store.type_payload(target).unwrap().symbol(),
            Some(source.source_symbol)
        );
        assert!(
            property_object_alias_projection(store, target)
                .unwrap()
                .is_none()
        );
        let projection = source_property_object_projection(store, target)
            .unwrap()
            .unwrap();
        assert!(matches!(
            projection,
            SourcePropertyObjectProjection::Inline(_)
        ));
        assert_eq!(projection.target(), target);
        assert_eq!(projection.parameters(), &[parameter]);
        assert_eq!(projection.arguments(), &[parameter]);
        assert_eq!(projection.parameter_owner(), source.parameter_owner);
        assert!(projection.mapper().is_none());
        assert!(projection.display_identity().is_none());
        assert!(projection.identity_arguments().is_empty());
        let original = store.type_node_links(literal).unwrap().clone();
        assert_eq!(
            original.outer_type_parameters.as_deref(),
            Some(&[parameter][..])
        );
        assert!(store.set_type_node_links(
            literal,
            TypeNodeLinks {
                resolved_type: Some(target),
                outer_type_parameters: Some(vec![other_parameter]),
            }
        ));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(source_property_object_projection(store, target).is_err());
            assert!(ensure_type_literal_shell(store, &plan).is_err());
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_type_node_links(literal, original));
        let warm = counts(store);
        for _ in 0..2 {
            assert_eq!(ensure_type_literal_shell(store, &plan).unwrap(), state);
            assert_eq!(
                source_property_object_projection(store, target).unwrap(),
                Some(projection.clone())
            );
            assert_eq!(counts(store), warm);
            for property in &source.properties {
                assert!(store.value_symbol_links(property.symbol).is_none());
                assert!(store.type_node_links(property.type_node).is_none());
            }
        }
    }

    #[test]
    fn inline_shell_rejects_cold_property_link_poison_before_publication() {
        let parsed = parse_source_file(
            "type Other<T> = { other: T }; type Subject<T> = { value: T; fixed: \"fixed\" } & Other<T>;",
        );
        let mut context = context(&parsed);
        let body = alias_body(&context, "Subject");
        let literal = literal_under(context.store(), body);
        let source = inline_property_object_source_header(context.store(), literal)
            .unwrap()
            .unwrap();
        let bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_type_literal(context.store(), &host, literal, None).unwrap();
        let annotation = plan.properties[1].type_node;
        let fixed = context.get_type_from_type_node(annotation).unwrap();
        let store = context.store_mut_for_test();
        assert_eq!(
            store.type_node_links(annotation).unwrap().resolved_type,
            Some(fixed)
        );
        assert!(store.declared_type_links(source.parameters[0].1).is_none());
        let property = plan.properties[0].symbol;
        let links = ValueSymbolLinks {
            write_type: Some(store.intrinsic_bootstrap().unwrap().number_type),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(property, links.clone()));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(preflight_inline_type_literal_shell_cache(store, &plan).is_err());
            assert!(ensure_type_literal_shell(store, &plan).is_err());
            assert_eq!(store.value_symbol_links(property), Some(&links));
            assert!(store.type_node_links(literal).is_none());
            assert!(store.declared_type_links(source.parameters[0].1).is_none());
            assert_eq!(
                store.type_node_links(annotation).unwrap().resolved_type,
                Some(fixed)
            );
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_value_symbol_links(property, ValueSymbolLinks::default()));
        assert_eq!(
            preflight_inline_type_literal_shell_cache(store, &plan).unwrap(),
            None
        );
        assert_eq!(counts(store), poisoned);
        context
            .get_declared_type_of_symbol(source.parameters[0].1)
            .unwrap();
        let store = context.store_mut_for_test();
        assert!(matches!(
            ensure_type_literal_shell(store, &plan),
            Ok(PropertyObjectState::Shell(_))
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Cold source, cache poison, and restoration share the same object.
    fn closed_alias_source_identity_keeps_properties_cold_and_checks_present_values() {
        let parsed = parse_source_file(concat!(
            "type Closed = { value: number; }; type Noop = () => void; ",
            "type Generic<T> = { value: T; }; ",
            "function outer<T>() { type Captured = { value: T; }; }",
        ));
        let mut context = context(&parsed);
        let closed = alias_body(&context, "Closed");
        let noop = alias_body(&context, "Noop");
        let generic = alias_body(&context, "Generic");
        let captured = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                if record.kind != SyntaxKind::TypeAliasDeclaration {
                    return None;
                }
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                let name = context
                    .store()
                    .source_child_with_kind(node, SyntaxKind::Identifier)?;
                (context.store().source_identifier_text(name) == Some("Captured"))
                    .then(|| context.store().source_direct_type_annotation(node).unwrap())
            })
            .unwrap();
        let before = counts(context.store());
        let source = closed_type_alias_source_header(context.store(), closed)
            .unwrap()
            .unwrap();
        assert!(
            closed_type_alias_source_header(context.store(), noop)
                .unwrap()
                .is_some()
        );
        assert!(
            closed_type_alias_source_header(context.store(), generic)
                .unwrap()
                .is_none()
        );
        assert!(
            closed_type_alias_source_header(context.store(), captured)
                .unwrap()
                .is_none()
        );
        assert_eq!(counts(context.store()), before);
        let bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let plan = plan_type_literal(store, &host, closed, Some(source.alias_symbol)).unwrap();
        let target = ensure_type_literal_shell(store, &plan).unwrap().type_id();
        let property = &plan.properties[0];
        assert!(store.value_symbol_links(property.symbol).is_none());
        assert!(store.type_node_links(property.type_node).is_none());
        let warm = counts(store);
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).unwrap());
            assert_eq!(counts(store), warm);
            assert!(store.value_symbol_links(property.symbol).is_none());
            assert!(store.type_node_links(property.type_node).is_none());
        }
        let partial = TypeNodeLinks {
            outer_type_parameters: Some(vec![store.intrinsic_bootstrap().unwrap().number_type]),
            ..TypeNodeLinks::default()
        };
        assert!(store.set_type_node_links(property.type_node, partial.clone()));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).is_err());
            assert_eq!(store.type_node_links(property.type_node), Some(&partial));
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_type_node_links(property.type_node, TypeNodeLinks::default()));
        let partial = SymbolNodeLinks {
            resolved_symbol: Some(source.alias_symbol),
        };
        assert!(store.set_symbol_node_links(property.type_node, partial.clone()));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).is_err());
            assert_eq!(store.symbol_node_links(property.type_node), Some(&partial));
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_symbol_node_links(property.type_node, SymbolNodeLinks::default()));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let links = ValueSymbolLinks {
            resolved_type: Some(string),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(property.symbol, links.clone()));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).is_err());
            assert_eq!(store.value_symbol_links(property.symbol), Some(&links));
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_value_symbol_links(property.symbol, ValueSymbolLinks::default()));
        assert!(closed_declared_property_object_is_mapping_invariant(store, target).unwrap());
        assert_eq!(counts(store), poisoned);
    }

    #[test]
    fn closed_property_named_cache_must_match_real_alias_provider() {
        let parsed = parse_source_file("type Noop = () => void; type Closed = { value: Noop; };");
        let mut context = context(&parsed);
        let literal = alias_body(&context, "Closed");
        let source = closed_type_alias_source_header(context.store(), literal)
            .unwrap()
            .unwrap();
        let bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan =
            plan_type_literal(context.store(), &host, literal, Some(source.alias_symbol)).unwrap();
        let state = ensure_type_literal_shell(context.store_mut_for_test(), &plan).unwrap();
        let property = &plan.properties[0];
        let value = context.get_type_from_type_node(property.type_node).unwrap();
        let store = context.store_mut_for_test();
        let target = publish_property_members(store, &plan, state, &[value]).unwrap();
        assert!(closed_declared_property_object_is_mapping_invariant(store, target).unwrap());
        let value_links = store.value_symbol_links(property.symbol).unwrap().clone();
        let type_links = store.type_node_links(property.type_node).unwrap().clone();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert_ne!(value, number);
        assert!(store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            }
        ));
        assert!(store.set_type_node_links(
            property.type_node,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            }
        ));
        let poisoned = counts(store);
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).is_err());
            assert_eq!(counts(store), poisoned);
        }
        assert!(store.set_value_symbol_links(property.symbol, value_links));
        assert!(store.set_type_node_links(property.type_node, type_links));
        for _ in 0..2 {
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).unwrap());
            assert_eq!(counts(store), poisoned);
        }
    }

    #[test]
    fn closed_exported_alias_source_identity_replays_resolved_members() {
        for text in [
            "export type Closed = { readonly value: number; };",
            "export type Closed = {};",
        ] {
            let parsed = parse_source_file(text);
            let mut context = context_with_module_state(&parsed, CanonicalModuleState::External);
            let literal = literal_under(
                context.store(),
                NodeRef::new(parsed.arena.id(), FILE, parsed.source_file),
            );
            let source = closed_type_alias_source_header(context.store(), literal)
                .unwrap()
                .unwrap();
            assert!(
                context
                    .store()
                    .symbol(source.alias_symbol)
                    .unwrap()
                    .parent()
                    .is_some()
            );
            let bound = context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let store = context.store_mut_for_test();
            let plan = plan_type_literal(store, &host, literal, Some(source.alias_symbol)).unwrap();
            let state = ensure_type_literal_shell(store, &plan).unwrap();
            let target = state.type_id();
            assert!(closed_declared_property_object_is_mapping_invariant(store, target).unwrap());
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let values = vec![number; plan.properties.len()];
            assert_eq!(
                publish_property_members(store, &plan, state, &values).unwrap(),
                target
            );
            let warm = counts(store);
            for _ in 0..2 {
                assert!(
                    closed_declared_property_object_is_mapping_invariant(store, target).unwrap()
                );
                assert_eq!(counts(store), warm);
                for property in &plan.properties {
                    assert_eq!(
                        store.symbol(property.symbol).unwrap().parent(),
                        Some(source.source_symbol)
                    );
                    assert_eq!(
                        store
                            .value_symbol_links(property.symbol)
                            .unwrap()
                            .resolved_type,
                        Some(number)
                    );
                }
            }
        }
    }
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
