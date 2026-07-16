//! Exact tuple annotation syntax and cache validation.
//!
//! This leaf owns the non-generic type-node slice of pinned
//! `getTypeFromArrayOrTupleTypeNode`, `getTupleElementFlags`, and
//! `getTupleElementInfo`. It deliberately stops before variadic tuples and
//! named rest elements. A syntactic `...T[]` is admitted only with the
//! authoritative global Array targets used by the canonical tuple constructor.
//! Recursive tuple aliases remain an explicit planner boundary until deferred
//! type references and normalized recursive tuple construction are installed.

use ts_ast::{NodeData, NodeRef, SyntaxKind};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, TypeId,
    array_types::CanonicalArrayTargets,
    declared::{DeclaredTypeError, preflight_node},
    signatures::{ElementFlags, TupleElementInfo},
    store::CanonicalTupleTargetKey,
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
};

/// One tuple element after wrappers have been validated and stripped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedTupleElement {
    type_node: NodeRef,
    info: TupleElementInfo,
}

impl PlannedTupleElement {
    pub(super) const fn type_node(self) -> NodeRef {
        self.type_node
    }

    pub(super) const fn info(self) -> TupleElementInfo {
        self.info
    }
}

/// Dependency-free proof for one supported tuple annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TupleTypeNodePlan {
    tuple: NodeRef,
    readonly_operator: Option<NodeRef>,
    elements: Vec<PlannedTupleElement>,
    readonly: bool,
    cached_type: Option<TypeId>,
    cached_element_types: Vec<TypeId>,
}

impl TupleTypeNodePlan {
    pub(super) const fn tuple(&self) -> NodeRef {
        self.tuple
    }

    pub(super) const fn readonly_operator(&self) -> Option<NodeRef> {
        self.readonly_operator
    }

    pub(super) fn elements(&self) -> &[PlannedTupleElement] {
        &self.elements
    }

    pub(super) const fn readonly(&self) -> bool {
        self.readonly
    }

    pub(super) const fn cached_type(&self) -> Option<TypeId> {
        self.cached_type
    }

    pub(super) fn element_infos(&self) -> Result<Vec<TupleElementInfo>, TupleTypeNodeError> {
        let mut infos = Vec::new();
        infos
            .try_reserve(self.elements.len())
            .map_err(|_| TupleTypeNodeError::Capacity(self.tuple))?;
        infos.extend(self.elements.iter().map(|element| element.info));
        Ok(infos)
    }

    pub(super) fn optional_element_count(&self) -> usize {
        self.elements
            .iter()
            .filter(|element| element.info.flags() == ElementFlags::OPTIONAL)
            .count()
    }
}

/// A syntax, provenance, or cache boundary for the supported tuple slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TupleTypeNodeError {
    DeclaredType(DeclaredTypeError),
    InvalidSyntax(NodeRef),
    UnsupportedSyntax {
        node: NodeRef,
        kind: SyntaxKind,
    },
    UnsupportedElementOrder {
        tuple: NodeRef,
        element: NodeRef,
        index: usize,
    },
    AuthoritativeArrayTargetsRequired(NodeRef),
    InvalidCachedType {
        node: NodeRef,
        type_: TypeId,
    },
    InvalidElementInfo(NodeRef),
    Capacity(NodeRef),
}

impl From<DeclaredTypeError> for TupleTypeNodeError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

/// Validates one tuple or `readonly` tuple root without allocating semantics.
pub(super) fn plan_tuple_type_node(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TupleTypeNodePlan, TupleTypeNodeError> {
    let record = preflight_node(store, host, node)?;
    let (tuple, readonly_operator) = match (&record.data, record.kind) {
        (NodeData::TupleTypeNode(_), SyntaxKind::TupleType) => {
            (node, readonly_tuple_parent(store, host, node)?)
        }
        (NodeData::TypeOperatorNode(operator), SyntaxKind::TypeOperator)
            if operator.operator == SyntaxKind::ReadonlyKeyword =>
        {
            let tuple = NodeRef::new(node.arena, node.file, operator.type_);
            let tuple_record = preflight_node(store, host, tuple)?;
            if tuple_record.kind != SyntaxKind::TupleType
                || !matches!(&tuple_record.data, NodeData::TupleTypeNode(_))
                || tuple_record.parent != Some(node.node)
                || tuple_record.range.start <= record.range.start
                || tuple_record.range.end != record.range.end
            {
                return Err(TupleTypeNodeError::InvalidSyntax(node));
            }
            (tuple, Some(node))
        }
        _ => {
            return Err(TupleTypeNodeError::UnsupportedSyntax {
                node,
                kind: record.kind,
            });
        }
    };
    let tuple_record = preflight_node(store, host, tuple)?;
    let NodeData::TupleTypeNode(tuple_data) = &tuple_record.data else {
        return Err(TupleTypeNodeError::InvalidSyntax(tuple));
    };
    if tuple_record.kind != SyntaxKind::TupleType || tuple_data.elements.range != tuple_record.range
    {
        return Err(TupleTypeNodeError::InvalidSyntax(tuple));
    }

    let readonly = readonly_operator.is_some();
    let mut elements = Vec::new();
    elements
        .try_reserve(tuple_data.elements.nodes.len())
        .map_err(|_| TupleTypeNodeError::Capacity(tuple))?;
    let mut previous_end = tuple_record.range.start;
    let mut saw_optional = false;
    let mut seen = Vec::new();
    seen.try_reserve(tuple_data.elements.nodes.len())
        .map_err(|_| TupleTypeNodeError::Capacity(tuple))?;
    for (index, element_id) in tuple_data.elements.nodes.iter().copied().enumerate() {
        let element = NodeRef::new(tuple.arena, tuple.file, element_id);
        let element_record = preflight_node(store, host, element)?;
        if element_record.parent != Some(tuple.node)
            || element_record.range.start < previous_end
            || element_record.range.start < tuple_record.range.start
            || element_record.range.end > tuple_record.range.end
            || seen.contains(&element)
        {
            return Err(TupleTypeNodeError::InvalidSyntax(tuple));
        }
        previous_end = element_record.range.end;
        seen.push(element);

        let planned = plan_tuple_element(store, host, element, array_targets)?;
        match planned.info.flags() {
            ElementFlags::REQUIRED if !saw_optional => {}
            ElementFlags::REQUIRED => {
                return Err(TupleTypeNodeError::UnsupportedElementOrder {
                    tuple,
                    element,
                    index,
                });
            }
            ElementFlags::OPTIONAL => saw_optional = true,
            ElementFlags::REST if index + 1 == tuple_data.elements.nodes.len() => {}
            ElementFlags::REST => {
                return Err(TupleTypeNodeError::UnsupportedElementOrder {
                    tuple,
                    element,
                    index,
                });
            }
            _ => {
                return Err(TupleTypeNodeError::UnsupportedSyntax {
                    node: element,
                    kind: element_record.kind,
                });
            }
        }
        elements.push(planned);
    }

    let mut infos = Vec::new();
    infos
        .try_reserve(elements.len())
        .map_err(|_| TupleTypeNodeError::Capacity(tuple))?;
    infos.extend(elements.iter().map(|element| element.info));
    validate_existing_target(store, tuple, &infos, readonly)?;
    let (cached_type, cached_element_types) = validate_warm_cache(
        store,
        tuple,
        readonly_operator,
        &infos,
        readonly,
        array_targets,
    )?;
    Ok(TupleTypeNodePlan {
        tuple,
        readonly_operator,
        elements,
        readonly,
        cached_type,
        cached_element_types,
    })
}

fn readonly_tuple_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    tuple: NodeRef,
) -> Result<Option<NodeRef>, TupleTypeNodeError> {
    let tuple_record = preflight_node(store, host, tuple)?;
    let Some(parent_id) = tuple_record.parent else {
        return Ok(None);
    };
    let parent = NodeRef::new(tuple.arena, tuple.file, parent_id);
    let parent_record = preflight_node(store, host, parent)?;
    let NodeData::TypeOperatorNode(operator) = &parent_record.data else {
        return Ok(None);
    };
    if parent_record.kind != SyntaxKind::TypeOperator
        || operator.operator != SyntaxKind::ReadonlyKeyword
    {
        return Ok(None);
    }
    if operator.type_ != tuple.node
        || tuple_record.range.start <= parent_record.range.start
        || tuple_record.range.end != parent_record.range.end
    {
        return Err(TupleTypeNodeError::InvalidSyntax(parent));
    }
    Ok(Some(parent))
}

fn plan_tuple_element(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    element: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<PlannedTupleElement, TupleTypeNodeError> {
    let record = preflight_node(store, host, element)?;
    let (type_node, flags, label) = match (&record.data, record.kind) {
        (NodeData::OptionalTypeNode(optional), SyntaxKind::OptionalType) => {
            let child = direct_child(store, host, element, optional.type_)?;
            (child, ElementFlags::OPTIONAL, None)
        }
        (NodeData::NamedTupleMember(named), SyntaxKind::NamedTupleMember) => {
            if named.dot_dot_dot_token.is_some() {
                return Err(TupleTypeNodeError::UnsupportedSyntax {
                    node: element,
                    kind: SyntaxKind::NamedTupleMember,
                });
            }
            let name = direct_child(store, host, element, named.name)?;
            let name_record = preflight_node(store, host, name)?;
            if name_record.kind != SyntaxKind::Identifier {
                return Err(TupleTypeNodeError::InvalidSyntax(element));
            }
            let child = direct_child(store, host, element, named.type_)?;
            let child_record = preflight_node(store, host, child)?;
            if child_record.range.start < name_record.range.end {
                return Err(TupleTypeNodeError::InvalidSyntax(element));
            }
            let optional = if let Some(question_id) = named.question_token {
                let question = direct_child(store, host, element, question_id)?;
                let question_record = preflight_node(store, host, question)?;
                if question_record.kind != SyntaxKind::QuestionToken
                    || question_record.range.start < name_record.range.end
                    || question_record.range.end > child_record.range.start
                {
                    return Err(TupleTypeNodeError::InvalidSyntax(element));
                }
                true
            } else {
                false
            };
            let flags = if optional {
                ElementFlags::OPTIONAL
            } else {
                ElementFlags::REQUIRED
            };
            (child, flags, Some(element))
        }
        (NodeData::RestTypeNode(rest), SyntaxKind::RestType) => {
            let Some(_) = array_targets else {
                return Err(TupleTypeNodeError::AuthoritativeArrayTargetsRequired(
                    element,
                ));
            };
            let array = direct_child(store, host, element, rest.type_)?;
            let Some(child) = parenthesized_array_element(store, host, array)? else {
                return Err(TupleTypeNodeError::UnsupportedSyntax {
                    node: element,
                    kind: SyntaxKind::RestType,
                });
            };
            (child, ElementFlags::REST, None)
        }
        (_, SyntaxKind::RestType | SyntaxKind::OptionalType | SyntaxKind::NamedTupleMember) => {
            return Err(TupleTypeNodeError::InvalidSyntax(element));
        }
        _ => (element, ElementFlags::REQUIRED, None),
    };
    let info = store
        .create_tuple_element_info(flags, label)
        .ok_or(TupleTypeNodeError::InvalidElementInfo(element))?;
    Ok(PlannedTupleElement { type_node, info })
}

fn parenthesized_array_element(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<Option<NodeRef>, TupleTypeNodeError> {
    loop {
        let record = preflight_node(store, host, node)?;
        match (&record.data, record.kind) {
            (NodeData::ParenthesizedTypeNode(parenthesized), SyntaxKind::ParenthesizedType) => {
                node = direct_child(store, host, node, parenthesized.type_)?;
            }
            (NodeData::ArrayTypeNode(array), SyntaxKind::ArrayType) => {
                return direct_child(store, host, node, array.element_type).map(Some);
            }
            _ => return Ok(None),
        }
    }
}

fn direct_child(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    parent: NodeRef,
    child: ts_ast::NodeId,
) -> Result<NodeRef, TupleTypeNodeError> {
    let parent_record = preflight_node(store, host, parent)?;
    let child = NodeRef::new(parent.arena, parent.file, child);
    let child_record = preflight_node(store, host, child)?;
    if child_record.parent != Some(parent.node)
        || child_record.range.start < parent_record.range.start
        || child_record.range.end > parent_record.range.end
    {
        return Err(TupleTypeNodeError::InvalidSyntax(parent));
    }
    Ok(child)
}

fn validate_existing_target(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    infos: &[TupleElementInfo],
    readonly: bool,
) -> Result<(), TupleTypeNodeError> {
    let mut element_infos = Vec::new();
    element_infos
        .try_reserve(infos.len())
        .map_err(|_| TupleTypeNodeError::Capacity(node))?;
    element_infos.extend_from_slice(infos);
    let key = CanonicalTupleTargetKey {
        element_infos,
        readonly,
    };
    let Some(provenance) = store.canonical_tuple_target(&key) else {
        return Ok(());
    };
    let shape = store
        .canonical_tuple_shape(provenance.target)
        .map_err(|_| TupleTypeNodeError::InvalidCachedType {
            node,
            type_: provenance.target,
        })?
        .ok_or(TupleTypeNodeError::InvalidCachedType {
            node,
            type_: provenance.target,
        })?;
    if shape.element_infos() != infos || shape.is_readonly() != readonly {
        return Err(TupleTypeNodeError::InvalidCachedType {
            node,
            type_: provenance.target,
        });
    }
    Ok(())
}

fn validate_warm_cache(
    store: &CanonicalTypeMapperStore,
    tuple: NodeRef,
    readonly_operator: Option<NodeRef>,
    infos: &[TupleElementInfo],
    readonly: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(Option<TypeId>, Vec<TypeId>), TupleTypeNodeError> {
    let tuple_cached = store
        .type_node_links(tuple)
        .and_then(|links| links.resolved_type);
    let operator_cached = readonly_operator
        .and_then(|operator| store.type_node_links(operator))
        .and_then(|links| links.resolved_type);
    if tuple_cached.is_none()
        && let (Some(operator_cached), Some(operator)) = (operator_cached, readonly_operator)
    {
        return Err(TupleTypeNodeError::InvalidCachedType {
            node: operator,
            type_: operator_cached,
        });
    }
    if let (Some(tuple_cached), Some(operator_cached), Some(operator)) =
        (tuple_cached, operator_cached, readonly_operator)
        && tuple_cached != operator_cached
    {
        return Err(TupleTypeNodeError::InvalidCachedType {
            node: operator,
            type_: operator_cached,
        });
    }
    let cached = tuple_cached.or(operator_cached);
    let Some(cached) = cached else {
        return Ok((None, Vec::new()));
    };
    if infos.len() == 1 && infos[0].flags() == ElementFlags::REST {
        let Some(targets) = array_targets else {
            return Err(TupleTypeNodeError::AuthoritativeArrayTargetsRequired(tuple));
        };
        let reference = store
            .canonical_array_reference_with_targets(targets, cached)
            .map_err(|_| TupleTypeNodeError::InvalidCachedType {
                node: tuple,
                type_: cached,
            })?
            .ok_or(TupleTypeNodeError::InvalidCachedType {
                node: tuple,
                type_: cached,
            })?;
        if reference.readonly != readonly
            || reference.array_literal
            || reference.base_type != cached
        {
            return Err(TupleTypeNodeError::InvalidCachedType {
                node: tuple,
                type_: cached,
            });
        }
        let mut element_types = Vec::new();
        element_types
            .try_reserve(1)
            .map_err(|_| TupleTypeNodeError::Capacity(tuple))?;
        element_types.push(reference.element_type);
        return Ok((Some(cached), element_types));
    }
    let shape = store
        .canonical_tuple_shape(cached)
        .map_err(|_| TupleTypeNodeError::InvalidCachedType {
            node: tuple,
            type_: cached,
        })?
        .ok_or(TupleTypeNodeError::InvalidCachedType {
            node: tuple,
            type_: cached,
        })?;
    if shape.element_infos() != infos || shape.is_readonly() != readonly {
        return Err(TupleTypeNodeError::InvalidCachedType {
            node: tuple,
            type_: cached,
        });
    }
    let mut element_types = Vec::new();
    element_types
        .try_reserve(shape.element_types().len())
        .map_err(|_| TupleTypeNodeError::Capacity(tuple))?;
    element_types.extend_from_slice(shape.element_types());
    Ok((Some(cached), element_types))
}

/// Validates the semantic element identities held by a warm tuple cache.
pub(super) fn validate_warm_tuple_elements(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    plan: &TupleTypeNodePlan,
    base_types: &[TypeId],
) -> Result<(), TupleTypeNodeError> {
    if plan.cached_type.is_none() {
        return Ok(());
    }
    if base_types.len() != plan.elements.len()
        || plan.cached_element_types.len() != plan.elements.len()
    {
        return Err(TupleTypeNodeError::InvalidCachedType {
            node: plan.tuple,
            type_: plan.cached_type.expect("warm plan has a cache"),
        });
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(TupleTypeNodeError::InvalidSyntax(plan.tuple))?;
    for ((element, base), resolved) in plan
        .elements
        .iter()
        .zip(base_types)
        .zip(&plan.cached_element_types)
    {
        let valid = if element.info.flags() == ElementFlags::OPTIONAL
            && bootstrap.options.strict_null_checks
        {
            valid_optional_element_type(
                store,
                array_targets,
                *base,
                bootstrap.undefined_or_missing_type,
                *resolved,
            )
        } else {
            base == resolved
        };
        if !valid {
            return Err(TupleTypeNodeError::InvalidCachedType {
                node: plan.tuple,
                type_: plan.cached_type.expect("warm plan has a cache"),
            });
        }
    }
    Ok(())
}

fn valid_optional_element_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    base: TypeId,
    sentinel: TypeId,
    resolved: TypeId,
) -> bool {
    let Some(base_record) = store.type_payload(base) else {
        return false;
    };
    if base == sentinel
        || base_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return resolved == base;
    }
    let mut expected = match base_record.data() {
        TypeData::Union(union) if union.union.types.contains(&sentinel) => {
            let valid = match array_targets {
                Some(targets) => store.validate_union_constituent_with_array_targets(targets, base),
                None => store.validate_union_constituent(base),
            };
            return resolved == base && valid.is_ok();
        }
        TypeData::Union(_) => {
            return store
                .validate_optional_union_of_union_result(array_targets, base, sentinel, resolved)
                .is_ok();
        }
        _ => vec![base],
    };
    expected.retain(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
    });
    if !expected.contains(&sentinel) {
        expected.push(sentinel);
    }
    if expected.len() == 1 {
        return resolved == expected[0];
    }
    let Some(TypeData::Union(union)) = store.type_payload(resolved).map(TypeRecord::data) else {
        return false;
    };
    let valid_union = match array_targets {
        Some(targets) => {
            store.validate_cached_union_result_with_array_targets(targets, resolved, None)
        }
        None => store.validate_cached_union_result(resolved, None),
    };
    valid_union.is_ok() && union.union.types.as_slice() == expected.as_slice()
}
