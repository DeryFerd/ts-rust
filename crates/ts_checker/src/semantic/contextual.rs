//! Contextual typing for the property-only object-literal source slice.
//!
//! The pinned checker obtains an object's contextual type once, looks up each
//! source property by name, and checks ordinary property initializers as
//! mutable locations. Const-asserted properties retain regular literal types.
//! Finite mapped `Record` targets retain their authenticated transient member
//! symbols. Broad string-keyed records retain their real canonical index
//! instead. Resolved object intersections preserve contextual information from
//! their non-`any` constituents. This module validates the complete dependency
//! tree before publishing the source object, so a malformed target cannot
//! leave a partially constructed object behind.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{EscapedName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, IndexInfoId,
    RelationUnavailable, SymbolTableId, TypeId, VariableInvariant,
    callables::{StoredSingleCallableValidation, validate_stored_single_callable},
    declared::cached_ordinary_type_parameter_owner,
    mapped_types::{FiniteRecordMappedProjection, MappedTypeError, MappedTypeModifiers},
    object_members::PlannedProperty,
    relater::ResolvedDeclaredPropertyObject,
    source::{
        PlannedExpression, PlannedExpressionKind, PlannedIdentifierReadKind, SourceCheckError,
        SourceSyntaxRole, UnsupportedSourceSyntax,
    },
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// Whether an expression is checked through the cached root path or as a
/// mutable object-property initializer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpressionLocation {
    Cached,
    Mutable,
    Readonly,
}

struct ExpressionPreparationState<'a> {
    current_flow_types: &'a HashMap<SemanticSymbolId, TypeId>,
    tuple_contexts: HashMap<NodeRef, TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LiteralTreatment {
    Fresh,
    Regular,
    WidenedPrimitive,
    Identity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PreparedExpression {
    Literal(LiteralTreatment),
    Identifier(LiteralTreatment),
    ClassReceiver,
    Template(Option<TypeId>),
    Parenthesized(Box<PreparedExpression>),
    Array(Vec<PreparedExpression>),
    Object(Vec<PreparedExpression>),
    Property(Box<PreparedExpression>),
    Arrow(Option<TypeId>),
    Assertion(Option<TypeId>),
    Conditional {
        contextual_type: Option<TypeId>,
        mutable_result: bool,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LiteralKind {
    String,
    Number,
    BigInt,
    Boolean,
}

/// Source-declared members and transient mapped members require distinct
/// projections because mapped properties do not have source declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
enum ContextualPropertyObject {
    Declared {
        object: ResolvedDeclaredPropertyObject,
        string_index: Option<TypeId>,
    },
    Synthetic(Vec<(EscapedName, TypeId)>),
    FiniteRecord(FiniteRecordMappedProjection),
    BroadRecord(BroadRecordMappedProjection),
}

/// The authenticated, declaration-free string index of `Record<string, T>`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct BroadRecordMappedProjection {
    pub(super) type_: TypeId,
    pub(super) members: SymbolTableId,
    pub(super) index: IndexInfoId,
    pub(super) value_type: TypeId,
}

impl ContextualPropertyObject {
    fn property_types(&self) -> Vec<TypeId> {
        match self {
            Self::Declared {
                object,
                string_index,
            } => object
                .properties()
                .iter()
                .map(|property| property.type_)
                .chain(string_index.iter().copied())
                .collect(),
            Self::Synthetic(properties) => properties.iter().map(|(_, type_)| *type_).collect(),
            Self::FiniteRecord(object) => object
                .properties
                .iter()
                .map(|property| property.type_)
                .collect(),
            Self::BroadRecord(object) => vec![object.value_type],
        }
    }

    fn get_source(&self, name: &str) -> Option<TypeId> {
        match self {
            Self::Declared {
                object,
                string_index,
            } => object
                .get_source(name)
                .map(|property| property.type_)
                .or(*string_index),
            Self::Synthetic(properties) => {
                let name = EscapedName::source(name);
                properties
                    .iter()
                    .find(|(property, _)| property == &name)
                    .map(|(_, type_)| *type_)
            }
            Self::FiniteRecord(object) => {
                let name = EscapedName::source(name);
                object
                    .properties
                    .iter()
                    .find(|property| property.name == name)
                    .map(|property| property.type_)
            }
            Self::BroadRecord(object) => Some(object.value_type),
        }
    }
}

/// Prepares the contextual decisions for one cached variable initializer.
///
/// All target and union validation completes before source object publication.
#[cfg(test)]
pub(super) fn prepare_expression_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
    contextual_type: TypeId,
) -> Result<PreparedExpression, SourceCheckError> {
    prepare_expression_context_worker(
        store,
        host,
        None,
        &HashMap::new(),
        expression,
        contextual_type,
    )
    .map(|(prepared, _)| prepared)
}

/// Prepares a contextual expression with authoritative generic-global identities.
pub(super) fn prepare_expression_context_with_global_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
    contextual_type: TypeId,
) -> Result<PreparedExpression, SourceCheckError> {
    prepare_expression_context_and_tuple_contexts_with_global_types(
        store,
        host,
        global_types,
        current_flow_types,
        expression,
        contextual_type,
    )
    .map(|(prepared, _)| prepared)
}

/// Retains the contextual tuple type for each array literal in the prepared tree.
pub(super) fn prepare_expression_context_and_tuple_contexts_with_global_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
    contextual_type: TypeId,
) -> Result<(PreparedExpression, HashMap<NodeRef, TypeId>), SourceCheckError> {
    prepare_expression_context_worker(
        store,
        host,
        Some(global_types),
        current_flow_types,
        expression,
        contextual_type,
    )
}

fn prepare_expression_context_worker(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
    contextual_type: TypeId,
) -> Result<(PreparedExpression, HashMap<NodeRef, TypeId>), SourceCheckError> {
    if matches!(&expression.kind, PlannedExpressionKind::Object { .. }) {
        preflight_contextual_type_graph(
            store,
            host,
            global_types,
            contextual_type,
            &mut HashSet::new(),
            &mut HashSet::new(),
        )?;
    }
    let mut state = ExpressionPreparationState {
        current_flow_types,
        tuple_contexts: HashMap::new(),
    };
    let prepared = prepare_expression(
        store,
        host,
        global_types,
        &mut state,
        expression,
        Some(contextual_type),
        ExpressionLocation::Cached,
    )?;
    Ok((prepared, state.tuple_contexts))
}

/// Prepares a non-contextual expression with authoritative generic-global identities.
pub(super) fn prepare_expression_without_context_with_global_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
) -> Result<PreparedExpression, SourceCheckError> {
    prepare_expression_without_context_worker(
        store,
        host,
        Some(global_types),
        current_flow_types,
        expression,
    )
}

fn prepare_expression_without_context_worker(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
    expression: &PlannedExpression,
) -> Result<PreparedExpression, SourceCheckError> {
    let mut state = ExpressionPreparationState {
        current_flow_types,
        tuple_contexts: HashMap::new(),
    };
    prepare_expression(
        store,
        host,
        global_types,
        &mut state,
        expression,
        None,
        ExpressionLocation::Cached,
    )
}

/// Validates every type reachable from the contextual target before source
/// alignment can publish an object literal. `visiting` admits recursive
/// declared objects, while `validated` prevents repeated work in shared
/// subgraphs.
fn preflight_contextual_type_graph(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    contextual_type: TypeId,
    validated: &mut HashSet<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), SourceCheckError> {
    if validated.contains(&contextual_type) {
        return Ok(());
    }
    if !visiting.insert(contextual_type) {
        return Ok(());
    }
    let result = (|| {
        let flags = store
            .type_payload(contextual_type)
            .map(TypeRecord::flags)
            .ok_or(RelationUnavailable::Type(contextual_type))?;
        if flags.intersects(TypeFlags::UNION) {
            validate_contextual_union(store, global_types, contextual_type)?;
            let TypeData::Union(union) = store
                .type_payload(contextual_type)
                .ok_or(RelationUnavailable::Type(contextual_type))?
                .data()
            else {
                return Err(RelationUnavailable::MalformedUnion(contextual_type).into());
            };
            for constituent in union.union.types.clone() {
                preflight_contextual_type_graph(
                    store,
                    host,
                    global_types,
                    constituent,
                    validated,
                    visiting,
                )?;
            }
            return Ok(());
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let contextual = resolve_contextual_property_object(store, host, contextual_type)?
                .ok_or(RelationUnavailable::UnsupportedStructuredType(
                    contextual_type,
                ))?;
            for property_type in contextual.property_types() {
                preflight_contextual_type_graph(
                    store,
                    host,
                    global_types,
                    property_type,
                    validated,
                    visiting,
                )?;
            }
            return Ok(());
        }
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            for placeholder in validate_contextual_template(store, contextual_type)? {
                preflight_contextual_type_graph(
                    store,
                    host,
                    global_types,
                    placeholder,
                    validated,
                    visiting,
                )?;
            }
            return Ok(());
        }
        if flags.intersects(TypeFlags::OBJECT) {
            match validate_stored_single_callable(store, contextual_type) {
                StoredSingleCallableValidation::Valid { .. } => return Ok(()),
                StoredSingleCallableValidation::Pending { .. } => {
                    return Err(RelationUnavailable::UnresolvedFunctionType(contextual_type).into());
                }
                StoredSingleCallableValidation::Malformed { .. } => {
                    return Err(RelationUnavailable::MalformedFunctionType(contextual_type).into());
                }
                StoredSingleCallableValidation::NotCallable => {}
            }
            if let Some(global_types) = global_types
                && let Some(element_type) =
                    store.canonical_array_element_type(global_types, contextual_type)?
            {
                return preflight_contextual_type_graph(
                    store,
                    host,
                    Some(global_types),
                    element_type,
                    validated,
                    visiting,
                );
            }
            let tuple_elements = store
                .canonical_tuple_shape(contextual_type)
                .map_err(|_| RelationUnavailable::InvalidStructuredMembers(contextual_type))?
                .map(|shape| shape.element_types().to_vec());
            if let Some(tuple_elements) = tuple_elements {
                for element in tuple_elements {
                    preflight_contextual_type_graph(
                        store,
                        host,
                        global_types,
                        element,
                        validated,
                        visiting,
                    )?;
                }
                return Ok(());
            }
            let contextual = resolve_contextual_property_object(store, host, contextual_type)?
                .ok_or(RelationUnavailable::UnsupportedStructuredType(
                    contextual_type,
                ))?;
            for property_type in contextual.property_types() {
                preflight_contextual_type_graph(
                    store,
                    host,
                    global_types,
                    property_type,
                    validated,
                    visiting,
                )?;
            }
            return Ok(());
        }
        if flags == TypeFlags::TYPE_PARAMETER
            && cached_ordinary_type_parameter_owner(store, contextual_type).is_some()
        {
            return validate_contextual_union(store, global_types, contextual_type);
        }
        if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
            return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
        }
        validate_contextual_union(store, global_types, contextual_type)
    })();
    assert!(visiting.remove(&contextual_type));
    if result.is_ok() {
        validated.insert(contextual_type);
    }
    result
}

fn prepare_expression(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    state: &mut ExpressionPreparationState<'_>,
    expression: &PlannedExpression,
    contextual_type: Option<TypeId>,
    location: ExpressionLocation,
) -> Result<PreparedExpression, SourceCheckError> {
    let prepared = match &expression.kind {
        PlannedExpressionKind::ClassReceiver(_) => PreparedExpression::ClassReceiver,
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::RegularExpression(_) => {
            PreparedExpression::Literal(LiteralTreatment::Identity)
        }
        PlannedExpressionKind::Identifier(read)
            if read.kind == PlannedIdentifierReadKind::Unresolved =>
        {
            PreparedExpression::Identifier(LiteralTreatment::Identity)
        }
        PlannedExpressionKind::Identifier(read) => {
            PreparedExpression::Identifier(identifier_treatment(
                store,
                global_types,
                *state.current_flow_types.get(&read.value_symbol).ok_or(
                    SourceCheckError::Variable(VariableInvariant::MissingCurrentFlowType(
                        read.value_symbol,
                    )),
                )?,
                contextual_type,
                location,
            )?)
        }
        PlannedExpressionKind::TypeImportValueUse(_) => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(expression.node),
            ));
        }
        PlannedExpressionKind::String(_) => PreparedExpression::Literal(literal_treatment(
            store,
            global_types,
            LiteralKind::String,
            contextual_type,
            location,
        )?),
        PlannedExpressionKind::Template(_) => PreparedExpression::Template(contextual_type),
        PlannedExpressionKind::Number { .. } => PreparedExpression::Literal(literal_treatment(
            store,
            global_types,
            LiteralKind::Number,
            contextual_type,
            location,
        )?),
        PlannedExpressionKind::BigInt { .. } => PreparedExpression::Literal(literal_treatment(
            store,
            global_types,
            LiteralKind::BigInt,
            contextual_type,
            location,
        )?),
        PlannedExpressionKind::Boolean(_) => PreparedExpression::Literal(literal_treatment(
            store,
            global_types,
            LiteralKind::Boolean,
            contextual_type,
            location,
        )?),
        PlannedExpressionKind::Parenthesized(inner) => {
            PreparedExpression::Parenthesized(Box::new(prepare_expression(
                store,
                host,
                global_types,
                state,
                inner,
                contextual_type,
                location,
            )?))
        }
        PlannedExpressionKind::Assertion { .. } => PreparedExpression::Assertion(contextual_type),
        PlannedExpressionKind::Conditional(_) => PreparedExpression::Conditional {
            contextual_type,
            mutable_result: location == ExpressionLocation::Mutable,
        },
        PlannedExpressionKind::Array(elements) => {
            let element_context = match (global_types, contextual_type) {
                (Some(global_types), Some(contextual_type)) => {
                    store.canonical_array_element_type(global_types, contextual_type)?
                }
                _ => None,
            };
            let tuple_context = contextual_type
                .map(|contextual_type| {
                    store
                        .canonical_tuple_shape(contextual_type)
                        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(contextual_type))
                        .map(|shape| {
                            shape.map(|shape| {
                                (
                                    shape.element_types().to_vec(),
                                    shape.element_infos().last().is_some_and(|info| {
                                        info.flags().contains(super::signatures::ElementFlags::REST)
                                    }),
                                )
                            })
                        })
                })
                .transpose()?
                .flatten();
            if tuple_context.is_some()
                && let Some(contextual_type) = contextual_type
            {
                state
                    .tuple_contexts
                    .insert(expression.node, contextual_type);
            }
            let mut prepared = Vec::with_capacity(elements.len());
            for (index, element) in elements.iter().enumerate() {
                if let Some(spread) = expression.array_spread_node(index) {
                    let PlannedExpressionKind::Identifier(read) = &element.kind else {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Syntax {
                                node: spread,
                                kind: SyntaxKind::SpreadElement,
                                role: SourceSyntaxRole::ArrayElement,
                            },
                        ));
                    };
                    let source_type = *state.current_flow_types.get(&read.value_symbol).ok_or(
                        SourceCheckError::Variable(VariableInvariant::MissingCurrentFlowType(
                            read.value_symbol,
                        )),
                    )?;
                    let array = global_types
                        .map(|global_types| {
                            store.canonical_array_element_type(global_types, source_type)
                        })
                        .transpose()?
                        .flatten();
                    let tuple = store
                        .canonical_tuple_shape(source_type)
                        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(source_type))?;
                    if array.is_none() && tuple.is_none()
                        || tuple.as_ref().is_some_and(|shape| {
                            shape
                                .combined_flags()
                                .intersects(super::signatures::ElementFlags::VARIABLE)
                        })
                        || tuple_context.is_some()
                            && (array.is_some() || index != elements.len() - 1)
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Syntax {
                                node: spread,
                                kind: SyntaxKind::SpreadElement,
                                role: SourceSyntaxRole::ArrayElement,
                            },
                        ));
                    }
                    prepared.push(prepare_expression(
                        store,
                        host,
                        global_types,
                        state,
                        element,
                        None,
                        ExpressionLocation::Cached,
                    )?);
                    continue;
                }
                let positional_context = tuple_context.as_ref().and_then(|(types, has_rest)| {
                    types
                        .get(index)
                        .copied()
                        .or_else(|| has_rest.then(|| types.last().copied()).flatten())
                });
                prepared.push(prepare_expression(
                    store,
                    host,
                    global_types,
                    state,
                    element,
                    positional_context.or(element_context),
                    ExpressionLocation::Mutable,
                )?);
            }
            PreparedExpression::Array(prepared)
        }
        PlannedExpressionKind::Object { plan, properties } => {
            debug_assert_eq!(plan.properties.len(), properties.len());
            let contextual = contextual_objects(
                store,
                host,
                global_types,
                contextual_type,
                &plan.properties,
                properties,
                state.current_flow_types,
            )?;
            let mut prepared = Vec::with_capacity(properties.len());
            for (property, expression) in plan.properties.iter().zip(properties) {
                let name = property
                    .name
                    .as_utf8()
                    .ok_or(RelationUnavailable::UnsupportedProperty(property.symbol))?;
                let property_context = contextual_property_type(
                    store,
                    &contextual,
                    name,
                    expression,
                    state.current_flow_types,
                )?;
                prepared.push(prepare_expression(
                    store,
                    host,
                    global_types,
                    state,
                    expression,
                    property_context,
                    if property.readonly {
                        ExpressionLocation::Readonly
                    } else {
                        ExpressionLocation::Mutable
                    },
                )?);
            }
            PreparedExpression::Object(prepared)
        }
        PlannedExpressionKind::Property(property) => {
            PreparedExpression::Property(Box::new(prepare_expression(
                store,
                host,
                global_types,
                state,
                &property.receiver,
                None,
                ExpressionLocation::Cached,
            )?))
        }
        PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::SuperCall(_)
        | PlannedExpressionKind::ImportCall(_) => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(expression.node),
            ));
        }
        PlannedExpressionKind::Arrow(_) => PreparedExpression::Arrow(
            contextual_type
                .map(|type_| contextual_arrow_initializer_type(store, global_types, type_))
                .transpose()?,
        ),
        PlannedExpressionKind::New(_) => {
            return Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                expression.node,
            )));
        }
        PlannedExpressionKind::Binary(_)
        | PlannedExpressionKind::Logical(_)
        | PlannedExpressionKind::Element(_) => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node: expression.node,
                    kind: ts_ast::SyntaxKind::BinaryExpression,
                    role: super::source::SourceSyntaxRole::BinaryExpression,
                },
            ));
        }
    };
    Ok(prepared)
}

fn contextual_objects(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    contextual_type: Option<TypeId>,
    source_properties: &[PlannedProperty],
    expressions: &[PlannedExpression],
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
) -> Result<Vec<ContextualPropertyObject>, SourceCheckError> {
    let Some(contextual_type) = contextual_type else {
        return Ok(Vec::new());
    };
    let flags = store
        .type_payload(contextual_type)
        .map(TypeRecord::flags)
        .ok_or(RelationUnavailable::Type(contextual_type))?;
    if flags.intersects(TypeFlags::UNION) {
        validate_contextual_union(store, global_types, contextual_type)?;
        let TypeData::Union(union) = store
            .type_payload(contextual_type)
            .ok_or(RelationUnavailable::Type(contextual_type))?
            .data()
        else {
            return Err(RelationUnavailable::MalformedUnion(contextual_type).into());
        };
        let constituents = union.union.types.clone();
        let mut candidates = Vec::new();
        for constituent in constituents {
            let flags = store
                .type_payload(constituent)
                .map(TypeRecord::flags)
                .ok_or(RelationUnavailable::Type(constituent))?;
            if flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION) {
                let candidate = resolve_contextual_property_object(store, host, constituent)?
                    .ok_or(RelationUnavailable::UnsupportedStructuredType(constituent))?;
                candidates.push(candidate);
            } else if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
                return Err(RelationUnavailable::UnsupportedStructuredType(constituent).into());
            }
        }
        for (property, expression) in source_properties.iter().zip(expressions) {
            let name = property
                .name
                .as_utf8()
                .ok_or(RelationUnavailable::UnsupportedProperty(property.symbol))?;
            let discriminates = candidates.iter().try_fold(false, |found, candidate| {
                if found {
                    return Ok::<_, SourceCheckError>(true);
                }
                let Some(target) = candidate.get_source(name) else {
                    return Ok(false);
                };
                Ok(
                    source_matches_discriminant(store, expression, target, current_flow_types)?
                        .is_some(),
                )
            })?;
            if !discriminates {
                continue;
            }
            let retained = candidates
                .iter()
                .filter_map(|candidate| {
                    let Some(target) = candidate.get_source(name) else {
                        return Some(Ok(candidate.clone()));
                    };
                    match source_matches_discriminant(store, expression, target, current_flow_types)
                    {
                        Ok(Some(false)) => None,
                        Ok(_) => Some(Ok(candidate.clone())),
                        Err(error) => Some(Err(error)),
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            if !retained.is_empty() {
                candidates = retained;
            }
        }
        return Ok(candidates);
    }
    if flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION) {
        return resolve_contextual_property_object(store, host, contextual_type)
            .map(|object| object.into_iter().collect());
    }
    if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
        return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
    }
    Ok(Vec::new())
}

fn resolve_contextual_property_object(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    contextual_type: TypeId,
) -> Result<Option<ContextualPropertyObject>, SourceCheckError> {
    if store
        .type_payload(contextual_type)
        .is_some_and(|record| record.flags().intersects(TypeFlags::INTERSECTION))
    {
        return intersection_contextual_property_projection(store, host, contextual_type)
            .map(ContextualPropertyObject::Synthetic)
            .map(Some);
    }

    let mapped_key = match store.type_payload(contextual_type).map(TypeRecord::data) {
        Some(TypeData::Mapped(mapped)) => mapped.constraint_type,
        _ => None,
    };
    let is_mapped = matches!(
        store.type_payload(contextual_type).map(TypeRecord::data),
        Some(TypeData::Mapped(_))
    );
    if is_mapped {
        let broad_string_key = store
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| mapped_key == Some(bootstrap.string_type));
        if broad_string_key {
            return resolve_broad_record_mapped_projection(store, contextual_type)
                .map(ContextualPropertyObject::BroadRecord)
                .map(Some)
                .map_err(Into::into);
        }
        return store
            .resolve_finite_record_mapped_projection(contextual_type)
            .map(ContextualPropertyObject::FiniteRecord)
            .map(Some)
            .map_err(|error| contextual_mapped_error(contextual_type, error));
    }
    if let Some(properties) = synthetic_contextual_property_projection(store, contextual_type)? {
        return Ok(Some(ContextualPropertyObject::Synthetic(properties)));
    }
    let Some(object) = store.resolved_declared_property_object(host, contextual_type)? else {
        return Ok(None);
    };
    let string = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .string_type;
    let string_index = store
        .type_payload(contextual_type)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.index_infos.as_deref())
        .unwrap_or_default()
        .iter()
        .find_map(|index| {
            store
                .index_info(*index)
                .filter(|index| index.key_type() == string)
                .map(super::signatures::IndexInfo::value_type)
        });
    Ok(Some(ContextualPropertyObject::Declared {
        object,
        string_index,
    }))
}

/// Retains informative constituent properties instead of an `any`-merged value.
fn intersection_contextual_property_projection(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    contextual_type: TypeId,
) -> Result<Vec<(EscapedName, TypeId)>, SourceCheckError> {
    let projection = match store.validate_intersection_type(contextual_type) {
        Ok(projection) => projection,
        Err(_)
            if store
                .validate_deferred_intersection_type(contextual_type)
                .is_ok() =>
        {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(contextual_type).into());
        }
        Err(_) => return Err(RelationUnavailable::MalformedIntersection(contextual_type).into()),
    };
    if projection.reduced_to_never {
        return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
    }
    let record = store
        .type_payload(contextual_type)
        .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
    let TypeData::Intersection(intersection) = record.data() else {
        return Err(RelationUnavailable::MalformedIntersection(contextual_type).into());
    };
    if intersection.intersection.structured.signatures.is_some()
        || intersection.intersection.structured.call_signature_count != 0
    {
        return Err(RelationUnavailable::StructuredSignatures(contextual_type).into());
    }

    let mut constituents = Vec::with_capacity(projection.types.len());
    for constituent in projection.types {
        let flags = store
            .type_payload(constituent)
            .map(TypeRecord::flags)
            .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
        if !flags.intersects(TypeFlags::OBJECT) {
            return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
        }
        let object = resolve_contextual_property_object(store, host, constituent)?
            .ok_or(RelationUnavailable::UnsupportedStructuredType(constituent))?;
        constituents.push(object);
    }

    let mut properties = Vec::with_capacity(projection.properties.len());
    for symbol in projection.properties {
        let name = store
            .symbol(symbol)
            .map(|record| record.name().to_owned())
            .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
        let source_name = name
            .as_utf8()
            .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
        let merged = store
            .resolved_own_property(contextual_type, source_name)?
            .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
        if merged.symbol != symbol {
            return Err(RelationUnavailable::MalformedIntersection(contextual_type).into());
        }

        let mut found = false;
        let mut informative = None;
        for constituent in &constituents {
            let Some(type_) = constituent.get_source(source_name) else {
                continue;
            };
            found = true;
            let flags = store
                .type_payload(type_)
                .map(TypeRecord::flags)
                .ok_or(RelationUnavailable::MalformedIntersection(contextual_type))?;
            if flags.intersects(TypeFlags::ANY | TypeFlags::UNKNOWN) {
                continue;
            }
            match informative {
                None => informative = Some(type_),
                Some(previous) if previous == type_ => {}
                Some(_) => {
                    return Err(
                        RelationUnavailable::UnsupportedStructuredType(contextual_type).into(),
                    );
                }
            }
        }
        if !found {
            return Err(RelationUnavailable::MalformedIntersection(contextual_type).into());
        }
        properties.push((name, informative.unwrap_or(merged.type_)));
    }
    Ok(properties)
}

/// Projects declaration-free `JSDoc` properties through the relater's full validation.
fn synthetic_contextual_property_projection(
    store: &mut CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> Result<Option<Vec<(EscapedName, TypeId)>>, RelationUnavailable> {
    let properties = store.type_payload(contextual_type).and_then(|record| {
        if record.symbol().is_some() {
            return None;
        }
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        let properties = object.structured.properties.as_deref()?;
        properties
            .iter()
            .any(|property| {
                store
                    .symbol(*property)
                    .is_some_and(|record| record.flags().contains(SymbolFlags::TRANSIENT))
            })
            .then(|| properties.to_vec())
    });
    let Some(properties) = properties else {
        return Ok(None);
    };

    let mut projection = Vec::with_capacity(properties.len());
    for symbol in properties {
        let name = store
            .symbol(symbol)
            .map(|record| record.name().to_owned())
            .ok_or(RelationUnavailable::InvalidStructuredMembers(
                contextual_type,
            ))?;
        let source_name = name
            .as_utf8()
            .ok_or(RelationUnavailable::InvalidStructuredMembers(
                contextual_type,
            ))?;
        let property = store
            .resolved_own_property(contextual_type, source_name)?
            .ok_or(RelationUnavailable::InvalidStructuredMembers(
                contextual_type,
            ))?;
        if property.symbol != symbol {
            return Err(RelationUnavailable::InvalidStructuredMembers(
                contextual_type,
            ));
        }
        projection.push((name, property.type_));
    }
    Ok(Some(projection))
}

/// Validates an already-published canonical `Record<string, T>` index.
pub(super) fn broad_record_mapped_projection(
    store: &CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> Result<BroadRecordMappedProjection, RelationUnavailable> {
    let (key_type, value_type) = validate_broad_record_mapped_identity(store, contextual_type)?;
    let record = store.type_payload(contextual_type).ok_or(
        RelationUnavailable::InvalidStructuredMembers(contextual_type),
    )?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ));
    };
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return Err(RelationUnavailable::UnresolvedStructuredMembers(
            contextual_type,
        ));
    }
    let structured = &mapped.object.structured;
    let members = structured
        .members
        .ok_or(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ))?;
    let [index] = structured.index_infos.as_deref().unwrap_or_default() else {
        return Err(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ));
    };
    let index = *index;
    let index_info =
        store
            .index_info(index)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(
                contextual_type,
            ))?;
    if store
        .symbol_table(members)
        .is_none_or(|table| !table.is_empty())
        || structured.properties.is_some()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || index_info.key_type() != key_type
        || index_info.value_type() != value_type
        || index_info.is_readonly()
        || index_info.declaration().is_some()
        || index_info.index_symbol().is_some()
        || !index_info.components().is_empty()
    {
        return Err(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ));
    }
    Ok(BroadRecordMappedProjection {
        type_: contextual_type,
        members,
        index,
        value_type,
    })
}

/// Publishes one authenticated broad `Record` index before contextual lookup.
pub(super) fn resolve_broad_record_mapped_projection(
    store: &mut CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> Result<BroadRecordMappedProjection, RelationUnavailable> {
    validate_broad_record_mapped_identity(store, contextual_type)?;
    if store.type_payload(contextual_type).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    }) {
        return broad_record_mapped_projection(store, contextual_type);
    }
    let members = store
        .resolve_mapped_type_members(contextual_type, MappedTypeModifiers::NONE)
        .map_err(|error| broad_record_mapped_error(contextual_type, error))?;
    if members.type_id() != contextual_type || !members.properties().is_empty() {
        return Err(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ));
    }
    let projection = broad_record_mapped_projection(store, contextual_type)?;
    if projection.members != members.members() {
        return Err(RelationUnavailable::InvalidStructuredMembers(
            contextual_type,
        ));
    }
    Ok(projection)
}

fn validate_broad_record_mapped_identity(
    store: &CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> Result<(TypeId, TypeId), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(contextual_type);
    let record = store.type_payload(contextual_type).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(RelationUnavailable::UnsupportedStructuredType(
            contextual_type,
        ));
    };
    let identity = record
        .alias()
        .and_then(|identity| store.type_alias(identity))
        .ok_or_else(invalid)?;
    let owner = identity.symbol().ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let owner_arguments = identity.type_arguments().ok_or_else(invalid)?;
    let alias = if owner_record.name().as_utf8() == Some("Record") {
        owner
    } else {
        store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Record"))
            .and_then(|alias| store.get_merged_symbol(alias))
            .ok_or_else(invalid)?
    };
    let declared = mapped.object.target.ok_or_else(invalid)?;
    let key_type = mapped.constraint_type.ok_or_else(invalid)?;
    let value_type = mapped.template_type.ok_or_else(invalid)?;
    let string_type = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .string_type;
    if key_type != string_type {
        return Err(RelationUnavailable::UnsupportedStructuredType(
            contextual_type,
        ));
    }
    let parameters = store
        .type_alias_links(alias)
        .and_then(|links| links.type_parameters.as_deref())
        .ok_or_else(invalid)?;
    store
        .validate_record_mapped_alias_instantiation(
            alias,
            declared,
            parameters,
            &[key_type, value_type],
            contextual_type,
        )
        .map_err(|error| broad_record_mapped_error(contextual_type, error))?;
    if owner != alias {
        let owner_links = store.type_alias_links(owner).ok_or_else(invalid)?;
        if owner_links.declared_type != Some(contextual_type)
            || owner_links.type_parameters.as_deref().unwrap_or_default() != owner_arguments
        {
            return Err(invalid());
        }
    }
    Ok((key_type, value_type))
}

fn broad_record_mapped_error(
    contextual_type: TypeId,
    error: MappedTypeError,
) -> RelationUnavailable {
    match error {
        MappedTypeError::BootstrapUninitialized => RelationUnavailable::MissingBootstrap,
        MappedTypeError::UnsupportedSource(_)
        | MappedTypeError::UnsupportedConstraint(_)
        | MappedTypeError::UnsupportedNameType(_)
        | MappedTypeError::UnsupportedTemplate(_)
        | MappedTypeError::RecursiveMembers(_)
        | MappedTypeError::InstantiationDepthLimit { .. }
        | MappedTypeError::InstantiationCountLimit { .. }
        | MappedTypeError::CrossProductTooLarge { .. } => {
            RelationUnavailable::UnsupportedStructuredType(contextual_type)
        }
        MappedTypeError::Capacity => RelationUnavailable::UnionValidationCapacity(contextual_type),
        MappedTypeError::Declared(_)
        | MappedTypeError::InvalidDeclaration(_)
        | MappedTypeError::InvalidSymbol(_)
        | MappedTypeError::InvalidTypeParameter(_)
        | MappedTypeError::InvalidMappedType(_)
        | MappedTypeError::InvalidModifiers
        | MappedTypeError::InvalidSource(_)
        | MappedTypeError::InvalidCachedMembers(_)
        | MappedTypeError::InvalidCachedProperty(_)
        | MappedTypeError::CircularProperty(_) => {
            RelationUnavailable::InvalidStructuredMembers(contextual_type)
        }
    }
}

fn contextual_mapped_error(contextual_type: TypeId, error: MappedTypeError) -> SourceCheckError {
    match error {
        MappedTypeError::Declared(error) => error.into(),
        MappedTypeError::BootstrapUninitialized => RelationUnavailable::MissingBootstrap.into(),
        MappedTypeError::UnsupportedSource(_)
        | MappedTypeError::UnsupportedConstraint(_)
        | MappedTypeError::UnsupportedNameType(_)
        | MappedTypeError::UnsupportedTemplate(_)
        | MappedTypeError::RecursiveMembers(_)
        | MappedTypeError::InstantiationDepthLimit { .. }
        | MappedTypeError::InstantiationCountLimit { .. }
        | MappedTypeError::CrossProductTooLarge { .. } => {
            RelationUnavailable::UnsupportedStructuredType(contextual_type).into()
        }
        MappedTypeError::Capacity => {
            RelationUnavailable::UnionValidationCapacity(contextual_type).into()
        }
        MappedTypeError::InvalidDeclaration(_)
        | MappedTypeError::InvalidSymbol(_)
        | MappedTypeError::InvalidTypeParameter(_)
        | MappedTypeError::InvalidMappedType(_)
        | MappedTypeError::InvalidModifiers
        | MappedTypeError::InvalidSource(_)
        | MappedTypeError::InvalidCachedMembers(_)
        | MappedTypeError::InvalidCachedProperty(_)
        | MappedTypeError::CircularProperty(_) => {
            RelationUnavailable::InvalidStructuredMembers(contextual_type).into()
        }
    }
}

fn contextual_property_type(
    store: &CanonicalTypeMapperStore,
    candidates: &[ContextualPropertyObject],
    name: &str,
    expression: &PlannedExpression,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
) -> Result<Option<TypeId>, SourceCheckError> {
    let mut fallback = None;
    for candidate in candidates {
        let Some(property_type) = candidate.get_source(name) else {
            continue;
        };
        fallback.get_or_insert(property_type);
        if source_matches_discriminant(store, expression, property_type, current_flow_types)?
            == Some(true)
        {
            return Ok(Some(property_type));
        }
    }
    Ok(fallback)
}

fn source_matches_discriminant(
    store: &CanonicalTypeMapperStore,
    expression: &PlannedExpression,
    target: TypeId,
    current_flow_types: &HashMap<SemanticSymbolId, TypeId>,
) -> Result<Option<bool>, SourceCheckError> {
    let target_record = store
        .type_payload(target)
        .ok_or(RelationUnavailable::Type(target))?;
    if let TypeData::Union(union) = target_record.data() {
        let mut contains_discriminant = false;
        for constituent in &union.union.types {
            match source_matches_discriminant(store, expression, *constituent, current_flow_types)?
            {
                Some(true) => return Ok(Some(true)),
                Some(false) => contains_discriminant = true,
                None => {}
            }
        }
        return Ok(contains_discriminant.then_some(false));
    }
    let result = match (&expression.kind, target_record.data()) {
        (PlannedExpressionKind::Parenthesized(inner), _) => {
            return source_matches_discriminant(store, inner, target, current_flow_types);
        }
        (PlannedExpressionKind::String(actual), TypeData::Literal(literal)) => {
            let LiteralValue::String(expected) = &literal.value else {
                return Ok(None);
            };
            Some(actual == expected)
        }
        (PlannedExpressionKind::Number { value, .. }, TypeData::Literal(literal)) => {
            let LiteralValue::Number(expected) = &literal.value else {
                return Ok(None);
            };
            Some(value == expected)
        }
        (PlannedExpressionKind::BigInt { value, .. }, TypeData::Literal(literal)) => {
            let LiteralValue::BigInt(expected) = &literal.value else {
                return Ok(None);
            };
            Some(value == expected)
        }
        (PlannedExpressionKind::Boolean(actual), TypeData::Literal(literal)) => {
            let LiteralValue::Boolean(expected) = &literal.value else {
                return Ok(None);
            };
            Some(actual == expected)
        }
        (PlannedExpressionKind::Null, _) if target_record.flags() == TypeFlags::NULL => Some(true),
        (PlannedExpressionKind::GlobalUndefined, _)
            if target_record.flags() == TypeFlags::UNDEFINED =>
        {
            Some(true)
        }
        (PlannedExpressionKind::Identifier(read), TypeData::Literal(_)) => current_flow_types
            .get(&read.value_symbol)
            .map(|actual| *actual == target),
        _ => None,
    };
    Ok(result)
}

pub(super) fn mutable_literal_treatment(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    contextual_type: Option<TypeId>,
) -> Result<LiteralTreatment, SourceCheckError> {
    if contextual_type.is_none() {
        return Ok(LiteralTreatment::WidenedPrimitive);
    }
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let mut flags = record.flags();
    if let TypeData::Union(union) = record.data() {
        let constituents = union.union.types.clone();
        validate_contextual_union(store, global_types, type_)?;
        for constituent in constituents {
            flags |= store
                .type_payload(constituent)
                .ok_or(RelationUnavailable::Type(constituent))?
                .flags();
        }
    }
    // A literal context selects one treatment for the whole expression union.
    for (kind, flag) in [
        (LiteralKind::String, TypeFlags::STRING_LITERAL),
        (LiteralKind::Number, TypeFlags::NUMBER_LITERAL),
        (LiteralKind::BigInt, TypeFlags::BIG_INT_LITERAL),
        (LiteralKind::Boolean, TypeFlags::BOOLEAN_LITERAL),
    ] {
        if flags.intersects(flag)
            && is_literal_of_contextual_type(
                store,
                global_types,
                kind,
                contextual_type,
                &mut HashSet::new(),
            )?
        {
            return Ok(LiteralTreatment::Regular);
        }
    }
    Ok(LiteralTreatment::WidenedPrimitive)
}

fn literal_treatment(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    kind: LiteralKind,
    contextual_type: Option<TypeId>,
    location: ExpressionLocation,
) -> Result<LiteralTreatment, SourceCheckError> {
    if location == ExpressionLocation::Cached {
        return Ok(LiteralTreatment::Fresh);
    }
    if location == ExpressionLocation::Readonly {
        return Ok(LiteralTreatment::Regular);
    }
    if is_literal_of_contextual_type(
        store,
        global_types,
        kind,
        contextual_type,
        &mut HashSet::new(),
    )? {
        Ok(LiteralTreatment::Regular)
    } else {
        Ok(LiteralTreatment::WidenedPrimitive)
    }
}

fn identifier_treatment(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    contextual_type: Option<TypeId>,
    location: ExpressionLocation,
) -> Result<LiteralTreatment, SourceCheckError> {
    if location == ExpressionLocation::Cached {
        return Ok(LiteralTreatment::Identity);
    }
    let record = store
        .type_payload(type_)
        .ok_or(RelationUnavailable::Type(type_))?;
    let TypeData::Literal(literal) = record.data() else {
        return Ok(LiteralTreatment::Identity);
    };
    store.validate_union_constituent(type_)?;
    if literal.fresh_type != Some(type_) || literal.regular_type == type_ {
        return Ok(LiteralTreatment::Identity);
    }
    let kind = if record.flags().intersects(TypeFlags::STRING_LITERAL) {
        LiteralKind::String
    } else if record.flags().intersects(TypeFlags::NUMBER_LITERAL) {
        LiteralKind::Number
    } else if record.flags().intersects(TypeFlags::BIG_INT_LITERAL) {
        LiteralKind::BigInt
    } else if record.flags().intersects(TypeFlags::BOOLEAN_LITERAL) {
        LiteralKind::Boolean
    } else {
        return Err(RelationUnavailable::UnsupportedStructuredType(type_).into());
    };
    if is_literal_of_contextual_type(
        store,
        global_types,
        kind,
        contextual_type,
        &mut HashSet::new(),
    )? {
        Ok(LiteralTreatment::Regular)
    } else {
        Ok(LiteralTreatment::WidenedPrimitive)
    }
}

fn is_literal_of_contextual_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    kind: LiteralKind,
    contextual_type: Option<TypeId>,
    visited: &mut HashSet<TypeId>,
) -> Result<bool, SourceCheckError> {
    let Some(contextual_type) = contextual_type else {
        return Ok(false);
    };
    if !visited.insert(contextual_type) {
        return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
    }
    let result = (|| {
        let record = store
            .type_payload(contextual_type)
            .ok_or(RelationUnavailable::Type(contextual_type))?;
        let flags = record.flags();
        if flags.intersects(TypeFlags::UNION | TypeFlags::INTERSECTION) {
            let types = if flags.intersects(TypeFlags::UNION) {
                validate_contextual_union(store, global_types, contextual_type)?;
                let TypeData::Union(union) = record.data() else {
                    return Err(RelationUnavailable::MalformedUnion(contextual_type).into());
                };
                union.union.types.clone()
            } else {
                match store.validate_intersection_type(contextual_type) {
                    Ok(projection) => projection.types,
                    Err(_)
                        if store
                            .validate_deferred_intersection_type(contextual_type)
                            .is_ok() =>
                    {
                        return Err(RelationUnavailable::UnresolvedStructuredMembers(
                            contextual_type,
                        )
                        .into());
                    }
                    Err(_) => {
                        return Err(
                            RelationUnavailable::MalformedIntersection(contextual_type).into()
                        );
                    }
                }
            };
            for constituent in types {
                if is_literal_of_contextual_type(
                    store,
                    global_types,
                    kind,
                    Some(constituent),
                    visited,
                )? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        if flags.intersects(TypeFlags::OBJECT) {
            return Ok(false);
        }
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            validate_contextual_template(store, contextual_type)?;
            return Ok(kind == LiteralKind::String);
        }
        if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
            return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
        }
        if flags.intersects(TypeFlags::FRESHABLE) {
            store.validate_union_constituent(contextual_type)?;
        }
        Ok(match kind {
            LiteralKind::String => flags.intersects(TypeFlags::STRING_LITERAL),
            LiteralKind::Number => flags.intersects(TypeFlags::NUMBER_LITERAL),
            LiteralKind::BigInt => flags.intersects(TypeFlags::BIG_INT_LITERAL),
            LiteralKind::Boolean => flags.intersects(TypeFlags::BOOLEAN_LITERAL),
        })
    })();
    assert!(visited.remove(&contextual_type));
    result
}

fn validate_contextual_template(
    store: &CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> Result<Vec<TypeId>, SourceCheckError> {
    let record = store
        .type_payload(contextual_type)
        .ok_or(RelationUnavailable::Type(contextual_type))?;
    let TypeData::TemplateLiteral(template) = record.data() else {
        return Err(RelationUnavailable::MalformedStructuredType(contextual_type).into());
    };
    if record.flags() != TypeFlags::TEMPLATE_LITERAL
        || template.types.is_empty()
        || template.texts.len() != template.types.len() + 1
        || store
            .cached_resolved_template_literal_type(&template.texts, &template.types)
            .map_err(|_| RelationUnavailable::MalformedStructuredType(contextual_type))?
            != Some(contextual_type)
    {
        return Err(RelationUnavailable::MalformedStructuredType(contextual_type).into());
    }
    Ok(template.types.clone())
}

fn validate_contextual_union(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    union: TypeId,
) -> Result<(), SourceCheckError> {
    let result = match global_types {
        Some(global_types) => {
            store.validate_union_constituent_with_global_types(global_types, union)
        }
        None => store.validate_union_constituent(union),
    };
    result
        .map_err(|error| super::relater::union_validation_unavailable(union, error))
        .map_err(Into::into)
}

/// Initialized arrows receive their callable context without its optional undefined branch.
fn contextual_arrow_initializer_type(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    contextual_type: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Ok(contextual_type);
    };
    if !bootstrap.options.strict_null_checks {
        return Ok(contextual_type);
    }
    let Some(TypeData::Union(union)) = store.type_payload(contextual_type).map(TypeRecord::data)
    else {
        return Ok(contextual_type);
    };
    let [first, second] = union.union.types.as_slice() else {
        return Ok(contextual_type);
    };
    let callable = if *first == bootstrap.undefined_type {
        *second
    } else if *second == bootstrap.undefined_type {
        *first
    } else {
        return Ok(contextual_type);
    };

    validate_contextual_union(store, global_types, contextual_type)?;
    match validate_stored_single_callable(store, callable) {
        StoredSingleCallableValidation::Valid { .. } => Ok(callable),
        StoredSingleCallableValidation::Pending { .. } => {
            Err(RelationUnavailable::UnresolvedFunctionType(callable).into())
        }
        StoredSingleCallableValidation::Malformed { .. } => {
            Err(RelationUnavailable::MalformedFunctionType(callable).into())
        }
        StoredSingleCallableValidation::NotCallable => Ok(contextual_type),
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        CheckFlags, EscapedName, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        jsdoc::{plan_javascript_source_jsdoc, resolve_planned_jsdoc_type},
        signatures::ElementFlags,
        tuple_types::CanonicalTupleTypeRequest,
        types::ObjectFlags,
    };

    fn initialized() -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn mapped_record_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/contextual-record.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn mapped_record_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
        parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "value").then(|| {
                    (
                        NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap()),
                        NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap()),
                    )
                })
            })
            .expect("the fixture contains one annotated object named value")
    }

    fn generic_object_return_nodes(
        parsed: &ParseResult,
        file: FileId,
    ) -> (NodeRef, NodeRef, NodeRef) {
        let find = |kind| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap()
        };
        (
            find(SyntaxKind::TypeParameter),
            find(SyntaxKind::TypeLiteral),
            find(SyntaxKind::ObjectLiteralExpression),
        )
    }

    fn mapped_record_expression(
        parsed: &ParseResult,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        object: NodeRef,
    ) -> PlannedExpression {
        let plan = super::super::object_members::plan_object_literal(store, host, object).unwrap();
        let properties = plan
            .properties
            .iter()
            .map(|property| {
                let NodeData::StringLiteral(value) =
                    &parsed.arena.get(property.type_node.node).unwrap().data
                else {
                    panic!("mapped object fixture properties have string initializers")
                };
                PlannedExpression::new(
                    property.type_node,
                    PlannedExpressionKind::String(value.text.clone()),
                )
            })
            .collect();
        PlannedExpression::new(object, PlannedExpressionKind::Object { plan, properties })
    }

    fn intersection_object_expression(
        parsed: &ParseResult,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        object: NodeRef,
    ) -> PlannedExpression {
        let plan = super::super::object_members::plan_object_literal(store, host, object).unwrap();
        let properties = plan
            .properties
            .iter()
            .map(|property| {
                let record = parsed.arena.get(property.type_node.node).unwrap();
                let kind = match &record.data {
                    NodeData::StringLiteral(literal) => {
                        PlannedExpressionKind::String(literal.text.clone())
                    }
                    NodeData::NumericLiteral(literal) => PlannedExpressionKind::Number {
                        value: ts_jsnum::Number::new(literal.text.parse().unwrap()),
                        unary_operand: None,
                    },
                    _ => panic!("intersection fixtures use string or numeric properties"),
                };
                PlannedExpression::new(property.type_node, kind)
            })
            .collect();
        PlannedExpression::new(object, PlannedExpressionKind::Object { plan, properties })
    }

    fn contextual_function_types(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
    ) -> Vec<(NodeRef, TypeId)> {
        parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                if record.kind != SyntaxKind::FunctionType {
                    return None;
                }
                let node = NodeRef::new(parsed.arena.id(), file, node);
                store
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    .map(|type_| (node, type_))
            })
            .collect()
    }

    #[test]
    fn synthetic_jsdoc_objects_provide_context_and_reject_forged_properties() {
        let parsed = parse_source_file("const value: { age: number } = { age: 1 };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_068);
        let mut context = mapped_record_context(&parsed, file);
        let (_, object) = mapped_record_nodes(&parsed, file);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let plan =
            super::super::object_members::plan_object_literal(context.store(), &host, object)
                .unwrap();
        let [age] = plan.properties.as_slice() else {
            panic!("the source object has one age property")
        };
        let expression = PlannedExpression::new(
            object,
            PlannedExpressionKind::Object {
                properties: vec![PlannedExpression::new(
                    age.type_node,
                    PlannedExpressionKind::Number {
                        value: ts_jsnum::Number::new(1.0),
                        unary_operand: None,
                    },
                )],
                plan,
            },
        );

        let javascript = parse_javascript_source_file(concat!(
            "/** @typedef {{ age: number, label?: string }} Person */\n",
            "/** @type {Person} */\n",
            "var person;",
        ));
        assert!(
            javascript.diagnostics.is_empty(),
            "{:?}",
            javascript.diagnostics
        );
        let source = NodeRef::new(
            javascript.arena.id(),
            FileId::new(1_069),
            javascript.source_file,
        );
        let jsdoc = plan_javascript_source_jsdoc(&javascript.arena, source).unwrap();
        let [declaration] = jsdoc.declarations() else {
            panic!("the JavaScript fixture has one annotated declaration")
        };
        let annotation = declaration.type_().unwrap();
        let globals = context.global_types().clone();
        let options = context.options();
        let target =
            resolve_planned_jsdoc_type(context.store_mut_for_test(), &globals, options, annotation)
                .unwrap();
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        let projected = resolve_contextual_property_object(store, &host, target)
            .unwrap()
            .unwrap();
        assert_eq!(projected.property_types(), vec![number, string]);
        assert_eq!(projected.get_source("age"), Some(number));
        assert_eq!(projected.get_source("label"), Some(string));
        assert_eq!(projected.get_source("missing"), None);
        assert_eq!(
            prepare_expression_context_with_global_types(
                store,
                &host,
                &globals,
                &HashMap::new(),
                &expression,
                target,
            ),
            Ok(PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
            ])),
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(store.type_node_links(object).is_none());

        let property = match store.type_payload(target).unwrap().data() {
            TypeData::Object(object) => object.structured.properties.as_ref().unwrap()[0],
            _ => panic!("a JSDoc structural type must be an anonymous object"),
        };
        let original_flags = store.symbol(property).unwrap().flags();
        let original_checks = store.symbol(property).unwrap().check_flags();
        let original_links = store.value_symbol_links(property).unwrap().clone();

        for forged_links in [false, true] {
            if forged_links {
                let mut poisoned = original_links.clone();
                poisoned.target = Some(property);
                assert!(store.set_value_symbol_links(property, poisoned));
            } else {
                assert!(store.set_symbol_flags(
                    property,
                    original_flags.without(SymbolFlags::TRANSIENT),
                    original_checks,
                ));
            }
            let poisoned = (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            );

            assert_eq!(
                prepare_expression_context_with_global_types(
                    store,
                    &host,
                    &globals,
                    &HashMap::new(),
                    &expression,
                    target,
                ),
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::InvalidStructuredMembers(target),
                )),
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                ),
                poisoned,
            );
            assert!(store.type_node_links(object).is_none());

            if forged_links {
                assert!(store.set_value_symbol_links(property, original_links.clone()));
            } else {
                assert!(store.set_symbol_flags(property, original_flags, original_checks));
            }
        }

        assert!(
            prepare_expression_context_with_global_types(
                store,
                &host,
                &globals,
                &HashMap::new(),
                &expression,
                target,
            )
            .is_ok()
        );
    }

    #[test]
    fn contextual_intersections_preserve_non_any_literals_in_either_constituent_order() {
        for (index, source) in [
            "const value: { item: any } & { item: 'edge' } = { item: 'edge' };",
            "const value: { item: 'edge' } & { item: any } = { item: 'edge' };",
            "const value: { item: any } & { item: 1 } = { item: 1 };",
            "const value: { item: 1 } & { item: any } = { item: 1 };",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(9_420 + u32::try_from(index).unwrap());
            let mut context = mapped_record_context(&parsed, file);
            let (annotation, object) = mapped_record_nodes(&parsed, file);
            let target = context.get_type_from_type_node(annotation).unwrap();
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let expression =
                intersection_object_expression(&parsed, context.store(), &host, object);
            let globals = context.global_types().clone();
            let (any, expected) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                let expected = if source.contains("'edge'") {
                    bootstrap.cached_string_literal_type("edge").unwrap()
                } else {
                    bootstrap
                        .cached_number_literal_type(ts_jsnum::Number::new(1.0))
                        .unwrap()
                };
                (bootstrap.any_type, expected)
            };
            let store = context.store_mut_for_test();
            let merged = store.validate_intersection_type(target).unwrap();
            let [property] = merged.properties.as_slice() else {
                panic!("the target intersection must have one merged property")
            };
            assert_eq!(
                store
                    .value_symbol_links(*property)
                    .and_then(|links| links.resolved_type),
                Some(any),
            );
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            );

            for _ in 0..2 {
                let contextual = resolve_contextual_property_object(store, &host, target)
                    .unwrap()
                    .unwrap();
                assert_eq!(contextual.get_source("item"), Some(expected));
                assert_eq!(
                    prepare_expression_context_with_global_types(
                        store,
                        &host,
                        &globals,
                        &HashMap::new(),
                        &expression,
                        target,
                    ),
                    Ok(PreparedExpression::Object(vec![
                        PreparedExpression::Literal(LiteralTreatment::Regular),
                    ])),
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                    ),
                    before,
                );
                assert!(store.type_node_links(object).is_none());
            }
        }
    }

    #[test]
    fn contextual_intersections_reject_deferred_targets_without_writes() {
        let deferred_source =
            parse_source_file("const value: { item: any } & { item: 'edge' } = { item: 'edge' };");
        assert!(
            deferred_source.diagnostics.is_empty(),
            "{:?}",
            deferred_source.diagnostics
        );
        let file = FileId::new(9_424);
        let mut context = mapped_record_context(&deferred_source, file);
        let (annotation, object) = mapped_record_nodes(&deferred_source, file);
        let NodeData::IntersectionTypeNode(intersection) =
            &deferred_source.arena.get(annotation.node).unwrap().data
        else {
            panic!("expected a source intersection annotation")
        };
        let [left, right] = intersection.types.nodes.as_slice() else {
            panic!("expected two source intersection constituents")
        };
        let left = context
            .get_type_from_type_node(NodeRef::new(deferred_source.arena.id(), file, *left))
            .unwrap();
        let right = context
            .get_type_from_type_node(NodeRef::new(deferred_source.arena.id(), file, *right))
            .unwrap();
        let deferred = context
            .store_mut_for_test()
            .canonical_deferred_intersection_type(&[left, right], None)
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&deferred_source.arena, &bound)]).unwrap();
        let expression =
            intersection_object_expression(&deferred_source, context.store(), &host, object);
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            prepare_expression_context_with_global_types(
                store,
                &host,
                &globals,
                &HashMap::new(),
                &expression,
                deferred,
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnresolvedStructuredMembers(deferred),
            )),
        );
        assert_eq!(
            is_literal_of_contextual_type(
                store,
                Some(&globals),
                LiteralKind::String,
                Some(deferred),
                &mut HashSet::new(),
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnresolvedStructuredMembers(deferred),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn contextual_intersections_reject_ambiguous_properties_without_writes() {
        let ambiguous_source =
            parse_source_file("const value: { item: number } & { item: 1 } = { item: 1 };");
        assert!(
            ambiguous_source.diagnostics.is_empty(),
            "{:?}",
            ambiguous_source.diagnostics
        );
        let file = FileId::new(9_425);
        let mut context = mapped_record_context(&ambiguous_source, file);
        let (annotation, object) = mapped_record_nodes(&ambiguous_source, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&ambiguous_source.arena, &bound)]).unwrap();
        let expression =
            intersection_object_expression(&ambiguous_source, context.store(), &host, object);
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            prepare_expression_context_with_global_types(
                store,
                &host,
                &globals,
                &HashMap::new(),
                &expression,
                target,
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnsupportedStructuredType(target),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn contextual_intersections_reject_forged_cached_properties_without_writes() {
        let parsed =
            parse_source_file("const value: { item: any } & { item: 'edge' } = { item: 'edge' };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(9_426);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = intersection_object_expression(&parsed, context.store(), &host, object);
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let property = store.validate_intersection_type(target).unwrap().properties[0];
        let original_flags = store.symbol(property).unwrap().flags();
        let original_checks = store.symbol(property).unwrap().check_flags();
        let original_links = store.value_symbol_links(property).unwrap().clone();

        for poison_links in [false, true] {
            if poison_links {
                let mut poisoned = original_links.clone();
                poisoned.target = Some(property);
                assert!(store.set_value_symbol_links(property, poisoned));
            } else {
                assert!(store.set_symbol_flags(
                    property,
                    original_flags.without(SymbolFlags::TRANSIENT),
                    original_checks,
                ));
            }
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            );

            assert_eq!(
                prepare_expression_context_with_global_types(
                    store,
                    &host,
                    &globals,
                    &HashMap::new(),
                    &expression,
                    target,
                ),
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::MalformedIntersection(target),
                )),
            );
            assert_eq!(
                is_literal_of_contextual_type(
                    store,
                    Some(&globals),
                    LiteralKind::String,
                    Some(target),
                    &mut HashSet::new(),
                ),
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::MalformedIntersection(target),
                )),
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                ),
                before,
            );
            assert!(store.type_node_links(object).is_none());

            if poison_links {
                assert!(store.set_value_symbol_links(property, original_links.clone()));
            } else {
                assert!(store.set_symbol_flags(property, original_flags, original_checks));
            }
        }

        assert_eq!(
            prepare_expression_context_with_global_types(
                store,
                &host,
                &globals,
                &HashMap::new(),
                &expression,
                target,
            ),
            Ok(PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::Regular),
            ])),
        );
    }

    #[test]
    fn contextual_object_graph_preserves_source_type_parameter_leaves() {
        let parsed =
            parse_source_file("function f<T>(value: T): { value: T } { return { value }; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(965);
        let mut context = mapped_record_context(&parsed, file);
        let (declaration, annotation, object) = generic_object_return_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let symbol = bound.symbol(declaration).unwrap();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let store = context.store_mut_for_test();
        let parameter = store
            .declared_type_links(symbol)
            .unwrap()
            .declared_type
            .unwrap();
        assert_eq!(
            cached_ordinary_type_parameter_owner(store, parameter),
            Some(symbol),
        );
        let TypeData::TypeParameter(original) = store.type_payload(parameter).unwrap().data()
        else {
            panic!("the source query must retain the declared type parameter")
        };
        let original = original.clone();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        for _ in 0..2 {
            for global_types in [None, Some(&globals)] {
                preflight_contextual_type_graph(
                    store,
                    &host,
                    global_types,
                    target,
                    &mut HashSet::new(),
                    &mut HashSet::new(),
                )
                .unwrap();
                let contextual = resolve_contextual_property_object(store, &host, target)
                    .unwrap()
                    .unwrap();
                assert_eq!(contextual.get_source("value"), Some(parameter));
                assert_eq!(
                    identifier_treatment(
                        store,
                        global_types,
                        parameter,
                        Some(parameter),
                        ExpressionLocation::Mutable,
                    ),
                    Ok(LiteralTreatment::Identity),
                );
                assert!(matches!(
                    store.type_payload(parameter).map(TypeRecord::data),
                    Some(TypeData::TypeParameter(data)) if data == &original
                ));
                assert_eq!(
                    cached_ordinary_type_parameter_owner(store, parameter),
                    Some(symbol),
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                    ),
                    before,
                );
                assert!(store.type_node_links(object).is_none());
            }
        }
    }

    #[test]
    fn contextual_type_parameter_leaves_reject_changed_owners_and_caches() {
        #[derive(Clone, Copy, Debug)]
        enum Poison {
            DeclaredCache,
            ValueDeclaration,
            Declaration,
            InstantiationTarget,
        }

        for poison in [
            Poison::DeclaredCache,
            Poison::ValueDeclaration,
            Poison::Declaration,
            Poison::InstantiationTarget,
        ] {
            let parsed =
                parse_source_file("function f<T>(value: T): { value: T } { return { value }; }");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(965);
            let mut context = mapped_record_context(&parsed, file);
            let (declaration, annotation, object) = generic_object_return_nodes(&parsed, file);
            let target = context.get_type_from_type_node(annotation).unwrap();
            let bound = context.file(file).unwrap().1.clone();
            let symbol = bound.symbol(declaration).unwrap();
            let globals = context.global_types().clone();
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let store = context.store_mut_for_test();
            let parameter = store
                .declared_type_links(symbol)
                .unwrap()
                .declared_type
                .unwrap();
            preflight_contextual_type_graph(
                store,
                &host,
                Some(&globals),
                target,
                &mut HashSet::new(),
                &mut HashSet::new(),
            )
            .unwrap();

            let expected = match poison {
                Poison::DeclaredCache => {
                    let mut links = store.declared_type_links(symbol).unwrap().clone();
                    links.declared_type = Some(store.intrinsic_bootstrap().unwrap().number_type);
                    assert!(store.set_declared_type_links(symbol, links));
                    RelationUnavailable::UnsupportedStructuredType(parameter)
                }
                Poison::ValueDeclaration => {
                    assert!(store.set_symbol_declarations(
                        symbol,
                        Some(vec![declaration]),
                        Some(declaration),
                    ));
                    RelationUnavailable::UnsupportedUnionConstituent(parameter)
                }
                Poison::Declaration => {
                    assert!(store.set_symbol_declarations(symbol, Some(vec![object]), None));
                    RelationUnavailable::UnsupportedUnionConstituent(parameter)
                }
                Poison::InstantiationTarget => {
                    let TypeData::TypeParameter(data) =
                        store.type_payload(parameter).unwrap().data()
                    else {
                        panic!("the source query must retain the declared type parameter")
                    };
                    let data = data.clone();
                    assert!(store.set_type_parameter_resolution(
                        parameter,
                        data.constraint,
                        Some(parameter),
                        data.mapper,
                        data.resolved_default_type,
                    ));
                    RelationUnavailable::UnsupportedStructuredType(parameter)
                }
            };
            assert_eq!(
                cached_ordinary_type_parameter_owner(store, parameter),
                match poison {
                    Poison::ValueDeclaration | Poison::Declaration => Some(symbol),
                    Poison::DeclaredCache | Poison::InstantiationTarget => None,
                },
            );
            let poisoned_links = store.declared_type_links(symbol).unwrap().clone();
            let TypeData::TypeParameter(poisoned_data) =
                store.type_payload(parameter).unwrap().data()
            else {
                panic!("poisoning must not replace the type parameter payload")
            };
            let poisoned_data = poisoned_data.clone();
            let poisoned_checks = store.symbol(symbol).unwrap().check_flags();
            let poisoned_value_declaration = store.symbol(symbol).unwrap().value_declaration();
            let poisoned_declarations = store
                .symbol(symbol)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            );

            for global_types in [None, Some(&globals), None, Some(&globals)] {
                assert_eq!(
                    preflight_contextual_type_graph(
                        store,
                        &host,
                        global_types,
                        parameter,
                        &mut HashSet::new(),
                        &mut HashSet::new(),
                    ),
                    Err(SourceCheckError::RelationUnavailable(expected)),
                    "{poison:?}",
                );
                assert!(
                    preflight_contextual_type_graph(
                        store,
                        &host,
                        global_types,
                        target,
                        &mut HashSet::new(),
                        &mut HashSet::new(),
                    )
                    .is_err(),
                    "{poison:?}",
                );
                assert_eq!(store.declared_type_links(symbol), Some(&poisoned_links));
                assert!(matches!(
                    store.type_payload(parameter).map(TypeRecord::data),
                    Some(TypeData::TypeParameter(data)) if data == &poisoned_data
                ));
                assert_eq!(store.symbol(symbol).unwrap().check_flags(), poisoned_checks);
                assert_eq!(
                    store.symbol(symbol).unwrap().value_declaration(),
                    poisoned_value_declaration,
                );
                assert_eq!(
                    store.symbol(symbol).unwrap().declarations(),
                    Some(poisoned_declarations.as_slice()),
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                    ),
                    before,
                    "{poison:?}",
                );
                assert!(store.type_node_links(object).is_none());
            }
        }
    }

    #[test]
    fn contextual_object_graph_accepts_authenticated_nested_callable_leaves() {
        let parsed = parse_source_file(concat!(
            "interface Target { ",
            "callback: (value: string) => string; ",
            "nested: { handler: (value: number) => number }; ",
            "} ",
            "const value: Target = { ",
            "callback: (value: string) => value, ",
            "nested: { handler: (value: number) => value }, ",
            "};",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_065);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let callables = contextual_function_types(&parsed, file, context.store());
        assert_eq!(callables.len(), 2);
        assert!(callables.iter().all(|(_, callable)| {
            matches!(
                validate_stored_single_callable(context.store(), *callable),
                StoredSingleCallableValidation::Valid { .. }
            )
        }));
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        for _ in 0..2 {
            preflight_contextual_type_graph(
                store,
                &host,
                None,
                target,
                &mut HashSet::new(),
                &mut HashSet::new(),
            )
            .unwrap();
            let root = resolve_contextual_property_object(store, &host, target)
                .unwrap()
                .unwrap();
            assert_eq!(root.get_source("callback"), Some(callables[0].1));
            let nested = root.get_source("nested").unwrap();
            let nested = resolve_contextual_property_object(store, &host, nested)
                .unwrap()
                .unwrap();
            assert_eq!(nested.get_source("handler"), Some(callables[1].1));
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                ),
                before,
            );
            assert!(store.type_node_links(object).is_none());
        }
    }

    #[test]
    fn nullable_callback_properties_preserve_contextual_arrow_parameter_types() {
        let parsed = parse_source_file(concat!(
            "interface Target { callback: ((value: number) => number) | undefined; } ",
            "const value: Target = { callback: value => value };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_081);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/contextual-undefined.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                no_implicit_any: true,
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();

        let function = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let callable = context.get_type_from_type_node(function).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, undefined) = (bootstrap.number_type, bootstrap.undefined_type);
        let contextual = context
            .store_mut_for_test()
            .literal_union_type(&[callable, undefined], None)
            .unwrap();

        let StoredSingleCallableValidation::Valid {
            callable: signature,
            ..
        } = validate_stored_single_callable(context.store(), callable)
        else {
            panic!("the contextual union must contain one authenticated callable")
        };
        assert_eq!(signature.parameters.as_slice(), &[number]);

        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );

        for _ in 0..2 {
            assert_eq!(
                contextual_arrow_initializer_type(
                    context.store(),
                    Some(context.global_types()),
                    contextual,
                ),
                Ok(callable),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().relation_state_snapshot(),
                ),
                before,
            );
        }

        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nullable_scalar_contexts_do_not_become_callable_contexts() {
        let mut store = initialized();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, undefined) = (bootstrap.number_type, bootstrap.undefined_type);
        let contextual = store
            .literal_union_type(&[number, undefined], None)
            .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        assert_eq!(
            contextual_arrow_initializer_type(&store, None, contextual),
            Ok(contextual),
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
    }

    #[test]
    fn malformed_contextual_callable_leaf_fails_before_object_publication() {
        let parsed = parse_source_file(concat!(
            "interface Target { callback: (value: string) => string; } ",
            "const value: Target = { callback: (value: string) => value };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_066);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let [(declaration, callable)] = contextual_function_types(&parsed, file, context.store())
            .try_into()
            .expect("the target declares one authenticated function type");
        let store = context.store_mut_for_test();
        let signature = store
            .signature_links(declaration)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let [parameter] = store.signature(signature).unwrap().parameters() else {
            panic!("the contextual signature has one parameter")
        };
        let parameter = *parameter;
        let original = store.value_symbol_links(parameter).unwrap().clone();
        let mut poisoned = original.clone();
        poisoned.resolved_type = Some(store.intrinsic_bootstrap().unwrap().number_type);
        assert!(store.set_value_symbol_links(parameter, poisoned));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        assert_eq!(
            preflight_contextual_type_graph(
                store,
                &host,
                None,
                callable,
                &mut HashSet::new(),
                &mut HashSet::new(),
            ),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::MalformedFunctionType(callable),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(store.type_node_links(object).is_none());

        assert!(store.set_value_symbol_links(parameter, original));
        preflight_contextual_type_graph(
            store,
            &host,
            None,
            target,
            &mut HashSet::new(),
            &mut HashSet::new(),
        )
        .unwrap();
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn finite_record_context_resolves_actual_computed_properties_and_replays_warm() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "type Keys = 'second' | 'first'; ",
            "const value: Record<Keys, 'ready'> = ",
            "{ ['second']: 'ready', ['first']: 'ready' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_062);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();

        let PlannedExpressionKind::Object { plan, .. } = &expression.kind else {
            panic!("the contextual fixture retains an object literal")
        };
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_utf8().unwrap())
                .collect::<Vec<_>>(),
            ["second", "first"],
        );

        assert!(matches!(
            store.type_payload(target).map(TypeRecord::data),
            Some(TypeData::Mapped(mapped)) if mapped.object.structured.members.is_none()
        ));
        assert!(store.type_node_links(object).is_none());

        let prepared = prepare_expression_context(store, &host, &expression, target).unwrap();
        assert_eq!(
            prepared,
            PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::Regular),
                PreparedExpression::Literal(LiteralTreatment::Regular),
            ]),
        );

        let projection = store.finite_record_mapped_projection(target).unwrap();
        assert_eq!(
            projection
                .properties
                .iter()
                .map(|property| property.name.as_utf8().unwrap())
                .collect::<Vec<_>>(),
            ["first", "second"],
        );
        for property in &projection.properties {
            let symbol = store.symbol(property.symbol).unwrap();
            assert_eq!(
                symbol.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            );
            assert!(symbol.check_flags().contains(CheckFlags::MAPPED));
            assert!(symbol.declarations().is_none());
            assert_eq!(
                store
                    .value_symbol_links(property.symbol)
                    .and_then(|links| links.resolved_type),
                Some(property.type_),
            );
        }
        assert!(store.type_node_links(object).is_none());

        let warm = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
            projection.clone(),
        );
        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Ok(prepared),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                store.finite_record_mapped_projection(target).unwrap(),
            ),
            warm,
        );
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn finite_record_context_rejects_poisoned_property_types_without_source_writes() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "const value: Record<'first' | 'second', string> = ",
            "{ first: 'one', second: 'two' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_063);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();
        let projection = store
            .resolve_finite_record_mapped_projection(target)
            .unwrap();
        let property = projection.properties.last().unwrap().symbol;
        let original = store.value_symbol_links(property).unwrap().clone();
        let mut poisoned = original.clone();
        poisoned.resolved_type = Some(store.intrinsic_bootstrap().unwrap().number_type);
        assert!(store.set_value_symbol_links(property, poisoned));

        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(target),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(store.type_node_links(object).is_none());

        assert!(store.set_value_symbol_links(property, original));
        assert!(prepare_expression_context(store, &host, &expression, target).is_ok());
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn declared_string_indexes_supply_context_to_every_object_property() {
        let parsed = parse_source_file(concat!(
            "type Dictionary = { [key: string]: 'ready' }; ",
            "const value: Dictionary = { first: 'ready', second: 'ready' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_071);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();

        let prepared = prepare_expression_context(store, &host, &expression, target).unwrap();
        assert_eq!(
            prepared,
            PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::Regular),
                PreparedExpression::Literal(LiteralTreatment::Regular),
            ]),
        );
        let contextual = resolve_contextual_property_object(store, &host, target)
            .unwrap()
            .unwrap();
        let expected = contextual.get_source("first").unwrap();
        assert_eq!(contextual.get_source("second"), Some(expected));
        assert_eq!(contextual.get_source("later"), Some(expected));
        assert!(matches!(
            store.type_payload(expected).map(TypeRecord::data),
            Some(TypeData::Literal(literal))
                if matches!(&literal.value, LiteralValue::String(value) if value == "ready")
        ));

        let warm = (
            store.type_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Ok(prepared),
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            warm,
        );
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn broad_record_context_uses_the_canonical_string_index_and_replays_warm() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "const value: Record<string, string> = { first: 'one', second: 'two' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_064);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();

        assert_eq!(
            broad_record_mapped_projection(store, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(target)),
        );
        let prepared = prepare_expression_context(store, &host, &expression, target).unwrap();
        assert_eq!(
            prepared,
            PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
                PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
            ]),
        );
        let projection = broad_record_mapped_projection(store, target).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let index = store.index_info(projection.index).unwrap();
        assert_eq!(projection.type_, target);
        assert_eq!(projection.value_type, string);
        assert_eq!(index.key_type(), string);
        assert_eq!(index.value_type(), string);
        assert!(!index.is_readonly());
        assert!(index.declaration().is_none());
        assert!(index.index_symbol().is_none());
        assert!(index.components().is_empty());
        assert!(store.symbol_table(projection.members).unwrap().is_empty());
        assert!(store.type_node_links(object).is_none());

        let warm = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
            projection,
        );
        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Ok(prepared),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                broad_record_mapped_projection(store, target).unwrap(),
            ),
            warm,
        );
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn broad_record_literal_value_context_preserves_each_property_literal() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "const value: Record<string, 'ready'> = ",
            "{ first: 'ready', second: 'ready' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_067);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();

        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Ok(PreparedExpression::Object(vec![
                PreparedExpression::Literal(LiteralTreatment::Regular),
                PreparedExpression::Literal(LiteralTreatment::Regular),
            ])),
        );
        let projection = broad_record_mapped_projection(store, target).unwrap();
        assert!(matches!(
            store
                .type_payload(projection.value_type)
                .map(TypeRecord::data),
            Some(TypeData::Literal(literal))
                if matches!(&literal.value, LiteralValue::String(value) if value == "ready")
        ));
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn broad_record_context_rejects_forged_index_metadata_without_source_writes() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "const value: Record<string, string> = { first: 'one' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_068);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();
        let projection = resolve_broad_record_mapped_projection(store, target).unwrap();
        let symbol = store
            .type_payload(target)
            .and_then(TypeRecord::symbol)
            .unwrap();
        assert!(store.set_index_info_symbol(projection.index, Some(symbol)));
        let poisoned = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        assert_eq!(
            broad_record_mapped_projection(store, target),
            Err(RelationUnavailable::InvalidStructuredMembers(target)),
        );
        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::InvalidStructuredMembers(target),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            poisoned,
        );
        assert!(store.type_node_links(object).is_none());

        assert!(store.set_index_info_symbol(projection.index, None));
        assert_eq!(
            broad_record_mapped_projection(store, target),
            Ok(projection)
        );
        assert!(prepare_expression_context(store, &host, &expression, target).is_ok());
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn broad_non_string_record_context_remains_unsupported_without_publication() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "const value: Record<number, string> = { first: 'one' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_069);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, object) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let expression = mapped_record_expression(&parsed, context.store(), &host, object);
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        assert_eq!(
            prepare_expression_context(store, &host, &expression, target),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnsupportedStructuredType(target),
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
        assert!(matches!(
            store.type_payload(target).map(TypeRecord::data),
            Some(TypeData::Mapped(mapped)) if mapped.object.structured.members.is_none()
        ));
        assert!(store.type_node_links(object).is_none());
    }

    #[test]
    fn literal_treatment_matches_pinned_kind_not_value_rules() {
        let mut store = initialized();
        let (string, number, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let expected = store
            .regular_string_literal_type("expected".into())
            .unwrap();
        let literal_or_number = store.literal_union_type(&[expected, number], None).unwrap();
        let primitive_or_number = store.literal_union_type(&[string, number], None).unwrap();

        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::String,
                Some(expected),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::Regular)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::String,
                Some(literal_or_number),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::Regular),
            "a same-kind literal constituent preserves any source value"
        );
        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::String,
                Some(primitive_or_number),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::WidenedPrimitive)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::Boolean,
                Some(boolean),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::Regular),
            "boolean is the canonical union of regular false and true"
        );
        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::String,
                None,
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::WidenedPrimitive)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
                None,
                LiteralKind::String,
                Some(expected),
                ExpressionLocation::Cached,
            ),
            Ok(LiteralTreatment::Fresh),
            "root cached expressions retain freshness"
        );
    }

    #[test]
    fn contextual_union_validation_rejects_objects_and_object_claims_without_writes() {
        let mut store = initialized();
        let (undefined, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let containing_object = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, object])
            .unwrap();
        let claiming_object = store
            .alloc_union_type(
                ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                vec![string, number],
            )
            .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.relation_state_snapshot(),
            store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            validate_contextual_union(&store, None, containing_object),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnsupportedUnionConstituent(object)
            ))
        );
        assert_eq!(
            validate_contextual_union(&store, None, claiming_object),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::MalformedUnion(claiming_object)
            ))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.relation_state_snapshot(),
                store.checker_link_allocated_lengths(),
            ),
            before
        );
    }

    #[test]
    fn cached_scalar_does_not_preflight_an_object_union_context() {
        let mut store = initialized();
        let host = DeclaredTypeHost::new(std::iter::empty::<(
            &ts_ast::NodeArena,
            &ts_binder::BoundFile,
        )>())
        .unwrap();
        let first = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let second = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let object_union = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.relation_state_snapshot(),
            store.checker_link_allocated_lengths(),
        );
        let arena = NodeArena::new();
        let expression = PlannedExpression::new(
            NodeRef::new(arena.id(), FileId::new(0), NodeId::new(0)),
            PlannedExpressionKind::Boolean(true),
        );

        assert_eq!(
            prepare_expression_context(&mut store, &host, &expression, object_union),
            Ok(PreparedExpression::Literal(LiteralTreatment::Fresh))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.relation_state_snapshot(),
                store.checker_link_allocated_lengths(),
            ),
            before
        );
    }

    #[test]
    fn tuple_context_preserves_each_array_element_literal_at_its_position() {
        let mut store = initialized();
        let host = DeclaredTypeHost::new(std::iter::empty::<(
            &ts_ast::NodeArena,
            &ts_binder::BoundFile,
        )>())
        .unwrap();
        let string_literal = store
            .regular_string_literal_type("expected".into())
            .unwrap();
        let number_literal = store
            .regular_number_literal_type(ts_jsnum::Number::new(2.0))
            .unwrap();
        let elements = [string_literal, number_literal];
        let infos = [
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
        ];
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&elements, &infos, false))
            .unwrap();
        let arena = NodeArena::new();
        let root = NodeRef::new(arena.id(), FileId::new(0), NodeId::new(0));
        let expression = PlannedExpression::new(
            root,
            PlannedExpressionKind::Array(vec![
                PlannedExpression::new(
                    NodeRef::new(arena.id(), FileId::new(0), NodeId::new(1)),
                    PlannedExpressionKind::String("actual".into()),
                ),
                PlannedExpression::new(
                    NodeRef::new(arena.id(), FileId::new(0), NodeId::new(2)),
                    PlannedExpressionKind::Number {
                        value: ts_jsnum::Number::new(5.0),
                        unary_operand: None,
                    },
                ),
            ]),
        );

        let expected = PreparedExpression::Array(vec![
            PreparedExpression::Literal(LiteralTreatment::Regular),
            PreparedExpression::Literal(LiteralTreatment::Regular),
        ]);
        let (prepared, tuple_contexts) = prepare_expression_context_worker(
            &mut store,
            &host,
            None,
            &HashMap::new(),
            &expression,
            tuple,
        )
        .unwrap();

        assert_eq!(prepared, expected);
        assert_eq!(tuple_contexts, HashMap::from([(root, tuple)]));
        assert_eq!(
            prepare_expression_context(&mut store, &host, &expression, tuple),
            Ok(expected),
        );
    }

    #[test]
    fn contextual_array_retains_tuple_targets_for_each_nested_array_literal() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "const value: [number, number][] = [[1, 2], [3, 4]];",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_067);
        let mut context = mapped_record_context(&parsed, file);
        let (annotation, root) = mapped_record_nodes(&parsed, file);
        let target = context.get_type_from_type_node(annotation).unwrap();
        let global_types = context.global_types().clone();
        let tuple = context
            .store()
            .canonical_array_element_type(&global_types, target)
            .unwrap()
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let NodeData::ArrayLiteralExpression(outer) = &parsed.arena.get(root.node).unwrap().data
        else {
            panic!("the contextual fixture has an outer array literal")
        };
        let inner_nodes = outer
            .elements
            .nodes
            .iter()
            .copied()
            .map(|node| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        let inner_expressions = inner_nodes
            .iter()
            .copied()
            .map(|node| {
                let NodeData::ArrayLiteralExpression(inner) =
                    &parsed.arena.get(node.node).unwrap().data
                else {
                    panic!("the contextual fixture contains nested array literals")
                };
                let elements = inner
                    .elements
                    .nodes
                    .iter()
                    .copied()
                    .map(|element| {
                        let NodeData::NumericLiteral(literal) =
                            &parsed.arena.get(element).unwrap().data
                        else {
                            panic!("the contextual fixture contains numeric tuple elements")
                        };
                        PlannedExpression::new(
                            NodeRef::new(parsed.arena.id(), file, element),
                            PlannedExpressionKind::Number {
                                value: ts_jsnum::Number::new(literal.text.parse().unwrap()),
                                unary_operand: None,
                            },
                        )
                    })
                    .collect();
                PlannedExpression::new(node, PlannedExpressionKind::Array(elements))
            })
            .collect();
        let expression =
            PlannedExpression::new(root, PlannedExpressionKind::Array(inner_expressions));
        let store = context.store_mut_for_test();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        );

        let (prepared, tuple_contexts) =
            prepare_expression_context_and_tuple_contexts_with_global_types(
                store,
                &host,
                &global_types,
                &HashMap::new(),
                &expression,
                target,
            )
            .unwrap();

        assert_eq!(
            prepared,
            PreparedExpression::Array(vec![
                PreparedExpression::Array(vec![
                    PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
                    PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
                ]),
                PreparedExpression::Array(vec![
                    PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
                    PreparedExpression::Literal(LiteralTreatment::WidenedPrimitive),
                ]),
            ]),
        );
        assert_eq!(tuple_contexts.len(), inner_nodes.len());
        assert!(!tuple_contexts.contains_key(&root));
        assert!(
            inner_nodes
                .iter()
                .all(|node| tuple_contexts.get(node) == Some(&tuple))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            ),
            before,
        );
    }

    #[test]
    fn contextual_object_unions_preserve_literals_and_identify_excess_properties() {
        let parsed = parse_source_file(concat!(
            "type Thing = { str: 'a'; num: 0 } | { str: 'b' } | { num: 1 }; ",
            "const first: Thing = { str: 'a', num: 0 }; ",
            "const second: Thing = { str: 'b', num: 1 }; ",
            "const third: Thing = { num: 1, str: 'b' }; ",
            "type Item = { kind: 'a'; subkind: 0; value: string } ",
            "| { kind: 'a'; subkind: 1; value: number } | { kind: 'b' }; ",
            "const fourth: Item = { subkind: 1, kind: 'b' }; ",
            "const fifth: Item = { kind: 'b', subkind: 1 };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_061);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/contextual-discriminants.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2353, 2353]
        );
        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            counts
        );
        assert_eq!(context.diagnostics().len(), 2);
    }
}
