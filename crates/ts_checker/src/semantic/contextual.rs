//! Contextual typing for the property-only object-literal source slice.
//!
//! The pinned checker obtains an object's contextual type once, looks up each
//! source property by name, and checks property initializers as mutable
//! locations. This module precomputes that dependency tree without publishing
//! checker state, so a malformed target cannot leave a partially constructed
//! source object behind.

use std::collections::HashSet;

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, TypeId,
    source::{PlannedExpression, SourceCheckError},
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
};

/// Whether an expression is checked through the cached root path or as a
/// mutable object-property initializer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpressionLocation {
    Cached,
    Mutable,
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
    Object(Vec<PreparedExpression>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LiteralKind {
    String,
    Number,
    BigInt,
    Boolean,
}

/// Prepares the contextual decisions for one cached variable initializer.
///
/// All target and union validation completes before source object publication.
pub(super) fn prepare_expression_context(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    expression: &PlannedExpression,
    contextual_type: TypeId,
) -> Result<PreparedExpression, SourceCheckError> {
    if matches!(expression, PlannedExpression::Object { .. }) {
        preflight_contextual_type_graph(
            store,
            host,
            contextual_type,
            &mut HashSet::new(),
            &mut HashSet::new(),
        )?;
    }
    prepare_expression(
        store,
        host,
        expression,
        Some(contextual_type),
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
            return validate_contextual_union(store, contextual_type);
        }
        if flags.intersects(TypeFlags::OBJECT) {
            let contextual = store
                .resolved_declared_property_object(host, contextual_type)?
                .ok_or(RelationUnavailable::UnsupportedStructuredType(
                    contextual_type,
                ))?;
            for property in contextual.properties() {
                preflight_contextual_type_graph(store, host, property.type_, validated, visiting)?;
            }
            return Ok(());
        }
        if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
            return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
        }
        validate_contextual_union(store, contextual_type)
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
    expression: &PlannedExpression,
    contextual_type: Option<TypeId>,
    location: ExpressionLocation,
) -> Result<PreparedExpression, SourceCheckError> {
    let prepared = match expression {
        PlannedExpression::Null | PlannedExpression::GlobalUndefined => {
            PreparedExpression::Literal(LiteralTreatment::Identity)
        }
        PlannedExpression::String(_) => PreparedExpression::Literal(literal_treatment(
            store,
            LiteralKind::String,
            contextual_type,
            location,
        )?),
        PlannedExpression::Number { .. } => PreparedExpression::Literal(literal_treatment(
            store,
            LiteralKind::Number,
            contextual_type,
            location,
        )?),
        PlannedExpression::BigInt { .. } => PreparedExpression::Literal(literal_treatment(
            store,
            LiteralKind::BigInt,
            contextual_type,
            location,
        )?),
        PlannedExpression::Boolean(_) => PreparedExpression::Literal(literal_treatment(
            store,
            LiteralKind::Boolean,
            contextual_type,
            location,
        )?),
        PlannedExpression::Object { plan, properties } => {
            debug_assert_eq!(plan.properties.len(), properties.len());
            let contextual = contextual_object(store, host, contextual_type)?;
            let mut prepared = Vec::with_capacity(properties.len());
            for (property, expression) in plan.properties.iter().zip(properties) {
                let property_context = contextual
                    .as_ref()
                    .and_then(|contextual| contextual.get_source(&property.name))
                    .map(|property| property.type_);
                prepared.push(prepare_expression(
                    store,
                    host,
                    expression,
                    property_context,
                    ExpressionLocation::Mutable,
                )?);
            }
            PreparedExpression::Object(prepared)
        }
    };
    Ok(prepared)
}

fn contextual_object(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    contextual_type: Option<TypeId>,
) -> Result<Option<super::relater::ResolvedDeclaredPropertyObject>, SourceCheckError> {
    let Some(contextual_type) = contextual_type else {
        return Ok(None);
    };
    let flags = store
        .type_payload(contextual_type)
        .map(TypeRecord::flags)
        .ok_or(RelationUnavailable::Type(contextual_type))?;
    if flags.intersects(TypeFlags::UNION) {
        // The installed union validator admits only the primitive/literal
        // union domain. An object constituent (or an OBJECT-claiming malformed
        // union) is therefore a typed failure here, before source publication.
        // A valid primitive union has no members to propagate to an object.
        validate_contextual_union(store, contextual_type)?;
        return Ok(None);
    }
    if flags.intersects(TypeFlags::OBJECT) {
        return store
            .resolved_declared_property_object(host, contextual_type)
            .map_err(Into::into);
    }
    if flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
        return Err(RelationUnavailable::UnsupportedStructuredType(contextual_type).into());
    }
    Ok(None)
}

fn literal_treatment(
    store: &mut CanonicalTypeMapperStore,
    kind: LiteralKind,
    contextual_type: Option<TypeId>,
    location: ExpressionLocation,
) -> Result<LiteralTreatment, SourceCheckError> {
    if location == ExpressionLocation::Cached {
        return Ok(LiteralTreatment::Fresh);
    }
    if is_literal_of_contextual_type(store, kind, contextual_type, &mut HashSet::new())? {
        Ok(LiteralTreatment::Regular)
    } else {
        Ok(LiteralTreatment::WidenedPrimitive)
    }
}

fn is_literal_of_contextual_type(
    store: &mut CanonicalTypeMapperStore,
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
        if flags.intersects(TypeFlags::UNION) {
            validate_contextual_union(store, contextual_type)?;
            let TypeData::Union(union) = record.data() else {
                return Err(RelationUnavailable::MalformedUnion(contextual_type).into());
            };
            let types = union.union.types.clone();
            for constituent in types {
                if is_literal_of_contextual_type(store, kind, Some(constituent), visited)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        if flags.intersects(TypeFlags::OBJECT) {
            return Ok(false);
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

fn validate_contextual_union(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
) -> Result<(), SourceCheckError> {
    store
        .validate_union_constituent(union)
        .map_err(|error| super::relater::union_validation_unavailable(union, error))
        .map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{IntrinsicBootstrapOptions, types::ObjectFlags};

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
                LiteralKind::String,
                Some(expected),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::Regular)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
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
                LiteralKind::String,
                Some(primitive_or_number),
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::WidenedPrimitive)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
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
                LiteralKind::String,
                None,
                ExpressionLocation::Mutable,
            ),
            Ok(LiteralTreatment::WidenedPrimitive)
        );
        assert_eq!(
            literal_treatment(
                &mut store,
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
            validate_contextual_union(&store, containing_object),
            Err(SourceCheckError::RelationUnavailable(
                RelationUnavailable::UnsupportedUnionConstituent(object)
            ))
        );
        assert_eq!(
            validate_contextual_union(&store, claiming_object),
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

        assert_eq!(
            prepare_expression_context(
                &mut store,
                &host,
                &PlannedExpression::Boolean(true),
                object_union,
            ),
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
}
