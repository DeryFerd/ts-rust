//! Go's generic object and index flags, without changing type record caches.

use std::collections::{HashMap, HashSet};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    conditional_types::ConditionalBranchSource,
    instantiate::{self, InstantiationError},
    mapped_types::{self, MappedTypeError},
    signatures::ElementFlags,
    template_types::TemplateTypeError,
    tuple_types::TupleTypeError,
    type_records::TypeData,
    types::ObjectFlags,
};

#[derive(Debug)]
pub(super) enum GenericTypeQueryError {
    Source(super::DeclaredTypeError),
    Recovered(TypeId),
    InvalidType(TypeId),
    RecursiveType(TypeId),
    InvalidCachedFlags(TypeId),
    UnresolvedMappedName { mapped: TypeId, name: TypeId, parameter: TypeId, constraint: TypeId },
    Instantiation(InstantiationError),
    Mapped(MappedTypeError),
    Tuple(TupleTypeError),
    Template(TemplateTypeError),
    Union(LiteralTypeCacheError),
}

pub(super) fn generic_type_flags(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<ObjectFlags, GenericTypeQueryError> {
    visit(store, type_, globals, source, &mut HashMap::new(), &mut HashSet::new())
}

fn visit(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
    completed: &mut HashMap<TypeId, ObjectFlags>,
    active: &mut HashSet<TypeId>,
) -> Result<ObjectFlags, GenericTypeQueryError> {
    if let Some(flags) = completed.get(&type_) {
        return Ok(*flags);
    }
    if !active.insert(type_) {
        return Err(GenericTypeQueryError::RecursiveType(type_));
    }
    let result = (|| {
        let invalid = || GenericTypeQueryError::InvalidType(type_);
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        let arrays = CanonicalArrayTargets::from_global_types(globals);
        // The caller proves the selected property type. Read only the headers
        // and operands that determine genericity, not unrelated member values.
        if !store.type_record_header_is_valid(type_) { return Err(invalid()); }
        let object = ObjectFlags::IS_GENERIC_OBJECT_TYPE;
        let index = ObjectFlags::IS_GENERIC_INDEX_TYPE;
        let mut nested = |input| visit(store, input, globals, source, completed, active);
        let composite = matches!(record.data(), TypeData::Union(_) | TypeData::Intersection(_) | TypeData::Substitution(_));
        let flags = match record.data() {
            TypeData::Union(union) => {
                store.validate_union_query_metadata(type_).map_err(GenericTypeQueryError::Union)?;
                let mut flags = ObjectFlags::NONE;
                for input in &union.union.types { flags |= nested(*input)?; }
                flags
            }
            TypeData::Intersection(intersection) => {
                let mut flags = ObjectFlags::NONE;
                for input in &intersection.intersection.types { flags |= nested(*input)?; }
                flags
            }
            TypeData::Substitution(substitution) => nested(substitution.base_type)? | nested(substitution.constraint)?,
            TypeData::TypeParameter(_) | TypeData::IndexedAccess(_) | TypeData::Conditional(_) => object | index,
            TypeData::Index(_) => index,
            TypeData::Mapped(_) => {
                let inputs = mapped_types::generic_mapped_type_inputs(store, type_, Some(arrays), Some((globals, source)))
                    .map_err(GenericTypeQueryError::Mapped)?;
                if nested(inputs.constraint)?.intersects(index) {
                    object
                } else if let Some(name) = inputs.name {
                    let instantiated = instantiate::cached_instantiation_with_vector_and_source(
                        store, name, &[inputs.parameter], &[inputs.constraint], globals, source,
                    ).map_err(GenericTypeQueryError::Instantiation)?
                        .ok_or(GenericTypeQueryError::UnresolvedMappedName {
                            mapped: type_, name, parameter: inputs.parameter, constraint: inputs.constraint,
                        })?;
                    if nested(instantiated)?.intersects(index) { object } else { ObjectFlags::NONE }
                } else {
                    ObjectFlags::NONE
                }
            }
            TypeData::Tuple(_) | TypeData::TypeReference(_) => {
                if store.canonical_tuple_shape(type_).map_err(GenericTypeQueryError::Tuple)?
                    .is_some_and(|shape| shape.combined_flags().intersects(ElementFlags::VARIADIC)) {
                    object
                } else {
                    ObjectFlags::NONE
                }
            }
            TypeData::TemplateLiteral(_) | TypeData::StringMapping(_) => {
                if store.is_template_pattern_literal_type(type_, &mut HashSet::new())
                    .map_err(GenericTypeQueryError::Template)? { ObjectFlags::NONE } else { index }
            }
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_)
            | TypeData::Object(_) | TypeData::Interface(_) | TypeData::InstantiationExpression(_)
            | TypeData::ReverseMapped(_) | TypeData::EvolvingArray(_) => ObjectFlags::NONE,
        };
        if composite {
            let stored = record.object_flags();
            let computed = stored.contains(ObjectFlags::IS_GENERIC_TYPE_COMPUTED);
            let pair = stored & (object | index);
            if computed && pair != flags || !computed && pair != ObjectFlags::NONE {
                return Err(GenericTypeQueryError::InvalidCachedFlags(type_));
            }
        }
        Ok(flags)
    })();
    active.remove(&type_);
    if let Ok(flags) = result { completed.insert(type_, flags); }
    result
}
