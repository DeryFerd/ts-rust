//! Canonical mutable empty-tuple identity.
//!
//! This is the zero-arity dependency-closed slice of pinned
//! `checker.go::createTupleTypeEx`, `getTupleTargetType`, and
//! `createTupleTargetType` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. For zero elements,
//! `createTupleTypeEx` returns the cached tuple target itself. The target owns
//! one synthetic `this` parameter, maps its empty type-argument key back to
//! itself, and declares a synthetic `length` property whose type is literal
//! zero.

use ts_binder::{CheckFlags, EscapedName, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId,
    declared::type_list_key,
    links::ValueSymbolLinks,
    signatures::ElementFlags,
    type_records::{
        ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData, TypeParameterData,
    },
    types::{ObjectFlags, TypeFlags},
};

const LENGTH: &str = "length";

/// A mutable empty-tuple request rejected before publishing a new cache entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EmptyTupleTypeError {
    BootstrapUninitialized,
    InvalidCache(TypeId),
    Capacity,
}

impl std::fmt::Display for EmptyTupleTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("empty tuple type requires intrinsic checker bootstrap")
            }
            Self::InvalidCache(type_) => {
                write!(formatter, "empty tuple cache entry {type_:?} is invalid")
            }
            Self::Capacity => formatter.write_str("empty tuple type capacity was exhausted"),
        }
    }
}

impl std::error::Error for EmptyTupleTypeError {}

impl CanonicalTypeMapperStore {
    /// Creates or reuses the exact mutable `[]` target returned by pinned
    /// `createTupleTypeEx([])`.
    ///
    /// A warm request validates the complete recursive graph before returning
    /// its stable identity. A poisoned or foreign cache entry is never
    /// replaced implicitly.
    pub(super) fn create_canonical_empty_tuple_type(
        &mut self,
    ) -> Result<TypeId, EmptyTupleTypeError> {
        let zero_type = self
            .intrinsic_bootstrap()
            .ok_or(EmptyTupleTypeError::BootstrapUninitialized)?
            .zero_type;
        if let Some(cached) = self.canonical_empty_tuple_type_cache() {
            self.validate_canonical_empty_tuple_type(cached)?;
            return Ok(cached);
        }

        if !self.try_reserve_types(2) || !self.try_reserve_checker_symbol_allocations(1, 1) {
            return Err(EmptyTupleTypeError::Capacity);
        }

        // Preserve the pinned per-arena order: members and `length` are
        // synthesized before the tuple target, whose `this` parameter follows
        // the target allocation.
        let declared_members = self.alloc_symbol_table();
        let length = self.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source(LENGTH),
            CheckFlags::NONE,
        );
        assert!(self.set_value_symbol_links(
            length,
            ValueSymbolLinks {
                resolved_type: Some(zero_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            self.insert_symbol(declared_members, EscapedName::source(LENGTH), length),
            Some(None),
        );

        let metadata = self
            .create_tuple_metadata(Vec::new(), false)
            .expect("empty tuple metadata has no foreign labels");
        let tuple = self
            .alloc_tuple_type(ObjectFlags::REFERENCE | ObjectFlags::TUPLE, None, metadata)
            .expect("preflighted empty tuple shell is valid");
        let this_type = self
            .alloc_type_parameter(None)
            .expect("reference-free empty tuple this type is valid");
        assert!(self.initialize_empty_tuple_target(
            tuple,
            this_type,
            declared_members,
            type_list_key(&[]),
        ));
        assert!(self.publish_canonical_empty_tuple_type(tuple));
        debug_assert_eq!(self.validate_canonical_empty_tuple_type(tuple), Ok(()));
        Ok(tuple)
    }

    /// Validates one identity as the store's exact cached mutable empty tuple.
    ///
    /// This read-only boundary is shared by warm construction and canonical
    /// display, so neither consumer can accidentally accept a tuple-shaped
    /// forgery without cache ownership.
    pub(super) fn validate_canonical_empty_tuple_type(
        &self,
        type_: TypeId,
    ) -> Result<(), EmptyTupleTypeError> {
        let invalid = || EmptyTupleTypeError::InvalidCache(type_);
        if self.canonical_empty_tuple_type_cache() != Some(type_) {
            return Err(invalid());
        }
        let zero_type = self
            .intrinsic_bootstrap()
            .ok_or(EmptyTupleTypeError::BootstrapUninitialized)?
            .zero_type;
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Tuple(tuple) = record.data() else {
            return Err(invalid());
        };
        let interface = &tuple.interface;
        let reference = &interface.reference;
        let object = &reference.object;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::REFERENCE | ObjectFlags::TUPLE)
            || record.symbol().is_some()
            || record.alias().is_some()
            || object.structured != StructuredTypeData::default()
            || object.target != Some(type_)
            || object.mapper.is_some()
            || reference.node.is_some()
            || reference.resolved_type_arguments.as_deref() != Some(&[])
            || interface.outer_type_parameter_count != 0
            || interface.base_types_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.resolved_base_types.is_some()
            || !interface.declared_members_resolved
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
            || !tuple.metadata.element_infos().is_empty()
            || tuple.metadata.min_length() != 0
            || tuple.metadata.fixed_length() != 0
            || tuple.metadata.combined_flags() != ElementFlags::NONE
            || tuple.metadata.is_readonly()
        {
            return Err(invalid());
        }

        let Some([this_type]) = interface.all_type_parameters.as_deref() else {
            return Err(invalid());
        };
        if interface.this_type != Some(*this_type) {
            return Err(invalid());
        }
        let TypeCacheState::Allocated(instantiations) = &object.instantiations else {
            return Err(invalid());
        };
        if instantiations.len() != 1 || instantiations.get(&type_list_key(&[])) != Some(&type_) {
            return Err(invalid());
        }
        let this_record = self.type_payload(*this_type).ok_or_else(invalid)?;
        let TypeData::TypeParameter(this_data) = this_record.data() else {
            return Err(invalid());
        };
        if this_record.flags() != TypeFlags::TYPE_PARAMETER
            || !this_record.object_flags().is_empty()
            || this_record.symbol().is_some()
            || this_record.alias().is_some()
            || this_data
                != &(TypeParameterData {
                    constrained: ConstrainedTypeData::default(),
                    constraint: Some(type_),
                    target: None,
                    mapper: None,
                    is_this_type: true,
                    resolved_default_type: None,
                })
        {
            return Err(invalid());
        }

        let declared_members = interface.declared_members.ok_or_else(invalid)?;
        let members = self.symbol_table(declared_members).ok_or_else(invalid)?;
        let length = members.get_source(LENGTH).ok_or_else(invalid)?;
        if members.len() != 1 {
            return Err(invalid());
        }
        let length_symbol = self.symbol(length).ok_or_else(invalid)?;
        if self.get_merged_symbol(length) != Some(length)
            || length_symbol.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
            || length_symbol.check_flags() != CheckFlags::NONE
            || length_symbol.name().as_bytes() != LENGTH.as_bytes()
            || length_symbol.declarations().is_some()
            || length_symbol.value_declaration().is_some()
            || length_symbol.members().is_some()
            || length_symbol.exports().is_some()
            || length_symbol.parent().is_some()
            || length_symbol.export_symbol().is_some()
            || self.value_symbol_links(length)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(zero_type),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(invalid());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, TypeDisplayUnavailable, formatter::type_to_string,
        type_records::TypeRecord,
    };
    use crate::semantic::{SemanticStore, mapper::TypeMapper};

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    fn initialized() -> TestStore {
        let mut store = TestStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn observable_state(store: &TestStore) -> (usize, usize, usize, [usize; 26], Option<TypeId>) {
        (
            store.type_len(),
            store.symbol_store().checker_created_symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.canonical_empty_tuple_type_cache(),
        )
    }

    #[test]
    fn mutable_empty_tuple_graph_is_exact_stable_and_displayable() {
        let mut store = initialized();
        let before = observable_state(&store);
        let tuple = store.create_canonical_empty_tuple_type().unwrap();
        assert_eq!(store.validate_canonical_empty_tuple_type(tuple), Ok(()));
        assert_eq!(type_to_string(&store, tuple).unwrap(), "[]");

        let cold = observable_state(&store);
        assert_eq!(
            cold.0,
            before.0 + 2,
            "tuple target plus synthetic this type"
        );
        assert_eq!(cold.1, before.1 + 1, "synthetic length property");
        assert_eq!(cold.2, before.2 + 1, "declared member table");
        assert_eq!(cold.3[10], before.3[10] + 1, "length value links");
        assert_eq!(cold.4, Some(tuple));

        assert_eq!(store.create_canonical_empty_tuple_type(), Ok(tuple));
        assert_eq!(observable_state(&store), cold);
    }

    #[test]
    fn bootstrap_foreign_cache_and_graph_poison_are_rejected_read_only() {
        let mut pristine = TestStore::new();
        let pristine_state = observable_state(&pristine);
        assert_eq!(
            pristine.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::BootstrapUninitialized),
        );
        assert_eq!(observable_state(&pristine), pristine_state);

        let mut store = initialized();
        let tuple = store.create_canonical_empty_tuple_type().unwrap();
        let this_type = match store.type_payload(tuple).unwrap().data() {
            TypeData::Tuple(data) => data.interface.this_type.unwrap(),
            _ => unreachable!(),
        };
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert!(store.set_resolved_base_constraint(this_type, Some(number)));
        let poisoned_graph = observable_state(&store);
        assert_eq!(
            store.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::InvalidCache(tuple)),
        );
        assert_eq!(observable_state(&store), poisoned_graph);
        assert_eq!(
            type_to_string(&store, tuple),
            Err(TypeDisplayUnavailable::EmptyTupleType(
                EmptyTupleTypeError::InvalidCache(tuple),
            )),
        );

        let mut foreign = initialized();
        let foreign_tuple = foreign.create_canonical_empty_tuple_type().unwrap();
        assert_eq!(
            store.replace_canonical_empty_tuple_type_for_test(Some(foreign_tuple)),
            Some(tuple),
        );
        let foreign_cache = observable_state(&store);
        assert_eq!(
            store.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::InvalidCache(foreign_tuple)),
        );
        assert_eq!(observable_state(&store), foreign_cache);
    }
}
