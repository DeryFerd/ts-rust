//! Canonical `Array<T>` and `ReadonlyArray<T>` expression types.
//!
//! Ordinary references remain owned by the authoritative global target's
//! instantiation cache. Array-literal types are exact reference clones kept in
//! a separate derived-type cache, matching pinned `createArrayLiteralType`.

use super::{
    CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes, CanonicalTypeMapperStore, TypeId,
    declared::type_list_key,
    global_types::{create_type_from_generic_global_type, preflight_generic_global_type_target},
    type_records::{TypeCacheState, TypeData, TypeReferenceData},
    types::ObjectFlags,
};

/// A canonical global-array reference and its normalized ordinary identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CanonicalArrayReference {
    pub(super) base_type: TypeId,
    pub(super) element_type: TypeId,
    pub(super) readonly: bool,
    pub(super) array_literal: bool,
}

/// A malformed global-array target, reference, or derived cache entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayTypeError {
    GlobalType(CanonicalGlobalTypeInitializationError),
    InvalidReference(TypeId),
    InvalidArrayLiteralCache { base: TypeId, cached: TypeId },
    Capacity(TypeId),
}

impl std::fmt::Display for ArrayTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::GlobalType(error) => error.fmt(formatter),
            Self::InvalidReference(type_id) => {
                write!(
                    formatter,
                    "array type {type_id:?} is not a canonical reference"
                )
            }
            Self::InvalidArrayLiteralCache { base, cached } => write!(
                formatter,
                "array-literal cache entry {base:?} -> {cached:?} is invalid"
            ),
            Self::Capacity(type_id) => write!(
                formatter,
                "array-literal type capacity was exhausted while cloning {type_id:?}"
            ),
        }
    }
}

impl std::error::Error for ArrayTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::GlobalType(error) => Some(error),
            Self::InvalidReference(_)
            | Self::InvalidArrayLiteralCache { .. }
            | Self::Capacity(_) => None,
        }
    }
}

impl From<CanonicalGlobalTypeInitializationError> for ArrayTypeError {
    fn from(error: CanonicalGlobalTypeInitializationError) -> Self {
        Self::GlobalType(error)
    }
}

impl CanonicalTypeMapperStore {
    /// Validates and classifies a direct reference to the authoritative global
    /// `Array` or `ReadonlyArray` target. Tuple and evolving-array records are
    /// deliberately not accepted as arrays by this predicate.
    pub(super) fn canonical_array_reference(
        &self,
        global_types: &CanonicalGlobalTypes,
        type_id: TypeId,
    ) -> Result<Option<CanonicalArrayReference>, ArrayTypeError> {
        let Some(record) = self.type_payload(type_id) else {
            return Err(ArrayTypeError::InvalidReference(type_id));
        };
        let Some(reference) = direct_reference(record.data()) else {
            return Ok(None);
        };
        self.validate_array_targets(global_types)?;
        let Some(target) = reference.object.target else {
            return Ok(None);
        };
        let readonly = if target == global_types.array_type {
            false
        } else if target == global_types.readonly_array_type {
            true
        } else {
            return Ok(None);
        };
        if preflight_generic_global_type_target(self, target)?.is_some() {
            return Err(ArrayTypeError::InvalidReference(type_id));
        }

        let [element_type] = reference
            .resolved_type_arguments
            .as_deref()
            .ok_or(ArrayTypeError::InvalidReference(type_id))?
        else {
            return Err(ArrayTypeError::InvalidReference(type_id));
        };
        if self.type_payload(*element_type).is_none() {
            return Err(ArrayTypeError::InvalidReference(type_id));
        }

        let base_type = self
            .canonical_array_base(target, *element_type)
            .ok_or(ArrayTypeError::InvalidReference(type_id))?;
        let array_literal = record.object_flags().contains(ObjectFlags::ARRAY_LITERAL);
        if array_literal {
            self.validate_array_literal_clone(base_type, type_id)?;
        } else if type_id != base_type {
            return Err(ArrayTypeError::InvalidReference(type_id));
        }

        Ok(Some(CanonicalArrayReference {
            base_type,
            element_type: *element_type,
            readonly,
            array_literal,
        }))
    }

    /// Returns the sole resolved element argument of a canonical direct array
    /// reference, including a validated array-literal clone.
    #[allow(dead_code)] // Contextual array-expression wiring lands in the integration slice.
    pub(super) fn canonical_array_element_type(
        &self,
        global_types: &CanonicalGlobalTypes,
        type_id: TypeId,
    ) -> Result<Option<TypeId>, ArrayTypeError> {
        Ok(self
            .canonical_array_reference(global_types, type_id)?
            .map(|reference| reference.element_type))
    }

    /// Creates or reuses the target-cache-owned `Array<T>` or
    /// `ReadonlyArray<T>` reference. A missing global target returns the
    /// canonical non-reference fallback unchanged.
    #[allow(dead_code)] // Source array-expression construction lands in the integration slice.
    pub(super) fn create_canonical_array_type(
        &mut self,
        global_types: &CanonicalGlobalTypes,
        element_type: TypeId,
        readonly: bool,
    ) -> Result<TypeId, ArrayTypeError> {
        let target = if readonly {
            global_types.readonly_array_type
        } else {
            global_types.array_type
        };
        Ok(create_type_from_generic_global_type(
            self,
            target,
            element_type,
            ObjectFlags::NONE,
        )?)
    }

    /// Creates or reuses the derived array-literal clone of an ordinary
    /// canonical array reference. Passing an already validated clone is
    /// idempotent; a non-reference fallback is returned unchanged.
    #[allow(dead_code)] // Source array-expression construction lands in the integration slice.
    pub(super) fn create_array_literal_type(
        &mut self,
        global_types: &CanonicalGlobalTypes,
        type_id: TypeId,
    ) -> Result<TypeId, ArrayTypeError> {
        let Some(reference) = self.canonical_array_reference(global_types, type_id)? else {
            return Ok(type_id);
        };
        if reference.array_literal {
            return Ok(type_id);
        }
        let base_type = reference.base_type;

        if let Some(cached) = self
            .derived_types
            .array_literal_types
            .get(&base_type)
            .copied()
        {
            self.validate_array_literal_clone(base_type, cached)?;
            return Ok(cached);
        }

        let base = self
            .type_payload(base_type)
            .ok_or(ArrayTypeError::InvalidReference(base_type))?;
        if !matches!(base.data(), TypeData::TypeReference(_)) {
            return Err(ArrayTypeError::InvalidReference(base_type));
        }
        let clone_flags = base.object_flags() & !ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        let symbol = base.symbol();
        let target = direct_reference(base.data())
            .and_then(|reference| reference.object.target)
            .ok_or(ArrayTypeError::InvalidReference(base_type))?;
        let resolved_type_arguments = direct_reference(base.data())
            .and_then(|reference| reference.resolved_type_arguments.clone())
            .ok_or(ArrayTypeError::InvalidReference(base_type))?;

        if !self.derived_types.try_reserve_array_literals(1) || !self.try_reserve_types(1) {
            return Err(ArrayTypeError::Capacity(base_type));
        }
        let clone = self
            .alloc_type_reference(clone_flags, symbol)
            .ok_or(ArrayTypeError::InvalidReference(base_type))?;
        assert!(self.set_type_object_flags(clone, clone_flags));
        assert!(self.set_object_target_and_mapper(clone, Some(target), None));
        assert!(self.set_type_reference_resolution(clone, None, Some(resolved_type_arguments),));
        assert_eq!(
            self.derived_types
                .array_literal_types
                .insert(base_type, clone),
            None
        );
        Ok(clone)
    }

    fn validate_array_targets(
        &self,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<(), ArrayTypeError> {
        preflight_generic_global_type_target(self, global_types.array_type)?;
        if global_types.readonly_array_type != global_types.array_type {
            preflight_generic_global_type_target(self, global_types.readonly_array_type)?;
        }
        Ok(())
    }

    fn canonical_array_base(&self, target: TypeId, element_type: TypeId) -> Option<TypeId> {
        let TypeData::Interface(interface) = self.type_payload(target)?.data() else {
            return None;
        };
        let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
        else {
            return None;
        };
        instantiations.get(&type_list_key(&[element_type])).copied()
    }

    fn validate_array_literal_clone(
        &self,
        base_type: TypeId,
        cached: TypeId,
    ) -> Result<(), ArrayTypeError> {
        let invalid = || ArrayTypeError::InvalidArrayLiteralCache {
            base: base_type,
            cached,
        };
        if self
            .derived_types
            .array_literal_types
            .get(&base_type)
            .copied()
            != Some(cached)
        {
            return Err(invalid());
        }
        let base = self.type_payload(base_type).ok_or_else(invalid)?;
        let clone = self.type_payload(cached).ok_or_else(invalid)?;
        let TypeData::TypeReference(base_reference) = base.data() else {
            return Err(invalid());
        };
        let TypeData::TypeReference(clone_reference) = clone.data() else {
            return Err(invalid());
        };
        let expected_flags = base.object_flags() & !ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        let mutable_flags = ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
            | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
            | ObjectFlags::UNRESOLVED_MEMBERS;
        if cached == base_type
            || clone.flags() != base.flags()
            || clone.object_flags() & !mutable_flags != expected_flags & !mutable_flags
            || clone.symbol() != base.symbol()
            || clone.alias().is_some()
            || clone_reference.object.target != base_reference.object.target
            || clone_reference.object.mapper.is_some()
            || clone_reference.object.instantiations != TypeCacheState::Unallocated
            || !clone.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
                && clone_reference.object.structured != Default::default()
            || clone_reference.node.is_some()
            || clone_reference.resolved_type_arguments != base_reference.resolved_type_arguments
        {
            return Err(invalid());
        }
        Ok(())
    }
}

fn direct_reference(data: &TypeData) -> Option<&TypeReferenceData> {
    match data {
        TypeData::TypeReference(reference) => Some(reference),
        TypeData::Interface(interface) => Some(&interface.reference),
        _ => None,
    }
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
    use crate::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/array-types.ts\""),
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

    fn array_context(file: FileId) -> CanonicalCheckerContext<'static> {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        // The context retains the arena for its full test lifetime.
        let parsed = Box::leak(Box::new(parsed));
        context(parsed, file)
    }

    #[test]
    fn ordinary_and_literal_arrays_have_distinct_stable_cache_ownership() {
        let mut context = array_context(FileId::new(910));
        let global_types = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();

        let base = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        assert!(store.add_type_object_flags(base, ObjectFlags::MEMBERS_RESOLVED));
        let literal = store
            .create_array_literal_type(&global_types, base)
            .unwrap();
        assert_ne!(literal, base);
        assert_eq!(
            store
                .create_array_literal_type(&global_types, base)
                .unwrap(),
            literal
        );
        assert_eq!(
            store
                .create_array_literal_type(&global_types, literal)
                .unwrap(),
            literal
        );

        let classification = store
            .canonical_array_reference(&global_types, literal)
            .unwrap()
            .unwrap();
        assert_eq!(
            classification,
            CanonicalArrayReference {
                base_type: base,
                element_type: number,
                readonly: false,
                array_literal: true,
            }
        );
        let base_record = store.type_payload(base).unwrap();
        let literal_record = store.type_payload(literal).unwrap();
        assert_eq!(literal_record.symbol(), base_record.symbol());
        assert_eq!(
            literal_record.object_flags(),
            base_record.object_flags() & !ObjectFlags::MEMBERS_RESOLVED
                | ObjectFlags::ARRAY_LITERAL
                | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
        );
        let TypeData::TypeReference(base_reference) = base_record.data() else {
            panic!("ordinary array must be a reference")
        };
        let TypeData::TypeReference(literal_reference) = literal_record.data() else {
            panic!("array literal must be a reference clone")
        };
        assert_eq!(
            literal_reference.object.target,
            base_reference.object.target
        );
        assert_eq!(
            literal_reference.resolved_type_arguments,
            base_reference.resolved_type_arguments
        );
        assert_eq!(
            literal_reference.object.instantiations,
            TypeCacheState::Unallocated
        );
        let TypeData::Interface(target) =
            store.type_payload(global_types.array_type).unwrap().data()
        else {
            panic!("Array must be an interface target")
        };
        let TypeCacheState::Allocated(instantiations) = &target.reference.object.instantiations
        else {
            panic!("Array target must own an instantiation cache")
        };
        assert!(instantiations.values().any(|cached| *cached == base));
        assert!(!instantiations.values().any(|cached| *cached == literal));
        assert!(store.add_type_object_flags(literal, ObjectFlags::MEMBERS_RESOLVED));
        assert_eq!(
            store
                .create_array_literal_type(&global_types, base)
                .unwrap(),
            literal
        );
    }

    #[test]
    fn fallback_tuple_and_evolving_array_identities_remain_distinct() {
        let parsed = parse_source_file("");
        let mut context = context(&parsed, FileId::new(911));
        let global_types = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();

        let fallback = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        assert_eq!(
            store
                .create_array_literal_type(&global_types, fallback)
                .unwrap(),
            fallback
        );
        assert_eq!(
            store
                .canonical_array_element_type(&global_types, fallback)
                .unwrap(),
            None
        );

        let tuple_metadata = store.create_tuple_metadata(Vec::new(), false).unwrap();
        let tuple = store
            .alloc_tuple_type(
                ObjectFlags::REFERENCE | ObjectFlags::TUPLE,
                None,
                tuple_metadata,
            )
            .unwrap();
        let evolving = store
            .alloc_evolving_array_type(ObjectFlags::EVOLVING_ARRAY, None)
            .unwrap();
        assert_eq!(
            store
                .canonical_array_reference(&global_types, tuple)
                .unwrap(),
            None
        );
        assert_eq!(
            store
                .canonical_array_reference(&global_types, evolving)
                .unwrap(),
            None
        );
        assert!(
            !store
                .type_payload(tuple)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::ARRAY_LITERAL)
        );
        assert!(
            !store
                .type_payload(evolving)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::ARRAY_LITERAL)
        );
    }

    #[test]
    fn poisoned_warm_literal_cache_fails_before_any_query_write() {
        let mut context = array_context(FileId::new(912));
        let global_types = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let base = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let literal = store
            .create_array_literal_type(&global_types, base)
            .unwrap();

        assert!(store.set_object_target_and_mapper(
            literal,
            Some(global_types.readonly_array_type),
            None,
        ));
        let before = (
            store.type_len(),
            store.derived_types.array_literal_types.clone(),
        );
        assert_eq!(
            store.create_array_literal_type(&global_types, base),
            Err(ArrayTypeError::InvalidArrayLiteralCache {
                base,
                cached: literal,
            })
        );
        assert_eq!(
            (
                store.type_len(),
                store.derived_types.array_literal_types.clone(),
            ),
            before
        );

        store.derived_types.array_literal_types.insert(base, number);
        let before = (
            store.type_len(),
            store.derived_types.array_literal_types.clone(),
        );
        assert_eq!(
            store.create_array_literal_type(&global_types, base),
            Err(ArrayTypeError::InvalidArrayLiteralCache {
                base,
                cached: number,
            })
        );
        assert_eq!(
            (
                store.type_len(),
                store.derived_types.array_literal_types.clone(),
            ),
            before
        );
    }

    #[test]
    fn foreign_global_targets_are_rejected_read_only() {
        let mut first = array_context(FileId::new(913));
        let second = array_context(FileId::new(914));
        let first_globals = first.global_types().clone();
        let second_globals = second.global_types().clone();
        let number = first.store().intrinsic_bootstrap().unwrap().number_type;
        let store = first.store_mut_for_test();
        let base = store
            .create_canonical_array_type(&first_globals, number, false)
            .unwrap();
        let before = (
            store.type_len(),
            store.derived_types.array_literal_types.len(),
        );

        assert_eq!(
            store.canonical_array_reference(&second_globals, base),
            Err(ArrayTypeError::GlobalType(
                CanonicalGlobalTypeInitializationError::InvalidType(second_globals.array_type)
            ))
        );
        assert_eq!(
            (
                store.type_len(),
                store.derived_types.array_literal_types.len()
            ),
            before
        );
    }
}
