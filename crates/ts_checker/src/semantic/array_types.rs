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

/// The authoritative global targets required to validate canonical array
/// references without retaining the full initialized-global record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CanonicalArrayTargets {
    array_type: TypeId,
    readonly_array_type: TypeId,
}

impl CanonicalArrayTargets {
    pub(super) const fn from_global_types(global_types: &CanonicalGlobalTypes) -> Self {
        Self {
            array_type: global_types.array_type,
            readonly_array_type: global_types.readonly_array_type,
        }
    }

    #[cfg(test)]
    pub(super) const fn for_test(array_type: TypeId, readonly_array_type: TypeId) -> Self {
        Self {
            array_type,
            readonly_array_type,
        }
    }

    /// Builds a validation-only capability for a reference whose registered
    /// global target is already known. Treating the one target as both array
    /// variants preserves exact target/cache validation without granting a
    /// context-free query either array construction capability.
    pub(super) const fn for_single_target_validation(target: TypeId) -> Self {
        Self {
            array_type: target,
            readonly_array_type: target,
        }
    }

    pub(super) const fn array_type(self) -> TypeId {
        self.array_type
    }

    pub(super) const fn readonly_array_type(self) -> TypeId {
        self.readonly_array_type
    }
}

/// A malformed global-array target, reference, or derived cache entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayTypeError {
    GlobalType(CanonicalGlobalTypeInitializationError),
    UnsupportedCreationFlags(ObjectFlags),
    InvalidReference(TypeId),
    InvalidArrayLiteralCache { base: TypeId, cached: TypeId },
    Capacity(TypeId),
}

impl std::fmt::Display for ArrayTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::GlobalType(error) => error.fmt(formatter),
            Self::UnsupportedCreationFlags(flags) => {
                write!(
                    formatter,
                    "array request uses unsupported creation flags {flags:?}"
                )
            }
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
            Self::UnsupportedCreationFlags(_)
            | Self::InvalidReference(_)
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
        self.canonical_array_reference_with_targets(
            CanonicalArrayTargets::from_global_types(global_types),
            type_id,
        )
    }

    /// Target-only form used by semantic operations that retain an explicit
    /// capability derived from [`CanonicalGlobalTypes`].
    pub(super) fn canonical_array_reference_with_targets(
        &self,
        targets: CanonicalArrayTargets,
        type_id: TypeId,
    ) -> Result<Option<CanonicalArrayReference>, ArrayTypeError> {
        let Some(record) = self.type_payload(type_id) else {
            return Err(ArrayTypeError::InvalidReference(type_id));
        };
        let Some(reference) = direct_reference(record.data()) else {
            return Ok(None);
        };
        self.validate_array_targets(targets)?;
        let Some(target) = reference.object.target else {
            return Ok(None);
        };
        let readonly = if target == targets.array_type {
            false
        } else if target == targets.readonly_array_type {
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
    pub(super) fn create_canonical_array_type(
        &mut self,
        global_types: &CanonicalGlobalTypes,
        element_type: TypeId,
        readonly: bool,
    ) -> Result<TypeId, ArrayTypeError> {
        self.create_canonical_array_type_with_targets(
            CanonicalArrayTargets::from_global_types(global_types),
            element_type,
            readonly,
        )
    }

    /// Target-capability form used by semantic operations that retain only
    /// the authoritative canonical Array identities.
    pub(super) fn create_canonical_array_type_with_targets(
        &mut self,
        targets: CanonicalArrayTargets,
        element_type: TypeId,
        readonly: bool,
    ) -> Result<TypeId, ArrayTypeError> {
        self.create_canonical_array_type_with_targets_and_flags(
            targets,
            element_type,
            readonly,
            ObjectFlags::NONE,
        )
    }

    /// Target-capability form with the exact creation flags used by pinned
    /// `createTypeReferenceEx`. The target cache remains keyed only by the
    /// element type, so flags apply only when this call wins the first
    /// allocation for that key.
    pub(super) fn create_canonical_array_type_with_targets_and_flags(
        &mut self,
        targets: CanonicalArrayTargets,
        element_type: TypeId,
        readonly: bool,
        creation_flags: ObjectFlags,
    ) -> Result<TypeId, ArrayTypeError> {
        if !(creation_flags & !ObjectFlags::FROM_TYPE_NODE).is_empty() {
            return Err(ArrayTypeError::UnsupportedCreationFlags(creation_flags));
        }
        let target = if readonly {
            targets.readonly_array_type
        } else {
            targets.array_type
        };
        Ok(create_type_from_generic_global_type(
            self,
            target,
            element_type,
            creation_flags,
        )?)
    }

    /// Creates or reuses the derived array-literal clone of an ordinary
    /// canonical array reference. Passing an already validated clone is
    /// idempotent; a non-reference fallback is returned unchanged.
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

    fn validate_array_targets(&self, targets: CanonicalArrayTargets) -> Result<(), ArrayTypeError> {
        preflight_generic_global_type_target(self, targets.array_type)?;
        if targets.readonly_array_type != targets.array_type {
            preflight_generic_global_type_target(self, targets.readonly_array_type)?;
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

    pub(super) fn validate_array_literal_clone(
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
                && clone_reference.object.structured
                    != super::type_records::StructuredTypeData::default()
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
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, RelationUnavailable,
        bootstrap::{LiteralTypeCacheError, UnionReduction},
    };

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
    fn array_creation_flags_follow_first_target_cache_writer() {
        let mut context = array_context(FileId::new(916));
        let global_types = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = context.store_mut_for_test();

        let from_type_node = store
            .create_canonical_array_type_with_targets_and_flags(
                targets,
                number,
                false,
                ObjectFlags::FROM_TYPE_NODE,
            )
            .unwrap();
        assert_eq!(
            store.type_payload(from_type_node).unwrap().object_flags(),
            ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE
        );
        assert_eq!(
            store
                .create_canonical_array_type_with_targets(targets, number, false)
                .unwrap(),
            from_type_node
        );
        assert!(
            store
                .type_payload(from_type_node)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );

        let semantic_first = store
            .create_canonical_array_type_with_targets(targets, string, false)
            .unwrap();
        assert_eq!(
            store.type_payload(semantic_first).unwrap().object_flags(),
            ObjectFlags::REFERENCE
        );
        assert_eq!(
            store
                .create_canonical_array_type_with_targets_and_flags(
                    targets,
                    string,
                    false,
                    ObjectFlags::FROM_TYPE_NODE,
                )
                .unwrap(),
            semantic_first
        );
        assert!(
            !store
                .type_payload(semantic_first)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FROM_TYPE_NODE)
        );
    }

    #[test]
    fn flagged_array_creation_preserves_empty_generic_fallback() {
        let parsed = parse_source_file("");
        let mut context = context(&parsed, FileId::new(917));
        let global_types = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let (number, empty_object) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.empty_object_type)
        };
        let store = context.store_mut_for_test();
        let before = store.type_len();

        assert_eq!(
            store.create_canonical_array_type_with_targets_and_flags(
                targets,
                number,
                false,
                ObjectFlags::FROM_TYPE_NODE,
            ),
            Ok(empty_object)
        );
        assert_eq!(
            store.create_canonical_array_type_with_targets(targets, number, false),
            Ok(empty_object)
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn unsupported_array_creation_flags_are_rejected_before_caches_and_fallbacks() {
        let invalid_flags = ObjectFlags::FROM_TYPE_NODE | ObjectFlags::ARRAY_LITERAL;
        let mut initialized = array_context(FileId::new(918));
        let global_types = initialized.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let (number, string) = {
            let bootstrap = initialized.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = initialized.store_mut_for_test();

        let cold_before = store.type_len();
        assert_eq!(
            store.create_canonical_array_type_with_targets_and_flags(
                targets,
                number,
                false,
                invalid_flags,
            ),
            Err(ArrayTypeError::UnsupportedCreationFlags(invalid_flags))
        );
        assert_eq!(store.type_len(), cold_before);

        let warm = store
            .create_canonical_array_type_with_targets(targets, string, false)
            .unwrap();
        let warm_before = store.type_len();
        assert_eq!(
            store.create_canonical_array_type_with_targets_and_flags(
                targets,
                string,
                false,
                invalid_flags,
            ),
            Err(ArrayTypeError::UnsupportedCreationFlags(invalid_flags))
        );
        assert_eq!(store.type_len(), warm_before);
        assert_eq!(
            store.create_canonical_array_type_with_targets(targets, string, false),
            Ok(warm)
        );

        let parsed = parse_source_file("");
        let mut fallback_context = context(&parsed, FileId::new(919));
        let fallback_globals = fallback_context.global_types().clone();
        let fallback_targets = CanonicalArrayTargets::from_global_types(&fallback_globals);
        let (number, empty_object) = {
            let bootstrap = fallback_context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.empty_object_type)
        };
        let fallback_store = fallback_context.store_mut_for_test();
        let fallback_before = fallback_store.type_len();
        assert_eq!(
            fallback_store.create_canonical_array_type_with_targets_and_flags(
                fallback_targets,
                number,
                false,
                invalid_flags,
            ),
            Err(ArrayTypeError::UnsupportedCreationFlags(invalid_flags))
        );
        assert_eq!(fallback_store.type_len(), fallback_before);
        assert_eq!(
            fallback_store.create_canonical_array_type_with_targets(
                fallback_targets,
                number,
                false,
            ),
            Ok(empty_object)
        );
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
    fn global_aware_expression_unions_validate_nested_array_cache_ownership() {
        let mut context = array_context(FileId::new(915));
        let global_types = context.global_types().clone();
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = context.store_mut_for_test();
        let inner_base = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let inner_literal = store
            .create_array_literal_type(&global_types, inner_base)
            .unwrap();
        let outer_base = store
            .create_canonical_array_type(&global_types, inner_literal, false)
            .unwrap();
        let outer_literal = store
            .create_array_literal_type(&global_types, outer_base)
            .unwrap();

        assert_eq!(
            store.expression_union_type(&[outer_literal], UnionReduction::None),
            Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                outer_literal
            )),
            "the legacy union boundary remains fail-closed without global identities",
        );
        let union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[outer_literal, string],
                UnionReduction::None,
            )
            .unwrap();
        assert_eq!(
            store
                .expression_union_type_with_global_types(
                    &global_types,
                    &[string, outer_literal],
                    UnionReduction::None,
                )
                .unwrap(),
            union,
            "the recursively validated global-aware cache is stable when warm",
        );
        let element_union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[inner_literal, string],
                UnionReduction::None,
            )
            .unwrap();
        let target_outer = store
            .create_canonical_array_type(&global_types, element_union, false)
            .unwrap();
        assert_eq!(
            store.is_type_assignable_to_with_global_types(
                outer_literal,
                target_outer,
                &global_types,
            ),
            Ok(true),
            "array covariance recurses through a union containing a canonical array",
        );
        assert!(matches!(
            store.is_type_assignable_to_with_global_types(
                target_outer,
                outer_literal,
                &global_types,
            ),
            Err(RelationUnavailable::UnsupportedStructuredType(_)),
        ));

        let outer_record = store.type_payload(outer_literal).unwrap();
        let outer_symbol = outer_record.symbol();
        let TypeData::TypeReference(outer_reference) = outer_record.data() else {
            panic!("array literal must be a reference clone")
        };
        let outer_target = outer_reference.object.target;
        let outer_arguments = outer_reference.resolved_type_arguments.clone();
        let forged = store
            .alloc_type_reference(outer_record.object_flags(), outer_symbol)
            .unwrap();
        assert!(store.set_object_target_and_mapper(forged, outer_target, None));
        assert!(store.set_type_reference_resolution(forged, None, outer_arguments));
        let forged_error = store
            .expression_union_type_with_global_types(
                &global_types,
                &[forged, string],
                UnionReduction::None,
            )
            .unwrap_err();
        let expected_forged_error = ArrayTypeError::InvalidArrayLiteralCache {
            base: outer_base,
            cached: forged,
        };
        assert_eq!(
            forged_error,
            LiteralTypeCacheError::ArrayType {
                type_: forged,
                error: expected_forged_error,
            },
            "an exact-shape clone without derived-cache ownership is rejected",
        );
        assert_eq!(
            std::error::Error::source(&forged_error)
                .and_then(|error| error.downcast_ref::<ArrayTypeError>()),
            Some(&expected_forged_error),
        );

        store
            .derived_types
            .array_literal_types
            .insert(inner_base, string);
        let before = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.derived_types.array_literal_types.clone(),
        );
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[outer_literal, string],
                UnionReduction::None,
            ),
            Err(LiteralTypeCacheError::ArrayType {
                type_: inner_literal,
                error: ArrayTypeError::InvalidArrayLiteralCache {
                    base: inner_base,
                    cached: inner_literal,
                },
            }),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.derived_types.array_literal_types.clone(),
            ),
            before,
            "recursive cache poison is detected before any query write",
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
