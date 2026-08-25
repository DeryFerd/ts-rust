use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, SignatureId, TypeId,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::ValidatedSingleCallable,
    declared::cached_ordinary_type_parameter_owner,
    instantiated_members::{GenericInterfaceMemberError, validate_generic_interface_members},
    links::ValueSymbolLinks,
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        resolved_declared_property_types, validate_resolved_declared_property_object,
    },
    reference_types::validate_direct_generic_reference,
    type_records::{StructuredTypeData, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct IntersectionTypeCacheKey {
    pub(super) types: Vec<TypeId>,
    pub(super) alias_symbol: Option<SemanticSymbolId>,
    pub(super) alias_arguments: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum IntersectionTypeError {
    BootstrapUninitialized,
    Capacity,
    UnsupportedConstituent(TypeId),
    UnsupportedPropertyType(TypeId),
    MalformedConstituent(TypeId),
    InvalidAliasSymbol(SemanticSymbolId),
    InvalidCachedIntersection(TypeId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct IntersectionTypeProjection {
    pub(super) types: Vec<TypeId>,
    pub(super) members: SymbolTableId,
    pub(super) properties: Vec<SemanticSymbolId>,
    pub(super) reduced_to_never: bool,
}

/// Validated constituent and alias identity before intersection members resolve.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DeferredIntersectionTypeProjection {
    pub(super) types: Vec<TypeId>,
    pub(super) alias_symbol: Option<SemanticSymbolId>,
    pub(super) alias_arguments: Vec<TypeId>,
}

#[derive(Clone, Debug)]
struct SourceProperty {
    symbol: SemanticSymbolId,
    name: EscapedName,
    type_: TypeId,
    symbol_flags: SymbolFlags,
    check_flags: CheckFlags,
    literal: bool,
    explicit_never: bool,
}

#[derive(Clone, Debug)]
struct PropertyGroup {
    name: EscapedName,
    sources: Vec<SourceProperty>,
}

#[derive(Clone, Debug)]
enum ExpectedProperty {
    Borrowed(SemanticSymbolId),
    Synthetic {
        name: EscapedName,
        type_: TypeId,
        flags: SymbolFlags,
        check_flags: CheckFlags,
        declarations: Option<Vec<ts_ast::NodeRef>>,
    },
}

impl ExpectedProperty {
    fn name(&self, store: &CanonicalTypeMapperStore) -> Option<EscapedName> {
        match self {
            Self::Borrowed(symbol) => Some(store.symbol(*symbol)?.name().to_owned()),
            Self::Synthetic { name, .. } => Some(name.clone()),
        }
    }
}

impl CanonicalTypeMapperStore {
    pub(super) fn validate_intersection_constituent(
        &self,
        type_: TypeId,
    ) -> Result<(), IntersectionTypeError> {
        let mut constituents = Vec::new();
        self.append_intersection_constituent(type_, &mut constituents)?;
        self.validate_branded_string_intersection(&constituents)?;
        expected_properties(self, &constituents)?;
        expected_call_signatures(self, &constituents).map(|_| ())
    }

    pub(super) fn canonical_intersection_type(
        &mut self,
        input: &[TypeId],
        alias_symbol: Option<SemanticSymbolId>,
    ) -> Result<TypeId, IntersectionTypeError> {
        let (unknown_type, never_type) = self
            .intrinsic_bootstrap()
            .map(|bootstrap| (bootstrap.unknown_type, bootstrap.never_type))
            .ok_or(IntersectionTypeError::BootstrapUninitialized)?;
        if let Some(symbol) = alias_symbol
            && self.symbol(symbol).is_none_or(|record| {
                !record.flags().contains(SymbolFlags::TYPE_ALIAS)
                    || self.get_merged_symbol(symbol) != Some(symbol)
            })
        {
            return Err(IntersectionTypeError::InvalidAliasSymbol(symbol));
        }

        let mut types = Vec::new();
        for type_ in input {
            self.append_intersection_constituent(*type_, &mut types)?;
        }
        self.validate_branded_string_intersection(&types)?;
        if types.is_empty() {
            return Ok(unknown_type);
        }
        if types.len() == 1 {
            return Ok(types[0]);
        }

        let key = IntersectionTypeCacheKey {
            types,
            alias_symbol,
            alias_arguments: Vec::new(),
        };
        if let Some(cached) = self.intersection_types.get(&key).copied() {
            if self.type_payload(cached).is_some_and(|record| {
                record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            }) {
                self.validate_intersection_type(cached)?;
                return Ok(cached);
            }
            self.validate_deferred_intersection_type(cached)?;
            return self.materialize_deferred_intersection_type(cached);
        }

        let expected = expected_properties(self, &key.types)?;
        let call_signatures = expected_call_signatures(self, &key.types)?;
        let synthetic_count = expected
            .iter()
            .filter(|property| matches!(property, ExpectedProperty::Synthetic { .. }))
            .count();
        let alias_count = usize::from(key.alias_symbol.is_some());
        let prepared_members =
            PreparedSymbolTable::new(expected.len()).ok_or(IntersectionTypeError::Capacity)?;
        if !self.try_reserve_types(1)
            || !self.try_reserve_type_aliases(alias_count)
            || !self.try_reserve_checker_symbol_allocations(synthetic_count, 1)
            || !self.try_reserve_value_symbol_links(synthetic_count)
            || self.intersection_types.try_reserve(1).is_err()
            || self.intersection_keys_by_type.try_reserve(1).is_err()
        {
            return Err(IntersectionTypeError::Capacity);
        }

        let mut object_flags = key.types.iter().fold(ObjectFlags::NONE, |flags, type_| {
            flags
                | (self
                    .type_payload(*type_)
                    .expect("validated intersection constituent remains owned")
                    .object_flags()
                    & ObjectFlags::PROPAGATING_FLAGS)
        });
        let reduced_to_never = expected.iter().any(|property| {
            matches!(
                property,
                ExpectedProperty::Synthetic {
                    type_,
                    flags,
                    check_flags,
                    ..
                } if *type_ == never_type
                    && !flags.contains(SymbolFlags::OPTIONAL)
                    && check_flags.contains(CheckFlags::NON_UNIFORM_AND_LITERAL)
                    && !check_flags.contains(CheckFlags::HAS_NEVER_TYPE)
            )
        });
        object_flags |= ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED;
        if reduced_to_never {
            object_flags |= ObjectFlags::IS_NEVER_INTERSECTION;
        }

        let intersection_type = self
            .alloc_intersection_type(object_flags, key.types.clone())
            .expect("a preflighted intersection allocation is infallible");
        if let Some(symbol) = key.alias_symbol {
            let alias = self
                .alloc_type_alias(Some(symbol))
                .expect("a preflighted intersection alias allocation is infallible");
            assert!(self.set_type_alias(intersection_type, Some(alias)));
        }
        assert!(self.set_structured_type_members(
            intersection_type,
            None,
            None,
            (!call_signatures.is_empty()).then_some(call_signatures),
            None,
            None,
        ));

        let members = self.alloc_prepared_symbol_table(prepared_members);
        let mut properties = Vec::with_capacity(expected.len());
        for property in expected {
            let (name, symbol) = match property {
                ExpectedProperty::Borrowed(symbol) => {
                    let name = self
                        .symbol(symbol)
                        .expect("validated borrowed property remains owned")
                        .name()
                        .to_owned();
                    (name, symbol)
                }
                ExpectedProperty::Synthetic {
                    name,
                    type_: property_type,
                    flags,
                    check_flags,
                    declarations,
                } => {
                    let symbol = self.alloc_transient_symbol(flags, name.clone(), check_flags);
                    if declarations.is_some() {
                        assert!(self.set_symbol_declarations(symbol, declarations, None));
                    }
                    assert!(self.set_value_symbol_links(
                        symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(property_type),
                            containing_type: Some(intersection_type),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                    (name, symbol)
                }
            };
            assert_eq!(self.insert_symbol(members, name, symbol), Some(None));
            properties.push(symbol);
        }

        assert!(self.set_union_or_intersection_caches(
            intersection_type,
            Some(members),
            None,
            Some(properties),
        ));
        assert!(
            self.intersection_types
                .insert(key.clone(), intersection_type)
                .is_none()
        );
        assert!(
            self.intersection_keys_by_type
                .insert(intersection_type, key)
                .is_none()
        );
        Ok(intersection_type)
    }

    /// Interns an authenticated intersection without resolving constituent members.
    pub(super) fn canonical_deferred_intersection_type(
        &mut self,
        input: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
    ) -> Result<TypeId, IntersectionTypeError> {
        let unknown = self
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.unknown_type)
            .ok_or(IntersectionTypeError::BootstrapUninitialized)?;
        let (alias_symbol, alias_arguments) = match alias {
            None => (None, Vec::new()),
            Some((symbol, arguments)) => {
                self.validate_deferred_intersection_alias(symbol, arguments)?;
                (Some(symbol), arguments.to_vec())
            }
        };

        let mut types = Vec::with_capacity(input.len());
        for type_ in input {
            self.append_deferred_intersection_constituent(*type_, &mut types)?;
        }
        if types.is_empty() {
            return Ok(unknown);
        }
        if types.len() == 1 {
            return Ok(types[0]);
        }

        let key = IntersectionTypeCacheKey {
            types,
            alias_symbol,
            alias_arguments,
        };
        if let Some(cached) = self.intersection_types.get(&key).copied() {
            if self.type_payload(cached).is_some_and(|record| {
                record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            }) {
                self.validate_intersection_type(cached)?;
            } else {
                self.validate_deferred_intersection_type(cached)?;
            }
            return Ok(cached);
        }

        let object_flags = self.deferred_intersection_object_flags(&key.types)?;
        let alias_count = usize::from(key.alias_symbol.is_some());
        if !self.try_reserve_types(1)
            || !self.try_reserve_type_aliases(alias_count)
            || self.intersection_types.try_reserve(1).is_err()
            || self.intersection_keys_by_type.try_reserve(1).is_err()
        {
            return Err(IntersectionTypeError::Capacity);
        }

        let intersection = self
            .alloc_intersection_type(object_flags, key.types.clone())
            .ok_or(IntersectionTypeError::Capacity)?;
        if let Some(symbol) = key.alias_symbol {
            let identity = self
                .alloc_type_alias(Some(symbol))
                .ok_or(IntersectionTypeError::InvalidAliasSymbol(symbol))?;
            if !key.alias_arguments.is_empty()
                && !self.set_type_alias_arguments(identity, Some(key.alias_arguments.clone()))
            {
                return Err(IntersectionTypeError::InvalidAliasSymbol(symbol));
            }
            if !self.set_type_alias(intersection, Some(identity)) {
                return Err(IntersectionTypeError::InvalidAliasSymbol(symbol));
            }
        }
        if self
            .intersection_types
            .insert(key.clone(), intersection)
            .is_some()
            || self
                .intersection_keys_by_type
                .insert(intersection, key)
                .is_some()
        {
            return Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection,
            ));
        }
        Ok(intersection)
    }

    /// Validates an interned intersection whose properties remain unresolved.
    pub(super) fn validate_deferred_intersection_type(
        &self,
        type_: TypeId,
    ) -> Result<DeferredIntersectionTypeProjection, IntersectionTypeError> {
        let invalid = || IntersectionTypeError::InvalidCachedIntersection(type_);
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Intersection(intersection) = record.data() else {
            return Err(invalid());
        };
        if record.flags() != TypeFlags::INTERSECTION
            || record.symbol().is_some()
            || intersection.intersection.types.len() < 2
            || intersection.intersection.structured != StructuredTypeData::default()
            || intersection.intersection.property_cache.is_some()
            || intersection
                .intersection
                .property_cache_without_function_property_augment
                .is_some()
            || intersection.intersection.resolved_properties.is_some()
            || intersection.resolved_apparent_type.is_some()
            || intersection.unique_literal_filled_instantiation.is_some()
        {
            return Err(invalid());
        }

        let (alias_symbol, alias_arguments) = match record.alias() {
            None => (None, Vec::new()),
            Some(identity) => {
                let identity = self.type_alias(identity).ok_or_else(invalid)?;
                let symbol = identity.symbol().ok_or_else(invalid)?;
                let arguments = identity.type_arguments().unwrap_or_default().to_vec();
                self.validate_deferred_intersection_alias(symbol, &arguments)
                    .map_err(|_| invalid())?;
                (Some(symbol), arguments)
            }
        };
        let key = IntersectionTypeCacheKey {
            types: intersection.intersection.types.clone(),
            alias_symbol,
            alias_arguments: alias_arguments.clone(),
        };
        if self.intersection_types.get(&key) != Some(&type_)
            || self.intersection_keys_by_type.get(&type_) != Some(&key)
            || record.object_flags()
                != self
                    .deferred_intersection_object_flags(&key.types)
                    .map_err(|_| invalid())?
        {
            return Err(invalid());
        }

        let mut validated = Vec::with_capacity(key.types.len());
        for constituent in &key.types {
            self.append_deferred_intersection_constituent(*constituent, &mut validated)
                .map_err(|_| invalid())?;
        }
        if validated != key.types {
            return Err(invalid());
        }

        Ok(DeferredIntersectionTypeProjection {
            types: key.types,
            alias_symbol,
            alias_arguments,
        })
    }

    fn validate_deferred_intersection_alias(
        &self,
        symbol: SemanticSymbolId,
        arguments: &[TypeId],
    ) -> Result<(), IntersectionTypeError> {
        let owner = self
            .symbol(symbol)
            .ok_or(IntersectionTypeError::InvalidAliasSymbol(symbol))?;
        let Some([declaration]) = owner.declarations() else {
            return Err(IntersectionTypeError::InvalidAliasSymbol(symbol));
        };
        if !owner.flags().contains(SymbolFlags::TYPE_ALIAS)
            || self.get_merged_symbol(symbol) != Some(symbol)
            || self.source_node_kind(*declaration) != Some(SyntaxKind::TypeAliasDeclaration)
            || arguments
                .iter()
                .any(|argument| self.type_payload(*argument).is_none())
            || self
                .type_alias_links(symbol)
                .and_then(|links| links.type_parameters.as_deref())
                .is_some_and(|parameters| parameters.len() != arguments.len())
        {
            return Err(IntersectionTypeError::InvalidAliasSymbol(symbol));
        }
        Ok(())
    }

    fn deferred_intersection_object_flags(
        &self,
        constituents: &[TypeId],
    ) -> Result<ObjectFlags, IntersectionTypeError> {
        constituents
            .iter()
            .try_fold(ObjectFlags::NONE, |flags, constituent| {
                let record = self
                    .type_payload(*constituent)
                    .ok_or(IntersectionTypeError::MalformedConstituent(*constituent))?;
                Ok(flags | record.object_flags() & ObjectFlags::PROPAGATING_FLAGS)
            })
    }

    fn append_deferred_intersection_constituent(
        &self,
        type_: TypeId,
        output: &mut Vec<TypeId>,
    ) -> Result<(), IntersectionTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
        match record.data() {
            TypeData::Intersection(_) => {
                let constituents = if record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
                {
                    self.validate_intersection_type(type_)?.types
                } else {
                    self.validate_deferred_intersection_type(type_)?.types
                };
                for constituent in constituents {
                    self.append_deferred_intersection_constituent(constituent, output)?;
                }
                return Ok(());
            }
            TypeData::TypeParameter(_) => {
                let owner = cached_ordinary_type_parameter_owner(self, type_)
                    .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
                let symbol = self
                    .symbol(owner)
                    .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
                let Some([declaration]) = symbol.declarations() else {
                    return Err(IntersectionTypeError::MalformedConstituent(type_));
                };
                if self.get_merged_symbol(owner) != Some(owner)
                    || self.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
                {
                    return Err(IntersectionTypeError::MalformedConstituent(type_));
                }
            }
            TypeData::TypeReference(_) | TypeData::Interface(_)
                if record.object_flags().contains(ObjectFlags::REFERENCE) =>
            {
                let reference = validate_direct_generic_reference(self, type_)
                    .map_err(|_| IntersectionTypeError::MalformedConstituent(type_))?;
                let target = self
                    .type_payload(reference.target)
                    .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
                if !matches!(target.data(), TypeData::Interface(_))
                    || target.symbol().is_none_or(|symbol| {
                        self.get_merged_symbol(symbol) != Some(symbol)
                            || self.symbol(symbol).is_none_or(|owner| {
                                !owner.flags().contains(SymbolFlags::INTERFACE)
                                    || owner
                                        .flags()
                                        .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
                                        != SymbolFlags::NONE
                            })
                    })
                {
                    return Err(IntersectionTypeError::UnsupportedConstituent(type_));
                }
                if record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
                {
                    if !matches!(
                        validate_generic_interface_members(self, type_, None),
                        Ok(Some(_))
                    ) {
                        return Err(IntersectionTypeError::MalformedConstituent(type_));
                    }
                } else if record.data().structured() != Some(&StructuredTypeData::default()) {
                    return Err(IntersectionTypeError::MalformedConstituent(type_));
                }
            }
            TypeData::Interface(_) | TypeData::Object(_) => {
                match validate_resolved_declared_property_object(self, type_) {
                    DeclaredPropertyObjectValidation::Valid(_) => {}
                    DeclaredPropertyObjectValidation::NotDeclared => {
                        return Err(IntersectionTypeError::UnsupportedConstituent(type_));
                    }
                    DeclaredPropertyObjectValidation::Malformed => {
                        return Err(IntersectionTypeError::MalformedConstituent(type_));
                    }
                }
            }
            _ => return Err(IntersectionTypeError::UnsupportedConstituent(type_)),
        }
        if !output.contains(&type_) {
            output.push(type_);
        }
        Ok(())
    }

    fn materialize_deferred_intersection_type(
        &mut self,
        type_: TypeId,
    ) -> Result<TypeId, IntersectionTypeError> {
        let projection = self.validate_deferred_intersection_type(type_)?;
        for constituent in &projection.types {
            let mut validated = Vec::new();
            self.append_intersection_constituent(*constituent, &mut validated)?;
            if validated.as_slice() != [*constituent] {
                return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
            }
        }
        let expected = expected_properties(self, &projection.types)?;
        let call_signatures = expected_call_signatures(self, &projection.types)?;
        let synthetic_count = expected
            .iter()
            .filter(|property| matches!(property, ExpectedProperty::Synthetic { .. }))
            .count();
        let prepared_members =
            PreparedSymbolTable::new(expected.len()).ok_or(IntersectionTypeError::Capacity)?;
        if !self.try_reserve_checker_symbol_allocations(synthetic_count, 1)
            || !self.try_reserve_value_symbol_links(synthetic_count)
        {
            return Err(IntersectionTypeError::Capacity);
        }

        let never = self
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(IntersectionTypeError::BootstrapUninitialized)?;
        let reduced_to_never = expected.iter().any(|property| {
            matches!(
                property,
                ExpectedProperty::Synthetic {
                    type_,
                    flags,
                    check_flags,
                    ..
                } if *type_ == never
                    && !flags.contains(SymbolFlags::OPTIONAL)
                    && check_flags.contains(CheckFlags::NON_UNIFORM_AND_LITERAL)
                    && !check_flags.contains(CheckFlags::HAS_NEVER_TYPE)
            )
        });
        let mut flags = self.deferred_intersection_object_flags(&projection.types)?
            | ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED;
        if reduced_to_never {
            flags |= ObjectFlags::IS_NEVER_INTERSECTION;
        }
        if !self.set_type_object_flags(type_, flags)
            || !self.set_structured_type_members(
                type_,
                None,
                None,
                (!call_signatures.is_empty()).then_some(call_signatures),
                None,
                None,
            )
        {
            return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
        }

        let members = self.alloc_prepared_symbol_table(prepared_members);
        let mut properties = Vec::with_capacity(expected.len());
        for property in expected {
            let (name, symbol) = match property {
                ExpectedProperty::Borrowed(symbol) => {
                    let name = self
                        .symbol(symbol)
                        .ok_or(IntersectionTypeError::InvalidCachedIntersection(type_))?
                        .name()
                        .to_owned();
                    (name, symbol)
                }
                ExpectedProperty::Synthetic {
                    name,
                    type_: property_type,
                    flags,
                    check_flags,
                    declarations,
                } => {
                    let symbol = self.alloc_transient_symbol(flags, name.clone(), check_flags);
                    if declarations.is_some()
                        && !self.set_symbol_declarations(symbol, declarations, None)
                    {
                        return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
                    }
                    if !self.set_value_symbol_links(
                        symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(property_type),
                            containing_type: Some(type_),
                            ..ValueSymbolLinks::default()
                        },
                    ) {
                        return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
                    }
                    (name, symbol)
                }
            };
            if self.insert_symbol(members, name, symbol) != Some(None) {
                return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
            }
            properties.push(symbol);
        }
        if !self.set_union_or_intersection_caches(type_, Some(members), None, Some(properties)) {
            return Err(IntersectionTypeError::InvalidCachedIntersection(type_));
        }
        self.validate_intersection_type(type_)?;
        Ok(type_)
    }

    fn append_intersection_constituent(
        &self,
        type_: TypeId,
        output: &mut Vec<TypeId>,
    ) -> Result<(), IntersectionTypeError> {
        let Some(record) = self.type_payload(type_) else {
            return Err(IntersectionTypeError::UnsupportedConstituent(type_));
        };
        if record.flags() == TypeFlags::INTERSECTION {
            let projection = self.validate_intersection_type(type_)?;
            for constituent in projection.types {
                if !output.contains(&constituent) {
                    output.push(constituent);
                }
            }
            return Ok(());
        }
        if record.flags() == TypeFlags::STRING_LITERAL {
            self.validate_union_constituent(type_)
                .map_err(|_| IntersectionTypeError::MalformedConstituent(type_))?;
            if !output.contains(&type_) {
                output.push(type_);
            }
            return Ok(());
        }
        match validate_resolved_declared_property_object(self, type_) {
            DeclaredPropertyObjectValidation::Valid(_) => {
                if !output.contains(&type_) {
                    output.push(type_);
                }
                Ok(())
            }
            DeclaredPropertyObjectValidation::NotDeclared => {
                if record.flags() == TypeFlags::OBJECT
                    && record.object_flags().contains(ObjectFlags::REFERENCE)
                    && matches!(
                        record.data(),
                        TypeData::TypeReference(_) | TypeData::Interface(_)
                    )
                {
                    self.validate_resolved_generic_intersection_constituent(type_)?;
                    if !output.contains(&type_) {
                        output.push(type_);
                    }
                    return Ok(());
                }
                match validate_stored_callable_set(self, type_) {
                    StoredCallableSetValidation::Valid { projection, .. }
                        if !projection.call_signatures.is_empty()
                            && projection.construct_signatures.is_empty()
                            && projection.call_signatures.iter().all(|callable| {
                                callable.return_type.is_some()
                                    && self.signature(callable.signature).is_some_and(|signature| {
                                        signature.type_parameters().is_empty()
                                            && signature.this_parameter().is_none()
                                    })
                            }) =>
                    {
                        if !output.contains(&type_) {
                            output.push(type_);
                        }
                        Ok(())
                    }
                    StoredCallableSetValidation::Malformed { .. } => {
                        Err(IntersectionTypeError::MalformedConstituent(type_))
                    }
                    StoredCallableSetValidation::NotCallable
                    | StoredCallableSetValidation::Pending { .. }
                    | StoredCallableSetValidation::Valid { .. } => {
                        Err(IntersectionTypeError::UnsupportedConstituent(type_))
                    }
                }
            }
            DeclaredPropertyObjectValidation::Malformed => {
                Err(IntersectionTypeError::MalformedConstituent(type_))
            }
        }
    }

    fn validate_branded_string_intersection(
        &self,
        constituents: &[TypeId],
    ) -> Result<(), IntersectionTypeError> {
        let Some(literal) = constituents.iter().copied().find(|constituent| {
            self.type_payload(*constituent)
                .is_some_and(|record| record.flags() == TypeFlags::STRING_LITERAL)
        }) else {
            return Ok(());
        };
        let [string, brand] = constituents else {
            return Err(IntersectionTypeError::UnsupportedConstituent(literal));
        };
        if *string != literal {
            return Err(IntersectionTypeError::UnsupportedConstituent(literal));
        }
        match validate_resolved_declared_property_object(self, *brand) {
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral) => {}
            DeclaredPropertyObjectValidation::Malformed => {
                return Err(IntersectionTypeError::MalformedConstituent(*brand));
            }
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
            | DeclaredPropertyObjectValidation::NotDeclared => {
                return Err(IntersectionTypeError::UnsupportedConstituent(*brand));
            }
        }
        if self
            .type_payload(*brand)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .is_none_or(|properties| properties.is_empty())
        {
            return Err(IntersectionTypeError::UnsupportedConstituent(*brand));
        }
        Ok(())
    }

    fn validate_resolved_generic_intersection_constituent(
        &self,
        type_: TypeId,
    ) -> Result<(), IntersectionTypeError> {
        let members = match validate_generic_interface_members(self, type_, None) {
            Ok(Some(members)) => members,
            Ok(None)
            | Err(
                GenericInterfaceMemberError::UnsupportedTarget(_)
                | GenericInterfaceMemberError::UnsupportedMember(_)
                | GenericInterfaceMemberError::UnsupportedPropertyType(_),
            ) => return Err(IntersectionTypeError::UnsupportedConstituent(type_)),
            Err(GenericInterfaceMemberError::Capacity(_)) => {
                return Err(IntersectionTypeError::Capacity);
            }
            Err(
                GenericInterfaceMemberError::Reference(_)
                | GenericInterfaceMemberError::InvalidTarget(_)
                | GenericInterfaceMemberError::InvalidMember(_)
                | GenericInterfaceMemberError::InvalidCachedMembers(_)
                | GenericInterfaceMemberError::InvalidCachedProperty(_),
            ) => return Err(IntersectionTypeError::MalformedConstituent(type_)),
        };
        let Some(mapper) = members.mapper() else {
            return Err(IntersectionTypeError::UnsupportedConstituent(type_));
        };
        if members.reference() != type_
            || members.target() == type_
            || members.properties().is_empty()
            || members.members().is_none()
        {
            return Err(IntersectionTypeError::MalformedConstituent(type_));
        }

        let mut has_proxy = false;
        for property in members.properties() {
            let symbol = self
                .symbol(*property)
                .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
            let links = self
                .value_symbol_links(*property)
                .ok_or(IntersectionTypeError::MalformedConstituent(type_))?;
            if links.resolved_type.is_none() {
                return Err(IntersectionTypeError::UnsupportedConstituent(type_));
            }
            if symbol.flags().contains(SymbolFlags::TRANSIENT) {
                has_proxy = true;
                if links.target.is_none()
                    || links.mapper != Some(mapper)
                    || !symbol.check_flags().contains(CheckFlags::INSTANTIATED)
                {
                    return Err(IntersectionTypeError::MalformedConstituent(type_));
                }
            }
        }
        if !has_proxy {
            return Err(IntersectionTypeError::MalformedConstituent(type_));
        }
        Ok(())
    }

    pub(super) fn validate_intersection_type(
        &self,
        type_: TypeId,
    ) -> Result<IntersectionTypeProjection, IntersectionTypeError> {
        let invalid = || IntersectionTypeError::InvalidCachedIntersection(type_);
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Intersection(data) = record.data() else {
            return Err(invalid());
        };
        if record.flags() != TypeFlags::INTERSECTION
            || record.symbol().is_some()
            || data.intersection.types.len() < 2
            || data
                .intersection
                .types
                .iter()
                .enumerate()
                .any(|(index, constituent)| {
                    data.intersection.types[..index].contains(constituent)
                        || self
                            .type_payload(*constituent)
                            .is_none_or(|record| record.flags() == TypeFlags::INTERSECTION)
                })
        {
            return Err(invalid());
        }

        let (alias_symbol, alias_arguments) = match record.alias() {
            None => (None, Vec::new()),
            Some(alias) => {
                let alias = self.type_alias(alias).ok_or_else(invalid)?;
                let symbol = alias.symbol().ok_or_else(invalid)?;
                if self.symbol(symbol).is_none_or(|record| {
                    !record.flags().contains(SymbolFlags::TYPE_ALIAS)
                        || self.get_merged_symbol(symbol) != Some(symbol)
                }) {
                    return Err(invalid());
                }
                let arguments = alias.type_arguments().unwrap_or_default().to_vec();
                if arguments
                    .iter()
                    .any(|argument| self.type_payload(*argument).is_none())
                {
                    return Err(invalid());
                }
                (Some(symbol), arguments)
            }
        };
        let key = IntersectionTypeCacheKey {
            types: data.intersection.types.clone(),
            alias_symbol,
            alias_arguments,
        };
        if self.intersection_types.get(&key) != Some(&type_)
            || self.intersection_keys_by_type.get(&type_) != Some(&key)
        {
            return Err(invalid());
        }
        if self
            .validate_branded_string_intersection(&key.types)
            .is_err()
        {
            return Err(invalid());
        }

        for constituent in &key.types {
            let mut validated = Vec::new();
            if self
                .append_intersection_constituent(*constituent, &mut validated)
                .is_err()
                || validated.as_slice() != [*constituent]
            {
                return Err(invalid());
            }
        }
        let expected = expected_properties(self, &key.types).map_err(|_| invalid())?;
        let expected_signatures =
            expected_call_signatures(self, &key.types).map_err(|_| invalid())?;
        let Some(members) = data.intersection.property_cache else {
            return Err(invalid());
        };
        if data
            .intersection
            .property_cache_without_function_property_augment
            .is_some()
            || data.resolved_apparent_type.is_some()
            || data.unique_literal_filled_instantiation.is_some()
        {
            return Err(invalid());
        }
        let properties = data
            .intersection
            .resolved_properties
            .clone()
            .ok_or_else(invalid)?;
        if properties.len() != expected.len() {
            return Err(invalid());
        }
        let table = self.symbol_table(members).ok_or_else(invalid)?;
        if table.len() != expected.len() {
            return Err(invalid());
        }
        for (expected, actual) in expected.iter().zip(&properties) {
            let expected_name = expected.name(self).ok_or_else(invalid)?;
            if table.get(expected_name.as_ref()) != Some(*actual) {
                return Err(invalid());
            }
            match expected {
                ExpectedProperty::Borrowed(symbol) if symbol == actual => {}
                ExpectedProperty::Borrowed(_) => return Err(invalid()),
                ExpectedProperty::Synthetic {
                    type_: property_type,
                    flags,
                    check_flags,
                    declarations,
                    ..
                } => {
                    let symbol = self.symbol(*actual).ok_or_else(invalid)?;
                    let links = self.value_symbol_links(*actual).ok_or_else(invalid)?;
                    if symbol.flags() != *flags | SymbolFlags::TRANSIENT
                        || symbol.check_flags() != *check_flags
                        || symbol.declarations() != declarations.as_deref()
                        || symbol.value_declaration().is_some()
                        || symbol.members().is_some()
                        || symbol.exports().is_some()
                        || symbol.parent().is_some()
                        || symbol.export_symbol().is_some()
                        || links
                            != &(ValueSymbolLinks {
                                resolved_type: Some(*property_type),
                                containing_type: Some(type_),
                                ..ValueSymbolLinks::default()
                            })
                    {
                        return Err(invalid());
                    }
                }
            }
        }

        let bootstrap = self.intrinsic_bootstrap().ok_or_else(invalid)?;
        let reduced_to_never = expected.iter().any(|property| {
            matches!(
                property,
                ExpectedProperty::Synthetic {
                    type_: property_type,
                    flags,
                    check_flags,
                    ..
                } if *property_type == bootstrap.never_type
                    && !flags.contains(SymbolFlags::OPTIONAL)
                    && check_flags.contains(CheckFlags::NON_UNIFORM_AND_LITERAL)
                    && !check_flags.contains(CheckFlags::HAS_NEVER_TYPE)
            )
        });
        let propagated = key
            .types
            .iter()
            .fold(ObjectFlags::NONE, |flags, constituent| {
                flags
                    | (self
                        .type_payload(*constituent)
                        .expect("validated constituent remains owned")
                        .object_flags()
                        & ObjectFlags::PROPAGATING_FLAGS)
            });
        let expected_flags = propagated
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED
            | if reduced_to_never {
                ObjectFlags::IS_NEVER_INTERSECTION
            } else {
                ObjectFlags::NONE
            };
        let expected_structured = StructuredTypeData {
            signatures: (!expected_signatures.is_empty()).then_some(expected_signatures.clone()),
            call_signature_count: expected_signatures.len(),
            ..StructuredTypeData::default()
        };
        if record.object_flags() != expected_flags
            || data.intersection.structured != expected_structured
        {
            return Err(invalid());
        }
        Ok(IntersectionTypeProjection {
            types: key.types,
            members,
            properties,
            reduced_to_never,
        })
    }
}

fn expected_call_signatures(
    store: &CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<Vec<SignatureId>, IntersectionTypeError> {
    let mut signatures = Vec::<ValidatedSingleCallable>::new();
    for type_ in types {
        match validate_stored_callable_set(store, *type_) {
            StoredCallableSetValidation::NotCallable => {}
            StoredCallableSetValidation::Pending { .. } => {
                return Err(IntersectionTypeError::UnsupportedConstituent(*type_));
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(IntersectionTypeError::MalformedConstituent(*type_));
            }
            StoredCallableSetValidation::Valid { projection, .. } => {
                if !projection.construct_signatures.is_empty() {
                    return Err(IntersectionTypeError::UnsupportedConstituent(*type_));
                }
                for callable in projection.call_signatures {
                    let signature = store
                        .signature(callable.signature)
                        .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
                    if callable.return_type.is_none()
                        || !signature.type_parameters().is_empty()
                        || signature.this_parameter().is_some()
                    {
                        return Err(IntersectionTypeError::UnsupportedConstituent(*type_));
                    }
                    if signatures.iter().any(|existing| {
                        existing.signature == callable.signature
                            || existing.parameters == callable.parameters
                                && existing.rest_parameter == callable.rest_parameter
                                && existing.min_argument_count == callable.min_argument_count
                                && existing.return_type == callable.return_type
                    }) {
                        continue;
                    }
                    signatures.push(callable);
                }
            }
        }
    }
    Ok(signatures
        .into_iter()
        .map(|signature| signature.signature)
        .collect())
}

fn expected_properties(
    store: &CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<Vec<ExpectedProperty>, IntersectionTypeError> {
    let boolean_type = store
        .intrinsic_bootstrap()
        .ok_or(IntersectionTypeError::BootstrapUninitialized)?
        .boolean_type;
    let mut groups: Vec<PropertyGroup> = Vec::new();
    let mut validating_property_types = HashSet::new();
    let mut validated_property_types = HashSet::new();
    for type_ in types {
        let record = store
            .type_payload(*type_)
            .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
        if record.flags() == TypeFlags::STRING_LITERAL {
            store
                .validate_union_constituent(*type_)
                .map_err(|_| IntersectionTypeError::MalformedConstituent(*type_))?;
            continue;
        }
        let structured = record
            .data()
            .structured()
            .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
        for symbol in structured.properties.as_deref().unwrap_or_default() {
            let record = store
                .symbol(*symbol)
                .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
            let links = store
                .value_symbol_links(*symbol)
                .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
            let property_type = links
                .resolved_type
                .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?;
            validate_property_type(
                store,
                property_type,
                &mut validating_property_types,
                &mut validated_property_types,
            )?;
            let property_flags = store
                .type_payload(property_type)
                .ok_or(IntersectionTypeError::MalformedConstituent(*type_))?
                .flags();
            let source = SourceProperty {
                symbol: *symbol,
                name: record.name().to_owned(),
                type_: property_type,
                symbol_flags: record.flags(),
                check_flags: record.check_flags(),
                literal: property_type == boolean_type
                    || property_flags.intersects(TypeFlags::UNIT),
                explicit_never: property_flags == TypeFlags::NEVER,
            };
            if let Some(group) = groups.iter_mut().find(|group| group.name == source.name) {
                if !group
                    .sources
                    .iter()
                    .any(|existing| existing.symbol == source.symbol)
                {
                    group.sources.push(source);
                }
            } else {
                groups.push(PropertyGroup {
                    name: source.name.clone(),
                    sources: vec![source],
                });
            }
        }
    }

    groups
        .into_iter()
        .map(|group| {
            if let [source] = group.sources.as_slice() {
                return Ok(ExpectedProperty::Borrowed(source.symbol));
            }
            let property_types = group
                .sources
                .iter()
                .map(|source| source.type_)
                .collect::<Vec<_>>();
            let merged_type = intersect_property_types(store, &property_types)?;
            let flags = SymbolFlags::PROPERTY
                | if group
                    .sources
                    .iter()
                    .all(|source| source.symbol_flags.contains(SymbolFlags::OPTIONAL))
                {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            let mut check_flags = CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC;
            if group
                .sources
                .iter()
                .all(|source| source.check_flags.contains(CheckFlags::READONLY))
            {
                check_flags |= CheckFlags::READONLY;
            }
            if property_types
                .first()
                .is_some_and(|first| property_types.iter().any(|type_| type_ != first))
            {
                check_flags |= CheckFlags::HAS_NON_UNIFORM_TYPE;
            }
            if group.sources.iter().any(|source| source.literal) {
                check_flags |= CheckFlags::HAS_LITERAL_TYPE;
            }
            if group.sources.iter().any(|source| source.explicit_never) {
                check_flags |= CheckFlags::HAS_NEVER_TYPE;
            }
            let declarations = group
                .sources
                .iter()
                .flat_map(|source| {
                    store
                        .symbol(source.symbol)
                        .and_then(|symbol| symbol.declarations())
                        .unwrap_or_default()
                        .iter()
                        .copied()
                })
                .collect::<Vec<_>>();
            Ok(ExpectedProperty::Synthetic {
                name: group.name,
                type_: merged_type,
                flags,
                check_flags,
                declarations: (!declarations.is_empty()).then_some(declarations),
            })
        })
        .collect()
}

fn validate_property_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    validating: &mut HashSet<TypeId>,
    validated: &mut HashSet<TypeId>,
) -> Result<(), IntersectionTypeError> {
    if validated.contains(&type_) {
        return Ok(());
    }
    if !validating.insert(type_) {
        return Err(IntersectionTypeError::UnsupportedPropertyType(type_));
    }
    let result = validate_property_type_worker(store, type_, validating, validated);
    assert!(validating.remove(&type_));
    if result.is_ok() {
        validated.insert(type_);
    }
    result
}

fn validate_property_type_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    validating: &mut HashSet<TypeId>,
    validated: &mut HashSet<TypeId>,
) -> Result<(), IntersectionTypeError> {
    if store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| type_ == bootstrap.boolean_type)
    {
        // The canonical `boolean` primitive is represented by its fixed
        // `false | true` union. Admit only that exact bootstrap identity.
        return Ok(());
    }
    let record = store
        .type_payload(type_)
        .ok_or(IntersectionTypeError::UnsupportedPropertyType(type_))?;
    if let TypeData::Union(union) = record.data() {
        store
            .validate_union_constituent(type_)
            .map_err(|_| IntersectionTypeError::UnsupportedPropertyType(type_))?;
        for constituent in &union.union.types {
            validate_property_type(store, *constituent, validating, validated)?;
        }
        return Ok(());
    }
    let flags = record.flags();
    if matches!(
        flags,
        TypeFlags::ANY
            | TypeFlags::UNKNOWN
            | TypeFlags::UNDEFINED
            | TypeFlags::NULL
            | TypeFlags::VOID
            | TypeFlags::STRING
            | TypeFlags::NUMBER
            | TypeFlags::BIG_INT
            | TypeFlags::BOOLEAN
            | TypeFlags::ES_SYMBOL
            | TypeFlags::STRING_LITERAL
            | TypeFlags::NUMBER_LITERAL
            | TypeFlags::BIG_INT_LITERAL
            | TypeFlags::BOOLEAN_LITERAL
            | TypeFlags::UNIQUE_ES_SYMBOL
            | TypeFlags::NEVER
    ) {
        return Ok(());
    }
    if flags == TypeFlags::OBJECT {
        return match validate_resolved_declared_property_object(store, type_) {
            DeclaredPropertyObjectValidation::Valid(_) => {
                let property_types = resolved_declared_property_types(store, type_)
                    .ok_or(IntersectionTypeError::UnsupportedPropertyType(type_))?;
                for property_type in property_types {
                    validate_property_type(store, property_type, validating, validated)?;
                }
                Ok(())
            }
            DeclaredPropertyObjectValidation::NotDeclared
            | DeclaredPropertyObjectValidation::Malformed => {
                Err(IntersectionTypeError::UnsupportedPropertyType(type_))
            }
        };
    }
    Err(IntersectionTypeError::UnsupportedPropertyType(type_))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveDomain {
    String,
    Number,
    BigInt,
    Boolean,
    Symbol,
    Undefined,
    Null,
}

fn primitive_domain(flags: TypeFlags) -> Option<(PrimitiveDomain, bool)> {
    match flags {
        TypeFlags::STRING => Some((PrimitiveDomain::String, false)),
        TypeFlags::STRING_LITERAL => Some((PrimitiveDomain::String, true)),
        TypeFlags::NUMBER => Some((PrimitiveDomain::Number, false)),
        TypeFlags::NUMBER_LITERAL => Some((PrimitiveDomain::Number, true)),
        TypeFlags::BIG_INT => Some((PrimitiveDomain::BigInt, false)),
        TypeFlags::BIG_INT_LITERAL => Some((PrimitiveDomain::BigInt, true)),
        TypeFlags::BOOLEAN => Some((PrimitiveDomain::Boolean, false)),
        TypeFlags::BOOLEAN_LITERAL => Some((PrimitiveDomain::Boolean, true)),
        TypeFlags::ES_SYMBOL => Some((PrimitiveDomain::Symbol, false)),
        TypeFlags::UNIQUE_ES_SYMBOL => Some((PrimitiveDomain::Symbol, true)),
        TypeFlags::UNDEFINED => Some((PrimitiveDomain::Undefined, true)),
        TypeFlags::NULL => Some((PrimitiveDomain::Null, true)),
        // `void` is the wider member of the pinned `void & undefined`
        // reduction, so it shares the domain while remaining the base.
        TypeFlags::VOID => Some((PrimitiveDomain::Undefined, false)),
        _ => None,
    }
}

fn literal_values_equal(store: &CanonicalTypeMapperStore, left: TypeId, right: TypeId) -> bool {
    let value = |type_| match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::Literal(literal)) => Some(&literal.value),
        _ => None,
    };
    match (value(left), value(right)) {
        (Some(left), Some(right)) => left == right,
        _ => left == right,
    }
}

fn intersect_property_types(
    store: &CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<TypeId, IntersectionTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(IntersectionTypeError::BootstrapUninitialized)?;
    if let Some(first) = types.first().copied()
        && types.iter().all(|type_| *type_ == first)
    {
        return Ok(first);
    }
    if types.iter().any(|type_| {
        *type_ != bootstrap.boolean_type
            && matches!(
                store.type_payload(*type_).map(TypeRecord::data),
                Some(TypeData::Union(_))
            )
    }) {
        return intersect_union_property_types(store, types);
    }
    for type_ in types {
        if *type_ == bootstrap.boolean_type {
            continue;
        }
        let flags = store
            .type_payload(*type_)
            .ok_or(IntersectionTypeError::UnsupportedPropertyType(*type_))?
            .flags();
        if !matches!(
            flags,
            TypeFlags::ANY
                | TypeFlags::UNKNOWN
                | TypeFlags::UNDEFINED
                | TypeFlags::NULL
                | TypeFlags::VOID
                | TypeFlags::STRING
                | TypeFlags::NUMBER
                | TypeFlags::BIG_INT
                | TypeFlags::BOOLEAN
                | TypeFlags::ES_SYMBOL
                | TypeFlags::STRING_LITERAL
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BIG_INT_LITERAL
                | TypeFlags::BOOLEAN_LITERAL
                | TypeFlags::UNIQUE_ES_SYMBOL
                | TypeFlags::NEVER
        ) {
            return Err(IntersectionTypeError::UnsupportedPropertyType(*type_));
        }
    }
    if types.contains(&bootstrap.never_type) {
        return Ok(bootstrap.never_type);
    }
    if types.contains(&bootstrap.any_type) {
        return Ok(bootstrap.any_type);
    }
    let significant = types
        .iter()
        .copied()
        .filter(|type_| *type_ != bootstrap.unknown_type)
        .collect::<Vec<_>>();
    if significant.is_empty() {
        return Ok(bootstrap.unknown_type);
    }

    let mut domain = None;
    let mut base = None;
    let mut literal = None;
    for type_ in significant {
        let flags = store
            .type_payload(type_)
            .ok_or(IntersectionTypeError::UnsupportedPropertyType(type_))?
            .flags();
        let (next_domain, is_literal) = if type_ == bootstrap.boolean_type {
            (PrimitiveDomain::Boolean, false)
        } else {
            let Some(classification) = primitive_domain(flags) else {
                return Err(IntersectionTypeError::UnsupportedPropertyType(type_));
            };
            classification
        };
        if domain.is_some_and(|domain| domain != next_domain) {
            return Ok(bootstrap.never_type);
        }
        domain = Some(next_domain);
        if is_literal {
            if let Some(previous) = literal {
                if !literal_values_equal(store, previous, type_) {
                    return Ok(bootstrap.never_type);
                }
            } else {
                literal = Some(type_);
            }
        } else {
            base = Some(type_);
        }
    }
    Ok(literal
        .or(base)
        .expect("a significant primitive type was classified"))
}

fn intersect_union_property_types(
    store: &CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<TypeId, IntersectionTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(IntersectionTypeError::BootstrapUninitialized)?;
    let mut candidates = vec![bootstrap.unknown_type];

    for type_ in types {
        let record = store
            .type_payload(*type_)
            .ok_or(IntersectionTypeError::UnsupportedPropertyType(*type_))?;
        let members = if *type_ != bootstrap.boolean_type
            && let TypeData::Union(union) = record.data()
        {
            union.union.types.as_slice()
        } else {
            std::slice::from_ref(type_)
        };
        if candidates
            .len()
            .checked_mul(members.len())
            .is_none_or(|count| count >= 100_000)
        {
            return Err(IntersectionTypeError::UnsupportedPropertyType(*type_));
        }

        let mut next = Vec::new();
        for candidate in &candidates {
            for member in members {
                let intersection = intersect_property_types(store, &[*candidate, *member])?;
                if intersection != bootstrap.never_type && !next.contains(&intersection) {
                    next.push(intersection);
                }
            }
        }
        if next.is_empty() {
            return Ok(bootstrap.never_type);
        }
        candidates = next;
    }

    if let [candidate] = candidates.as_slice() {
        return Ok(*candidate);
    }
    for type_ in types {
        let Some(TypeData::Union(union)) = store.type_payload(*type_).map(TypeRecord::data) else {
            continue;
        };
        if union.union.types.len() == candidates.len()
            && candidates
                .iter()
                .all(|candidate| union.union.types.contains(candidate))
        {
            return Ok(*type_);
        }
    }
    for (candidate, record) in store.types() {
        let TypeData::Union(union) = record.data() else {
            continue;
        };
        if record.alias().is_none()
            && union.origin.is_none()
            && union.union.types.len() == candidates.len()
            && candidates
                .iter()
                .all(|member| union.union.types.contains(member))
            && bootstrap.cached_union_type(&union.union.types) == Some(candidate)
        {
            return Ok(candidate);
        }
    }
    Err(IntersectionTypeError::UnsupportedPropertyType(types[0]))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    };

    fn generic_intersection_context(
        source: &ParseResult,
        file: FileId,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/generic-intersections.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        context
    }

    fn generic_intersection_alias_symbol(
        source: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
        name: &str,
    ) -> SemanticSymbolId {
        let declaration = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &source.arena.get(alias.name)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(source.arena.id(), file, node))
            })
            .unwrap();
        context.file(file).unwrap().1.symbol(declaration).unwrap()
    }

    fn generic_intersection_alias(
        source: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
        name: &str,
    ) -> TypeId {
        let symbol = generic_intersection_alias_symbol(source, context, file, name);
        context
            .store()
            .type_alias_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap()
    }

    fn intersection_cache_state(
        store: &CanonicalTypeMapperStore,
    ) -> (usize, usize, usize, usize, [usize; 26]) {
        (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
        )
    }

    #[test]
    fn deferred_intersections_preserve_cold_references_and_materialize_in_place() {
        let source = parse_source_file(concat!(
            "interface Base<T> { base: T }\n",
            "interface Extra<T> { extra: T }\n",
            "type Left = Base<string>;\n",
            "type Right = Extra<number>;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_405);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let right = generic_intersection_alias(&source, &context, file, "Right");
        let store = context.store_mut_for_test();
        let before = intersection_cache_state(store);

        let deferred = store
            .canonical_deferred_intersection_type(&[left, right], None)
            .unwrap();
        let projection = store.validate_deferred_intersection_type(deferred).unwrap();
        assert_eq!(projection.types, [left, right]);
        assert_eq!(projection.alias_symbol, None);
        assert!(projection.alias_arguments.is_empty());
        assert_eq!(store.type_len(), before.0 + 1);
        assert_eq!(store.mapper_len(), before.1);
        assert_eq!(store.symbol_len(), before.2);
        assert_eq!(store.symbol_store().symbol_table_len(), before.3);
        let TypeData::Intersection(data) = store.type_payload(deferred).unwrap().data() else {
            panic!("expected a deferred intersection")
        };
        assert_eq!(data.intersection.structured, StructuredTypeData::default());
        assert!(data.intersection.property_cache.is_none());
        assert!(data.intersection.resolved_properties.is_none());
        assert!(matches!(
            store.validate_intersection_type(deferred),
            Err(IntersectionTypeError::InvalidCachedIntersection(actual)) if actual == deferred
        ));

        let warm = intersection_cache_state(store);
        assert_eq!(
            store.canonical_deferred_intersection_type(&[left, right], None),
            Ok(deferred),
        );
        assert_eq!(intersection_cache_state(store), warm);

        store
            .resolve_generic_interface_property(left, "base", None)
            .unwrap();
        store
            .resolve_generic_interface_property(right, "extra", None)
            .unwrap();
        assert_eq!(
            store.canonical_intersection_type(&[left, right], None),
            Ok(deferred),
        );
        let resolved = store.validate_intersection_type(deferred).unwrap();
        assert_eq!(resolved.types, [left, right]);
        assert_eq!(resolved.properties.len(), 2);
        assert!(store.validate_deferred_intersection_type(deferred).is_err());

        let resolved_state = intersection_cache_state(store);
        assert_eq!(
            store.canonical_deferred_intersection_type(&[left, right], None),
            Ok(deferred),
        );
        assert_eq!(intersection_cache_state(store), resolved_state);
    }

    #[test]
    fn deferred_intersections_authenticate_transient_generic_interface_owners() {
        let source = parse_source_file(concat!(
            "interface Base<T> { base: T }\n",
            "interface Extra<T> { extra: T }\n",
            "type Left = Base<string>;\n",
            "type Right = Extra<number>;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_408);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let right = generic_intersection_alias(&source, &context, file, "Right");
        let target = validate_direct_generic_reference(context.store(), left)
            .unwrap()
            .target;
        let owner = context
            .store()
            .type_payload(target)
            .and_then(TypeRecord::symbol)
            .unwrap();
        let store = context.store_mut_for_test();
        assert!(store.set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));

        let deferred = store
            .canonical_deferred_intersection_type(&[left, right], None)
            .unwrap();
        assert_eq!(
            store
                .validate_deferred_intersection_type(deferred)
                .unwrap()
                .types,
            [left, right],
        );
        let warm = intersection_cache_state(store);
        assert_eq!(
            store.canonical_deferred_intersection_type(&[left, right], None),
            Ok(deferred),
        );
        assert_eq!(intersection_cache_state(store), warm);

        assert!(store.set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT | SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let poisoned = intersection_cache_state(store);
        assert_eq!(
            store.validate_deferred_intersection_type(deferred),
            Err(IntersectionTypeError::InvalidCachedIntersection(deferred)),
        );
        assert_eq!(
            store.canonical_deferred_intersection_type(&[left, right], None),
            Err(IntersectionTypeError::UnsupportedConstituent(left)),
        );
        assert_eq!(intersection_cache_state(store), poisoned);

        assert!(store.set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        assert_eq!(
            store.canonical_deferred_intersection_type(&[left, right], None),
            Ok(deferred),
        );
        assert_eq!(intersection_cache_state(store), warm);
    }

    #[test]
    fn deferred_intersections_authenticate_binder_parameters_and_alias_argument_order() {
        let source = parse_source_file(concat!(
            "interface Base<T> { value: T }\n",
            "type Left = Base<string>;\n",
            "type Alias<E, T> = E;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_406);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let alias = generic_intersection_alias_symbol(&source, &context, file, "Alias");
        let parameters = context
            .store()
            .type_alias_links(alias)
            .and_then(|links| links.type_parameters.clone())
            .unwrap();
        let [props, element] = parameters.as_slice() else {
            panic!("expected two authenticated alias parameters")
        };
        let (props, element) = (*props, *element);
        let target = validate_direct_generic_reference(context.store(), left)
            .unwrap()
            .target;
        let store = context.store_mut_for_test();
        let generic = store
            .create_direct_generic_reference_type(target, &[element])
            .unwrap();
        let declared = store
            .canonical_deferred_intersection_type(
                &[generic, props],
                Some((alias, &[props, element])),
            )
            .unwrap();
        let projection = store.validate_deferred_intersection_type(declared).unwrap();
        assert_eq!(projection.types, [generic, props]);
        assert_eq!(projection.alias_symbol, Some(alias));
        assert_eq!(projection.alias_arguments, [props, element]);
        let identity = store
            .type_payload(declared)
            .and_then(TypeRecord::alias)
            .and_then(|identity| store.type_alias(identity))
            .unwrap();
        assert_eq!(identity.symbol(), Some(alias));
        assert_eq!(identity.type_arguments(), Some([props, element].as_slice()));

        let reordered = store
            .canonical_deferred_intersection_type(
                &[generic, props],
                Some((alias, &[element, props])),
            )
            .unwrap();
        assert_ne!(declared, reordered);
        let warm = intersection_cache_state(store);
        assert_eq!(
            store.canonical_deferred_intersection_type(
                &[generic, props],
                Some((alias, &[props, element])),
            ),
            Ok(declared),
        );
        assert_eq!(intersection_cache_state(store), warm);
    }

    #[test]
    fn deferred_intersections_reject_forged_alias_and_reverse_cache_without_writes() {
        let source = parse_source_file(concat!(
            "interface Base<T> { value: T }\n",
            "type Left = Base<string>;\n",
            "type Alias<E, T> = E;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_407);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let alias = generic_intersection_alias_symbol(&source, &context, file, "Alias");
        let parameters = context
            .store()
            .type_alias_links(alias)
            .and_then(|links| links.type_parameters.clone())
            .unwrap();
        let [first, second] = parameters.as_slice() else {
            panic!("expected two authenticated alias parameters")
        };
        let (first, second) = (*first, *second);
        let store = context.store_mut_for_test();
        let intersection = store
            .canonical_deferred_intersection_type(&[left, first], Some((alias, &[first, second])))
            .unwrap();
        let identity = store
            .type_payload(intersection)
            .and_then(TypeRecord::alias)
            .unwrap();
        let key = store
            .intersection_keys_by_type
            .remove(&intersection)
            .unwrap();
        let state = intersection_cache_state(store);
        assert_eq!(
            store.validate_deferred_intersection_type(intersection),
            Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection
            )),
        );
        assert_eq!(
            store.canonical_deferred_intersection_type(
                &[left, first],
                Some((alias, &[first, second])),
            ),
            Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection
            )),
        );
        assert_eq!(intersection_cache_state(store), state);
        assert!(
            store
                .intersection_keys_by_type
                .insert(intersection, key)
                .is_none()
        );

        assert!(store.set_type_alias_arguments(identity, Some(vec![second, first])));
        let state = intersection_cache_state(store);
        assert_eq!(
            store.validate_deferred_intersection_type(intersection),
            Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection
            )),
        );
        assert_eq!(
            store.canonical_deferred_intersection_type(
                &[left, first],
                Some((alias, &[first, second])),
            ),
            Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection
            )),
        );
        assert_eq!(intersection_cache_state(store), state);
    }

    #[test]
    fn resolved_generic_interface_intersections_preserve_proxy_properties_and_warm_identity() {
        let source = parse_source_file(concat!(
            "interface Base<T> { base: T; shared: string }\n",
            "interface Extra<T> { extra: T; shared: string }\n",
            "type Left = Base<string>;\n",
            "type Right = Extra<number>;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_402);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let right = generic_intersection_alias(&source, &context, file, "Right");
        let store = context.store_mut_for_test();
        for (reference, names) in [(left, ["base", "shared"]), (right, ["extra", "shared"])] {
            store
                .resolve_generic_interface_members(reference, None)
                .unwrap();
            for name in names {
                assert!(
                    store
                        .resolve_generic_interface_property(reference, name, None)
                        .unwrap()
                        .is_some()
                );
            }
        }

        let intersection = store
            .canonical_intersection_type(&[left, right], None)
            .unwrap();
        let projection = store.validate_intersection_type(intersection).unwrap();
        assert_eq!(projection.types, [left, right]);
        assert_eq!(
            projection
                .properties
                .iter()
                .map(|property| {
                    store
                        .symbol(*property)
                        .and_then(|symbol| symbol.name().as_utf8())
                        .unwrap()
                })
                .collect::<Vec<_>>(),
            ["base", "shared", "extra"],
        );
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        assert_eq!(
            projection
                .properties
                .iter()
                .map(|property| {
                    store
                        .value_symbol_links(*property)
                        .and_then(|links| links.resolved_type)
                        .unwrap()
                })
                .collect::<Vec<_>>(),
            [string, string, number],
        );

        let warm = intersection_cache_state(store);
        assert_eq!(
            store.canonical_intersection_type(&[left, right], None),
            Ok(intersection),
        );
        assert_eq!(
            store.validate_intersection_type(intersection),
            Ok(projection)
        );
        assert_eq!(intersection_cache_state(store), warm);
    }

    #[test]
    fn generic_interface_intersections_reject_cold_members_and_unresolved_proxy_values() {
        let source = parse_source_file(concat!(
            "interface Base<T> { base: T }\n",
            "interface Extra<T> { extra: T }\n",
            "type Left = Base<string>;\n",
            "type Right = Extra<number>;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_403);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let right = generic_intersection_alias(&source, &context, file, "Right");
        let store = context.store_mut_for_test();

        let cold = intersection_cache_state(store);
        assert_eq!(
            store.canonical_intersection_type(&[left, right], None),
            Err(IntersectionTypeError::UnsupportedConstituent(left)),
        );
        assert_eq!(intersection_cache_state(store), cold);

        store.resolve_generic_interface_members(left, None).unwrap();
        store
            .resolve_generic_interface_members(right, None)
            .unwrap();
        let unresolved = intersection_cache_state(store);
        assert_eq!(
            store.canonical_intersection_type(&[left, right], None),
            Err(IntersectionTypeError::UnsupportedConstituent(left)),
        );
        assert_eq!(intersection_cache_state(store), unresolved);

        store
            .resolve_generic_interface_property(left, "base", None)
            .unwrap();
        store
            .resolve_generic_interface_property(right, "extra", None)
            .unwrap();
        assert!(
            store
                .canonical_intersection_type(&[left, right], None)
                .is_ok()
        );
    }

    #[test]
    fn generic_interface_intersections_reject_forged_proxy_caches_without_writes() {
        let source = parse_source_file(concat!(
            "interface Base<T> { base: T }\n",
            "interface Extra<T> { extra: T }\n",
            "type Left = Base<string>;\n",
            "type Right = Extra<number>;\n",
        ));
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let file = FileId::new(4_404);
        let mut context = generic_intersection_context(&source, file);
        let left = generic_intersection_alias(&source, &context, file, "Left");
        let right = generic_intersection_alias(&source, &context, file, "Right");
        let store = context.store_mut_for_test();
        let left_property = store
            .resolve_generic_interface_property(left, "base", None)
            .unwrap()
            .unwrap()
            .symbol();
        store
            .resolve_generic_interface_property(right, "extra", None)
            .unwrap();
        let intersection = store
            .canonical_intersection_type(&[left, right], None)
            .unwrap();
        let original = store.value_symbol_links(left_property).unwrap().clone();
        let wrong = store.intrinsic_bootstrap().unwrap().number_type;

        for (mapper, resolved_type) in [
            (None, original.resolved_type),
            (original.mapper, Some(wrong)),
        ] {
            let mut poisoned = original.clone();
            poisoned.mapper = mapper;
            poisoned.resolved_type = resolved_type;
            assert!(store.set_value_symbol_links(left_property, poisoned));
            let state = intersection_cache_state(store);
            assert_eq!(
                store.canonical_intersection_type(&[left, right], None),
                Err(IntersectionTypeError::MalformedConstituent(left)),
            );
            assert_eq!(
                store.validate_intersection_type(intersection),
                Err(IntersectionTypeError::InvalidCachedIntersection(
                    intersection
                )),
            );
            assert_eq!(intersection_cache_state(store), state);
            assert!(store.set_value_symbol_links(left_property, original.clone()));
        }

        assert_eq!(
            store.canonical_intersection_type(&[left, right], None),
            Ok(intersection),
        );
    }

    #[test]
    fn finite_literal_property_unions_reduce_to_existing_canonical_identities() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let left = store
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let middle = store
            .regular_string_literal_type("middle".to_owned())
            .unwrap();
        let right = store
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        let wide = store
            .literal_union_type(&[left, middle, right], None)
            .unwrap();
        let narrow = store.literal_union_type(&[left, right], None).unwrap();
        let alternate = store.literal_union_type(&[middle, right], None).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let never = store.intrinsic_bootstrap().unwrap().never_type;

        let mut visiting = HashSet::new();
        let mut validated = HashSet::new();
        assert_eq!(
            validate_property_type(&store, wide, &mut visiting, &mut validated),
            Ok(()),
        );
        assert_eq!(
            intersect_property_types(&store, &[wide, narrow]),
            Ok(narrow)
        );
        assert_eq!(
            intersect_property_types(&store, &[narrow, alternate]),
            Ok(right),
        );
        assert_eq!(intersect_property_types(&store, &[wide, string]), Ok(wide));
        assert_eq!(intersect_property_types(&store, &[wide, number]), Ok(never));
    }

    #[test]
    fn callable_intersections_preserve_order_deduplicate_signatures_and_reject_poison() {
        let source = parse_source_file(concat!(
            "type First = (value: string) => number;\n",
            "type Second = (value: number) => string;\n",
            "type Duplicate = (value: string) => number;\n",
            "type Shape = { marker: boolean };\n",
        ));
        assert!(source.diagnostics.is_empty());
        let file = FileId::new(4_401);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/callable-intersections.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();

        let alias_type = |name: &str| {
            let declaration = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &source.arena.get(alias.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(source.arena.id(), file, node))
                })
                .unwrap();
            let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let symbol = context.store().get_merged_symbol(raw).unwrap();
            context
                .store()
                .type_alias_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap()
        };
        let first = alias_type("First");
        let second = alias_type("Second");
        let duplicate = alias_type("Duplicate");
        let shape = alias_type("Shape");
        let callable_signature = |type_| {
            context
                .store()
                .type_payload(type_)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .and_then(|signatures| signatures.first().copied())
                .unwrap()
        };
        let signatures = [
            callable_signature(first),
            callable_signature(second),
            callable_signature(duplicate),
        ];
        for signature in signatures {
            context.get_return_type_of_signature(signature).unwrap();
        }

        let store = context.store_mut_for_test();
        let constituents = [first, second, duplicate, shape];
        let intersection = store
            .canonical_intersection_type(&constituents, None)
            .unwrap();
        let projection = store.validate_intersection_type(intersection).unwrap();
        assert_eq!(projection.types.as_slice(), constituents.as_slice());
        assert_eq!(projection.properties.len(), 1);
        assert_eq!(
            store
                .symbol(projection.properties[0])
                .unwrap()
                .name()
                .as_utf8(),
            Some("marker"),
        );
        let structured = store
            .type_payload(intersection)
            .and_then(|record| record.data().structured())
            .unwrap();
        assert_eq!(structured.call_signature_count, 2);
        assert_eq!(structured.signatures.as_deref(), Some(&signatures[..2]));

        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
        );
        assert_eq!(
            store.canonical_intersection_type(&constituents, None),
            Ok(intersection),
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
            ),
            warm,
        );

        assert!(store.set_structured_type_members(
            intersection,
            None,
            None,
            Some(vec![signatures[1], signatures[0]]),
            None,
            None,
        ));
        let poisoned = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
        );
        assert_eq!(
            store.canonical_intersection_type(&constituents, None),
            Err(IntersectionTypeError::InvalidCachedIntersection(
                intersection
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
            ),
            poisoned,
        );
    }
}
