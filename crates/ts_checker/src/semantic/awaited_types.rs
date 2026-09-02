//! Promise adoption through the canonical property, signature, and union queries.

use std::collections::{HashMap, HashSet};

use ts_binder::{EscapedName, SymbolFlags};

use super::super::{
    RelationKind, RelationUnavailable, SourceCheckError,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    callables::ValidatedSingleCallable,
    calls::{DirectCallError, try_get_type_at_position},
    classes::{
        ClassError, execute_nongeneric_class_member_query, plan_nongeneric_class_member_query,
        preflight_nongeneric_class_member_query,
    },
    intersection_types::IntersectionTypeError,
    object_members::{
        resolve_object_property_by_key, resolve_object_property_by_key_with_source,
    },
    reference_types::validate_direct_generic_reference,
    relater::SourceRelationError,
    signatures::ElementFlags,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};
use super::{
    CanonicalCheckerOptions, CanonicalTypeQuery, CanonicalTypeQueryOptions, DeclaredTypeError,
    SignatureId, TypeId, TypeNodeUnavailable, TypeQueryPlanner,
    cached_ordinary_type_parameter_owner, preflight_class_or_interface_reference,
    source_class_type_query_error, type_node_unavailable,
};

/// Semantic failures stay separate from unsupported or invalid checker state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AwaitedTypeError {
    InvalidThenable {
        type_: TypeId,
        this_type: Option<TypeId>,
    },
    CircularThenable(TypeId),
    UnsupportedGeneric(TypeId),
    UnsupportedSignatureUnion(TypeId),
    UnsupportedSignature(SignatureId),
    InvalidType(TypeId),
    InvalidSignature(SignatureId),
    Query(DeclaredTypeError),
    Relation(RelationUnavailable),
    Source(SourceCheckError),
}

impl std::fmt::Display for AwaitedTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidThenable { type_, .. } => write!(formatter, "invalid thenable {type_:?}"),
            Self::CircularThenable(type_) => write!(formatter, "circular thenable {type_:?}"),
            Self::UnsupportedGeneric(type_) => {
                write!(formatter, "unsupported generic awaited type {type_:?}")
            }
            Self::UnsupportedSignatureUnion(type_) => {
                write!(formatter, "unsupported thenable signature union {type_:?}")
            }
            Self::UnsupportedSignature(signature) => {
                write!(formatter, "unsupported thenable signature {signature:?}")
            }
            Self::InvalidType(type_) => write!(formatter, "invalid awaited type {type_:?}"),
            Self::InvalidSignature(signature) => {
                write!(formatter, "invalid thenable signature {signature:?}")
            }
            Self::Query(error) => error.fmt(formatter),
            Self::Relation(error) => error.fmt(formatter),
            Self::Source(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for AwaitedTypeError {}

impl From<DeclaredTypeError> for AwaitedTypeError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::Query(error)
    }
}

impl From<RelationUnavailable> for AwaitedTypeError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<SourceCheckError> for AwaitedTypeError {
    fn from(error: SourceCheckError) -> Self {
        match error {
            SourceCheckError::DeclaredType(error) => Self::Query(error),
            SourceCheckError::RelationUnavailable(error) => Self::Relation(error),
            error => Self::Source(error),
        }
    }
}

impl From<LiteralTypeCacheError> for AwaitedTypeError {
    fn from(error: LiteralTypeCacheError) -> Self {
        SourceCheckError::from(error).into()
    }
}

impl From<SourceRelationError<DeclaredTypeError>> for AwaitedTypeError {
    fn from(error: SourceRelationError<DeclaredTypeError>) -> Self {
        match error {
            SourceRelationError::Relation(error) => Self::Relation(error),
            SourceRelationError::Source(error) => Self::Query(error),
        }
    }
}

enum AwaitedWork {
    Enter(TypeId),
    Promise { input: TypeId, promised: TypeId },
    Union { input: TypeId, members: Vec<TypeId> },
}

/// Only the first parameter and `this` are needed to adopt a thenable.
struct AwaitedSignature {
    first_parameter: Option<TypeId>,
    this_type: Option<TypeId>,
    generic: bool,
}

impl CanonicalTypeQuery<'_, '_, '_, '_> {
    /// Uses the caller's source options and session. No alias wrapper is created.
    pub(in crate::semantic) fn get_awaited_type_no_alias(
        &mut self,
        input: TypeId,
        options: CanonicalCheckerOptions,
    ) -> Result<TypeId, AwaitedTypeError> {
        if CanonicalTypeQueryOptions::from(options) != self.options
            || self
                .store
                .intrinsic_bootstrap()
                .is_none_or(|bootstrap| bootstrap.options != options.intrinsic)
            || self.global_types.is_none()
            || self.instantiation_session.is_none()
            || !self.pending_function_parameters.is_empty()
        {
            return Err(type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery).into());
        }
        self.reject_type_reference_alias_capabilities()?;
        self.begin_source_query();
        let result = self.awaited_type_worker(input, options);
        self.finish_source_query();
        result
    }

    fn awaited_type_worker(
        &mut self,
        input: TypeId,
        options: CanonicalCheckerOptions,
    ) -> Result<TypeId, AwaitedTypeError> {
        let mut active = HashSet::new();
        let mut completed = HashMap::new();
        let mut pending = vec![AwaitedWork::Enter(input)];
        while let Some(work) = pending.pop() {
            match work {
                AwaitedWork::Enter(type_) => {
                    if active.contains(&type_) {
                        return Err(AwaitedTypeError::CircularThenable(type_));
                    }
                    if completed.contains_key(&type_) {
                        continue;
                    }
                    let record = self
                        .store
                        .type_payload(type_)
                        .ok_or(AwaitedTypeError::InvalidType(type_))?;
                    if record.flags().intersects(
                        TypeFlags::ANY
                            | TypeFlags::UNKNOWN
                            | TypeFlags::NEVER
                            | TypeFlags::PRIMITIVE
                            | TypeFlags::NON_PRIMITIVE,
                    ) {
                        self.store.validate_union_constituent_with_global_types(
                            self.global_types
                                .as_ref()
                                .expect("the caller supplied globals"),
                            type_,
                        )?;
                        completed.insert(type_, type_);
                    } else if let TypeData::Union(union) = record.data() {
                        let members = union.union.types.clone();
                        self.store.validate_union_query_metadata(type_)?;
                        active.insert(type_);
                        pending.push(AwaitedWork::Union {
                            input: type_,
                            members: members.clone(),
                        });
                        pending.extend(members.into_iter().rev().map(AwaitedWork::Enter));
                    } else if let TypeData::TypeParameter(parameter) = record.data() {
                        if let Some(owner) = cached_ordinary_type_parameter_owner(self.store, type_) {
                            if self.get_declared_type_of_symbol(owner)? != type_ {
                                return Err(AwaitedTypeError::InvalidType(type_));
                            }
                        } else if parameter.is_this_type {
                            let owner = record
                                .symbol()
                                .ok_or(AwaitedTypeError::InvalidType(type_))?;
                            let constraint = parameter.constraint;
                            let declared = self.get_declared_type_of_symbol(owner)?;
                            if constraint != Some(declared)
                                || !self.store.type_payload(declared).is_some_and(|record| {
                                    matches!(record.data(), TypeData::Interface(interface)
                                        if interface.this_type == Some(type_))
                                })
                            {
                                return Err(AwaitedTypeError::InvalidType(type_));
                            }
                        } else {
                            return Err(AwaitedTypeError::UnsupportedGeneric(type_));
                        }
                        completed.insert(type_, type_);
                    } else if record.flags().intersects(TypeFlags::INSTANTIABLE) {
                        return Err(AwaitedTypeError::UnsupportedGeneric(type_));
                    } else if self.awaited_is_primitive_intersection(type_)? {
                        completed.insert(type_, type_);
                    } else if let Some(promised) = self.promised_type_of_promise(type_, options)? {
                        if promised == type_ || active.contains(&promised) {
                            return Err(AwaitedTypeError::CircularThenable(promised));
                        }
                        active.insert(type_);
                        pending.push(AwaitedWork::Promise {
                            input: type_,
                            promised,
                        });
                        pending.push(AwaitedWork::Enter(promised));
                    } else {
                        completed.insert(type_, type_);
                    }
                }
                AwaitedWork::Promise { input, promised } => {
                    let result = completed
                        .get(&promised)
                        .copied()
                        .ok_or(AwaitedTypeError::InvalidType(promised))?;
                    active.remove(&input);
                    completed.insert(input, result);
                }
                AwaitedWork::Union { input, members } => {
                    let results = members
                        .iter()
                        .map(|member| {
                            completed
                                .get(member)
                                .copied()
                                .ok_or(AwaitedTypeError::InvalidType(*member))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let result = if results == members {
                        input
                    } else {
                        self.awaited_union(&results, UnionReduction::Literal)?
                    };
                    active.remove(&input);
                    completed.insert(input, result);
                }
            }
        }
        completed
            .get(&input)
            .copied()
            .ok_or(AwaitedTypeError::InvalidType(input))
    }

    fn awaited_union(
        &mut self,
        types: &[TypeId],
        reduction: UnionReduction,
    ) -> Result<TypeId, AwaitedTypeError> {
        let mut demanded = HashSet::new();
        loop {
            let result = self
                .store
                .expression_union_type_with_global_types_and_session(
                    self.global_types
                        .as_ref()
                        .expect("the caller supplied globals"),
                    types,
                    reduction,
                    self.instantiation_session
                        .as_deref_mut()
                        .expect("the caller supplied a session"),
                );
            match result {
                Ok(type_) => return Ok(type_),
                Err(error @ LiteralTypeCacheError::UnsupportedUnionConstituent(type_)) => {
                    if !demanded.insert(type_) || !self.prepare_awaited_union_class(type_)? {
                        return Err(error.into());
                    }
                }
                Err(error) => return Err(error.into()),
            }
        }
    }

    /// Callback values can reach a class before an annotation union prepares its members.
    fn prepare_awaited_union_class(&mut self, type_: TypeId) -> Result<bool, AwaitedTypeError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        if !matches!(record.data(), TypeData::Interface(_))
            || record.object_flags() != (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
        {
            return Ok(false);
        }
        let owner = record
            .symbol()
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        if self.get_declared_type_of_symbol(owner)? != type_ {
            return Err(AwaitedTypeError::InvalidType(type_));
        }
        let declaration = self
            .store
            .symbol(owner)
            .and_then(|owner| owner.value_declaration())
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        let plan = match plan_nongeneric_class_member_query(self.store, self.host, owner) {
            Ok(plan) => plan,
            Err(ClassError::Unsupported(_)) => return Ok(false),
            Err(error) => {
                return Err(source_class_type_query_error(error, declaration, owner).into());
            }
        };
        preflight_nongeneric_class_member_query(self.store, self.host, &plan)
            .map_err(|error| source_class_type_query_error(error, declaration, owner))?;
        let members = execute_nongeneric_class_member_query(self.store, self.host, &plan)
            .map_err(|error| source_class_type_query_error(error, declaration, owner))?;
        if members.shells().instance_type() != type_ {
            return Err(AwaitedTypeError::InvalidType(type_));
        }
        Ok(true)
    }

    fn awaited_is_primitive_intersection(
        &mut self,
        type_: TypeId,
    ) -> Result<bool, AwaitedTypeError> {
        let Some(TypeData::Intersection(intersection)) =
            self.store.type_payload(type_).map(|record| record.data())
        else {
            return Ok(false);
        };
        let mut pending = intersection.intersection.types.clone();
        let mut seen = HashSet::new();
        while let Some(member) = pending.pop() {
            if !seen.insert(member) {
                continue;
            }
            let record = self
                .store
                .type_payload(member)
                .ok_or(AwaitedTypeError::InvalidType(member))?;
            if record
                .flags()
                .intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
                || matches!(record.data(), TypeData::Mapped(_))
            {
                return Err(AwaitedTypeError::UnsupportedGeneric(type_));
            }
            match record.data() {
                TypeData::Union(union) => pending.extend_from_slice(&union.union.types),
                TypeData::Intersection(intersection) => {
                    pending.extend_from_slice(&intersection.intersection.types);
                }
                _ => {}
            }
            if self
                .store
                .canonical_tuple_shape(member)
                .map_err(|_| AwaitedTypeError::InvalidType(member))?
                .is_some_and(|tuple| tuple.combined_flags().intersects(ElementFlags::VARIADIC))
            {
                return Err(AwaitedTypeError::UnsupportedGeneric(type_));
            }
        }
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .expect("the query has bootstrap types");
        let primitives = [
            bootstrap.number_type,
            bootstrap.bigint_type,
            bootstrap.string_type,
            bootstrap.boolean_type,
            bootstrap.void_type,
            bootstrap.never_type,
            bootstrap.null_type,
            bootstrap.undefined_type,
            bootstrap.es_symbol_type,
        ];
        for primitive in primitives {
            if self
                .relate_source_types(type_, primitive, RelationKind::Assignable)?
                .related()
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn awaited_without_nullish(&mut self, type_: TypeId) -> Result<TypeId, AwaitedTypeError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        let members = match record.data() {
            TypeData::Union(union) => {
                self.store.validate_union_query_metadata(type_)?;
                union.union.types.clone()
            }
            _ => vec![type_],
        };
        let mut retained = Vec::new();
        for member in &members {
            let record = self
                .store
                .type_payload(*member)
                .ok_or(AwaitedTypeError::InvalidType(*member))?;
            if !record
                .flags()
                .intersects(TypeFlags::NULL | TypeFlags::UNDEFINED | TypeFlags::VOID)
            {
                retained.push(*member);
            }
        }
        if retained == members {
            Ok(type_)
        } else {
            self.awaited_union(&retained, UnionReduction::Literal)
        }
    }

    fn awaited_promise_argument(&mut self, type_: TypeId) -> Result<Option<TypeId>, AwaitedTypeError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        let Some(symbol) = record.symbol() else {
            return Ok(None);
        };
        let global = self
            .store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| self.store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Promise"))
            .and_then(|symbol| self.store.get_merged_symbol(symbol));
        if global != Some(symbol) {
            return Ok(None);
        }
        let anchor = self
            .store
            .symbol(symbol)
            .and_then(|record| record.declarations())
            .and_then(|declarations| declarations.first())
            .copied()
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        let count = preflight_class_or_interface_reference(
            self.store,
            self.host,
            symbol,
            self.symbol_flags(symbol)?,
        )?;
        TypeQueryPlanner::new(
            self.store,
            self.host,
            self.array_type,
            self.global_types
                .as_ref()
                .map(CanonicalArrayTargets::from_global_types),
            self.options.strict_builtin_iterator_return,
            &self.type_reference_alias_targets,
        )
        .preflight_default_library_promise_reference(anchor, symbol, count)?;
        let reference = validate_direct_generic_reference(self.store, type_)
            .map_err(|_| AwaitedTypeError::InvalidType(type_))?;
        let [argument] = reference.type_arguments.as_slice() else {
            return Err(AwaitedTypeError::InvalidType(type_));
        };
        Ok(Some(*argument))
    }

    fn awaited_then_type(
        &mut self,
        type_: TypeId,
        options: CanonicalCheckerOptions,
    ) -> Result<Option<TypeId>, AwaitedTypeError> {
        let globals = self
            .global_types
            .clone()
            .expect("the caller supplied globals");
        let key = EscapedName::source("then");
        let mut demanded = HashSet::new();
        let property = loop {
            let session = self
                .instantiation_session
                .as_deref_mut()
                .expect("the caller supplied a session");
            let record = self
                .store
                .type_payload(type_)
                .ok_or(AwaitedTypeError::InvalidType(type_))?;
            let result = if record.symbol().is_none() {
                resolve_object_property_by_key(
                    self.store,
                    Some(&globals),
                    type_,
                    key.as_ref(),
                    session,
                )
                .map_err(SourceCheckError::from)
            } else {
                resolve_object_property_by_key_with_source(
                    self.store,
                    self.host,
                    &globals,
                    options,
                    type_,
                    key.as_ref(),
                    session,
                    self.diagnostics,
                )
            };
            match result {
                Ok(property) => break property,
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::UnresolvedPropertyType(symbol),
                )) if demanded.insert(symbol) => {
                    if self.symbol_flags(symbol)?.contains(SymbolFlags::METHOD) {
                        self.get_type_of_interface_method(symbol)?;
                    } else {
                        self.get_type_of_declared_value(symbol)?;
                    }
                }
                Err(error) => return Err(error.into()),
            }
        };
        let Some(property) = property else {
            return Ok(None);
        };
        if property.optional && options.intrinsic.strict_null_checks {
            let undefined = self
                .store
                .intrinsic_bootstrap()
                .expect("the query has bootstrap types")
                .undefined_or_missing_type;
            return self
                .awaited_union(&[property.type_, undefined], UnionReduction::Literal)
                .map(Some);
        }
        Ok(Some(property.type_))
    }

    fn promised_type_of_promise(
        &mut self,
        type_: TypeId,
        options: CanonicalCheckerOptions,
    ) -> Result<Option<TypeId>, AwaitedTypeError> {
        if let Some(argument) = self.awaited_promise_argument(type_)? {
            return Ok(Some(argument));
        }
        let Some(then_type) = self.awaited_then_type(type_, options)? else {
            return Ok(None);
        };
        if self
            .store
            .type_payload(then_type)
            .is_some_and(|record| record.flags().intersects(TypeFlags::ANY))
        {
            self.store.validate_union_constituent_with_global_types(
                self.global_types
                    .as_ref()
                    .expect("the caller supplied globals"),
                then_type,
            )?;
            return Ok(None);
        }
        let signatures = self.awaited_signatures(then_type)?;
        if signatures.is_empty() {
            let non_nullish = self.awaited_without_nullish(then_type)?;
            return if self.awaited_signatures(non_nullish)?.is_empty() {
                Ok(None)
            } else {
                Err(AwaitedTypeError::InvalidThenable {
                    type_,
                    this_type: None,
                })
            };
        }
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .expect("the query has bootstrap types");
        let void_type = bootstrap.void_type;
        let never_type = bootstrap.never_type;
        let mut callbacks = Vec::new();
        let mut this_type_for_error = None;
        for signature in signatures {
            if let Some(this_type) = signature.this_type
                && this_type != void_type
                && !self
                    .relate_source_types(type_, this_type, RelationKind::Subtype)?
                    .related()
            {
                this_type_for_error = Some(this_type);
            } else {
                callbacks.push(signature.first_parameter.unwrap_or(never_type));
            }
        }
        if callbacks.is_empty() {
            return Err(AwaitedTypeError::InvalidThenable {
                type_,
                this_type: this_type_for_error,
            });
        }
        let callback = self.awaited_union(&callbacks, UnionReduction::Literal)?;
        let callback = self.awaited_without_nullish(callback)?;
        let signatures = self.awaited_signatures(callback)?;
        if signatures.is_empty() {
            return Err(AwaitedTypeError::InvalidThenable {
                type_,
                this_type: None,
            });
        }
        let values = signatures
            .into_iter()
            .map(|signature| signature.first_parameter.unwrap_or(never_type))
            .collect::<Vec<_>>();
        self.awaited_union(&values, UnionReduction::Subtype).map(Some)
    }

    fn awaited_signatures(
        &mut self,
        type_: TypeId,
    ) -> Result<Vec<AwaitedSignature>, AwaitedTypeError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(AwaitedTypeError::InvalidType(type_))?;
        if record.flags().intersects(TypeFlags::INSTANTIABLE) {
            return Err(AwaitedTypeError::UnsupportedGeneric(type_));
        }
        if let TypeData::Union(union) = record.data() {
            let members = union.union.types.clone();
            self.store.validate_union_constituent_with_global_types(
                self.global_types
                    .as_ref()
                    .expect("the caller supplied globals"),
                type_,
            )?;
            self.store.validate_union_query_metadata(type_)?;
            let mut parameters = Vec::new();
            let mut this_types = Vec::new();
            for member in members {
                let signatures = self.awaited_signatures(member)?;
                if signatures.is_empty() {
                    return Ok(Vec::new());
                }
                let [signature] = signatures.as_slice() else {
                    return Err(AwaitedTypeError::UnsupportedSignatureUnion(type_));
                };
                if signature.generic {
                    return Err(AwaitedTypeError::UnsupportedSignatureUnion(type_));
                }
                parameters.extend(signature.first_parameter);
                this_types.extend(signature.this_type);
            }
            // A missing shorter parameter does not constrain the union signature.
            let first_parameter = if parameters.is_empty() {
                None
            } else {
                Some(self.awaited_intersection(type_, &parameters)?)
            };
            let this_type = if this_types.is_empty() {
                None
            } else {
                Some(self.awaited_intersection(type_, &this_types)?)
            };
            return Ok(vec![AwaitedSignature {
                first_parameter,
                this_type,
                generic: false,
            }]);
        }
        let source_interface = match record.data() {
            TypeData::Interface(_) => record.symbol().map(|owner| (owner, type_)),
            TypeData::TypeReference(reference) => reference.object.target.and_then(|target| {
                self.store
                    .type_payload(target)
                    .and_then(|record| record.symbol())
                    .map(|owner| (owner, target))
            }),
            _ => None,
        }
        .filter(|(owner, _)| {
            self.store.symbol(*owner).is_some_and(|owner| {
                owner.flags().contains(SymbolFlags::INTERFACE)
                    && !owner.flags().contains(SymbolFlags::CLASS)
            })
        });
        if let Some((owner, target)) = source_interface
            && self.get_declared_type_of_symbol(owner)? != target
        {
            return Err(AwaitedTypeError::InvalidType(type_));
        }
        let targets = self
            .global_types
            .as_ref()
            .map(CanonicalArrayTargets::from_global_types);
        let signatures = match validate_stored_callable_set_with_array_targets(
            self.store,
            type_,
            targets,
        ) {
            StoredCallableSetValidation::NotCallable => {
                if source_interface.is_some()
                    && self.store.type_payload(type_).is_some_and(|record| {
                        !record.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
                    })
                {
                    return Err(RelationUnavailable::UnresolvedFunctionType(type_).into());
                }
                self.store.validate_union_constituent_with_global_types(
                    self.global_types
                        .as_ref()
                        .expect("the caller supplied globals"),
                    type_,
                )?;
                return Ok(Vec::new());
            }
            StoredCallableSetValidation::Pending { .. } => {
                return Err(RelationUnavailable::UnresolvedFunctionType(type_).into());
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(RelationUnavailable::MalformedFunctionType(type_).into());
            }
            StoredCallableSetValidation::Valid { projection, .. } => projection.call_signatures,
        };
        signatures
            .iter()
            .map(|signature| self.awaited_signature(signature))
            .collect()
    }

    fn awaited_signature(
        &mut self,
        callable: &ValidatedSingleCallable,
    ) -> Result<AwaitedSignature, AwaitedTypeError> {
        let signature = self
            .store
            .signature(callable.signature)
            .ok_or(AwaitedTypeError::InvalidSignature(callable.signature))?;
        let generic = !signature.type_parameters().is_empty();
        let has_parameters = !signature.parameters().is_empty();
        let this_type = signature
            .this_parameter()
            .map(|parameter| {
                self.store
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type)
                    .ok_or(RelationUnavailable::UnresolvedPropertyType(parameter))
            })
            .transpose()?;
        let first_parameter = try_get_type_at_position(
            self.store,
            self.global_types.as_ref(),
            callable,
            0,
        )
        .map_err(|error| match error {
            DirectCallError::Relation(error) => AwaitedTypeError::Relation(error),
            DirectCallError::Unsupported(_) => {
                AwaitedTypeError::UnsupportedSignature(callable.signature)
            }
            DirectCallError::Invariant(_) => {
                AwaitedTypeError::InvalidSignature(callable.signature)
            }
        })?;
        if has_parameters && first_parameter.is_none() {
            return Err(AwaitedTypeError::UnsupportedSignature(callable.signature));
        }
        Ok(AwaitedSignature {
            first_parameter,
            this_type,
            generic,
        })
    }

    fn awaited_intersection(
        &mut self,
        input: TypeId,
        types: &[TypeId],
    ) -> Result<TypeId, AwaitedTypeError> {
        self.store
            .canonical_intersection_type_with_array_targets(
                types,
                None,
                self.global_types
                    .as_ref()
                    .map(CanonicalArrayTargets::from_global_types),
            )
            .map_err(|error| match error {
                IntersectionTypeError::UnsupportedConstituent(_)
                | IntersectionTypeError::UnsupportedPropertyType(_) => {
                    AwaitedTypeError::UnsupportedSignatureUnion(input)
                }
                _ => AwaitedTypeError::InvalidType(input),
            })
    }
}
