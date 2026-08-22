//! Semantic enums and flags used by canonical signature, tuple, and index records.
//!
//! Values are pinned to typescript-go `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

use std::collections::HashSet;

use ts_ast::NodeRef;
use ts_binder::{CheckFlags, SymbolData, SymbolFlags};

use super::{
    ids::{
        IndexInfoId, SemanticStoreId, SemanticSymbolId, SignatureId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena,
    },
    links::ValueSymbolLinks,
    mapper::CanonicalTypeMapperStore,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

macro_rules! impl_flag_operators {
    ($flags:ty) => {
        impl std::ops::BitAnd for $flags {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }

        impl std::ops::BitAndAssign for $flags {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl std::ops::BitOr for $flags {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }

        impl std::ops::BitOrAssign for $flags {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl std::ops::BitXor for $flags {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self::Output {
                Self(self.0 ^ rhs.0)
            }
        }

        impl std::ops::Not for $flags {
            type Output = Self;

            fn not(self) -> Self::Output {
                Self(!self.0)
            }
        }
    };
}

/// Selects call or construct signatures.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum SignatureKind {
    #[default]
    Call = 0,
    Construct = 1,
}

/// Metadata propagated while signatures are instantiated and combined.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct SignatureFlags(u32);

impl SignatureFlags {
    pub const NONE: Self = Self(0);
    pub const HAS_REST_PARAMETER: Self = Self(1 << 0);
    pub const HAS_LITERAL_TYPES: Self = Self(1 << 1);
    pub const CONSTRUCT: Self = Self(1 << 2);
    pub const ABSTRACT: Self = Self(1 << 3);
    pub const IS_INNER_CALL_CHAIN: Self = Self(1 << 4);
    pub const IS_OUTER_CALL_CHAIN: Self = Self(1 << 5);
    pub const IS_UNTYPED_SIGNATURE_IN_JS_FILE: Self = Self(1 << 6);
    pub const IS_NON_INFERRABLE: Self = Self(1 << 7);
    pub const IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE: Self = Self(1 << 8);

    /// Flags copied to instantiated signatures.
    ///
    /// Call-chain position is deliberately excluded so recursive return-type
    /// instantiation does not repeatedly add `undefined`.
    pub const PROPAGATING_FLAGS: Self = Self(
        Self::HAS_REST_PARAMETER.0
            | Self::HAS_LITERAL_TYPES.0
            | Self::CONSTRUCT.0
            | Self::ABSTRACT.0
            | Self::IS_UNTYPED_SIGNATURE_IN_JS_FILE.0
            | Self::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE.0,
    );
    pub const CALL_CHAIN_FLAGS: Self =
        Self(Self::IS_INNER_CALL_CHAIN.0 | Self::IS_OUTER_CALL_CHAIN.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl_flag_operators!(SignatureFlags);

/// The storage and arity behavior of one tuple element.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ElementFlags(u32);

impl ElementFlags {
    pub const NONE: Self = Self(0);
    pub const REQUIRED: Self = Self(1 << 0);
    pub const OPTIONAL: Self = Self(1 << 1);
    pub const REST: Self = Self(1 << 2);
    pub const VARIADIC: Self = Self(1 << 3);

    pub const FIXED: Self = Self(Self::REQUIRED.0 | Self::OPTIONAL.0);
    pub const VARIABLE: Self = Self(Self::REST.0 | Self::VARIADIC.0);
    pub const NON_REQUIRED: Self = Self(Self::OPTIONAL.0 | Self::REST.0 | Self::VARIADIC.0);
    pub const NON_REST: Self = Self(Self::REQUIRED.0 | Self::OPTIONAL.0 | Self::VARIADIC.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl_flag_operators!(ElementFlags);

/// Controls canonical index-type construction and reduction.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct IndexFlags(u32);

impl IndexFlags {
    pub const NONE: Self = Self(0);
    pub const STRINGS_ONLY: Self = Self(1 << 0);
    pub const NO_INDEX_SIGNATURES: Self = Self(1 << 1);
    pub const NO_REDUCIBLE_CHECK: Self = Self(1 << 2);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl_flag_operators!(IndexFlags);

/// The syntactic form represented by a type predicate.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum TypePredicateKind {
    #[default]
    This = 0,
    Identifier = 1,
    AssertsThis = 2,
    AssertsIdentifier = 3,
}

/// Four-valued result of a canonical type relation.
///
/// The representation makes bitwise AND select the lesser and bitwise OR the
/// greater value in `False < Unknown < Maybe < True`. `Maybe` marks a relation
/// that depends on itself; `Unknown` marks a variance check that depends on
/// itself and therefore must not be cached as a circular variance result.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(i8)]
pub enum Ternary {
    #[default]
    False = 0,
    Unknown = 1,
    Maybe = 3,
    True = -1,
}

impl Ternary {
    const fn from_value(value: i8) -> Self {
        match value {
            0 => Self::False,
            1 => Self::Unknown,
            3 => Self::Maybe,
            -1 => Self::True,
            _ => panic!("invalid Ternary bitwise result"),
        }
    }
}

impl std::ops::BitAnd for Ternary {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::from_value((self as i8) & (rhs as i8))
    }
}

impl std::ops::BitAndAssign for Ternary {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitOr for Ternary {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::from_value((self as i8) | (rhs as i8))
    }
}

impl std::ops::BitOrAssign for Ternary {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

/// Canonical call or construct signature.
///
/// This is the ID-based equivalent of typescript-go's `Signature`. Pointer
/// fields become IDs in their owning semantic arenas and AST pointers become
/// program-wide [`NodeRef`] values. Allocation is restricted to the aggregate
/// [`super::SemanticStore`], so IDs and references cannot cross programs.
#[derive(Debug, Eq, PartialEq)]
pub struct Signature {
    id: SignatureId,
    flags: SignatureFlags,
    min_argument_count: i32,
    resolved_min_argument_count: i32,
    declaration: Option<NodeRef>,
    type_parameters: Vec<TypeId>,
    parameters: Vec<SemanticSymbolId>,
    this_parameter: Option<SemanticSymbolId>,
    resolved_return_type: Option<TypeId>,
    resolved_type_predicate: Option<TypePredicateId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    isolated_signature_type: Option<TypeId>,
    composite: Option<CompositeSignature>,
}

impl Signature {
    #[must_use]
    pub const fn id(&self) -> SignatureId {
        self.id
    }

    #[must_use]
    pub const fn flags(&self) -> SignatureFlags {
        self.flags
    }

    #[must_use]
    pub const fn min_argument_count(&self) -> i32 {
        self.min_argument_count
    }

    /// Returns `-1` until lazy minimum-argument resolution has completed.
    #[must_use]
    pub const fn resolved_min_argument_count(&self) -> i32 {
        self.resolved_min_argument_count
    }

    #[must_use]
    pub const fn declaration(&self) -> Option<NodeRef> {
        self.declaration
    }

    #[must_use]
    pub fn type_parameters(&self) -> &[TypeId] {
        &self.type_parameters
    }

    #[must_use]
    pub fn parameters(&self) -> &[SemanticSymbolId] {
        &self.parameters
    }

    #[must_use]
    pub const fn this_parameter(&self) -> Option<SemanticSymbolId> {
        self.this_parameter
    }

    #[must_use]
    pub const fn resolved_return_type(&self) -> Option<TypeId> {
        self.resolved_return_type
    }

    #[must_use]
    pub const fn resolved_type_predicate(&self) -> Option<TypePredicateId> {
        self.resolved_type_predicate
    }

    #[must_use]
    pub const fn target(&self) -> Option<SignatureId> {
        self.target
    }

    #[must_use]
    pub const fn mapper(&self) -> Option<TypeMapperId> {
        self.mapper
    }

    #[must_use]
    pub const fn isolated_signature_type(&self) -> Option<TypeId> {
        self.isolated_signature_type
    }

    #[must_use]
    pub const fn composite(&self) -> Option<&CompositeSignature> {
        self.composite.as_ref()
    }

    #[must_use]
    pub const fn has_rest_parameter(&self) -> bool {
        self.flags.contains(SignatureFlags::HAS_REST_PARAMETER)
    }
}

/// Invalid canonical input or exhausted storage during signature creation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignatureInstantiationError {
    InvalidSignature(SignatureId),
    InvalidMapper(TypeMapperId),
    InvalidTypeParameter(TypeId),
    InvalidSymbol(SemanticSymbolId),
    InvalidInstantiatedSymbol(SemanticSymbolId),
    Capacity(SignatureId),
}

impl std::fmt::Display for SignatureInstantiationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSignature(signature) => {
                write!(
                    formatter,
                    "cannot instantiate invalid signature {signature:?}"
                )
            }
            Self::InvalidMapper(mapper) => {
                write!(
                    formatter,
                    "cannot instantiate with invalid mapper {mapper:?}"
                )
            }
            Self::InvalidTypeParameter(type_parameter) => write!(
                formatter,
                "signature has an invalid type parameter {type_parameter:?}"
            ),
            Self::InvalidSymbol(symbol) => {
                write!(formatter, "signature has an invalid symbol {symbol:?}")
            }
            Self::InvalidInstantiatedSymbol(symbol) => write!(
                formatter,
                "instantiated symbol {symbol:?} has invalid target or mapper links"
            ),
            Self::Capacity(signature) => write!(
                formatter,
                "signature instantiation exhausted storage for {signature:?}"
            ),
        }
    }
}

impl std::error::Error for SignatureInstantiationError {}

struct SignatureTypeParameterPlan {
    type_: TypeId,
    symbol: Option<SemanticSymbolId>,
}

enum SignatureSymbolPlan {
    Reuse(SemanticSymbolId),
    Instantiate {
        target: SemanticSymbolId,
        previous_mapper: Option<TypeMapperId>,
        data: SymbolData,
        name_type: Option<TypeId>,
    },
}

struct SignatureInstantiationPlan {
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    min_argument_count: i32,
    type_parameters: Vec<SignatureTypeParameterPlan>,
    this_parameter: Option<SignatureSymbolPlan>,
    parameters: Vec<SignatureSymbolPlan>,
    new_symbol_count: usize,
    combined_symbol_mapper_count: usize,
}

impl CanonicalTypeMapperStore {
    /// Instantiates a signature while retaining fresh generic parameters.
    ///
    /// Parameter symbols, predicates, and return types stay unresolved until
    /// their owning checker operation demands them.
    ///
    /// # Errors
    ///
    /// Returns an error when an input belongs to another store, an existing
    /// signature or symbol is malformed, or storage cannot be reserved.
    pub fn instantiate_signature(
        &mut self,
        signature: SignatureId,
        mapper: TypeMapperId,
    ) -> Result<SignatureId, SignatureInstantiationError> {
        self.instantiate_signature_ex(signature, mapper, false)
    }

    /// Mirrors pinned `instantiateSignatureEx`, including fresh parameters,
    /// mapper composition, symbol metadata, and lazy return/predicate slots.
    ///
    /// # Errors
    ///
    /// Returns an error when an input belongs to another store, an existing
    /// signature or symbol is malformed, or storage cannot be reserved.
    ///
    /// # Panics
    ///
    /// Panics if a validated allocation or mapper publication fails after its
    /// storage has been reserved.
    pub fn instantiate_signature_ex(
        &mut self,
        signature: SignatureId,
        mapper: TypeMapperId,
        erase_type_parameters: bool,
    ) -> Result<SignatureId, SignatureInstantiationError> {
        if self.mapper_payload(mapper).is_none() {
            return Err(SignatureInstantiationError::InvalidMapper(mapper));
        }
        let plan = self.prepare_signature_instantiation(signature, erase_type_parameters)?;
        let new_type_parameter_count = plan.type_parameters.len();
        let fresh_mapper_count = usize::from(new_type_parameter_count != 0) * 2;
        if !self.try_reserve_types(new_type_parameter_count)
            || !self.try_reserve_mappers(fresh_mapper_count + plan.combined_symbol_mapper_count)
            || !self.try_reserve_checker_symbol_allocations(plan.new_symbol_count, 0)
            || !self.try_reserve_value_symbol_links(plan.new_symbol_count)
            || !self.try_reserve_signatures(1)
        {
            return Err(SignatureInstantiationError::Capacity(signature));
        }

        let mut effective_mapper = mapper;
        let mut fresh_type_parameters = Vec::with_capacity(new_type_parameter_count);
        if !plan.type_parameters.is_empty() {
            let mut original_type_parameters = Vec::with_capacity(new_type_parameter_count);
            for type_parameter in &plan.type_parameters {
                let fresh = self
                    .alloc_type_parameter(type_parameter.symbol)
                    .expect("reserved type parameter allocation must succeed");
                assert!(self.set_type_parameter_resolution(
                    fresh,
                    None,
                    Some(type_parameter.type_),
                    None,
                    None,
                ));
                original_type_parameters.push(type_parameter.type_);
                fresh_type_parameters.push(fresh);
            }
            let fresh_mapper = self
                .new_type_mapper(original_type_parameters, fresh_type_parameters.clone())
                .expect("fresh type parameters remain owned by this store");
            effective_mapper = self
                .combine_type_mappers(Some(fresh_mapper), mapper)
                .expect("fresh and original mappers remain owned by this store");
            for (fresh, original) in fresh_type_parameters
                .iter()
                .copied()
                .zip(&plan.type_parameters)
            {
                assert!(self.set_type_parameter_resolution(
                    fresh,
                    None,
                    Some(original.type_),
                    Some(effective_mapper),
                    None,
                ));
            }
        }

        let this_parameter = plan.this_parameter.map(|parameter| {
            self.publish_instantiated_signature_symbol(parameter, effective_mapper)
        });
        let parameters = plan
            .parameters
            .into_iter()
            .map(|parameter| {
                self.publish_instantiated_signature_symbol(parameter, effective_mapper)
            })
            .collect();
        let instantiated = self
            .alloc_signature(
                plan.flags,
                plan.declaration,
                fresh_type_parameters,
                this_parameter,
                parameters,
                None,
                None,
                plan.min_argument_count,
            )
            .expect("reserved signature allocation must succeed");
        assert!(self.set_signature_target_and_mapper(
            instantiated,
            Some(signature),
            Some(effective_mapper),
        ));
        Ok(instantiated)
    }

    /// Mirrors pinned `cloneSignature` without demanding lazy result fields.
    ///
    /// # Errors
    ///
    /// Returns an error when the signature is not owned by this store or
    /// storage cannot be reserved.
    ///
    /// # Panics
    ///
    /// Panics if the reserved signature cannot be allocated or its validated
    /// provenance cannot be published.
    pub fn clone_signature(
        &mut self,
        signature: SignatureId,
    ) -> Result<SignatureId, SignatureInstantiationError> {
        let source = self
            .signature(signature)
            .ok_or(SignatureInstantiationError::InvalidSignature(signature))?;
        let flags = source.flags() & SignatureFlags::PROPAGATING_FLAGS;
        let declaration = source.declaration();
        let type_parameters = source.type_parameters().to_vec();
        let this_parameter = source.this_parameter();
        let parameters = source.parameters().to_vec();
        let min_argument_count = source.min_argument_count();
        let target = source.target();
        let mapper = source.mapper();
        let composite = source.composite().cloned();
        if !self.try_reserve_signatures(1) {
            return Err(SignatureInstantiationError::Capacity(signature));
        }
        let clone = self
            .alloc_signature(
                flags,
                declaration,
                type_parameters,
                this_parameter,
                parameters,
                None,
                None,
                min_argument_count,
            )
            .expect("reserved signature allocation must succeed");
        assert!(self.set_signature_target_and_mapper(clone, target, mapper));
        assert!(self.set_signature_composite(clone, composite));
        Ok(clone)
    }

    fn prepare_signature_instantiation(
        &self,
        signature: SignatureId,
        erase_type_parameters: bool,
    ) -> Result<SignatureInstantiationPlan, SignatureInstantiationError> {
        let source = self
            .signature(signature)
            .ok_or(SignatureInstantiationError::InvalidSignature(signature))?;
        if source.min_argument_count() < 0
            || usize::try_from(source.min_argument_count())
                .is_ok_and(|minimum| minimum > source.parameters().len())
            || source.has_rest_parameter() && source.parameters().is_empty()
        {
            return Err(SignatureInstantiationError::InvalidSignature(signature));
        }
        let type_parameters = if erase_type_parameters {
            Vec::new()
        } else {
            let mut seen = HashSet::with_capacity(source.type_parameters().len());
            source
                .type_parameters()
                .iter()
                .copied()
                .map(|type_parameter| {
                    let Some(record) = self.type_payload(type_parameter) else {
                        return Err(SignatureInstantiationError::InvalidTypeParameter(
                            type_parameter,
                        ));
                    };
                    if !matches!(record.data(), TypeData::TypeParameter(_))
                        || !seen.insert(type_parameter)
                    {
                        return Err(SignatureInstantiationError::InvalidTypeParameter(
                            type_parameter,
                        ));
                    }
                    Ok(SignatureTypeParameterPlan {
                        type_: type_parameter,
                        symbol: record.symbol(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };

        let this_parameter = source
            .this_parameter()
            .map(|parameter| self.prepare_instantiated_signature_symbol(parameter))
            .transpose()?;
        let parameters = source
            .parameters()
            .iter()
            .copied()
            .map(|parameter| self.prepare_instantiated_signature_symbol(parameter))
            .collect::<Result<Vec<_>, _>>()?;
        let new_symbol_count = this_parameter
            .iter()
            .chain(&parameters)
            .filter(|parameter| matches!(parameter, SignatureSymbolPlan::Instantiate { .. }))
            .count();
        let combined_symbol_mapper_count = this_parameter
            .iter()
            .chain(&parameters)
            .filter(|parameter| {
                matches!(
                    parameter,
                    SignatureSymbolPlan::Instantiate {
                        previous_mapper: Some(_),
                        ..
                    }
                )
            })
            .count();
        Ok(SignatureInstantiationPlan {
            flags: source.flags() & SignatureFlags::PROPAGATING_FLAGS,
            declaration: source.declaration(),
            min_argument_count: source.min_argument_count(),
            type_parameters,
            this_parameter,
            parameters,
            new_symbol_count,
            combined_symbol_mapper_count,
        })
    }

    fn prepare_instantiated_signature_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SignatureSymbolPlan, SignatureInstantiationError> {
        let source = self
            .symbol(symbol)
            .ok_or(SignatureInstantiationError::InvalidSymbol(symbol))?;
        let links = self.value_symbol_links(symbol);
        if let Some(resolved_type) = links.and_then(|links| links.resolved_type)
            && !self.signature_type_could_contain_variables(resolved_type, &mut HashSet::new())?
            && (!source.flags().contains(SymbolFlags::SET_ACCESSOR)
                || links
                    .and_then(|links| links.write_type)
                    .map(|write_type| {
                        self.signature_type_could_contain_variables(write_type, &mut HashSet::new())
                    })
                    .transpose()?
                    == Some(false))
        {
            return Ok(SignatureSymbolPlan::Reuse(symbol));
        }

        let (target, previous_mapper) = if source.check_flags().contains(CheckFlags::INSTANTIATED) {
            let links = links.ok_or(SignatureInstantiationError::InvalidInstantiatedSymbol(
                symbol,
            ))?;
            let target =
                links
                    .target
                    .ok_or(SignatureInstantiationError::InvalidInstantiatedSymbol(
                        symbol,
                    ))?;
            let mapper =
                links
                    .mapper
                    .ok_or(SignatureInstantiationError::InvalidInstantiatedSymbol(
                        symbol,
                    ))?;
            if self.symbol(target).is_none() || self.mapper_payload(mapper).is_none() {
                return Err(SignatureInstantiationError::InvalidInstantiatedSymbol(
                    symbol,
                ));
            }
            (target, Some(mapper))
        } else {
            (symbol, None)
        };
        let target_record = self
            .symbol(target)
            .ok_or(SignatureInstantiationError::InvalidSymbol(target))?;
        let mut data = SymbolData::new(
            target_record.flags() | SymbolFlags::TRANSIENT,
            target_record.name().to_owned(),
        );
        data.check_flags = CheckFlags::INSTANTIATED
            | (target_record.check_flags()
                & (CheckFlags::READONLY
                    | CheckFlags::LATE
                    | CheckFlags::OPTIONAL_PARAMETER
                    | CheckFlags::REST_PARAMETER));
        data.declarations = target_record.declarations().map(<[_]>::to_vec);
        data.value_declaration = target_record.value_declaration();
        data.parent = target_record.parent();
        Ok(SignatureSymbolPlan::Instantiate {
            target,
            previous_mapper,
            data,
            name_type: links.and_then(|links| links.name_type),
        })
    }

    fn publish_instantiated_signature_symbol(
        &mut self,
        parameter: SignatureSymbolPlan,
        mapper: TypeMapperId,
    ) -> SemanticSymbolId {
        match parameter {
            SignatureSymbolPlan::Reuse(symbol) => symbol,
            SignatureSymbolPlan::Instantiate {
                target,
                previous_mapper,
                data,
                name_type,
            } => {
                let mapper = match previous_mapper {
                    None => mapper,
                    Some(previous_mapper) => self
                        .combine_type_mappers(Some(previous_mapper), mapper)
                        .expect("validated symbol mappers remain owned by this store"),
                };
                let instantiated = self
                    .alloc_symbol(data)
                    .expect("reserved instantiated-symbol allocation must succeed");
                assert!(self.set_value_symbol_links(
                    instantiated,
                    ValueSymbolLinks {
                        resolved_type: None,
                        target: Some(target),
                        mapper: Some(mapper),
                        name_type,
                        ..ValueSymbolLinks::default()
                    },
                ));
                instantiated
            }
        }
    }

    fn signature_type_could_contain_variables(
        &self,
        type_: TypeId,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, SignatureInstantiationError> {
        let record = self
            .type_payload(type_)
            .ok_or(SignatureInstantiationError::InvalidTypeParameter(type_))?;
        if !record
            .flags()
            .intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            return Ok(false);
        }
        if record.flags().intersects(TypeFlags::INSTANTIABLE) || !active.insert(type_) {
            return Ok(true);
        }
        let result = match record.data() {
            TypeData::Union(data) if !record.flags().intersects(TypeFlags::ENUM_LITERAL) => data
                .union
                .types
                .iter()
                .copied()
                .try_fold(false, |contains, constituent| {
                    Ok(contains
                        || self.signature_type_could_contain_variables(constituent, active)?)
                }),
            TypeData::Intersection(data) => {
                data.intersection
                    .types
                    .iter()
                    .copied()
                    .try_fold(false, |contains, constituent| {
                        Ok(contains
                            || self.signature_type_could_contain_variables(constituent, active)?)
                    })
            }
            TypeData::TypeReference(data) => self.signature_reference_could_contain_variables(
                data.node,
                data.resolved_type_arguments.as_deref(),
                active,
            ),
            TypeData::Interface(data) => self.signature_reference_could_contain_variables(
                data.reference.node,
                data.reference.resolved_type_arguments.as_deref(),
                active,
            ),
            TypeData::Tuple(data) => self.signature_reference_could_contain_variables(
                data.interface.reference.node,
                data.interface.reference.resolved_type_arguments.as_deref(),
                active,
            ),
            TypeData::Object(_) => {
                let generic_object_flags = ObjectFlags::MAPPED
                    | ObjectFlags::REVERSE_MAPPED
                    | ObjectFlags::OBJECT_REST_TYPE
                    | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE;
                let anonymous_with_declarations =
                    record.object_flags().contains(ObjectFlags::ANONYMOUS)
                        && record
                            .symbol()
                            .and_then(|symbol| self.symbol(symbol))
                            .is_some_and(|symbol| {
                                symbol.flags().intersects(
                                    SymbolFlags::FUNCTION
                                        | SymbolFlags::METHOD
                                        | SymbolFlags::CLASS
                                        | SymbolFlags::TYPE_LITERAL
                                        | SymbolFlags::OBJECT_LITERAL,
                                ) && symbol.declarations().is_some()
                            });
                Ok(record.object_flags().intersects(generic_object_flags)
                    || anonymous_with_declarations)
            }
            _ => Ok(true),
        };
        active.remove(&type_);
        result
    }

    fn signature_reference_could_contain_variables(
        &self,
        node: Option<NodeRef>,
        arguments: Option<&[TypeId]>,
        active: &mut HashSet<TypeId>,
    ) -> Result<bool, SignatureInstantiationError> {
        if node.is_some() {
            return Ok(true);
        }
        arguments
            .unwrap_or_default()
            .iter()
            .copied()
            .try_fold(false, |contains, argument| {
                Ok(contains || self.signature_type_could_contain_variables(argument, active)?)
            })
    }
}

/// Store-owned storage for canonical signatures.
#[derive(Debug)]
pub(super) struct SignatureArena {
    signatures: TypedArena<SignatureId, Signature>,
}

impl SignatureArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            signatures: TypedArena::new(store),
        }
    }

    /// Implements the record initialization performed by
    /// typescript-go `checker.go::newSignature`.
    ///
    /// `target`, `mapper`, `isolated_signature_type`, and `composite` start
    /// absent, and `resolved_min_argument_count` starts at the exact upstream
    /// sentinel value `-1`.
    ///
    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    #[allow(clippy::too_many_arguments)] // Mirrors upstream newSignature exactly.
    pub(super) fn alloc(
        &mut self,
        flags: SignatureFlags,
        declaration: Option<NodeRef>,
        type_parameters: Vec<TypeId>,
        this_parameter: Option<SemanticSymbolId>,
        parameters: Vec<SemanticSymbolId>,
        resolved_return_type: Option<TypeId>,
        resolved_type_predicate: Option<TypePredicateId>,
        min_argument_count: i32,
    ) -> SignatureId {
        self.signatures.alloc_with(|id| Signature {
            id,
            flags,
            min_argument_count,
            resolved_min_argument_count: -1,
            declaration,
            type_parameters,
            parameters,
            this_parameter,
            resolved_return_type,
            resolved_type_predicate,
            target: None,
            mapper: None,
            isolated_signature_type: None,
            composite: None,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: SignatureId) -> Option<&Signature> {
        self.signatures.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.signatures.len()
    }

    pub(super) fn try_reserve(&mut self, additional: usize) -> bool {
        self.signatures.try_reserve(additional)
    }

    #[must_use]
    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = (SignatureId, &Signature)> {
        self.signatures.iter()
    }

    /// Updates the lazy cache written by
    /// typescript-go `getMinArgumentCount`.
    pub(super) fn set_resolved_min_argument_count(&mut self, id: SignatureId, count: i32) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_min_argument_count = count;
        true
    }

    /// Updates the lazy return-type slot used during signature resolution.
    pub(super) fn set_resolved_return_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_return_type = type_id;
        true
    }

    /// Updates the lazy type-predicate slot used during signature resolution.
    pub(super) fn set_resolved_type_predicate(
        &mut self,
        id: SignatureId,
        predicate: Option<TypePredicateId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_type_predicate = predicate;
        true
    }

    /// Updates the lazily constructed isolated signature type.
    pub(super) fn set_isolated_signature_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.isolated_signature_type = type_id;
        true
    }

    /// Records the source signature and mapper for an instantiated signature.
    ///
    /// A target from outside this arena is rejected. Mapper identity belongs
    /// to the program's canonical mapper arena and is therefore type-checked
    /// here but validated by the eventual aggregate semantic store.
    pub(super) fn set_target_and_mapper(
        &mut self,
        id: SignatureId,
        target: Option<SignatureId>,
        mapper: Option<TypeMapperId>,
    ) -> bool {
        if target.is_some_and(|target| self.signatures.get(target).is_none()) {
            return false;
        }
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.target = target;
        signature.mapper = mapper;
        true
    }

    /// Attaches immutable union/intersection provenance to a signature.
    ///
    /// Every constituent must already exist in this arena, preventing a
    /// composite record from silently holding an out-of-range signature ID.
    pub(super) fn set_composite(
        &mut self,
        id: SignatureId,
        composite: Option<CompositeSignature>,
    ) -> bool {
        if composite.as_ref().is_some_and(|composite| {
            composite
                .signatures()
                .iter()
                .any(|signature| self.signatures.get(*signature).is_none())
        }) {
            return false;
        }
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.composite = composite;
        true
    }

    pub(super) fn set_flags(&mut self, id: SignatureId, flags: SignatureFlags) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.flags = flags;
        true
    }

    pub(super) fn set_type_parameters(
        &mut self,
        id: SignatureId,
        type_parameters: Vec<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.type_parameters = type_parameters;
        true
    }

    pub(super) fn set_this_parameter(
        &mut self,
        id: SignatureId,
        this_parameter: Option<SemanticSymbolId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.this_parameter = this_parameter;
        true
    }
}

/// Constituent signatures combined as a union or intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositeSignature {
    is_union: bool,
    signatures: Vec<SignatureId>,
}

impl CompositeSignature {
    pub(super) const fn new(is_union: bool, signatures: Vec<SignatureId>) -> Self {
        Self {
            is_union,
            signatures,
        }
    }

    #[must_use]
    pub const fn is_union(&self) -> bool {
        self.is_union
    }

    #[must_use]
    pub fn signatures(&self) -> &[SignatureId] {
        &self.signatures
    }
}

/// Canonical semantic type predicate.
#[derive(Debug, Eq, PartialEq)]
pub struct TypePredicate {
    id: TypePredicateId,
    kind: TypePredicateKind,
    parameter_index: i32,
    parameter_name: String,
    type_id: Option<TypeId>,
}

impl TypePredicate {
    #[must_use]
    pub const fn id(&self) -> TypePredicateId {
        self.id
    }

    #[must_use]
    pub const fn kind(&self) -> TypePredicateKind {
        self.kind
    }

    #[must_use]
    pub const fn parameter_index(&self) -> i32 {
        self.parameter_index
    }

    #[must_use]
    pub fn parameter_name(&self) -> &str {
        &self.parameter_name
    }

    /// The narrowed type, if one was written. Assertion predicates may omit it.
    #[must_use]
    pub const fn type_id(&self) -> Option<TypeId> {
        self.type_id
    }
}

/// Store-owned storage for canonical type predicates.
#[derive(Debug)]
pub(super) struct TypePredicateArena {
    predicates: TypedArena<TypePredicateId, TypePredicate>,
}

impl TypePredicateArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            predicates: TypedArena::new(store),
        }
    }

    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub(super) fn alloc(
        &mut self,
        kind: TypePredicateKind,
        parameter_index: i32,
        parameter_name: impl Into<String>,
        type_id: Option<TypeId>,
    ) -> TypePredicateId {
        let parameter_name = parameter_name.into();
        self.predicates.alloc_with(|id| TypePredicate {
            id,
            kind,
            parameter_index,
            parameter_name,
            type_id,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: TypePredicateId) -> Option<&TypePredicate> {
        self.predicates.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.predicates.len()
    }
}

/// Canonical index-signature information.
#[derive(Debug, Eq, PartialEq)]
pub struct IndexInfo {
    id: IndexInfoId,
    key_type: TypeId,
    value_type: TypeId,
    is_readonly: bool,
    declaration: Option<NodeRef>,
    index_symbol: Option<SemanticSymbolId>,
    components: Vec<NodeRef>,
}

impl IndexInfo {
    #[must_use]
    pub const fn id(&self) -> IndexInfoId {
        self.id
    }

    #[must_use]
    pub const fn key_type(&self) -> TypeId {
        self.key_type
    }

    #[must_use]
    pub const fn value_type(&self) -> TypeId {
        self.value_type
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.is_readonly
    }

    #[must_use]
    pub const fn declaration(&self) -> Option<NodeRef> {
        self.declaration
    }

    #[must_use]
    pub const fn index_symbol(&self) -> Option<SemanticSymbolId> {
        self.index_symbol
    }

    #[must_use]
    pub fn components(&self) -> &[NodeRef] {
        &self.components
    }
}

/// Store-owned storage for canonical index information.
#[derive(Debug)]
pub(super) struct IndexInfoArena {
    infos: TypedArena<IndexInfoId, IndexInfo>,
}

impl IndexInfoArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            infos: TypedArena::new(store),
        }
    }

    #[must_use]
    pub(super) fn try_reserve(&mut self, additional: usize) -> bool {
        self.infos.try_reserve(additional)
    }

    /// Implements the record initialization performed by
    /// typescript-go `checker.go::newIndexInfo`.
    ///
    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub(super) fn alloc(
        &mut self,
        key_type: TypeId,
        value_type: TypeId,
        is_readonly: bool,
        declaration: Option<NodeRef>,
        components: Vec<NodeRef>,
    ) -> IndexInfoId {
        self.infos.alloc_with(|id| IndexInfo {
            id,
            key_type,
            value_type,
            is_readonly,
            declaration,
            index_symbol: None,
            components,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: IndexInfoId) -> Option<&IndexInfo> {
        self.infos.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.infos.len()
    }

    /// Updates the synthetic property symbol lazily created for this index.
    pub(super) fn set_index_symbol(
        &mut self,
        id: IndexInfoId,
        symbol: Option<SemanticSymbolId>,
    ) -> bool {
        let Some(info) = self.infos.get_mut(id) else {
            return false;
        };
        info.index_symbol = symbol;
        true
    }
}

/// Flags and optional label declaration for one tuple element.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TupleElementInfo {
    flags: ElementFlags,
    labeled_declaration: Option<NodeRef>,
}

impl TupleElementInfo {
    pub(super) const fn new(flags: ElementFlags, labeled_declaration: Option<NodeRef>) -> Self {
        Self {
            flags,
            labeled_declaration,
        }
    }

    #[must_use]
    pub const fn flags(self) -> ElementFlags {
        self.flags
    }

    #[must_use]
    pub const fn labeled_declaration(self) -> Option<NodeRef> {
        self.labeled_declaration
    }
}

/// Tuple-specific metadata from typescript-go's `TupleType` record.
///
/// The embedded interface/type payload is deliberately outside this
/// dependency-closed cluster. Length and combined-flag fields are derived with
/// the same rules as `checker.go::createTupleTargetType`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleMetadata {
    element_infos: Vec<TupleElementInfo>,
    min_length: usize,
    fixed_length: usize,
    combined_flags: ElementFlags,
    readonly: bool,
}

impl TupleMetadata {
    pub(super) fn new(element_infos: Vec<TupleElementInfo>, readonly: bool) -> Self {
        let mut min_length = 0;
        let mut combined_flags = ElementFlags::NONE;
        let mut fixed_length = element_infos.len();
        for (index, info) in element_infos.iter().enumerate() {
            let flags = info.flags();
            if flags.intersects(ElementFlags::REQUIRED | ElementFlags::VARIADIC) {
                min_length += 1;
            }
            combined_flags |= flags;
            if fixed_length == element_infos.len()
                && combined_flags.intersects(ElementFlags::VARIABLE)
            {
                fixed_length = index;
            }
        }
        Self {
            element_infos,
            min_length,
            fixed_length,
            combined_flags,
            readonly,
        }
    }

    #[must_use]
    pub fn element_infos(&self) -> &[TupleElementInfo] {
        &self.element_infos
    }

    #[must_use]
    pub fn element_flags(&self) -> Vec<ElementFlags> {
        self.element_infos.iter().map(|info| info.flags()).collect()
    }

    #[must_use]
    pub const fn min_length(&self) -> usize {
        self.min_length
    }

    #[must_use]
    pub const fn fixed_length(&self) -> usize {
        self.fixed_length
    }

    #[must_use]
    pub const fn combined_flags(&self) -> ElementFlags {
        self.combined_flags
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use ts_binder::{CheckFlags, EscapedName, SymbolData, SymbolFlags};

    use super::{
        CanonicalTypeMapperStore, ElementFlags, IndexFlags, SignatureFlags,
        SignatureInstantiationError, SignatureKind, Ternary, TypePredicateKind,
    };
    use crate::semantic::{
        SemanticSymbolId, TypeId, instantiate::instantiate_type, links::ValueSymbolLinks,
        mapper::TypeMapperKind, type_records::TypeData, types::TypeFlags,
    };

    fn intrinsic(store: &mut CanonicalTypeMapperStore, flags: TypeFlags, name: &str) -> TypeId {
        store.alloc_intrinsic_type(flags, name).unwrap()
    }

    fn parameter(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        flags: CheckFlags,
        type_: Option<TypeId>,
    ) -> SemanticSymbolId {
        let symbol_flags = if flags == CheckFlags::NONE {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
        };
        let mut data = SymbolData::new(symbol_flags, EscapedName::source(name));
        data.check_flags = flags;
        let symbol = store.alloc_symbol(data).unwrap();
        if type_.is_some() {
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: type_,
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        symbol
    }

    fn counts(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize) {
        (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
        )
    }

    #[test]
    fn instantiated_signatures_freshen_type_parameters_and_preserve_lazy_metadata() {
        let mut store = CanonicalTypeMapperStore::new();
        let string = intrinsic(&mut store, TypeFlags::STRING, "string");
        let number = intrinsic(&mut store, TypeFlags::NUMBER, "number");
        let outer = store.alloc_type_parameter(None).unwrap();
        let type_parameter_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("T"),
            ))
            .unwrap();
        let original_type_parameter = store
            .alloc_type_parameter(Some(type_parameter_symbol))
            .unwrap();
        let mapper = store.new_simple_type_mapper(outer, number).unwrap();
        let this = parameter(&mut store, "this", CheckFlags::NONE, Some(string));
        let required = parameter(
            &mut store,
            "required",
            CheckFlags::NONE,
            Some(original_type_parameter),
        );
        let optional = parameter(
            &mut store,
            "optional",
            CheckFlags::OPTIONAL_PARAMETER | CheckFlags::READONLY,
            Some(original_type_parameter),
        );
        let rest = parameter(
            &mut store,
            "rest",
            CheckFlags::REST_PARAMETER | CheckFlags::LATE,
            Some(outer),
        );
        assert!(store.set_value_symbol_links(
            optional,
            ValueSymbolLinks {
                resolved_type: Some(original_type_parameter),
                name_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let predicate = store
            .alloc_type_predicate(
                TypePredicateKind::Identifier,
                0,
                "required",
                Some(original_type_parameter),
            )
            .unwrap();
        let flags = SignatureFlags::HAS_REST_PARAMETER
            | SignatureFlags::HAS_LITERAL_TYPES
            | SignatureFlags::CONSTRUCT
            | SignatureFlags::IS_INNER_CALL_CHAIN
            | SignatureFlags::IS_NON_INFERRABLE;
        let source = store
            .alloc_signature(
                flags,
                None,
                vec![original_type_parameter],
                Some(this),
                vec![required, optional, rest],
                Some(original_type_parameter),
                Some(predicate),
                1,
            )
            .unwrap();
        assert!(store.set_signature_resolved_min_argument_count(source, 0));
        assert!(store.set_signature_isolated_type(source, Some(string)));
        let before = counts(&store);

        let instantiated = store.instantiate_signature(source, mapper).unwrap();
        let record = store.signature(instantiated).unwrap();
        let fresh = record.type_parameters()[0];
        let effective_mapper = record.mapper().unwrap();
        let parameters = record.parameters().to_vec();
        assert_eq!(record.flags(), flags & SignatureFlags::PROPAGATING_FLAGS);
        assert_eq!(record.target(), Some(source));
        assert_eq!(record.this_parameter(), Some(this));
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_min_argument_count(), -1);
        assert_eq!(record.resolved_return_type(), None);
        assert_eq!(record.resolved_type_predicate(), None);
        assert_eq!(record.isolated_signature_type(), None);
        assert_eq!(record.composite(), None);
        assert_ne!(fresh, original_type_parameter);
        assert_eq!(
            counts(&store),
            (before.0 + 1, before.1 + 2, before.2 + 3, before.3 + 1)
        );

        let fresh_record = store.type_payload(fresh).unwrap();
        assert_eq!(fresh_record.symbol(), Some(type_parameter_symbol));
        let TypeData::TypeParameter(fresh_data) = fresh_record.data() else {
            unreachable!();
        };
        assert_eq!(fresh_data.target, Some(original_type_parameter));
        assert_eq!(fresh_data.mapper, Some(effective_mapper));
        assert_eq!(fresh_data.constraint, None);
        assert_eq!(
            store.mapper_kind(effective_mapper),
            Some(TypeMapperKind::Unknown)
        );
        assert_eq!(
            instantiate_type(&mut store, original_type_parameter, effective_mapper),
            Ok(fresh)
        );
        assert_eq!(
            instantiate_type(&mut store, outer, effective_mapper),
            Ok(number)
        );

        for (instantiated, target) in parameters.into_iter().zip([required, optional, rest]) {
            let symbol = store.symbol(instantiated).unwrap();
            let original = store.symbol(target).unwrap();
            let expected_flags = CheckFlags::INSTANTIATED
                | (original.check_flags()
                    & (CheckFlags::READONLY
                        | CheckFlags::LATE
                        | CheckFlags::OPTIONAL_PARAMETER
                        | CheckFlags::REST_PARAMETER));
            assert_eq!(symbol.flags(), original.flags() | SymbolFlags::TRANSIENT);
            assert_eq!(symbol.check_flags(), expected_flags);
            assert_eq!(symbol.name(), original.name());
            assert_eq!(symbol.declarations(), original.declarations());
            let links = store.value_symbol_links(instantiated).unwrap();
            assert_eq!(links.resolved_type, None);
            assert_eq!(links.target, Some(target));
            assert_eq!(links.mapper, Some(effective_mapper));
            assert_eq!(links.name_type, (target == optional).then_some(string));
        }
    }

    #[test]
    fn erased_signature_instantiation_reuses_invariant_parameter_symbols() {
        let mut store = CanonicalTypeMapperStore::new();
        let string = intrinsic(&mut store, TypeFlags::STRING, "string");
        let type_parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store
            .new_simple_type_mapper(type_parameter, string)
            .unwrap();
        let invariant = parameter(&mut store, "fixed", CheckFlags::NONE, Some(string));
        let generic = parameter(
            &mut store,
            "generic",
            CheckFlags::NONE,
            Some(type_parameter),
        );
        let source = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![type_parameter],
                None,
                vec![invariant, generic],
                Some(type_parameter),
                None,
                2,
            )
            .unwrap();
        let before = counts(&store);

        let instantiated = store
            .instantiate_signature_ex(source, mapper, true)
            .unwrap();
        let record = store.signature(instantiated).unwrap();
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.mapper(), Some(mapper));
        assert_eq!(record.parameters()[0], invariant);
        assert_ne!(record.parameters()[1], generic);
        assert_eq!(
            counts(&store),
            (before.0, before.1, before.2 + 1, before.3 + 1)
        );
        assert_eq!(
            store.value_symbol_links(record.parameters()[1]),
            Some(&ValueSymbolLinks {
                resolved_type: None,
                target: Some(generic),
                mapper: Some(mapper),
                ..ValueSymbolLinks::default()
            })
        );
    }

    #[test]
    fn nested_instantiated_parameter_symbols_compose_their_original_mapper() {
        let mut store = CanonicalTypeMapperStore::new();
        let string = intrinsic(&mut store, TypeFlags::STRING, "string");
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let first_mapper = store.new_simple_type_mapper(first, second).unwrap();
        let second_mapper = store.new_simple_type_mapper(second, string).unwrap();
        let original = parameter(
            &mut store,
            "value",
            CheckFlags::OPTIONAL_PARAMETER,
            Some(first),
        );
        let mut proxy_data = SymbolData::new(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
            EscapedName::source("value"),
        );
        proxy_data.check_flags = CheckFlags::INSTANTIATED | CheckFlags::OPTIONAL_PARAMETER;
        let proxy = store.alloc_symbol(proxy_data).unwrap();
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                target: Some(original),
                mapper: Some(first_mapper),
                name_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let source = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                vec![proxy],
                Some(first),
                None,
                0,
            )
            .unwrap();
        let before = counts(&store);

        let instantiated = store.instantiate_signature(source, second_mapper).unwrap();
        let record = store.signature(instantiated).unwrap();
        assert_eq!(record.mapper(), Some(second_mapper));
        let symbol = record.parameters()[0];
        let links = store.value_symbol_links(symbol).unwrap();
        let combined = links.mapper.unwrap();
        assert_eq!(links.target, Some(original));
        assert_eq!(links.name_type, Some(string));
        assert_ne!(links.target, Some(proxy));
        assert_eq!(
            store.symbol(symbol).unwrap().check_flags(),
            CheckFlags::INSTANTIATED | CheckFlags::OPTIONAL_PARAMETER
        );
        assert_eq!(
            counts(&store),
            (before.0, before.1 + 1, before.2 + 1, before.3 + 1)
        );
        assert_eq!(instantiate_type(&mut store, first, combined), Ok(string));
    }

    #[test]
    fn cloned_signatures_preserve_provenance_and_clear_lazy_result_fields() {
        let mut store = CanonicalTypeMapperStore::new();
        let string = intrinsic(&mut store, TypeFlags::STRING, "string");
        let type_parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store
            .new_simple_type_mapper(type_parameter, string)
            .unwrap();
        let this = parameter(&mut store, "this", CheckFlags::NONE, Some(string));
        let value = parameter(&mut store, "value", CheckFlags::NONE, Some(type_parameter));
        let target = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let predicate = store
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "value", Some(string))
            .unwrap();
        let flags = SignatureFlags::HAS_LITERAL_TYPES | SignatureFlags::IS_OUTER_CALL_CHAIN;
        let source = store
            .alloc_signature(
                flags,
                None,
                vec![type_parameter],
                Some(this),
                vec![value],
                Some(string),
                Some(predicate),
                1,
            )
            .unwrap();
        assert!(store.set_signature_target_and_mapper(source, Some(target), Some(mapper)));
        let composite = store
            .create_composite_signature(true, vec![target])
            .unwrap();
        assert!(store.set_signature_composite(source, Some(composite.clone())));
        assert!(store.set_signature_isolated_type(source, Some(string)));
        assert!(store.set_signature_resolved_min_argument_count(source, 0));
        let before = counts(&store);

        let clone = store.clone_signature(source).unwrap();
        let record = store.signature(clone).unwrap();
        assert_eq!(record.flags(), SignatureFlags::HAS_LITERAL_TYPES);
        assert_eq!(record.type_parameters(), &[type_parameter]);
        assert_eq!(record.this_parameter(), Some(this));
        assert_eq!(record.parameters(), &[value]);
        assert_eq!(record.target(), Some(target));
        assert_eq!(record.mapper(), Some(mapper));
        assert_eq!(record.composite(), Some(&composite));
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_min_argument_count(), -1);
        assert_eq!(record.resolved_return_type(), None);
        assert_eq!(record.resolved_type_predicate(), None);
        assert_eq!(record.isolated_signature_type(), None);
        assert_eq!(counts(&store), (before.0, before.1, before.2, before.3 + 1));
    }

    #[test]
    fn invalid_signature_instantiation_inputs_fail_before_publication() {
        let mut store = CanonicalTypeMapperStore::new();
        let string = intrinsic(&mut store, TypeFlags::STRING, "string");
        let mapper = store.new_simple_type_mapper(string, string).unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let invalid_type_parameter_signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![string],
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let invalid_rest_signature = store
            .alloc_signature(
                SignatureFlags::HAS_REST_PARAMETER,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let invalid_proxy = parameter(&mut store, "proxy", CheckFlags::INSTANTIATED, None);
        let invalid_proxy_signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                vec![invalid_proxy],
                None,
                None,
                0,
            )
            .unwrap();

        let mut foreign = CanonicalTypeMapperStore::new();
        let foreign_string = intrinsic(&mut foreign, TypeFlags::STRING, "string");
        let foreign_mapper = foreign
            .new_simple_type_mapper(foreign_string, foreign_string)
            .unwrap();
        let foreign_signature = foreign
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let before = counts(&store);

        assert_eq!(
            store.instantiate_signature(signature, foreign_mapper),
            Err(SignatureInstantiationError::InvalidMapper(foreign_mapper))
        );
        assert_eq!(
            store.instantiate_signature(foreign_signature, mapper),
            Err(SignatureInstantiationError::InvalidSignature(
                foreign_signature
            ))
        );
        assert_eq!(
            store.instantiate_signature(invalid_type_parameter_signature, mapper),
            Err(SignatureInstantiationError::InvalidTypeParameter(string))
        );
        assert_eq!(
            store.instantiate_signature(invalid_rest_signature, mapper),
            Err(SignatureInstantiationError::InvalidSignature(
                invalid_rest_signature
            ))
        );
        assert_eq!(
            store.instantiate_signature(invalid_proxy_signature, mapper),
            Err(SignatureInstantiationError::InvalidInstantiatedSymbol(
                invalid_proxy
            ))
        );
        assert_eq!(
            store.clone_signature(foreign_signature),
            Err(SignatureInstantiationError::InvalidSignature(
                foreign_signature
            ))
        );
        assert_eq!(counts(&store), before);
    }

    #[test]
    fn signature_kinds_match_upstream_repr_and_values() {
        assert_eq!(size_of::<SignatureKind>(), size_of::<i32>());
        assert_eq!(
            [SignatureKind::Call as i32, SignatureKind::Construct as i32],
            [0, 1]
        );
    }

    #[test]
    fn signature_flags_match_every_upstream_numeric_value() {
        assert_eq!(size_of::<SignatureFlags>(), size_of::<u32>());
        assert_eq!(
            [
                SignatureFlags::NONE.bits(),
                SignatureFlags::HAS_REST_PARAMETER.bits(),
                SignatureFlags::HAS_LITERAL_TYPES.bits(),
                SignatureFlags::CONSTRUCT.bits(),
                SignatureFlags::ABSTRACT.bits(),
                SignatureFlags::IS_INNER_CALL_CHAIN.bits(),
                SignatureFlags::IS_OUTER_CALL_CHAIN.bits(),
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE.bits(),
                SignatureFlags::IS_NON_INFERRABLE.bits(),
                SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE.bits(),
                SignatureFlags::PROPAGATING_FLAGS.bits(),
                SignatureFlags::CALL_CHAIN_FLAGS.bits(),
            ],
            [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 335, 48]
        );
        assert!(
            SignatureFlags::PROPAGATING_FLAGS
                .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
        );
        assert_eq!(
            SignatureFlags::HAS_REST_PARAMETER
                | SignatureFlags::HAS_LITERAL_TYPES
                | SignatureFlags::CONSTRUCT
                | SignatureFlags::ABSTRACT
                | SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
                | SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE,
            SignatureFlags::PROPAGATING_FLAGS
        );
        assert_eq!(
            SignatureFlags::IS_INNER_CALL_CHAIN | SignatureFlags::IS_OUTER_CALL_CHAIN,
            SignatureFlags::CALL_CHAIN_FLAGS
        );
        assert!(!SignatureFlags::PROPAGATING_FLAGS.intersects(SignatureFlags::CALL_CHAIN_FLAGS));
        assert!(!SignatureFlags::PROPAGATING_FLAGS.intersects(SignatureFlags::IS_NON_INFERRABLE));
    }

    #[test]
    fn element_flags_match_every_upstream_numeric_and_composite_value() {
        assert_eq!(size_of::<ElementFlags>(), size_of::<u32>());
        assert_eq!(
            [
                ElementFlags::NONE.bits(),
                ElementFlags::REQUIRED.bits(),
                ElementFlags::OPTIONAL.bits(),
                ElementFlags::REST.bits(),
                ElementFlags::VARIADIC.bits(),
                ElementFlags::FIXED.bits(),
                ElementFlags::VARIABLE.bits(),
                ElementFlags::NON_REQUIRED.bits(),
                ElementFlags::NON_REST.bits(),
            ],
            [0, 1, 2, 4, 8, 3, 12, 14, 11]
        );
        assert_eq!(
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL,
            ElementFlags::FIXED
        );
        assert_eq!(
            ElementFlags::REST | ElementFlags::VARIADIC,
            ElementFlags::VARIABLE
        );
        assert_eq!(
            ElementFlags::OPTIONAL | ElementFlags::REST | ElementFlags::VARIADIC,
            ElementFlags::NON_REQUIRED
        );
        assert_eq!(
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::VARIADIC,
            ElementFlags::NON_REST
        );
    }

    #[test]
    fn index_flags_match_every_upstream_numeric_value() {
        assert_eq!(size_of::<IndexFlags>(), size_of::<u32>());
        assert_eq!(
            [
                IndexFlags::NONE.bits(),
                IndexFlags::STRINGS_ONLY.bits(),
                IndexFlags::NO_INDEX_SIGNATURES.bits(),
                IndexFlags::NO_REDUCIBLE_CHECK.bits(),
            ],
            [0, 1, 2, 4]
        );
    }

    #[test]
    fn type_predicate_kinds_match_upstream_repr_and_values() {
        assert_eq!(size_of::<TypePredicateKind>(), size_of::<i32>());
        assert_eq!(
            [
                TypePredicateKind::This as i32,
                TypePredicateKind::Identifier as i32,
                TypePredicateKind::AssertsThis as i32,
                TypePredicateKind::AssertsIdentifier as i32,
            ],
            [0, 1, 2, 3]
        );
    }

    #[test]
    fn ternary_values_match_upstream_i8_repr() {
        assert_eq!(size_of::<Ternary>(), size_of::<i8>());
        assert_eq!(
            [
                Ternary::False as i8,
                Ternary::Unknown as i8,
                Ternary::Maybe as i8,
                Ternary::True as i8,
            ],
            [0, 1, 3, -1]
        );
    }

    #[test]
    fn ternary_and_truth_table_selects_the_lesser_value() {
        let values = [
            Ternary::False,
            Ternary::Unknown,
            Ternary::Maybe,
            Ternary::True,
        ];
        let expected = [
            [
                Ternary::False,
                Ternary::False,
                Ternary::False,
                Ternary::False,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Unknown,
                Ternary::Unknown,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::Maybe,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
        ];

        for (left_index, left) in values.into_iter().enumerate() {
            for (right_index, right) in values.into_iter().enumerate() {
                assert_eq!(left & right, expected[left_index][right_index]);
                assert_eq!((left & right) as i8, (left as i8) & (right as i8));
                let mut assigned = left;
                assigned &= right;
                assert_eq!(assigned, expected[left_index][right_index]);
            }
        }
    }

    #[test]
    fn ternary_or_truth_table_selects_the_greater_value() {
        let values = [
            Ternary::False,
            Ternary::Unknown,
            Ternary::Maybe,
            Ternary::True,
        ];
        let expected = [
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
            [
                Ternary::Unknown,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
            [
                Ternary::Maybe,
                Ternary::Maybe,
                Ternary::Maybe,
                Ternary::True,
            ],
            [Ternary::True, Ternary::True, Ternary::True, Ternary::True],
        ];

        for (left_index, left) in values.into_iter().enumerate() {
            for (right_index, right) in values.into_iter().enumerate() {
                assert_eq!(left | right, expected[left_index][right_index]);
                assert_eq!((left | right) as i8, (left as i8) | (right as i8));
                let mut assigned = left;
                assigned |= right;
                assert_eq!(assigned, expected[left_index][right_index]);
            }
        }
    }
}
