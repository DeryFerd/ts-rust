//! Dependency-closed constraint and base-constraint traversal.
//!
//! The installed slice mirrors pinned `getConstraintOfType`,
//! `getConstraintOfTypeParameter`, and `getBaseConstraintOfType` for resolved
//! type parameters plus primitive/literal unions. Declaration and inferred
//! constraint resolution remains checker-query work; an unresolved cache is a
//! typed error, never an invented `unknown` or identity constraint.

use std::collections::HashSet;

use super::{
    RelationUnavailable, SemanticSymbolId, TypeId, TypeResolutionTarget, TypeSystemPropertyName,
    bootstrap::LiteralTypeCacheError,
    conditional_types::{
        ConditionalTypeError, cached_conditional_branches, get_constraint_from_conditional_type,
    },
    instantiate::{InstantiationError, canonical_anonymous_union, instantiate_type},
    intersection_types::IntersectionTypeError,
    mapper::CanonicalTypeMapperStore,
    template_types::TemplateTypeError,
    type_records::{TypeData, TypeRecord},
    types::TypeFlags,
};

const MINIMUM_CONSTRAINT_DEPTH: usize = 10;
const MAXIMUM_CONSTRAINT_DEPTH: usize = 50;

/// Explicit work bound for one base-constraint traversal.
///
/// Depth follows pinned `getResolvedBaseConstraint`: always explore ten
/// levels, then continue to fifty only while recursion identities do not
/// repeat. `max_count` is an additional fail-closed Rust work budget.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)] // Installed ahead of the relation and generic-call consumers.
pub(super) struct ConstraintLimits {
    pub max_count: usize,
}

impl Default for ConstraintLimits {
    fn default() -> Self {
        Self {
            max_count: 5_000_000,
        }
    }
}

/// A missing semantic dependency or explicit traversal boundary.
#[derive(Debug, PartialEq)]
#[allow(dead_code)] // Installed ahead of the relation and generic-call consumers.
pub(super) enum ConstraintError {
    MissingBootstrap,
    InvalidType(TypeId),
    InvalidCachedConstraint(TypeId),
    InvalidConstraintPublication(TypeId),
    UnresolvedTypeParameter(TypeId),
    UnresolvedConditionalBranches(TypeId),
    UnsupportedBaseType(TypeId),
    CountLimit { count: usize, limit: usize },
    Conditional(Box<ConditionalTypeError>),
    Intersection(IntersectionTypeError),
    Instantiation(InstantiationError),
    Relation(RelationUnavailable),
    Template(TemplateTypeError),
    Union(LiteralTypeCacheError),
}

impl std::fmt::Display for ConstraintError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("constraint traversal requires intrinsic sentinels")
            }
            Self::InvalidType(type_) => {
                write!(formatter, "cannot constrain invalid type {type_:?}")
            }
            Self::InvalidCachedConstraint(type_) => write!(
                formatter,
                "constraint cache contains invalid type {type_:?}"
            ),
            Self::InvalidConstraintPublication(type_) => write!(
                formatter,
                "type {type_:?} rejected its resolved constraint cache"
            ),
            Self::UnresolvedTypeParameter(type_) => write!(
                formatter,
                "type parameter {type_:?} requires declaration or inferred constraint resolution"
            ),
            Self::UnresolvedConditionalBranches(type_) => write!(
                formatter,
                "conditional type {type_:?} requires resolved true and false branches"
            ),
            Self::UnsupportedBaseType(type_) => write!(
                formatter,
                "type {type_:?} is outside the installed base-constraint slice"
            ),
            Self::CountLimit { count, limit } => write!(
                formatter,
                "base-constraint count {count} reached configured limit {limit}"
            ),
            Self::Conditional(error) => error.fmt(formatter),
            Self::Intersection(error) => {
                write!(formatter, "intersection constraint failed: {error:?}")
            }
            Self::Instantiation(error) => error.fmt(formatter),
            Self::Relation(error) => error.fmt(formatter),
            Self::Template(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ConstraintError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Conditional(error) => Some(error.as_ref()),
            Self::Instantiation(error) => Some(error),
            Self::Relation(error) => Some(error),
            Self::Template(error) => Some(error),
            Self::Union(error) => Some(error),
            _ => None,
        }
    }
}

impl From<InstantiationError> for ConstraintError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
    }
}

impl From<LiteralTypeCacheError> for ConstraintError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

impl From<ConditionalTypeError> for ConstraintError {
    fn from(error: ConditionalTypeError) -> Self {
        Self::Conditional(Box::new(error))
    }
}

impl From<IntersectionTypeError> for ConstraintError {
    fn from(error: IntersectionTypeError) -> Self {
        Self::Intersection(error)
    }
}

impl From<RelationUnavailable> for ConstraintError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<TemplateTypeError> for ConstraintError {
    fn from(error: TemplateTypeError) -> Self {
        Self::Template(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BaseConstraint {
    Type(TypeId),
    None,
    Circular,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ConstraintRecursionIdentity {
    Type(TypeId),
    Symbol(SemanticSymbolId),
}

#[derive(Debug)]
enum ConstraintKind {
    Leaf,
    Parameter {
        is_this_type: bool,
    },
    Union(Vec<TypeId>),
    Intersection(Vec<TypeId>),
    Index,
    Template {
        texts: Vec<String>,
        types: Vec<TypeId>,
    },
    StringMapping {
        symbol: Option<SemanticSymbolId>,
        target: TypeId,
    },
    Conditional,
    Substitution {
        base_type: TypeId,
        constraint: TypeId,
    },
    Unsupported,
}

struct ConstraintSession<'store> {
    store: &'store mut CanonicalTypeMapperStore,
    limits: ConstraintLimits,
    count: usize,
    resolution_stack: Vec<TypeId>,
    failed_resolutions: HashSet<TypeId>,
    no_constraint: TypeId,
    circular_constraint: TypeId,
}

impl<'store> ConstraintSession<'store> {
    fn new(
        store: &'store mut CanonicalTypeMapperStore,
        limits: ConstraintLimits,
    ) -> Result<Self, ConstraintError> {
        let (no_constraint, circular_constraint) = store
            .intrinsic_bootstrap()
            .map(|bootstrap| {
                (
                    bootstrap.no_constraint_type,
                    bootstrap.circular_constraint_type,
                )
            })
            .ok_or(ConstraintError::MissingBootstrap)?;
        Ok(Self {
            store,
            limits,
            count: 0,
            resolution_stack: Vec::new(),
            failed_resolutions: HashSet::new(),
            no_constraint,
            circular_constraint,
        })
    }

    fn enter(&mut self) -> Result<(), ConstraintError> {
        if self.count >= self.limits.max_count {
            return Err(ConstraintError::CountLimit {
                count: self.count,
                limit: self.limits.max_count,
            });
        }
        self.count += 1;
        Ok(())
    }

    fn classify_constraint(&self, type_: TypeId) -> Result<BaseConstraint, ConstraintError> {
        if self.store.type_payload(type_).is_none() {
            Err(ConstraintError::InvalidCachedConstraint(type_))
        } else if type_ == self.no_constraint {
            Ok(BaseConstraint::None)
        } else if type_ == self.circular_constraint {
            Ok(BaseConstraint::Circular)
        } else {
            Ok(BaseConstraint::Type(type_))
        }
    }

    fn constraint_of_type_parameter(
        &mut self,
        type_: TypeId,
    ) -> Result<BaseConstraint, ConstraintError> {
        match self.resolve_base_constraint(type_, &mut Vec::new())? {
            BaseConstraint::Circular => return Ok(BaseConstraint::None),
            BaseConstraint::Type(_) | BaseConstraint::None => {}
        }
        self.direct_constraint(type_)
    }

    fn direct_constraint(&mut self, type_: TypeId) -> Result<BaseConstraint, ConstraintError> {
        let (constraint, target, mapper, resolved_default_type) = {
            let record = self
                .store
                .type_payload(type_)
                .ok_or(ConstraintError::InvalidType(type_))?;
            let TypeData::TypeParameter(data) = record.data() else {
                return Err(ConstraintError::UnsupportedBaseType(type_));
            };
            (
                data.constraint,
                data.target,
                data.mapper,
                data.resolved_default_type,
            )
        };
        if let Some(constraint) = constraint {
            return self.classify_constraint(constraint);
        }
        let Some(target) = target else {
            return Err(ConstraintError::UnresolvedTypeParameter(type_));
        };
        let target_constraint = self.constraint_of_type_parameter(target)?;
        let result = if let BaseConstraint::Type(target_constraint) = target_constraint {
            if let Some(mapper) = mapper {
                let instantiated = instantiate_type(self.store, target_constraint, mapper)?;
                self.classify_constraint(instantiated)?
            } else {
                BaseConstraint::Type(target_constraint)
            }
        } else {
            target_constraint
        };
        let cached = match result {
            BaseConstraint::Type(type_) => type_,
            BaseConstraint::None => self.no_constraint,
            BaseConstraint::Circular => self.circular_constraint,
        };
        if !self.store.set_type_parameter_resolution(
            type_,
            Some(cached),
            Some(target),
            mapper,
            resolved_default_type,
        ) {
            return Err(ConstraintError::InvalidConstraintPublication(type_));
        }
        Ok(result)
    }

    fn resolve_base_constraint(
        &mut self,
        type_: TypeId,
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let (cached, kind, identity, constrained) = {
            let record = self
                .store
                .type_payload(type_)
                .ok_or(ConstraintError::InvalidType(type_))?;
            let kind = match record.data() {
                TypeData::Intrinsic(_)
                | TypeData::Literal(_)
                | TypeData::UniqueEsSymbol(_)
                | TypeData::Interface(_)
                | TypeData::Tuple(_) => ConstraintKind::Leaf,
                TypeData::TypeReference(reference)
                    if reference.object.target.is_some()
                        && reference.resolved_type_arguments.is_some() =>
                {
                    ConstraintKind::Leaf
                }
                TypeData::TypeParameter(data) => ConstraintKind::Parameter {
                    is_this_type: data.is_this_type,
                },
                TypeData::Union(data) => ConstraintKind::Union(data.union.types.clone()),
                TypeData::Intersection(data) => {
                    ConstraintKind::Intersection(data.intersection.types.clone())
                }
                TypeData::Index(_) => ConstraintKind::Index,
                TypeData::TemplateLiteral(data) => ConstraintKind::Template {
                    texts: data.texts.clone(),
                    types: data.types.clone(),
                },
                TypeData::StringMapping(data) => ConstraintKind::StringMapping {
                    symbol: record.symbol(),
                    target: data.target,
                },
                TypeData::Conditional(_) => ConstraintKind::Conditional,
                TypeData::Substitution(data) => ConstraintKind::Substitution {
                    base_type: data.base_type,
                    constraint: data.constraint,
                },
                _ => ConstraintKind::Unsupported,
            };
            let identity = match record.data() {
                TypeData::TypeParameter(_) => record.symbol().map_or(
                    ConstraintRecursionIdentity::Type(type_),
                    ConstraintRecursionIdentity::Symbol,
                ),
                _ => ConstraintRecursionIdentity::Type(type_),
            };
            (
                record
                    .data()
                    .constrained()
                    .and_then(|data| data.resolved_base_constraint),
                kind,
                identity,
                record.data().constrained().is_some(),
            )
        };
        if let Some(cached) = cached {
            return self.classify_constraint(cached);
        }
        if matches!(kind, ConstraintKind::Leaf) {
            return Ok(BaseConstraint::Type(type_));
        }
        self.enter()?;
        if let Some(cycle_start) = self
            .resolution_stack
            .iter()
            .position(|active| *active == type_)
        {
            self.failed_resolutions
                .extend(self.resolution_stack[cycle_start..].iter().copied());
            return Ok(BaseConstraint::Circular);
        }
        if !self
            .store
            .push_type_resolution(
                TypeResolutionTarget::Type(type_),
                TypeSystemPropertyName::ResolvedBaseConstraint,
            )
            .map_err(|_| ConstraintError::InvalidConstraintPublication(type_))?
        {
            return Ok(BaseConstraint::Circular);
        }
        self.resolution_stack.push(type_);
        let should_explore = stack.len() < MINIMUM_CONSTRAINT_DEPTH
            || stack.len() < MAXIMUM_CONSTRAINT_DEPTH && !stack.contains(&identity);
        let result = if should_explore {
            stack.push(identity);
            let result = self.compute_active_constraint(type_, kind, stack);
            stack.pop();
            result
        } else {
            Ok(BaseConstraint::None)
        };
        let cycle_free = self
            .store
            .pop_type_resolution()
            .ok_or(ConstraintError::InvalidConstraintPublication(type_))?;
        let popped = self.resolution_stack.pop();
        debug_assert_eq!(popped, Some(type_));
        let mut result = result?;
        let failed = self.failed_resolutions.remove(&type_);
        if !cycle_free || failed {
            result = BaseConstraint::Circular;
        }
        if constrained {
            let cached = match result {
                BaseConstraint::Type(type_) => type_,
                BaseConstraint::None => self.no_constraint,
                BaseConstraint::Circular => self.circular_constraint,
            };
            if !self.store.set_resolved_base_constraint(type_, Some(cached)) {
                return Err(ConstraintError::InvalidConstraintPublication(type_));
            }
        }
        Ok(result)
    }

    fn compute_active_constraint(
        &mut self,
        type_: TypeId,
        kind: ConstraintKind,
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        match kind {
            ConstraintKind::Leaf => unreachable!("leaf types return before recursion limits"),
            ConstraintKind::Parameter { is_this_type } => {
                let constraint = self.direct_constraint(type_)?;
                if is_this_type {
                    return Ok(constraint);
                }
                match constraint {
                    BaseConstraint::Type(constraint) => {
                        Ok(match self.resolve_base_constraint(constraint, stack)? {
                            BaseConstraint::Type(constraint) => BaseConstraint::Type(constraint),
                            BaseConstraint::None | BaseConstraint::Circular => BaseConstraint::None,
                        })
                    }
                    BaseConstraint::None | BaseConstraint::Circular => Ok(BaseConstraint::None),
                }
            }
            ConstraintKind::Union(members) => self.compute_union_constraint(type_, &members, stack),
            ConstraintKind::Intersection(members) => {
                self.compute_intersection_constraint(type_, &members, stack)
            }
            ConstraintKind::Index => Ok(BaseConstraint::Type(
                self.store
                    .intrinsic_bootstrap()
                    .ok_or(ConstraintError::MissingBootstrap)?
                    .string_number_symbol_type,
            )),
            ConstraintKind::Template { texts, types } => {
                self.compute_template_constraint(&texts, &types, stack)
            }
            ConstraintKind::StringMapping { symbol, target } => {
                self.compute_string_mapping_constraint(symbol, target, stack)
            }
            ConstraintKind::Conditional => self.compute_conditional_constraint(type_, stack),
            ConstraintKind::Substitution {
                base_type,
                constraint,
            } => self.compute_substitution_constraint(base_type, constraint, stack),
            ConstraintKind::Unsupported => Err(ConstraintError::UnsupportedBaseType(type_)),
        }
    }

    fn compute_union_constraint(
        &mut self,
        source: TypeId,
        types: &[TypeId],
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let mut constraints = Vec::with_capacity(types.len());
        let mut changed = false;
        let mut missing = false;
        for type_ in types {
            match self.resolve_base_constraint(*type_, stack)? {
                BaseConstraint::Type(constraint) => {
                    changed |= constraint != *type_;
                    constraints.push(constraint);
                }
                BaseConstraint::None | BaseConstraint::Circular => {
                    changed = true;
                    missing = true;
                }
            }
        }
        if missing {
            return Ok(BaseConstraint::None);
        }
        if !changed {
            return Ok(BaseConstraint::Type(source));
        }
        Ok(BaseConstraint::Type(canonical_anonymous_union(
            self.store,
            &constraints,
        )?))
    }

    fn compute_intersection_constraint(
        &mut self,
        source: TypeId,
        types: &[TypeId],
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let mut constraints = Vec::with_capacity(types.len());
        let mut changed = false;
        for type_ in types {
            match self.resolve_base_constraint(*type_, stack)? {
                BaseConstraint::Type(constraint) => {
                    changed |= constraint != *type_;
                    constraints.push(constraint);
                }
                BaseConstraint::None | BaseConstraint::Circular => changed = true,
            }
        }
        if !changed {
            return Ok(BaseConstraint::Type(source));
        }
        if constraints.is_empty() {
            return Ok(BaseConstraint::None);
        }
        self.intersect_constraints(&constraints)
            .map(BaseConstraint::Type)
    }

    fn compute_template_constraint(
        &mut self,
        texts: &[String],
        types: &[TypeId],
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let mut constraints = Vec::with_capacity(types.len());
        for type_ in types {
            match self.resolve_base_constraint(*type_, stack)? {
                BaseConstraint::Type(constraint) => constraints.push(constraint),
                BaseConstraint::None | BaseConstraint::Circular => {
                    return Ok(BaseConstraint::Type(
                        self.store
                            .intrinsic_bootstrap()
                            .ok_or(ConstraintError::MissingBootstrap)?
                            .string_type,
                    ));
                }
            }
        }
        Ok(BaseConstraint::Type(
            self.store.get_template_literal_type(texts, &constraints)?,
        ))
    }

    fn compute_string_mapping_constraint(
        &mut self,
        symbol: Option<SemanticSymbolId>,
        target: TypeId,
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        if let BaseConstraint::Type(constraint) = self.resolve_base_constraint(target, stack)?
            && constraint != target
        {
            let symbol = symbol.ok_or(ConstraintError::UnsupportedBaseType(target))?;
            return Ok(BaseConstraint::Type(
                self.store.get_string_mapping_type(symbol, constraint)?,
            ));
        }
        Ok(BaseConstraint::Type(
            self.store
                .intrinsic_bootstrap()
                .ok_or(ConstraintError::MissingBootstrap)?
                .string_type,
        ))
    }

    fn compute_conditional_constraint(
        &mut self,
        conditional: TypeId,
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let branches = cached_conditional_branches(self.store, conditional)?
            .ok_or(ConstraintError::UnresolvedConditionalBranches(conditional))?;
        let constraint =
            get_constraint_from_conditional_type(self.store, conditional, branches, None, None)?;
        self.resolve_base_constraint(constraint, stack)
    }

    fn compute_substitution_constraint(
        &mut self,
        base_type: TypeId,
        constraint: TypeId,
        stack: &mut Vec<ConstraintRecursionIdentity>,
    ) -> Result<BaseConstraint, ConstraintError> {
        let base = self.resolve_base_constraint(base_type, stack)?;
        let constraint = self.resolve_base_constraint(constraint, stack)?;
        match (base, constraint) {
            (BaseConstraint::Type(base), BaseConstraint::Type(constraint)) => self
                .intersect_constraints(&[base, constraint])
                .map(BaseConstraint::Type),
            _ => Ok(BaseConstraint::None),
        }
    }

    fn intersect_constraints(&mut self, types: &[TypeId]) -> Result<TypeId, ConstraintError> {
        let mut result = types[0];
        let never = self
            .store
            .intrinsic_bootstrap()
            .ok_or(ConstraintError::MissingBootstrap)?
            .never_type;
        for candidate in &types[1..] {
            if result == *candidate || self.store.is_type_assignable_to(result, *candidate)? {
                continue;
            }
            if self.store.is_type_assignable_to(*candidate, result)? {
                result = *candidate;
                continue;
            }
            let result_flags = self
                .store
                .type_payload(result)
                .map(TypeRecord::flags)
                .ok_or(ConstraintError::InvalidType(result))?;
            let candidate_flags = self
                .store
                .type_payload(*candidate)
                .map(TypeRecord::flags)
                .ok_or(ConstraintError::InvalidType(*candidate))?;
            if result_flags.intersects(TypeFlags::PRIMITIVE)
                && candidate_flags.intersects(TypeFlags::PRIMITIVE)
            {
                return Ok(never);
            }
            result = self
                .store
                .canonical_intersection_type(&[result, *candidate], None)?;
        }
        Ok(result)
    }
}

/// Pinned `getConstraintOfType` for the installed dependency-closed domain.
#[allow(dead_code)] // Installed ahead of the relation and generic-call consumers.
pub(super) fn get_constraint_of_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<TypeId>, ConstraintError> {
    get_constraint_of_type_with_limits(store, type_, ConstraintLimits::default())
}

#[allow(dead_code)] // Configurable boundary used by checker-query integration and focused tests.
pub(super) fn get_constraint_of_type_with_limits(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    limits: ConstraintLimits,
) -> Result<Option<TypeId>, ConstraintError> {
    let mut session = ConstraintSession::new(store, limits)?;
    let kind = match session
        .store
        .type_payload(type_)
        .ok_or(ConstraintError::InvalidType(type_))?
        .data()
    {
        TypeData::TypeParameter(_) => 0,
        TypeData::Union(_)
        | TypeData::Intersection(_)
        | TypeData::Index(_)
        | TypeData::TemplateLiteral(_)
        | TypeData::StringMapping(_)
        | TypeData::Conditional(_)
        | TypeData::Substitution(_) => 1,
        _ => return Ok(None),
    };
    let result = if kind == 0 {
        session.constraint_of_type_parameter(type_)?
    } else {
        session.resolve_base_constraint(type_, &mut Vec::new())?
    };
    Ok(match result {
        BaseConstraint::Type(type_) => Some(type_),
        BaseConstraint::None | BaseConstraint::Circular => None,
    })
}

/// Pinned `getBaseConstraintOfType` for supported instantiable records.
#[allow(dead_code)] // Installed ahead of the relation and generic-call consumers.
pub(super) fn get_base_constraint_of_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<TypeId>, ConstraintError> {
    get_base_constraint_of_type_with_limits(store, type_, ConstraintLimits::default())
}

#[allow(dead_code)] // Configurable boundary used by checker-query integration and focused tests.
pub(super) fn get_base_constraint_of_type_with_limits(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    limits: ConstraintLimits,
) -> Result<Option<TypeId>, ConstraintError> {
    let mut session = ConstraintSession::new(store, limits)?;
    let record = session
        .store
        .type_payload(type_)
        .ok_or(ConstraintError::InvalidType(type_))?;
    if !matches!(
        record.data(),
        TypeData::TypeParameter(_)
            | TypeData::Union(_)
            | TypeData::Intersection(_)
            | TypeData::Index(_)
            | TypeData::TemplateLiteral(_)
            | TypeData::StringMapping(_)
            | TypeData::Conditional(_)
            | TypeData::Substitution(_)
    ) {
        return Ok(None);
    }
    Ok(
        match session.resolve_base_constraint(type_, &mut Vec::new())? {
            BaseConstraint::Type(type_) => Some(type_),
            BaseConstraint::None | BaseConstraint::Circular => None,
        },
    )
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{EscapedName, SymbolData, SymbolFlags};
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore,
        mapper::TypeMapper,
        signatures::IndexFlags,
        type_records::{TypeData, TypeRecord},
        types::ObjectFlags,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn constrained_chain(
        store: &mut CanonicalTypeMapperStore,
        length: usize,
        terminal: TypeId,
    ) -> TypeId {
        let mut constraint = terminal;
        for _ in 0..length {
            let parameter = store.alloc_type_parameter(None).unwrap();
            assert!(store.set_type_parameter_resolution(
                parameter,
                Some(constraint),
                None,
                None,
                None,
            ));
            constraint = parameter;
        }
        constraint
    }

    #[test]
    fn direct_and_base_constraints_remain_distinct_and_publish_base_cache() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let outer = store.alloc_type_parameter(None).unwrap();
        let inner = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(inner, Some(string), None, None, None));
        assert!(store.set_type_parameter_resolution(outer, Some(inner), None, None, None));

        assert_eq!(get_constraint_of_type(&mut store, outer), Ok(Some(inner)));
        assert_eq!(
            get_base_constraint_of_type(&mut store, outer),
            Ok(Some(string))
        );
        let TypeData::TypeParameter(data) = store.type_payload(outer).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constrained.resolved_base_constraint, Some(string));
        assert_eq!(
            get_base_constraint_of_type_with_limits(
                &mut store,
                outer,
                ConstraintLimits { max_count: 0 },
            ),
            Ok(Some(string)),
            "a resolved cache precedes the fail-closed work budget"
        );
    }

    #[test]
    fn no_constraint_and_circular_chains_publish_distinct_sentinels() {
        let mut store = initialized_store();
        let (no_constraint, circular_constraint, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.no_constraint_type,
                bootstrap.circular_constraint_type,
                bootstrap.string_type,
            )
        };
        let unconstrained = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(
            unconstrained,
            Some(no_constraint),
            None,
            None,
            None,
        ));
        assert_eq!(get_constraint_of_type(&mut store, unconstrained), Ok(None));
        assert_eq!(
            get_base_constraint_of_type(&mut store, unconstrained),
            Ok(None)
        );

        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(first, Some(second), None, None, None));
        assert!(store.set_type_parameter_resolution(second, Some(first), None, None, None));
        assert_eq!(get_constraint_of_type(&mut store, first), Ok(None));
        assert_eq!(get_base_constraint_of_type(&mut store, first), Ok(None));
        for parameter in [first, second] {
            let TypeData::TypeParameter(data) = store.type_payload(parameter).unwrap().data()
            else {
                unreachable!();
            };
            assert_eq!(
                data.constrained.resolved_base_constraint,
                Some(circular_constraint)
            );
        }

        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, string])
            .unwrap();
        assert_eq!(get_base_constraint_of_type(&mut store, union), Ok(None));
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(
            data.union.structured.constrained.resolved_base_constraint,
            Some(no_constraint),
            "a circular union member is a missing next constraint"
        );
    }

    #[test]
    fn changed_union_constraints_use_canonical_literal_reduction() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(string), None, None, None));
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, number])
            .unwrap();

        let result = get_base_constraint_of_type(&mut store, union)
            .unwrap()
            .unwrap();
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("two primitive constraints must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
        let TypeData::Union(source) = store.type_payload(union).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(
            source.union.structured.constrained.resolved_base_constraint,
            Some(result)
        );
    }

    #[test]
    fn active_union_cycle_marks_only_participating_resolution_frames_circular() {
        let mut store = initialized_store();
        let (string, no_constraint, circular_constraint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.no_constraint_type,
                bootstrap.circular_constraint_type,
            )
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(union), None, None, None,));

        assert_eq!(get_constraint_of_type(&mut store, parameter), Ok(None));
        for type_ in [parameter, union] {
            let cached = store
                .type_payload(type_)
                .unwrap()
                .data()
                .constrained()
                .unwrap()
                .resolved_base_constraint;
            assert_eq!(cached, Some(circular_constraint));
        }

        let outer = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(outer, Some(parameter), None, None, None,));
        assert_eq!(get_base_constraint_of_type(&mut store, outer), Ok(None));
        let TypeData::TypeParameter(data) = store.type_payload(outer).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(
            data.constrained.resolved_base_constraint,
            Some(no_constraint),
            "a caller outside the active cycle observes a missing next constraint"
        );
    }

    #[test]
    fn missing_union_member_does_not_hide_later_unsupported_member() {
        let mut store = initialized_store();
        let no_constraint = store.intrinsic_bootstrap().unwrap().no_constraint_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(
            parameter,
            Some(no_constraint),
            None,
            None,
            None,
        ));
        let unsupported = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, unsupported])
            .unwrap();

        assert_eq!(
            get_base_constraint_of_type(&mut store, union),
            Err(ConstraintError::UnsupportedBaseType(unsupported))
        );
    }

    #[test]
    fn target_constraints_are_instantiated_and_cached_through_retained_mapper() {
        let mut store = initialized_store();
        let (string, no_constraint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.no_constraint_type)
        };
        let target = store.alloc_type_parameter(None).unwrap();
        let target_constraint = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(
            target_constraint,
            Some(no_constraint),
            None,
            None,
            None,
        ));
        assert!(store.set_type_parameter_resolution(
            target,
            Some(target_constraint),
            None,
            None,
            None,
        ));
        let mapper = store
            .new_simple_type_mapper(target_constraint, string)
            .unwrap();
        let clone = store.alloc_type_parameter(None).unwrap();
        assert!(
            store.set_type_parameter_resolution(clone, None, Some(target), Some(mapper), None,)
        );

        assert_eq!(get_constraint_of_type(&mut store, clone), Ok(Some(string)));
        let TypeData::TypeParameter(data) = store.type_payload(clone).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constraint, Some(string));
        assert_eq!(
            get_base_constraint_of_type(&mut store, clone),
            Ok(Some(string))
        );
    }

    #[test]
    fn pinned_constraint_depth_returns_leaf_at_50_and_cuts_off_at_51() {
        let mut shallow = initialized_store();
        let shallow_string = shallow.intrinsic_bootstrap().unwrap().string_type;
        let shallow_root = constrained_chain(&mut shallow, 50, shallow_string);
        assert_eq!(
            get_base_constraint_of_type(&mut shallow, shallow_root),
            Ok(Some(shallow_string))
        );

        let mut deep = initialized_store();
        let (deep_string, no_constraint) = {
            let bootstrap = deep.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.no_constraint_type)
        };
        let deep_root = constrained_chain(&mut deep, 51, deep_string);
        assert_eq!(get_base_constraint_of_type(&mut deep, deep_root), Ok(None));
        let TypeData::TypeParameter(data) = deep.type_payload(deep_root).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(
            data.constrained.resolved_base_constraint,
            Some(no_constraint)
        );
    }

    #[test]
    fn unresolved_constraints_and_count_limit_are_explicit() {
        let mut store = initialized_store();
        let unresolved = store.alloc_type_parameter(None).unwrap();
        assert_eq!(
            get_constraint_of_type(&mut store, unresolved),
            Err(ConstraintError::UnresolvedTypeParameter(unresolved))
        );

        let constrained = store.alloc_type_parameter(None).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert!(store.set_type_parameter_resolution(constrained, Some(string), None, None, None,));
        assert_eq!(
            get_base_constraint_of_type_with_limits(
                &mut store,
                constrained,
                ConstraintLimits { max_count: 0 },
            ),
            Err(ConstraintError::CountLimit { count: 0, limit: 0 })
        );
    }

    #[test]
    fn foreign_base_constraint_cache_cannot_be_published() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let foreign = initialized_store();
        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;

        assert!(!store.set_resolved_base_constraint(parameter, Some(foreign_string)));
        let TypeData::TypeParameter(data) = store.type_payload(parameter).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constrained.resolved_base_constraint, None);
    }

    #[test]
    fn index_constraints_use_the_canonical_property_key_union() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, keys) = (bootstrap.string_type, bootstrap.string_number_symbol_type);
        let index = store.alloc_index_type(string, IndexFlags::NONE).unwrap();

        assert_eq!(get_constraint_of_type(&mut store, index), Ok(Some(keys)));
        assert_eq!(
            get_base_constraint_of_type(&mut store, index),
            Ok(Some(keys))
        );
        let TypeData::Index(data) = store.type_payload(index).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constrained.resolved_base_constraint, Some(keys));
    }

    #[test]
    fn template_constraints_substitute_resolved_parameter_constraints() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let literal = store
            .regular_string_literal_type("value".to_owned())
            .unwrap();
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(literal), None, None, None));
        let template = store
            .alloc_template_literal_type(vec!["prefix-".to_owned(), String::new()], vec![parameter])
            .unwrap();
        let expected = store
            .regular_string_literal_type("prefix-value".to_owned())
            .unwrap();

        assert_eq!(
            get_base_constraint_of_type(&mut store, template),
            Ok(Some(expected))
        );
        let TypeData::TemplateLiteral(data) = store.type_payload(template).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constrained.resolved_base_constraint, Some(expected));

        let unconstrained = store.alloc_type_parameter(None).unwrap();
        let no_constraint = store.intrinsic_bootstrap().unwrap().no_constraint_type;
        assert!(store.set_type_parameter_resolution(
            unconstrained,
            Some(no_constraint),
            None,
            None,
            None,
        ));
        let fallback = store
            .alloc_template_literal_type(vec![String::new(), String::new()], vec![unconstrained])
            .unwrap();
        assert_eq!(
            get_base_constraint_of_type(&mut store, fallback),
            Ok(Some(string))
        );
    }

    #[test]
    fn substitution_and_intersection_constraints_reduce_primitive_domains() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(string), None, None, None));

        let compatible = store.alloc_substitution_type(parameter, string).unwrap();
        assert_eq!(
            get_base_constraint_of_type(&mut store, compatible),
            Ok(Some(string))
        );

        let incompatible = store.alloc_substitution_type(parameter, number).unwrap();
        assert_eq!(
            get_base_constraint_of_type(&mut store, incompatible),
            Ok(Some(never))
        );

        let intersection = store
            .alloc_intersection_type(ObjectFlags::NONE, vec![parameter, number])
            .unwrap();
        assert_eq!(
            get_base_constraint_of_type(&mut store, intersection),
            Ok(Some(never))
        );
    }

    #[test]
    fn string_mapping_constraints_apply_the_intrinsic_to_parameter_bounds() {
        let mut store = initialized_store();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Uppercase"),
            ))
            .unwrap();
        let lower = store
            .regular_string_literal_type("value".to_owned())
            .unwrap();
        let expected = store
            .regular_string_literal_type("VALUE".to_owned())
            .unwrap();
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(lower), None, None, None));
        let mapping = store.get_string_mapping_type(symbol, parameter).unwrap();

        assert_eq!(
            get_base_constraint_of_type(&mut store, mapping),
            Ok(Some(expected))
        );
        let TypeData::StringMapping(data) = store.type_payload(mapping).unwrap().data() else {
            unreachable!();
        };
        assert_eq!(data.constrained.resolved_base_constraint, Some(expected));
    }

    #[test]
    fn array_like_and_keyof_parameter_bounds_preserve_their_exact_constraints() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (unknown, keys) = (bootstrap.unknown_type, bootstrap.string_number_symbol_type);
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let array = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(array, Some(target), None));
        assert!(store.set_type_reference_resolution(array, None, Some(vec![unknown])));

        let array_parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(
            array_parameter,
            Some(array),
            None,
            None,
            None,
        ));
        assert_eq!(
            get_constraint_of_type(&mut store, array_parameter),
            Ok(Some(array))
        );
        assert_eq!(
            get_base_constraint_of_type(&mut store, array_parameter),
            Ok(Some(array))
        );

        let keyof = store.alloc_index_type(unknown, IndexFlags::NONE).unwrap();
        let key_parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(key_parameter, Some(keyof), None, None, None,));
        assert_eq!(
            get_constraint_of_type(&mut store, key_parameter),
            Ok(Some(keyof))
        );
        assert_eq!(
            get_base_constraint_of_type(&mut store, key_parameter),
            Ok(Some(keys))
        );
    }

    #[test]
    fn conditional_constraint_reentry_uses_the_shared_resolution_stack() {
        let mut store = initialized_store();
        let parsed = parse_source_file("type Loop<T> = T extends string ? string : string;");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(91);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ConditionalType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, circular) = (bootstrap.string_type, bootstrap.circular_constraint_type);
        let parameter = store.alloc_type_parameter(None).unwrap();
        let root = store
            .alloc_conditional_root(
                node,
                parameter,
                string,
                true,
                None,
                Some(vec![parameter]),
                None,
            )
            .unwrap();
        let conditional = store
            .alloc_conditional_type(root, parameter, string, None, None)
            .unwrap();
        assert!(store.set_conditional_resolution(
            conditional,
            Some(string),
            Some(string),
            Some(string),
            None,
            None,
            None,
            None,
        ));
        assert!(store.set_type_parameter_resolution(
            parameter,
            Some(conditional),
            None,
            None,
            None,
        ));

        assert_eq!(get_base_constraint_of_type(&mut store, parameter), Ok(None));
        assert!(store.type_resolution_is_empty());
        for type_ in [parameter, conditional] {
            let cached = store
                .type_payload(type_)
                .and_then(|record| record.data().constrained())
                .and_then(|constraint| constraint.resolved_base_constraint);
            assert_eq!(cached, Some(circular));
        }
        let warm = (store.type_len(), store.type_resolution_len());
        assert_eq!(get_base_constraint_of_type(&mut store, parameter), Ok(None));
        assert_eq!((store.type_len(), store.type_resolution_len()), warm);
    }
}
