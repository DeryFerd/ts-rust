//! Exact dependency-closed fast and simple type relations.
//!
//! This module ports `isTypeRelatedTo`, `isSimpleTypeRelatedTo`, and their
//! no-diagnostic entry points from pinned `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. It deliberately stops before
//! union decomposition and uncached structural comparison. Those paths return
//! [`RelationUnavailable`] instead of being misreported as unrelated.

use ts_binder::{SemanticSymbolId, SymbolFlags};

use super::{
    ids::TypeId,
    links::MembersOrExportsResolutionKind,
    relation::{IntersectionState, RelationComparisonResult, RelationKeyUnavailable, RelationKind},
    signatures::Ternary,
    store::SemanticStore,
    type_records::{TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// A canonical record or checker capability needed to answer a relation was
/// unavailable. No variant is a negative relation result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelationUnavailable {
    MissingBootstrap,
    Type(TypeId),
    Symbol(SemanticSymbolId),
    MalformedLiteral(TypeId),
    MalformedStructuredType(TypeId),
    MalformedEnumType(TypeId),
    EnumRelation {
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    LateBoundMembers(SemanticSymbolId),
    InvalidSymbolMembers(SemanticSymbolId),
    RelationKeyType(TypeId),
    RelationKeyTypeReferenceArguments(TypeId),
    RelationKeyTypeReferenceTarget(TypeId),
    RelationKeyTypeParameterConstraint(TypeId),
    RelationKeyCyclicGenericArguments(TypeId),
    InvalidUnknownLikeUnionState(TypeId),
    StructuralRelation {
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    },
}

impl std::fmt::Display for RelationUnavailable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("type relations require intrinsic checker bootstrap")
            }
            Self::Type(type_id) => write!(formatter, "type {type_id:?} is not store-owned"),
            Self::Symbol(symbol) => write!(formatter, "symbol {symbol:?} is not store-owned"),
            Self::MalformedLiteral(type_id) => {
                write!(formatter, "type {type_id:?} has an invalid literal payload")
            }
            Self::MalformedStructuredType(type_id) => {
                write!(
                    formatter,
                    "type {type_id:?} has an invalid structured payload"
                )
            }
            Self::MalformedEnumType(type_id) => {
                write!(formatter, "enum type {type_id:?} has no canonical symbol")
            }
            Self::EnumRelation { source, target } => write!(
                formatter,
                "enum relation between {source:?} and {target:?} requires enum member semantics"
            ),
            Self::LateBoundMembers(symbol) => write!(
                formatter,
                "empty-object classification for {symbol:?} requires late-bound members"
            ),
            Self::InvalidSymbolMembers(symbol) => {
                write!(
                    formatter,
                    "symbol {symbol:?} references an invalid member table"
                )
            }
            Self::RelationKeyType(type_id) => {
                write!(formatter, "relation key cannot read type {type_id:?}")
            }
            Self::RelationKeyTypeReferenceArguments(type_id) => write!(
                formatter,
                "relation key requires resolved arguments for {type_id:?}"
            ),
            Self::RelationKeyTypeReferenceTarget(type_id) => write!(
                formatter,
                "relation key requires a resolved target for {type_id:?}"
            ),
            Self::RelationKeyTypeParameterConstraint(type_id) => write!(
                formatter,
                "relation key requires the constraint state of {type_id:?}"
            ),
            Self::RelationKeyCyclicGenericArguments(type_id) => write!(
                formatter,
                "relation key found cyclic generic arguments at {type_id:?}"
            ),
            Self::InvalidUnknownLikeUnionState(type_id) => write!(
                formatter,
                "type {type_id:?} rejected its unknown-like union cache state"
            ),
            Self::StructuralRelation {
                source,
                target,
                relation,
            } => write!(
                formatter,
                "uncached {relation:?} relation from {source:?} to {target:?} requires structural comparison"
            ),
        }
    }
}

impl std::error::Error for RelationUnavailable {}

#[derive(Clone, Copy)]
struct RelationBootstrapFacts {
    strict_null_checks: bool,
    wildcard_type: TypeId,
    any_function_type: TypeId,
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    /// Pinned `isTypeIdenticalTo` for the dependency-closed relation domain.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_identical_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Identity)
    }

    /// Pinned `compareTypesIdentical` for the dependency-closed relation domain.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_identical(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_identical_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesAssignableSimple`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_assignable_simple(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_assignable_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesAssignableWorker`.
    ///
    /// The pinned worker ignores `reportErrors` and delegates to the same
    /// no-diagnostic entry point, so this dependency-closed port does too.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_assignable_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        _report_errors: bool,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_assignable_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_subtype_of(source, target).map(bool_to_ternary)
    }

    /// Pinned `isTypeAssignableTo`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_assignable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Assignable)
    }

    /// Pinned `isTypeSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Subtype)
    }

    /// Pinned `isTypeStrictSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_strict_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::StrictSubtype)
    }

    /// Pinned `isTypeComparableTo`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_comparable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Comparable)
    }

    /// Pinned `areTypesComparable`, including directional short-circuiting.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn are_types_comparable(
        &mut self,
        left: TypeId,
        right: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        if self.is_type_comparable_to(left, right)? {
            return Ok(true);
        }
        self.is_type_comparable_to(right, left)
    }

    /// Pinned `isTypeRelatedTo` through its exact simple and cache-read paths.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    ) -> Result<bool, RelationUnavailable> {
        let bootstrap = self.relation_bootstrap_facts()?;
        let source = self.regular_type_if_fresh(source)?;
        let target = self.regular_type_if_fresh(target)?;
        if source == target {
            return Ok(true);
        }

        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
        if !relation.is_identity() {
            if (relation == RelationKind::Comparable
                && !target_flags.intersects(TypeFlags::NEVER)
                && self.is_simple_type_related_to(target, source, relation, bootstrap)?)
                || self.is_simple_type_related_to(source, target, relation, bootstrap)?
            {
                return Ok(true);
            }
        } else if !(source_flags | target_flags).intersects(
            TypeFlags::UNION_OR_INTERSECTION
                | TypeFlags::INDEXED_ACCESS
                | TypeFlags::CONDITIONAL
                | TypeFlags::SUBSTITUTION,
        ) {
            if source_flags != target_flags {
                return Ok(false);
            }
            if source_flags.intersects(TypeFlags::SINGLETON) {
                return Ok(true);
            }
        }

        if source_flags.intersects(TypeFlags::OBJECT) && target_flags.intersects(TypeFlags::OBJECT)
        {
            let key = self
                .relation_key_if_available(
                    source,
                    target,
                    IntersectionState::NONE,
                    relation.is_identity(),
                    false,
                )
                .map_err(relation_key_unavailable)?;
            let related = self.relation_cache_get(relation, key.key());
            if !related.is_empty() {
                return Ok(related.intersects(RelationComparisonResult::SUCCEEDED));
            }
        }

        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation,
            });
        }
        Ok(false)
    }

    #[allow(clippy::too_many_lines)] // Keep the pinned branch order visibly linear.
    fn is_simple_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
    ) -> Result<bool, RelationUnavailable> {
        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
        if target_flags.intersects(TypeFlags::ANY)
            || source_flags.intersects(TypeFlags::NEVER)
            || source == bootstrap.wildcard_type
        {
            return Ok(true);
        }
        if target_flags.intersects(TypeFlags::UNKNOWN)
            && !(relation == RelationKind::StrictSubtype && source_flags.intersects(TypeFlags::ANY))
        {
            return Ok(true);
        }
        if target_flags.intersects(TypeFlags::NEVER) {
            return Ok(false);
        }
        if source_flags.intersects(TypeFlags::STRING_LIKE)
            && target_flags.intersects(TypeFlags::STRING)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::STRING_LITERAL)
            && source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::STRING_LITERAL)
            && !target_flags.intersects(TypeFlags::ENUM_LITERAL)
            && self.literal_values_equal(source, target)?
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NUMBER_LIKE)
            && target_flags.intersects(TypeFlags::NUMBER)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NUMBER_LITERAL)
            && source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::NUMBER_LITERAL)
            && !target_flags.intersects(TypeFlags::ENUM_LITERAL)
            && self.literal_values_equal(source, target)?
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::BIG_INT_LIKE)
            && target_flags.intersects(TypeFlags::BIG_INT)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::BOOLEAN_LIKE)
            && target_flags.intersects(TypeFlags::BOOLEAN)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::ES_SYMBOL_LIKE)
            && target_flags.intersects(TypeFlags::ES_SYMBOL)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::ENUM) && target_flags.intersects(TypeFlags::ENUM) {
            let source_symbol = self.enum_symbol(source)?;
            let target_symbol = self.enum_symbol(target)?;
            let names_equal =
                self.symbol_name(source_symbol)? == self.symbol_name(target_symbol)?;
            if names_equal && self.enum_types_related_if_available(source_symbol, target_symbol)? {
                return Ok(true);
            }
        }
        if source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::ENUM_LITERAL)
        {
            if source_flags.intersects(TypeFlags::UNION)
                && target_flags.intersects(TypeFlags::UNION)
            {
                let source_symbol = self.enum_symbol(source)?;
                let target_symbol = self.enum_symbol(target)?;
                if self.enum_types_related_if_available(source_symbol, target_symbol)? {
                    return Ok(true);
                }
            }
            if source_flags.intersects(TypeFlags::LITERAL)
                && target_flags.intersects(TypeFlags::LITERAL)
                && self.literal_values_equal(source, target)?
            {
                let source_symbol = self.enum_symbol(source)?;
                let target_symbol = self.enum_symbol(target)?;
                if self.enum_types_related_if_available(source_symbol, target_symbol)? {
                    return Ok(true);
                }
            }
        }
        if source_flags.intersects(TypeFlags::UNDEFINED)
            && ((!bootstrap.strict_null_checks
                && !target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION))
                || target_flags.intersects(TypeFlags::UNDEFINED | TypeFlags::VOID))
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NULL)
            && ((!bootstrap.strict_null_checks
                && !target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION))
                || target_flags.intersects(TypeFlags::NULL))
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::NON_PRIMITIVE)
        {
            let rejected_empty_strict_subtype = relation == RelationKind::StrictSubtype
                && self.is_empty_anonymous_object_type(source, bootstrap.any_function_type)?
                && !self
                    .type_payload(source)
                    .ok_or(RelationUnavailable::Type(source))?
                    .object_flags()
                    .intersects(ObjectFlags::FRESH_LITERAL);
            if !rejected_empty_strict_subtype {
                return Ok(true);
            }
        }
        if relation == RelationKind::Assignable || relation == RelationKind::Comparable {
            if source_flags.intersects(TypeFlags::ANY) {
                return Ok(true);
            }
            if source_flags.intersects(TypeFlags::NUMBER)
                && (target_flags.intersects(TypeFlags::ENUM)
                    || target_flags.intersects(TypeFlags::NUMBER_LITERAL)
                        && target_flags.intersects(TypeFlags::ENUM_LITERAL))
            {
                return Ok(true);
            }
            if source_flags.intersects(TypeFlags::NUMBER_LITERAL)
                && !source_flags.intersects(TypeFlags::ENUM_LITERAL)
                && (target_flags.intersects(TypeFlags::ENUM)
                    || target_flags.intersects(TypeFlags::NUMBER_LITERAL)
                        && target_flags.intersects(TypeFlags::ENUM_LITERAL)
                        && self.literal_values_equal(source, target)?)
            {
                return Ok(true);
            }
            if self.is_unknown_like_union_type(target, bootstrap)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn relation_bootstrap_facts(&self) -> Result<RelationBootstrapFacts, RelationUnavailable> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        Ok(RelationBootstrapFacts {
            strict_null_checks: bootstrap.options.strict_null_checks,
            wildcard_type: bootstrap.wildcard_type,
            any_function_type: bootstrap.any_function_type,
        })
    }

    fn type_flags(&self, type_id: TypeId) -> Result<TypeFlags, RelationUnavailable> {
        self.type_payload(type_id)
            .map(TypeRecord::flags)
            .ok_or(RelationUnavailable::Type(type_id))
    }

    fn regular_type_if_fresh(&self, type_id: TypeId) -> Result<TypeId, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !record.flags().intersects(TypeFlags::FRESHABLE) {
            return Ok(type_id);
        }
        let TypeData::Literal(literal) = record.data() else {
            return Err(RelationUnavailable::MalformedLiteral(type_id));
        };
        if literal.fresh_type != Some(type_id) {
            return Ok(type_id);
        }
        self.type_payload(literal.regular_type)
            .map(|_| literal.regular_type)
            .ok_or(RelationUnavailable::Type(literal.regular_type))
    }

    fn literal_values_equal(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let source = self
            .type_payload(source)
            .ok_or(RelationUnavailable::Type(source))?;
        let target = self
            .type_payload(target)
            .ok_or(RelationUnavailable::Type(target))?;
        let TypeData::Literal(source) = source.data() else {
            return Err(RelationUnavailable::MalformedLiteral(source.id()));
        };
        let TypeData::Literal(target) = target.data() else {
            return Err(RelationUnavailable::MalformedLiteral(target.id()));
        };
        Ok(source.value == target.value)
    }

    fn enum_symbol(&self, type_id: TypeId) -> Result<SemanticSymbolId, RelationUnavailable> {
        self.type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?
            .symbol()
            .ok_or(RelationUnavailable::MalformedEnumType(type_id))
    }

    fn symbol_name(&self, symbol: SemanticSymbolId) -> Result<&[u8], RelationUnavailable> {
        self.symbol(symbol)
            .map(|symbol| symbol.name().as_bytes())
            .ok_or(RelationUnavailable::Symbol(symbol))
    }

    fn enum_types_related_if_available(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Result<bool, RelationUnavailable> {
        let source = self.enum_parent_or_self(source)?;
        let target = self.enum_parent_or_self(target)?;
        if source == target {
            return Ok(true);
        }
        let source_symbol = self
            .symbol(source)
            .ok_or(RelationUnavailable::Symbol(source))?;
        let target_symbol = self
            .symbol(target)
            .ok_or(RelationUnavailable::Symbol(target))?;
        if source_symbol.name() != target_symbol.name()
            || !source_symbol.flags().intersects(SymbolFlags::REGULAR_ENUM)
            || !target_symbol.flags().intersects(SymbolFlags::REGULAR_ENUM)
        {
            return Ok(false);
        }
        let cached = self
            .enum_relation_cache_get(source, target)
            .ok_or(RelationUnavailable::Symbol(source))?;
        if cached.is_empty() {
            return Err(RelationUnavailable::EnumRelation { source, target });
        }
        Ok(cached.intersects(RelationComparisonResult::SUCCEEDED))
    }

    fn enum_parent_or_self(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, RelationUnavailable> {
        let record = self
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        if record.flags().intersects(SymbolFlags::ENUM_MEMBER) {
            return self
                .get_parent_of_symbol(symbol)
                .ok_or(RelationUnavailable::Symbol(symbol));
        }
        Ok(symbol)
    }

    fn is_empty_anonymous_object_type(
        &self,
        type_id: TypeId,
        any_function_type: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !record.object_flags().intersects(ObjectFlags::ANONYMOUS) {
            return Ok(false);
        }
        if record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            let structured = record
                .data()
                .structured()
                .ok_or(RelationUnavailable::MalformedStructuredType(type_id))?;
            let is_empty_resolved = type_id != any_function_type
                && structured.properties.as_ref().is_none_or(Vec::is_empty)
                && structured.signatures.as_ref().is_none_or(Vec::is_empty)
                && structured.index_infos.as_ref().is_none_or(Vec::is_empty);
            if is_empty_resolved {
                return Ok(true);
            }
        }
        let Some(symbol) = record.symbol() else {
            return Ok(false);
        };
        let symbol_record = self
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        if !symbol_record.flags().intersects(SymbolFlags::TYPE_LITERAL) {
            return Ok(false);
        }
        if symbol_record
            .flags()
            .intersects(SymbolFlags::LATE_BINDING_CONTAINER)
        {
            let members = self
                .members_and_exports_links(symbol)
                .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
                .ok_or(RelationUnavailable::LateBoundMembers(symbol))?;
            return self
                .symbol_table(members)
                .map(ts_binder::semantic::SymbolTable::is_empty)
                .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol));
        }
        match symbol_record.members() {
            None => Ok(true),
            Some(members) => self
                .symbol_table(members)
                .map(ts_binder::semantic::SymbolTable::is_empty)
                .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol)),
        }
    }

    fn is_unknown_like_union_type(
        &mut self,
        type_id: TypeId,
        bootstrap: RelationBootstrapFacts,
    ) -> Result<bool, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !bootstrap.strict_null_checks || !record.flags().intersects(TypeFlags::UNION) {
            return Ok(false);
        }
        if record
            .object_flags()
            .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        {
            return Ok(record
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        }
        let TypeData::Union(union) = record.data() else {
            return Err(RelationUnavailable::MalformedStructuredType(type_id));
        };
        let types = union.union.types.clone();
        let is_unknown_like = if types.len() >= 3
            && self.type_flags(types[0])?.intersects(TypeFlags::UNDEFINED)
            && self.type_flags(types[1])?.intersects(TypeFlags::NULL)
        {
            let mut found_empty = false;
            for constituent in &types {
                if self.is_empty_anonymous_object_type(*constituent, bootstrap.any_function_type)? {
                    found_empty = true;
                    break;
                }
            }
            found_empty
        } else {
            false
        };
        let cache_flags = ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED
            | if is_unknown_like {
                ObjectFlags::IS_UNKNOWN_LIKE_UNION
            } else {
                ObjectFlags::NONE
            };
        if !self.add_type_object_flags(type_id, cache_flags) {
            return Err(RelationUnavailable::InvalidUnknownLikeUnionState(type_id));
        }
        Ok(is_unknown_like)
    }
}

const fn bool_to_ternary(value: bool) -> Ternary {
    if value { Ternary::True } else { Ternary::False }
}

const fn relation_key_unavailable(error: RelationKeyUnavailable) -> RelationUnavailable {
    match error {
        RelationKeyUnavailable::Type(type_id) => RelationUnavailable::RelationKeyType(type_id),
        RelationKeyUnavailable::TypeReferenceArguments(type_id) => {
            RelationUnavailable::RelationKeyTypeReferenceArguments(type_id)
        }
        RelationKeyUnavailable::TypeReferenceTarget(type_id) => {
            RelationUnavailable::RelationKeyTypeReferenceTarget(type_id)
        }
        RelationKeyUnavailable::TypeParameterConstraint(type_id) => {
            RelationUnavailable::RelationKeyTypeParameterConstraint(type_id)
        }
        RelationKeyUnavailable::CyclicGenericArguments(type_id) => {
            RelationUnavailable::RelationKeyCyclicGenericArguments(type_id)
        }
    }
}

#[cfg(test)]
mod tests {
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_jsnum::{Number, PseudoBigInt};

    use super::RelationUnavailable;
    use crate::semantic::{
        CanonicalTypeMapperStore, IntrinsicBootstrapOptions, MembersAndExportsLinks,
        MembersOrExportsResolutionKind, RelationComparisonResult, RelationKind, TypeId,
        signatures::Ternary,
        type_records::{LiteralValue, RegularLiteralLink, TypeData},
        types::{ObjectFlags, TypeFlags},
    };

    type TestStore = CanonicalTypeMapperStore;

    fn initialized(strict_null_checks: bool) -> TestStore {
        let mut store = TestStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn alloc_symbol(store: &mut TestStore, flags: SymbolFlags, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn alloc_literal(store: &mut TestStore, flags: TypeFlags, value: LiteralValue) -> TypeId {
        store
            .alloc_literal_type(flags, value, RegularLiteralLink::SelfType)
            .unwrap()
    }

    fn alloc_resolved_object(
        store: &mut TestStore,
        object_flags: ObjectFlags,
        properties: Option<Vec<SemanticSymbolId>>,
    ) -> TypeId {
        let object = store.alloc_plain_object_type(object_flags, None).unwrap();
        assert!(store.set_structured_type_members(object, None, properties, None, None, None));
        object
    }

    fn alloc_enum_type(store: &mut TestStore, symbol: SemanticSymbolId) -> TypeId {
        let enum_type = alloc_literal(store, TypeFlags::ENUM, LiteralValue::ComputedEnum);
        assert!(store.set_type_symbol(enum_type, Some(symbol)));
        enum_type
    }

    fn alloc_reference(store: &mut TestStore, target: TypeId, arguments: Vec<TypeId>) -> TypeId {
        let reference = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(reference, Some(target), None));
        assert!(store.set_type_reference_resolution(reference, None, Some(arguments)));
        reference
    }

    fn cache_resolved_members(
        store: &mut TestStore,
        symbol: SemanticSymbolId,
        members: ts_binder::SymbolTableId,
    ) {
        let mut links = MembersAndExportsLinks::default();
        links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] = Some(members);
        assert!(store.set_members_and_exports_links(symbol, links));
    }

    #[test]
    fn entrypoints_require_bootstrap_and_reject_foreign_types_atomically() {
        let mut uninitialized = TestStore::new();
        let string = uninitialized
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        assert_eq!(
            uninitialized.is_type_assignable_to(string, string),
            Err(RelationUnavailable::MissingBootstrap)
        );

        let mut store = initialized(true);
        let foreign = initialized(true);
        let local_string = store.intrinsic_bootstrap().unwrap().string_type;
        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(local_string, foreign_string),
            Err(RelationUnavailable::Type(foreign_string))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn fresh_literals_singletons_and_advanced_identity_follow_pinned_fast_path() {
        let mut store = initialized(true);
        let (regular_false, fresh_false, any, auto, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.regular_false_type,
                bootstrap.false_type,
                bootstrap.any_type,
                bootstrap.auto_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        assert_eq!(
            store.is_type_identical_to(fresh_false, regular_false),
            Ok(true)
        );
        assert_eq!(store.is_type_identical_to(any, auto), Ok(true));
        assert_eq!(store.is_type_identical_to(string, number), Ok(false));
        assert_eq!(store.compare_types_identical(any, auto), Ok(Ternary::True));

        let left = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        let right = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        assert_eq!(
            store.is_type_identical_to(left, right),
            Err(RelationUnavailable::StructuralRelation {
                source: left,
                target: right,
                relation: RelationKind::Identity,
            })
        );
    }

    #[test]
    fn top_bottom_wildcard_and_primitive_widening_matrix_is_exact_and_uncached() {
        let mut store = initialized(true);
        let (any, unknown, never, wildcard, string, number, bigint, boolean, es_symbol, true_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.never_type,
                bootstrap.wildcard_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.es_symbol_type,
                bootstrap.true_type,
            )
        };
        let string_literal = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("value".into()),
        );
        let number_literal = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let bigint_literal = alloc_literal(
            &mut store,
            TypeFlags::BIG_INT_LITERAL,
            LiteralValue::BigInt(PseudoBigInt::new("1", false)),
        );
        let unique_symbol = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "unique");
        let unique_symbol_type = store.alloc_unique_es_symbol_type(unique_symbol).unwrap();
        let before = store.relation_state_snapshot();

        assert_eq!(store.is_type_assignable_to(string, any), Ok(true));
        assert_eq!(store.is_type_subtype_of(never, number), Ok(true));
        assert_eq!(store.is_type_assignable_to(wildcard, never), Ok(true));
        assert_eq!(store.is_type_subtype_of(number, unknown), Ok(true));
        assert_eq!(store.is_type_strict_subtype_of(any, unknown), Ok(false));
        assert_eq!(store.is_type_subtype_of(any, unknown), Ok(true));
        assert_eq!(store.is_type_assignable_to(string, never), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(string_literal, string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(number_literal, number),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(bigint_literal, bigint),
            Ok(true)
        );
        assert_eq!(store.is_type_assignable_to(true_type, boolean), Ok(true));
        assert_eq!(
            store.is_type_assignable_to(unique_symbol_type, es_symbol),
            Ok(true)
        );
        assert_eq!(store.is_type_assignable_to(any, number), Ok(true));
        assert_eq!(store.is_type_comparable_to(any, number), Ok(true));
        assert_eq!(store.is_type_subtype_of(any, number), Ok(false));
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn enum_backed_literal_values_use_direct_equality_including_nan() {
        let mut store = initialized(true);
        let enum_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::String("x".into()),
        );
        let ordinary_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("x".into()),
        );
        let other_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("y".into()),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_string, ordinary_string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(enum_string, other_string),
            Ok(false)
        );

        let enum_number = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let ordinary_number = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_number, ordinary_number),
            Ok(true)
        );

        let enum_nan = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::nan()),
        );
        let ordinary_nan = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::nan()),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_nan, ordinary_nan),
            Ok(false),
            "Go's direct jsnum.Number equality keeps NaN unequal"
        );
    }

    #[test]
    fn strict_and_non_strict_nullability_preserve_union_exclusion() {
        let mut strict = initialized(true);
        let (undefined, null, void, string) = {
            let bootstrap = strict.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.void_type,
                bootstrap.string_type,
            )
        };
        assert_eq!(strict.is_type_assignable_to(undefined, void), Ok(true));
        assert_eq!(strict.is_type_assignable_to(undefined, string), Ok(false));
        assert_eq!(strict.is_type_assignable_to(null, string), Ok(false));

        let mut loose = initialized(false);
        let (undefined, null, string, number) = {
            let bootstrap = loose.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        assert_eq!(loose.is_type_assignable_to(undefined, string), Ok(true));
        assert_eq!(loose.is_type_assignable_to(null, number), Ok(true));
        let union = loose
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        assert_eq!(
            loose.is_type_assignable_to(undefined, union),
            Err(RelationUnavailable::StructuralRelation {
                source: undefined,
                target: union,
                relation: RelationKind::Assignable,
            })
        );
    }

    #[test]
    fn object_to_nonprimitive_preserves_empty_strict_subtype_exception() {
        let mut store = initialized(true);
        let (empty, any_function, non_primitive) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.empty_object_type,
                bootstrap.any_function_type,
                bootstrap.non_primitive_type,
            )
        };
        assert_eq!(store.is_type_assignable_to(empty, non_primitive), Ok(true));
        assert_eq!(
            store.is_type_strict_subtype_of(empty, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: empty,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );
        assert_eq!(
            store.is_type_strict_subtype_of(any_function, non_primitive),
            Ok(true)
        );

        let fresh_empty = alloc_resolved_object(
            &mut store,
            ObjectFlags::ANONYMOUS | ObjectFlags::FRESH_LITERAL,
            None,
        );
        assert_eq!(
            store.is_type_strict_subtype_of(fresh_empty, non_primitive),
            Ok(true)
        );
        let property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        let nonempty =
            alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, Some(vec![property]));
        assert_eq!(
            store.is_type_strict_subtype_of(nonempty, non_primitive),
            Ok(true)
        );
    }

    #[test]
    fn late_bound_type_literal_members_require_and_honor_the_resolved_members_cache() {
        let mut store = initialized(true);
        let non_primitive = store.intrinsic_bootstrap().unwrap().non_primitive_type;
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__type");
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::LateBoundMembers(symbol))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let members = store.alloc_symbol_table();
        cache_resolved_members(&mut store, symbol, members);
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: object,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );

        let property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("value"), property),
            Some(None)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Ok(true)
        );
    }

    #[test]
    fn resolved_nonempty_type_literal_falls_through_to_cached_symbol_members() {
        let mut store = initialized(true);
        let non_primitive = store.intrinsic_bootstrap().unwrap().non_primitive_type;
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__inconsistent");
        let structured_property =
            alloc_symbol(&mut store, SymbolFlags::PROPERTY, "structuredProperty");
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            None,
            Some(vec![structured_property]),
            None,
            None,
            None,
        ));
        let cached_members = store.alloc_symbol_table();
        cache_resolved_members(&mut store, symbol, cached_members);

        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: object,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );
    }

    #[test]
    fn comparability_checks_reverse_first_and_guards_reverse_never() {
        let mut store = initialized(true);
        let (any, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.any_type, bootstrap.never_type)
        };
        let enum_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::String("x".into()),
        );
        let ordinary_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("x".into()),
        );
        assert_eq!(
            store.is_type_comparable_to(ordinary_string, enum_string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_comparable_to(enum_string, ordinary_string),
            Ok(true)
        );
        assert_eq!(store.is_type_comparable_to(any, never), Ok(false));
        assert_eq!(store.are_types_comparable(any, never), Ok(true));
    }

    #[test]
    fn numeric_enum_carveouts_and_enum_capability_boundary_are_exact() {
        let mut store = initialized(true);
        let (number, number_literal) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.zero_type)
        };
        let enum_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let computed_enum = alloc_enum_type(&mut store, enum_symbol);
        assert_eq!(store.is_type_assignable_to(number, computed_enum), Ok(true));
        assert_eq!(store.is_type_subtype_of(number, computed_enum), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(number_literal, computed_enum),
            Ok(true)
        );

        let enum_zero = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(0.0)),
        );
        assert!(store.set_type_symbol(enum_zero, Some(enum_symbol)));
        assert_eq!(
            store.is_type_assignable_to(number_literal, enum_zero),
            Ok(true)
        );

        let same_enum_other_type = alloc_enum_type(&mut store, enum_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, same_enum_other_type),
            Ok(true)
        );
        let same_name_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let same_name_enum = alloc_enum_type(&mut store, same_name_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, same_name_enum),
            Err(RelationUnavailable::EnumRelation {
                source: enum_symbol,
                target: same_name_symbol,
            })
        );
        let other_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "Other");
        let other_enum = alloc_enum_type(&mut store, other_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, other_enum),
            Ok(false)
        );
    }

    #[test]
    fn enum_relation_cache_answers_success_failure_and_miss_directionally() {
        let mut store = initialized(true);
        let source_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let target_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let miss_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let source = alloc_enum_type(&mut store, source_symbol);
        let target = alloc_enum_type(&mut store, target_symbol);
        let miss = alloc_enum_type(&mut store, miss_symbol);

        assert!(store.enum_relation_cache_set(
            source_symbol,
            target_symbol,
            RelationComparisonResult::SUCCEEDED,
        ));
        assert!(store.enum_relation_cache_set(
            target_symbol,
            source_symbol,
            RelationComparisonResult::FAILED,
        ));
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(store.is_type_assignable_to(target, source), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(source, miss),
            Err(RelationUnavailable::EnumRelation {
                source: source_symbol,
                target: miss_symbol,
            })
        );
        assert_eq!(store.enum_relation_cache_size(), 2);
    }

    #[test]
    fn enum_member_symbols_canonicalize_to_their_shared_parent() {
        let mut store = initialized(true);
        let enum_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let left_member = alloc_symbol(&mut store, SymbolFlags::ENUM_MEMBER, "Left");
        let right_member = alloc_symbol(&mut store, SymbolFlags::ENUM_MEMBER, "Right");
        assert!(store.set_symbol_relationships(left_member, None, None, Some(enum_symbol), None,));
        assert!(store.set_symbol_relationships(right_member, None, None, Some(enum_symbol), None,));
        let left = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let right = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        assert!(store.set_type_symbol(left, Some(left_member)));
        assert!(store.set_type_symbol(right, Some(right_member)));
        assert_eq!(store.is_type_assignable_to(left, right), Ok(true));
    }

    #[test]
    fn unknown_like_union_is_memoized_without_populating_relation_caches() {
        let mut store = initialized(true);
        let (string, unknown_union, undefined, null, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.unknown_union_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.number_type,
            )
        };
        let before_relations = store.relation_state_snapshot();
        assert!(
            !store
                .type_payload(unknown_union)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        );
        assert_eq!(store.is_type_assignable_to(string, unknown_union), Ok(true));
        let flags = store.type_payload(unknown_union).unwrap().object_flags();
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED));
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        assert_eq!(store.is_type_assignable_to(number, unknown_union), Ok(true));
        assert_eq!(store.relation_state_snapshot(), before_relations);

        let ordinary_union = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, null, string, number])
            .unwrap();
        assert_eq!(
            store.is_type_assignable_to(string, ordinary_union),
            Err(RelationUnavailable::StructuralRelation {
                source: string,
                target: ordinary_union,
                relation: RelationKind::Assignable,
            })
        );
        let flags = store.type_payload(ordinary_union).unwrap().object_flags();
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED));
        assert!(!flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        assert_eq!(store.relation_state_snapshot(), before_relations);
    }

    #[test]
    fn unavailable_unknown_like_scan_does_not_publish_a_false_cache() {
        let mut store = initialized(true);
        let (string, undefined, null) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
            )
        };
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__late");
        let unresolved = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, null, unresolved])
            .unwrap();
        assert_eq!(
            store.is_type_assignable_to(string, union),
            Err(RelationUnavailable::LateBoundMembers(symbol))
        );
        assert!(
            !store
                .type_payload(union)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        );
    }

    #[test]
    fn object_cache_reads_are_directional_isolated_and_never_filled_on_miss() {
        let mut store = initialized(true);
        let source = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let target = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        store.relation_cache_set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        store.relation_cache_set(RelationKind::Subtype, key, RelationComparisonResult::FAILED);
        store.relation_cache_set(
            RelationKind::StrictSubtype,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        let identity_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, true, false)
            .unwrap()
            .key();
        store.relation_cache_set(
            RelationKind::Identity,
            identity_key,
            RelationComparisonResult::FAILED,
        );
        let before = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(store.is_type_subtype_of(source, target), Ok(false));
        assert_eq!(store.is_type_strict_subtype_of(source, target), Ok(true));
        assert_eq!(store.is_type_identical_to(source, target), Ok(false));
        assert_eq!(
            store.is_type_comparable_to(source, target),
            Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: RelationKind::Comparable,
            })
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn generic_object_key_gap_is_propagated_instead_of_becoming_a_cache_miss() {
        let mut store = initialized(true);
        let base = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = alloc_reference(&mut store, base, vec![parameter]);
        let target = alloc_reference(&mut store, base, vec![parameter]);
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::RelationKeyTypeParameterConstraint(
                parameter
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn wrappers_return_only_true_or_false_ternary_values() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert_eq!(
            store.compare_types_assignable_simple(string, string),
            Ok(Ternary::True)
        );
        assert_eq!(
            store.compare_types_assignable_worker(string, number, true),
            Ok(Ternary::False)
        );
        assert_eq!(
            store.compare_types_subtype_of(string, number),
            Ok(Ternary::False)
        );
    }

    #[test]
    fn unknown_like_cache_bits_remain_union_payload_state() {
        let mut store = initialized(true);
        let unknown_union = store.intrinsic_bootstrap().unwrap().unknown_union_type;
        let TypeData::Union(_) = store.type_payload(unknown_union).unwrap().data() else {
            panic!("strict bootstrap unknown union must retain its union payload");
        };
        assert!(store.add_type_object_flags(
            unknown_union,
            ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED | ObjectFlags::IS_UNKNOWN_LIKE_UNION,
        ));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(store.is_type_assignable_to(string, unknown_union), Ok(true));
    }
}
