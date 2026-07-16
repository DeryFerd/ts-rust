//! Canonical result types for `&&`, `||`, and `??`.
//!
//! This ports the dependency-closed portion of typescript-go
//! `checkBinaryLikeExpression`, `getTypeFacts`,
//! `removeDefinitelyFalsyTypes`, and `extractDefinitelyFalsyTypes`. Syntax
//! diagnostics and source-link publication remain source-dispatch concerns.

use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_jsnum::Number;

use super::{
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    enums::canonical_enum_type_owner,
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::TypeFlags,
    CanonicalGlobalTypes, CanonicalTypeMapperStore, TypeId,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LogicalBinaryRequest {
    pub(super) operator: SyntaxKind,
    pub(super) left_type: TypeId,
    pub(super) right_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LogicalBinaryResolution {
    pub(super) result_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LogicalBinaryUnsupported {
    Operator(SyntaxKind),
    Type(TypeId),
    #[cfg(not(test))]
    MissingGlobalTypes,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LogicalBinaryInvariant {
    MissingBootstrap,
    InvalidType(TypeId),
    CyclicUnion(TypeId),
    InvalidUnion(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LogicalBinaryError {
    Unsupported(LogicalBinaryUnsupported),
    Invariant(LogicalBinaryInvariant),
    Literal(LiteralTypeCacheError),
}

impl From<LogicalBinaryInvariant> for LogicalBinaryError {
    fn from(error: LogicalBinaryInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<LiteralTypeCacheError> for LogicalBinaryError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct LogicalTypeFacts {
    truthy: bool,
    falsy: bool,
    nullish: bool,
}

impl LogicalTypeFacts {
    fn include(&mut self, other: Self) {
        self.truthy |= other.truthy;
        self.falsy |= other.falsy;
        self.nullish |= other.nullish;
    }
}

/// Computes the pinned result after both operands have been checked.
pub(super) fn check_logical_binary(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    request: LogicalBinaryRequest,
) -> Result<LogicalBinaryResolution, LogicalBinaryError> {
    if store.type_payload(request.left_type).is_none() {
        return Err(LogicalBinaryInvariant::InvalidType(request.left_type).into());
    }
    if store.type_payload(request.right_type).is_none() {
        return Err(LogicalBinaryInvariant::InvalidType(request.right_type).into());
    }
    let strict_null_checks = store
        .intrinsic_bootstrap()
        .ok_or(LogicalBinaryInvariant::MissingBootstrap)?
        .options
        .strict_null_checks;
    let facts = logical_type_facts(store, request.left_type, strict_null_checks)?;
    let result_type = match request.operator {
        SyntaxKind::AmpersandAmpersandToken => {
            if facts.truthy {
                // This seemingly surprising non-strict branch is exact: the
                // pinned checker extracts the falsy part of the widened right
                // operand when strict null checks are disabled.
                let projected = if strict_null_checks {
                    extract_definitely_falsy_types(
                        store,
                        global_types,
                        request.left_type,
                        strict_null_checks,
                    )?
                } else {
                    let right_base =
                        base_type_of_literal_type(store, global_types, request.right_type)?;
                    extract_definitely_falsy_types(
                        store,
                        global_types,
                        right_base,
                        strict_null_checks,
                    )?
                };
                logical_union(
                    store,
                    global_types,
                    &[projected, request.right_type],
                    UnionReduction::Literal,
                )?
            } else {
                request.left_type
            }
        }
        SyntaxKind::BarBarToken => {
            if facts.falsy {
                let truthy = remove_definitely_falsy_types(
                    store,
                    global_types,
                    request.left_type,
                    strict_null_checks,
                )?;
                let non_nullable =
                    get_non_nullable_type(store, global_types, truthy, strict_null_checks)?;
                logical_union(
                    store,
                    global_types,
                    &[non_nullable, request.right_type],
                    UnionReduction::Subtype,
                )?
            } else {
                request.left_type
            }
        }
        SyntaxKind::QuestionQuestionToken => {
            if facts.nullish {
                let non_nullable = get_non_nullable_type(
                    store,
                    global_types,
                    request.left_type,
                    strict_null_checks,
                )?;
                logical_union(
                    store,
                    global_types,
                    &[non_nullable, request.right_type],
                    UnionReduction::Subtype,
                )?
            } else {
                request.left_type
            }
        }
        operator => {
            return Err(LogicalBinaryError::Unsupported(
                LogicalBinaryUnsupported::Operator(operator),
            ));
        }
    };
    Ok(LogicalBinaryResolution { result_type })
}

/// Narrows a matching identifier while the right operand is evaluated.
pub(super) fn narrow_logical_right_operand(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    operator: SyntaxKind,
    left_type: TypeId,
) -> Result<TypeId, LogicalBinaryError> {
    let strict_null_checks = store
        .intrinsic_bootstrap()
        .ok_or(LogicalBinaryInvariant::MissingBootstrap)?
        .options
        .strict_null_checks;
    match operator {
        SyntaxKind::AmpersandAmpersandToken => {
            let truthy =
                remove_definitely_falsy_types(store, global_types, left_type, strict_null_checks)?;
            get_non_nullable_type(store, global_types, truthy, strict_null_checks)
        }
        SyntaxKind::BarBarToken => filter_union_leaves(
            store,
            global_types,
            left_type,
            UnionReduction::Literal,
            |store, leaf| Ok(logical_type_facts(store, leaf, strict_null_checks)?.falsy),
        ),
        SyntaxKind::QuestionQuestionToken => {
            narrow_nullish_right(store, global_types, left_type, strict_null_checks)
        }
        operator => Err(LogicalBinaryError::Unsupported(
            LogicalBinaryUnsupported::Operator(operator),
        )),
    }
}

fn logical_type_facts(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    strict_null_checks: bool,
) -> Result<LogicalTypeFacts, LogicalBinaryError> {
    logical_type_facts_worker(store, type_, strict_null_checks, &mut HashSet::new())
}

fn logical_type_facts_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    strict_null_checks: bool,
    visiting: &mut HashSet<TypeId>,
) -> Result<LogicalTypeFacts, LogicalBinaryError> {
    let record = store
        .type_payload(type_)
        .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
    if record.flags().intersects(TypeFlags::UNION) {
        if !visiting.insert(type_) {
            return Err(LogicalBinaryInvariant::CyclicUnion(type_).into());
        }
        let TypeData::Union(union) = record.data() else {
            return Err(LogicalBinaryInvariant::InvalidUnion(type_).into());
        };
        let mut facts = LogicalTypeFacts::default();
        for constituent in &union.union.types {
            facts.include(logical_type_facts_worker(
                store,
                *constituent,
                strict_null_checks,
                visiting,
            )?);
        }
        assert!(visiting.remove(&type_));
        return Ok(facts);
    }

    let flags = record.flags();
    let mut facts = if flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
        LogicalTypeFacts {
            truthy: true,
            falsy: true,
            nullish: true,
        }
    } else if flags.intersects(TypeFlags::NEVER) {
        LogicalTypeFacts::default()
    } else if flags.intersects(TypeFlags::VOID_LIKE | TypeFlags::NULL) {
        LogicalTypeFacts {
            truthy: false,
            falsy: true,
            nullish: true,
        }
    } else if flags.intersects(TypeFlags::STRING_LITERAL) {
        let LiteralValue::String(value) = literal_value(record, type_)? else {
            return Err(LogicalBinaryInvariant::InvalidType(type_).into());
        };
        LogicalTypeFacts {
            truthy: !value.is_empty(),
            falsy: value.is_empty(),
            nullish: false,
        }
    } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        let LiteralValue::Number(value) = literal_value(record, type_)? else {
            return Err(LogicalBinaryInvariant::InvalidType(type_).into());
        };
        LogicalTypeFacts {
            truthy: *value != Number::new(0.0),
            falsy: *value == Number::new(0.0),
            nullish: false,
        }
    } else if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        let LiteralValue::BigInt(value) = literal_value(record, type_)? else {
            return Err(LogicalBinaryInvariant::InvalidType(type_).into());
        };
        LogicalTypeFacts {
            truthy: value.sign() != 0,
            falsy: value.sign() == 0,
            nullish: false,
        }
    } else if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        let LiteralValue::Boolean(value) = literal_value(record, type_)? else {
            return Err(LogicalBinaryInvariant::InvalidType(type_).into());
        };
        LogicalTypeFacts {
            truthy: *value,
            falsy: !*value,
            nullish: false,
        }
    } else if flags.intersects(
        TypeFlags::STRING
            | TypeFlags::NUMBER
            | TypeFlags::BIG_INT
            | TypeFlags::BOOLEAN
            | TypeFlags::ENUM,
    ) {
        LogicalTypeFacts {
            truthy: true,
            falsy: true,
            nullish: false,
        }
    } else if flags
        .intersects(TypeFlags::OBJECT | TypeFlags::NON_PRIMITIVE | TypeFlags::ES_SYMBOL_LIKE)
    {
        LogicalTypeFacts {
            truthy: true,
            falsy: false,
            nullish: false,
        }
    } else {
        return Err(LogicalBinaryError::Unsupported(
            LogicalBinaryUnsupported::Type(type_),
        ));
    };
    // In the non-strict facts table null and undefined are assignable to every
    // non-never family, so each such family also contributes falsy/nullish.
    if !strict_null_checks && !flags.intersects(TypeFlags::NEVER) {
        facts.falsy = true;
        facts.nullish = true;
    }
    Ok(facts)
}

fn literal_value(record: &TypeRecord, type_: TypeId) -> Result<&LiteralValue, LogicalBinaryError> {
    let TypeData::Literal(literal) = record.data() else {
        return Err(LogicalBinaryInvariant::InvalidType(type_).into());
    };
    Ok(&literal.value)
}

fn extract_definitely_falsy_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    strict_null_checks: bool,
) -> Result<TypeId, LogicalBinaryError> {
    let (flags, union_types) = {
        let record = store
            .type_payload(type_)
            .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
        (
            record.flags(),
            match record.data() {
                TypeData::Union(union) => Some(union.union.types.clone()),
                _ => None,
            },
        )
    };
    if let Some(constituents) = union_types {
        let mut projected = Vec::with_capacity(constituents.len());
        for constituent in constituents {
            projected.push(extract_definitely_falsy_types(
                store,
                global_types,
                constituent,
                strict_null_checks,
            )?);
        }
        return logical_union(store, global_types, &projected, UnionReduction::Literal);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(LogicalBinaryInvariant::MissingBootstrap)?;
    if flags.intersects(TypeFlags::STRING) {
        return Ok(bootstrap.empty_string_type);
    }
    if flags.intersects(TypeFlags::NUMBER) {
        return Ok(bootstrap.zero_type);
    }
    if flags.intersects(TypeFlags::BIG_INT) {
        return Ok(bootstrap.zero_bigint_type);
    }
    if flags.intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::VOID_LIKE | TypeFlags::NULL) {
        return Ok(type_);
    }
    let never = bootstrap.never_type;
    let facts = logical_type_facts(store, type_, strict_null_checks)?;
    Ok(if facts.falsy && !facts.truthy {
        type_
    } else {
        never
    })
}

fn remove_definitely_falsy_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    strict_null_checks: bool,
) -> Result<TypeId, LogicalBinaryError> {
    filter_union_leaves(
        store,
        global_types,
        type_,
        UnionReduction::Literal,
        |store, leaf| Ok(logical_type_facts(store, leaf, strict_null_checks)?.truthy),
    )
}

fn get_non_nullable_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    strict_null_checks: bool,
) -> Result<TypeId, LogicalBinaryError> {
    if !strict_null_checks {
        return Ok(type_);
    }
    let (flags, unknown_empty_object) = {
        let record = store
            .type_payload(type_)
            .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LogicalBinaryInvariant::MissingBootstrap)?;
        (record.flags(), bootstrap.unknown_empty_object_type)
    };
    if flags.intersects(TypeFlags::UNKNOWN) {
        return Ok(unknown_empty_object);
    }
    filter_union_leaves(
        store,
        global_types,
        type_,
        UnionReduction::Literal,
        |store, leaf| {
            let flags = store
                .type_payload(leaf)
                .map(TypeRecord::flags)
                .ok_or(LogicalBinaryInvariant::InvalidType(leaf))?;
            Ok(flags.intersects(TypeFlags::ANY)
                || !flags.intersects(TypeFlags::VOID_LIKE | TypeFlags::NULL | TypeFlags::UNKNOWN))
        },
    )
}

fn narrow_nullish_right(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    strict_null_checks: bool,
) -> Result<TypeId, LogicalBinaryError> {
    if strict_null_checks {
        let flags = store
            .type_payload(type_)
            .map(TypeRecord::flags)
            .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
        if flags.intersects(TypeFlags::UNKNOWN) {
            let (undefined, null) = {
                let bootstrap = store
                    .intrinsic_bootstrap()
                    .ok_or(LogicalBinaryInvariant::MissingBootstrap)?;
                (bootstrap.undefined_type, bootstrap.null_type)
            };
            return logical_union(
                store,
                global_types,
                &[undefined, null],
                UnionReduction::Literal,
            );
        }
    }
    filter_union_leaves(
        store,
        global_types,
        type_,
        UnionReduction::Literal,
        |store, leaf| Ok(logical_type_facts(store, leaf, strict_null_checks)?.nullish),
    )
}

fn filter_union_leaves(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
    reduction: UnionReduction,
    mut include: impl FnMut(&CanonicalTypeMapperStore, TypeId) -> Result<bool, LogicalBinaryError>,
) -> Result<TypeId, LogicalBinaryError> {
    let leaves = union_leaves(store, type_)?;
    let mut retained = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        if include(store, leaf)? {
            retained.push(leaf);
        }
    }
    logical_union(store, global_types, &retained, reduction)
}

fn union_leaves(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Vec<TypeId>, LogicalBinaryError> {
    let mut leaves = Vec::new();
    collect_union_leaves(store, type_, &mut leaves, &mut HashSet::new())?;
    Ok(leaves)
}

fn collect_union_leaves(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    leaves: &mut Vec<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), LogicalBinaryError> {
    let record = store
        .type_payload(type_)
        .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
    if record.flags().intersects(TypeFlags::UNION) {
        if !visiting.insert(type_) {
            return Err(LogicalBinaryInvariant::CyclicUnion(type_).into());
        }
        let TypeData::Union(union) = record.data() else {
            return Err(LogicalBinaryInvariant::InvalidUnion(type_).into());
        };
        for constituent in &union.union.types {
            collect_union_leaves(store, *constituent, leaves, visiting)?;
        }
        assert!(visiting.remove(&type_));
    } else {
        leaves.push(type_);
    }
    Ok(())
}

fn base_type_of_literal_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Result<TypeId, LogicalBinaryError> {
    let (flags, union_types) = {
        let record = store
            .type_payload(type_)
            .ok_or(LogicalBinaryInvariant::InvalidType(type_))?;
        (
            record.flags(),
            match record.data() {
                TypeData::Union(union) => Some(union.union.types.clone()),
                _ => None,
            },
        )
    };
    if flags.intersects(TypeFlags::ENUM_LIKE) {
        let owner = canonical_enum_type_owner(store, type_).ok_or(
            LogicalBinaryError::Unsupported(LogicalBinaryUnsupported::Type(type_)),
        )?;
        let declared = store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .ok_or(LogicalBinaryError::Unsupported(
                LogicalBinaryUnsupported::Type(type_),
            ))?;
        if store.type_payload(declared).is_none() {
            return Err(LogicalBinaryInvariant::InvalidType(declared).into());
        }
        return Ok(declared);
    }
    if let Some(constituents) = union_types {
        let mut bases = Vec::with_capacity(constituents.len());
        for constituent in constituents {
            bases.push(base_type_of_literal_type(store, global_types, constituent)?);
        }
        return logical_union(store, global_types, &bases, UnionReduction::Literal);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(LogicalBinaryInvariant::MissingBootstrap)?;
    if flags.intersects(TypeFlags::STRING_LITERAL) {
        Ok(bootstrap.string_type)
    } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
        Ok(bootstrap.number_type)
    } else if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
        Ok(bootstrap.bigint_type)
    } else if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
        Ok(bootstrap.boolean_type)
    } else {
        Ok(type_)
    }
}

fn logical_union(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    types: &[TypeId],
    reduction: UnionReduction,
) -> Result<TypeId, LogicalBinaryError> {
    if let Some(global_types) = global_types {
        return store
            .expression_union_type_with_global_types(global_types, types, reduction)
            .map_err(Into::into);
    }
    #[cfg(test)]
    {
        store
            .expression_union_type(types, reduction)
            .map_err(Into::into)
    }
    #[cfg(not(test))]
    {
        let _ = (store, types, reduction);
        Err(LogicalBinaryError::Unsupported(
            LogicalBinaryUnsupported::MissingGlobalTypes,
        ))
    }
}

#[cfg(test)]
mod tests {
    use ts_jsnum::PseudoBigInt;

    use super::*;
    use crate::semantic::{
        mapper::TypeMapper, type_records::TypeRecord, IntrinsicBootstrapOptions, SemanticStore,
    };

    fn initialized_store(strict_null_checks: bool) -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                ..IntrinsicBootstrapOptions::default()
            })
            .unwrap();
        store
    }

    fn request(
        operator: SyntaxKind,
        left_type: TypeId,
        right_type: TypeId,
    ) -> LogicalBinaryRequest {
        LogicalBinaryRequest {
            operator,
            left_type,
            right_type,
        }
    }

    fn union_types(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<TypeId> {
        match store.type_payload(type_).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => vec![type_],
        }
    }

    #[test]
    fn strict_and_extracts_only_the_pinned_falsy_projection() {
        let mut store = initialized_store(true);
        let (string, number, empty, false_type, true_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.empty_string_type,
                bootstrap.regular_false_type,
                bootstrap.regular_true_type,
            )
        };
        let result = check_logical_binary(
            &mut store,
            None,
            request(SyntaxKind::AmpersandAmpersandToken, string, number),
        )
        .unwrap()
        .result_type;
        assert_eq!(union_types(&store, result), vec![number, empty]);
        assert_eq!(
            check_logical_binary(
                &mut store,
                None,
                request(SyntaxKind::AmpersandAmpersandToken, false_type, number,),
            )
            .unwrap()
            .result_type,
            false_type,
        );
        assert_eq!(
            check_logical_binary(
                &mut store,
                None,
                request(SyntaxKind::AmpersandAmpersandToken, true_type, number),
            )
            .unwrap()
            .result_type,
            number,
        );
    }

    #[test]
    fn strict_or_removes_only_definitely_falsy_and_nullable_constituents() {
        let mut store = initialized_store(true);
        let empty = store.regular_string_literal_type(String::new()).unwrap();
        let present = store
            .regular_string_literal_type("present".to_owned())
            .unwrap();
        let (null, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.null_type, bootstrap.number_type)
        };
        let left = store
            .literal_union_type(&[empty, present, null], None)
            .unwrap();
        let result = check_logical_binary(
            &mut store,
            None,
            request(SyntaxKind::BarBarToken, left, number),
        )
        .unwrap()
        .result_type;
        assert_eq!(union_types(&store, result), vec![number, present]);

        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let primitive = check_logical_binary(
            &mut store,
            None,
            request(SyntaxKind::BarBarToken, string, number),
        )
        .unwrap()
        .result_type;
        assert_eq!(union_types(&store, primitive), vec![string, number]);
    }

    #[test]
    fn strict_nullish_coalescing_removes_null_and_undefined_only_when_present() {
        let mut store = initialized_store(true);
        let (string, number, null, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.null_type,
                bootstrap.undefined_type,
            )
        };
        let left = store
            .literal_union_type(&[string, null, undefined], None)
            .unwrap();
        let result = check_logical_binary(
            &mut store,
            None,
            request(SyntaxKind::QuestionQuestionToken, left, number),
        )
        .unwrap()
        .result_type;
        assert_eq!(union_types(&store, result), vec![string, number]);
        assert_eq!(
            check_logical_binary(
                &mut store,
                None,
                request(SyntaxKind::QuestionQuestionToken, string, number),
            )
            .unwrap()
            .result_type,
            string,
        );
    }

    #[test]
    fn non_strict_and_uses_the_right_base_literal_falsy_projection() {
        let mut store = initialized_store(false);
        let right = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("2n"))
            .unwrap();
        let (left, zero) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.zero_bigint_type)
        };
        let result = check_logical_binary(
            &mut store,
            None,
            request(SyntaxKind::AmpersandAmpersandToken, left, right),
        )
        .unwrap()
        .result_type;
        assert_eq!(union_types(&store, result), vec![zero, right]);
    }

    #[test]
    fn warm_results_reuse_identity_and_foreign_types_fail_closed() {
        let mut store = initialized_store(true);
        let foreign = initialized_store(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let input = request(SyntaxKind::BarBarToken, string, number);
        let first = check_logical_binary(&mut store, None, input)
            .unwrap()
            .result_type;
        let second = check_logical_binary(&mut store, None, input)
            .unwrap()
            .result_type;
        assert_eq!(first, second);

        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            check_logical_binary(
                &mut store,
                None,
                request(SyntaxKind::BarBarToken, foreign_string, number),
            ),
            Err(LogicalBinaryError::Invariant(
                LogicalBinaryInvariant::InvalidType(foreign_string),
            )),
        );
        assert_eq!(
            check_logical_binary(
                &mut store,
                None,
                request(SyntaxKind::PlusToken, string, number),
            ),
            Err(LogicalBinaryError::Unsupported(
                LogicalBinaryUnsupported::Operator(SyntaxKind::PlusToken),
            )),
        );
    }
}
