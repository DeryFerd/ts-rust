//! Exact scalar kernel for ordinary non-assignment binary operators.
//!
//! The admitted domain is deliberately atomic: the canonical `string`,
//! `number`, `bigint`, and `boolean` types plus their validated literal pairs.
//! Every broader type family remains a typed boundary. The kernel mirrors the
//! pinned checker's operator-specific diagnostics and recovery types without
//! publishing expression links; source integration owns publication after the
//! complete result and diagnostic batch have been staged.

use ts_ast::{NodeRef, SyntaxKind};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalTypeMapperStore, RelationUnavailable,
    TypeDisplayUnavailable, TypeId,
    bootstrap::LiteralTypeCacheError,
    formatter::type_to_string,
    type_records::{LiteralValue, TypeData},
    types::TypeFlags,
};

/// Target capability needed only by `bigint ** bigint`.
#[allow(dead_code)] // Known targets are retained for the future compiler-option handoff.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimitiveBigIntExponentiationTarget {
    KnownAtLeastEs2016,
    KnownBeforeEs2016,
    Unknown,
}

/// Unforgeable-at-source provenance for a result recovered by this kernel.
///
/// The source executor retains this tag only on a completed primitive binary
/// result and validates it against the exact bootstrap identity on reuse.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimitiveBinaryRecovery {
    Any,
    Error,
}

/// Syntax-neutral input after both operands have been checked left-to-right.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PrimitiveBinaryRequest {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) operator: SyntaxKind,
    pub(super) right: NodeRef,
    pub(super) left_type: TypeId,
    pub(super) right_type: TypeId,
    pub(super) left_recovery: Option<PrimitiveBinaryRecovery>,
    pub(super) right_recovery: Option<PrimitiveBinaryRecovery>,
    pub(super) bigint_exponentiation_target: PrimitiveBigIntExponentiationTarget,
}

/// One complete operator result. Diagnostics retain raw checker issuance order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PrimitiveBinaryResolution {
    pub(super) result_type: TypeId,
    pub(super) recovery: Option<PrimitiveBinaryRecovery>,
    pub(super) diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

/// Valid TypeScript behavior outside the atomic scalar kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimitiveBinaryUnsupported {
    Operator(SyntaxKind),
    Operand { node: NodeRef, type_: TypeId },
    BigIntExponentiationTarget(NodeRef),
}

/// Malformed or foreign canonical state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PrimitiveBinaryInvariant {
    MissingBootstrap,
    InvalidType(TypeId),
    InvalidRecovery {
        type_: TypeId,
        recovery: PrimitiveBinaryRecovery,
    },
    MissingDiagnostic(u32),
}

/// Capability, store, relation, or display failure without a guessed result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PrimitiveBinaryError {
    Unsupported(PrimitiveBinaryUnsupported),
    Invariant(PrimitiveBinaryInvariant),
    Literal(LiteralTypeCacheError),
    Relation(RelationUnavailable),
    Display(TypeDisplayUnavailable),
}

impl From<PrimitiveBinaryUnsupported> for PrimitiveBinaryError {
    fn from(error: PrimitiveBinaryUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<PrimitiveBinaryInvariant> for PrimitiveBinaryError {
    fn from(error: PrimitiveBinaryInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<LiteralTypeCacheError> for PrimitiveBinaryError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

impl From<RelationUnavailable> for PrimitiveBinaryError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<TypeDisplayUnavailable> for PrimitiveBinaryError {
    fn from(error: TypeDisplayUnavailable) -> Self {
        Self::Display(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveScalarFamily {
    String,
    Number,
    BigInt,
    Boolean,
}

impl PrimitiveScalarFamily {
    const fn is_numeric(self) -> bool {
        matches!(self, Self::Number | Self::BigInt)
    }

    const fn is_bigint(self) -> bool {
        matches!(self, Self::BigInt)
    }

    const fn is_plus_close_enough(self) -> bool {
        !matches!(self, Self::Boolean)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PrimitiveScalar {
    type_: TypeId,
    base: TypeId,
    family: PrimitiveScalarFamily,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveBinaryOperand {
    Scalar(PrimitiveScalar),
    Recovery(PrimitiveBinaryRecovery),
    Nullish(PrimitiveNullishFamily),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveNullishFamily {
    Null,
    Undefined,
}

impl PrimitiveBinaryOperand {
    const fn scalar(self) -> Option<PrimitiveScalar> {
        match self {
            Self::Scalar(scalar) => Some(scalar),
            Self::Recovery(_) | Self::Nullish(_) => None,
        }
    }

    const fn recovery(self) -> Option<PrimitiveBinaryRecovery> {
        match self {
            Self::Scalar(_) | Self::Nullish(_) => None,
            Self::Recovery(recovery) => Some(recovery),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PrimitiveBinaryValue {
    type_: TypeId,
    recovery: Option<PrimitiveBinaryRecovery>,
}

impl PrimitiveBinaryValue {
    const fn plain(type_: TypeId) -> Self {
        Self {
            type_,
            recovery: None,
        }
    }

    const fn recovered(type_: TypeId, recovery: PrimitiveBinaryRecovery) -> Self {
        Self {
            type_,
            recovery: Some(recovery),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrimitiveBinaryOperator {
    Plus,
    Arithmetic(SyntaxKind),
    Relational(SyntaxKind),
    Equality(SyntaxKind),
}

impl PrimitiveBinaryOperator {
    fn from_syntax(kind: SyntaxKind) -> Result<Self, PrimitiveBinaryUnsupported> {
        Ok(match kind {
            SyntaxKind::PlusToken => Self::Plus,
            SyntaxKind::MinusToken
            | SyntaxKind::AsteriskToken
            | SyntaxKind::SlashToken
            | SyntaxKind::PercentToken
            | SyntaxKind::AsteriskAsteriskToken
            | SyntaxKind::BarToken
            | SyntaxKind::AmpersandToken
            | SyntaxKind::CaretToken
            | SyntaxKind::LessThanLessThanToken
            | SyntaxKind::GreaterThanGreaterThanToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanToken => Self::Arithmetic(kind),
            SyntaxKind::LessThanToken
            | SyntaxKind::LessThanEqualsToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::GreaterThanEqualsToken => Self::Relational(kind),
            SyntaxKind::EqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken
            | SyntaxKind::EqualsEqualsEqualsToken
            | SyntaxKind::ExclamationEqualsEqualsToken => Self::Equality(kind),
            _ => return Err(PrimitiveBinaryUnsupported::Operator(kind)),
        })
    }

    const fn syntax(self) -> SyntaxKind {
        match self {
            Self::Plus => SyntaxKind::PlusToken,
            Self::Arithmetic(kind) | Self::Relational(kind) | Self::Equality(kind) => kind,
        }
    }

    fn text(self) -> &'static str {
        match self.syntax() {
            SyntaxKind::PlusToken => "+",
            SyntaxKind::MinusToken => "-",
            SyntaxKind::AsteriskToken => "*",
            SyntaxKind::SlashToken => "/",
            SyntaxKind::PercentToken => "%",
            SyntaxKind::AsteriskAsteriskToken => "**",
            SyntaxKind::BarToken => "|",
            SyntaxKind::AmpersandToken => "&",
            SyntaxKind::CaretToken => "^",
            SyntaxKind::LessThanLessThanToken => "<<",
            SyntaxKind::GreaterThanGreaterThanToken => ">>",
            SyntaxKind::GreaterThanGreaterThanGreaterThanToken => ">>>",
            SyntaxKind::LessThanToken => "<",
            SyntaxKind::LessThanEqualsToken => "<=",
            SyntaxKind::GreaterThanToken => ">",
            SyntaxKind::GreaterThanEqualsToken => ">=",
            SyntaxKind::EqualsEqualsToken => "==",
            SyntaxKind::ExclamationEqualsToken => "!=",
            SyntaxKind::EqualsEqualsEqualsToken => "===",
            SyntaxKind::ExclamationEqualsEqualsToken => "!==",
            _ => unreachable!("a primitive binary operator has canonical text"),
        }
    }
}

/// Checks one already-typed scalar operation without publishing source state.
pub(super) fn check_primitive_binary(
    store: &mut CanonicalTypeMapperStore,
    request: PrimitiveBinaryRequest,
) -> Result<PrimitiveBinaryResolution, PrimitiveBinaryError> {
    let operator = PrimitiveBinaryOperator::from_syntax(request.operator)?;
    let mut left = primitive_binary_operand(
        store,
        request.left,
        request.left_type,
        request.left_recovery,
    )?;
    let mut right = primitive_binary_operand(
        store,
        request.right,
        request.right_type,
        request.right_recovery,
    )?;
    let mut diagnostics = Vec::new();

    let string_plus = operator == PrimitiveBinaryOperator::Plus
        && (left
            .scalar()
            .is_some_and(|scalar| scalar.family == PrimitiveScalarFamily::String)
            || right
                .scalar()
                .is_some_and(|scalar| scalar.family == PrimitiveScalarFamily::String));
    if !matches!(operator, PrimitiveBinaryOperator::Equality(_)) && !string_plus {
        left = check_non_null_operand(request.left, left, &mut diagnostics)?;
        right = check_non_null_operand(request.right, right, &mut diagnostics)?;
    }
    let result = match operator {
        PrimitiveBinaryOperator::Plus => check_plus(store, request, left, right, &mut diagnostics)?,
        PrimitiveBinaryOperator::Arithmetic(kind) => {
            check_arithmetic(store, request, kind, left, right, &mut diagnostics)?
        }
        PrimitiveBinaryOperator::Relational(_) => {
            check_relational(store, request, operator, left, right, &mut diagnostics)?
        }
        PrimitiveBinaryOperator::Equality(_) => {
            check_equality(store, request, operator, left, right, &mut diagnostics)?
        }
    };

    Ok(PrimitiveBinaryResolution {
        result_type: result.type_,
        recovery: result.recovery,
        diagnostics,
    })
}

fn primitive_binary_operand(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
    recovery: Option<PrimitiveBinaryRecovery>,
) -> Result<PrimitiveBinaryOperand, PrimitiveBinaryError> {
    let Some(recovery) = recovery else {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
        let nullish = if type_ == bootstrap.null_type || type_ == bootstrap.null_widening_type {
            Some(PrimitiveNullishFamily::Null)
        } else if type_ == bootstrap.undefined_type || type_ == bootstrap.undefined_widening_type {
            Some(PrimitiveNullishFamily::Undefined)
        } else {
            None
        };
        if let Some(nullish) = nullish {
            store.validate_union_constituent(type_)?;
            return Ok(PrimitiveBinaryOperand::Nullish(nullish));
        }
        return primitive_scalar(store, node, type_).map(PrimitiveBinaryOperand::Scalar);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    let expected = match recovery {
        PrimitiveBinaryRecovery::Any => bootstrap.any_type,
        PrimitiveBinaryRecovery::Error => bootstrap.error_type,
    };
    if type_ != expected {
        return Err(PrimitiveBinaryInvariant::InvalidRecovery { type_, recovery }.into());
    }
    Ok(PrimitiveBinaryOperand::Recovery(recovery))
}

fn check_non_null_operand(
    node: NodeRef,
    operand: PrimitiveBinaryOperand,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<PrimitiveBinaryOperand, PrimitiveBinaryError> {
    let PrimitiveBinaryOperand::Nullish(kind) = operand else {
        return Ok(operand);
    };
    let value = match kind {
        PrimitiveNullishFamily::Null => "null",
        PrimitiveNullishFamily::Undefined => "undefined",
    };
    let message =
        message_by_code(18_050).ok_or(PrimitiveBinaryInvariant::MissingDiagnostic(18_050))?;
    diagnostics.push(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(message, [value.to_owned()]),
        related_information: Vec::new(),
    });
    Ok(PrimitiveBinaryOperand::Recovery(
        PrimitiveBinaryRecovery::Error,
    ))
}

fn primitive_scalar(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> Result<PrimitiveScalar, PrimitiveBinaryError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    let bases = [
        (bootstrap.string_type, PrimitiveScalarFamily::String),
        (bootstrap.number_type, PrimitiveScalarFamily::Number),
        (bootstrap.bigint_type, PrimitiveScalarFamily::BigInt),
        (bootstrap.boolean_type, PrimitiveScalarFamily::Boolean),
    ];
    if let Some((base, family)) = bases.into_iter().find(|(candidate, _)| *candidate == type_) {
        store.validate_union_constituent(type_)?;
        return Ok(PrimitiveScalar {
            type_,
            base,
            family,
        });
    }

    let record = store
        .type_payload(type_)
        .ok_or(PrimitiveBinaryInvariant::InvalidType(type_))?;
    let TypeData::Literal(literal) = record.data() else {
        return Err(PrimitiveBinaryUnsupported::Operand { node, type_ }.into());
    };
    let family = match (record.flags(), &literal.value) {
        (TypeFlags::STRING_LITERAL, LiteralValue::String(_)) => PrimitiveScalarFamily::String,
        (TypeFlags::NUMBER_LITERAL, LiteralValue::Number(_)) => PrimitiveScalarFamily::Number,
        (TypeFlags::BIG_INT_LITERAL, LiteralValue::BigInt(_)) => PrimitiveScalarFamily::BigInt,
        (TypeFlags::BOOLEAN_LITERAL, LiteralValue::Boolean(_)) => PrimitiveScalarFamily::Boolean,
        _ => return Err(PrimitiveBinaryUnsupported::Operand { node, type_ }.into()),
    };
    store.validate_union_constituent(type_)?;
    let base = match family {
        PrimitiveScalarFamily::String => bootstrap.string_type,
        PrimitiveScalarFamily::Number => bootstrap.number_type,
        PrimitiveScalarFamily::BigInt => bootstrap.bigint_type,
        PrimitiveScalarFamily::Boolean => bootstrap.boolean_type,
    };
    Ok(PrimitiveScalar {
        type_,
        base,
        family,
    })
}

fn check_plus(
    store: &mut CanonicalTypeMapperStore,
    request: PrimitiveBinaryRequest,
    left: PrimitiveBinaryOperand,
    right: PrimitiveBinaryOperand,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<PrimitiveBinaryValue, PrimitiveBinaryError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    if left
        .scalar()
        .is_some_and(|scalar| scalar.family == PrimitiveScalarFamily::String)
        || right
            .scalar()
            .is_some_and(|scalar| scalar.family == PrimitiveScalarFamily::String)
    {
        return Ok(PrimitiveBinaryValue::plain(bootstrap.string_type));
    }
    if let Some(recovery) = combined_recovery(left, right) {
        let type_ = match recovery {
            PrimitiveBinaryRecovery::Any => bootstrap.any_type,
            PrimitiveBinaryRecovery::Error => bootstrap.error_type,
        };
        return Ok(PrimitiveBinaryValue::recovered(type_, recovery));
    }

    let left = left
        .scalar()
        .expect("an operand without recovery is a scalar");
    let right = right
        .scalar()
        .expect("an operand without recovery is a scalar");
    let result = if left.family == PrimitiveScalarFamily::Number
        && right.family == PrimitiveScalarFamily::Number
    {
        PrimitiveBinaryValue::plain(bootstrap.number_type)
    } else if left.family == PrimitiveScalarFamily::BigInt
        && right.family == PrimitiveScalarFamily::BigInt
    {
        PrimitiveBinaryValue::plain(bootstrap.bigint_type)
    } else {
        let (display_left, display_right) =
            if left.family.is_plus_close_enough() && right.family.is_plus_close_enough() {
                (left.type_, right.type_)
            } else {
                (left.base, right.base)
            };
        diagnostics.push(operator_diagnostic(
            store,
            request.expression,
            PrimitiveBinaryOperator::Plus,
            display_left,
            display_right,
        )?);
        PrimitiveBinaryValue::recovered(bootstrap.any_type, PrimitiveBinaryRecovery::Any)
    };
    Ok(result)
}

const fn combined_recovery(
    left: PrimitiveBinaryOperand,
    right: PrimitiveBinaryOperand,
) -> Option<PrimitiveBinaryRecovery> {
    match (left.recovery(), right.recovery()) {
        (Some(PrimitiveBinaryRecovery::Error), _) | (_, Some(PrimitiveBinaryRecovery::Error)) => {
            Some(PrimitiveBinaryRecovery::Error)
        }
        (Some(PrimitiveBinaryRecovery::Any), _) | (_, Some(PrimitiveBinaryRecovery::Any)) => {
            Some(PrimitiveBinaryRecovery::Any)
        }
        (None, None) => None,
    }
}

fn check_arithmetic(
    store: &mut CanonicalTypeMapperStore,
    request: PrimitiveBinaryRequest,
    kind: SyntaxKind,
    left: PrimitiveBinaryOperand,
    right: PrimitiveBinaryOperand,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<PrimitiveBinaryValue, PrimitiveBinaryError> {
    if left
        .scalar()
        .is_some_and(|scalar| !scalar.family.is_numeric())
    {
        diagnostics.push(fixed_diagnostic(request.left, 2362)?);
    }
    if right
        .scalar()
        .is_some_and(|scalar| !scalar.family.is_numeric())
    {
        diagnostics.push(fixed_diagnostic(request.right, 2363)?);
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    let left_bigint = left
        .scalar()
        .is_some_and(|scalar| scalar.family.is_bigint());
    let right_bigint = right
        .scalar()
        .is_some_and(|scalar| scalar.family.is_bigint());
    if left.recovery().is_some() && right.recovery().is_some() || !left_bigint && !right_bigint {
        return Ok(PrimitiveBinaryValue::plain(bootstrap.number_type));
    }
    if (left_bigint || left.recovery().is_some()) && (right_bigint || right.recovery().is_some()) {
        if kind == SyntaxKind::GreaterThanGreaterThanGreaterThanToken {
            let left = left
                .scalar()
                .map_or(bootstrap.error_type, |scalar| scalar.type_);
            let right = right
                .scalar()
                .map_or(bootstrap.error_type, |scalar| scalar.type_);
            diagnostics.push(operator_diagnostic(
                store,
                request.expression,
                PrimitiveBinaryOperator::Arithmetic(kind),
                left,
                right,
            )?);
        }
        check_bigint_exponentiation_target(request, kind, diagnostics)?;
        return Ok(PrimitiveBinaryValue::plain(bootstrap.bigint_type));
    }

    let left = left
        .scalar()
        .expect("mixed bigint failure has two scalar operands");
    let right = right
        .scalar()
        .expect("mixed bigint failure has two scalar operands");
    diagnostics.push(operator_diagnostic(
        store,
        request.expression,
        PrimitiveBinaryOperator::Arithmetic(kind),
        left.base,
        right.base,
    )?);
    Ok(PrimitiveBinaryValue::recovered(
        bootstrap.error_type,
        PrimitiveBinaryRecovery::Error,
    ))
}

fn check_bigint_exponentiation_target(
    request: PrimitiveBinaryRequest,
    kind: SyntaxKind,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<(), PrimitiveBinaryError> {
    if kind != SyntaxKind::AsteriskAsteriskToken {
        return Ok(());
    }
    match request.bigint_exponentiation_target {
        PrimitiveBigIntExponentiationTarget::KnownAtLeastEs2016 => Ok(()),
        PrimitiveBigIntExponentiationTarget::KnownBeforeEs2016 => {
            diagnostics.push(fixed_diagnostic(request.expression, 2791)?);
            Ok(())
        }
        PrimitiveBigIntExponentiationTarget::Unknown => {
            Err(PrimitiveBinaryUnsupported::BigIntExponentiationTarget(request.expression).into())
        }
    }
}

fn check_relational(
    store: &mut CanonicalTypeMapperStore,
    request: PrimitiveBinaryRequest,
    operator: PrimitiveBinaryOperator,
    left: PrimitiveBinaryOperand,
    right: PrimitiveBinaryOperand,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<PrimitiveBinaryValue, PrimitiveBinaryError> {
    let boolean = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.boolean_type)
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    if left.recovery().is_some() || right.recovery().is_some() {
        return Ok(PrimitiveBinaryValue::plain(boolean));
    }
    let left = left
        .scalar()
        .expect("an operand without recovery is a scalar");
    let right = right
        .scalar()
        .expect("an operand without recovery is a scalar");
    let left_numeric = left.family.is_numeric();
    let right_numeric = right.family.is_numeric();
    let compatible = left_numeric && right_numeric
        || !left_numeric && !right_numeric && store.are_types_comparable(left.base, right.base)?;
    if !compatible {
        diagnostics.push(operator_diagnostic(
            store,
            request.expression,
            operator,
            left.base,
            right.base,
        )?);
    }
    Ok(PrimitiveBinaryValue::plain(boolean))
}

fn check_equality(
    store: &mut CanonicalTypeMapperStore,
    request: PrimitiveBinaryRequest,
    _operator: PrimitiveBinaryOperator,
    left: PrimitiveBinaryOperand,
    right: PrimitiveBinaryOperand,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<PrimitiveBinaryValue, PrimitiveBinaryError> {
    let boolean = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.boolean_type)
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    if left.recovery().is_some()
        || right.recovery().is_some()
        || matches!(left, PrimitiveBinaryOperand::Nullish(_))
        || matches!(right, PrimitiveBinaryOperand::Nullish(_))
    {
        return Ok(PrimitiveBinaryValue::plain(boolean));
    }
    let left = left
        .scalar()
        .expect("an operand without recovery is a scalar");
    let right = right
        .scalar()
        .expect("an operand without recovery is a scalar");
    // Pinned `isTypeEqualityComparableTo` adds only a nullable-target escape.
    // Both operands have already been proven non-null atomic scalars, so its
    // two directional calls are exactly ordinary `areTypesComparable` here.
    if !store.are_types_comparable(left.type_, right.type_)? {
        let (display_left, display_right) = if store.are_types_comparable(left.base, right.base)? {
            (left.type_, right.type_)
        } else {
            (left.base, right.base)
        };
        diagnostics.push(comparison_diagnostic(
            store,
            request.expression,
            display_left,
            display_right,
        )?);
    }
    Ok(PrimitiveBinaryValue::plain(boolean))
}

fn fixed_diagnostic(
    node: NodeRef,
    code: u32,
) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
    let message = message_by_code(code).ok_or(PrimitiveBinaryInvariant::MissingDiagnostic(code))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::new(message),
        related_information: Vec::new(),
    })
}

fn operator_diagnostic(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    operator: PrimitiveBinaryOperator,
    left: TypeId,
    right: TypeId,
) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
    let message = message_by_code(2365).ok_or(PrimitiveBinaryInvariant::MissingDiagnostic(2365))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(
            message,
            [
                operator.text().to_owned(),
                type_to_string(store, left)?,
                type_to_string(store, right)?,
            ],
        ),
        related_information: Vec::new(),
    })
}

fn comparison_diagnostic(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    left: TypeId,
    right: TypeId,
) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
    let message = message_by_code(2367).ok_or(PrimitiveBinaryInvariant::MissingDiagnostic(2367))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(
            message,
            [type_to_string(store, left)?, type_to_string(store, right)?],
        ),
        related_information: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, mapper::TypeMapper, type_records::TypeRecord,
    };

    #[derive(Clone, Copy)]
    struct BinaryNodes {
        expression: NodeRef,
        left: NodeRef,
        right: NodeRef,
    }

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn binary_nodes(parsed: &ParseResult) -> BinaryNodes {
        let file = FileId::new(1);
        let (expression, binary) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                Some((node, binary))
            })
            .expect("fixture must contain a binary expression");
        BinaryNodes {
            expression: NodeRef::new(parsed.arena.id(), file, expression),
            left: NodeRef::new(parsed.arena.id(), file, binary.left),
            right: NodeRef::new(parsed.arena.id(), file, binary.right),
        }
    }

    fn request(
        nodes: BinaryNodes,
        operator: SyntaxKind,
        left_type: TypeId,
        right_type: TypeId,
    ) -> PrimitiveBinaryRequest {
        PrimitiveBinaryRequest {
            expression: nodes.expression,
            left: nodes.left,
            operator,
            right: nodes.right,
            left_type,
            right_type,
            left_recovery: None,
            right_recovery: None,
            bigint_exponentiation_target: PrimitiveBigIntExponentiationTarget::KnownAtLeastEs2016,
        }
    }

    fn rendered(resolution: &PrimitiveBinaryResolution) -> Vec<(NodeRef, u32, String)> {
        resolution
            .diagnostics
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.node.unwrap(),
                    diagnostic.diagnostic.code(),
                    diagnostic.diagnostic.render().unwrap(),
                )
            })
            .collect()
    }

    #[test]
    fn every_operator_token_has_the_pinned_scalar_success_result() {
        let parsed = parse_source_file("const value = left + right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (string, number, bigint, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
            )
        };

        for (operator, left, right, expected) in [
            (SyntaxKind::PlusToken, number, number, number),
            (SyntaxKind::PlusToken, bigint, bigint, bigint),
            (SyntaxKind::PlusToken, string, boolean, string),
            (SyntaxKind::MinusToken, number, number, number),
            (SyntaxKind::AsteriskToken, bigint, bigint, bigint),
            (SyntaxKind::SlashToken, number, number, number),
            (SyntaxKind::PercentToken, bigint, bigint, bigint),
            (SyntaxKind::AsteriskAsteriskToken, number, number, number),
            (SyntaxKind::AsteriskAsteriskToken, bigint, bigint, bigint),
            (SyntaxKind::BarToken, number, number, number),
            (SyntaxKind::AmpersandToken, bigint, bigint, bigint),
            (SyntaxKind::CaretToken, number, number, number),
            (SyntaxKind::LessThanLessThanToken, number, number, number),
            (
                SyntaxKind::GreaterThanGreaterThanToken,
                bigint,
                bigint,
                bigint,
            ),
            (
                SyntaxKind::GreaterThanGreaterThanGreaterThanToken,
                number,
                number,
                number,
            ),
            (SyntaxKind::LessThanToken, number, bigint, boolean),
            (SyntaxKind::LessThanEqualsToken, string, string, boolean),
            (SyntaxKind::GreaterThanToken, boolean, boolean, boolean),
            (SyntaxKind::GreaterThanEqualsToken, bigint, number, boolean),
            (SyntaxKind::EqualsEqualsToken, number, number, boolean),
            (SyntaxKind::ExclamationEqualsToken, bigint, bigint, boolean),
            (SyntaxKind::EqualsEqualsEqualsToken, string, string, boolean),
            (
                SyntaxKind::ExclamationEqualsEqualsToken,
                boolean,
                boolean,
                boolean,
            ),
        ] {
            let resolution =
                check_primitive_binary(&mut store, request(nodes, operator, left, right)).unwrap();
            assert_eq!(resolution.result_type, expected, "operator {operator:?}");
            assert!(resolution.diagnostics.is_empty(), "operator {operator:?}");
        }
    }

    #[test]
    fn arithmetic_preserves_operand_issuance_recovery_and_mixed_bigint_error() {
        let parsed = parse_source_file("const value = left - right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (string, number, bigint, boolean, error) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.error_type,
            )
        };

        let invalid = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::MinusToken, string, boolean),
        )
        .unwrap();
        assert_eq!(invalid.result_type, number);
        assert_eq!(invalid.recovery, None);
        assert_eq!(
            rendered(&invalid),
            [
                (
                    nodes.left,
                    2362,
                    "The left-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.".to_owned(),
                ),
                (
                    nodes.right,
                    2363,
                    "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.".to_owned(),
                ),
            ]
        );

        let mixed = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::AsteriskToken, string, bigint),
        )
        .unwrap();
        assert_eq!(mixed.result_type, error);
        assert_eq!(mixed.recovery, Some(PrimitiveBinaryRecovery::Error));
        assert_eq!(
            rendered(&mixed),
            [
                (
                    nodes.left,
                    2362,
                    "The left-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.".to_owned(),
                ),
                (
                    nodes.expression,
                    2365,
                    "Operator '*' cannot be applied to types 'string' and 'bigint'.".to_owned(),
                ),
            ]
        );
    }

    #[test]
    fn nullish_bitwise_operands_report_ts18050_and_recover_to_number() {
        let parsed = parse_source_file("const value = left | right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (number, null, undefined, null_widening, undefined_widening) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.null_type,
                bootstrap.undefined_type,
                bootstrap.null_widening_type,
                bootstrap.undefined_widening_type,
            )
        };

        for (left, right, expected) in [
            (
                number,
                null_widening,
                vec![(nodes.right, "The value 'null' cannot be used here.")],
            ),
            (
                number,
                undefined_widening,
                vec![(nodes.right, "The value 'undefined' cannot be used here.")],
            ),
            (
                undefined,
                undefined_widening,
                vec![
                    (nodes.left, "The value 'undefined' cannot be used here."),
                    (nodes.right, "The value 'undefined' cannot be used here."),
                ],
            ),
            (
                null,
                null_widening,
                vec![
                    (nodes.left, "The value 'null' cannot be used here."),
                    (nodes.right, "The value 'null' cannot be used here."),
                ],
            ),
        ] {
            let resolution = check_primitive_binary(
                &mut store,
                request(nodes, SyntaxKind::BarToken, left, right),
            )
            .unwrap();
            assert_eq!(resolution.result_type, number);
            assert_eq!(resolution.recovery, None);
            assert_eq!(
                rendered(&resolution),
                expected
                    .into_iter()
                    .map(|(node, message)| (node, 18_050, message.to_owned()))
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn string_concatenation_accepts_nullish_operands_without_null_diagnostics() {
        let parsed = parse_source_file("const value = left + right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (string, null, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.null_widening_type,
                bootstrap.undefined_widening_type,
            )
        };

        for (left, right) in [(string, null), (undefined, string)] {
            let resolution = check_primitive_binary(
                &mut store,
                request(nodes, SyntaxKind::PlusToken, left, right),
            )
            .unwrap();
            assert_eq!(resolution.result_type, string);
            assert!(resolution.diagnostics.is_empty());
        }
    }

    #[test]
    fn nullish_equality_is_valid_for_every_comparison_operator() {
        let parsed = parse_source_file("const value = left === right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (boolean, number, string, null, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.boolean_type,
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.null_widening_type,
                bootstrap.undefined_widening_type,
            )
        };

        for operator in [
            SyntaxKind::EqualsEqualsToken,
            SyntaxKind::ExclamationEqualsToken,
            SyntaxKind::EqualsEqualsEqualsToken,
            SyntaxKind::ExclamationEqualsEqualsToken,
        ] {
            for (left, right) in [
                (null, null),
                (null, undefined),
                (undefined, null),
                (undefined, undefined),
                (number, null),
                (null, number),
                (string, undefined),
                (undefined, string),
            ] {
                let resolution =
                    check_primitive_binary(&mut store, request(nodes, operator, left, right))
                        .unwrap();
                assert_eq!(resolution.result_type, boolean);
                assert_eq!(resolution.recovery, None);
                assert!(resolution.diagnostics.is_empty());
            }
        }
    }

    #[test]
    fn unsigned_bigint_shift_reports_ts2365_and_retains_bigint_result() {
        let parsed = parse_source_file("const value = left >>> right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let bigint = store.intrinsic_bootstrap().unwrap().bigint_type;

        let resolution = check_primitive_binary(
            &mut store,
            request(
                nodes,
                SyntaxKind::GreaterThanGreaterThanGreaterThanToken,
                bigint,
                bigint,
            ),
        )
        .unwrap();

        assert_eq!(resolution.result_type, bigint);
        assert_eq!(resolution.recovery, None);
        assert_eq!(
            rendered(&resolution),
            [(
                nodes.expression,
                2365,
                "Operator '>>>' cannot be applied to types 'bigint' and 'bigint'.".to_owned(),
            )]
        );

        let one = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("1n"))
            .unwrap();
        let two = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("2n"))
            .unwrap();
        let literal = check_primitive_binary(
            &mut store,
            request(
                nodes,
                SyntaxKind::GreaterThanGreaterThanGreaterThanToken,
                one,
                two,
            ),
        )
        .unwrap();
        assert_eq!(literal.result_type, bigint);
        assert_eq!(
            rendered(&literal),
            [(
                nodes.expression,
                2365,
                "Operator '>>>' cannot be applied to types '1n' and '2n'.".to_owned(),
            )]
        );
    }

    #[test]
    fn plus_keeps_close_literal_names_but_widens_boolean_failures() {
        let parsed = parse_source_file("const value = left + right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two_big = store
            .regular_bigint_literal_type(PseudoBigInt::parse_valid("2n"))
            .unwrap();
        let fresh_one = store.fresh_type_of_literal_type(one).unwrap();
        let fresh_two_big = store.fresh_type_of_literal_type(two_big).unwrap();
        let (number, bigint, boolean, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.any_type,
            )
        };

        let close = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::PlusToken, one, two_big),
        )
        .unwrap();
        assert_eq!(close.result_type, any);
        assert_eq!(close.recovery, Some(PrimitiveBinaryRecovery::Any));
        assert_eq!(
            rendered(&close),
            [(
                nodes.expression,
                2365,
                "Operator '+' cannot be applied to types '1' and '2n'.".to_owned(),
            )]
        );

        let mixed_left_literal = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::PlusToken, fresh_one, bigint),
        )
        .unwrap();
        assert_eq!(mixed_left_literal.result_type, any);
        assert_eq!(
            rendered(&mixed_left_literal),
            [(
                nodes.expression,
                2365,
                "Operator '+' cannot be applied to types '1' and 'bigint'.".to_owned(),
            )]
        );

        let mixed_right_literal = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::PlusToken, number, fresh_two_big),
        )
        .unwrap();
        assert_eq!(mixed_right_literal.result_type, any);
        assert_eq!(
            rendered(&mixed_right_literal),
            [(
                nodes.expression,
                2365,
                "Operator '+' cannot be applied to types 'number' and '2n'.".to_owned(),
            )]
        );

        let boolean_failure = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::PlusToken, one, boolean),
        )
        .unwrap();
        assert_eq!(boolean_failure.result_type, any);
        assert_eq!(
            rendered(&boolean_failure),
            [(
                nodes.expression,
                2365,
                "Operator '+' cannot be applied to types 'number' and 'boolean'.".to_owned(),
            )]
        );
    }

    #[test]
    fn relational_and_equality_use_distinct_compatibility_and_display_rules() {
        let parsed = parse_source_file("const value = left < right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two = store.regular_number_literal_type(Number::new(2.0)).unwrap();
        let fresh_one = store.fresh_type_of_literal_type(one).unwrap();
        let fresh_two = store.fresh_type_of_literal_type(two).unwrap();
        let a = store.regular_string_literal_type("a".to_owned()).unwrap();
        let boolean = store.intrinsic_bootstrap().unwrap().boolean_type;

        let relational = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::LessThanToken, one, boolean),
        )
        .unwrap();
        assert_eq!(relational.result_type, boolean);
        assert_eq!(
            rendered(&relational),
            [(
                nodes.expression,
                2365,
                "Operator '<' cannot be applied to types 'number' and 'boolean'.".to_owned(),
            )]
        );

        let same_family = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::EqualsEqualsEqualsToken, one, two),
        )
        .unwrap();
        assert_eq!(same_family.result_type, boolean);
        assert_eq!(
            rendered(&same_family),
            [(
                nodes.expression,
                2367,
                "This comparison appears to be unintentional because the types '1' and '2' have no overlap.".to_owned(),
            )]
        );

        let fresh_same_family = check_primitive_binary(
            &mut store,
            request(
                nodes,
                SyntaxKind::ExclamationEqualsEqualsToken,
                fresh_one,
                fresh_two,
            ),
        )
        .unwrap();
        assert_eq!(fresh_same_family.result_type, boolean);
        assert_eq!(rendered(&fresh_same_family), rendered(&same_family));

        let cross_family = check_primitive_binary(
            &mut store,
            request(nodes, SyntaxKind::ExclamationEqualsToken, one, a),
        )
        .unwrap();
        assert_eq!(cross_family.result_type, boolean);
        assert_eq!(
            rendered(&cross_family),
            [(
                nodes.expression,
                2367,
                "This comparison appears to be unintentional because the types 'number' and 'string' have no overlap.".to_owned(),
            )]
        );
    }

    #[test]
    fn kernel_recoveries_propagate_only_through_explicit_validated_capabilities() {
        let parsed = parse_source_file("const value = left + right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let (string, number, bigint, boolean, any, error) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.any_type,
                bootstrap.error_type,
            )
        };

        for (recovery, type_) in [
            (PrimitiveBinaryRecovery::Any, any),
            (PrimitiveBinaryRecovery::Error, error),
        ] {
            let mut plus = request(nodes, SyntaxKind::PlusToken, type_, number);
            plus.left_recovery = Some(recovery);
            let plus = check_primitive_binary(&mut store, plus).unwrap();
            assert_eq!(plus.result_type, type_);
            assert_eq!(plus.recovery, Some(recovery));
            assert!(plus.diagnostics.is_empty());

            let mut string_wins = request(nodes, SyntaxKind::PlusToken, type_, string);
            string_wins.left_recovery = Some(recovery);
            let string_wins = check_primitive_binary(&mut store, string_wins).unwrap();
            assert_eq!(string_wins.result_type, string);
            assert_eq!(string_wins.recovery, None);
            assert!(string_wins.diagnostics.is_empty());

            let mut invalid_peer = request(nodes, SyntaxKind::MinusToken, type_, string);
            invalid_peer.left_recovery = Some(recovery);
            let invalid_peer = check_primitive_binary(&mut store, invalid_peer).unwrap();
            assert_eq!(invalid_peer.result_type, number);
            assert_eq!(invalid_peer.recovery, None);
            assert_eq!(
                rendered(&invalid_peer),
                [(
                    nodes.right,
                    2363,
                    "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.".to_owned(),
                )]
            );

            let mut bigint_peer = request(nodes, SyntaxKind::AsteriskToken, type_, bigint);
            bigint_peer.left_recovery = Some(recovery);
            let bigint_peer = check_primitive_binary(&mut store, bigint_peer).unwrap();
            assert_eq!(bigint_peer.result_type, bigint);
            assert_eq!(bigint_peer.recovery, None);
            assert!(bigint_peer.diagnostics.is_empty());

            for operator in [
                SyntaxKind::LessThanToken,
                SyntaxKind::EqualsEqualsEqualsToken,
            ] {
                let mut comparison = request(nodes, operator, type_, boolean);
                comparison.left_recovery = Some(recovery);
                let comparison = check_primitive_binary(&mut store, comparison).unwrap();
                assert_eq!(comparison.result_type, boolean);
                assert_eq!(comparison.recovery, None);
                assert!(comparison.diagnostics.is_empty());
            }
        }

        let mut two_recoveries = request(nodes, SyntaxKind::SlashToken, any, error);
        two_recoveries.left_recovery = Some(PrimitiveBinaryRecovery::Any);
        two_recoveries.right_recovery = Some(PrimitiveBinaryRecovery::Error);
        let two_recoveries = check_primitive_binary(&mut store, two_recoveries).unwrap();
        assert_eq!(two_recoveries.result_type, number);
        assert_eq!(two_recoveries.recovery, None);
        assert!(two_recoveries.diagnostics.is_empty());

        let mut forged = request(nodes, SyntaxKind::PlusToken, number, boolean);
        forged.left_recovery = Some(PrimitiveBinaryRecovery::Any);
        assert_eq!(
            check_primitive_binary(&mut store, forged),
            Err(PrimitiveBinaryError::Invariant(
                PrimitiveBinaryInvariant::InvalidRecovery {
                    type_: number,
                    recovery: PrimitiveBinaryRecovery::Any,
                },
            )),
        );
        for unsupported in [any, error] {
            assert_eq!(
                check_primitive_binary(
                    &mut store,
                    request(nodes, SyntaxKind::PlusToken, unsupported, boolean),
                ),
                Err(PrimitiveBinaryError::Unsupported(
                    PrimitiveBinaryUnsupported::Operand {
                        node: nodes.left,
                        type_: unsupported,
                    },
                )),
            );
        }
    }

    #[test]
    fn bigint_exponentiation_requires_target_capability_and_recovers_bigint() {
        let parsed = parse_source_file("const value = left ** right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let bigint = store.intrinsic_bootstrap().unwrap().bigint_type;

        let mut before = request(nodes, SyntaxKind::AsteriskAsteriskToken, bigint, bigint);
        before.bigint_exponentiation_target =
            PrimitiveBigIntExponentiationTarget::KnownBeforeEs2016;
        let before = check_primitive_binary(&mut store, before).unwrap();
        assert_eq!(before.result_type, bigint);
        assert_eq!(
            rendered(&before),
            [(
                nodes.expression,
                2791,
                "Exponentiation cannot be performed on 'bigint' values unless the 'target' option is set to 'es2016' or later.".to_owned(),
            )]
        );

        let mut unknown = request(nodes, SyntaxKind::AsteriskAsteriskToken, bigint, bigint);
        unknown.bigint_exponentiation_target = PrimitiveBigIntExponentiationTarget::Unknown;
        assert_eq!(
            check_primitive_binary(&mut store, unknown),
            Err(PrimitiveBinaryError::Unsupported(
                PrimitiveBinaryUnsupported::BigIntExponentiationTarget(nodes.expression),
            ))
        );
    }

    #[test]
    fn unsupported_and_foreign_operands_never_receive_guessed_results() {
        let parsed = parse_source_file("const value = left + right;");
        assert!(parsed.diagnostics.is_empty());
        let nodes = binary_nodes(&parsed);
        let mut store = initialized_store();
        let foreign = initialized_store();
        let (number, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.any_type)
        };
        let foreign_number = foreign.intrinsic_bootstrap().unwrap().number_type;

        assert_eq!(
            check_primitive_binary(
                &mut store,
                request(nodes, SyntaxKind::PlusToken, any, number),
            ),
            Err(PrimitiveBinaryError::Unsupported(
                PrimitiveBinaryUnsupported::Operand {
                    node: nodes.left,
                    type_: any,
                },
            ))
        );
        assert_eq!(
            check_primitive_binary(
                &mut store,
                request(nodes, SyntaxKind::PlusToken, foreign_number, number),
            ),
            Err(PrimitiveBinaryError::Invariant(
                PrimitiveBinaryInvariant::InvalidType(foreign_number),
            ))
        );
    }
}
