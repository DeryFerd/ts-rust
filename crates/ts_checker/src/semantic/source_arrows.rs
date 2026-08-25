//! Planning for exact arrow values in direct top-level declarations.
//!
//! The installed path proves an unannotated top-level declaration of the form
//! `var|let|const name = (parameters): Return => body`. A separate read-only
//! contextual planner proves `name: Context = (parameters) => body` for empty,
//! concise, and single-return bodies without resolving `Context` or fabricating
//! parameter types. Both retain the ordinary variable symbol separately from
//! the binder's anonymous FUNCTION owner and preserve the export route when
//! present. Publication remains deferred to source dispatch.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation, CheckFlags,
    InternalSymbolName, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    declared::preflight_node,
    functions::{FunctionTypeError, plan_function_type},
    jsdoc::PlannedJavaScriptDeclaration,
    signatures::SignatureFlags,
    source_callables::{
        SourceCallableError, SourceCallableFamily, SourceCallableInvariant, SourceCallablePlan,
        SourceCallableUnsupported, plan_source_callable,
    },
    variables::{
        VariableBindingKind, VariableInvariant, VariablePlanError, VariableUnsupported,
        plan_top_level_variable,
    },
};

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;
const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// The semantic capability requested from the variable annotation.
///
/// Resolution is deliberately outside this module. Source execution must
/// resolve [`SourceContextualTypeRequest::type_node`] and prove this requirement
/// before asking for parameter origins.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualSignatureRequirement {
    SingleNonGenericCallSignature,
}

/// Exact contextual-type syntax retained without resolving a `TypeId`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceContextualTypeRequest {
    pub(super) type_node: NodeRef,
    pub(super) requirement: SourceContextualSignatureRequirement,
}

/// A parameter's request before the contextual signature has been resolved.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualParameterRequest {
    Position { index: usize },
    RestTail { start: usize },
}

/// One identifier parameter and its binder-owned value symbol.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceContextualParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) optional: bool,
    pub(super) rest: bool,
    pub(super) request: SourceContextualParameterRequest,
}

/// The bounded inferred-return shapes admitted by contextual source arrows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualReturnOrigin {
    InferredEmptyBody {
        block: NodeRef,
    },
    InferredConciseExpression {
        expression: NodeRef,
    },
    InferredReturnExpression {
        block: NodeRef,
        statement: NodeRef,
        expression: NodeRef,
    },
}

/// Immutable syntax/binder proof for a context-sensitive arrow initializer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceContextualArrowPlan {
    pub(super) variable_declaration: NodeRef,
    pub(super) variable_name: NodeRef,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) contextual_type: SourceContextualTypeRequest,
    pub(super) contextual_signature_shape: SourceContextualSignatureShape,
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) parameters: Vec<SourceContextualParameterPlan>,
    pub(super) leading_required_parameter_count: usize,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_origin: SourceContextualReturnOrigin,
}

/// Store-independent shape projected from one resolved contextual signature.
///
/// `parameter_count` is the effective positional count after any provider-side
/// tuple-rest normalization, not the raw signature-symbol count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceContextualSignatureShape {
    pub(super) call_signature_count: usize,
    pub(super) type_parameter_count: usize,
    pub(super) parameter_count: usize,
    pub(super) has_effective_rest: bool,
}

/// Why a final parameter type exists after contextual arity is known.
///
/// The final `TypeId` is intentionally absent. In particular, an explicit or
/// contextual `any` and an implicit fallback `any` share an identity but differ
/// in whether TS7006 is reported.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualParameterOrigin {
    ContextualPosition { index: usize },
    ImplicitAny { missing_position: usize },
    ContextualEmptyRestTail { start: usize },
}

/// One parameter after contextual signature selection and arity checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceContextualParameter {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) optional: bool,
    pub(super) rest: bool,
    pub(super) origin: SourceContextualParameterOrigin,
}

/// Semantic-origin plan produced without allocating or publishing types.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceContextualArrowPlan {
    pub(super) parameters: Vec<ResolvedSourceContextualParameter>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_origin: SourceContextualReturnOrigin,
}

impl ResolvedSourceContextualArrowPlan {
    /// Returns the parameter nodes that receive TS7006 under `noImplicitAny`.
    pub(super) fn implicit_any_diagnostic_nodes(&self, no_implicit_any: bool) -> Vec<NodeRef> {
        if !no_implicit_any {
            return Vec::new();
        }
        self.parameters
            .iter()
            .filter_map(|parameter| {
                matches!(
                    parameter.origin,
                    SourceContextualParameterOrigin::ImplicitAny { .. }
                )
                .then_some(parameter.declaration)
            })
            .collect()
    }
}

/// The bounded body shapes whose semantics can be added without replanning the
/// declaration or callable identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowBodyPlan {
    EmptyBlock {
        block: NodeRef,
    },
    ReturnExpression {
        block: NodeRef,
        statement: NodeRef,
        expression: NodeRef,
    },
    ConciseExpression {
        expression: NodeRef,
    },
}

/// Exact syntax for an awaited expression in an inferred async arrow body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceAsyncArrowAwaitStatement {
    pub(super) block: NodeRef,
    pub(super) statement: NodeRef,
    pub(super) await_expression: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) throw_expression: Option<NodeRef>,
}

/// Immutable syntax/binder proof retained by future source dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceArrowPlan {
    pub(super) variable_declaration: NodeRef,
    pub(super) variable_name: NodeRef,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) callable: SourceCallablePlan,
    pub(super) body: SourceArrowBodyPlan,
}

/// Valid TypeScript source shapes intentionally deferred beyond this direct,
/// noncontextual arrow cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowUnsupported {
    NonConstDeclaration(NodeRef),
    NonSingleDeclaration(NodeRef),
    NestedDeclaration(NodeRef),
    ModifiedOrExportedDeclaration(NodeRef),
    NonIdentifierName(NodeRef),
    VariableAnnotation(NodeRef),
    MissingInitializer(NodeRef),
    NonArrowInitializer(NodeRef),
    ComplexBlock(NodeRef),
    BareReturn(NodeRef),
    JsDocContext(NodeRef),
    Variable(VariableUnsupported),
    Callable(SourceCallableUnsupported),
}

/// Malformed AST, binder provenance, or a violated identity invariant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowInvariant {
    InvalidVariableDeclaration(NodeRef),
    InvalidDeclarationList(NodeRef),
    InvalidVariableStatement(NodeRef),
    InvalidSourceFile(NodeRef),
    InvalidVariableName(NodeRef),
    InvalidVariableType(NodeRef),
    InvalidInitializer(NodeRef),
    InvalidOwnerSymbol(NodeRef),
    InvalidBody(NodeRef),
    Variable(VariableInvariant),
    Callable(SourceCallableInvariant),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowError {
    Unsupported(SourceArrowUnsupported),
    Invariant(SourceArrowInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl SourceArrowError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match reason {
                SourceArrowUnsupported::NonConstDeclaration(node)
                | SourceArrowUnsupported::NonSingleDeclaration(node)
                | SourceArrowUnsupported::NestedDeclaration(node)
                | SourceArrowUnsupported::ModifiedOrExportedDeclaration(node)
                | SourceArrowUnsupported::NonIdentifierName(node)
                | SourceArrowUnsupported::VariableAnnotation(node)
                | SourceArrowUnsupported::MissingInitializer(node)
                | SourceArrowUnsupported::NonArrowInitializer(node)
                | SourceArrowUnsupported::ComplexBlock(node)
                | SourceArrowUnsupported::BareReturn(node)
                | SourceArrowUnsupported::JsDocContext(node) => Some(node),
                SourceArrowUnsupported::Variable(_) => None,
                SourceArrowUnsupported::Callable(reason) => {
                    SourceCallableError::Unsupported(reason).node()
                }
            },
            Self::Invariant(reason) => match reason {
                SourceArrowInvariant::InvalidVariableDeclaration(node)
                | SourceArrowInvariant::InvalidDeclarationList(node)
                | SourceArrowInvariant::InvalidVariableStatement(node)
                | SourceArrowInvariant::InvalidSourceFile(node)
                | SourceArrowInvariant::InvalidVariableName(node)
                | SourceArrowInvariant::InvalidVariableType(node)
                | SourceArrowInvariant::InvalidInitializer(node)
                | SourceArrowInvariant::InvalidOwnerSymbol(node)
                | SourceArrowInvariant::InvalidBody(node) => Some(node),
                SourceArrowInvariant::Variable(_) => None,
                SourceArrowInvariant::Callable(reason) => {
                    SourceCallableError::Invariant(reason).node()
                }
            },
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceArrowError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for SourceArrowError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

/// Valid contextual-arrow shapes intentionally deferred beyond the exhausted
/// target-tail, inferred-empty-body cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualArrowUnsupported {
    NonConstDeclaration(NodeRef),
    NonSingleDeclaration(NodeRef),
    NestedDeclaration(NodeRef),
    ModifiedOrExportedDeclaration(NodeRef),
    NonIdentifierName(NodeRef),
    MissingVariableAnnotation(NodeRef),
    MissingInitializer(NodeRef),
    NonArrowInitializer(NodeRef),
    ExpandoProperties(NodeRef),
    GenericSignature(NodeRef),
    Modifiers(NodeRef),
    TrailingParameterComma(NodeRef),
    AnnotatedParameter(NodeRef),
    InitializedParameter(NodeRef),
    DestructuredParameter(NodeRef),
    ParameterModifiers(NodeRef),
    OptionalRestParameter(NodeRef),
    RestParameterNotLast(NodeRef),
    RequiredAfterOptional(NodeRef),
    ExplicitReturnType(NodeRef),
    NonEmptyBody(NodeRef),
    ContextualSignatureCount(NodeRef),
    ContextualGenericSignature(NodeRef),
    ContextualEffectiveRest(NodeRef),
    ContextualArity(NodeRef),
    ContextualNonEmptyRestTail(NodeRef),
    ContextualTargetSyntax(NodeRef),
    Variable(VariableUnsupported),
}

/// Malformed AST, binder provenance, or identity corruption in contextual
/// arrow planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualArrowInvariant {
    InvalidVariableDeclaration(NodeRef),
    InvalidDeclarationList(NodeRef),
    InvalidVariableStatement(NodeRef),
    InvalidSourceFile(NodeRef),
    InvalidVariableName(NodeRef),
    InvalidVariableType(NodeRef),
    InvalidInitializer(NodeRef),
    InvalidOwnerSymbol(NodeRef),
    InvalidParameter(NodeRef),
    InvalidParameterSymbol(NodeRef),
    InvalidBody(NodeRef),
    Capacity(NodeRef),
    Variable(VariableInvariant),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualArrowError {
    Unsupported(SourceContextualArrowUnsupported),
    Invariant(SourceContextualArrowInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl SourceContextualArrowError {
    #[allow(dead_code)] // Consumed by the next source-execution integration slice.
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match reason {
                SourceContextualArrowUnsupported::NonConstDeclaration(node)
                | SourceContextualArrowUnsupported::NonSingleDeclaration(node)
                | SourceContextualArrowUnsupported::NestedDeclaration(node)
                | SourceContextualArrowUnsupported::ModifiedOrExportedDeclaration(node)
                | SourceContextualArrowUnsupported::NonIdentifierName(node)
                | SourceContextualArrowUnsupported::MissingVariableAnnotation(node)
                | SourceContextualArrowUnsupported::MissingInitializer(node)
                | SourceContextualArrowUnsupported::NonArrowInitializer(node)
                | SourceContextualArrowUnsupported::ExpandoProperties(node)
                | SourceContextualArrowUnsupported::GenericSignature(node)
                | SourceContextualArrowUnsupported::Modifiers(node)
                | SourceContextualArrowUnsupported::TrailingParameterComma(node)
                | SourceContextualArrowUnsupported::AnnotatedParameter(node)
                | SourceContextualArrowUnsupported::InitializedParameter(node)
                | SourceContextualArrowUnsupported::DestructuredParameter(node)
                | SourceContextualArrowUnsupported::ParameterModifiers(node)
                | SourceContextualArrowUnsupported::OptionalRestParameter(node)
                | SourceContextualArrowUnsupported::RestParameterNotLast(node)
                | SourceContextualArrowUnsupported::RequiredAfterOptional(node)
                | SourceContextualArrowUnsupported::ExplicitReturnType(node)
                | SourceContextualArrowUnsupported::NonEmptyBody(node)
                | SourceContextualArrowUnsupported::ContextualSignatureCount(node)
                | SourceContextualArrowUnsupported::ContextualGenericSignature(node)
                | SourceContextualArrowUnsupported::ContextualEffectiveRest(node)
                | SourceContextualArrowUnsupported::ContextualArity(node)
                | SourceContextualArrowUnsupported::ContextualNonEmptyRestTail(node)
                | SourceContextualArrowUnsupported::ContextualTargetSyntax(node) => Some(node),
                SourceContextualArrowUnsupported::Variable(_) => None,
            },
            Self::Invariant(reason) => match reason {
                SourceContextualArrowInvariant::InvalidVariableDeclaration(node)
                | SourceContextualArrowInvariant::InvalidDeclarationList(node)
                | SourceContextualArrowInvariant::InvalidVariableStatement(node)
                | SourceContextualArrowInvariant::InvalidSourceFile(node)
                | SourceContextualArrowInvariant::InvalidVariableName(node)
                | SourceContextualArrowInvariant::InvalidVariableType(node)
                | SourceContextualArrowInvariant::InvalidInitializer(node)
                | SourceContextualArrowInvariant::InvalidOwnerSymbol(node)
                | SourceContextualArrowInvariant::InvalidParameter(node)
                | SourceContextualArrowInvariant::InvalidParameterSymbol(node)
                | SourceContextualArrowInvariant::InvalidBody(node)
                | SourceContextualArrowInvariant::Capacity(node) => Some(node),
                SourceContextualArrowInvariant::Variable(_) => None,
            },
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceContextualArrowError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for SourceContextualArrowError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

fn contextual_target_plan_error(
    error: FunctionTypeError,
    fallback: NodeRef,
) -> SourceContextualArrowError {
    let node = error.node().unwrap_or(fallback);
    match error {
        FunctionTypeError::Unsupported(_) => contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
        ),
        FunctionTypeError::Invariant(_) => {
            contextual_invariant(SourceContextualArrowInvariant::InvalidVariableType(node))
        }
        FunctionTypeError::DeclaredType(error) => SourceContextualArrowError::DeclaredType(error),
        FunctionTypeError::LiteralCache(error) => SourceContextualArrowError::LiteralCache(error),
    }
}

fn plan_contextual_target_syntax_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_node: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(SourceContextualSignatureShape, NodeRef), SourceContextualArrowError> {
    let (function, alias) =
        contextual_function_type_syntax(store, host, type_node, None, &mut HashSet::new())?;
    let function_record = preflight_node(store, host, function)?;
    let (parameter_count, return_type) = match function_record.kind {
        SyntaxKind::FunctionType => {
            let plan = plan_function_type(store, host, function, alias, false, array_targets)
                .map_err(|error| contextual_target_plan_error(error, type_node))?;
            (plan.parameters.len(), plan.return_type)
        }
        SyntaxKind::TypeLiteral | SyntaxKind::InterfaceDeclaration => {
            contextual_declared_call_signature_shape(store, host, function, type_node)?
        }
        _ => {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::ContextualTargetSyntax(type_node),
            ));
        }
    };
    let return_record = preflight_node(store, host, return_type)?;
    if !matches!(
        return_record.kind,
        SyntaxKind::VoidKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::LiteralType
            | SyntaxKind::TypeLiteral
            | SyntaxKind::TypeReference
            | SyntaxKind::ParenthesizedType
            | SyntaxKind::UnionType
    ) {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(return_type),
        ));
    }
    Ok((
        SourceContextualSignatureShape {
            call_signature_count: 1,
            type_parameter_count: 0,
            parameter_count,
            has_effective_rest: false,
        },
        return_type,
    ))
}

#[allow(clippy::too_many_lines)] // Keep one declared-call syntax and ownership proof atomic.
fn contextual_declared_call_signature_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    target: NodeRef,
) -> Result<(usize, NodeRef), SourceContextualArrowError> {
    let record = preflight_node(store, host, owner)?;
    let (members, expected_owner_flags) = match &record.data {
        NodeData::TypeLiteralNode(literal) if record.kind == SyntaxKind::TypeLiteral => {
            (&literal.members, SymbolFlags::TYPE_LITERAL)
        }
        NodeData::InterfaceDeclaration(interface)
            if record.kind == SyntaxKind::InterfaceDeclaration =>
        {
            (&interface.members, SymbolFlags::INTERFACE)
        }
        _ => {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidVariableType(owner),
            ));
        }
    };
    let bound = host.bound_file(owner).ok_or_else(|| {
        contextual_invariant(SourceContextualArrowInvariant::InvalidVariableType(owner))
    })?;
    let owner_symbol = bound.symbol(owner).ok_or_else(|| {
        contextual_invariant(SourceContextualArrowInvariant::InvalidVariableType(owner))
    })?;
    if store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store
            .symbol(owner_symbol)
            .is_none_or(|symbol| !symbol.flags().contains(expected_owner_flags))
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableType(owner),
        ));
    }

    let mut signature = None;
    for member in &members.nodes {
        let member = NodeRef::new(owner.arena, owner.file, *member);
        let member_record = preflight_node(store, host, member)?;
        if member_record.parent != Some(owner.node)
            || !range_contains(record.range, member_record.range)
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidVariableType(member),
            ));
        }
        if member_record.kind == SyntaxKind::CallSignature && signature.replace(member).is_some() {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::ContextualSignatureCount(target),
            ));
        }
    }
    let Some(signature) = signature else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualSignatureCount(target),
        ));
    };
    let signature_record = preflight_node(store, host, signature)?;
    let NodeData::CallSignatureDeclaration(call) = &signature_record.data else {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableType(signature),
        ));
    };
    if signature_record.flags.0 != 0
        || call.full_signature.is_some()
        || call.next_container.is_some()
        || call.symbol.is_some()
        || call.type_parameters.is_some()
        || call.parameters.has_trailing_comma
    {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(signature),
        ));
    }
    let Some(return_id) = call.type_ else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(signature),
        ));
    };
    let return_type = NodeRef::new(signature.arena, signature.file, return_id);
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.parent != Some(signature.node)
        || !range_contains(signature_record.range, return_record.range)
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableType(return_type),
        ));
    }
    for parameter in &call.parameters.nodes {
        let parameter = NodeRef::new(signature.arena, signature.file, *parameter);
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidVariableType(parameter),
            ));
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(signature.node)
            || !range_contains(signature_record.range, parameter_record.range)
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidVariableType(parameter),
            ));
        }
        if data.type_.is_none()
            || data.dot_dot_dot_token.is_some()
            || data.initializer.is_some()
            || data.modifiers.is_some()
        {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::ContextualTargetSyntax(parameter),
            ));
        }
    }
    Ok((call.parameters.nodes.len(), return_type))
}

#[allow(clippy::too_many_lines)] // Keep the read-only alias and intersection proof atomic.
fn contextual_function_type_syntax(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    alias: Option<SemanticSymbolId>,
    active_aliases: &mut HashSet<SemanticSymbolId>,
) -> Result<(NodeRef, Option<SemanticSymbolId>), SourceContextualArrowError> {
    let record = preflight_node(store, host, node)?;
    match (&record.kind, &record.data) {
        (SyntaxKind::FunctionType, NodeData::FunctionTypeNode(_)) => Ok((node, alias)),
        (SyntaxKind::TypeLiteral, NodeData::TypeLiteralNode(literal)) => {
            let has_call_signature = literal.members.nodes.iter().any(|member| {
                let member = NodeRef::new(node.arena, node.file, *member);
                host.node(member)
                    .is_some_and(|record| record.kind == SyntaxKind::CallSignature)
            });
            if has_call_signature {
                Ok((node, alias))
            } else {
                Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ))
            }
        }
        (SyntaxKind::ParenthesizedType, NodeData::ParenthesizedTypeNode(parenthesized)) => {
            let child = NodeRef::new(node.arena, node.file, parenthesized.type_);
            let child_record = preflight_node(store, host, child)?;
            if child_record.parent != Some(node.node)
                || !range_contains(record.range, child_record.range)
            {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(child),
                ));
            }
            contextual_function_type_syntax(store, host, child, alias, active_aliases)
        }
        (SyntaxKind::TypeReference, NodeData::TypeReferenceNode(reference)) => {
            if reference.type_arguments.is_some() {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            }
            let name = NodeRef::new(node.arena, node.file, reference.type_name);
            let name_record = preflight_node(store, host, name)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.parent != Some(node.node)
                || name_record.flags.0 != 0
                || identifier.flow_node.is_some()
            {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(name),
                ));
            }
            let (arena, bound) = host.source(node).ok_or_else(|| {
                contextual_invariant(SourceContextualArrowInvariant::InvalidVariableType(node))
            })?;
            let mut callback_host = host.name_resolver_host(store)?;
            let mut resolver =
                CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
                    .map_err(DeclaredTypeError::from)?;
            let symbol = match resolver.resolve(
                Some(CanonicalResolutionLocation::Bound(name)),
                &identifier.text,
                SymbolFlags::TYPE,
                None,
                true,
                false,
            ) {
                Ok(Some(symbol)) => symbol,
                Ok(None) | Err(CanonicalNameResolutionError::AliasResolutionUnavailable(_)) => {
                    return Err(contextual_unsupported(
                        SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                    ));
                }
                Err(error) => return Err(DeclaredTypeError::from(error).into()),
            };
            let Some(symbol) = store.get_merged_symbol(symbol) else {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(node),
                ));
            };
            let Some(symbol_record) = store.symbol(symbol) else {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(node),
                ));
            };
            let Some([declaration]) = symbol_record.declarations() else {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            };
            if !host.symbol_matches(store, *declaration, symbol) {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            }
            if symbol_record.flags() == SymbolFlags::INTERFACE {
                let declaration_record = preflight_node(store, host, *declaration)?;
                if declaration_record.kind == SyntaxKind::InterfaceDeclaration {
                    return Ok((*declaration, None));
                }
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(*declaration),
                ));
            }
            if symbol_record.flags() != SymbolFlags::TYPE_ALIAS || !active_aliases.insert(symbol) {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            }
            let declaration_record = preflight_node(store, host, *declaration)?;
            let NodeData::TypeAliasDeclaration(declaration_data) = &declaration_record.data else {
                active_aliases.remove(&symbol);
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(*declaration),
                ));
            };
            if declaration_record.kind != SyntaxKind::TypeAliasDeclaration
                || declaration_data.type_parameters.is_some()
            {
                active_aliases.remove(&symbol);
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                ));
            }
            let body = NodeRef::new(declaration.arena, declaration.file, declaration_data.type_);
            let body_record = preflight_node(store, host, body)?;
            if body_record.parent != Some(declaration.node)
                || !range_contains(declaration_record.range, body_record.range)
            {
                active_aliases.remove(&symbol);
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidVariableType(body),
                ));
            }
            let alias_target =
                contextual_function_type_syntax(store, host, body, Some(symbol), active_aliases);
            active_aliases.remove(&symbol);
            alias_target
        }
        (SyntaxKind::IntersectionType, NodeData::IntersectionTypeNode(intersection)) => {
            let mut callable = None;
            for constituent in &intersection.types.nodes {
                let constituent = NodeRef::new(node.arena, node.file, *constituent);
                let constituent_record = preflight_node(store, host, constituent)?;
                if constituent_record.parent != Some(node.node)
                    || !range_contains(record.range, constituent_record.range)
                {
                    return Err(contextual_invariant(
                        SourceContextualArrowInvariant::InvalidVariableType(constituent),
                    ));
                }
                match contextual_function_type_syntax(
                    store,
                    host,
                    constituent,
                    None,
                    active_aliases,
                ) {
                    Ok(found) if callable.replace(found).is_some() => {
                        return Err(contextual_unsupported(
                            SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
                        ));
                    }
                    Ok(_)
                    | Err(SourceContextualArrowError::Unsupported(
                        SourceContextualArrowUnsupported::ContextualTargetSyntax(_),
                    )) => {}
                    Err(error) => return Err(error),
                }
            }
            callable.ok_or_else(|| {
                contextual_unsupported(SourceContextualArrowUnsupported::ContextualTargetSyntax(
                    node,
                ))
            })
        }
        _ => Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(node),
        )),
    }
}

/// Proves one direct context-sensitive arrow without resolving its annotation
/// or mutating semantic state.
#[allow(clippy::too_many_lines)] // One atomic syntax and binder provenance proof.
pub(super) fn plan_contextual_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    variable_declaration: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceContextualArrowPlan, SourceContextualArrowError> {
    let declaration_record = preflight_node(store, host, variable_declaration)?;
    let NodeData::VariableDeclaration(declaration) = &declaration_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonConstDeclaration(variable_declaration),
        ));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration.exclamation_token.is_some()
        || declaration.local_symbol.is_some()
        || declaration.symbol.is_some()
        || declaration.facts != 0
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableDeclaration(variable_declaration),
        ));
    }

    let Some(list_id) = declaration_record.parent else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NestedDeclaration(variable_declaration),
        ));
    };
    let list = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        list_id,
    );
    let list_record = preflight_node(store, host, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NestedDeclaration(variable_declaration),
        ));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || !range_contains(list_record.range, declaration_record.range)
        || list_data.declarations.range != list_record.range
        || list_data.declarations.has_trailing_comma
        || list_data.facts != 0
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidDeclarationList(list),
        ));
    }
    let binding = arrow_binding_kind(list_record.flags.0).ok_or_else(|| {
        contextual_unsupported(SourceContextualArrowUnsupported::NonConstDeclaration(list))
    })?;
    if list_data.declarations.nodes.len() != 1 {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonSingleDeclaration(list),
        ));
    }
    if list_data.declarations.nodes[0] != variable_declaration.node {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidDeclarationList(list),
        ));
    }

    let Some(statement_id) = list_record.parent else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NestedDeclaration(list),
        ));
    };
    let statement = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        statement_id,
    );
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NestedDeclaration(list),
        ));
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
        || statement_record.flags.0 != 0
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !range_contains(statement_record.range, list_record.range)
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableStatement(statement),
        ));
    }
    let exported = match statement_data.modifiers.as_ref() {
        None => false,
        Some(modifiers)
            if valid_arrow_export_modifier(
                store,
                host,
                statement,
                statement_record,
                list_record,
                modifiers,
            )? =>
        {
            true
        }
        Some(_) => {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::ModifiedOrExportedDeclaration(statement),
            ));
        }
    };

    let bound = host.bound_file(variable_declaration).ok_or_else(|| {
        contextual_invariant(SourceContextualArrowInvariant::InvalidSourceFile(statement))
    })?;
    let source = bound.source_file();
    if statement_record.parent != Some(source.node) {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NestedDeclaration(statement),
        ));
    }
    let source_record = preflight_node(store, host, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidSourceFile(source),
        ));
    };
    if source_record.kind != SyntaxKind::SourceFile
        || !range_contains(source_record.range, statement_record.range)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidSourceFile(source),
        ));
    }

    let variable_name = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        declaration.name,
    );
    let name_record = preflight_node(store, host, variable_name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonIdentifierName(variable_name),
        ));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(variable_declaration.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || !range_contains(declaration_record.range, name_record.range)
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableName(variable_name),
        ));
    }

    let Some(type_id) = declaration.type_ else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::MissingVariableAnnotation(variable_declaration),
        ));
    };
    let type_node = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        type_id,
    );
    let type_record = preflight_node(store, host, type_node)?;
    if type_record.parent != Some(variable_declaration.node)
        || !range_contains(declaration_record.range, type_record.range)
        || type_record.range.start < name_record.range.end
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidVariableType(type_node),
        ));
    }
    let (contextual_signature_shape, contextual_return_type) =
        plan_contextual_target_syntax_shape(store, host, type_node, array_targets)?;

    let Some(initializer_id) = declaration.initializer else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::MissingInitializer(variable_declaration),
        ));
    };
    let initializer = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        initializer_id,
    );
    let initializer_record = preflight_node(store, host, initializer)?;
    if initializer_record.parent != Some(variable_declaration.node)
        || !range_contains(declaration_record.range, initializer_record.range)
        || initializer_record.range.start < type_record.range.end
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidInitializer(initializer),
        ));
    }
    let NodeData::ArrowFunction(arrow) = &initializer_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonArrowInitializer(initializer),
        ));
    };
    if initializer_record.kind != SyntaxKind::ArrowFunction
        || initializer_record.flags.0 & NODE_FLAG_JSDOC != 0
        || arrow.asterisk_token.is_some()
        || arrow.full_signature.is_some()
        || arrow.next_container.is_some()
        || arrow.symbol.is_some()
        || arrow.flow_node.is_some()
        || arrow.end_flow_node.is_some()
        || arrow.facts != 0
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidInitializer(initializer),
        ));
    }
    if arrow.type_parameters.is_some() {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::GenericSignature(initializer),
        ));
    }
    if arrow.modifiers.is_some() {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::Modifiers(initializer),
        ));
    }
    if let Some(return_id) = arrow.type_ {
        let return_type = NodeRef::new(initializer.arena, initializer.file, return_id);
        let return_record = preflight_node(store, host, return_type)?;
        if return_record.parent != Some(initializer.node)
            || !range_contains(initializer_record.range, return_record.range)
            || return_record.range.start < arrow.parameters.range.end
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidInitializer(return_type),
            ));
        }
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ExplicitReturnType(return_type),
        ));
    }
    if arrow.parameters.range.start < initializer_record.range.start
        || arrow.parameters.range.end > initializer_record.range.end
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidInitializer(initializer),
        ));
    }
    if arrow.parameters.has_trailing_comma {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::TrailingParameterComma(initializer),
        ));
    }

    let variable_symbol = plan_top_level_variable(
        bound,
        store,
        variable_declaration,
        variable_name,
        &identifier.text,
        binding,
        exported,
    )
    .map_err(map_contextual_variable_error)?;
    let owner_symbol = bound.symbol(initializer).ok_or_else(|| {
        contextual_invariant(SourceContextualArrowInvariant::InvalidOwnerSymbol(
            initializer,
        ))
    })?;
    let owner = store.symbol(owner_symbol).ok_or_else(|| {
        contextual_invariant(SourceContextualArrowInvariant::InvalidOwnerSymbol(
            initializer,
        ))
    })?;
    if owner_symbol == variable_symbol
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.name() != InternalSymbolName::Function.as_ref()
        || owner.declarations() != Some(&[initializer])
        || owner.value_declaration() != Some(initializer)
        || owner.members().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidOwnerSymbol(initializer),
        ));
    }
    // Contextual arrows use a separate planner, but retain the same pinned
    // expando ownership: valid property assignments live in owner exports.
    if owner.exports().is_some() {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ExpandoProperties(initializer),
        ));
    }

    let parameter_count = arrow.parameters.nodes.len();
    let mut parameters = Vec::with_capacity(parameter_count);
    let mut previous_end = arrow.parameters.range.start;
    let mut optional_seen = false;
    let mut leading_required_parameter_count = 0usize;
    let mut flags = SignatureFlags::NONE;
    for (index, parameter_id) in arrow.parameters.nodes.iter().enumerate() {
        let parameter = NodeRef::new(initializer.arena, initializer.file, *parameter_id);
        if parameters
            .iter()
            .any(|planned: &SourceContextualParameterPlan| planned.declaration == parameter)
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            ));
        }
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            ));
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(initializer.node)
            || parameter_record.flags.0 & NODE_FLAG_JSDOC != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < arrow.parameters.range.start
            || parameter_record.range.end > arrow.parameters.range.end
            || data.symbol.is_some()
            || data.facts != 0
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            ));
        }
        previous_end = parameter_record.range.end;
        if data.modifiers.is_some() {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::ParameterModifiers(parameter),
            ));
        }
        if data.initializer.is_some() {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::InitializedParameter(parameter),
            ));
        }
        if let Some(type_id) = data.type_ {
            let annotation = NodeRef::new(parameter.arena, parameter.file, type_id);
            preflight_contextual_child(
                store,
                host,
                parameter,
                annotation,
                SourceContextualArrowInvariant::InvalidParameter(annotation),
            )?;
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::AnnotatedParameter(annotation),
            ));
        }

        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(parameter_identifier) = &name_record.data else {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::DestructuredParameter(parameter),
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || name_record.flags.0 != 0
            || parameter_identifier.flow_node.is_some()
            || !range_contains(parameter_record.range, name_record.range)
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            ));
        }
        if parameter_identifier.text == "this" {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::DestructuredParameter(parameter),
            ));
        }

        let rest = if let Some(token_id) = data.dot_dot_dot_token {
            let token = NodeRef::new(parameter.arena, parameter.file, token_id);
            let token_record = preflight_contextual_child(
                store,
                host,
                parameter,
                token,
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            )?;
            if token_record.kind != SyntaxKind::DotDotDotToken
                || token_record.range.start < parameter_record.range.start
                || token_record.range.end > name_record.range.start
            {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidParameter(parameter),
                ));
            }
            true
        } else {
            false
        };
        let optional = if let Some(token_id) = data.question_token {
            let token = NodeRef::new(parameter.arena, parameter.file, token_id);
            let token_record = preflight_contextual_child(
                store,
                host,
                parameter,
                token,
                SourceContextualArrowInvariant::InvalidParameter(parameter),
            )?;
            if token_record.kind != SyntaxKind::QuestionToken
                || token_record.range.start < name_record.range.end
                || token_record.range.end > parameter_record.range.end
            {
                return Err(contextual_invariant(
                    SourceContextualArrowInvariant::InvalidParameter(parameter),
                ));
            }
            true
        } else {
            false
        };
        if rest && optional {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::OptionalRestParameter(parameter),
            ));
        }
        if rest && index + 1 != parameter_count {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::RestParameterNotLast(parameter),
            ));
        }
        if optional {
            optional_seen = true;
        } else if !rest && optional_seen {
            return Err(contextual_unsupported(
                SourceContextualArrowUnsupported::RequiredAfterOptional(parameter),
            ));
        } else if !rest {
            leading_required_parameter_count = leading_required_parameter_count
                .checked_add(1)
                .ok_or_else(|| {
                    contextual_invariant(SourceContextualArrowInvariant::Capacity(parameter))
                })?;
        }
        if rest {
            flags |= SignatureFlags::HAS_REST_PARAMETER;
        }

        let raw_symbol = bound.symbol(parameter).ok_or_else(|| {
            contextual_invariant(SourceContextualArrowInvariant::InvalidParameterSymbol(
                parameter,
            ))
        })?;
        let symbol = store.get_merged_symbol(raw_symbol).ok_or_else(|| {
            contextual_invariant(SourceContextualArrowInvariant::InvalidParameterSymbol(
                parameter,
            ))
        })?;
        let symbol_record = store.symbol(symbol).ok_or_else(|| {
            contextual_invariant(SourceContextualArrowInvariant::InvalidParameterSymbol(
                parameter,
            ))
        })?;
        if symbol != raw_symbol
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_bytes() != parameter_identifier.text.as_bytes()
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration() != Some(parameter)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidParameterSymbol(parameter),
            ));
        }
        parameters.push(SourceContextualParameterPlan {
            declaration: parameter,
            name,
            symbol,
            optional,
            rest,
            request: if rest {
                SourceContextualParameterRequest::RestTail { start: index }
            } else {
                SourceContextualParameterRequest::Position { index }
            },
        });
    }

    let body = NodeRef::new(initializer.arena, initializer.file, arrow.body);
    let body_record = preflight_node(store, host, body)?;
    if body_record.parent != Some(initializer.node)
        || !range_contains(initializer_record.range, body_record.range)
        || body_record.flags.0 != 0
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidBody(body),
        ));
    }
    let return_origin = if let NodeData::Block(block) = &body_record.data {
        if body_record.kind != SyntaxKind::Block
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.statements.has_trailing_comma
            || block.facts != 0
        {
            return Err(contextual_invariant(
                SourceContextualArrowInvariant::InvalidBody(body),
            ));
        }
        match block.statements.nodes.as_slice() {
            [] => {
                if preflight_node(store, host, contextual_return_type)?.kind
                    != SyntaxKind::VoidKeyword
                {
                    return Err(contextual_unsupported(
                        SourceContextualArrowUnsupported::ContextualTargetSyntax(
                            contextual_return_type,
                        ),
                    ));
                }
                SourceContextualReturnOrigin::InferredEmptyBody { block: body }
            }
            [statement] => {
                let statement = NodeRef::new(body.arena, body.file, *statement);
                let statement_record = preflight_node(store, host, statement)?;
                let NodeData::ReturnStatement(return_statement) = &statement_record.data else {
                    return Err(contextual_unsupported(
                        SourceContextualArrowUnsupported::NonEmptyBody(body),
                    ));
                };
                let Some(expression) = return_statement.expression else {
                    return Err(contextual_unsupported(
                        SourceContextualArrowUnsupported::NonEmptyBody(body),
                    ));
                };
                let expression = NodeRef::new(statement.arena, statement.file, expression);
                let expression_record = preflight_node(store, host, expression)?;
                if statement_record.kind != SyntaxKind::ReturnStatement
                    || statement_record.flags.0 != 0
                    || statement_record.parent != Some(body.node)
                    || return_statement.flow_node.is_some()
                    || return_statement.facts != 0
                    || !range_contains(body_record.range, statement_record.range)
                    || expression_record.parent != Some(statement.node)
                    || !range_contains(statement_record.range, expression_record.range)
                {
                    return Err(contextual_invariant(
                        SourceContextualArrowInvariant::InvalidBody(statement),
                    ));
                }
                SourceContextualReturnOrigin::InferredReturnExpression {
                    block: body,
                    statement,
                    expression,
                }
            }
            _ => {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::NonEmptyBody(body),
                ));
            }
        }
    } else {
        SourceContextualReturnOrigin::InferredConciseExpression { expression: body }
    };
    let arrow_token = NodeRef::new(
        initializer.arena,
        initializer.file,
        arrow.equals_greater_than_token,
    );
    let arrow_token_record = preflight_contextual_child(
        store,
        host,
        initializer,
        arrow_token,
        SourceContextualArrowInvariant::InvalidInitializer(arrow_token),
    )?;
    if arrow_token_record.kind != SyntaxKind::EqualsGreaterThanToken
        || arrow_token_record.range.start < arrow.parameters.range.end
        || arrow_token_record.range.end > body_record.range.start
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidInitializer(arrow_token),
        ));
    }

    let min_argument_count = i32::try_from(leading_required_parameter_count)
        .map_err(|_| contextual_invariant(SourceContextualArrowInvariant::Capacity(initializer)))?;
    let plan = SourceContextualArrowPlan {
        variable_declaration,
        variable_name,
        variable_symbol,
        contextual_type: SourceContextualTypeRequest {
            type_node,
            requirement: SourceContextualSignatureRequirement::SingleNonGenericCallSignature,
        },
        contextual_signature_shape,
        declaration: initializer,
        owner_symbol,
        parameters,
        leading_required_parameter_count,
        flags,
        min_argument_count,
        return_origin,
    };
    resolve_contextual_arrow_parameter_origins(&plan, contextual_signature_shape)?;
    Ok(plan)
}

/// Applies pinned contextual-signature eligibility and records why each
/// parameter receives a type, without allocating that type.
pub(super) fn resolve_contextual_arrow_parameter_origins(
    plan: &SourceContextualArrowPlan,
    contextual: SourceContextualSignatureShape,
) -> Result<ResolvedSourceContextualArrowPlan, SourceContextualArrowError> {
    let target = plan.contextual_type.type_node;
    if contextual.call_signature_count != 1 {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualSignatureCount(target),
        ));
    }
    if contextual.type_parameter_count != 0 {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualGenericSignature(target),
        ));
    }
    if contextual.has_effective_rest {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualEffectiveRest(target),
        ));
    }
    if contextual.parameter_count < plan.leading_required_parameter_count {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualArity(target),
        ));
    }

    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for parameter in &plan.parameters {
        let origin = match parameter.request {
            SourceContextualParameterRequest::Position { index }
                if index < contextual.parameter_count =>
            {
                SourceContextualParameterOrigin::ContextualPosition { index }
            }
            SourceContextualParameterRequest::Position { index } => {
                SourceContextualParameterOrigin::ImplicitAny {
                    missing_position: index,
                }
            }
            SourceContextualParameterRequest::RestTail { start }
                if start < contextual.parameter_count =>
            {
                return Err(contextual_unsupported(
                    SourceContextualArrowUnsupported::ContextualNonEmptyRestTail(
                        parameter.declaration,
                    ),
                ));
            }
            SourceContextualParameterRequest::RestTail { start } => {
                SourceContextualParameterOrigin::ContextualEmptyRestTail { start }
            }
        };
        parameters.push(ResolvedSourceContextualParameter {
            declaration: parameter.declaration,
            name: parameter.name,
            symbol: parameter.symbol,
            optional: parameter.optional,
            rest: parameter.rest,
            origin,
        });
    }
    Ok(ResolvedSourceContextualArrowPlan {
        parameters,
        flags: plan.flags,
        min_argument_count: plan.min_argument_count,
        return_origin: plan.return_origin,
    })
}

/// Proves one JavaScript arrow whose contextual signature comes from its own
/// resolved `@callback` annotation instead of a written variable type node.
pub(super) fn plan_jsdoc_contextual_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    variable_declaration: NodeRef,
    jsdoc: &PlannedJavaScriptDeclaration,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceArrowPlan, SourceArrowError> {
    let invalid_context =
        || unsupported(SourceArrowUnsupported::JsDocContext(variable_declaration));
    if jsdoc.node() != variable_declaration {
        return Err(invariant(SourceArrowInvariant::InvalidVariableDeclaration(
            variable_declaration,
        )));
    }
    let bound = host.bound_file(variable_declaration).ok_or_else(|| {
        invariant(SourceArrowInvariant::InvalidSourceFile(
            variable_declaration,
        ))
    })?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file())
    {
        return Err(invalid_context());
    }

    let annotation = jsdoc.type_().ok_or_else(invalid_context)?;
    let callback = annotation.resolved_callback().ok_or_else(invalid_context)?;
    if annotation.resolved_alias_name() != Some(callback.name())
        || jsdoc
            .callbacks()
            .iter()
            .filter(|candidate| *candidate == callback)
            .count()
            != 1
        || !callback.template_parameters().is_empty()
        || callback.this_type().is_some()
        || callback.return_type().is_none()
        || callback.parameters().iter().any(|parameter| {
            parameter.name().is_empty() || parameter.type_().is_none() || parameter.is_optional()
        })
    {
        return Err(invalid_context());
    }

    let planned = plan_source_arrow(store, host, variable_declaration, array_targets)?;
    let SourceArrowBodyPlan::EmptyBlock { block } = planned.body else {
        return Err(unsupported(SourceArrowUnsupported::ComplexBlock(
            planned.callable.body,
        )));
    };
    let block_record = preflight_node(store, host, block)?;
    let NodeData::Block(body) = &block_record.data else {
        return Err(invariant(SourceArrowInvariant::InvalidBody(block)));
    };
    if !body.statements.nodes.is_empty() {
        return Err(unsupported(SourceArrowUnsupported::ComplexBlock(block)));
    }
    if planned.callable.family != SourceCallableFamily::ArrowFunction
        || !planned.callable.type_parameters.is_empty()
        || !planned.callable.return_type.is_inferred()
        || planned.callable.parameters.len() != callback.parameters().len()
        || planned.callable.min_argument_count
            != i32::try_from(planned.callable.parameters.len()).map_err(|_| invalid_context())?
        || planned.callable.flags
            != if planned.callable.parameters.is_empty() {
                SignatureFlags::NONE
            } else {
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
            }
        || planned.callable.parameters.iter().any(|parameter| {
            parameter.explicit_type_node().is_some()
                || parameter.initializer.is_some()
                || parameter.optional
                || parameter.rest
        })
    {
        return Err(invalid_context());
    }

    Ok(planned)
}

/// Proves one direct annotated arrow without mutating semantic state.
pub(super) fn plan_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    variable_declaration: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceArrowPlan, SourceArrowError> {
    let declaration_record = preflight_node(store, host, variable_declaration)?;
    let NodeData::VariableDeclaration(declaration) = &declaration_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonConstDeclaration(
            variable_declaration,
        )));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration.exclamation_token.is_some()
        || declaration.local_symbol.is_some()
        || declaration.symbol.is_some()
        || declaration.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableDeclaration(
            variable_declaration,
        )));
    }

    let Some(list_id) = declaration_record.parent else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            variable_declaration,
        )));
    };
    let list = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        list_id,
    );
    let list_record = preflight_node(store, host, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            variable_declaration,
        )));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || !range_contains(list_record.range, declaration_record.range)
        || list_data.declarations.range != list_record.range
        || list_data.declarations.has_trailing_comma
        || list_data.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidDeclarationList(
            list,
        )));
    }
    let binding = arrow_binding_kind(list_record.flags.0)
        .ok_or_else(|| unsupported(SourceArrowUnsupported::NonConstDeclaration(list)))?;
    if list_data.declarations.nodes.len() != 1 {
        return Err(unsupported(SourceArrowUnsupported::NonSingleDeclaration(
            list,
        )));
    }
    if list_data.declarations.nodes[0] != variable_declaration.node {
        return Err(invariant(SourceArrowInvariant::InvalidDeclarationList(
            list,
        )));
    }

    let Some(statement_id) = list_record.parent else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(list)));
    };
    let statement = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        statement_id,
    );
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(list)));
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
        || statement_record.flags.0 != 0
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !range_contains(statement_record.range, list_record.range)
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableStatement(
            statement,
        )));
    }
    let exported = match statement_data.modifiers.as_ref() {
        None => false,
        Some(modifiers)
            if valid_arrow_export_modifier(
                store,
                host,
                statement,
                statement_record,
                list_record,
                modifiers,
            )? =>
        {
            true
        }
        Some(_) => {
            return Err(unsupported(
                SourceArrowUnsupported::ModifiedOrExportedDeclaration(statement),
            ));
        }
    };

    let bound = host
        .bound_file(variable_declaration)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidSourceFile(statement)))?;
    let source = bound.source_file();
    if statement_record.parent != Some(source.node) {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            statement,
        )));
    }
    let source_record = preflight_node(store, host, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceArrowInvariant::InvalidSourceFile(source)));
    };
    if source_record.kind != SyntaxKind::SourceFile
        || !range_contains(source_record.range, statement_record.range)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
    {
        return Err(invariant(SourceArrowInvariant::InvalidSourceFile(source)));
    }

    let variable_name = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        declaration.name,
    );
    let name_record = preflight_node(store, host, variable_name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonIdentifierName(
            variable_name,
        )));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(variable_declaration.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || !range_contains(declaration_record.range, name_record.range)
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableName(
            variable_name,
        )));
    }

    if let Some(type_id) = declaration.type_ {
        let type_node = NodeRef::new(
            variable_declaration.arena,
            variable_declaration.file,
            type_id,
        );
        let type_record = preflight_node(store, host, type_node)?;
        if type_record.parent != Some(variable_declaration.node)
            || !range_contains(declaration_record.range, type_record.range)
            || type_record.range.start < name_record.range.end
        {
            return Err(invariant(SourceArrowInvariant::InvalidVariableType(
                type_node,
            )));
        }
        return Err(unsupported(SourceArrowUnsupported::VariableAnnotation(
            type_node,
        )));
    }

    let Some(initializer_id) = declaration.initializer else {
        return Err(unsupported(SourceArrowUnsupported::MissingInitializer(
            variable_declaration,
        )));
    };
    let initializer = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        initializer_id,
    );
    let initializer_record = preflight_node(store, host, initializer)?;
    if initializer_record.parent != Some(variable_declaration.node)
        || !range_contains(declaration_record.range, initializer_record.range)
        || initializer_record.range.start < name_record.range.end
    {
        return Err(invariant(SourceArrowInvariant::InvalidInitializer(
            initializer,
        )));
    }
    let NodeData::ArrowFunction(initializer_data) = &initializer_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonArrowInitializer(
            initializer,
        )));
    };
    if initializer_record.kind != SyntaxKind::ArrowFunction || initializer_data.facts != 0 {
        return Err(invariant(SourceArrowInvariant::InvalidInitializer(
            initializer,
        )));
    }

    let variable_symbol = plan_top_level_variable(
        bound,
        store,
        variable_declaration,
        variable_name,
        &identifier.text,
        binding,
        exported,
    )
    .map_err(map_variable_error)?;
    let (callable, body) = plan_source_arrow_value(store, host, initializer, array_targets)?;
    if callable.owner_symbol == variable_symbol {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            initializer,
        )));
    }
    Ok(SourceArrowPlan {
        variable_declaration,
        variable_name,
        variable_symbol,
        callable,
        body,
    })
}

/// Proves an arrow callable and its body independently of its containing
/// expression, without publishing checker state.
pub(super) fn plan_source_arrow_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(SourceCallablePlan, SourceArrowBodyPlan), SourceArrowError> {
    let record = preflight_node(store, host, declaration)?;
    let NodeData::ArrowFunction(arrow) = &record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonArrowInitializer(
            declaration,
        )));
    };
    if record.kind != SyntaxKind::ArrowFunction || arrow.facts != 0 {
        return Err(invariant(SourceArrowInvariant::InvalidInitializer(
            declaration,
        )));
    }
    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(declaration)))?;
    let owner_symbol = bound
        .symbol(declaration)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(declaration)))?;
    let owner = store
        .symbol(owner_symbol)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(declaration)))?;
    if owner.flags() != SymbolFlags::FUNCTION
        || owner.name() != InternalSymbolName::Function.as_ref()
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }

    let callable = plan_source_callable(store, host, declaration, owner_symbol, array_targets)
        .map_err(map_callable_error)?;
    if callable.family != SourceCallableFamily::ArrowFunction
        || callable.declaration != declaration
        || callable.owner_symbol != owner_symbol
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }
    let body = plan_body(store, host, &callable)?;
    Ok((callable, body))
}

fn plan_body(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
) -> Result<SourceArrowBodyPlan, SourceArrowError> {
    let body = callable.body;
    let body_record = preflight_node(store, host, body)?;
    if body_record.parent != Some(callable.declaration.node) {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    }
    if body_record.kind != SyntaxKind::Block {
        if !is_concise_expression(body_record.kind) {
            return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
        }
        return Ok(SourceArrowBodyPlan::ConciseExpression { expression: body });
    }

    let NodeData::Block(block) = &body_record.data else {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    };
    if body_record.flags.0 != 0
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    }
    match block.statements.nodes.as_slice() {
        [] => Ok(SourceArrowBodyPlan::EmptyBlock { block: body }),
        [statement_id] => {
            let statement = NodeRef::new(body.arena, body.file, *statement_id);
            let statement_record = preflight_node(store, host, statement)?;
            if statement_record.parent != Some(body.node)
                || !range_contains(body_record.range, statement_record.range)
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
            }
            if matches!(statement_record.data, NodeData::ExpressionStatement(_)) {
                return if plan_async_arrow_await_statement(store, host, callable)?.is_some()
                    || plan_array_arrow_identifier_statement(store, host, callable)?.is_some()
                {
                    Ok(SourceArrowBodyPlan::EmptyBlock { block: body })
                } else {
                    Err(unsupported(SourceArrowUnsupported::ComplexBlock(body)))
                };
            }
            let NodeData::ReturnStatement(return_statement) = &statement_record.data else {
                return Err(unsupported(SourceArrowUnsupported::ComplexBlock(body)));
            };
            if statement_record.kind != SyntaxKind::ReturnStatement
                || statement_record.flags.0 != 0
                || return_statement.flow_node.is_some()
                || return_statement.facts != 0
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
            }
            let Some(expression_id) = return_statement.expression else {
                return plan_bare_return_body(store, host, callable, body, statement);
            };
            let expression = NodeRef::new(body.arena, body.file, expression_id);
            let expression_record = preflight_node(store, host, expression)?;
            if expression_record.parent != Some(statement.node)
                || !range_contains(statement_record.range, expression_record.range)
                || !is_concise_expression(expression_record.kind)
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(expression)));
            }
            Ok(SourceArrowBodyPlan::ReturnExpression {
                block: body,
                statement,
                expression,
            })
        }
        [_, _] if plan_async_arrow_await_statement(store, host, callable)?.is_some() => {
            Ok(SourceArrowBodyPlan::EmptyBlock { block: body })
        }
        _ => Err(unsupported(SourceArrowUnsupported::ComplexBlock(body))),
    }
}

fn plan_bare_return_body(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
    body: NodeRef,
    statement: NodeRef,
) -> Result<SourceArrowBodyPlan, SourceArrowError> {
    let bound = host.bound_file(callable.declaration).ok_or_else(|| {
        invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            callable.declaration,
        ))
    })?;
    let flow = bound.flow_graph();
    if bound.container(body) != Some(callable.declaration)
        || bound.block_scope_container(body) != Some(callable.declaration)
        || bound.container(statement) != Some(callable.declaration)
        || bound.block_scope_container(statement) != Some(callable.declaration)
        || bound.flow_container(statement) != Some(callable.declaration)
        || flow.container_is_complete(callable.declaration) != Some(true)
        || flow.container_start(callable.declaration).is_none()
        || flow.container_end(callable.declaration).is_some()
        || flow.container_return(callable.declaration).is_some()
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
    }

    let Some(mut annotation) = callable.return_type.type_node() else {
        return Ok(SourceArrowBodyPlan::EmptyBlock { block: body });
    };
    loop {
        let record = preflight_node(store, host, annotation)?;
        if matches!(
            record.kind,
            SyntaxKind::AnyKeyword | SyntaxKind::VoidKeyword | SyntaxKind::UndefinedKeyword
        ) {
            return Ok(SourceArrowBodyPlan::EmptyBlock { block: body });
        }
        let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
            return Err(unsupported(SourceArrowUnsupported::BareReturn(statement)));
        };
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(invariant(SourceArrowInvariant::InvalidBody(annotation)));
        }
        let inner = NodeRef::new(annotation.arena, annotation.file, parenthesized.type_);
        let inner_record = preflight_node(store, host, inner)?;
        if inner_record.parent != Some(annotation.node)
            || !range_contains(record.range, inner_record.range)
        {
            return Err(invariant(SourceArrowInvariant::InvalidBody(inner)));
        }
        annotation = inner;
    }
}

/// Authenticates an awaited call or the exact awaited-number/throw IIFE body.
#[allow(clippy::too_many_lines)] // Keep both async statement proofs complete and read-only.
pub(super) fn plan_async_arrow_await_statement(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
) -> Result<Option<SourceAsyncArrowAwaitStatement>, SourceArrowError> {
    if callable.family != SourceCallableFamily::ArrowFunction
        || !callable.is_async
        || !callable.parameters.is_empty()
        || !callable.type_parameters.is_empty()
        || !callable.return_type.is_inferred()
    {
        return Ok(None);
    }

    let declaration_record = preflight_node(store, host, callable.declaration)?;
    let block = callable.body;
    let block_record = preflight_node(store, host, block)?;
    let NodeData::Block(body) = &block_record.data else {
        return Ok(None);
    };
    if block_record.kind != SyntaxKind::Block
        || block_record.parent != Some(callable.declaration.node)
        || !range_contains(declaration_record.range, block_record.range)
        || block_record.flags.0 != 0
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(block)));
    }
    let (statement_id, throw_statement) = match body.statements.nodes.as_slice() {
        [statement] => (*statement, None),
        [statement, throw] => (*statement, Some(*throw)),
        _ => return Ok(None),
    };
    let statement = NodeRef::new(block.arena, block.file, statement_id);
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::ExpressionStatement(data) = &statement_record.data else {
        return Ok(None);
    };
    if statement_record.kind != SyntaxKind::ExpressionStatement
        || statement_record.parent != Some(block.node)
        || !range_contains(block_record.range, statement_record.range)
        || statement_record.flags.0 != 0
        || data.flow_node.is_some()
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
    }

    let await_expression = NodeRef::new(statement.arena, statement.file, data.expression);
    let await_record = preflight_node(store, host, await_expression)?;
    let NodeData::AwaitExpression(awaited) = &await_record.data else {
        return Ok(None);
    };
    if await_record.kind != SyntaxKind::AwaitExpression
        || await_record.parent != Some(statement.node)
        || !range_contains(statement_record.range, await_record.range)
        || await_record.flags.0 != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(
            await_expression,
        )));
    }

    let expression = NodeRef::new(
        await_expression.arena,
        await_expression.file,
        awaited.expression,
    );
    let expression_record = preflight_node(store, host, expression)?;
    if expression_record.parent != Some(await_expression.node)
        || !range_contains(await_record.range, expression_record.range)
        || expression_record.flags.0 != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(expression)));
    }

    let throw_expression = if let Some(throw_statement) = throw_statement {
        let NodeData::NumericLiteral(literal) = &expression_record.data else {
            return Ok(None);
        };
        if expression_record.kind != SyntaxKind::NumericLiteral || literal.token_flags.0 != 0 {
            return Ok(None);
        }
        let throw_statement = NodeRef::new(block.arena, block.file, throw_statement);
        let throw_record = preflight_node(store, host, throw_statement)?;
        let NodeData::ThrowStatement(thrown) = &throw_record.data else {
            return Ok(None);
        };
        if throw_record.kind != SyntaxKind::ThrowStatement
            || throw_record.flags.0 != 0
            || throw_record.parent != Some(block.node)
            || !range_contains(block_record.range, throw_record.range)
            || throw_record.range.start < statement_record.range.end
            || thrown.flow_node.is_some()
            || thrown.facts != 0
        {
            return Err(invariant(SourceArrowInvariant::InvalidBody(
                throw_statement,
            )));
        }
        let construction = NodeRef::new(block.arena, block.file, thrown.expression);
        let construction_record = preflight_node(store, host, construction)?;
        let NodeData::NewExpression(new_expression) = &construction_record.data else {
            return Ok(None);
        };
        let Some(arguments) = new_expression.arguments.as_ref() else {
            return Ok(None);
        };
        let name = NodeRef::new(block.arena, block.file, new_expression.expression);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(None);
        };
        if construction_record.kind != SyntaxKind::NewExpression
            || construction_record.flags.0 != 0
            || construction_record.parent != Some(throw_statement.node)
            || !range_contains(throw_record.range, construction_record.range)
            || !arguments.nodes.is_empty()
            || arguments.has_trailing_comma
            || new_expression.type_arguments.is_some()
            || new_expression.facts != 0
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(construction.node)
            || identifier.text != "Error"
            || identifier.flow_node.is_some()
            || !async_arrow_is_immediately_invoked(store, host, callable.declaration)?
            || !async_iife_error_constructor_is_global(store, host, name)?
        {
            return Ok(None);
        }
        Some(construction)
    } else if matches!(expression_record.data, NodeData::CallExpression(_))
        && expression_record.kind == SyntaxKind::CallExpression
    {
        None
    } else {
        return Ok(None);
    };

    Ok(Some(SourceAsyncArrowAwaitStatement {
        block,
        statement,
        await_expression,
        expression,
        throw_expression,
    }))
}

fn async_arrow_is_immediately_invoked(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<bool, SourceArrowError> {
    let declaration_record = preflight_node(store, host, declaration)?;
    let Some(parenthesized) = declaration_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(false);
    };
    let parenthesized_record = preflight_node(store, host, parenthesized)?;
    let NodeData::ParenthesizedExpression(parenthesized_expression) = &parenthesized_record.data
    else {
        return Ok(false);
    };
    let Some(call) = parenthesized_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return Ok(false);
    };
    let call_record = preflight_node(store, host, call)?;
    let NodeData::CallExpression(call_expression) = &call_record.data else {
        return Ok(false);
    };
    Ok(
        parenthesized_record.kind == SyntaxKind::ParenthesizedExpression
            && parenthesized_record.flags.0 == 0
            && parenthesized_expression.expression == declaration.node
            && range_contains(parenthesized_record.range, declaration_record.range)
            && call_record.kind == SyntaxKind::CallExpression
            && call_record.flags.0 == 0
            && call_expression.expression == parenthesized.node
            && call_expression.arguments.nodes.is_empty()
            && !call_expression.arguments.has_trailing_comma
            && call_expression.type_arguments.is_none()
            && call_expression.question_dot_token.is_none()
            && call_expression.symbol.is_none()
            && call_expression.facts == 0,
    )
}

fn async_iife_error_constructor_is_global(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: NodeRef,
) -> Result<bool, SourceArrowError> {
    let Some(global) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Error"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(global) else {
        return Ok(false);
    };
    let Some(declaration) = owner.value_declaration() else {
        return Ok(false);
    };
    if !owner.flags().intersects(SymbolFlags::VALUE)
        || host
            .bound_file(declaration)
            .and_then(ts_binder::BoundFile::source_facts)
            .is_none_or(|facts| !facts.is_default_library())
    {
        return Ok(false);
    }

    let (arena, bound) = host
        .source(name)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidBody(name)))?;
    let mut callback_host = host.name_resolver_host(store)?;
    let resolved =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(DeclaredTypeError::from)?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(name)),
                "Error",
                SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
                None,
                false,
                false,
            )
            .map_err(DeclaredTypeError::from)?;
    Ok(resolved.and_then(|symbol| store.get_merged_symbol(symbol)) == Some(global))
}

/// Returns one parameter-read statement from a single-element array arrow.
///
/// The existing empty-block body plan keeps this expression-free statement's
/// inferred return as `void`. Source execution can use these nodes to check and
/// cache the identifier without treating it as an arrow return value.
pub(super) fn plan_array_arrow_identifier_statement(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
) -> Result<Option<(NodeRef, NodeRef, NodeRef)>, SourceArrowError> {
    let [parameter] = callable.parameters.as_slice() else {
        return Ok(None);
    };
    if callable.family != SourceCallableFamily::ArrowFunction
        || !callable.return_type.is_inferred()
        || parameter.optional
        || parameter.rest
        || parameter.initializer.is_some()
    {
        return Ok(None);
    }

    let declaration_record = preflight_node(store, host, callable.declaration)?;
    let Some(array_id) = declaration_record.parent else {
        return Ok(None);
    };
    let array = NodeRef::new(
        callable.declaration.arena,
        callable.declaration.file,
        array_id,
    );
    let array_record = preflight_node(store, host, array)?;
    let NodeData::ArrayLiteralExpression(elements) = &array_record.data else {
        return Ok(None);
    };
    if array_record.kind != SyntaxKind::ArrayLiteralExpression
        || !range_contains(array_record.range, declaration_record.range)
    {
        return Err(invariant(SourceArrowInvariant::InvalidInitializer(array)));
    }
    if elements.elements.nodes.as_slice() != [callable.declaration.node] {
        return Ok(None);
    }

    let block = callable.body;
    let block_record = preflight_node(store, host, block)?;
    let NodeData::Block(body) = &block_record.data else {
        return Ok(None);
    };
    if block_record.kind != SyntaxKind::Block
        || block_record.parent != Some(callable.declaration.node)
        || !range_contains(declaration_record.range, block_record.range)
        || block_record.flags.0 != 0
        || body.flow_node.is_some()
        || body.next_container.is_some()
        || body.statements.has_trailing_comma
        || body.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(block)));
    }
    let [statement_id] = body.statements.nodes.as_slice() else {
        return Ok(None);
    };
    let statement = NodeRef::new(block.arena, block.file, *statement_id);
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::ExpressionStatement(data) = &statement_record.data else {
        return Ok(None);
    };
    if statement_record.kind != SyntaxKind::ExpressionStatement
        || statement_record.parent != Some(block.node)
        || !range_contains(block_record.range, statement_record.range)
        || statement_record.flags.0 != 0
        || data.flow_node.is_some()
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
    }

    let expression = NodeRef::new(statement.arena, statement.file, data.expression);
    let expression_record = preflight_node(store, host, expression)?;
    let NodeData::Identifier(identifier) = &expression_record.data else {
        return Ok(None);
    };
    if expression_record.kind != SyntaxKind::Identifier
        || expression_record.parent != Some(statement.node)
        || !range_contains(statement_record.range, expression_record.range)
        || expression_record.flags.0 != 0
        || identifier.flow_node.is_some()
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(expression)));
    }
    let symbol = store
        .symbol(parameter.symbol)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(expression)))?;
    if symbol.name().as_bytes() != identifier.text.as_bytes() {
        return Ok(None);
    }

    Ok(Some((block, statement, expression)))
}

fn is_concise_expression(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Identifier
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::RegularExpressionLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::ObjectLiteralExpression
            | SyntaxKind::PropertyAccessExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::CallExpression
            | SyntaxKind::NewExpression
            | SyntaxKind::TaggedTemplateExpression
            | SyntaxKind::TypeAssertionExpression
            | SyntaxKind::ParenthesizedExpression
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::DeleteExpression
            | SyntaxKind::TypeOfExpression
            | SyntaxKind::VoidExpression
            | SyntaxKind::AwaitExpression
            | SyntaxKind::PrefixUnaryExpression
            | SyntaxKind::PostfixUnaryExpression
            | SyntaxKind::BinaryExpression
            | SyntaxKind::ConditionalExpression
            | SyntaxKind::TemplateExpression
            | SyntaxKind::YieldExpression
            | SyntaxKind::ClassExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::NonNullExpression
            | SyntaxKind::MetaProperty
            | SyntaxKind::SatisfiesExpression
            | SyntaxKind::JsxElement
            | SyntaxKind::JsxSelfClosingElement
            | SyntaxKind::JsxFragment
    )
}

fn range_contains(parent: ts_core::TextRange, child: ts_core::TextRange) -> bool {
    child.start >= parent.start && child.end <= parent.end
}

const fn arrow_binding_kind(flags: u32) -> Option<VariableBindingKind> {
    match flags {
        0 => Some(VariableBindingKind::Var),
        NODE_FLAG_LET => Some(VariableBindingKind::Let),
        NODE_FLAG_CONST => Some(VariableBindingKind::Const),
        _ => None,
    }
}

fn valid_arrow_export_modifier(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    statement: NodeRef,
    statement_record: &ts_ast::Node,
    list_record: &ts_ast::Node,
    modifiers: &ts_ast::ModifierList,
) -> Result<bool, DeclaredTypeError> {
    let [modifier_id] = modifiers.list.nodes.as_slice() else {
        return Ok(false);
    };
    let modifier = NodeRef::new(statement.arena, statement.file, *modifier_id);
    let record = preflight_node(store, host, modifier)?;
    Ok(modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && modifiers.list.range.start == statement_record.range.start
        && modifiers.list.range.end < list_record.range.start
        && record.kind == SyntaxKind::ExportKeyword
        && matches!(record.data, NodeData::Token(_))
        && record.flags.0 == 0
        && record.parent == Some(statement.node)
        && record.range.start == statement_record.range.start
        && record.range.end < modifiers.list.range.end)
}

fn preflight_contextual_child<'a>(
    store: &CanonicalTypeMapperStore,
    host: &'a DeclaredTypeHost<'_>,
    parent: NodeRef,
    child: NodeRef,
    invalid: SourceContextualArrowInvariant,
) -> Result<&'a ts_ast::Node, SourceContextualArrowError> {
    let record = preflight_node(store, host, child)?;
    if child.arena != parent.arena
        || child.file != parent.file
        || record.parent != Some(parent.node)
    {
        return Err(contextual_invariant(invalid));
    }
    Ok(record)
}

fn map_contextual_variable_error(error: VariablePlanError) -> SourceContextualArrowError {
    match error {
        VariablePlanError::Unsupported(reason) => {
            contextual_unsupported(SourceContextualArrowUnsupported::Variable(reason))
        }
        VariablePlanError::Invariant(reason) => {
            contextual_invariant(SourceContextualArrowInvariant::Variable(reason))
        }
        VariablePlanError::DeclaredType(error) => SourceContextualArrowError::DeclaredType(error),
    }
}

fn map_variable_error(error: VariablePlanError) -> SourceArrowError {
    match error {
        VariablePlanError::Unsupported(reason) => {
            unsupported(SourceArrowUnsupported::Variable(reason))
        }
        VariablePlanError::Invariant(reason) => invariant(SourceArrowInvariant::Variable(reason)),
        VariablePlanError::DeclaredType(error) => SourceArrowError::DeclaredType(error),
    }
}

fn map_callable_error(error: SourceCallableError) -> SourceArrowError {
    match error {
        SourceCallableError::Unsupported(reason) => {
            unsupported(SourceArrowUnsupported::Callable(reason))
        }
        SourceCallableError::Invariant(reason) => invariant(SourceArrowInvariant::Callable(reason)),
        SourceCallableError::DeclaredType(error) => SourceArrowError::DeclaredType(error),
        SourceCallableError::LiteralCache(error) => SourceArrowError::LiteralCache(error),
    }
}

const fn contextual_unsupported(
    reason: SourceContextualArrowUnsupported,
) -> SourceContextualArrowError {
    SourceContextualArrowError::Unsupported(reason)
}

const fn contextual_invariant(
    reason: SourceContextualArrowInvariant,
) -> SourceContextualArrowError {
    SourceContextualArrowError::Invariant(reason)
}

const fn unsupported(reason: SourceArrowUnsupported) -> SourceArrowError {
    SourceArrowError::Unsupported(reason)
}

const fn invariant(reason: SourceArrowInvariant) -> SourceArrowError {
    SourceArrowError::Invariant(reason)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions,
        jsdoc::plan_javascript_source_jsdoc,
        production::GlobalMergeCompletion,
        source_callables::{SourceCallableState, source_callable_state},
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl Fixture {
        fn new(source: &str) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            Self::from_parsed(parsed)
        }

        fn from_parsed(parsed: ParseResult) -> Self {
            Self::from_parsed_with_language(
                parsed,
                CanonicalSourceLanguage::TypeScript,
                CanonicalModuleState::External,
            )
        }

        fn javascript(source: &str) -> Self {
            let parsed = parse_javascript_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            Self::from_parsed_with_language(
                parsed,
                CanonicalSourceLanguage::JavaScript,
                CanonicalModuleState::Script,
            )
        }

        fn from_parsed_with_language(
            parsed: ParseResult,
            language: CanonicalSourceLanguage,
            module_state: CanonicalModuleState,
        ) -> Self {
            let file = FileId::new(913);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(if language == CanonicalSourceLanguage::JavaScript {
                            "\"/project/source_arrows.js\""
                        } else {
                            "\"/project/source_arrows.ts\""
                        }),
                        language,
                        false,
                        module_state,
                    ),
                )
                .unwrap();
            if language == CanonicalSourceLanguage::JavaScript {
                binder
                    .bind_javascript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            } else {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
            let bound = files.remove(&file).unwrap();
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn host(&self) -> DeclaredTypeHost<'_> {
            DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap()
        }

        fn declarations(&self) -> Vec<NodeRef> {
            variable_declarations(&self.parsed, self.file)
        }

        fn plan(&self, index: usize) -> Result<SourceArrowPlan, SourceArrowError> {
            let host = self.host();
            plan_source_arrow(&self.store, &host, self.declarations()[index], None)
        }

        fn contextual_plan(
            &self,
            index: usize,
        ) -> Result<SourceContextualArrowPlan, SourceContextualArrowError> {
            let host = self.host();
            plan_contextual_source_arrow(&self.store, &host, self.declarations()[index], None)
        }
    }

    fn variable_declarations(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source file")
        };
        let mut declarations = Vec::new();
        for statement_id in &source.statements.nodes {
            let statement = parsed.arena.get(*statement_id).unwrap();
            let NodeData::VariableStatement(statement) = &statement.data else {
                continue;
            };
            let list = parsed.arena.get(statement.declaration_list).unwrap();
            let NodeData::VariableDeclarationList(list) = &list.data else {
                panic!("expected variable declaration list")
            };
            declarations.extend(
                list.declarations
                    .nodes
                    .iter()
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node)),
            );
        }
        declarations
    }

    #[test]
    fn direct_arrow_retains_distinct_variable_and_anonymous_callable_identity() {
        let fixture = Fixture::new("const f = (x: number): string => \"ok\";");
        let plan = fixture.plan(0).unwrap();

        assert_ne!(plan.variable_symbol, plan.callable.owner_symbol);
        assert_eq!(
            fixture.bound.symbol(plan.variable_declaration),
            Some(plan.variable_symbol)
        );
        assert_eq!(
            fixture.bound.symbol(plan.callable.declaration),
            Some(plan.callable.owner_symbol)
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.variable_symbol)
                .unwrap()
                .name()
                .as_utf8(),
            Some("f")
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.callable.owner_symbol)
                .unwrap()
                .name(),
            InternalSymbolName::Function.as_ref()
        );
        assert_eq!(plan.callable.family, SourceCallableFamily::ArrowFunction);
        assert_eq!(plan.callable.parameters.len(), 1);
        assert_eq!(plan.callable.min_argument_count, 1);
        assert!(!plan.callable.parameters[0].optional);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.callable.return_type.type_node().unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::StringKeyword
        );
        assert!(matches!(
            plan.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::StringLiteral
        ));
        assert_eq!(
            source_callable_state(&fixture.store, &plan.callable, true).unwrap(),
            SourceCallableState::Cold
        );
    }

    #[test]
    fn nested_arrow_values_reuse_exact_callable_and_body_planning() {
        for source in [
            "const container = { run: (value: string): string => value };",
            "const callbacks = [(value: number): number => value];",
            "const result = invoke((value: string): string => value);",
            "const inferred = invoke((value: number) => value);",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = fixture.host();

            let (callable, body) =
                plan_source_arrow_value(&fixture.store, &host, declaration, None).unwrap();
            assert_eq!(callable.declaration, declaration);
            assert_eq!(callable.owner_symbol, owner);
            assert_eq!(callable.parameters.len(), 1);
            assert!(matches!(
                body,
                SourceArrowBodyPlan::ConciseExpression { expression }
                    if fixture.parsed.arena.get(expression.node).unwrap().kind
                        == SyntaxKind::Identifier
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn async_arrow_await_statement_retains_authenticated_call_nodes() {
        for source in [
            "const value = async () => { await invoke(); };",
            "const value = { f: async () => { await dependency.f(); } };",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let host = fixture.host();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let (callable, body) =
                plan_source_arrow_value(&fixture.store, &host, declaration, None).unwrap();
            let awaited = plan_async_arrow_await_statement(&fixture.store, &host, &callable)
                .unwrap()
                .unwrap();

            assert!(callable.is_async);
            assert_eq!(
                body,
                SourceArrowBodyPlan::EmptyBlock {
                    block: awaited.block
                }
            );
            assert!(awaited.throw_expression.is_none());
            assert_eq!(
                fixture
                    .parsed
                    .arena
                    .get(awaited.await_expression.node)
                    .unwrap()
                    .kind,
                SyntaxKind::AwaitExpression,
            );
            assert_eq!(
                fixture
                    .parsed
                    .arena
                    .get(awaited.expression.node)
                    .unwrap()
                    .kind,
                SyntaxKind::CallExpression,
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn async_arrow_await_statement_rejects_unauthenticated_blocks() {
        for source in [
            "const value = async () => { invoke(); };",
            "const value = async () => { await value; };",
            "const value = async () => { await invoke(); await invoke(); };",
            "const value = async () => { await 10; throw new Error(); };",
        ] {
            let fixture = Fixture::new(source);
            assert!(
                matches!(
                    fixture.plan(0),
                    Err(SourceArrowError::Unsupported(
                        SourceArrowUnsupported::ComplexBlock(_)
                    ))
                ),
                "{source}",
            );
        }
    }

    #[test]
    fn bare_return_arrows_preserve_void_body_identity_and_remain_read_only() {
        for (source, inferred) in [
            ("const value = () => { return; };", true),
            ("const value = (input: number) => { return; };", true),
            (
                "const result = invoke((input: number) => { return; });",
                true,
            ),
            ("const value = (): void => { return; };", false),
            ("const value = (): undefined => { return; };", false),
            ("const value = (): any => { return; };", false),
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = fixture.host();

            let (callable, body) =
                plan_source_arrow_value(&fixture.store, &host, declaration, None).unwrap();
            let SourceArrowBodyPlan::EmptyBlock { block } = body else {
                panic!("bare return must preserve the existing void-body plan: {source}")
            };
            let NodeData::Block(data) = &fixture.parsed.arena.get(block.node).unwrap().data else {
                panic!("arrow body must retain its source block")
            };
            let [statement_id] = data.statements.nodes.as_slice() else {
                panic!("bare-return body must retain exactly one statement")
            };
            let statement = NodeRef::new(block.arena, block.file, *statement_id);

            assert_eq!(callable.declaration, declaration);
            assert_eq!(callable.owner_symbol, owner);
            assert_eq!(callable.return_type.is_inferred(), inferred);
            assert_eq!(block, callable.body);
            assert_eq!(fixture.bound.container(block), Some(declaration));
            assert_eq!(fixture.bound.container(statement), Some(declaration));
            assert_eq!(fixture.bound.flow_container(statement), Some(declaration));
            assert_eq!(
                fixture
                    .bound
                    .flow_graph()
                    .container_is_complete(declaration),
                Some(true),
            );
            assert!(
                fixture
                    .bound
                    .flow_graph()
                    .container_start(declaration)
                    .is_some()
            );
            assert!(
                fixture
                    .bound
                    .flow_graph()
                    .container_end(declaration)
                    .is_none()
            );
            assert_eq!(
                plan_source_arrow_value(&fixture.store, &host, declaration, None),
                Ok((callable, body)),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn bare_return_body_rejects_nonvoid_annotations_and_extra_statements() {
        for (source, bare_return) in [
            ("const value = (): number => { return; };", true),
            ("const value = (): string => { return; };", true),
            ("const value = () => { return; return; };", false),
            ("const value = () => { return; 1; };", false),
        ] {
            let fixture = Fixture::new(source);
            assert!(
                matches!(
                    (fixture.plan(0), bare_return),
                    (
                        Err(SourceArrowError::Unsupported(
                            SourceArrowUnsupported::BareReturn(_)
                        )),
                        true,
                    ) | (
                        Err(SourceArrowError::Unsupported(
                            SourceArrowUnsupported::ComplexBlock(_)
                        )),
                        false,
                    )
                ),
                "{source}",
            );
        }

        let returned = Fixture::new("const value = (): number => { return 1; };");
        assert!(matches!(
            returned.plan(0).unwrap().body,
            SourceArrowBodyPlan::ReturnExpression { .. }
        ));
    }

    #[test]
    fn malformed_bare_return_is_rejected_before_callable_publication() {
        let mut parsed = parse_source_file("const value = () => { return; };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let statement_id = parsed
            .arena
            .iter()
            .find_map(|(node, record)| (record.kind == SyntaxKind::ReturnStatement).then_some(node))
            .unwrap();
        let NodeData::ReturnStatement(statement) = &mut parsed
            .arena
            .get_mut(statement_id)
            .expect("bare return remains in its parsed arena")
            .data
        else {
            unreachable!()
        };
        statement.facts = 1;
        let fixture = Fixture::from_parsed(parsed);
        let declaration = fixture.declarations()[0];
        let NodeData::VariableDeclaration(variable) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let arrow = NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            variable.initializer.unwrap(),
        );
        let statement = NodeRef::new(fixture.parsed.arena.id(), fixture.file, statement_id);
        let owner = fixture.bound.symbol(arrow).unwrap();

        assert_eq!(
            fixture.plan(0),
            Err(SourceArrowError::Invariant(
                SourceArrowInvariant::InvalidBody(statement,)
            )),
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );
    }

    #[test]
    fn array_arrow_identifier_statement_preserves_void_body_and_exact_nodes() {
        for source in [
            "const callbacks = [(value: number) => { value; }];",
            "const result = invoke([(value: string) => { value; },]);",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = fixture.host();

            let (callable, body) =
                plan_source_arrow_value(&fixture.store, &host, declaration, None).unwrap();
            let (block, statement, expression) =
                plan_array_arrow_identifier_statement(&fixture.store, &host, &callable)
                    .unwrap()
                    .unwrap();

            assert_eq!(callable.owner_symbol, owner);
            assert!(callable.return_type.is_inferred());
            assert_eq!(body, SourceArrowBodyPlan::EmptyBlock { block });
            assert_eq!(
                fixture.parsed.arena.get(block.node).unwrap().kind,
                SyntaxKind::Block
            );
            assert_eq!(
                fixture.parsed.arena.get(statement.node).unwrap().kind,
                SyntaxKind::ExpressionStatement,
            );
            assert_eq!(
                fixture.parsed.arena.get(expression.node).unwrap().kind,
                SyntaxKind::Identifier,
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn array_arrow_identifier_statements_reject_other_blocks_without_publication() {
        for source in [
            "const direct = (value: number) => { value; };",
            "const callbacks = [(value: number) => { other; }];",
            "const callbacks = [(value: number) => { 1; }];",
            "const callbacks = [(first: number, second: number) => { first; }];",
            "const callbacks = [(value: number): void => { value; }];",
            "const callbacks = [(value: number) => { value; value; }];",
            "const callbacks = [(value: number) => { value; }, 1];",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = fixture.host();

            assert!(
                matches!(
                    plan_source_arrow_value(&fixture.store, &host, declaration, None),
                    Err(SourceArrowError::Unsupported(
                        SourceArrowUnsupported::ComplexBlock(_)
                    ))
                ),
                "{source}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn nested_arrow_arguments_preserve_lexical_this_expression_identity() {
        for (source, expected_kind, returned) in [
            (
                "const result = invoke((value: string): unknown => this);",
                SyntaxKind::ThisKeyword,
                false,
            ),
            (
                "const result = invoke((value: string): unknown => this.value);",
                SyntaxKind::PropertyAccessExpression,
                false,
            ),
            (
                "const result = invoke((value: string): unknown => { return this.value; });",
                SyntaxKind::PropertyAccessExpression,
                true,
            ),
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let host = fixture.host();

            let (callable, body) =
                plan_source_arrow_value(&fixture.store, &host, declaration, None).unwrap();
            assert_eq!(callable.declaration, declaration);
            assert_eq!(callable.owner_symbol, owner);
            assert_eq!(callable.parameters.len(), 1);

            let ((SourceArrowBodyPlan::ConciseExpression { expression }, false)
            | (SourceArrowBodyPlan::ReturnExpression { expression, .. }, true)) = (body, returned)
            else {
                panic!("unexpected lexical this arrow body")
            };
            assert_eq!(
                fixture.parsed.arena.get(expression.node).unwrap().kind,
                expected_kind,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn jsx_arrow_bodies_preserve_concise_and_return_expression_identity() {
        let parsed = ts_parser::parse_jsx_source_file(concat!(
            "const concise = (): unknown => <div />; ",
            "const returned = (): unknown => { return <span />; };",
            "const wrapped = (): unknown => (<section />); ",
            "const wrapped_return = (): unknown => { return (<article />); };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let fixture = Fixture::from_parsed(parsed);

        let concise = fixture.plan(0).unwrap();
        assert!(matches!(
            concise.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::JsxSelfClosingElement
        ));

        let returned = fixture.plan(1).unwrap();
        assert!(matches!(
            returned.body,
            SourceArrowBodyPlan::ReturnExpression { expression, .. }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::JsxSelfClosingElement
        ));

        let wrapped = fixture.plan(2).unwrap();
        assert!(matches!(
            wrapped.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::ParenthesizedExpression
        ));

        let wrapped_return = fixture.plan(3).unwrap();
        assert!(matches!(
            wrapped_return.body,
            SourceArrowBodyPlan::ReturnExpression { expression, .. }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::ParenthesizedExpression
        ));
    }

    #[test]
    fn direct_arrows_preserve_var_let_const_and_exported_variable_ownership() {
        let fixture = Fixture::new(concat!(
            "var first = (): string => \"first\"; ",
            "let second = (): number => 2; ",
            "const third = (): boolean => true; ",
            "export const fourth = (): string => \"fourth\";",
        ));

        for (index, expected_flags, exported) in [
            (0, SymbolFlags::FUNCTION_SCOPED_VARIABLE, false),
            (1, SymbolFlags::BLOCK_SCOPED_VARIABLE, false),
            (2, SymbolFlags::BLOCK_SCOPED_VARIABLE, false),
            (3, SymbolFlags::BLOCK_SCOPED_VARIABLE, true),
        ] {
            let plan = fixture.plan(index).unwrap();
            assert_eq!(
                fixture.store.symbol(plan.variable_symbol).unwrap().flags(),
                expected_flags,
            );
            assert_eq!(
                fixture
                    .bound
                    .local_symbol(plan.variable_declaration)
                    .is_some(),
                exported,
            );
            assert_ne!(plan.variable_symbol, plan.callable.owner_symbol);
        }
    }

    #[test]
    fn contextual_arrows_preserve_var_let_and_exported_variable_ownership() {
        let fixture = Fixture::new(concat!(
            "var first: () => void = () => {}; ",
            "let second: () => void = () => {}; ",
            "export const third: () => void = () => {};",
        ));

        for (index, expected_flags, exported) in [
            (0, SymbolFlags::FUNCTION_SCOPED_VARIABLE, false),
            (1, SymbolFlags::BLOCK_SCOPED_VARIABLE, false),
            (2, SymbolFlags::BLOCK_SCOPED_VARIABLE, true),
        ] {
            let plan = fixture.contextual_plan(index).unwrap();
            assert_eq!(
                fixture.store.symbol(plan.variable_symbol).unwrap().flags(),
                expected_flags,
            );
            assert_eq!(
                fixture
                    .bound
                    .local_symbol(plan.variable_declaration)
                    .is_some(),
                exported,
            );
            assert_ne!(plan.variable_symbol, plan.owner_symbol);
        }
    }

    #[test]
    fn contextual_arrows_preserve_concise_and_single_return_body_provenance() {
        for (index, source) in [
            "const value: (input: number) => number = input => input;",
            "const value: (input: number) => number = input => { return input; };",
            concat!(
                "type Result = { value: number }; ",
                "const value: (input: number) => Result = input => ({ value: input });",
            ),
            concat!(
                "const value: (input: number) => { value: number } = ",
                "input => ({ value: input });",
            ),
            "const value: () => 'ready' = () => 'ready';",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = Fixture::new(source);
            let cold = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let plan = fixture.contextual_plan(0).unwrap();

            match (index, plan.return_origin) {
                (
                    1,
                    SourceContextualReturnOrigin::InferredReturnExpression {
                        block,
                        statement,
                        expression,
                    },
                ) => {
                    assert_eq!(
                        fixture.parsed.arena.get(block.node).unwrap().kind,
                        SyntaxKind::Block,
                    );
                    assert_eq!(
                        fixture.parsed.arena.get(statement.node).unwrap().kind,
                        SyntaxKind::ReturnStatement,
                    );
                    assert_eq!(
                        fixture.parsed.arena.get(expression.node).unwrap().kind,
                        SyntaxKind::Identifier,
                    );
                }
                (_, SourceContextualReturnOrigin::InferredConciseExpression { expression }) => {
                    assert_eq!(
                        fixture.parsed.arena.get(expression.node).unwrap().parent,
                        Some(plan.declaration.node),
                    );
                }
                _ => panic!("unexpected contextual return origin for {source}"),
            }

            assert_ne!(plan.owner_symbol, plan.variable_symbol);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold,
            );
        }
    }

    #[test]
    fn jsdoc_callback_arrows_keep_source_ownership_without_a_written_type_node() {
        let fixture = Fixture::javascript(concat!(
            "/** @callback NS.MyCallback\n",
            " * @param {string} name\n",
            " * @returns {void}\n",
            " */\n",
            "/** @type {NS.MyCallback} */\n",
            "const f = (name) => {};",
        ));
        let declaration = fixture.declarations()[0];
        let jsdoc =
            plan_javascript_source_jsdoc(&fixture.parsed.arena, fixture.bound.source_file())
                .unwrap();
        let hosted = jsdoc.declaration(declaration).unwrap();
        assert_eq!(
            hosted.type_().unwrap().resolved_alias_name(),
            Some("NS.MyCallback")
        );
        let callback = hosted.type_().unwrap().resolved_callback().unwrap();
        assert_eq!(callback.parameters().len(), 1);

        let host = fixture.host();
        assert!(matches!(
            plan_contextual_source_arrow(&fixture.store, &host, declaration, None),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::MissingVariableAnnotation(node),
            )) if node == declaration
        ));
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let planned =
            plan_jsdoc_contextual_source_arrow(&fixture.store, &host, declaration, hosted, None)
                .unwrap();
        assert_eq!(planned.variable_declaration, declaration);
        assert_eq!(
            fixture.bound.symbol(planned.variable_declaration),
            Some(planned.variable_symbol)
        );
        assert_eq!(
            fixture.bound.symbol(planned.callable.declaration),
            Some(planned.callable.owner_symbol)
        );
        assert_ne!(planned.variable_symbol, planned.callable.owner_symbol);
        assert_eq!(
            planned.callable.flags,
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
        );
        assert_eq!(planned.callable.min_argument_count, 1);
        assert_eq!(planned.callable.parameters.len(), 1);
        assert!(planned.callable.parameters[0].is_implicit_any());
        assert!(
            planned.callable.parameters[0]
                .explicit_type_node()
                .is_none()
        );
        assert!(matches!(
            planned.body,
            SourceArrowBodyPlan::EmptyBlock { .. }
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            cold
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(planned.callable.owner_symbol)
                .is_none()
        );
    }

    #[test]
    fn jsdoc_arrow_body_casts_preserve_the_existing_callable_and_variable_owners() {
        let fixture = Fixture::javascript(concat!(
            "/** @param {string} value */\n",
            "const read = value => /** @type {number} */ (value);",
        ));
        let declaration = fixture.declarations()[0];
        let host = fixture.host();
        let cold = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let planned = plan_source_arrow(&fixture.store, &host, declaration, None).unwrap();
        let SourceArrowBodyPlan::ConciseExpression { expression } = planned.body else {
            panic!("expected the inline JSDoc cast to remain a concise arrow body")
        };
        let comments =
            plan_javascript_source_jsdoc(&fixture.parsed.arena, fixture.bound.source_file())
                .unwrap();
        assert_eq!(
            comments
                .callable_declaration(&fixture.parsed.arena, planned.callable.declaration)
                .map(super::super::jsdoc::PlannedJavaScriptDeclaration::node),
            Some(declaration),
        );
        assert_eq!(
            comments.expression_type(expression).unwrap().type_(),
            &super::super::jsdoc::JsDocType::Intrinsic(
                super::super::jsdoc::JsDocIntrinsicType::Number,
            ),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            cold,
        );
    }

    #[test]
    fn jsdoc_callback_arrows_reject_missing_context_and_mismatched_parameters() {
        for source in [
            "/** @type {number} */\nconst f = (name) => {};",
            concat!(
                "/** @callback Handler\n",
                " * @param {string} first\n",
                " * @param {string} second\n",
                " * @returns {void}\n",
                " */\n",
                "/** @type {Handler} */\n",
                "const f = (name) => {};",
            ),
        ] {
            let fixture = Fixture::javascript(source);
            let declaration = fixture.declarations()[0];
            let jsdoc =
                plan_javascript_source_jsdoc(&fixture.parsed.arena, fixture.bound.source_file())
                    .unwrap();
            let hosted = jsdoc.declaration(declaration).unwrap();
            let host = fixture.host();
            let cold = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_jsdoc_contextual_source_arrow(
                    &fixture.store,
                    &host,
                    declaration,
                    hosted,
                    None,
                ),
                Err(SourceArrowError::Unsupported(SourceArrowUnsupported::JsDocContext(node)))
                    if node == declaration
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold
            );
        }
    }

    #[test]
    fn named_contextual_callable_aliases_retain_exact_signature_shapes_without_writes() {
        for source in [
            "type Callback = () => void; export const value: Callback = () => {};",
            concat!(
                "type Callback = (input: string) => void; ",
                "export const value: Callback = (input) => {};",
            ),
            concat!(
                "type Callback = () => void; type Alias = Callback; ",
                "export const value: Alias = () => {};",
            ),
            concat!(
                "type Page = (() => void) & { getLayout?: () => void }; ",
                "export const value: Page = () => {};",
            ),
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.declarations()[0];
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected contextual variable declaration")
            };
            let arrow = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let owner = fixture.bound.symbol(arrow).unwrap();
            let cold = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let plan = fixture.contextual_plan(0).unwrap();
            assert_eq!(plan.contextual_type.type_node.node, variable.type_.unwrap());
            assert_eq!(plan.contextual_signature_shape.call_signature_count, 1);
            assert_eq!(
                plan.contextual_signature_shape.parameter_count,
                plan.parameters.len(),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn declared_contextual_call_signatures_preserve_type_literal_and_interface_identity() {
        for source in [
            concat!(
                "const callback: { (input: string): void } = ",
                "(input) => {};",
            ),
            concat!(
                "type Callback = { (input: string): void; label?: string }; ",
                "export const callback: Callback = (input) => {};",
            ),
            concat!(
                "interface Callback { (input: string): void; label?: string } ",
                "export const callback: Callback = (input) => {};",
            ),
        ] {
            let fixture = Fixture::new(source);
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let plan = fixture.contextual_plan(0).unwrap();
            assert_eq!(plan.contextual_signature_shape.call_signature_count, 1);
            assert_eq!(plan.contextual_signature_shape.parameter_count, 1);
            assert_eq!(plan.parameters.len(), 1);
            assert_eq!(
                plan.parameters[0].request,
                SourceContextualParameterRequest::Position { index: 0 },
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn generic_named_contextual_callable_targets_remain_atomic_typed_boundaries() {
        for source in [
            concat!(
                "type Callback<Value> = (value: Value) => void; ",
                "export const value: Callback<string> = () => {};",
            ),
            concat!(
                "type Page<Props = unknown> = (() => void) & { getLayout?: () => void }; ",
                "export const value: Page = () => {};",
            ),
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.declarations()[0];
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected contextual variable declaration")
            };
            let annotation = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.type_.unwrap(),
            );
            let arrow = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let owner = fixture.bound.symbol(arrow).unwrap();
            let cold = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                fixture.contextual_plan(0),
                Err(SourceContextualArrowError::Unsupported(
                    SourceContextualArrowUnsupported::ContextualTargetSyntax(annotation),
                )),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                cold,
            );
            assert!(
                fixture
                    .store
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
        }
    }

    #[test]
    fn contextual_arrow_retains_target_request_and_distinct_ownership() {
        let fixture = Fixture::new("const f: () => void = (a?, ...b) => {};");
        let plan = fixture.contextual_plan(0).unwrap();

        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.contextual_type.type_node.node)
                .unwrap()
                .kind,
            SyntaxKind::FunctionType
        );
        assert_eq!(
            plan.contextual_type.requirement,
            SourceContextualSignatureRequirement::SingleNonGenericCallSignature
        );
        assert_ne!(plan.variable_symbol, plan.owner_symbol);
        assert_eq!(
            fixture.bound.symbol(plan.variable_declaration),
            Some(plan.variable_symbol)
        );
        assert_eq!(
            fixture.bound.symbol(plan.declaration),
            Some(plan.owner_symbol)
        );
        assert_eq!(plan.parameters.len(), 2);
        assert!(plan.parameters[0].optional);
        assert!(!plan.parameters[0].rest);
        assert_eq!(
            plan.parameters[0].request,
            SourceContextualParameterRequest::Position { index: 0 }
        );
        assert!(!plan.parameters[1].optional);
        assert!(plan.parameters[1].rest);
        assert_eq!(
            plan.parameters[1].request,
            SourceContextualParameterRequest::RestTail { start: 1 }
        );
        assert_eq!(plan.leading_required_parameter_count, 0);
        assert_eq!(plan.min_argument_count, 0);
        assert!(plan.flags.contains(SignatureFlags::HAS_REST_PARAMETER));
        assert!(matches!(
            plan.return_origin,
            SourceContextualReturnOrigin::InferredEmptyBody { block }
                if fixture.parsed.arena.get(block.node).unwrap().kind == SyntaxKind::Block
        ));
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(plan.owner_symbol)
                .is_none()
        );
    }

    #[test]
    fn contextual_arrow_records_implicit_any_and_exhausted_rest_origins() {
        let fixture = Fixture::new("const f: () => void = (a?, ...b) => {};");
        let plan = fixture.contextual_plan(0).unwrap();
        let resolved = resolve_contextual_arrow_parameter_origins(
            &plan,
            SourceContextualSignatureShape {
                call_signature_count: 1,
                type_parameter_count: 0,
                parameter_count: 0,
                has_effective_rest: false,
            },
        )
        .unwrap();

        assert_eq!(resolved.parameters.len(), 2);
        assert_eq!(
            resolved.parameters[0].origin,
            SourceContextualParameterOrigin::ImplicitAny {
                missing_position: 0
            }
        );
        assert_eq!(
            resolved.parameters[1].origin,
            SourceContextualParameterOrigin::ContextualEmptyRestTail { start: 1 }
        );
        assert!(resolved.implicit_any_diagnostic_nodes(false).is_empty());
        assert_eq!(
            resolved.implicit_any_diagnostic_nodes(true),
            vec![plan.parameters[0].declaration]
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(plan.owner_symbol)
                .is_none()
        );
    }

    #[test]
    fn contextual_position_origin_is_not_implicit_any() {
        let fixture = Fixture::new("const f: (value?: any) => void = (value) => {};");
        let plan = fixture.contextual_plan(0).unwrap();
        let resolved = resolve_contextual_arrow_parameter_origins(
            &plan,
            SourceContextualSignatureShape {
                call_signature_count: 1,
                type_parameter_count: 0,
                parameter_count: 1,
                has_effective_rest: false,
            },
        )
        .unwrap();

        assert_eq!(
            resolved.parameters[0].origin,
            SourceContextualParameterOrigin::ContextualPosition { index: 0 }
        );
        assert!(resolved.implicit_any_diagnostic_nodes(true).is_empty());
    }

    #[test]
    fn contextual_shape_resolution_has_explicit_safety_boundaries() {
        let fixture = Fixture::new("const f: () => void = (a?, ...b) => {};");
        let plan = fixture.contextual_plan(0).unwrap();
        let shape = |call_signature_count, type_parameter_count, parameter_count, rest| {
            SourceContextualSignatureShape {
                call_signature_count,
                type_parameter_count,
                parameter_count,
                has_effective_rest: rest,
            }
        };

        assert!(matches!(
            resolve_contextual_arrow_parameter_origins(&plan, shape(2, 0, 0, false)),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ContextualSignatureCount(_)
            ))
        ));
        assert!(matches!(
            resolve_contextual_arrow_parameter_origins(&plan, shape(1, 1, 0, false)),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ContextualGenericSignature(_)
            ))
        ));
        assert!(matches!(
            resolve_contextual_arrow_parameter_origins(&plan, shape(1, 0, 0, true)),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ContextualEffectiveRest(_)
            ))
        ));
        assert!(matches!(
            resolve_contextual_arrow_parameter_origins(&plan, shape(1, 0, 2, false)),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ContextualNonEmptyRestTail(_)
            ))
        ));

        let required = Fixture::new("const f: () => void = (a) => {};");
        assert!(matches!(
            required.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ContextualArity(_)
            ))
        ));
    }

    #[test]
    fn contextual_planner_rejects_shapes_outside_the_first_cut() {
        let unannotated = Fixture::new("const f = (a) => {};");
        assert!(matches!(
            unannotated.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::MissingVariableAnnotation(_)
            ))
        ));

        let annotated_parameter = Fixture::new("const f: (a: number) => void = (a: number) => {};");
        assert!(matches!(
            annotated_parameter.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::AnnotatedParameter(_)
            ))
        ));

        let initialized = Fixture::new("const f: (a: number) => void = (a = 0) => {};");
        assert!(matches!(
            initialized.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::InitializedParameter(_)
            ))
        ));

        let destructured = Fixture::new("const f: (a: number) => void = ({ a }) => {};");
        assert!(matches!(
            destructured.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::DestructuredParameter(_)
            ))
        ));

        let explicit_return = Fixture::new("const f: () => void = (): void => {};");
        assert!(matches!(
            explicit_return.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ExplicitReturnType(_)
            ))
        ));

        let nonempty = Fixture::new("const f: () => void = () => { return; };");
        assert!(matches!(
            nonempty.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::NonEmptyBody(_)
            ))
        ));
    }

    #[test]
    fn rejects_nonzero_arrow_parser_facts_before_callable_publication() {
        let mut parsed = parse_source_file("const f = (): void => {};");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(913);
        let declaration = variable_declarations(&parsed, file)[0];
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let initializer = NodeRef::new(parsed.arena.id(), file, variable.initializer.unwrap());
        let NodeData::ArrowFunction(arrow) = &mut parsed
            .arena
            .get_mut(initializer.node)
            .expect("arrow initializer remains in the parsed arena")
            .data
        else {
            unreachable!()
        };
        arrow.facts = 1;
        let fixture = Fixture::from_parsed(parsed);

        assert_eq!(
            fixture.plan(0),
            Err(SourceArrowError::Invariant(
                SourceArrowInvariant::InvalidInitializer(initializer)
            ))
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(fixture.bound.symbol(initializer).unwrap())
                .is_none()
        );
    }

    #[test]
    fn required_then_optional_parameters_have_exact_arity() {
        let fixture =
            Fixture::new("const f = (required: string, optional?: number): boolean => true;");
        let plan = fixture.plan(0).unwrap();

        assert_eq!(plan.callable.parameters.len(), 2);
        assert_eq!(plan.callable.min_argument_count, 1);
        assert!(!plan.callable.parameters[0].optional);
        assert!(plan.callable.parameters[1].optional);
        assert_ne!(
            plan.callable.parameters[0].symbol,
            plan.callable.parameters[1].symbol
        );
    }

    #[test]
    fn classifies_only_the_three_bounded_body_shapes() {
        let fixture = Fixture::new(
            r#"
                const empty = (): void => {};
                const returned = (): string => { return "ok"; };
                const concise = (): number => 1;
            "#,
        );
        let empty = fixture.plan(0).unwrap();
        let returned = fixture.plan(1).unwrap();
        let concise = fixture.plan(2).unwrap();

        assert!(matches!(
            empty.body,
            SourceArrowBodyPlan::EmptyBlock { block } if block == empty.callable.body
        ));
        assert!(matches!(
            returned.body,
            SourceArrowBodyPlan::ReturnExpression {
                block,
                statement: _,
                expression,
            } if block == returned.callable.body
                && fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::StringLiteral
        ));
        assert!(matches!(
            concise.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if expression == concise.callable.body
                    && fixture.parsed.arena.get(expression.node).unwrap().kind
                        == SyntaxKind::NumericLiteral
        ));
    }

    #[test]
    fn rejects_contextual_or_non_direct_variable_shapes() {
        let annotated =
            Fixture::new("const f: (x: number) => string = (x: number): string => \"ok\";");
        assert!(matches!(
            annotated.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::VariableAnnotation(_)
            ))
        ));

        let siblings =
            Fixture::new("const f = (x: number): number => x, g = (x: number): number => x;");
        assert!(matches!(
            siblings.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::NonSingleDeclaration(_)
            ))
        ));

        let wrapped = Fixture::new("const f = ((x: number): string => \"ok\");");
        assert!(matches!(
            wrapped.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::NonArrowInitializer(_)
            ))
        ));
    }

    #[test]
    fn admits_bound_direct_expandos_but_rejects_contextual_expandos() {
        let direct = Fixture::new("const foo = () => {}; foo.bar = 42; export {};");
        let direct_declaration = direct.declarations()[0];
        let NodeData::VariableDeclaration(direct_variable) = &direct
            .parsed
            .arena
            .get(direct_declaration.node)
            .unwrap()
            .data
        else {
            panic!("expected variable declaration")
        };
        let direct_arrow = NodeRef::new(
            direct.parsed.arena.id(),
            direct.file,
            direct_variable.initializer.unwrap(),
        );
        let direct_owner = direct.bound.symbol(direct_arrow).unwrap();
        assert!(
            direct
                .store
                .symbol(direct_owner)
                .unwrap()
                .exports()
                .is_some()
        );
        let direct_plan = direct.plan(0).unwrap();
        assert_eq!(direct_plan.callable.declaration, direct_arrow);
        assert_eq!(direct_plan.callable.owner_symbol, direct_owner);
        assert!(
            direct
                .store
                .source_callable_type_for_owner(direct_owner)
                .is_none()
        );

        let mut malformed = Fixture::new("const foo = () => {}; foo.bar = 42; export {};");
        let assignment = malformed
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                    malformed.parsed.arena.id(),
                    malformed.file,
                    node,
                ))
            })
            .unwrap();
        let property = malformed.bound.symbol(assignment).unwrap();
        let record = malformed.store.symbol(property).unwrap();
        let (members, exports, export_symbol) =
            (record.members(), record.exports(), record.export_symbol());
        assert!(malformed.store.set_symbol_relationships(
            property,
            members,
            exports,
            None,
            export_symbol,
        ));
        assert!(matches!(
            malformed.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::ExpandoProperties(_))
            ))
        ));

        let contextual = Fixture::new("const foo: () => void = () => {}; foo.bar = 42; export {};");
        assert!(matches!(
            contextual.contextual_plan(0),
            Err(SourceContextualArrowError::Unsupported(
                SourceContextualArrowUnsupported::ExpandoProperties(_)
            ))
        ));
    }

    #[test]
    fn rejects_unbounded_block_bodies_without_claiming_corruption() {
        let complex = Fixture::new("const f = (): void => { 1; };");
        assert!(matches!(
            complex.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::ComplexBlock(_)
            ))
        ));

        let bare = Fixture::new("const f = (): number => { return; };");
        assert!(matches!(
            bare.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::BareReturn(_)
            ))
        ));
    }

    #[test]
    fn preserves_shared_callable_unsupported_reasons() {
        let generic = Fixture::new("const f = <T>(x: T): T => x;");
        assert!(matches!(
            generic.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::GenericSignature(_))
            ))
        ));

        let missing_parameter_type = Fixture::new("const f = (x): number => x;");
        assert!(matches!(
            missing_parameter_type.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::MissingParameterType(
                    _
                ))
            ))
        ));

        let inferred_return = Fixture::new("const f = (x: number) => x;");
        assert!(
            inferred_return
                .plan(0)
                .unwrap()
                .callable
                .return_type
                .is_inferred()
        );

        let initialized = Fixture::new("const f = (x: number = 0): number => x;");
        let initialized = initialized.plan(0).unwrap();
        assert_eq!(initialized.callable.min_argument_count, 0);
        assert!(!initialized.callable.parameters[0].optional);
        assert!(initialized.callable.parameters[0].initializer.is_some());

        let rest = Fixture::new("const f = (head: string, ...values: number[]): string => head;");
        let rest = rest.plan(0).unwrap();
        assert_eq!(rest.callable.min_argument_count, 1);
        assert!(
            rest.callable
                .flags
                .contains(SignatureFlags::HAS_REST_PARAMETER)
        );
        assert!(rest.callable.parameters[1].rest);

        let predicate = Fixture::new("const f = (x: unknown): x is string => true;");
        assert!(matches!(
            predicate.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::TypePredicate(_))
            ))
        ));
    }
}
