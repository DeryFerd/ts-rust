//! Planning for exact arrow values in direct top-level declarations.
//!
//! The installed path proves an unannotated top-level declaration of the form
//! `var|let|const name = (parameters): Return => body`. A separate read-only
//! contextual planner proves `name: Context = (parameters) => {}` without
//! resolving `Context` or fabricating parameter types. Both retain the ordinary
//! variable symbol separately from the binder's anonymous FUNCTION owner and
//! preserve the export route when present. Publication remains deferred to
//! source dispatch.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    declared::preflight_node,
    functions::{FunctionTypeError, plan_function_type},
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

/// The only inferred-return shape admitted by the first contextual cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceContextualReturnOrigin {
    InferredEmptyBody { block: NodeRef },
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
                | SourceArrowUnsupported::BareReturn(node) => Some(node),
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
) -> Result<SourceContextualSignatureShape, SourceContextualArrowError> {
    let plan = plan_function_type(store, host, type_node, None, false, array_targets)
        .map_err(|error| contextual_target_plan_error(error, type_node))?;
    let return_type = plan.return_type;
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.kind != SyntaxKind::VoidKeyword {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::ContextualTargetSyntax(return_type),
        ));
    }
    Ok(SourceContextualSignatureShape {
        call_signature_count: 1,
        type_parameter_count: 0,
        parameter_count: plan.parameters.len(),
        has_effective_rest: false,
    })
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
    let contextual_signature_shape =
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
    let NodeData::Block(block) = &body_record.data else {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonEmptyBody(body),
        ));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.parent != Some(initializer.node)
        || !range_contains(initializer_record.range, body_record.range)
        || body_record.flags.0 != 0
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return Err(contextual_invariant(
            SourceContextualArrowInvariant::InvalidBody(body),
        ));
    }
    if !block.statements.nodes.is_empty() {
        return Err(contextual_unsupported(
            SourceContextualArrowUnsupported::NonEmptyBody(body),
        ));
    }
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
        return_origin: SourceContextualReturnOrigin::InferredEmptyBody { block: body },
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
    let owner_symbol = bound
        .symbol(initializer)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(initializer)))?;
    if owner_symbol == variable_symbol
        || store.symbol(owner_symbol).is_some_and(|symbol| {
            symbol.flags() != SymbolFlags::FUNCTION
                || symbol.name() != InternalSymbolName::Function.as_ref()
        })
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            initializer,
        )));
    }

    let callable = plan_source_callable(store, host, initializer, owner_symbol, array_targets)
        .map_err(map_callable_error)?;
    if callable.family != SourceCallableFamily::ArrowFunction
        || callable.declaration != initializer
        || callable.owner_symbol != owner_symbol
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            initializer,
        )));
    }
    let body = plan_body(store, host, &callable)?;
    Ok(SourceArrowPlan {
        variable_declaration,
        variable_name,
        variable_symbol,
        callable,
        body,
    })
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
                return Err(unsupported(SourceArrowUnsupported::BareReturn(statement)));
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
        _ => Err(unsupported(SourceArrowUnsupported::ComplexBlock(body))),
    }
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
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions,
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
            let file = FileId::new(913);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/source_arrows.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
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
    fn classifies_bound_expando_properties_as_deferred_source_semantics() {
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
        assert!(matches!(
            direct.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::ExpandoProperties(_))
            ))
        ));
        assert!(
            direct
                .store
                .source_callable_type_for_owner(direct_owner)
                .is_none()
        );

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

        let bare = Fixture::new("const f = (): void => { return; };");
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
