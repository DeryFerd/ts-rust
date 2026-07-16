//! Exact annotated function-type signatures for the dependency-closed type-node cut.
//!
//! This module owns the semantic shape of a non-generic `FunctionTypeNode`.
//! The type-node planner/executor only supplies recursive annotation callbacks;
//! binder proof, cache validation, shell publication, signatures, parameter
//! value types, and lazy return-type validation stay here.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    callables::{ValidatedSingleCallParameterDisplay, ValidatedSingleCallSignatureDisplay},
    declared::preflight_node,
    links::{
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        TypeAliasLinks, TypeNodeLinks, ValueSymbolLinks,
    },
    signatures::{Signature, SignatureFlags},
    store::SourceNodeParent,
    type_records::{ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// One identifier parameter whose annotation belongs to this exact slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FunctionParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
    pub(super) optional: bool,
}

/// Binder and syntax identities retained for one function-type node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FunctionTypePlan {
    pub(super) node: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) members: SymbolTableId,
    pub(super) call_symbol: SemanticSymbolId,
    pub(super) alias_symbol: Option<SemanticSymbolId>,
    pub(super) parameters: Vec<FunctionParameterPlan>,
    pub(super) return_type: NodeRef,
    return_identity_node: NodeRef,
    return_null_literal_identity: bool,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    array_targets: Option<CanonicalArrayTargets>,
}

/// Malformed syntax, binder provenance, or semantic cache state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FunctionTypeInvariant {
    InvalidSyntax(NodeRef),
    InvalidTypeSymbol(NodeRef),
    InvalidCallSymbol(NodeRef),
    InvalidParameter(NodeRef),
    InvalidParameterSymbol(NodeRef),
    InvalidTypeCache(NodeRef),
    InvalidSignatureCache(NodeRef),
    InvalidParameterCache(NodeRef),
    Capacity(NodeRef),
    Publication(NodeRef),
}

/// Valid function-like families intentionally excluded from phase one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FunctionTypeUnsupported {
    GenericAlias(NodeRef),
    GenericSignature(NodeRef),
    ThisParameter(NodeRef),
    RestParameter(NodeRef),
    InitializedParameter(NodeRef),
    DestructuredParameter(NodeRef),
    ParameterModifiers(NodeRef),
    MissingParameterType(NodeRef),
    MissingReturnType(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FunctionTypeError {
    Unsupported(FunctionTypeUnsupported),
    Invariant(FunctionTypeInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl FunctionTypeError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => Some(match reason {
                FunctionTypeUnsupported::GenericAlias(node)
                | FunctionTypeUnsupported::GenericSignature(node)
                | FunctionTypeUnsupported::ThisParameter(node)
                | FunctionTypeUnsupported::RestParameter(node)
                | FunctionTypeUnsupported::InitializedParameter(node)
                | FunctionTypeUnsupported::DestructuredParameter(node)
                | FunctionTypeUnsupported::ParameterModifiers(node)
                | FunctionTypeUnsupported::MissingParameterType(node)
                | FunctionTypeUnsupported::MissingReturnType(node) => node,
            }),
            Self::Invariant(reason) => Some(match reason {
                FunctionTypeInvariant::InvalidSyntax(node)
                | FunctionTypeInvariant::InvalidTypeSymbol(node)
                | FunctionTypeInvariant::InvalidCallSymbol(node)
                | FunctionTypeInvariant::InvalidParameter(node)
                | FunctionTypeInvariant::InvalidParameterSymbol(node)
                | FunctionTypeInvariant::InvalidTypeCache(node)
                | FunctionTypeInvariant::InvalidSignatureCache(node)
                | FunctionTypeInvariant::InvalidParameterCache(node)
                | FunctionTypeInvariant::Capacity(node)
                | FunctionTypeInvariant::Publication(node) => node,
            }),
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for FunctionTypeError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for FunctionTypeError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FunctionTypeState {
    Cold,
    ActiveBarrier {
        type_: TypeId,
        signature: SignatureId,
    },
    ActiveParameters {
        type_: TypeId,
        signature: SignatureId,
    },
    Resolved {
        type_: TypeId,
        signature: SignatureId,
    },
}

/// A newly published signature whose parameter annotations still need their
/// recursive type-node execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PendingFunctionType {
    pub(super) type_: TypeId,
    pub(super) signature: SignatureId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PendingFunctionTypeProof {
    store: SemanticStoreId,
    type_: TypeId,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
    plan: FunctionTypePlan,
}

impl PendingFunctionTypeProof {
    pub(super) const fn store(&self) -> SemanticStoreId {
        self.store
    }

    pub(super) const fn type_(&self) -> TypeId {
        self.type_
    }

    pub(super) const fn array_targets(&self) -> Option<CanonicalArrayTargets> {
        self.array_targets
    }
}

/// Parameter types are published only after every recursively reached function
/// object has left its structured empty-member barrier.
#[derive(Clone, Debug)]
pub(super) struct PendingParameterTypes {
    pub(super) plan: FunctionTypePlan,
    pub(super) base_types: Vec<TypeId>,
}

/// Store-only classification used by union-cache validation. Full AST and
/// parameter-link proof is performed by [`function_type_state`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredFunctionTypeValidation {
    NotFunctionType,
    Pending,
    Valid(Vec<TypeId>),
    Malformed,
}

/// Why an otherwise function-shaped type cannot be projected for display.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FunctionTypeDisplayError {
    Unsupported(FunctionTypeUnsupported),
    Pending,
    Malformed,
}

pub(super) fn plan_function_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
    alias_is_generic: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<FunctionTypePlan, FunctionTypeError> {
    if alias_is_generic {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericAlias(node),
        ));
    }
    let record = preflight_node(store, host, node)?;
    let NodeData::FunctionTypeNode(function) = &record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    };
    if record.kind != SyntaxKind::FunctionType
        || record.flags.0 & NODE_FLAG_JSDOC != 0
        || function.full_signature.is_some()
        || function.next_container.is_some()
        || function.symbol.is_some()
        || function.modifiers.is_some()
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    }
    if function.type_parameters.is_some() {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(node),
        ));
    }
    if function.parameters.range.start < record.range.start
        || function.parameters.range.end > record.range.end
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    }

    let bound = host
        .bound_file(node)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    let raw_symbol = bound
        .symbol(node)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    let symbol = store
        .get_merged_symbol(raw_symbol)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    if symbol != raw_symbol {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)));
    }
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    let members = symbol_record
        .members()
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    if symbol_record.flags() != SymbolFlags::TYPE_LITERAL
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Type.as_ref()
        || symbol_record.declarations() != Some(&[node])
        || symbol_record.value_declaration().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)));
    }

    let members_table = store
        .symbol_table(members)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    let call_symbol = members_table
        .get(InternalSymbolName::Call.as_ref())
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidCallSymbol(node)))?;
    if members_table.len() != 1 {
        return Err(invariant(FunctionTypeInvariant::InvalidCallSymbol(node)));
    }
    let call_record = store
        .symbol(call_symbol)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidCallSymbol(node)))?;
    if call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record.declarations() != Some(&[node])
        || call_record.value_declaration().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.parent().is_some()
        || call_record.export_symbol().is_some()
        || store.get_merged_symbol(call_symbol) != Some(call_symbol)
    {
        return Err(invariant(FunctionTypeInvariant::InvalidCallSymbol(node)));
    }
    validate_alias_symbol(store, node, alias_symbol)?;

    let mut parameters = Vec::with_capacity(function.parameters.nodes.len());
    let mut previous_end = function.parameters.range.start;
    let mut min_argument_count = 0usize;
    let mut flags = SignatureFlags::NONE;
    for parameter_id in &function.parameters.nodes {
        let parameter = NodeRef::new(node.arena, node.file, *parameter_id);
        if parameters
            .iter()
            .any(|planned: &FunctionParameterPlan| planned.declaration == parameter)
        {
            return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                parameter,
            )));
        }
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                parameter,
            )));
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(node.node)
            || parameter_record.flags.0 & NODE_FLAG_JSDOC != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < function.parameters.range.start
            || parameter_record.range.end > function.parameters.range.end
            || data.symbol.is_some()
            || data.facts != 0
        {
            return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                parameter,
            )));
        }
        previous_end = parameter_record.range.end;
        if data.dot_dot_dot_token.is_some() {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::RestParameter(parameter),
            ));
        }
        if data.initializer.is_some() {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::InitializedParameter(parameter),
            ));
        }
        if data.modifiers.is_some() {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::ParameterModifiers(parameter),
            ));
        }

        let name = NodeRef::new(node.arena, node.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::DestructuredParameter(parameter),
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || name_record.range.start < parameter_record.range.start
            || name_record.range.end > parameter_record.range.end
        {
            return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                parameter,
            )));
        }
        if identifier.text == "this" {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::ThisParameter(parameter),
            ));
        }

        let Some(type_id) = data.type_ else {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::MissingParameterType(parameter),
            ));
        };
        let type_node = NodeRef::new(node.arena, node.file, type_id);
        let type_record = preflight_node(store, host, type_node)?;
        if type_record.parent != Some(parameter.node)
            || type_record.range.start < name_record.range.end
            || type_record.range.end > parameter_record.range.end
        {
            return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                parameter,
            )));
        }
        let optional = if let Some(question_id) = data.question_token {
            let question = NodeRef::new(node.arena, node.file, question_id);
            let question_record = preflight_node(store, host, question)?;
            if question_record.kind != SyntaxKind::QuestionToken
                || question_record.parent != Some(parameter.node)
                || question_record.range.start < name_record.range.end
                || question_record.range.end > type_record.range.start
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                    parameter,
                )));
            }
            true
        } else {
            false
        };

        let raw_parameter_symbol = bound
            .symbol(parameter)
            .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidParameterSymbol(parameter)))?;
        let parameter_symbol = store
            .get_merged_symbol(raw_parameter_symbol)
            .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidParameterSymbol(parameter)))?;
        if parameter_symbol != raw_parameter_symbol {
            return Err(invariant(FunctionTypeInvariant::InvalidParameterSymbol(
                parameter,
            )));
        }
        let parameter_symbol_record = store
            .symbol(parameter_symbol)
            .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidParameterSymbol(parameter)))?;
        if parameter_symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || parameter_symbol_record.check_flags() != CheckFlags::NONE
            || parameter_symbol_record.name().as_bytes() != identifier.text.as_bytes()
            || parameter_symbol_record.declarations() != Some(&[parameter])
            || parameter_symbol_record.value_declaration() != Some(parameter)
            || parameter_symbol_record.members().is_some()
            || parameter_symbol_record.exports().is_some()
            || parameter_symbol_record.parent().is_some()
            || parameter_symbol_record.export_symbol().is_some()
        {
            return Err(invariant(FunctionTypeInvariant::InvalidParameterSymbol(
                parameter,
            )));
        }
        let identity_node = peel_parenthesized_type(store, host, type_node)?;
        if type_record.kind == SyntaxKind::LiteralType {
            flags |= SignatureFlags::HAS_LITERAL_TYPES;
        }
        parameters.push(FunctionParameterPlan {
            declaration: parameter,
            symbol: parameter_symbol,
            type_node,
            identity_node,
            null_literal_identity: is_null_literal_type(store, host, identity_node)?,
            optional,
        });
        if !optional {
            min_argument_count = parameters.len();
        }
    }

    let return_id = function.type_.ok_or(FunctionTypeError::Unsupported(
        FunctionTypeUnsupported::MissingReturnType(node),
    ))?;
    let return_type = NodeRef::new(node.arena, node.file, return_id);
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.parent != Some(node.node)
        || return_record.range.start < function.parameters.range.end
        || return_record.range.end > record.range.end
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    }

    let min_argument_count = i32::try_from(min_argument_count)
        .map_err(|_| invariant(FunctionTypeInvariant::Capacity(node)))?;
    let return_identity_node = peel_parenthesized_type(store, host, return_type)?;
    let plan = FunctionTypePlan {
        node,
        symbol,
        members,
        call_symbol,
        alias_symbol,
        parameters,
        return_type,
        return_identity_node,
        return_null_literal_identity: is_null_literal_type(store, host, return_identity_node)?,
        flags,
        min_argument_count,
        array_targets,
    };
    function_type_state(store, &plan, true)?;
    Ok(plan)
}

fn validate_alias_symbol(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
) -> Result<(), FunctionTypeError> {
    let Some(alias_symbol) = alias_symbol else {
        return Ok(());
    };
    let record = store
        .symbol(alias_symbol)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)))?;
    if store.get_merged_symbol(alias_symbol) != Some(alias_symbol)
        || record.flags() != SymbolFlags::TYPE_ALIAS
        || record.check_flags() != CheckFlags::NONE
    {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeSymbol(node)));
    }
    Ok(())
}

pub(super) fn function_type_state(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    allow_active_barrier: bool,
) -> Result<FunctionTypeState, FunctionTypeError> {
    let type_links = store.type_node_links(plan.node);
    if type_links.is_some_and(|links| links.outer_type_parameters.is_some()) {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
            plan.node,
        )));
    }
    let Some(type_) = type_links.and_then(|links| links.resolved_type) else {
        if !default_signature_links(store, plan.node)
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
        {
            return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
                plan.node,
            )));
        }
        return Ok(FunctionTypeState::Cold);
    };
    let record = store
        .type_payload(type_)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidTypeCache(plan.node)))?;
    let TypeData::Object(object) = record.data() else {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
            plan.node,
        )));
    };
    if record.flags() != TypeFlags::OBJECT
        || !store.type_has_function_type_provenance(type_)
        || record.symbol() != Some(plan.symbol)
        || !valid_alias(store, record, plan.alias_symbol)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
            plan.node,
        )));
    }
    let signature = exact_signature_link(store, plan.node)?;
    validate_signature(store, plan, signature)?;
    let resolved_return_type = store
        .signature(signature)
        .expect("the signature was validated")
        .resolved_return_type();

    let is_barrier = record.object_flags()
        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && object.structured == StructuredTypeData::default();
    if is_barrier {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
        {
            return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
                plan.node,
            )));
        }
        return Ok(FunctionTypeState::ActiveBarrier { type_, signature });
    }

    let structured = &object.structured;
    if record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || structured.constrained != ConstrainedTypeData::default()
        || structured.members != Some(plan.members)
        || structured.properties.as_deref() != Some(&[])
        || structured.signatures.as_deref() != Some(&[signature])
        || structured.call_signature_count != 1
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
            plan.node,
        )));
    }
    if !plan.parameters.is_empty()
        && plan
            .parameters
            .iter()
            .all(|parameter| default_parameter_links(store, parameter.symbol))
    {
        if !allow_active_barrier || resolved_return_type.is_some() {
            return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
                plan.node,
            )));
        }
        return Ok(FunctionTypeState::ActiveParameters { type_, signature });
    }
    for parameter in &plan.parameters {
        validate_parameter_links(store, plan, parameter)?;
    }
    validate_cached_return_type(store, plan, signature)?;
    Ok(FunctionTypeState::Resolved { type_, signature })
}

/// Produces the small, immutable signature view consumed by canonical type
/// display. Replanning against the retained AST proves parameter spelling and
/// optionality, while [`function_type_state`] proves that the cached signature
/// and parameter value types still describe that syntax exactly.
pub(super) fn function_type_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ValidatedSingleCallSignatureDisplay, FunctionTypeDisplayError> {
    let record = store
        .type_payload(type_)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    if !store.type_has_function_type_provenance(type_) {
        return Err(FunctionTypeDisplayError::Malformed);
    }
    let symbol = record.symbol().ok_or(FunctionTypeDisplayError::Malformed)?;
    let declaration = store
        .symbol(symbol)
        .and_then(|symbol| symbol.declarations())
        .and_then(|declarations| match declarations {
            [declaration] => Some(*declaration),
            _ => None,
        })
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let (alias_symbol, alias_is_generic) = match record.alias() {
        None => (None, false),
        Some(alias) => {
            let alias = store
                .type_alias(alias)
                .ok_or(FunctionTypeDisplayError::Malformed)?;
            (
                Some(alias.symbol().ok_or(FunctionTypeDisplayError::Malformed)?),
                alias.type_arguments().is_some(),
            )
        }
    };
    let plan = plan_function_type(
        store,
        host,
        declaration,
        alias_symbol,
        alias_is_generic,
        array_targets,
    )
    .map_err(function_type_display_error)?;
    let signature = match function_type_state(store, &plan, true)
        .map_err(function_type_display_error)?
    {
        FunctionTypeState::Resolved {
            type_: resolved,
            signature,
        } if resolved == type_ => signature,
        FunctionTypeState::ActiveBarrier { .. } | FunctionTypeState::ActiveParameters { .. } => {
            return Err(FunctionTypeDisplayError::Pending);
        }
        FunctionTypeState::Cold => return Err(FunctionTypeDisplayError::Malformed),
        FunctionTypeState::Resolved { .. } => {
            return Err(FunctionTypeDisplayError::Malformed);
        }
    };
    let signature = store
        .signature(signature)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let return_type = signature.resolved_return_type();
    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for parameter in &plan.parameters {
        let value_type = store
            .value_symbol_links(parameter.symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(FunctionTypeDisplayError::Malformed)?;
        let parameter_node = host
            .node(parameter.declaration)
            .ok_or(FunctionTypeDisplayError::Malformed)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
            return Err(FunctionTypeDisplayError::Malformed);
        };
        let name = NodeRef::new(
            parameter.declaration.arena,
            parameter.declaration.file,
            parameter_data.name,
        );
        let name_node = host.node(name).ok_or(FunctionTypeDisplayError::Malformed)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(FunctionTypeDisplayError::Malformed);
        };
        parameters.push(ValidatedSingleCallParameterDisplay {
            name: identifier.text.clone(),
            value_type,
            optional: parameter.optional,
        });
    }
    Ok(ValidatedSingleCallSignatureDisplay {
        owner: type_,
        parameters,
        return_type,
    })
}

const fn function_type_display_error(error: FunctionTypeError) -> FunctionTypeDisplayError {
    match error {
        FunctionTypeError::Unsupported(reason) => FunctionTypeDisplayError::Unsupported(reason),
        FunctionTypeError::Invariant(_)
        | FunctionTypeError::DeclaredType(_)
        | FunctionTypeError::LiteralCache(_) => FunctionTypeDisplayError::Malformed,
    }
}

pub(super) fn reserve_function_type_capacities(
    store: &mut CanonicalTypeMapperStore,
    plans: &[&FunctionTypePlan],
) -> Result<(usize, usize, usize), FunctionTypeError> {
    let Some(first) = plans.first() else {
        return Ok((0, 0, 0));
    };
    let mut cold = 0usize;
    let mut aliases = 0usize;
    let mut strict_optional_unions = 0usize;
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(first.node)))?
        .options
        .strict_null_checks;
    for plan in plans {
        let state = function_type_state(store, plan, true)?;
        if state == FunctionTypeState::Cold {
            cold = cold
                .checked_add(1)
                .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(plan.node)))?;
            aliases = aliases
                .checked_add(usize::from(plan.alias_symbol.is_some()))
                .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(plan.node)))?;
        }
        if strict
            && matches!(
                state,
                FunctionTypeState::Cold
                    | FunctionTypeState::ActiveBarrier { .. }
                    | FunctionTypeState::ActiveParameters { .. }
            )
        {
            strict_optional_unions = strict_optional_unions
                .checked_add(
                    plan.parameters
                        .iter()
                        .filter(|parameter| parameter.optional)
                        .count(),
                )
                .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(plan.node)))?;
        }
    }
    if !store.try_reserve_signatures(cold)
        || !store.try_reserve_function_type_provenance(cold)
        || !store.try_reserve_function_signature_return_annotations(cold)
    {
        return Err(invariant(FunctionTypeInvariant::Capacity(first.node)));
    }
    Ok((cold, aliases, strict_optional_unions))
}

pub(super) fn begin_function_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
) -> Result<Result<PendingFunctionType, TypeId>, FunctionTypeError> {
    match function_type_state(store, plan, true)? {
        FunctionTypeState::Resolved { type_, .. } => return Ok(Err(type_)),
        FunctionTypeState::Cold => {}
        FunctionTypeState::ActiveBarrier { type_, signature }
        | FunctionTypeState::ActiveParameters { type_, signature } => {
            return Ok(Ok(PendingFunctionType { type_, signature }));
        }
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or_else(|| invariant(FunctionTypeInvariant::Publication(plan.node)))?;
    let provenance = store.set_function_type_provenance(type_);
    assert!(
        provenance,
        "the planned function TypeId provenance was prevalidated and reserved"
    );
    if let Some(alias_symbol) = plan.alias_symbol {
        let alias = store
            .alloc_type_alias(Some(alias_symbol))
            .ok_or_else(|| invariant(FunctionTypeInvariant::Publication(plan.node)))?;
        if !store.set_type_alias(type_, Some(alias)) {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        }
    }
    if !store.set_type_node_links(
        plan.node,
        TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        },
    ) || !store.set_structured_type_members(type_, None, None, None, None, None)
    {
        return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
    }
    let signature = store
        .alloc_signature(
            plan.flags,
            Some(plan.node),
            Vec::new(),
            None,
            plan.parameters
                .iter()
                .map(|parameter| parameter.symbol)
                .collect(),
            None,
            None,
            plan.min_argument_count,
        )
        .ok_or_else(|| invariant(FunctionTypeInvariant::Publication(plan.node)))?;
    let return_annotation = store.set_function_signature_return_annotation(
        signature,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    assert!(
        return_annotation,
        "the planned function return annotation was prevalidated and reserved"
    );
    if !store.set_signature_links(
        plan.node,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ) {
        return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
    }
    Ok(Ok(PendingFunctionType { type_, signature }))
}

pub(super) fn finalize_function_structure(
    store: &mut CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    pending: PendingFunctionType,
) -> Result<(), FunctionTypeError> {
    match function_type_state(store, plan, true)? {
        FunctionTypeState::ActiveBarrier { type_, signature }
            if type_ == pending.type_ && signature == pending.signature => {}
        FunctionTypeState::ActiveParameters { type_, signature }
            if type_ == pending.type_ && signature == pending.signature =>
        {
            return Ok(());
        }
        _ => return Err(invariant(FunctionTypeInvariant::Publication(plan.node))),
    }
    if !store.set_structured_type_members(
        pending.type_,
        Some(plan.members),
        Some(Vec::new()),
        Some(vec![pending.signature]),
        None,
        None,
    ) {
        return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
    }
    Ok(())
}

pub(super) fn publish_parameter_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    pending: &[PendingParameterTypes],
    prepared: &mut PreparedTypeQueryTypes,
) -> Result<(), FunctionTypeError> {
    let Some(first) = pending.first() else {
        return Ok(());
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(FunctionTypeInvariant::Publication(first.plan.node)))?
        .options
        .strict_null_checks;
    let undefined = store
        .intrinsic_bootstrap()
        .expect("bootstrap was checked above")
        .undefined_type;
    let parameter_count = pending.iter().try_fold(0usize, |count, function| {
        count
            .checked_add(function.plan.parameters.len())
            .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(function.plan.node)))
    })?;
    for function in pending {
        if function.base_types.len() != function.plan.parameters.len()
            || !matches!(
                function_type_state(store, &function.plan, true)?,
                FunctionTypeState::ActiveParameters { .. }
            )
        {
            return Err(invariant(FunctionTypeInvariant::Publication(
                function.plan.node,
            )));
        }
        for (parameter, base) in function.plan.parameters.iter().zip(&function.base_types) {
            if store.type_payload(*base).is_none()
                || !default_parameter_links(store, parameter.symbol)
            {
                return Err(invariant(FunctionTypeInvariant::Publication(
                    parameter.declaration,
                )));
            }
            let cached_base = cached_annotation_identity(
                store,
                parameter.identity_node,
                parameter.null_literal_identity,
            )
            .ok_or_else(|| {
                invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                ))
            })?;
            if cached_base != *base
                || store
                    .validate_cached_array_capability_prepared(*base, global_types, prepared)
                    .is_err()
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
        }
    }

    let mut resolved = Vec::with_capacity(parameter_count);
    for function in pending {
        for (parameter, base) in function.plan.parameters.iter().zip(&function.base_types) {
            let type_ = if strict && parameter.optional {
                let already_contains_undefined = *base == undefined
                    || store.type_payload(*base).is_some_and(|record| {
                        matches!(
                            record.data(),
                            TypeData::Union(union) if union.union.types.contains(&undefined)
                        )
                    });
                if already_contains_undefined {
                    *base
                } else {
                    match global_types {
                        Some(global_types) => store.literal_union_type_prepared_with_global_types(
                            global_types,
                            &[*base, undefined],
                            None,
                            prepared,
                        )?,
                        None => store.literal_union_type_prepared(
                            &[*base, undefined],
                            None,
                            prepared,
                        )?,
                    }
                }
            } else {
                *base
            };
            if store
                .validate_cached_array_capability_prepared(type_, global_types, prepared)
                .is_err()
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
            resolved.push((parameter.symbol, type_));
        }
    }
    for (symbol, type_) in resolved {
        let published = store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        );
        assert!(
            published,
            "prevalidated function parameter publication is infallible"
        );
    }
    for function in pending {
        let state = function_type_state(store, &function.plan, false);
        assert!(
            matches!(state, Ok(FunctionTypeState::Resolved { .. })),
            "prevalidated function batch must publish a resolved cache"
        );
        let Ok(FunctionTypeState::Resolved { type_, .. }) = state else {
            unreachable!()
        };
        let capability = match function.plan.array_targets {
            Some(targets) => {
                store.validate_cached_array_capability_with_array_targets(targets, type_)
            }
            None => store.validate_cached_array_capability(type_),
        };
        assert!(
            capability.is_ok(),
            "published function edges were prevalidated under the same capability"
        );
    }
    Ok(())
}

pub(super) fn active_alias_shell(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
) -> Result<TypeId, FunctionTypeError> {
    match function_type_state(store, plan, true)? {
        FunctionTypeState::ActiveBarrier { type_, .. }
        | FunctionTypeState::ActiveParameters { type_, .. }
        | FunctionTypeState::Resolved { type_, .. } => Ok(type_),
        FunctionTypeState::Cold => Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
            plan.node,
        ))),
    }
}

pub(super) fn resumable_function_type(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
) -> Result<Option<PendingFunctionType>, FunctionTypeError> {
    match function_type_state(store, plan, true)? {
        FunctionTypeState::ActiveBarrier { type_, signature }
        | FunctionTypeState::ActiveParameters { type_, signature } => {
            Ok(Some(PendingFunctionType { type_, signature }))
        }
        FunctionTypeState::Cold | FunctionTypeState::Resolved { .. } => Ok(None),
    }
}

pub(super) fn pending_function_type_proof(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
) -> Result<Option<PendingFunctionTypeProof>, FunctionTypeError> {
    match function_type_state(store, plan, true)? {
        FunctionTypeState::ActiveBarrier { type_, signature }
        | FunctionTypeState::ActiveParameters { type_, signature } => {
            Ok(Some(PendingFunctionTypeProof {
                store: store.id(),
                type_,
                signature,
                array_targets: plan.array_targets,
                plan: plan.clone(),
            }))
        }
        FunctionTypeState::Cold | FunctionTypeState::Resolved { .. } => Ok(None),
    }
}

pub(super) fn validate_pending_function_type_proof(
    store: &CanonicalTypeMapperStore,
    proof: &PendingFunctionTypeProof,
) -> bool {
    proof.store == store.id()
        && matches!(
            function_type_state(store, &proof.plan, true),
            Ok(FunctionTypeState::ActiveBarrier { type_, signature }
                | FunctionTypeState::ActiveParameters { type_, signature })
                if type_ == proof.type_ && signature == proof.signature
        )
}

pub(super) fn validate_lazy_return_signature(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
) -> Result<Option<TypeId>, FunctionTypeError> {
    match function_type_state(store, plan, false)? {
        FunctionTypeState::Resolved {
            signature: cached, ..
        } if cached == signature => {}
        _ => {
            return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
                plan.node,
            )));
        }
    }
    Ok(store
        .signature(signature)
        .expect("the function cache was validated")
        .resolved_return_type())
}

pub(super) fn validate_function_type_signature_identity(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
) -> Result<(), FunctionTypeError> {
    let matches = match function_type_state(store, plan, true)? {
        FunctionTypeState::ActiveBarrier {
            signature: cached, ..
        }
        | FunctionTypeState::ActiveParameters {
            signature: cached, ..
        }
        | FunctionTypeState::Resolved {
            signature: cached, ..
        } => cached == signature,
        FunctionTypeState::Cold => false,
    };
    if !matches {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    }
    Ok(())
}

pub(super) fn publish_lazy_return_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
    return_type: TypeId,
) -> Result<TypeId, FunctionTypeError> {
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    if store.type_payload(return_type).is_none()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_return_signature(store, plan, signature)?.is_some()
        || annotation != Some(return_type)
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    }
    let published = store.set_signature_resolved_return_type(signature, Some(return_type));
    assert!(published, "the lazy return publication was prevalidated");
    validate_cached_return_type(store, plan, signature)?;
    Ok(return_type)
}

pub(super) fn publish_circular_lazy_return_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
    annotation_type: TypeId,
) -> Result<TypeId, FunctionTypeError> {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    };
    let any_type = bootstrap.any_type;
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    if store.type_payload(annotation_type).is_none()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_return_signature(store, plan, signature)?.is_some()
        || annotation != Some(annotation_type)
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    }
    let published =
        store.set_function_signature_circular_return_type(signature, any_type, annotation_type);
    assert!(
        published,
        "the circular lazy return publication was prevalidated"
    );
    validate_cached_return_type(store, plan, signature)?;
    Ok(any_type)
}

pub(super) fn validate_stored_function_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredFunctionTypeValidation {
    let branded = store.type_has_function_type_provenance(type_);
    let not_function = || {
        if branded {
            StoredFunctionTypeValidation::Malformed
        } else {
            StoredFunctionTypeValidation::NotFunctionType
        }
    };
    let Some(record) = store.type_payload(type_) else {
        return not_function();
    };
    let Some(symbol) = record.symbol() else {
        return not_function();
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return not_function();
    };
    let Some(declaration) = symbol_record
        .declarations()
        .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))
    else {
        return not_function();
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::FunctionType) {
        return not_function();
    }
    if !branded {
        return StoredFunctionTypeValidation::Malformed;
    }
    let Some(members) = symbol_record.members() else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some(call_symbol) = store
        .symbol_table(members)
        .filter(|table| table.len() == 1)
        .and_then(|table| table.get(InternalSymbolName::Call.as_ref()))
    else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some(call_record) = store.symbol(call_symbol) else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some(signature) = store.signature_links(declaration).and_then(|links| {
        (links.effects_signature == EffectsSignatureState::Unresolved
            && links.decorator_signature == DecoratorSignatureState::Unresolved)
            .then_some(links.resolved_signature)
    }) else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let ResolvedSignatureState::Resolved(signature) = signature else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some(signature_record) = store.signature(signature) else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some((return_identity_node, return_null_literal_identity)) =
        store.function_signature_return_annotation(signature)
    else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let Some(TypeData::Object(object)) = store.type_payload(type_).map(TypeRecord::data) else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let mut parameter_edges = Vec::with_capacity(signature_record.parameters().len());
    let mut default_parameter_count = 0usize;
    let parameters_valid = signature_record.parameters().iter().all(|parameter| {
        let Some(parameter_record) = store.symbol(*parameter) else {
            return false;
        };
        let Some(declaration) = parameter_record
            .declarations()
            .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))
        else {
            return false;
        };
        let links_valid = match store.value_symbol_links(*parameter) {
            None => {
                default_parameter_count += 1;
                true
            }
            Some(links) if links == &ValueSymbolLinks::default() => {
                default_parameter_count += 1;
                true
            }
            Some(links) if links.resolved_type.is_some() => {
                let resolved_type = links.resolved_type.expect("the branch checked the type");
                let valid = links
                    == &(ValueSymbolLinks {
                        resolved_type: Some(resolved_type),
                        ..ValueSymbolLinks::default()
                    });
                if valid {
                    parameter_edges.push(resolved_type);
                }
                valid
            }
            Some(_) => false,
        };
        parameter_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && parameter_record.check_flags() == CheckFlags::NONE
            && parameter_record.value_declaration() == Some(declaration)
            && parameter_record.members().is_none()
            && parameter_record.exports().is_none()
            && parameter_record.parent().is_none()
            && parameter_record.export_symbol().is_none()
            && store.get_merged_symbol(*parameter) == Some(*parameter)
            && store.source_node_kind(declaration) == Some(SyntaxKind::Parameter)
            && signature_record.declaration().is_some_and(|owner| {
                store.source_node_parent(declaration) == Some(SourceNodeParent::Parent(owner))
            })
            && links_valid
    });
    let parameters_unique = signature_record
        .parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature_record.parameters()[..index].contains(parameter));
    let alias_state = stored_alias_state(store, type_, record, declaration);
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || symbol_record.flags() != SymbolFlags::TYPE_LITERAL
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Type.as_ref()
        || symbol_record.value_declaration().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.type_node_links(declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record.declarations() != Some(&[declaration])
        || call_record.value_declaration().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.parent().is_some()
        || call_record.export_symbol().is_some()
        || store.get_merged_symbol(call_symbol) != Some(call_symbol)
        || signature_record.flags().bits() & !SignatureFlags::HAS_LITERAL_TYPES.bits() != 0
        || signature_record.min_argument_count() < 0
        || usize::try_from(signature_record.min_argument_count()).map_or(true, |minimum| {
            minimum > signature_record.parameters().len()
        })
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.declaration() != Some(declaration)
        || !signature_record.type_parameters().is_empty()
        || signature_record.this_parameter().is_some()
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || !parameters_valid
        || default_parameter_count != 0
            && default_parameter_count != signature_record.parameters().len()
        || !parameters_unique
        || alias_state == StoredAliasState::Malformed
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return StoredFunctionTypeValidation::Malformed;
    }
    if object.structured == StructuredTypeData::default() {
        return if default_parameter_count == signature_record.parameters().len()
            && signature_record.resolved_return_type().is_none()
            && !store.signature_has_circular_return_type(signature)
        {
            StoredFunctionTypeValidation::Pending
        } else {
            StoredFunctionTypeValidation::Malformed
        };
    }
    if object.structured.members != Some(members)
        || object.structured.properties.as_deref() != Some(&[])
        || object.structured.signatures.as_deref() != Some(&[signature])
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return StoredFunctionTypeValidation::Malformed;
    }
    if default_parameter_count != 0 {
        if signature_record.resolved_return_type().is_some()
            || store.signature_has_circular_return_type(signature)
        {
            return StoredFunctionTypeValidation::Malformed;
        }
        return StoredFunctionTypeValidation::Pending;
    }
    if alias_state != StoredAliasState::Exact {
        return StoredFunctionTypeValidation::Malformed;
    }
    if let Some(return_type) = signature_record.resolved_return_type() {
        let annotation =
            cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
        let valid_return =
            if let Some(circular_annotation) = store.circular_return_annotation_type(signature) {
                let valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                    annotation == Some(circular_annotation) && return_type == bootstrap.any_type
                });
                if valid {
                    parameter_edges.push(circular_annotation);
                }
                valid
            } else {
                annotation == Some(return_type)
            };
        if !valid_return {
            return StoredFunctionTypeValidation::Malformed;
        }
        parameter_edges.push(return_type);
    } else if store.signature_has_circular_return_type(signature) {
        return StoredFunctionTypeValidation::Malformed;
    }
    StoredFunctionTypeValidation::Valid(parameter_edges)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StoredAliasState {
    Exact,
    Pending,
    Malformed,
}

fn stored_alias_state(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    declaration: NodeRef,
) -> StoredAliasState {
    let mut node = declaration;
    let alias_declaration = loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
            break None;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => node = parent,
            Some(SyntaxKind::TypeAliasDeclaration) => break Some(parent),
            _ => break None,
        }
    };
    match (record.alias(), alias_declaration) {
        (None, None) => StoredAliasState::Exact,
        (Some(alias), Some(alias_declaration)) => {
            let Some(alias) = store.type_alias(alias) else {
                return StoredAliasState::Malformed;
            };
            let Some(symbol) = alias.symbol() else {
                return StoredAliasState::Malformed;
            };
            if alias.type_arguments().is_some()
                || store.get_merged_symbol(symbol) != Some(symbol)
                || store.symbol(symbol).is_none_or(|symbol_record| {
                    symbol_record.flags() != SymbolFlags::TYPE_ALIAS
                        || symbol_record.check_flags() != CheckFlags::NONE
                        || symbol_record.declarations() != Some(&[alias_declaration])
                })
            {
                return StoredAliasState::Malformed;
            }
            match store.type_alias_links(symbol) {
                None => StoredAliasState::Pending,
                Some(links) if links == &TypeAliasLinks::default() => StoredAliasState::Pending,
                Some(links)
                    if links
                        == &(TypeAliasLinks {
                            declared_type: Some(type_),
                            ..TypeAliasLinks::default()
                        }) =>
                {
                    StoredAliasState::Exact
                }
                Some(_) => StoredAliasState::Malformed,
            }
        }
        _ => StoredAliasState::Malformed,
    }
}

fn validate_signature(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
) -> Result<(), FunctionTypeError> {
    let record = store
        .signature(signature)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidSignatureCache(plan.node)))?;
    let expected_parameters = plan
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    if record.flags() != plan.flags
        || record.min_argument_count() != plan.min_argument_count
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(plan.node)
        || !record.type_parameters().is_empty()
        || record.parameters() != expected_parameters
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.function_signature_return_annotation(signature)
            != Some((plan.return_identity_node, plan.return_null_literal_identity))
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    }
    Ok(())
}

fn exact_signature_link(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<SignatureId, FunctionTypeError> {
    let Some(links) = store.signature_links(node) else {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            node,
        )));
    };
    let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            node,
        )));
    };
    if links.effects_signature != EffectsSignatureState::Unresolved
        || links.decorator_signature != DecoratorSignatureState::Unresolved
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            node,
        )));
    }
    Ok(signature)
}

fn default_signature_links(store: &CanonicalTypeMapperStore, node: NodeRef) -> bool {
    store
        .signature_links(node)
        .is_none_or(|links| links == &SignatureLinks::default())
}

fn default_parameter_links(store: &CanonicalTypeMapperStore, symbol: SemanticSymbolId) -> bool {
    store
        .value_symbol_links(symbol)
        .is_none_or(|links| links == &ValueSymbolLinks::default())
}

fn validate_parameter_links(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    parameter: &FunctionParameterPlan,
) -> Result<(), FunctionTypeError> {
    let links = store.value_symbol_links(parameter.symbol).ok_or_else(|| {
        invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let Some(resolved) = links.resolved_type else {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    };
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(resolved),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    let base = cached_annotation_identity(
        store,
        parameter.identity_node,
        parameter.null_literal_identity,
    )
    .ok_or_else(|| {
        invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| {
            invariant(FunctionTypeInvariant::InvalidParameterCache(
                parameter.declaration,
            ))
        })?
        .options
        .strict_null_checks;
    let valid = if strict && parameter.optional {
        valid_optional_type(store, plan.array_targets, base, resolved)
    } else {
        base == resolved
    };
    if !valid {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    Ok(())
}

fn validate_cached_return_type(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    signature: SignatureId,
) -> Result<(), FunctionTypeError> {
    let resolved = store
        .signature(signature)
        .and_then(Signature::resolved_return_type);
    let circular_annotation = store.circular_return_annotation_type(signature);
    if resolved.is_none() {
        return if circular_annotation.is_some() {
            Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
                plan.node,
            )))
        } else {
            Ok(())
        };
    }
    let resolved = resolved.expect("the unresolved branch returned");
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    let valid = if let Some(circular_annotation) = circular_annotation {
        store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            annotation == Some(circular_annotation) && resolved == bootstrap.any_type
        })
    } else {
        annotation == Some(resolved)
    };
    if !valid {
        return Err(invariant(FunctionTypeInvariant::InvalidSignatureCache(
            plan.node,
        )));
    }
    Ok(())
}

fn cached_annotation_identity(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    null_literal_identity: bool,
) -> Option<TypeId> {
    let kind = store.source_node_kind(node)?;
    let bootstrap = store.intrinsic_bootstrap()?;
    if null_literal_identity {
        return Some(bootstrap.null_type);
    }
    let keyword = match kind {
        SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Some(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
        SyntaxKind::NullKeyword => Some(bootstrap.null_type),
        SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
        SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
        _ => None,
    };
    keyword.or_else(|| {
        store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
    })
}

fn peel_parenthesized_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<NodeRef, FunctionTypeError> {
    loop {
        let record = preflight_node(store, host, node)?;
        let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
            return Ok(node);
        };
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
        }
        let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
        if preflight_node(store, host, inner)?.parent != Some(node.node) {
            return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
        }
        node = inner;
    }
}

fn is_null_literal_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, FunctionTypeError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::LiteralTypeNode(literal) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::LiteralType {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    }
    let literal = NodeRef::new(node.arena, node.file, literal.literal);
    let literal_record = preflight_node(store, host, literal)?;
    if literal_record.parent != Some(node.node) || literal_record.range != record.range {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(node)));
    }
    Ok(literal_record.kind == SyntaxKind::NullKeyword
        && matches!(literal_record.data, NodeData::KeywordExpression(_)))
}

fn valid_optional_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    base: TypeId,
    resolved: TypeId,
) -> bool {
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(base_record) = store.type_payload(base) else {
        return false;
    };
    if base == undefined
        || base_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return resolved == base;
    }
    let mut expected = match base_record.data() {
        TypeData::Union(union) if union.union.types.contains(&undefined) => {
            let valid = match array_targets {
                Some(targets) => store.validate_union_constituent_with_array_targets(targets, base),
                None => store.validate_union_constituent(base),
            };
            return resolved == base && valid.is_ok();
        }
        TypeData::Union(_) => {
            return store
                .validate_optional_union_of_union_result(array_targets, base, undefined, resolved)
                .is_ok();
        }
        _ => vec![base],
    };
    expected.retain(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
    });
    if !expected.contains(&undefined) {
        expected.push(undefined);
    }
    if expected.len() == 1 {
        return resolved == expected[0];
    }
    let Some(TypeData::Union(union)) = store.type_payload(resolved).map(TypeRecord::data) else {
        return false;
    };
    let valid_union = match array_targets {
        Some(targets) => {
            store.validate_cached_union_result_with_array_targets(targets, resolved, None)
        }
        None => store.validate_cached_union_result(resolved, None),
    };
    expected.len() == union.union.types.len()
        && expected
            .iter()
            .all(|expected| union.union.types.contains(expected))
        && valid_union.is_ok()
}

fn valid_alias(
    store: &CanonicalTypeMapperStore,
    record: &TypeRecord,
    alias_symbol: Option<SemanticSymbolId>,
) -> bool {
    match (record.alias(), alias_symbol) {
        (None, None) => true,
        (Some(alias), Some(symbol)) => store.type_alias(alias).is_some_and(|alias| {
            alias.symbol() == Some(symbol) && alias.type_arguments().is_none()
        }),
        _ => false,
    }
}

const fn invariant(error: FunctionTypeInvariant) -> FunctionTypeError {
    FunctionTypeError::Invariant(error)
}
