//! Exact function-type signatures for the dependency-closed type-node cut.
//!
//! This module owns nongeneric function types, implicit `any[]` rest parameters,
//! and authenticated generic function types with outer lexical constraints.
//! The type-node planner/executor only supplies recursive annotation callbacks;
//! binder proof, cache validation, shell publication, signatures, parameter
//! value types, and lazy return-type validation stay here.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    callables::{ValidatedSingleCallParameterDisplay, ValidatedSingleCallSignatureDisplay},
    declared::{
        cached_ordinary_type_parameter_owner, execute_type_parameter,
        explicit_type_parameter_symbols, preflight_node, preflight_type_parameter_symbol,
    },
    jsdoc::{JsDocType, plan_javascript_source_jsdoc, validate_stored_source_jsdoc_function_type},
    links::{
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        SymbolNodeLinks, TypeAliasLinks, TypeNodeLinks, ValueSymbolLinks,
    },
    signatures::{ElementFlags, Signature, SignatureFlags},
    source_callables::implicit_any_array_type,
    store::SourceNodeParent,
    type_records::{ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// One identifier parameter and the existing type-node dependency required by its signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FunctionParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
    pub(super) optional: bool,
    rest_tuple_element: Option<FunctionRestTupleElementPlan>,
    implicit_any_rest: bool,
}

/// One required labeled tuple element expanded into a fixed signature parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FunctionRestTupleElementPlan {
    declaration: NodeRef,
    name: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
}

/// One inner signature parameter with an optional outer lexical constraint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FunctionTypeParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) constraint: Option<NodeRef>,
    pub(super) outer_symbol: Option<SemanticSymbolId>,
}

/// Binder and syntax identities retained for one function-type node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FunctionTypePlan {
    pub(super) node: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) members: SymbolTableId,
    pub(super) call_symbol: SemanticSymbolId,
    pub(super) alias_symbol: Option<SemanticSymbolId>,
    pub(super) type_parameters: Vec<FunctionTypeParameterPlan>,
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

        let implicit_any_rest = data.type_.is_none() && data.dot_dot_dot_token.is_some();
        let (type_node, type_start) = if let Some(type_id) = data.type_ {
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
            (type_node, type_record.range.start)
        } else if implicit_any_rest {
            let dependency = parameters
                .last()
                .map_or(return_type, |previous: &FunctionParameterPlan| {
                    previous.type_node
                });
            if implicit_any_array_type(store).is_none_or(|array| {
                array_targets.is_none()
                    && store
                        .intrinsic_bootstrap()
                        .is_none_or(|bootstrap| array != bootstrap.empty_object_type)
            }) || parameters.len() + 1 != function.parameters.nodes.len()
                || data.question_token.is_some()
                || parameters.is_empty()
                    && !matches!(
                        return_record.kind,
                        SyntaxKind::AnyKeyword
                            | SyntaxKind::UnknownKeyword
                            | SyntaxKind::StringKeyword
                            | SyntaxKind::NumberKeyword
                            | SyntaxKind::BigIntKeyword
                            | SyntaxKind::BooleanKeyword
                            | SyntaxKind::SymbolKeyword
                            | SyntaxKind::VoidKeyword
                            | SyntaxKind::UndefinedKeyword
                            | SyntaxKind::NullKeyword
                            | SyntaxKind::NeverKeyword
                            | SyntaxKind::ObjectKeyword
                            | SyntaxKind::IntrinsicKeyword
                    )
            {
                return Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::RestParameter(parameter),
                ));
            }
            (dependency, parameter_record.range.end)
        } else {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::MissingParameterType(parameter),
            ));
        };
        let optional = if let Some(question_id) = data.question_token {
            let question = NodeRef::new(node.arena, node.file, question_id);
            let question_record = preflight_node(store, host, question)?;
            if question_record.kind != SyntaxKind::QuestionToken
                || question_record.parent != Some(parameter.node)
                || question_record.range.start < name_record.range.end
                || question_record.range.end > type_start
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                    parameter,
                )));
            }
            true
        } else {
            false
        };
        let rest_tuple_element = match data.dot_dot_dot_token {
            Some(token) if implicit_any_rest => {
                let token = NodeRef::new(node.arena, node.file, token);
                let token_record = preflight_node(store, host, token)?;
                if token_record.kind != SyntaxKind::DotDotDotToken
                    || token_record.parent != Some(parameter.node)
                    || token_record.range.start < parameter_record.range.start
                    || token_record.range.end > name_record.range.start
                {
                    return Err(invariant(FunctionTypeInvariant::InvalidParameter(
                        parameter,
                    )));
                }
                flags |= SignatureFlags::HAS_REST_PARAMETER;
                None
            }
            Some(token) => Some(plan_rest_tuple_parameter(
                store,
                host,
                node,
                parameter,
                name,
                type_node,
                NodeRef::new(node.arena, node.file, token),
            )?),
            None => None,
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
        if parameter_symbol_record.flags()
            == SymbolFlags::TYPE_PARAMETER | SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && function
                .type_parameters
                .as_ref()
                .is_some_and(|type_parameters| {
                    let [type_parameter] = type_parameters.nodes.as_slice() else {
                        return false;
                    };
                    let type_parameter = NodeRef::new(node.arena, node.file, *type_parameter);
                    let Some(type_parameter_record) = host.node(type_parameter) else {
                        return false;
                    };
                    let NodeData::TypeParameterDeclaration(type_parameter_data) =
                        &type_parameter_record.data
                    else {
                        return false;
                    };
                    let type_parameter_name = NodeRef::new(
                        type_parameter.arena,
                        type_parameter.file,
                        type_parameter_data.name,
                    );
                    let Some(type_parameter_name_record) = host.node(type_parameter_name) else {
                        return false;
                    };
                    let NodeData::Identifier(type_parameter_identifier) =
                        &type_parameter_name_record.data
                    else {
                        return false;
                    };
                    type_parameter_record.kind == SyntaxKind::TypeParameter
                        && type_parameter_record.flags.0 == 0
                        && type_parameter_record.parent == Some(node.node)
                        && type_parameter_name_record.kind == SyntaxKind::Identifier
                        && type_parameter_name_record.flags.0 == 0
                        && type_parameter_name_record.parent == Some(type_parameter.node)
                        && type_parameter_identifier.flow_node.is_none()
                        && type_parameter_identifier.text == identifier.text
                        && bound.symbol(type_parameter) == Some(parameter_symbol)
                        && parameter_symbol_record.check_flags() == CheckFlags::NONE
                        && parameter_symbol_record.name().as_bytes() == identifier.text.as_bytes()
                        && parameter_symbol_record.declarations()
                            == Some([type_parameter, parameter].as_slice())
                        && parameter_symbol_record.value_declaration() == Some(parameter)
                        && parameter_symbol_record.members().is_none()
                        && parameter_symbol_record.exports().is_none()
                        && parameter_symbol_record.parent().is_none()
                        && parameter_symbol_record.export_symbol().is_none()
                        && bound
                            .locals(node)
                            .and_then(|locals| store.symbol_table(locals))
                            .and_then(|locals| locals.get_source(&identifier.text))
                            == Some(parameter_symbol)
                })
        {
            return Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::GenericSignature(node),
            ));
        }
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
        let identity_node = if implicit_any_rest {
            name
        } else {
            peel_parenthesized_type(store, host, type_node)?
        };
        if !implicit_any_rest {
            let signature_type_record = match rest_tuple_element {
                Some(element) => preflight_node(store, host, element.identity_node)?,
                None => preflight_node(store, host, type_node)?,
            };
            if signature_type_record.kind == SyntaxKind::LiteralType {
                flags |= SignatureFlags::HAS_LITERAL_TYPES;
            }
        }
        parameters.push(FunctionParameterPlan {
            declaration: parameter,
            symbol: parameter_symbol,
            type_node,
            identity_node,
            null_literal_identity: !implicit_any_rest
                && is_null_literal_type(store, host, identity_node)?,
            optional,
            rest_tuple_element,
            implicit_any_rest,
        });
        if !optional && !implicit_any_rest {
            min_argument_count = parameters.len();
        }
    }

    let min_argument_count = i32::try_from(min_argument_count)
        .map_err(|_| invariant(FunctionTypeInvariant::Capacity(node)))?;
    let return_identity_node = peel_parenthesized_type(store, host, return_type)?;
    let type_parameters = plan_function_type_parameters(
        store,
        host,
        node,
        function.type_parameters.as_ref(),
        function.parameters.range.start,
        return_identity_node,
    )?;
    if !type_parameters.is_empty()
        && (flags != SignatureFlags::NONE
            || usize::try_from(min_argument_count).ok() != Some(parameters.len())
            || parameters
                .iter()
                .any(|parameter| parameter.rest_tuple_element.is_some()))
    {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(node),
        ));
    }
    if let Some(type_parameter) = type_parameters.first() {
        for parameter in &parameters {
            if function_type_parameter_reference_symbol(store, host, parameter.identity_node)?
                != type_parameter.symbol
            {
                return Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::GenericSignature(node),
                ));
            }
        }
    }
    let plan = FunctionTypePlan {
        node,
        symbol,
        members,
        call_symbol,
        alias_symbol,
        type_parameters,
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

fn plan_rest_tuple_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    function: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    tuple: NodeRef,
    token: NodeRef,
) -> Result<FunctionRestTupleElementPlan, FunctionTypeError> {
    let function_record = preflight_node(store, host, function)?;
    let NodeData::FunctionTypeNode(function_data) = &function_record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(function)));
    };
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    };
    let token_record = preflight_node(store, host, token)?;
    let parameter_name_record = preflight_node(store, host, parameter_name)?;
    if token_record.kind != SyntaxKind::DotDotDotToken
        || token_record.parent != Some(parameter.node)
        || token_record.range.start < parameter_record.range.start
        || token_record.range.end > parameter_name_record.range.start
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    }
    if function_data.parameters.nodes.as_slice() != [parameter.node]
        || parameter_data.question_token.is_some()
    {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::RestParameter(parameter),
        ));
    }

    let tuple_record = preflight_node(store, host, tuple)?;
    let NodeData::TupleTypeNode(tuple_data) = &tuple_record.data else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::RestParameter(parameter),
        ));
    };
    if tuple_record.kind != SyntaxKind::TupleType
        || tuple_record.parent != Some(parameter.node)
        || tuple_data.elements.range != tuple_record.range
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    }
    let [element] = tuple_data.elements.nodes.as_slice() else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::RestParameter(parameter),
        ));
    };
    let declaration = NodeRef::new(tuple.arena, tuple.file, *element);
    let declaration_record = preflight_node(store, host, declaration)?;
    let NodeData::NamedTupleMember(member) = &declaration_record.data else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::RestParameter(parameter),
        ));
    };
    if declaration_record.kind != SyntaxKind::NamedTupleMember
        || declaration_record.parent != Some(tuple.node)
        || declaration_record.range.start < tuple_record.range.start
        || declaration_record.range.end > tuple_record.range.end
        || member.symbol.is_some()
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    }
    if member.dot_dot_dot_token.is_some() || member.question_token.is_some() {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::RestParameter(parameter),
        ));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, member.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(_) = &name_record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    };
    let element_type = NodeRef::new(declaration.arena, declaration.file, member.type_);
    let element_type_record = preflight_node(store, host, element_type)?;
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.range.start < declaration_record.range.start
        || name_record.range.end > declaration_record.range.end
        || element_type_record.parent != Some(declaration.node)
        || element_type_record.range.start < name_record.range.end
        || element_type_record.range.end > declaration_record.range.end
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameter(
            parameter,
        )));
    }
    let identity_node = peel_parenthesized_type(store, host, element_type)?;
    Ok(FunctionRestTupleElementPlan {
        declaration,
        name,
        identity_node,
        null_literal_identity: is_null_literal_type(store, host, identity_node)?,
    })
}

fn plan_function_type_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    function: NodeRef,
    parameters: Option<&NodeList>,
    value_parameters_start: ts_core::TextPos,
    return_type: NodeRef,
) -> Result<Vec<FunctionTypeParameterPlan>, FunctionTypeError> {
    let Some(parameters) = parameters else {
        return Ok(Vec::new());
    };
    let [parameter_node] = parameters.nodes.as_slice() else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(function),
        ));
    };
    let function_record = preflight_node(store, host, function)?;
    if parameters.range.start < function_record.range.start
        || parameters.range.end > value_parameters_start
        || parameters.range.start >= parameters.range.end
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(function)));
    }

    let mut checked = HashSet::new();
    let symbols =
        explicit_type_parameter_symbols(store, host, function, Some(parameters), &mut checked)?;
    let [symbol] = symbols.as_slice() else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(function),
        ));
    };
    let declaration = NodeRef::new(function.arena, function.file, *parameter_node);
    let declaration_record = preflight_node(store, host, declaration)?;
    let NodeData::TypeParameterDeclaration(parameter) = &declaration_record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(declaration)));
    };
    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(declaration)));
    };
    let owner = store
        .symbol(*symbol)
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidSyntax(declaration)))?;
    if declaration_record.kind != SyntaxKind::TypeParameter
        || declaration_record.parent != Some(function.node)
        || declaration_record.flags.0 & NODE_FLAG_JSDOC != 0
        || declaration_record.range.start < parameters.range.start
        || declaration_record.range.end > parameters.range.end
        || parameter.default_type.is_some()
        || parameter.expression.is_some()
        || parameter.modifiers.is_some()
        || parameter.symbol.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || owner.flags() != SymbolFlags::TYPE_PARAMETER
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some(identifier.text.as_str())
        || owner.declarations() != Some(&[declaration])
        || owner.value_declaration().is_some()
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(*symbol) != Some(*symbol)
    {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(function),
        ));
    }
    let (constraint, outer_symbol) = match parameter.constraint {
        Some(constraint) => {
            let constraint = NodeRef::new(function.arena, function.file, constraint);
            let constraint_record = preflight_node(store, host, constraint)?;
            if constraint_record.parent != Some(declaration.node)
                || constraint_record.range.start < declaration_record.range.start
                || constraint_record.range.end > declaration_record.range.end
            {
                return Err(invariant(FunctionTypeInvariant::InvalidSyntax(constraint)));
            }

            let outer_symbol = function_type_parameter_reference_symbol(store, host, constraint)?;
            if outer_symbol == *symbol {
                return Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::GenericSignature(function),
                ));
            }
            preflight_type_parameter_symbol(store, host, outer_symbol, &mut checked)?;
            let outer_declaration = store
                .symbol(outer_symbol)
                .and_then(|record| record.declarations())
                .and_then(|declarations| match declarations {
                    [declaration] => Some(*declaration),
                    _ => None,
                })
                .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidSyntax(constraint)))?;
            if !function_type_parameter_is_outer(store, function, outer_declaration) {
                return Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::GenericSignature(function),
                ));
            }
            (Some(constraint), Some(outer_symbol))
        }
        None => (None, None),
    };
    if function_type_parameter_reference_symbol(store, host, return_type)? != *symbol {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(function),
        ));
    }
    Ok(vec![FunctionTypeParameterPlan {
        declaration,
        symbol: *symbol,
        constraint,
        outer_symbol,
    }])
}

fn function_type_parameter_reference_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    reference: NodeRef,
) -> Result<SemanticSymbolId, FunctionTypeError> {
    let record = preflight_node(store, host, reference)?;
    let NodeData::TypeReferenceNode(data) = &record.data else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(reference),
        ));
    };
    if record.kind != SyntaxKind::TypeReference || data.type_arguments.is_some() {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(reference),
        ));
    }
    let name = NodeRef::new(reference.arena, reference.file, data.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(reference),
        ));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(reference.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
    {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(reference)));
    }
    let symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(DeclaredTypeError::from)?
        .ok_or(FunctionTypeError::Unsupported(
            FunctionTypeUnsupported::GenericSignature(reference),
        ))?;
    if store.get_merged_symbol(symbol) != Some(symbol) {
        return Err(invariant(FunctionTypeInvariant::InvalidSyntax(reference)));
    }
    Ok(symbol)
}

fn function_type_parameter_is_outer(
    store: &CanonicalTypeMapperStore,
    function: NodeRef,
    declaration: NodeRef,
) -> bool {
    let Some(SourceNodeParent::Parent(container)) = store.source_node_parent(declaration) else {
        return false;
    };
    let mut current = function;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) else {
            return false;
        };
        if parent == container {
            return true;
        }
        current = parent;
    }
    false
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
    let published_parameter_types = store.callable_signature_parameter_types(signature);

    let is_barrier = record.object_flags()
        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && object.structured == StructuredTypeData::default();
    if is_barrier {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
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
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
        {
            return Err(invariant(FunctionTypeInvariant::InvalidTypeCache(
                plan.node,
            )));
        }
        return Ok(FunctionTypeState::ActiveParameters { type_, signature });
    }
    let Some(published_parameter_types) = published_parameter_types else {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            plan.node,
        )));
    };
    if published_parameter_types.len() != plan.parameters.len() {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            plan.node,
        )));
    }
    for (parameter, expected) in plan.parameters.iter().zip(published_parameter_types) {
        validate_parameter_links(store, plan, parameter, *expected)?;
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
    if store.source_node_kind(declaration) == Some(SyntaxKind::Parameter) {
        return source_jsdoc_function_type_display_projection(store, host, type_, declaration);
    }
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
    let signature_id = signature;
    let signature = store
        .signature(signature_id)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let signature_parameter_types = store
        .callable_signature_parameter_types(signature_id)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let return_type = signature.resolved_return_type();
    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for (index, parameter) in plan.parameters.iter().enumerate() {
        let value_type = signature_parameter_types
            .get(index)
            .copied()
            .ok_or(FunctionTypeDisplayError::Malformed)?;
        let parameter_node = host
            .node(parameter.declaration)
            .ok_or(FunctionTypeDisplayError::Malformed)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
            return Err(FunctionTypeDisplayError::Malformed);
        };
        let name = parameter.rest_tuple_element.map_or_else(
            || {
                NodeRef::new(
                    parameter.declaration.arena,
                    parameter.declaration.file,
                    parameter_data.name,
                )
            },
            |element| element.name,
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

fn source_jsdoc_function_type_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    declaration: NodeRef,
) -> Result<ValidatedSingleCallSignatureDisplay, FunctionTypeDisplayError> {
    if validate_stored_source_jsdoc_function_type(store, type_).is_none() {
        return Err(FunctionTypeDisplayError::Malformed);
    }
    let (arena, bound) = host
        .source(declaration)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let parameter = host
        .node(declaration)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
        return Err(FunctionTypeDisplayError::Malformed);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let Some(NodeData::Identifier(identifier)) = host.node(name).map(|node| &node.data) else {
        return Err(FunctionTypeDisplayError::Malformed);
    };
    let Some(SourceNodeParent::Parent(callable)) = store.source_node_parent(declaration) else {
        return Err(FunctionTypeDisplayError::Malformed);
    };
    let comments = plan_javascript_source_jsdoc(arena, bound.source_file())
        .map_err(|_| FunctionTypeDisplayError::Malformed)?;
    let annotation = comments
        .callable_declaration(arena, callable)
        .and_then(|callable| callable.parameter(&identifier.text))
        .and_then(super::jsdoc::PlannedJsDocParameter::type_)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let JsDocType::Function(function) = annotation.type_() else {
        return Err(FunctionTypeDisplayError::Malformed);
    };
    let signature = store
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let record = store
        .signature(signature)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    let parameter_types = store
        .callable_signature_parameter_types(signature)
        .ok_or(FunctionTypeDisplayError::Malformed)?;
    if function.parameters().len() != parameter_types.len() {
        return Err(FunctionTypeDisplayError::Malformed);
    }
    let parameters = function
        .parameters()
        .iter()
        .zip(parameter_types)
        .map(
            |(parameter, value_type)| ValidatedSingleCallParameterDisplay {
                name: parameter.name().to_owned(),
                value_type: *value_type,
                optional: parameter.is_optional(),
            },
        )
        .collect();
    Ok(ValidatedSingleCallSignatureDisplay {
        owner: type_,
        parameters,
        return_type: record.resolved_return_type(),
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
    let mut cold_type_parameters = HashSet::new();
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
            for parameter in &plan.type_parameters {
                for symbol in parameter.outer_symbol.into_iter().chain([parameter.symbol]) {
                    if store
                        .declared_type_links(symbol)
                        .and_then(|links| links.declared_type)
                        .is_none()
                    {
                        cold_type_parameters.insert(symbol);
                    }
                }
            }
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
        || !store.try_reserve_callable_signature_parameter_types(plans.len())
    {
        return Err(invariant(FunctionTypeInvariant::Capacity(first.node)));
    }
    let type_allocations = cold
        .checked_add(cold_type_parameters.len())
        .ok_or_else(|| invariant(FunctionTypeInvariant::Capacity(first.node)))?;
    Ok((type_allocations, aliases, strict_optional_unions))
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
    let type_parameters = resolve_function_type_parameters(store, plan)?;
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
            type_parameters,
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

fn resolve_function_type_parameters(
    store: &mut CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
) -> Result<Vec<TypeId>, FunctionTypeError> {
    let mut resolved = Vec::with_capacity(plan.type_parameters.len());
    let no_constraint = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.no_constraint_type)
        .ok_or_else(|| invariant(FunctionTypeInvariant::Publication(plan.node)))?;
    for parameter in &plan.type_parameters {
        if parameter.constraint.is_some() != parameter.outer_symbol.is_some() {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        }
        let constraint = parameter.outer_symbol.map_or(no_constraint, |symbol| {
            execute_type_parameter(store, symbol)
        });
        let inner = execute_type_parameter(store, parameter.symbol);
        if parameter.outer_symbol.is_some_and(|symbol| {
            cached_ordinary_type_parameter_owner(store, constraint) != Some(symbol)
        }) || cached_ordinary_type_parameter_owner(store, inner) != Some(parameter.symbol)
        {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        }
        let Some(TypeData::TypeParameter(data)) = store.type_payload(inner).map(TypeRecord::data)
        else {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        };
        if data
            .constraint
            .is_some_and(|existing| existing != constraint)
            || data
                .resolved_default_type
                .is_some_and(|default_type| default_type != no_constraint)
            || data.target.is_some()
            || data.mapper.is_some()
            || data.is_this_type
        {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        }
        if (data.constraint != Some(constraint)
            || data.resolved_default_type != Some(no_constraint))
            && !store.set_type_parameter_resolution(
                inner,
                Some(constraint),
                None,
                None,
                Some(no_constraint),
            )
        {
            return Err(invariant(FunctionTypeInvariant::Publication(plan.node)));
        }
        resolved.push(inner);
    }
    Ok(resolved)
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
    if plan.parameters.is_empty() {
        let published = store
            .set_callable_signature_parameter_types_batch(vec![(pending.signature, Vec::new())]);
        assert!(
            published,
            "zero-parameter callable provenance was prevalidated and reserved"
        );
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
            let cached_base = function_parameter_base_type(store, parameter).ok_or_else(|| {
                invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                ))
            })?;
            let supplied_base = if parameter.implicit_any_rest {
                cached_annotation_identity(store, parameter.type_node, false)
                    .filter(|dependency| dependency == base)
                    .map(|_| cached_base)
                    .ok_or_else(|| {
                        invariant(FunctionTypeInvariant::InvalidParameterCache(
                            parameter.declaration,
                        ))
                    })?
            } else {
                *base
            };
            if cached_base != supplied_base
                || store
                    .validate_cached_array_capability_prepared(
                        supplied_base,
                        global_types,
                        prepared,
                    )
                    .is_err()
                || planned_signature_parameter_type(store, parameter, supplied_base).is_none()
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
        }
    }

    let mut resolved = Vec::with_capacity(parameter_count);
    let mut expected_parameter_types = Vec::with_capacity(pending.len());
    for function in pending {
        let signature = exact_signature_link(store, function.plan.node)?;
        let mut function_parameter_types = Vec::with_capacity(function.plan.parameters.len());
        for (parameter, base) in function.plan.parameters.iter().zip(&function.base_types) {
            let base = if parameter.implicit_any_rest {
                function_parameter_base_type(store, parameter).ok_or_else(|| {
                    invariant(FunctionTypeInvariant::InvalidParameterCache(
                        parameter.declaration,
                    ))
                })?
            } else {
                *base
            };
            let type_ = if strict && parameter.optional {
                let already_contains_undefined = base == undefined
                    || store.type_payload(base).is_some_and(|record| {
                        matches!(
                            record.data(),
                            TypeData::Union(union) if union.union.types.contains(&undefined)
                        )
                    });
                if already_contains_undefined {
                    base
                } else {
                    match global_types {
                        Some(global_types) => store.literal_union_type_prepared_with_global_types(
                            global_types,
                            &[base, undefined],
                            None,
                            prepared,
                        )?,
                        None => {
                            store.literal_union_type_prepared(&[base, undefined], None, prepared)?
                        }
                    }
                }
            } else {
                base
            };
            if store
                .validate_cached_array_capability_prepared(type_, global_types, prepared)
                .is_err()
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
            let signature_type = planned_signature_parameter_type(store, parameter, type_)
                .ok_or_else(|| {
                    invariant(FunctionTypeInvariant::InvalidParameterCache(
                        parameter.declaration,
                    ))
                })?;
            if store
                .validate_cached_array_capability_prepared(signature_type, global_types, prepared)
                .is_err()
            {
                return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
            resolved.push((parameter.symbol, type_));
            function_parameter_types.push(signature_type);
        }
        expected_parameter_types.push((signature, function_parameter_types));
    }
    let provenance = store.set_callable_signature_parameter_types_batch(expected_parameter_types);
    assert!(
        provenance,
        "prevalidated function parameter provenance publication is infallible"
    );
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
    if store.source_node_kind(declaration) == Some(SyntaxKind::Parameter) {
        return if branded {
            validate_stored_source_jsdoc_function_type(store, type_).map_or(
                StoredFunctionTypeValidation::Malformed,
                StoredFunctionTypeValidation::Valid,
            )
        } else {
            not_function()
        };
    }
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
    let Some(type_parameter_edges) = valid_stored_function_type_parameters(
        store,
        declaration,
        signature_record,
        return_identity_node,
    ) else {
        return StoredFunctionTypeValidation::Malformed;
    };
    let expected_parameter_types = store.callable_signature_parameter_types(signature);
    let mut parameter_edges =
        Vec::with_capacity(signature_record.parameters().len() + type_parameter_edges.len());
    parameter_edges.extend(type_parameter_edges);
    let mut default_parameter_count = 0usize;
    let parameters_valid =
        signature_record
            .parameters()
            .iter()
            .enumerate()
            .all(|(index, parameter)| {
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
                        let resolved_type =
                            links.resolved_type.expect("the branch checked the type");
                        let expected = expected_parameter_types
                            .and_then(|types| types.get(index))
                            .copied();
                        let valid = links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(resolved_type),
                                ..ValueSymbolLinks::default()
                            })
                            && expected.is_some_and(|expected| {
                                expected == resolved_type
                                    || signature_record.parameters().len() == 1
                                        && signature_record.min_argument_count() == 1
                                        && stored_rest_tuple_parameter_type(
                                            store,
                                            declaration,
                                            resolved_type,
                                        ) == Some(expected)
                            });
                        if valid {
                            parameter_edges.push(resolved_type);
                            if let Some(expected) = expected.filter(|type_| *type_ != resolved_type)
                            {
                                parameter_edges.push(expected);
                            }
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
                        store.source_node_parent(declaration)
                            == Some(SourceNodeParent::Parent(owner))
                    })
                    && links_valid
            });
    let parameters_unique = signature_record
        .parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature_record.parameters()[..index].contains(parameter));
    let rest_valid = !signature_record.has_rest_parameter()
        || !signature_record.parameters().is_empty()
            && usize::try_from(signature_record.min_argument_count())
                .is_ok_and(|minimum| minimum < signature_record.parameters().len())
            && expected_parameter_types
                .is_none_or(|types| types.last().copied() == implicit_any_array_type(store));
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
        || signature_record.flags().bits()
            & !(SignatureFlags::HAS_LITERAL_TYPES | SignatureFlags::HAS_REST_PARAMETER).bits()
            != 0
        || signature_record.min_argument_count() < 0
        || usize::try_from(signature_record.min_argument_count()).map_or(true, |minimum| {
            minimum > signature_record.parameters().len()
        })
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.declaration() != Some(declaration)
        || signature_record.this_parameter().is_some()
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || !parameters_valid
        || !rest_valid
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
            && expected_parameter_types.is_none()
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
        if expected_parameter_types.is_some()
            || signature_record.resolved_return_type().is_some()
            || store.signature_has_circular_return_type(signature)
        {
            return StoredFunctionTypeValidation::Malformed;
        }
        return StoredFunctionTypeValidation::Pending;
    }
    if expected_parameter_types
        .is_none_or(|types| types.len() != signature_record.parameters().len())
    {
        return StoredFunctionTypeValidation::Malformed;
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
    let expected_type_parameters = plan
        .type_parameters
        .iter()
        .map(|parameter| {
            store
                .declared_type_links(parameter.symbol)
                .and_then(|links| links.declared_type)
                .filter(|type_| {
                    cached_ordinary_type_parameter_owner(store, *type_) == Some(parameter.symbol)
                })
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| invariant(FunctionTypeInvariant::InvalidSignatureCache(plan.node)))?;
    if record.flags() != plan.flags
        || record.min_argument_count() != plan.min_argument_count
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(plan.node)
        || record.type_parameters() != expected_type_parameters.as_slice()
        || valid_stored_function_type_parameters(
            store,
            plan.node,
            record,
            plan.return_identity_node,
        )
        .is_none()
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

fn valid_stored_function_type_parameters(
    store: &CanonicalTypeMapperStore,
    function: NodeRef,
    signature: &Signature,
    return_annotation: NodeRef,
) -> Option<Vec<TypeId>> {
    let [type_parameter] = signature.type_parameters() else {
        return signature.type_parameters().is_empty().then(Vec::new);
    };
    if signature.flags() != SignatureFlags::NONE
        || usize::try_from(signature.min_argument_count()).ok()
            != Some(signature.parameters().len())
        || store.source_node_kind(return_annotation) != Some(SyntaxKind::TypeReference)
        || store.source_node_parent(return_annotation) != Some(SourceNodeParent::Parent(function))
    {
        return None;
    }
    let symbol = cached_ordinary_type_parameter_owner(store, *type_parameter)?;
    let symbol_record = store.symbol(symbol)?;
    let [declaration] = symbol_record.declarations()? else {
        return None;
    };
    if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_node_parent(*declaration) != Some(SourceNodeParent::Parent(function))
    {
        return None;
    }
    let TypeData::TypeParameter(data) = store.type_payload(*type_parameter)?.data() else {
        return None;
    };
    let no_constraint = store.intrinsic_bootstrap()?.no_constraint_type;
    if data.resolved_default_type != Some(no_constraint)
        || data.target.is_some()
        || data.mapper.is_some()
        || data.is_this_type
    {
        return None;
    }
    let outer = match store.source_direct_type_annotation(*declaration) {
        Some(annotation) => {
            let outer = data.constraint?;
            let outer_symbol = cached_ordinary_type_parameter_owner(store, outer)?;
            let [outer_declaration] = store.symbol(outer_symbol)?.declarations()? else {
                return None;
            };
            if outer == *type_parameter
                || store.source_node_kind(annotation) != Some(SyntaxKind::TypeReference)
                || store.source_node_parent(annotation)
                    != Some(SourceNodeParent::Parent(*declaration))
                || !function_type_parameter_is_outer(store, function, *outer_declaration)
                || store.symbol_node_links(annotation).is_some_and(|links| {
                    links != &SymbolNodeLinks::default()
                        && links
                            != &SymbolNodeLinks {
                                resolved_symbol: Some(outer_symbol),
                            }
                })
                || store.type_node_links(annotation).is_some_and(|links| {
                    links != &TypeNodeLinks::default()
                        && links
                            != &TypeNodeLinks {
                                resolved_type: Some(outer),
                                outer_type_parameters: None,
                            }
                })
            {
                return None;
            }
            Some(outer)
        }
        None if data.constraint == Some(no_constraint) => None,
        None => return None,
    };
    if store
        .symbol_node_links(return_annotation)
        .is_some_and(|links| {
            links != &SymbolNodeLinks::default()
                && links
                    != &SymbolNodeLinks {
                        resolved_symbol: Some(symbol),
                    }
        })
        || store
            .type_node_links(return_annotation)
            .is_some_and(|links| {
                links != &TypeNodeLinks::default()
                    && links
                        != &TypeNodeLinks {
                            resolved_type: Some(*type_parameter),
                            outer_type_parameters: None,
                        }
            })
    {
        return None;
    }
    let mut edges = vec![*type_parameter];
    edges.extend(outer);
    Some(edges)
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

fn planned_signature_parameter_type(
    store: &CanonicalTypeMapperStore,
    parameter: &FunctionParameterPlan,
    value_type: TypeId,
) -> Option<TypeId> {
    let Some(element) = parameter.rest_tuple_element else {
        return Some(value_type);
    };
    let signature_type =
        stored_rest_tuple_parameter_type(store, parameter.declaration, value_type)?;
    let shape = store.canonical_tuple_shape(value_type).ok().flatten()?;
    let [info] = shape.element_infos() else {
        return None;
    };
    if info.labeled_declaration() != Some(element.declaration)
        || cached_annotation_identity(store, element.identity_node, element.null_literal_identity)
            != Some(signature_type)
    {
        return None;
    }
    Some(signature_type)
}

fn stored_rest_tuple_parameter_type(
    store: &CanonicalTypeMapperStore,
    parameter: NodeRef,
    value_type: TypeId,
) -> Option<TypeId> {
    let shape = store.canonical_tuple_shape(value_type).ok().flatten()?;
    let [element_type] = shape.element_types() else {
        return None;
    };
    let [info] = shape.element_infos() else {
        return None;
    };
    let declaration = info.labeled_declaration()?;
    let SourceNodeParent::Parent(tuple) = store.source_node_parent(declaration)? else {
        return None;
    };
    if shape.is_readonly()
        || shape.min_length() != 1
        || shape.fixed_length() != 1
        || info.flags() != ElementFlags::REQUIRED
        || store.source_node_kind(declaration) != Some(SyntaxKind::NamedTupleMember)
        || store.source_node_kind(tuple) != Some(SyntaxKind::TupleType)
        || store.source_node_parent(tuple) != Some(SourceNodeParent::Parent(parameter))
        || store
            .type_node_links(tuple)
            .and_then(|links| links.resolved_type)
            != Some(value_type)
    {
        return None;
    }
    Some(*element_type)
}

fn validate_parameter_links(
    store: &CanonicalTypeMapperStore,
    plan: &FunctionTypePlan,
    parameter: &FunctionParameterPlan,
    expected: TypeId,
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
    if planned_signature_parameter_type(store, parameter, resolved) != Some(expected)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(resolved),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invariant(FunctionTypeInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    let base = function_parameter_base_type(store, parameter).ok_or_else(|| {
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

fn function_parameter_base_type(
    store: &CanonicalTypeMapperStore,
    parameter: &FunctionParameterPlan,
) -> Option<TypeId> {
    if parameter.implicit_any_rest {
        implicit_any_array_type(store)
    } else {
        cached_annotation_identity(
            store,
            parameter.identity_node,
            parameter.null_literal_identity,
        )
    }
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

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerDiagnostics, IntrinsicBootstrapOptions,
        global_types::initialize_global_library_types,
        production::GlobalMergeCompletion,
        type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    fn fixture(source: &str, file: FileId) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-function-type.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
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
        Fixture {
            parsed,
            file,
            bound,
            store,
        }
    }

    fn generic_function_node(fixture: &Fixture) -> NodeRef {
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionTypeNode(function) = &record.data else {
                    return None;
                };
                function
                    .type_parameters
                    .as_ref()
                    .map(|_| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap()
    }

    #[test]
    fn constrained_outer_parameter_signature_preserves_return_identity_cold_and_warm() {
        let mut fixture = fixture(
            "type Outer<x> = (<o extends x>() => o) extends (() => infer o) ? o : never;",
            FileId::new(95_001),
        );
        let function = generic_function_node(&fixture);
        let plan = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_function_type(&fixture.store, &host, function, None, false, None).unwrap()
        };
        let [planned] = plan.type_parameters.as_slice() else {
            panic!("expected one constrained signature type parameter")
        };
        let outer_symbol = planned
            .outer_symbol
            .expect("the constrained signature must retain its outer parameter");
        assert!(planned.constraint.is_some());
        assert!(plan.parameters.is_empty());
        assert!(fixture.store.declared_type_links(planned.symbol).is_none());
        assert!(fixture.store.declared_type_links(outer_symbol).is_none());

        reserve_function_type_capacities(&mut fixture.store, &[&plan]).unwrap();
        let pending = begin_function_type(&mut fixture.store, &plan)
            .unwrap()
            .unwrap();
        finalize_function_structure(&mut fixture.store, &plan, pending).unwrap();
        let signature = fixture.store.signature(pending.signature).unwrap();
        let [inner] = signature.type_parameters() else {
            panic!("expected the exact constrained inner identity")
        };
        let inner = *inner;
        let outer = fixture
            .store
            .declared_type_links(outer_symbol)
            .unwrap()
            .declared_type
            .unwrap();
        let TypeData::TypeParameter(parameter) = fixture.store.type_payload(inner).unwrap().data()
        else {
            panic!("expected a canonical type parameter")
        };
        assert_eq!(parameter.constraint, Some(outer));
        assert_eq!(
            parameter.resolved_default_type,
            Some(
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .no_constraint_type
            )
        );
        assert!(matches!(
            validate_stored_function_type(&fixture.store, pending.type_),
            StoredFunctionTypeValidation::Valid(_)
        ));

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_return_type_of_signature(pending.signature),
                Ok(inner)
            );
        }
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            begin_function_type(&mut fixture.store, &plan),
            Ok(Err(pending.type_))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unconstrained_generic_function_parameters_preserve_binder_identity_cold_and_warm() {
        let mut fixture = fixture(
            "declare let value: <Value>(input: Value) => Value;",
            FileId::new(95_002),
        );
        let function = generic_function_node(&fixture);
        let plan = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_function_type(&fixture.store, &host, function, None, false, None).unwrap()
        };
        let [planned] = plan.type_parameters.as_slice() else {
            panic!("expected one binder-owned generic signature parameter")
        };
        let [value] = plan.parameters.as_slice() else {
            panic!("expected one binder-owned generic value parameter")
        };
        assert!(planned.constraint.is_none());
        assert!(planned.outer_symbol.is_none());
        assert_eq!(plan.min_argument_count, 1);
        assert!(fixture.store.declared_type_links(planned.symbol).is_none());

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        let FunctionTypeState::Resolved { signature, .. } =
            function_type_state(&fixture.store, &plan, false).unwrap()
        else {
            panic!("the generic function signature must be fully resolved")
        };
        let signature_record = fixture.store.signature(signature).unwrap();
        let [inner] = signature_record.type_parameters() else {
            panic!("the signature must retain its binder-owned type parameter")
        };
        let inner = *inner;
        let no_constraint = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        let TypeData::TypeParameter(parameter) = fixture.store.type_payload(inner).unwrap().data()
        else {
            panic!("the generic signature parameter must retain its canonical identity")
        };
        assert_eq!(
            cached_ordinary_type_parameter_owner(&fixture.store, inner),
            Some(planned.symbol)
        );
        assert_eq!(parameter.constraint, Some(no_constraint));
        assert_eq!(parameter.resolved_default_type, Some(no_constraint));
        assert_eq!(signature_record.parameters(), [value.symbol].as_slice());
        assert_eq!(signature_record.min_argument_count(), 1);
        assert_eq!(
            fixture.store.value_symbol_links(value.symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(inner),
                ..ValueSymbolLinks::default()
            }),
        );
        assert!(matches!(
            validate_stored_function_type(&fixture.store, function_type),
            StoredFunctionTypeValidation::Valid(_)
        ));

        {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_return_type_of_signature(signature),
                Ok(inner),
            );
        }
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            begin_function_type(&mut fixture.store, &plan),
            Ok(Err(function_type)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn constrained_generic_function_value_parameters_preserve_outer_constraint() {
        let mut fixture = fixture(
            concat!(
                "type Outer<Value> = ",
                "(<Inner extends Value>(input: Inner) => Inner) ",
                "extends ((input: Value) => infer Result) ? Result : never;",
            ),
            FileId::new(95_003),
        );
        let function = generic_function_node(&fixture);
        let plan = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_function_type(&fixture.store, &host, function, None, false, None).unwrap()
        };
        let [planned] = plan.type_parameters.as_slice() else {
            panic!("expected one constrained generic type parameter")
        };
        let outer_symbol = planned.outer_symbol.unwrap();
        assert!(planned.constraint.is_some());
        assert_eq!(plan.parameters.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        let FunctionTypeState::Resolved { signature, .. } =
            function_type_state(&fixture.store, &plan, false).unwrap()
        else {
            panic!("the constrained generic function must publish its signature")
        };
        let [inner] = fixture
            .store
            .signature(signature)
            .unwrap()
            .type_parameters()
        else {
            panic!("the constrained generic signature must own one type parameter")
        };
        let outer = fixture
            .store
            .declared_type_links(outer_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::TypeParameter(parameter) = fixture.store.type_payload(*inner).unwrap().data()
        else {
            panic!("the signature type parameter must preserve its constraint")
        };
        assert_eq!(parameter.constraint, Some(outer));
        assert!(matches!(
            validate_stored_function_type(&fixture.store, function_type),
            StoredFunctionTypeValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unconstrained_generic_function_rejects_poisoned_constraint_without_publication() {
        let mut fixture = fixture(
            "declare let value: <Value>(input: Value) => Value;",
            FileId::new(95_004),
        );
        let function = generic_function_node(&fixture);
        let plan = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_function_type(&fixture.store, &host, function, None, false, None).unwrap()
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        let inner = fixture
            .store
            .declared_type_links(plan.type_parameters[0].symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let no_constraint = bootstrap.no_constraint_type;
        let string = bootstrap.string_type;
        assert!(fixture.store.set_type_parameter_resolution(
            inner,
            Some(string),
            None,
            None,
            Some(no_constraint),
        ));
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            validate_stored_function_type(&fixture.store, function_type),
            StoredFunctionTypeValidation::Malformed,
        );
        assert!(begin_function_type(&mut fixture.store, &plan).is_err());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn malformed_generic_function_parameter_owners_fail_before_publication() {
        for mutation in 0..2 {
            let mut fixture = fixture(
                "declare let value: <Value>(input: Value) => Value;",
                FileId::new(95_005 + mutation),
            );
            let function = generic_function_node(&fixture);
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let plan =
                plan_function_type(&fixture.store, &host, function, None, false, None).unwrap();
            let parameter = plan.type_parameters[0].symbol;
            match mutation {
                0 => assert!(fixture.store.set_symbol_flags(
                    parameter,
                    SymbolFlags::TYPE_PARAMETER | SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                1 => assert!(fixture.store.set_symbol_relationships(
                    parameter,
                    None,
                    None,
                    Some(plan.symbol),
                    None,
                )),
                _ => unreachable!(),
            }
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(
                plan_function_type(&fixture.store, &host, function, None, false, None).is_err()
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn generic_type_and_value_parameter_collisions_are_authenticated_boundaries() {
        let mut fixture = fixture(
            "declare const parse: <def>(def: def) => def;",
            FileId::new(95_007),
        );
        let function = generic_function_node(&fixture);
        let NodeData::FunctionTypeNode(syntax) =
            &fixture.parsed.arena.get(function.node).unwrap().data
        else {
            panic!("the fixture must retain one generic function annotation")
        };
        let type_parameter = NodeRef::new(
            function.arena,
            function.file,
            syntax.type_parameters.as_ref().unwrap().nodes[0],
        );
        let parameter = NodeRef::new(function.arena, function.file, syntax.parameters.nodes[0]);
        let symbol = fixture.bound.symbol(type_parameter).unwrap();
        assert_eq!(fixture.bound.symbol(parameter), Some(symbol));
        assert_eq!(
            fixture.store.symbol(symbol).unwrap().flags(),
            SymbolFlags::TYPE_PARAMETER | SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_function_type(&fixture.store, &host, function, None, false, None),
            Err(FunctionTypeError::Unsupported(
                FunctionTypeUnsupported::GenericSignature(node)
            )) if node == function
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        assert!(fixture.store.set_symbol_flags(
            symbol,
            SymbolFlags::TYPE_PARAMETER
                | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                | SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        assert!(matches!(
            plan_function_type(&fixture.store, &host, function, None, false, None),
            Err(FunctionTypeError::Invariant(
                FunctionTypeInvariant::InvalidParameterSymbol(node)
            )) if node == parameter
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn unsupported_generic_function_signatures_fail_before_publication() {
        for (index, signature) in [
            "<o extends string>() => o",
            "<o extends x>() => x",
            "<o>(value?: o) => o",
            "<o>(value: 'literal') => o",
            "<o extends x = x>() => o",
            "<o extends x, p extends x>() => o",
        ]
        .into_iter()
        .enumerate()
        {
            let source =
                format!("type Outer<x> = ({signature}) extends (() => infer o) ? o : never;");
            let fixture = fixture(&source, FileId::new(95_010 + u32::try_from(index).unwrap()));
            let function = generic_function_node(&fixture);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(matches!(
                plan_function_type(&fixture.store, &host, function, None, false, None),
                Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::GenericSignature(_)
                ))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }

    #[test]
    fn labeled_tuple_rest_preserves_parameter_value_and_expands_signature() {
        let mut fixture = fixture(
            "declare let value: (...args: [x: number]) => void;",
            FileId::new(95_020),
        );
        let function = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let plan = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            plan_function_type(&fixture.store, &host, function, None, false, None).unwrap()
        };
        let [parameter] = plan.parameters.as_slice() else {
            panic!("expected one expanded tuple parameter")
        };
        assert_eq!(plan.flags, SignatureFlags::NONE);
        assert_eq!(plan.min_argument_count, 1);
        assert!(parameter.rest_tuple_element.is_some());
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(parameter.type_node.node)
                .unwrap()
                .kind,
            SyntaxKind::TupleType
        );
        assert_eq!(
            fixture
                .store
                .symbol(parameter.symbol)
                .unwrap()
                .name()
                .as_utf8(),
            Some("args")
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        let tuple_type = fixture
            .store
            .value_symbol_links(parameter.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .type_node_links(parameter.type_node)
                .and_then(|links| links.resolved_type),
            Some(tuple_type)
        );
        let tuple = fixture
            .store
            .canonical_tuple_shape(tuple_type)
            .unwrap()
            .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(tuple.element_types(), [number]);
        let FunctionTypeState::Resolved { signature, .. } =
            function_type_state(&fixture.store, &plan, false).unwrap()
        else {
            panic!("expected resolved expanded function signature")
        };
        let signature_record = fixture.store.signature(signature).unwrap();
        assert_eq!(signature_record.parameters(), [parameter.symbol]);
        assert_eq!(signature_record.min_argument_count(), 1);
        assert!(!signature_record.has_rest_parameter());
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([number].as_slice())
        );
        assert!(matches!(
            validate_stored_function_type(&fixture.store, function_type),
            StoredFunctionTypeValidation::Valid(_)
        ));

        let projection = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            function_type_display_projection(&fixture.store, &host, function_type, None).unwrap()
        };
        assert_eq!(projection.parameters.len(), 1);
        assert_eq!(projection.parameters[0].name, "x");
        assert_eq!(projection.parameters[0].value_type, number);
        assert!(!projection.parameters[0].optional);

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let warm_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        assert_eq!(warm_type, function_type);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn implicit_any_rest_function_signatures_preserve_arity_and_replay_warm() {
        for (index, (signature_text, expected_minimum)) in [
            ("(...values) => void", 0),
            ("(first: number, ...values) => void", 1),
            ("(first: string, second?: number, ...values) => any", 1),
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!("declare let value: {signature_text};");
            let mut fixture = fixture(&source, FileId::new(95_040 + u32::try_from(index).unwrap()));
            let function = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let plan = {
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&fixture.parsed.arena, &fixture.bound)],
                    GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
                )
                .unwrap();
                plan_function_type(&fixture.store, &host, function, None, false, None)
                    .unwrap_or_else(|error| panic!("{signature_text}: {error:?}"))
            };
            let rest = plan.parameters.last().unwrap();
            let any_array = fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .empty_object_type;
            assert_eq!(plan.flags, SignatureFlags::HAS_REST_PARAMETER);
            assert_eq!(plan.min_argument_count, expected_minimum);
            assert!(rest.implicit_any_rest);
            assert!(rest.rest_tuple_element.is_none());

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let function_type = {
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&fixture.parsed.arena, &fixture.bound)],
                    GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
                )
                .unwrap();
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(function)
                .unwrap_or_else(|error| panic!("{signature_text}: {error:?}"))
            };
            let FunctionTypeState::Resolved { signature, .. } =
                function_type_state(&fixture.store, &plan, false).unwrap()
            else {
                panic!("{signature_text}: expected a resolved rest signature")
            };
            let signature_record = fixture.store.signature(signature).unwrap();
            assert!(signature_record.has_rest_parameter());
            assert_eq!(signature_record.min_argument_count(), expected_minimum);
            assert_eq!(
                fixture
                    .store
                    .callable_signature_parameter_types(signature)
                    .and_then(|types| types.last().copied()),
                Some(any_array)
            );
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(rest.symbol)
                    .and_then(|links| links.resolved_type),
                Some(any_array)
            );
            assert!(matches!(
                validate_stored_function_type(&fixture.store, function_type),
                StoredFunctionTypeValidation::Valid(_)
            ));

            let warm = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let replay = {
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&fixture.parsed.arena, &fixture.bound)],
                    GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
                )
                .unwrap();
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(function)
                .unwrap()
            };
            assert_eq!(replay, function_type);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn implicit_any_rest_function_signatures_reuse_the_global_array_identity() {
        let mut fixture = fixture(
            "interface IArguments {} interface Array<T> {} interface Object {} \
             interface Function {} interface String {} interface Number {} \
             interface Boolean {} interface RegExp {} interface ReadonlyArray<T> {} \
             interface ThisType<T> {} \
             declare let value: (first: number, ...values) => void;",
            FileId::new(95_043),
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let symbols = fixture
            .store
            .symbol_table(locals)
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in symbols {
            fixture.store.merge_global_symbol(globals, symbol).unwrap();
        }
        let global_types = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            initialize_global_library_types(&mut fixture.store, &host, globals, false).unwrap()
        };
        let function = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            assert!(matches!(
                plan_function_type(&fixture.store, &host, function, None, false, None),
                Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::RestParameter(_)
                ))
            ));
        }
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let function_type = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new_with_global_types(
                &mut fixture.store,
                &host,
                &global_types,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(function)
            .unwrap()
        };
        let signature = fixture
            .store
            .signature_links(function)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let rest = *fixture
            .store
            .signature(signature)
            .unwrap()
            .parameters()
            .last()
            .unwrap();
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(signature)
                .and_then(|types| types.last().copied()),
            Some(global_types.any_array_type)
        );
        assert_eq!(
            fixture
                .store
                .value_symbol_links(rest)
                .and_then(|links| links.resolved_type),
            Some(global_types.any_array_type)
        );
        assert!(matches!(
            validate_stored_function_type(&fixture.store, function_type),
            StoredFunctionTypeValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unsupported_tuple_rest_shapes_fail_before_publication() {
        for (index, signature) in [
            "(...args: [number]) => void",
            "(...args: [x?: number]) => void",
            "(...args: [x: number, y: string]) => void",
            "(...args: number[]) => void",
            "(prefix: string, ...args: [x: number]) => void",
            "(...args: [...number[]]) => void",
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!("declare let value: {signature};");
            let fixture = fixture(&source, FileId::new(95_030 + u32::try_from(index).unwrap()));
            let function = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();

            assert!(matches!(
                plan_function_type(&fixture.store, &host, function, None, false, None),
                Err(FunctionTypeError::Unsupported(
                    FunctionTypeUnsupported::RestParameter(_)
                ))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }
}
