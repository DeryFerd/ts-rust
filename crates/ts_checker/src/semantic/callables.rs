//! Syntax-neutral validation and consumer projections for exact callables.
//!
//! Callable families retain ownership of their syntax, binder provenance, and
//! publication protocol. This module only dispatches to those providers after
//! publication and normalizes the immutable views consumed by union/array
//! validation, type display, and signature relation. Keeping this boundary
//! free of `FunctionTypeNode` storage details lets later source-callable
//! providers participate without borrowing `FunctionType` provenance.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::SymbolFlags;

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    functions::{
        FunctionTypeDisplayError, StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
    source_callables::{
        SourceCallableDisplayError, SourceCallableFamily, StoredSourceCallableValidation,
        source_callable_display_projection, stored_source_callable_family,
        validate_stored_source_callable,
    },
    type_records::TypeData,
};

/// Provider family for an exact, independently validated callable object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CallableFamily {
    FunctionType,
    FunctionDeclaration,
    ArrowFunction,
    ObjectLiteralMethod,
    SourceFunctionOverloads,
    DeclaredCallSignatures,
}

impl From<SourceCallableFamily> for CallableFamily {
    fn from(family: SourceCallableFamily) -> Self {
        match family {
            SourceCallableFamily::FunctionDeclaration => Self::FunctionDeclaration,
            SourceCallableFamily::ArrowFunction => Self::ArrowFunction,
            SourceCallableFamily::ObjectLiteralMethod => Self::ObjectLiteralMethod,
        }
    }
}

/// Immutable signature view consumed by structural relation.
///
/// The provider has already proved the owner, signature, and parameter caches.
/// A return type remains optional because an otherwise resolved callable may
/// still require its provider-specific lazy-return path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallable {
    pub(super) owner: TypeId,
    pub(super) signature: SignatureId,
    pub(super) parameters: Vec<TypeId>,
    /// Raw final rest parameter type, kept separate from fixed positions.
    /// Providers may publish the canonical empty tuple to represent an
    /// exhausted contextual rest tail.
    pub(super) rest_parameter: Option<TypeId>,
    pub(super) min_argument_count: usize,
    pub(super) return_type: Option<TypeId>,
    pub(super) strict_variance_exempt: bool,
}

/// Store-only callable classification shared by cache validators and relation.
///
/// `edges` includes every semantic type dependency that the provider requires
/// graph validation to traverse. It is deliberately separate from the
/// relation projection: circular-return recovery, for example, retains an
/// annotation edge in addition to the signature's published return type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSingleCallableValidation {
    NotCallable,
    Pending {
        family: CallableFamily,
    },
    Valid {
        family: CallableFamily,
        callable: ValidatedSingleCallable,
        edges: Vec<TypeId>,
    },
    Malformed {
        family: CallableFamily,
    },
}

/// Syntax-neutral display data for one parameter of a validated single-call
/// signature. The semantic value type includes optional `undefined`; the
/// checked annotation can omit that implicit constituent in location-aware
/// display. The question mark and rest marker remain separate facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallParameterDisplay {
    pub(super) name: String,
    pub(super) value_type: TypeId,
    pub(super) annotation_type: Option<TypeId>,
    pub(super) optional: bool,
    pub(super) rest: bool,
}

/// Immutable display projection produced by a callable-family validator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallSignatureDisplay {
    pub(super) owner: TypeId,
    pub(super) signature: SignatureId,
    pub(super) parameters: Vec<ValidatedSingleCallParameterDisplay>,
    pub(super) return_type: Option<TypeId>,
}

/// Provider-specific reason that an admitted callable cannot be displayed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SingleCallableDisplayError {
    FunctionType(FunctionTypeDisplayError),
    SourceCallable(SourceCallableDisplayError),
    MalformedMethod,
}

/// Returns the installed provider brand without attempting cache validation.
///
/// Display uses this narrow query to preserve the distinction between a
/// branded provider value and an unbranded function-shaped object. Relation
/// and graph validation instead use [`validate_stored_single_callable`], which
/// deliberately detects malformed provider-shaped storage as well.
pub(super) fn single_callable_family(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<CallableFamily> {
    if super::instantiated_members::validate_instantiated_function_member_callable(store, type_)
        .is_some()
    {
        return Some(CallableFamily::FunctionType);
    }
    if store.type_has_function_type_provenance(type_) {
        Some(CallableFamily::FunctionType)
    } else {
        store
            .source_callable_provenance(type_)
            .map(|provenance| provenance.family.into())
    }
}

/// Validates an exact callable using only retained semantic-store state.
pub(super) fn validate_stored_single_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSingleCallableValidation {
    validate_stored_single_callable_with_array_targets(store, type_, None)
}

/// Keeps the caller's array targets while selecting an exact stored callable.
pub(super) fn validate_stored_single_callable_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> StoredSingleCallableValidation {
    match validate_stored_callable_set_with_array_targets(store, type_, array_targets) {
        StoredCallableSetValidation::NotCallable => StoredSingleCallableValidation::NotCallable,
        StoredCallableSetValidation::Pending { family } => {
            StoredSingleCallableValidation::Pending { family }
        }
        StoredCallableSetValidation::Malformed { family } => {
            StoredSingleCallableValidation::Malformed { family }
        }
        StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        } => {
            if projection.owner != type_ {
                return StoredSingleCallableValidation::Malformed { family };
            }
            if !projection.construct_signatures.is_empty() || projection.call_signatures.len() != 1
            {
                return StoredSingleCallableValidation::NotCallable;
            }
            let mut call_signatures = projection.call_signatures.into_vec();
            let Some(callable) = call_signatures.pop() else {
                return StoredSingleCallableValidation::Malformed { family };
            };
            StoredSingleCallableValidation::Valid {
                family,
                callable,
                edges,
            }
        }
    }
}

/// Provider dispatch used by the ordered callable-set boundary.
///
/// This remains separate from [`validate_stored_single_callable`] so the
/// single-call compatibility adapter can consume a set without recursively
/// dispatching back into itself. New callable families join the set dispatcher
/// only after their own syntax, provenance, and publication caches are proven.
pub(super) fn validate_stored_single_callable_provider(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSingleCallableValidation {
    match validate_stored_function_type(store, type_) {
        StoredFunctionTypeValidation::NotFunctionType => {}
        StoredFunctionTypeValidation::Pending => {
            return StoredSingleCallableValidation::Pending {
                family: CallableFamily::FunctionType,
            };
        }
        StoredFunctionTypeValidation::Malformed => {
            return StoredSingleCallableValidation::Malformed {
                family: CallableFamily::FunctionType,
            };
        }
        StoredFunctionTypeValidation::Valid(edges) => {
            let Some(callable) = validated_single_callable(store, type_) else {
                return StoredSingleCallableValidation::Malformed {
                    family: CallableFamily::FunctionType,
                };
            };
            return StoredSingleCallableValidation::Valid {
                family: CallableFamily::FunctionType,
                callable,
                edges,
            };
        }
    }
    match validate_stored_source_callable(store, type_) {
        StoredSourceCallableValidation::NotSourceCallable => {
            StoredSingleCallableValidation::NotCallable
        }
        validation => {
            let Some(family) =
                stored_source_callable_family(store, type_).map(CallableFamily::from)
            else {
                return StoredSingleCallableValidation::NotCallable;
            };
            match validation {
                StoredSourceCallableValidation::NotSourceCallable => {
                    StoredSingleCallableValidation::NotCallable
                }
                StoredSourceCallableValidation::Pending => {
                    StoredSingleCallableValidation::Pending { family }
                }
                StoredSourceCallableValidation::Malformed => {
                    StoredSingleCallableValidation::Malformed { family }
                }
                StoredSourceCallableValidation::Valid(edges) => {
                    let Some(callable) = validated_single_callable(store, type_) else {
                        return StoredSingleCallableValidation::Malformed { family };
                    };
                    StoredSingleCallableValidation::Valid {
                        family,
                        callable,
                        edges,
                    }
                }
            }
        }
    }
}

/// Produces the display overlay from the callable's source-owning provider.
pub(super) fn single_callable_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<Option<ValidatedSingleCallSignatureDisplay>, SingleCallableDisplayError> {
    if let Some(display) = super::instantiated_members::instantiated_function_member_display(
        store,
        host,
        type_,
        global_types.map(CanonicalArrayTargets::from_global_types),
    ) {
        return display
            .map(Some)
            .map_err(SingleCallableDisplayError::FunctionType);
    }
    let Some(family) = single_callable_family(store, type_) else {
        return fixed_method_display_projection(store, host, type_, global_types);
    };
    match family {
        CallableFamily::FunctionType => function_type_display_projection(
            store,
            host,
            type_,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )
        .map(Some)
        .map_err(SingleCallableDisplayError::FunctionType),
        CallableFamily::FunctionDeclaration
        | CallableFamily::ArrowFunction
        | CallableFamily::ObjectLiteralMethod => source_callable_display_projection(
            store,
            host,
            type_,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )
        .map(Some)
        .map_err(SingleCallableDisplayError::SourceCallable),
        CallableFamily::SourceFunctionOverloads | CallableFamily::DeclaredCallSignatures => {
            Ok(None)
        }
    }
}

/// Reads nonempty fixed method parameters after the source and stored owners agree.
pub(super) fn fixed_method_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<Option<ValidatedSingleCallSignatureDisplay>, SingleCallableDisplayError> {
    let invalid = || SingleCallableDisplayError::MalformedMethod;
    let Some(record) = store.type_payload(type_) else {
        return Ok(None);
    };
    let Some(method) = record.symbol() else {
        return Ok(None);
    };
    let method_record = store.symbol(method).ok_or_else(invalid)?;
    if !method_record.flags().contains(SymbolFlags::METHOD) {
        return Ok(None);
    }
    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    if let TypeData::Object(object) = record.data()
        && (object.target.is_some() || object.mapper.is_some())
    {
        let StoredCallableSetValidation::Valid {
            family: CallableFamily::DeclaredCallSignatures,
            projection,
            edges,
        } = validate_stored_callable_set_with_array_targets(store, type_, array_targets)
        else {
            return Err(invalid());
        };
        if projection.owner != type_ || !projection.construct_signatures.is_empty() {
            return Err(invalid());
        }
        for edge in edges {
            store
                .validate_cached_array_capability_with_pending_functions(array_targets, edge, &[])
                .map_err(|_| invalid())?;
        }
        let [callable] = projection.call_signatures.as_ref() else {
            return Ok(None);
        };
        let source = object.target.ok_or_else(invalid)?;
        if source == type_
            || object.mapper.is_none()
            || store.type_payload(source).and_then(|record| record.symbol()) != Some(method)
        {
            return Err(invalid());
        }
        let Some(source_display) =
            fixed_method_display_projection(store, host, source, global_types)?
        else {
            return Ok(None);
        };
        let signature = store.signature(callable.signature).ok_or_else(invalid)?;
        if source_display.owner != source
            || signature.target() != Some(source_display.signature)
            || signature.mapper() != object.mapper
            || source_display.parameters.len() != callable.parameters.len()
            || callable.min_argument_count != source_display.parameters.len()
            || callable.rest_parameter.is_some()
            || callable.return_type.is_none()
        {
            return Err(invalid());
        }
        // Keep declaration names and use the copy's mapped signature values.
        return Ok(Some(ValidatedSingleCallSignatureDisplay {
            owner: type_,
            signature: callable.signature,
            parameters: source_display
                .parameters
                .into_iter()
                .zip(&callable.parameters)
                .map(
                    |(source, &value_type)| ValidatedSingleCallParameterDisplay {
                        name: source.name,
                        value_type,
                        annotation_type: None,
                        optional: source.optional,
                        rest: source.rest,
                    },
                )
                .collect(),
            return_type: callable.return_type,
        }));
    }
    let declaration = method_record.value_declaration().ok_or_else(invalid)?;
    let node = host.node(declaration).ok_or_else(invalid)?;
    let parent = NodeRef::new(
        declaration.arena,
        declaration.file,
        node.parent.ok_or_else(invalid)?,
    );
    let parent_node = host.node(parent).ok_or_else(invalid)?;
    let (name, parameters, type_parameters, return_annotation, class_method) =
        match (&node.data, &parent_node.data) {
            (NodeData::MethodDeclaration(method), NodeData::ClassDeclaration(_))
                if node.kind == SyntaxKind::MethodDeclaration
                    && parent_node.kind == SyntaxKind::ClassDeclaration =>
            {
                (
                    method.name,
                    &method.parameters.nodes,
                    method.type_parameters.as_ref(),
                    method.type_,
                    true,
                )
            }
            (
                NodeData::MethodSignatureDeclaration(method),
                NodeData::InterfaceDeclaration(_) | NodeData::TypeLiteralNode(_),
            ) if node.kind == SyntaxKind::MethodSignature => (
                method.name,
                &method.parameters.nodes,
                method.type_parameters.as_ref(),
                method.type_,
                false,
            ),
            _ => return Ok(None),
        };
    if parameters.is_empty()
        || type_parameters.is_some()
        || method_record.name().is_private_identifier()
        || method_record.name().is_reserved_member_name()
        || method_record.name().is_late_bound()
    {
        return Ok(None);
    }
    let owner = method_record.parent().ok_or_else(invalid)?;
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    if !host.symbol_matches(store, declaration, method)
        || !host.symbol_matches(store, parent, owner)
        || !host.node(name).is_some_and(|node| {
            node.parent == Some(declaration.node)
                && matches!(&node.data, NodeData::Identifier(name)
                    if method_record.name().as_utf8() == Some(name.text.as_str()))
        })
    {
        return Err(invalid());
    }

    let overloads = if class_method {
        // Cold selected and legacy class methods keep their existing display path.
        if store.source_class_provenance_for_symbol(owner).is_none() {
            return Ok(None);
        }
        if super::classes::completed_source_class_members(store, host, owner)
            .map_err(|_| invalid())?
            .is_none()
        {
            return Err(invalid());
        }
        super::classes::source_class_method_overloads(store, type_).map_err(|_| invalid())?
    } else {
        let plan = super::object_members::plan_selected_interface_method(store, host, method)
            .map_err(|_| invalid())?;
        if super::object_members::interface_method_value_state(store, &plan)
            .map_err(|_| invalid())?
            != Some(type_)
        {
            return Err(invalid());
        }
        None
    };
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set_with_array_targets(store, type_, array_targets)
    else {
        return Err(invalid());
    };
    if projection.owner != type_ || !projection.construct_signatures.is_empty() {
        return Err(invalid());
    }
    if let Some(overloads) = &overloads
        && projection.call_signatures.as_ref() != overloads.signatures.as_slice()
    {
        return Err(invalid());
    }
    // A single public overload still has a hidden implementation to authenticate.
    for callable in projection.call_signatures.iter().chain(
        overloads
            .as_ref()
            .map(|overloads| &overloads.implementation),
    ) {
        let returned = callable.return_type.ok_or_else(invalid)?;
        for edge in callable
            .parameters
            .iter()
            .copied()
            .chain(callable.rest_parameter)
            .chain(std::iter::once(returned))
        {
            store
                .validate_cached_array_capability_with_pending_functions(array_targets, edge, &[])
                .map_err(|_| invalid())?;
        }
    }
    if overloads.is_some() {
        return Ok(None);
    }
    let [callable] = projection.call_signatures.as_ref() else {
        return Ok(None);
    };
    let signature = store.signature(callable.signature).ok_or_else(invalid)?;
    if method_record.declarations() != Some(&[declaration])
        || signature.declaration() != Some(declaration)
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.resolved_type_predicate().is_some()
        || signature.parameters().len() != parameters.len()
    {
        return Err(invalid());
    }
    if callable.rest_parameter.is_some()
        || callable.min_argument_count != parameters.len()
        || method_record.flags().contains(SymbolFlags::OPTIONAL)
    {
        return Ok(None);
    }
    let mut display = Vec::with_capacity(parameters.len());
    for ((node, symbol), value_type) in parameters
        .iter()
        .zip(signature.parameters())
        .zip(&callable.parameters)
    {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *node);
        let record = host.node(parameter).ok_or_else(invalid)?;
        let NodeData::ParameterDeclaration(data) = &record.data else {
            return Err(invalid());
        };
        if data.dot_dot_dot_token.is_some()
            || data.question_token.is_some()
            || data.initializer.is_some()
            || data.modifiers.is_some()
        {
            return Ok(None);
        }
        let Some(annotation) = data.type_ else {
            return Ok(None);
        };
        let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
        let name = NodeRef::new(declaration.arena, declaration.file, data.name);
        let name_node = host.node(name).ok_or_else(invalid)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Ok(None);
        };
        if record.kind != SyntaxKind::Parameter
            || record.parent != Some(declaration.node)
            || name_node.parent != Some(parameter.node)
            || !host.symbol_matches(store, parameter, *symbol)
            || store
                .symbol(*symbol)
                .is_none_or(|symbol| symbol.name().as_utf8() != Some(identifier.text.as_str()))
            || store.source_direct_type_annotation(parameter) != Some(annotation)
            || !store.source_direct_type_annotation_is_exact(annotation, *value_type)
        {
            return Err(invalid());
        }
        display.push(ValidatedSingleCallParameterDisplay {
            name: identifier.text.clone(),
            value_type: *value_type,
            annotation_type: Some(*value_type),
            optional: false,
            rest: false,
        });
    }
    let returned = callable.return_type.ok_or_else(invalid)?;
    if return_annotation.is_some_and(|annotation| {
        !store.source_direct_type_annotation_is_exact(
            NodeRef::new(declaration.arena, declaration.file, annotation),
            returned,
        )
    }) {
        return Err(invalid());
    }
    Ok(Some(ValidatedSingleCallSignatureDisplay {
        owner: type_,
        signature: callable.signature,
        parameters: display,
        return_type: Some(returned),
    }))
}

fn validated_single_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedSingleCallable> {
    let structured = store.type_payload(type_)?.data().structured()?;
    let [signature] = structured.signatures.as_deref()? else {
        return None;
    };
    let signature = *signature;
    let signature_record = store.signature(signature)?;
    let mut parameters = store
        .callable_signature_parameter_types(signature)?
        .to_vec();
    if parameters.len() != signature_record.parameters().len() {
        return None;
    }
    let rest_parameter = if signature_record.has_rest_parameter() {
        parameters.pop()
    } else {
        None
    };
    if signature_record.has_rest_parameter() && rest_parameter.is_none() {
        return None;
    }
    let min_argument_count = usize::try_from(signature_record.min_argument_count()).ok()?;
    Some(ValidatedSingleCallable {
        owner: type_,
        signature,
        parameters,
        rest_parameter,
        min_argument_count,
        return_type: signature_record.resolved_return_type(),
        strict_variance_exempt: store
            .source_callable_provenance(type_)
            .is_some_and(|provenance| {
                provenance.family == SourceCallableFamily::ObjectLiteralMethod
            }),
    })
}
