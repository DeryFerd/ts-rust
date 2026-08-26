//! Ordered, syntax-neutral callable-set projections.
//!
//! Providers retain ownership of syntax, binder provenance, and publication.
//! This leaf freezes the shared stored representation consumed by overload
//! selection: call signatures remain in provider order, followed by construct
//! signatures. Candidate reordering is deliberately a resolver concern.

use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_binder::{CheckFlags, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, ResolvedSignatureState, SignatureId, SignatureLinks, TypeId,
    TypeNodeLinks,
    array_types::CanonicalArrayTargets,
    callables::{
        CallableFamily, StoredSingleCallableValidation, ValidatedSingleCallable,
        validate_stored_single_callable_provider,
    },
    classes::{
        ClassHeritageMembersValidation, authenticated_class_constructor_value,
        validate_class_heritage_members,
    },
    declared::cached_ordinary_type_parameter_owner,
    instantiate::instantiated_member_type_matches,
    links::ValueSymbolLinks,
    mapper::TypeMapperApplication,
    object_members::{StoredDeclaredCallSetValidation, validate_stored_declared_call_set},
    reference_types::validate_direct_generic_reference,
    signatures::SignatureFlags,
    source_overloads::{StoredSourceOverloadValidation, validate_stored_source_overload},
    store::{SourceCallableReturnProvenance, SourceNodeParent},
    type_records::{ConstrainedTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

/// Immutable callable members after provider and store validation.
///
/// `call_signatures` preserves the stored call-signature prefix exactly.
/// Construct signatures retain their exact identities until the construct-call
/// semantic kernel is installed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CallableSetProjection {
    pub(super) owner: TypeId,
    pub(super) call_signatures: Box<[ValidatedSingleCallable]>,
    pub(super) construct_signatures: Box<[SignatureId]>,
}

/// Store-only callable-set classification shared by future overload consumers.
///
/// `edges` is provider-owned and includes every type dependency required by
/// graph validation. The normalized set intentionally contains only the
/// signatures visible to calls and constructs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredCallableSetValidation {
    NotCallable,
    Pending {
        family: CallableFamily,
    },
    Valid {
        family: CallableFamily,
        projection: CallableSetProjection,
        edges: Vec<TypeId>,
    },
    Malformed {
        family: CallableFamily,
    },
}

/// Validates every installed callable provider and normalizes its ordered set.
///
/// Exact-single providers retain their established validation path. The
/// declared-member provider proves its source and publication provenance first,
/// then reuses [`validate_stored_callable_set_projection`] for the common
/// ordered representation.
pub(super) fn validate_stored_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredCallableSetValidation {
    match validate_stored_single_callable_provider(store, type_) {
        StoredSingleCallableValidation::NotCallable => {}
        StoredSingleCallableValidation::Pending { family } => {
            return StoredCallableSetValidation::Pending { family };
        }
        StoredSingleCallableValidation::Malformed { family } => {
            return StoredCallableSetValidation::Malformed { family };
        }
        StoredSingleCallableValidation::Valid {
            family,
            callable,
            edges,
        } => {
            if !valid_untyped_javascript_source_signature(
                store,
                callable.owner,
                callable.signature,
                &callable.parameters,
                callable.min_argument_count,
            ) {
                return StoredCallableSetValidation::Malformed { family };
            }
            return StoredCallableSetValidation::Valid {
                family,
                projection: CallableSetProjection {
                    owner: type_,
                    call_signatures: Box::new([callable]),
                    construct_signatures: Box::new([]),
                },
                edges,
            };
        }
    }
    let family = CallableFamily::SourceFunctionOverloads;
    match validate_stored_source_overload(store, type_) {
        StoredSourceOverloadValidation::NotSourceOverload => {}
        StoredSourceOverloadValidation::Malformed => {
            return StoredCallableSetValidation::Malformed { family };
        }
        StoredSourceOverloadValidation::Valid(edges) => {
            let Some(projection) = validate_stored_callable_set_projection(store, type_, false)
            else {
                return StoredCallableSetValidation::Malformed { family };
            };
            return StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            };
        }
    }
    let family = CallableFamily::DeclaredCallSignatures;
    match super::instantiated_members::validate_instantiated_array_property_callable(store, type_) {
        super::instantiated_members::InstantiatedArrayPropertyCallableValidation::NotCallable => {}
        super::instantiated_members::InstantiatedArrayPropertyCallableValidation::Malformed => {
            return StoredCallableSetValidation::Malformed { family };
        }
        super::instantiated_members::InstantiatedArrayPropertyCallableValidation::Valid(edges) => {
            let Some(projection) =
                validate_stored_callable_set_projection_with(store, type_, false, |signature| {
                    store
                        .signature(signature)?
                        .parameters()
                        .iter()
                        .map(|parameter| store.value_symbol_links(*parameter)?.resolved_type)
                        .collect()
                })
            else {
                return StoredCallableSetValidation::Malformed { family };
            };
            return StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            };
        }
    }
    let family = CallableFamily::DeclaredCallSignatures;
    match validate_stored_declared_call_set(store, type_) {
        StoredDeclaredCallSetValidation::NotDeclaredCallSet => {}
        StoredDeclaredCallSetValidation::Malformed => {
            return StoredCallableSetValidation::Malformed { family };
        }
        StoredDeclaredCallSetValidation::Valid(edges) => {
            let Some(projection) = validate_stored_callable_set_projection(store, type_, false)
            else {
                return StoredCallableSetValidation::Malformed { family };
            };
            return StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            };
        }
    }

    if let Some(validation) = validate_stored_class_constructor_callable_set(store, type_) {
        return validation;
    }

    if let Some(validation) = validate_stored_default_library_method_callable_set(store, type_) {
        return validation;
    }

    if let Some(validation) =
        validate_stored_instantiated_type_literal_method_callable_set(store, type_)
    {
        return validation;
    }

    if let Some(validation) =
        validate_stored_instantiated_interface_method_callable_set(store, type_)
    {
        return validation;
    }

    if let Some(validation) = validate_stored_declared_method_callable_set(store, type_) {
        return validation;
    }

    if let Some(validation) = validate_stored_class_method_callable_set(store, type_) {
        return validation;
    }

    validate_stored_intersection_callable_set(store, type_)
}

fn validate_stored_class_constructor_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let record = store.type_payload(type_)?;
    if !matches!(record.data(), TypeData::Object(_)) {
        return None;
    }
    let symbol = record.symbol()?;
    if !store.symbol(symbol)?.flags().contains(SymbolFlags::CLASS) {
        return None;
    }

    let family = CallableFamily::DeclaredCallSignatures;
    let authenticated = (|| {
        let (value, expected) = authenticated_class_constructor_value(store, symbol)?;
        if value != type_ {
            return None;
        }
        let projection =
            validate_stored_callable_set_projection_with(store, type_, false, |signature| {
                store
                    .signature(signature)?
                    .parameters()
                    .iter()
                    .map(|parameter| {
                        let links = store.value_symbol_links(*parameter)?;
                        let type_ = links.resolved_type?;
                        (links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(type_),
                                ..ValueSymbolLinks::default()
                            })
                            && store.type_payload(type_).is_some())
                        .then_some(type_)
                    })
                    .collect()
            })?;
        let [signature] = projection.construct_signatures.as_ref() else {
            return None;
        };
        if !projection.call_signatures.is_empty() || *signature != expected {
            return None;
        }
        let signature = store.signature(*signature)?;
        let mut edges = signature
            .parameters()
            .iter()
            .map(|parameter| store.value_symbol_links(*parameter)?.resolved_type)
            .collect::<Option<Vec<_>>>()?;
        edges.push(signature.resolved_return_type()?);
        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

fn valid_untyped_javascript_source_signature(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
    parameter_types: &[TypeId],
    minimum: usize,
) -> bool {
    let Some(record) = store.signature(signature) else {
        return false;
    };
    if !record
        .flags()
        .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
    {
        return true;
    }
    let Some(provenance) = store.source_callable_provenance(owner) else {
        return false;
    };
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    if record.flags() != SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
        || record.declaration() != Some(provenance.declaration)
        || record.parameters().len() != parameter_types.len()
        || minimum != parameter_types.len()
        || minimum == 0
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || provenance.signature != signature
        || provenance.contextual_target.is_some()
        || provenance.contextual_variable.is_some()
        || provenance.generic_return_type_parameter.is_some()
        || provenance.return_provenance != SourceCallableReturnProvenance::Inferred
        || store.source_node_kind(provenance.declaration) != Some(provenance.family.syntax_kind())
        || store
            .type_payload(owner)
            .and_then(super::TypeRecord::symbol)
            != Some(provenance.owner_symbol)
        || store.source_callable_type_for_owner(provenance.owner_symbol) != Some(owner)
        || store.source_callable_type_for_declaration(provenance.declaration) != Some(owner)
        || store.source_callable_type_for_signature(signature) != Some(owner)
        || store
            .function_signature_return_annotation(signature)
            .is_some()
    {
        return false;
    }

    record
        .parameters()
        .iter()
        .copied()
        .zip(parameter_types)
        .all(|(symbol, type_)| {
            let Some([declaration]) = store
                .symbol(symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
            else {
                return false;
            };
            *type_ == bootstrap.any_type
                && store.source_node_kind(*declaration) == Some(SyntaxKind::Parameter)
                && store.source_node_parent(*declaration)
                    == Some(SourceNodeParent::Parent(provenance.declaration))
                && store
                    .source_primitive_type_annotation(*declaration)
                    .is_none()
                && store.value_symbol_links(symbol)
                    == Some(&ValueSymbolLinks {
                        resolved_type: Some(bootstrap.any_type),
                        ..ValueSymbolLinks::default()
                    })
        })
}

#[allow(clippy::too_many_lines)] // Keep the complete wrapper and method proof together.
fn validate_stored_default_library_method_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let method_symbol = store.type_payload(type_)?.symbol()?;
    let method = store.symbol(method_symbol)?;
    if !method.flags().contains(SymbolFlags::METHOD) {
        return None;
    }
    let [declaration] = method.declarations()? else {
        return None;
    };
    let declaration = *declaration;
    if store.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature) {
        return None;
    }
    let (owner_name, method_name, has_parameter) = match method.name().as_utf8() {
        Some("toFixed") => ("Number", "toFixed", true),
        Some("toLowerCase") => ("String", "toLowerCase", false),
        _ => return None,
    };

    let family = CallableFamily::DeclaredCallSignatures;
    let authenticated = (|| {
        let bootstrap = store.intrinsic_bootstrap()?;
        let (wrapper, authenticated_declaration) =
            store.authenticated_global_interface_method(method_symbol)?;
        let wrapper_record = store.type_payload(wrapper)?;
        let TypeData::Interface(_) = wrapper_record.data() else {
            return None;
        };
        let owner_symbol = method
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))?;
        let owner = store.symbol(owner_symbol)?;
        let Some(SourceNodeParent::Parent(owner_declaration)) =
            store.source_node_parent(declaration)
        else {
            return None;
        };
        let owner_flags = owner.flags();
        let allowed_owner_flags =
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
        let owner_declarations = owner.declarations()?;
        let global_owner = store
            .symbol_table(bootstrap.globals)?
            .get_source(owner_name)
            .and_then(|symbol| store.get_merged_symbol(symbol));
        if owner_flags & SymbolFlags::TYPE != SymbolFlags::INTERFACE
            || owner_flags.without(allowed_owner_flags) != SymbolFlags::NONE
            || owner.check_flags() != CheckFlags::NONE
            || owner.parent().is_some()
            || owner.exports().is_some()
            || owner.export_symbol().is_some()
            || authenticated_declaration != declaration
            || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || global_owner != Some(owner_symbol)
            || store
                .declared_type_links(owner_symbol)
                .and_then(|links| links.declared_type)
                != Some(wrapper)
            || wrapper_record.flags() != TypeFlags::OBJECT
            || !wrapper_record
                .object_flags()
                .contains(ObjectFlags::INTERFACE)
            || wrapper_record.symbol() != Some(owner_symbol)
            || wrapper_record.alias().is_some()
            || !owner_declarations.contains(&owner_declaration)
            || store.source_node_kind(owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
            || owner
                .members()
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source(method_name))
                != Some(method_symbol)
            || method.flags() != SymbolFlags::METHOD
            || method.check_flags() != CheckFlags::NONE
            || method.value_declaration() != Some(declaration)
            || method
                .parent()
                .and_then(|parent| store.get_merged_symbol(parent))
                != Some(owner_symbol)
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || store.get_merged_symbol(method_symbol) != Some(method_symbol)
            || store.value_symbol_links(method_symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }

        let record = store.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        let [signature] = object.structured.signatures.as_deref()? else {
            return None;
        };
        let signature = *signature;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || object.target.is_some()
            || object.mapper.is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.call_signature_count != 1
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
        {
            return None;
        }

        let return_annotation = store.source_primitive_type_annotation(declaration)?;
        if store.source_node_kind(return_annotation) != Some(SyntaxKind::StringKeyword)
            || store.type_node_links(return_annotation)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(bootstrap.string_type),
                    ..TypeNodeLinks::default()
                })
            || store
                .function_signature_return_annotation(signature)
                .is_some_and(|annotation| annotation != (return_annotation, false))
        {
            return None;
        }

        let signature_record = store.signature(signature)?;
        if signature_record.flags() != SignatureFlags::NONE
            || signature_record.declaration() != Some(declaration)
            || !signature_record.type_parameters().is_empty()
            || signature_record.this_parameter().is_some()
            || signature_record.parameters().len() != usize::from(has_parameter)
            || signature_record.min_argument_count() != 0
            || signature_record.resolved_min_argument_count() != -1
            || signature_record.resolved_return_type() != Some(bootstrap.string_type)
            || signature_record.resolved_type_predicate().is_some()
            || signature_record.target().is_some()
            || signature_record.mapper().is_some()
            || signature_record.isolated_signature_type().is_some()
            || signature_record.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || store.global_interface_method_callable_type(signature) != Some(type_)
            || store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
        {
            return None;
        }

        let parameter_types = if let Some(&parameter) = signature_record.parameters().first() {
            let parameter_record = store.symbol(parameter)?;
            let [parameter_declaration] = parameter_record.declarations()? else {
                return None;
            };
            let parameter_declaration = *parameter_declaration;
            let parameter_annotation =
                store.source_primitive_type_annotation(parameter_declaration)?;
            let parameter_type = store.value_symbol_links(parameter)?.resolved_type?;
            let expected_type = if bootstrap.options.strict_null_checks {
                let record = store.type_payload(parameter_type)?;
                let TypeData::Union(union) = record.data() else {
                    return None;
                };
                (record.flags() == TypeFlags::UNION
                    && record.symbol().is_none()
                    && record.alias().is_none()
                    && union.union.types.len() == 2
                    && union.union.types.contains(&bootstrap.number_type)
                    && union.union.types.contains(&bootstrap.undefined_type))
                .then_some(parameter_type)?
            } else {
                bootstrap.number_type
            };
            if parameter_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || parameter_record.check_flags() != CheckFlags::NONE
                || parameter_record.name().as_utf8() != Some("fractionDigits")
                || parameter_record.value_declaration() != Some(parameter_declaration)
                || parameter_record.members().is_some()
                || parameter_record.exports().is_some()
                || parameter_record.parent().is_some()
                || parameter_record.export_symbol().is_some()
                || store.get_merged_symbol(parameter) != Some(parameter)
                || store.source_node_kind(parameter_declaration) != Some(SyntaxKind::Parameter)
                || store.source_node_parent(parameter_declaration)
                    != Some(SourceNodeParent::Parent(declaration))
                || store.source_node_kind(parameter_annotation) != Some(SyntaxKind::NumberKeyword)
                || store.type_node_links(parameter_annotation)
                    != Some(&TypeNodeLinks {
                        resolved_type: Some(bootstrap.number_type),
                        ..TypeNodeLinks::default()
                    })
                || parameter_type != expected_type
                || store.value_symbol_links(parameter)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(expected_type),
                        ..ValueSymbolLinks::default()
                    })
            {
                return None;
            }
            vec![expected_type]
        } else {
            Vec::new()
        };
        if store
            .callable_signature_parameter_types(signature)
            .is_some_and(|cached| cached != parameter_types.as_slice())
        {
            return None;
        }

        let projection =
            validate_stored_callable_set_projection_with(store, type_, true, |candidate| {
                (candidate == signature).then(|| parameter_types.clone())
            })?;
        let [callable] = projection.call_signatures.as_ref() else {
            return None;
        };
        if !projection.construct_signatures.is_empty()
            || callable.signature != signature
            || callable.return_type != Some(bootstrap.string_type)
            || callable.min_argument_count != 0
            || callable.rest_parameter.is_some()
            || !callable.strict_variance_exempt
        {
            return None;
        }
        let mut edges = parameter_types;
        edges.push(bootstrap.string_type);
        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

fn validate_stored_instantiated_interface_method_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let (Some(source), Some(mapper)) = (object.target, object.mapper) else {
        return None;
    };
    let method = record.symbol()?;
    let (owner, owner_type) = store.authenticated_interface_method_owner(method)?;
    let family = CallableFamily::DeclaredCallSignatures;

    let authenticated = (|| {
        let source_validation = validate_stored_declared_method_callable_set(store, source)?;
        let StoredCallableSetValidation::Valid {
            projection: original,
            ..
        } = source_validation
        else {
            return None;
        };
        let method_record = store.symbol(method)?;
        let owner_record = store.symbol(owner)?;
        let declarations = method_record.declarations()?;
        let TypeData::Interface(interface) = store.type_payload(owner_type)?.data() else {
            return None;
        };
        let parameters = interface.reference.resolved_type_arguments.as_deref()?;
        let this_type = interface.this_type?;
        let receiver = store.map_type(mapper, this_type)?;
        let receiver_reference = validate_direct_generic_reference(store, receiver).ok()?;
        let array_targets = if matches!(
            owner_record.name().as_utf8(),
            Some("Array" | "ReadonlyArray")
        ) {
            let globals = store.intrinsic_bootstrap()?.globals;
            let global_owner = store
                .symbol_table(globals)?
                .get(owner_record.name())
                .and_then(|owner| store.get_merged_symbol(owner));
            let targets = CanonicalArrayTargets::for_single_target_validation(owner_type);
            if global_owner != Some(owner)
                || store
                    .canonical_array_reference_with_targets(targets, receiver)
                    .ok()
                    .flatten()
                    .is_none_or(|reference| reference.base_type != receiver)
            {
                return None;
            }
            Some(targets)
        } else {
            None
        };
        if parameters.is_empty()
            || receiver_reference.target != owner_type
            || receiver_reference.type_arguments.len() != parameters.len()
            || interface.all_type_parameters.as_deref().is_none_or(|all| {
                all.len() != parameters.len() + 1
                    || &all[..parameters.len()] != parameters
                    || all.last().copied() != Some(this_type)
            })
        {
            return None;
        }
        let mapper_sources = parameters
            .iter()
            .copied()
            .chain(std::iter::once(this_type))
            .collect::<Vec<_>>();
        let mapper_targets = receiver_reference
            .type_arguments
            .iter()
            .copied()
            .chain(std::iter::once(receiver))
            .collect::<Vec<_>>();
        if store.type_mapper_has_exact_endpoints(mapper, &mapper_sources, &mapper_targets)
            != Some(true)
            || record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
            || object.structured.call_signature_count != original.call_signatures.len()
            || declarations.len() != original.call_signatures.len()
            || store.value_symbol_links(method)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(source),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        let stored_signatures = object.structured.signatures.as_deref()?;
        if stored_signatures.len() != original.call_signatures.len() {
            return None;
        }

        let projection =
            validate_stored_callable_set_projection_with(store, type_, true, |signature| {
                let target = store.signature(signature)?.target()?;
                let source = original
                    .call_signatures
                    .iter()
                    .find(|callable| callable.signature == target)?;
                validated_instantiated_method_parameter_types(
                    store,
                    signature,
                    source,
                    mapper,
                    array_targets,
                )
            })?;
        if !projection.construct_signatures.is_empty()
            || projection.call_signatures.len() != original.call_signatures.len()
        {
            return None;
        }

        let mut edges = Vec::new();
        for ((callable, source_callable), declaration) in projection
            .call_signatures
            .iter()
            .zip(original.call_signatures.iter())
            .zip(declarations)
        {
            let signature = store.signature(callable.signature)?;
            let original_signature = store.signature(source_callable.signature)?;
            let return_type = callable.return_type?;
            let source_return = source_callable.return_type?;
            let signature_mapper = validated_instantiated_method_mapper(
                store,
                original_signature,
                signature,
                mapper,
                array_targets,
            )?;
            if signature.flags() != (original_signature.flags() & SignatureFlags::PROPAGATING_FLAGS)
                || signature.declaration() != Some(*declaration)
                || original_signature.declaration() != Some(*declaration)
                || signature.this_parameter().is_some()
                || signature.parameters().len() != original_signature.parameters().len()
                || signature.min_argument_count() != original_signature.min_argument_count()
                || signature.resolved_min_argument_count() != -1
                || signature.resolved_type_predicate().is_some()
                || signature.target() != Some(source_callable.signature)
                || signature.mapper() != Some(signature_mapper)
                || signature.isolated_signature_type().is_some()
                || signature.composite().is_some()
                || store.signature_has_circular_return_type(callable.signature)
                || !instantiated_method_type_matches(
                    store,
                    source_return,
                    return_type,
                    signature_mapper,
                    array_targets,
                )
            {
                return None;
            }
            edges.extend(signature.type_parameters().iter().copied());
            edges.extend(callable.parameters.iter().copied());
            edges.extend(callable.rest_parameter);
            edges.push(return_type);
        }

        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

fn validate_stored_instantiated_type_literal_method_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let (Some(source), Some(mapper)) = (object.target, object.mapper) else {
        return None;
    };
    let method = record.symbol()?;
    let owner = store
        .symbol(method)?
        .parent()
        .and_then(|parent| store.get_merged_symbol(parent))?;
    if store.symbol(owner)?.flags() != SymbolFlags::TYPE_LITERAL {
        return None;
    }

    let family = CallableFamily::DeclaredCallSignatures;
    let authenticated = (|| {
        let (authenticated_owner, _) = store.authenticated_type_literal_method_owner(method)?;
        if authenticated_owner != owner {
            return None;
        }
        let StoredCallableSetValidation::Valid {
            projection: original,
            ..
        } = validate_stored_declared_method_callable_set(store, source)?
        else {
            return None;
        };
        let method_record = store.symbol(method)?;
        let declarations = method_record.declarations()?;
        let alias = literal_method_generic_alias(store, owner, &original)?;
        let parameters = store.type_alias_links(alias)?.type_parameters.as_deref()?;
        let arguments = parameters
            .iter()
            .map(|parameter| store.map_type(mapper, *parameter))
            .collect::<Option<Vec<_>>>()?;
        if parameters.is_empty()
            || store.type_mapper_has_exact_endpoints(mapper, parameters, &arguments) != Some(true)
            || record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
            || object.structured.call_signature_count != original.call_signatures.len()
            || declarations.len() != original.call_signatures.len()
            || store.value_symbol_links(method)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(source),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        let stored_signatures = object.structured.signatures.as_deref()?;
        if stored_signatures.len() != original.call_signatures.len() {
            return None;
        }

        let projection =
            validate_stored_callable_set_projection_with(store, type_, true, |signature| {
                let target = store.signature(signature)?.target()?;
                let source = original
                    .call_signatures
                    .iter()
                    .find(|callable| callable.signature == target)?;
                validated_instantiated_method_parameter_types_with_targets(
                    store, signature, source, mapper, None,
                )
            })?;
        if !projection.construct_signatures.is_empty()
            || projection.call_signatures.len() != original.call_signatures.len()
        {
            return None;
        }

        let mut edges = Vec::new();
        for ((callable, source_callable), declaration) in projection
            .call_signatures
            .iter()
            .zip(original.call_signatures.iter())
            .zip(declarations)
        {
            let signature = store.signature(callable.signature)?;
            let original_signature = store.signature(source_callable.signature)?;
            let return_type = callable.return_type?;
            let source_return = source_callable.return_type?;
            let signature_mapper = validated_instantiated_method_mapper(
                store,
                original_signature,
                signature,
                mapper,
                None,
            )?;
            if signature.flags() != (original_signature.flags() & SignatureFlags::PROPAGATING_FLAGS)
                || signature.declaration() != Some(*declaration)
                || original_signature.declaration() != Some(*declaration)
                || signature.this_parameter().is_some()
                || signature.parameters().len() != original_signature.parameters().len()
                || signature.min_argument_count() != original_signature.min_argument_count()
                || signature.resolved_min_argument_count() != -1
                || signature.resolved_type_predicate().is_some()
                || signature.target() != Some(source_callable.signature)
                || signature.mapper() != Some(signature_mapper)
                || signature.isolated_signature_type().is_some()
                || signature.composite().is_some()
                || store.signature_has_circular_return_type(callable.signature)
                || !instantiated_method_type_matches(
                    store,
                    source_return,
                    return_type,
                    signature_mapper,
                    None,
                )
            {
                return None;
            }
            edges.extend(signature.type_parameters().iter().copied());
            edges.extend(callable.parameters.iter().copied());
            edges.extend(callable.rest_parameter);
            edges.push(return_type);
        }

        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

fn literal_method_generic_alias(
    store: &CanonicalTypeMapperStore,
    owner: ts_binder::SemanticSymbolId,
    projection: &CallableSetProjection,
) -> Option<ts_binder::SemanticSymbolId> {
    let [literal] = store.symbol(owner)?.declarations()? else {
        return None;
    };
    let alias = projection.call_signatures.iter().find_map(|callable| {
        callable
            .parameters
            .iter()
            .copied()
            .chain(callable.rest_parameter)
            .chain(callable.return_type)
            .find_map(|type_| alias_owner_of_method_type(store, type_, &mut HashSet::new()))
    })?;
    let alias_record = store.symbol(alias)?;
    let [declaration] = alias_record.declarations()? else {
        return None;
    };
    if alias_record.flags() != SymbolFlags::TYPE_ALIAS
        || store.get_merged_symbol(alias) != Some(alias)
    {
        return None;
    }
    let mut current = *literal;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let SourceNodeParent::Parent(parent) = store.source_node_parent(current)? else {
            return None;
        };
        if parent == *declaration {
            return Some(alias);
        }
        current = parent;
    }
    None
}

fn alias_owner_of_method_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visited: &mut HashSet<TypeId>,
) -> Option<ts_binder::SemanticSymbolId> {
    if !visited.insert(type_) {
        return None;
    }
    let result = match store.type_payload(type_)?.data() {
        TypeData::TypeParameter(_) => {
            let parameter = cached_ordinary_type_parameter_owner(store, type_)?;
            let [declaration] = store.symbol(parameter)?.declarations()? else {
                return None;
            };
            let SourceNodeParent::Parent(alias_declaration) =
                store.source_node_parent(*declaration)?
            else {
                return None;
            };
            let alias = store.cached_type_alias_symbol_for_declaration(alias_declaration)?;
            store
                .type_alias_links(alias)?
                .type_parameters
                .as_deref()?
                .contains(&type_)
                .then_some(alias)
        }
        TypeData::Union(union) => union
            .union
            .types
            .iter()
            .find_map(|type_| alias_owner_of_method_type(store, *type_, visited)),
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            validate_direct_generic_reference(store, type_)
                .ok()?
                .type_arguments
                .into_iter()
                .find_map(|type_| alias_owner_of_method_type(store, type_, visited))
        }
        _ => None,
    };
    visited.remove(&type_);
    result
}

fn validated_instantiated_method_parameter_types(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    original: &ValidatedSingleCallable,
    mapper: super::TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Vec<TypeId>> {
    validated_instantiated_method_parameter_types_with_targets(
        store,
        signature,
        original,
        mapper,
        array_targets,
    )
}

fn validated_instantiated_method_parameter_types_with_targets(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    original: &ValidatedSingleCallable,
    mapper: super::TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Vec<TypeId>> {
    let signature = store.signature(signature)?;
    let original_signature = store.signature(original.signature)?;
    let signature_mapper = validated_instantiated_method_mapper(
        store,
        original_signature,
        signature,
        mapper,
        array_targets,
    )?;
    if signature.target() != Some(original.signature)
        || signature.mapper() != Some(signature_mapper)
        || signature.parameters().len() != original_signature.parameters().len()
    {
        return None;
    }
    let original_types = store.callable_signature_parameter_types(original.signature)?;
    if original_types.len() != original_signature.parameters().len() {
        return None;
    }

    let mut parameter_types = Vec::with_capacity(signature.parameters().len());
    for ((parameter, original_parameter), template) in signature
        .parameters()
        .iter()
        .zip(original_signature.parameters())
        .zip(original_types)
    {
        let symbol = store.symbol(*parameter)?;
        let original_symbol = store.symbol(*original_parameter)?;
        let links = store.value_symbol_links(*parameter)?;
        let type_ = links.resolved_type?;
        let valid_links = if parameter == original_parameter {
            links
                == &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
                && type_ == *template
        } else {
            let expected_checks = CheckFlags::INSTANTIATED
                | (original_symbol.check_flags()
                    & (CheckFlags::READONLY
                        | CheckFlags::LATE
                        | CheckFlags::OPTIONAL_PARAMETER
                        | CheckFlags::REST_PARAMETER));
            symbol.flags() == original_symbol.flags() | SymbolFlags::TRANSIENT
                && symbol.check_flags() == expected_checks
                && symbol.name() == original_symbol.name()
                && symbol.declarations() == original_symbol.declarations()
                && symbol.value_declaration() == original_symbol.value_declaration()
                && symbol.parent() == original_symbol.parent()
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.export_symbol().is_none()
                && store.get_merged_symbol(*parameter) == Some(*parameter)
                && links
                    == &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        target: Some(*original_parameter),
                        mapper: Some(signature_mapper),
                        name_type: store
                            .value_symbol_links(*original_parameter)
                            .and_then(|links| links.name_type),
                        ..ValueSymbolLinks::default()
                    })
        };
        if !valid_links
            || !instantiated_method_type_matches(
                store,
                *template,
                type_,
                signature_mapper,
                array_targets,
            )
        {
            return None;
        }
        parameter_types.push(type_);
    }
    Some(parameter_types)
}

/// Validates the fresh method parameters and mapper retained by an instantiated signature.
pub(super) fn validated_instantiated_method_mapper(
    store: &CanonicalTypeMapperStore,
    original: &super::signatures::Signature,
    instantiated: &super::signatures::Signature,
    owner_mapper: super::TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<super::TypeMapperId> {
    let mapper = instantiated.mapper()?;
    if original.type_parameters().is_empty() {
        return (instantiated.type_parameters().is_empty() && mapper == owner_mapper)
            .then_some(mapper);
    }
    if instantiated.type_parameters().len() != original.type_parameters().len()
        || store.mapper_payload(mapper).is_none()
        || store.mapper_payload(owner_mapper).is_none()
    {
        return None;
    }
    let Some(TypeMapperApplication::Composite { first, second }) =
        store.mapper_application(mapper, original.type_parameters()[0])
    else {
        return None;
    };
    if second != owner_mapper
        || store.type_mapper_has_exact_endpoints(
            first,
            original.type_parameters(),
            instantiated.type_parameters(),
        ) != Some(true)
    {
        return None;
    }

    let mut unique = HashSet::with_capacity(instantiated.type_parameters().len());
    for (&source, &fresh) in original
        .type_parameters()
        .iter()
        .zip(instantiated.type_parameters())
    {
        let source_record = store.type_payload(source)?;
        let fresh_record = store.type_payload(fresh)?;
        let (TypeData::TypeParameter(source_data), TypeData::TypeParameter(fresh_data)) =
            (source_record.data(), fresh_record.data())
        else {
            return None;
        };
        let constraint_matches = match (source_data.constraint, fresh_data.constraint) {
            (None, None) => true,
            (Some(source), Some(actual)) => {
                instantiated_method_type_matches(store, source, actual, mapper, array_targets)
            }
            _ => false,
        };
        let default_matches = match (
            source_data.resolved_default_type,
            fresh_data.resolved_default_type,
        ) {
            (None, None) => true,
            (Some(source), Some(actual)) => {
                instantiated_method_type_matches(store, source, actual, mapper, array_targets)
            }
            _ => false,
        };
        if fresh == source
            || !unique.insert(fresh)
            || fresh_record.flags() != TypeFlags::TYPE_PARAMETER
            || fresh_record.symbol() != source_record.symbol()
            || fresh_record.alias().is_some()
            || fresh_data.is_this_type
            || fresh_data.target != Some(source)
            || fresh_data.mapper != Some(mapper)
            || mapped_method_type_parameter(store, mapper, source) != Some(fresh)
            || !constraint_matches
            || !default_matches
        {
            return None;
        }
    }
    Some(mapper)
}

/// Compares signature types through composed method mappers without allocating.
pub(super) fn instantiated_method_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: super::TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if instantiated_member_type_matches(store, template, actual, mapper, array_targets)
        .unwrap_or(false)
    {
        return true;
    }
    if !matches!(
        store.mapper_application(mapper, template),
        Some(TypeMapperApplication::Composite { .. })
    ) {
        return false;
    }
    instantiated_composite_method_type_matches(store, template, actual, mapper, &mut HashSet::new())
}

fn instantiated_composite_method_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: super::TypeMapperId,
    active: &mut HashSet<(TypeId, TypeId)>,
) -> bool {
    if !active.insert((template, actual)) {
        return true;
    }
    let result = match (
        store.type_payload(template).map(super::TypeRecord::data),
        store.type_payload(actual).map(super::TypeRecord::data),
    ) {
        (Some(TypeData::TypeParameter(_)), Some(_)) => {
            mapped_method_type_parameter(store, mapper, template) == Some(actual)
        }
        (Some(TypeData::Intrinsic(_) | TypeData::Literal(_)), Some(_)) => template == actual,
        (Some(TypeData::Union(source)), Some(TypeData::Union(mapped_union))) => {
            source.union.types.iter().all(|source| {
                mapped_union.union.types.iter().any(|actual| {
                    instantiated_composite_method_type_matches(
                        store, *source, *actual, mapper, active,
                    )
                })
            }) && mapped_union.union.types.iter().all(|actual| {
                source.union.types.iter().any(|source| {
                    instantiated_composite_method_type_matches(
                        store, *source, *actual, mapper, active,
                    )
                })
            })
        }
        (Some(TypeData::Union(source)), Some(_)) => source.union.types.iter().all(|source| {
            instantiated_composite_method_type_matches(store, *source, actual, mapper, active)
        }),
        (
            Some(TypeData::TypeReference(_) | TypeData::Interface(_)),
            Some(TypeData::TypeReference(_) | TypeData::Interface(_)),
        ) => match (
            validate_direct_generic_reference(store, template),
            validate_direct_generic_reference(store, actual),
        ) {
            (Ok(source), Ok(mapped_reference)) => {
                source.target == mapped_reference.target
                    && source.type_arguments.len() == mapped_reference.type_arguments.len()
                    && source
                        .type_arguments
                        .iter()
                        .zip(mapped_reference.type_arguments)
                        .all(|(source, actual)| {
                            instantiated_composite_method_type_matches(
                                store, *source, actual, mapper, active,
                            )
                        })
            }
            _ => false,
        },
        _ => false,
    };
    active.remove(&(template, actual));
    result
}

fn mapped_method_type_parameter(
    store: &CanonicalTypeMapperStore,
    mapper: super::TypeMapperId,
    type_: TypeId,
) -> Option<TypeId> {
    match store.mapper_application(mapper, type_)? {
        TypeMapperApplication::Direct(mapped_type) => Some(mapped_type),
        TypeMapperApplication::Merged { first, second }
        | TypeMapperApplication::Composite { first, second } => {
            let mapped_type = mapped_method_type_parameter(store, first, type_)?;
            mapped_method_type_parameter(store, second, mapped_type)
        }
    }
}

pub(super) fn validate_stored_declared_method_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let method_symbol = store.type_payload(type_)?.symbol()?;
    let method = store.symbol(method_symbol)?;
    if !method.flags().contains(SymbolFlags::METHOD) {
        return None;
    }
    let owner_symbol = method
        .parent()
        .and_then(|parent| store.get_merged_symbol(parent))?;
    let owner = store.symbol(owner_symbol)?;
    let interface_owner = owner.flags().contains(SymbolFlags::INTERFACE);
    let literal_owner = owner.flags() == SymbolFlags::TYPE_LITERAL;
    if !interface_owner && !literal_owner {
        return None;
    }

    let family = CallableFamily::DeclaredCallSignatures;
    let authenticated = (|| {
        let declarations = method.declarations()?;
        let owner_declarations = owner.declarations()?;
        let (authenticated_owner, owner_type) = if interface_owner {
            store.authenticated_interface_method_owner(method_symbol)?
        } else {
            store.authenticated_type_literal_method_owner(method_symbol)?
        };
        let owner_record = store.type_payload(owner_type)?;
        let valid_owner_type = if interface_owner {
            matches!(owner_record.data(), TypeData::Interface(_))
                && owner_record.object_flags().contains(ObjectFlags::INTERFACE)
                && owner_record.alias().is_none()
        } else {
            matches!(owner_record.data(), TypeData::Object(_))
                && owner_record.object_flags()
                    == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        };
        let allowed_owner_flags = SymbolFlags::INTERFACE
            | SymbolFlags::FUNCTION_SCOPED_VARIABLE
            | SymbolFlags::NAMESPACE_MODULE
            | SymbolFlags::TRANSIENT;
        if declarations.is_empty()
            || authenticated_owner != owner_symbol
            || interface_owner
                && (owner.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
                    || owner.flags().without(allowed_owner_flags) != SymbolFlags::NONE)
            || literal_owner && owner.flags() != SymbolFlags::TYPE_LITERAL
            || owner.check_flags() != CheckFlags::NONE
            || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || owner_record.flags() != TypeFlags::OBJECT
            || !valid_owner_type
            || owner_record.symbol() != Some(owner_symbol)
            || method.flags() != SymbolFlags::METHOD
            || method.check_flags() != CheckFlags::NONE
            || method.name().is_reserved_member_name()
            || method.name().is_private_identifier()
            || method.name().is_late_bound()
            || method
                .value_declaration()
                .is_none_or(|declaration| !declarations.contains(&declaration))
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || store.get_merged_symbol(method_symbol) != Some(method_symbol)
            || owner
                .members()
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(method.name()))
                .and_then(|method| store.get_merged_symbol(method))
                != Some(method_symbol)
            || store.value_symbol_links(method_symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }

        let record = store.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        let signatures = object.structured.signatures.as_deref()?;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || object.target.is_some()
            || object.mapper.is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.call_signature_count != signatures.len()
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
            || signatures.len() != declarations.len()
        {
            return None;
        }

        let projection =
            validate_stored_callable_set_projection_with(store, type_, true, |signature| {
                validated_method_signature_parameter_types(store, signature)
            })?;
        if !projection.construct_signatures.is_empty()
            || projection.call_signatures.len() != declarations.len()
        {
            return None;
        }

        let mut edges = Vec::new();
        for (callable, declaration) in projection.call_signatures.iter().zip(declarations) {
            let signature = store.signature(callable.signature)?;
            let allowed_flags =
                SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES;
            if store.source_node_kind(*declaration) != Some(SyntaxKind::MethodSignature)
                || !matches!(
                    store.source_node_parent(*declaration),
                    Some(SourceNodeParent::Parent(owner_declaration))
                        if owner_declarations.contains(&owner_declaration)
                            && store.source_node_kind(owner_declaration)
                                == Some(if interface_owner {
                                    SyntaxKind::InterfaceDeclaration
                                } else {
                                    SyntaxKind::TypeLiteral
                                })
                )
                || signature.declaration() != Some(*declaration)
                || signature.flags() & !allowed_flags != SignatureFlags::NONE
                || !valid_declared_method_type_parameters(store, signature, *declaration)
                || signature.this_parameter().is_some()
                || signature.resolved_min_argument_count() != -1
                || signature.resolved_type_predicate().is_some()
                || signature.target().is_some()
                || signature.mapper().is_some()
                || signature.isolated_signature_type().is_some()
                || signature.composite().is_some()
                || store.signature_has_circular_return_type(callable.signature)
                || store.signature_links(*declaration)
                    != Some(&SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolved(callable.signature),
                        ..SignatureLinks::default()
                    })
            {
                return None;
            }
            let return_type = callable.return_type?;
            let annotation = store.source_direct_type_annotation(*declaration)?;
            if validated_method_annotation_type(store, annotation) != Some(return_type) {
                return None;
            }
            for type_parameter in signature.type_parameters() {
                let TypeData::TypeParameter(data) = store.type_payload(*type_parameter)?.data()
                else {
                    return None;
                };
                edges.push(*type_parameter);
                edges.extend(data.constraint);
                edges.extend(data.resolved_default_type);
            }
            edges.extend(callable.parameters.iter().copied());
            edges.extend(callable.rest_parameter);
            edges.push(return_type);
        }

        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

pub(super) fn valid_declared_method_type_parameters(
    store: &CanonicalTypeMapperStore,
    signature: &super::signatures::Signature,
    declaration: ts_ast::NodeRef,
) -> bool {
    if signature.type_parameters().is_empty() {
        return true;
    }
    let mut declarations = Vec::with_capacity(signature.type_parameters().len());
    for index in 0..declaration.node.index() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let parameter = ts_ast::NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        if store.source_node_kind(parameter) == Some(SyntaxKind::TypeParameter)
            && store.source_node_parent(parameter) == Some(SourceNodeParent::Parent(declaration))
        {
            declarations.push(parameter);
        }
    }
    if declarations.len() != signature.type_parameters().len() {
        return false;
    }
    let mut symbols = HashSet::with_capacity(signature.type_parameters().len());
    let mut default_seen = false;
    signature
        .type_parameters()
        .iter()
        .copied()
        .zip(declarations)
        .all(|(type_, expected_declaration)| {
            let Some(symbol) = cached_ordinary_type_parameter_owner(store, type_) else {
                return false;
            };
            let Some(record) = store.symbol(symbol) else {
                return false;
            };
            let Some([parameter]) = record.declarations() else {
                return false;
            };
            let Some(TypeData::TypeParameter(data)) =
                store.type_payload(type_).map(super::TypeRecord::data)
            else {
                return false;
            };
            if !symbols.insert(symbol)
                || record.flags() != SymbolFlags::TYPE_PARAMETER
                || record.check_flags() != CheckFlags::NONE
                || record.value_declaration().is_some()
                || record.members().is_some()
                || record.exports().is_some()
                || record.parent().is_some()
                || record.export_symbol().is_some()
                || store.get_merged_symbol(symbol) != Some(symbol)
                || *parameter != expected_declaration
                || store.source_node_kind(*parameter) != Some(SyntaxKind::TypeParameter)
                || store.source_node_parent(*parameter)
                    != Some(SourceNodeParent::Parent(declaration))
                || data.is_this_type
                || data.target.is_some()
                || data.mapper.is_some()
                || data
                    .constraint
                    .is_some_and(|constraint| store.type_payload(constraint).is_none())
                || data
                    .resolved_default_type
                    .is_some_and(|default_type| store.type_payload(default_type).is_none())
                || default_seen && data.resolved_default_type.is_none()
            {
                return false;
            }
            default_seen |= data.resolved_default_type.is_some();
            true
        })
}

fn validated_method_signature_parameter_types(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
) -> Option<Vec<TypeId>> {
    let record = store.signature(signature)?;
    let declaration = record.declaration()?;
    let mut parameter_types = Vec::with_capacity(record.parameters().len());
    for parameter in record.parameters() {
        let symbol = store.symbol(*parameter)?;
        let [parameter_declaration] = symbol.declarations()? else {
            return None;
        };
        let links = store.value_symbol_links(*parameter)?;
        let type_ = links.resolved_type?;
        if symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol.check_flags() != CheckFlags::NONE
            || symbol.value_declaration() != Some(*parameter_declaration)
            || symbol.members().is_some()
            || symbol.exports().is_some()
            || symbol.parent().is_some()
            || symbol.export_symbol().is_some()
            || store.get_merged_symbol(*parameter) != Some(*parameter)
            || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::Parameter)
            || store.source_node_parent(*parameter_declaration)
                != Some(SourceNodeParent::Parent(declaration))
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            || store.type_payload(type_).is_none()
        {
            return None;
        }
        let annotation = store.source_direct_type_annotation(*parameter_declaration)?;
        let annotated = validated_method_annotation_type(store, annotation)?;
        if annotated != type_ {
            let undefined = store.intrinsic_bootstrap()?.undefined_type;
            let TypeData::Union(union) = store.type_payload(type_)?.data() else {
                return None;
            };
            if union.union.types.len() != 2
                || !union.union.types.contains(&annotated)
                || !union.union.types.contains(&undefined)
            {
                return None;
            }
        }
        parameter_types.push(type_);
    }
    if store
        .callable_signature_parameter_types(signature)
        .is_some_and(|cached| cached != parameter_types.as_slice())
    {
        return None;
    }
    Some(parameter_types)
}

fn validated_method_annotation_type(
    store: &CanonicalTypeMapperStore,
    annotation: ts_ast::NodeRef,
) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let kind = store.source_node_kind(annotation)?;
    let null_literal = if kind == SyntaxKind::LiteralType {
        let index = annotation.node.index().checked_sub(1)?;
        let literal = ts_ast::NodeRef::new(
            annotation.arena,
            annotation.file,
            ts_ast::NodeId::new(u32::try_from(index).ok()?),
        );
        store.source_node_kind(literal) == Some(SyntaxKind::NullKeyword)
            && store.source_node_parent(literal) == Some(SourceNodeParent::Parent(annotation))
    } else {
        false
    };
    let intrinsic = match kind {
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
        SyntaxKind::LiteralType if null_literal => Some(bootstrap.null_type),
        _ => None,
    };
    let Some(links) = store.type_node_links(annotation) else {
        return intrinsic;
    };
    let resolved = links.resolved_type?;
    if links
        != &(TypeNodeLinks {
            resolved_type: Some(resolved),
            ..TypeNodeLinks::default()
        })
        || intrinsic.is_some_and(|expected| expected != resolved)
        || store.type_payload(resolved).is_none()
    {
        return None;
    }
    Some(resolved)
}

fn validate_stored_class_method_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let method_symbol = store.type_payload(type_)?.symbol()?;
    let method = store.symbol(method_symbol)?;
    if !method.flags().contains(SymbolFlags::METHOD) {
        return None;
    }

    let family = CallableFamily::DeclaredCallSignatures;
    let authenticated = (|| {
        let [declaration] = method.declarations()? else {
            return None;
        };
        let declaration = *declaration;
        let owner = method.parent()?;
        let class = store.symbol(owner)?;
        let [class_declaration] = class.declarations()? else {
            return None;
        };
        let instance = store.declared_type_links(owner)?.declared_type?;
        let value = store.value_symbol_links(owner)?.resolved_type?;
        if method.flags() != SymbolFlags::METHOD
            || method.check_flags() != CheckFlags::NONE
            || method.name().is_reserved_member_name()
            || method.name().is_private_identifier()
            || method.name().is_late_bound()
            || method.value_declaration() != Some(declaration)
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || store.get_merged_symbol(method_symbol) != Some(method_symbol)
            || !class.flags().contains(SymbolFlags::CLASS)
            || store.get_merged_symbol(owner) != Some(owner)
            || store.source_node_kind(declaration) != Some(SyntaxKind::MethodDeclaration)
            || store.source_node_parent(declaration)
                != Some(SourceNodeParent::Parent(*class_declaration))
            || store.value_symbol_links(method_symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            || validate_class_heritage_members(store, instance)
                != ClassHeritageMembersValidation::Valid
        {
            return None;
        }

        let member_count = [instance, value]
            .into_iter()
            .filter(|class_type| {
                store
                    .type_payload(*class_type)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get(method.name()))
                    == Some(method_symbol)
            })
            .count();
        if member_count != 1 {
            return None;
        }

        let projection =
            validate_stored_callable_set_projection_with(store, type_, true, |signature| {
                validated_method_signature_parameter_types(store, signature)
            })?;
        let [callable] = projection.call_signatures.as_ref() else {
            return None;
        };
        let signature = callable.signature;
        let return_type = callable.return_type?;
        if !projection.construct_signatures.is_empty()
            || store.signature(signature)?.declaration() != Some(declaration)
            || store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
        {
            return None;
        }
        let mut edges = callable.parameters.clone();
        edges.extend(callable.rest_parameter);
        edges.push(return_type);
        Some((projection, edges))
    })();

    Some(match authenticated {
        Some((projection, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

fn validate_stored_intersection_callable_set(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredCallableSetValidation {
    let family = CallableFamily::DeclaredCallSignatures;
    let Some(record) = store.type_payload(type_) else {
        return StoredCallableSetValidation::NotCallable;
    };
    if record.flags() != TypeFlags::INTERSECTION
        || !matches!(record.data(), TypeData::Intersection(_))
    {
        return StoredCallableSetValidation::NotCallable;
    }
    let Ok(intersection) = store.validate_intersection_type(type_) else {
        return StoredCallableSetValidation::Malformed { family };
    };
    let Some(structured) = store
        .type_payload(type_)
        .and_then(|record| record.data().structured())
    else {
        return StoredCallableSetValidation::Malformed { family };
    };
    if structured.signatures.is_none() {
        return StoredCallableSetValidation::NotCallable;
    }
    let Some(projection) = validate_stored_callable_set_projection(store, type_, false) else {
        return StoredCallableSetValidation::Malformed { family };
    };
    if projection.call_signatures.is_empty() || !projection.construct_signatures.is_empty() {
        return StoredCallableSetValidation::Malformed { family };
    }

    let mut provider_family = None;
    let mut edges = Vec::new();
    for constituent in intersection.types {
        edges.push(constituent);
        match validate_stored_callable_set(store, constituent) {
            StoredCallableSetValidation::NotCallable => {}
            StoredCallableSetValidation::Pending { family } => {
                return StoredCallableSetValidation::Pending { family };
            }
            StoredCallableSetValidation::Malformed { family } => {
                return StoredCallableSetValidation::Malformed { family };
            }
            StoredCallableSetValidation::Valid {
                family,
                edges: constituent_edges,
                ..
            } => {
                if provider_family.is_none() {
                    provider_family = Some(family);
                } else if provider_family != Some(family) {
                    provider_family = Some(CallableFamily::DeclaredCallSignatures);
                }
                edges.extend(constituent_edges);
            }
        }
    }
    let Some(family) = provider_family else {
        return StoredCallableSetValidation::Malformed { family };
    };
    StoredCallableSetValidation::Valid {
        family,
        projection,
        edges,
    }
}

/// Projects one provider-proven structured-signature cache without changing
/// its order.
///
/// This function does not decide whether `owner` belongs to a callable family.
/// Callers must first prove provider-specific source and cache provenance. It
/// validates the common immutable suffix: a unique call prefix, a unique
/// construct suffix, exact parameter-value caches, and store-owned type edges.
pub(super) fn validate_stored_callable_set_projection(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    strict_variance_exempt: bool,
) -> Option<CallableSetProjection> {
    validate_stored_callable_set_projection_with(
        store,
        owner,
        strict_variance_exempt,
        |signature| {
            store
                .callable_signature_parameter_types(signature)
                .map(<[TypeId]>::to_vec)
        },
    )
}

fn validate_stored_callable_set_projection_with(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    strict_variance_exempt: bool,
    mut parameter_types: impl FnMut(SignatureId) -> Option<Vec<TypeId>>,
) -> Option<CallableSetProjection> {
    let structured = store.type_payload(owner)?.data().structured()?;
    let signatures = structured.signatures.as_deref()?;
    if signatures.is_empty() || structured.call_signature_count > signatures.len() {
        return None;
    }

    let mut unique = HashSet::with_capacity(signatures.len());
    let mut call_signatures = Vec::with_capacity(structured.call_signature_count);
    let mut construct_signatures =
        Vec::with_capacity(signatures.len() - structured.call_signature_count);
    for (index, signature) in signatures.iter().copied().enumerate() {
        if !unique.insert(signature) {
            return None;
        }
        let record = store.signature(signature)?;
        let is_construct = record.flags().contains(SignatureFlags::CONSTRUCT);
        if is_construct != (index >= structured.call_signature_count) {
            return None;
        }
        let mut parameters = parameter_types(signature)?;
        if parameters.len() != record.parameters().len()
            || parameters
                .iter()
                .any(|parameter| store.type_payload(*parameter).is_none())
            || record
                .resolved_return_type()
                .is_some_and(|return_type| store.type_payload(return_type).is_none())
        {
            return None;
        }
        let minimum = usize::try_from(record.min_argument_count()).ok()?;
        if !valid_untyped_javascript_source_signature(store, owner, signature, &parameters, minimum)
        {
            return None;
        }
        let rest_parameter = if record.has_rest_parameter() {
            Some(parameters.pop()?)
        } else {
            None
        };
        if minimum > parameters.len() {
            return None;
        }

        if is_construct {
            construct_signatures.push(signature);
        } else {
            call_signatures.push(ValidatedSingleCallable {
                owner,
                signature,
                parameters,
                rest_parameter,
                min_argument_count: minimum,
                return_type: record.resolved_return_type(),
                strict_variance_exempt,
            });
        }
    }

    Some(CallableSetProjection {
        owner,
        call_signatures: call_signatures.into_boxed_slice(),
        construct_signatures: construct_signatures.into_boxed_slice(),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
        SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, TypeRecord,
        bootstrap::{LiteralTypeCacheError, UnionReduction},
        callables::validate_stored_single_callable,
        calls::{DirectCallApplicability, DirectCallForm, DirectCallRequest, resolve_direct_call},
        mapper::TypeMapper,
        production::GlobalMergeCompletion,
        types::ObjectFlags,
    };

    const DEFAULT_LIBRARY_METHODS: &str = concat!(
        "interface IArguments {} ",
        "interface Array<T> {} ",
        "interface Object {} ",
        "interface Function {} ",
        "interface String { toLowerCase(): string } ",
        "interface Number { toFixed(fractionDigits?: number): string } ",
        "interface Boolean {} ",
        "interface RegExp {} ",
        "interface ReadonlyArray<T> {} ",
        "interface ThisType<T> {}",
    );

    struct PublishedDefaultLibraryMethod {
        type_: TypeId,
        signature: SignatureId,
        method: SemanticSymbolId,
        parameter: Option<SemanticSymbolId>,
        return_annotation: NodeRef,
    }

    struct PublishedInterfaceMethod {
        type_: TypeId,
        signatures: Vec<SignatureId>,
        declarations: Vec<NodeRef>,
        method: SemanticSymbolId,
        parameters: Vec<SemanticSymbolId>,
    }

    fn default_library_context(
        parsed: &ParseResult,
        file: FileId,
        strict_null_checks: bool,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source("\"/project/lib.es5.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn source_callable_context(
        parsed: &ParseResult,
        file: FileId,
        language: CanonicalSourceLanguage,
    ) -> CanonicalCheckerContext<'_> {
        let extension = match language {
            CanonicalSourceLanguage::TypeScript => "ts",
            CanonicalSourceLanguage::JavaScript => "js",
        };
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/{}.{extension}\"", file.index())),
                    language,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        match language {
            CanonicalSourceLanguage::TypeScript => binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap(),
            CanonicalSourceLanguage::JavaScript => binder
                .bind_javascript_declaration_slice(&parsed.arena, file)
                .unwrap(),
        };
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    #[allow(clippy::too_many_lines)] // Preserve the exact test publication order.
    fn publish_default_library_method(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        owner_name: &str,
        method_name: &str,
    ) -> PublishedDefaultLibraryMethod {
        let global_types = context.global_types().clone();
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let owner = store
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source(owner_name))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        let method = store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(method_name))
            .unwrap();
        let declaration = store.symbol(method).unwrap().declarations().unwrap()[0];
        let NodeData::MethodSignatureDeclaration(method_node) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected a default-library method signature")
        };
        let return_annotation = NodeRef::new(
            declaration.arena,
            declaration.file,
            method_node.type_.unwrap(),
        );
        let parameter = method_node.parameters.nodes.first().map(|parameter| {
            let declaration = NodeRef::new(declaration.arena, declaration.file, *parameter);
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the optional fractionDigits parameter")
            };
            let annotation = NodeRef::new(
                declaration.arena,
                declaration.file,
                parameter.type_.unwrap(),
            );
            let symbol = context
                .file(declaration.file)
                .unwrap()
                .1
                .symbol(declaration)
                .unwrap();
            (symbol, annotation)
        });
        let strict = bootstrap.options.strict_null_checks;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let undefined = bootstrap.undefined_type;
        let store = context.store_mut_for_test();
        let parameter_type = parameter.map(|_| {
            if strict {
                store
                    .expression_union_type_with_global_types(
                        &global_types,
                        &[number, undefined],
                        UnionReduction::Literal,
                    )
                    .unwrap()
            } else {
                number
            }
        });
        assert!(store.set_type_node_links(
            return_annotation,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        if let Some((symbol, annotation)) = parameter {
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: parameter_type,
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        let type_ = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                Vec::new(),
                None,
                parameter.map(|(symbol, _)| symbol).into_iter().collect(),
                Some(string),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(store.set_function_signature_return_annotation(
            signature,
            return_annotation,
            false,
        ));
        assert!(store.set_callable_signature_parameter_types_batch(vec![(
            signature,
            parameter_type.into_iter().collect()
        ),]));
        PublishedDefaultLibraryMethod {
            type_,
            signature,
            method,
            parameter: parameter.map(|(symbol, _)| symbol),
            return_annotation,
        }
    }

    fn publish_interface_method(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        owner_name: &str,
        method_name: &str,
        publish_keyword_annotations: bool,
    ) -> PublishedInterfaceMethod {
        let global_types = context.global_types().clone();
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let owner = store
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source(owner_name))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        let method = store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(method_name))
            .and_then(|method| store.get_merged_symbol(method))
            .unwrap();
        let declarations = store
            .symbol(method)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let any_array = global_types.any_array_type;
        let plans = declarations
            .iter()
            .copied()
            .map(|declaration| {
                let NodeData::MethodSignatureDeclaration(method) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("expected an interface method signature")
                };
                let parameters = method
                    .parameters
                    .nodes
                    .iter()
                    .map(|parameter| {
                        let declaration =
                            NodeRef::new(declaration.arena, declaration.file, *parameter);
                        let NodeData::ParameterDeclaration(parameter) =
                            &parsed.arena.get(declaration.node).unwrap().data
                        else {
                            panic!("expected an interface method parameter")
                        };
                        let annotation = NodeRef::new(
                            declaration.arena,
                            declaration.file,
                            parameter.type_.unwrap(),
                        );
                        let type_ = match parsed.arena.get(annotation.node).unwrap().kind {
                            SyntaxKind::StringKeyword => string,
                            SyntaxKind::NumberKeyword => number,
                            SyntaxKind::ArrayType => any_array,
                            _ => panic!("unexpected interface method parameter type"),
                        };
                        let symbol = context
                            .file(declaration.file)
                            .unwrap()
                            .1
                            .symbol(declaration)
                            .unwrap();
                        (
                            symbol,
                            annotation,
                            type_,
                            parameter.dot_dot_dot_token.is_some(),
                        )
                    })
                    .collect::<Vec<_>>();
                let annotation =
                    NodeRef::new(declaration.arena, declaration.file, method.type_.unwrap());
                let return_type = match parsed.arena.get(annotation.node).unwrap().kind {
                    SyntaxKind::StringKeyword => string,
                    SyntaxKind::NumberKeyword => number,
                    SyntaxKind::VoidKeyword => void,
                    _ => panic!("unexpected interface method return type"),
                };
                (declaration, parameters, annotation, return_type)
            })
            .collect::<Vec<_>>();

        let store = context.store_mut_for_test();
        if store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .is_none()
        {
            let interface = store
                .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
                .unwrap();
            assert!(store.set_declared_type_links(
                owner,
                DeclaredTypeLinks {
                    declared_type: Some(interface),
                    ..DeclaredTypeLinks::default()
                },
            ));
        }
        let type_ = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::with_capacity(plans.len());
        let mut all_parameters = Vec::new();
        for (declaration, parameters, annotation, return_type) in plans {
            if publish_keyword_annotations
                || !store
                    .source_node_kind(annotation)
                    .is_some_and(SyntaxKind::is_keyword_type)
            {
                assert!(store.set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(return_type),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
            for (symbol, annotation, type_, _) in &parameters {
                if publish_keyword_annotations
                    || !store
                        .source_node_kind(*annotation)
                        .is_some_and(SyntaxKind::is_keyword_type)
                {
                    assert!(store.set_type_node_links(
                        *annotation,
                        TypeNodeLinks {
                            resolved_type: Some(*type_),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                assert!(store.set_value_symbol_links(
                    *symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(*type_),
                        ..ValueSymbolLinks::default()
                    },
                ));
                all_parameters.push(*symbol);
            }
            let rest = parameters.last().is_some_and(|(_, _, _, rest)| *rest);
            let minimum = parameters.len().saturating_sub(usize::from(rest));
            let signature = store
                .alloc_signature(
                    if rest {
                        SignatureFlags::HAS_REST_PARAMETER
                    } else {
                        SignatureFlags::NONE
                    },
                    Some(declaration),
                    Vec::new(),
                    None,
                    parameters.iter().map(|(symbol, _, _, _)| *symbol).collect(),
                    Some(return_type),
                    None,
                    i32::try_from(minimum).unwrap(),
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
        }
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            type_,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));

        PublishedInterfaceMethod {
            type_,
            signatures,
            declarations,
            method,
            parameters: all_parameters,
        }
    }

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn signature(
        store: &mut CanonicalTypeMapperStore,
        flags: SignatureFlags,
        parameter_types: &[TypeId],
        minimum: i32,
        return_type: TypeId,
    ) -> SignatureId {
        let parameters = parameter_types
            .iter()
            .enumerate()
            .map(|(index, _)| {
                store
                    .alloc_symbol(SymbolData::new(
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                        EscapedName::source(format!("p{index}")),
                    ))
                    .unwrap()
            })
            .collect();
        store
            .alloc_signature(
                flags,
                None,
                Vec::new(),
                None,
                parameters,
                Some(return_type),
                None,
                minimum,
            )
            .unwrap()
    }

    fn owner(
        store: &mut CanonicalTypeMapperStore,
        calls: Vec<SignatureId>,
        constructs: Vec<SignatureId>,
    ) -> TypeId {
        let owner = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            owner,
            None,
            None,
            Some(calls),
            Some(constructs),
            None,
        ));
        owner
    }

    fn project(
        store: &CanonicalTypeMapperStore,
        owner: TypeId,
        parameter_types: &HashMap<SignatureId, Vec<TypeId>>,
    ) -> Option<CallableSetProjection> {
        validate_stored_callable_set_projection_with(store, owner, false, |signature| {
            parameter_types.get(&signature).cloned()
        })
    }

    #[test]
    fn call_order_and_construct_partition_are_preserved() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let first = signature(&mut store, SignatureFlags::NONE, &[number], 1, string);
        let second = signature(&mut store, SignatureFlags::NONE, &[string], 1, number);
        let construct = signature(&mut store, SignatureFlags::CONSTRUCT, &[number], 1, string);
        let owner = owner(&mut store, vec![second, first], vec![construct]);
        let parameter_types = HashMap::from([
            (first, vec![number]),
            (second, vec![string]),
            (construct, vec![number]),
        ]);

        let projected = project(&store, owner, &parameter_types).unwrap();
        assert_eq!(projected.owner, owner);
        assert_eq!(
            projected
                .call_signatures
                .iter()
                .map(|callable| callable.signature)
                .collect::<Vec<_>>(),
            vec![second, first]
        );
        assert_eq!(projected.construct_signatures.as_ref(), &[construct]);
    }

    #[test]
    fn class_constructor_providers_preserve_abstract_identity_and_canonical_unions() {
        let parsed = parse_source_file(concat!(
            "abstract class Abstract { value!: string; } ",
            "class Concrete {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_497);
        let mut context =
            source_callable_context(&parsed, file, CanonicalSourceLanguage::TypeScript);

        context.check_source_file(file).unwrap();

        let mut values = Vec::new();
        for (name, abstract_class) in [("Abstract", true), ("Concrete", false)] {
            let store = context.store();
            let owner = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap();
            let (value, signature) = authenticated_class_constructor_value(store, owner).unwrap();
            let instance = store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            assert_eq!(store.validate_union_constituent(instance), Ok(()));
            let StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            } = validate_stored_callable_set(store, value)
            else {
                panic!("{name} must retain one authenticated constructor provider")
            };
            assert_eq!(family, CallableFamily::DeclaredCallSignatures);
            assert_eq!(projection.owner, value);
            assert!(projection.call_signatures.is_empty());
            assert_eq!(projection.construct_signatures.as_ref(), &[signature]);
            assert_eq!(edges, [instance]);
            assert_eq!(
                store.signature(signature).unwrap().flags(),
                SignatureFlags::CONSTRUCT
                    | if abstract_class {
                        SignatureFlags::ABSTRACT
                    } else {
                        SignatureFlags::NONE
                    },
            );
            values.push(value);

            let prototype = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source("prototype"))
                .unwrap();
            assert!(context.store_mut_for_test().set_value_symbol_links(
                prototype,
                ValueSymbolLinks {
                    resolved_type: Some(instance),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                authenticated_class_constructor_value(context.store(), owner),
                Some((value, signature)),
            );
        }

        let union = context
            .store_mut_for_test()
            .literal_union_type(&values, None)
            .unwrap();
        let TypeData::Union(candidates) = context.store().type_payload(union).unwrap().data()
        else {
            panic!("class constructor values must retain their real canonical union")
        };
        assert_eq!(candidates.union.types.len(), 2);
        assert!(
            values
                .iter()
                .all(|value| candidates.union.types.contains(value))
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context
                .store_mut_for_test()
                .literal_union_type(&values, None),
            Ok(union),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn forged_class_constructor_providers_are_rejected_before_union_creation() {
        for poison in 0..3 {
            let parsed = parse_source_file("abstract class Model { value!: string; }");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_498 + poison);
            let mut context =
                source_callable_context(&parsed, file, CanonicalSourceLanguage::TypeScript);
            context.check_source_file(file).unwrap();
            let owner = {
                let store = context.store();
                store
                    .intrinsic_bootstrap()
                    .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                    .and_then(|globals| globals.get_source("Model"))
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap()
            };
            let (value, signature) =
                authenticated_class_constructor_value(context.store(), owner).unwrap();
            let instance = context
                .store()
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            match poison {
                0 => assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_flags(signature, SignatureFlags::CONSTRUCT)
                ),
                1 => {
                    let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_signature_resolved_return_type(signature, Some(wrong))
                    );
                }
                2 => {
                    assert!(context.store_mut_for_test().set_type_object_flags(
                        instance,
                        ObjectFlags::CLASS | ObjectFlags::REFERENCE,
                    ));
                }
                _ => unreachable!("unexpected class cache corruption"),
            }
            let state = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(matches!(
                validate_stored_callable_set(context.store(), value),
                StoredCallableSetValidation::Malformed {
                    family: CallableFamily::DeclaredCallSignatures,
                }
            ));
            assert_eq!(
                context.store().validate_union_constituent(value),
                Err(LiteralTypeCacheError::InvalidCachedUnion(value)),
            );
            assert_eq!(
                context.store().validate_union_constituent(instance),
                Err(LiteralTypeCacheError::InvalidCachedUnion(instance)),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                state,
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn duplicate_signature_ids_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[], 0, number);
        let owner = owner(&mut store, vec![signature, signature], Vec::new());
        let parameter_types = HashMap::from([(signature, Vec::new())]);

        assert_eq!(project(&store, owner, &parameter_types), None);
    }

    #[test]
    fn call_and_construct_flags_must_match_the_stored_prefix() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let call = signature(&mut store, SignatureFlags::NONE, &[], 0, number);
        let construct = signature(&mut store, SignatureFlags::CONSTRUCT, &[], 0, number);
        let parameter_types = HashMap::from([(call, Vec::new()), (construct, Vec::new())]);
        let construct_in_call_prefix = owner(&mut store, vec![construct], Vec::new());
        let call_in_construct_suffix = owner(&mut store, Vec::new(), vec![call]);

        assert_eq!(
            project(&store, construct_in_call_prefix, &parameter_types),
            None
        );
        assert_eq!(
            project(&store, call_in_construct_suffix, &parameter_types),
            None
        );
    }

    #[test]
    fn missing_or_malformed_parameter_caches_are_rejected() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[number], 1, string);
        let owner = owner(&mut store, vec![signature], Vec::new());

        assert_eq!(project(&store, owner, &HashMap::new()), None);
        assert_eq!(
            project(&store, owner, &HashMap::from([(signature, Vec::new())])),
            None
        );
    }

    #[test]
    fn foreign_types_and_owners_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = signature(&mut store, SignatureFlags::NONE, &[number], 1, number);
        let owner = owner(&mut store, vec![signature], Vec::new());
        let foreign = initialized_store();
        let foreign_number = foreign.intrinsic_bootstrap().unwrap().number_type;

        assert_eq!(
            project(
                &store,
                owner,
                &HashMap::from([(signature, vec![foreign_number])])
            ),
            None
        );
        assert_eq!(
            project(
                &store,
                foreign_number,
                &HashMap::from([(signature, vec![number])])
            ),
            None
        );
    }

    #[test]
    fn invalid_minimum_and_rest_shapes_are_rejected() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let invalid_minimum = signature(&mut store, SignatureFlags::NONE, &[], 1, number);
        let missing_rest = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[],
            0,
            number,
        );
        let invalid_rest_minimum = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            1,
            number,
        );
        let parameter_types = HashMap::from([
            (invalid_minimum, Vec::new()),
            (missing_rest, Vec::new()),
            (invalid_rest_minimum, vec![number]),
        ]);
        let invalid_minimum_owner = owner(&mut store, vec![invalid_minimum], Vec::new());
        let missing_rest_owner = owner(&mut store, vec![missing_rest], Vec::new());
        let invalid_rest_minimum_owner = owner(&mut store, vec![invalid_rest_minimum], Vec::new());

        assert_eq!(
            project(&store, invalid_minimum_owner, &parameter_types),
            None
        );
        assert_eq!(project(&store, missing_rest_owner, &parameter_types), None);
        assert_eq!(
            project(&store, invalid_rest_minimum_owner, &parameter_types),
            None,
        );
    }

    #[test]
    fn rest_only_callables_have_zero_fixed_arity() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let rest = signature(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            0,
            number,
        );
        let owner = owner(&mut store, vec![rest], Vec::new());
        let projected = project(&store, owner, &HashMap::from([(rest, vec![number])])).unwrap();
        let [callable] = projected.call_signatures.as_ref() else {
            panic!("expected one call signature")
        };
        assert!(callable.parameters.is_empty());
        assert_eq!(callable.rest_parameter, Some(number));
        assert_eq!(callable.min_argument_count, 0);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Compare raw and effective arity for both JavaScript owners.
    fn untyped_javascript_source_callables_keep_raw_arity_and_allow_zero_arguments() {
        for (index, (source, kind, expected_family)) in [
            (
                "function named(value) {}",
                SyntaxKind::FunctionDeclaration,
                CallableFamily::FunctionDeclaration,
            ),
            (
                "const object = { run: (value) => {} };",
                SyntaxKind::ArrowFunction,
                CallableFamily::ArrowFunction,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_javascript_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_422 + u32::try_from(index).unwrap());
            let mut context =
                source_callable_context(&parsed, file, CanonicalSourceLanguage::JavaScript);
            context.check_source_file(file).unwrap();

            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let type_ = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            let StoredCallableSetValidation::Valid {
                family, projection, ..
            } = validate_stored_callable_set(context.store(), type_)
            else {
                panic!("expected an authenticated untyped JavaScript callable")
            };
            assert_eq!(family, expected_family);
            let [callable] = projection.call_signatures.as_ref() else {
                panic!("expected one JavaScript source signature")
            };
            let signature = context.store().signature(callable.signature).unwrap();
            assert_eq!(
                signature.flags(),
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            );
            assert_eq!(signature.min_argument_count(), 1);
            assert_eq!(callable.min_argument_count, 1);
            assert_eq!(callable.parameters.len(), 1);

            let global_types = context.global_types().clone();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let no_arguments = resolve_direct_call(
                context.store_mut_for_test(),
                &global_types,
                false,
                DirectCallRequest {
                    form: DirectCallForm::Call,
                    optional_chain: false,
                    type_argument_count: 0,
                    has_spread_argument: false,
                    callee: type_,
                    arguments: &[],
                },
            )
            .unwrap();
            assert_eq!(no_arguments.projection.minimum_argument_count, 0);
            assert_eq!(no_arguments.projection.maximum_argument_count, 1);
            assert_eq!(
                no_arguments.applicability,
                DirectCallApplicability::Applicable
            );

            let extra_arguments = resolve_direct_call(
                context.store_mut_for_test(),
                &global_types,
                false,
                DirectCallRequest {
                    form: DirectCallForm::Call,
                    optional_chain: false,
                    type_argument_count: 0,
                    has_spread_argument: false,
                    callee: type_,
                    arguments: &[number, number, number],
                },
            )
            .unwrap();
            assert_eq!(extra_arguments.projection.minimum_argument_count, 0);
            assert_eq!(extra_arguments.projection.maximum_argument_count, 1);
            assert_eq!(
                extra_arguments.applicability,
                DirectCallApplicability::TooManyArguments {
                    expected_at_most: 1,
                    actual: 3,
                },
            );
        }
    }

    #[test]
    fn forged_javascript_arity_flags_require_an_untyped_source_callable() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let void = bootstrap.void_type;
        let signature = signature(
            &mut store,
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            &[any],
            1,
            void,
        );
        let owner = owner(&mut store, vec![signature], Vec::new());
        assert_eq!(
            project(&store, owner, &HashMap::from([(signature, vec![any])])),
            None,
        );

        let parsed = parse_source_file("function typed(value: number): void {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_424);
        let mut context =
            source_callable_context(&parsed, file, CanonicalSourceLanguage::TypeScript);
        context.check_source_file(file).unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let type_ = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(type_)
            .unwrap()
            .signature;
        assert!(
            context
                .store_mut_for_test()
                .set_signature_flags(signature, SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,)
        );
        assert!(matches!(
            validate_stored_callable_set(context.store(), type_),
            StoredCallableSetValidation::Malformed {
                family: CallableFamily::FunctionDeclaration,
            }
        ));
    }

    #[test]
    fn default_library_method_callables_preserve_arity_variance_and_warm_identity() {
        for (index, strict) in [false, true].into_iter().enumerate() {
            let parsed = parse_source_file(DEFAULT_LIBRARY_METHODS);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_412 + u32::try_from(index).unwrap());
            let mut context = default_library_context(&parsed, file, strict);

            for (owner_name, method_name, parameter_count) in
                [("Number", "toFixed", 1), ("String", "toLowerCase", 0)]
            {
                let method =
                    publish_default_library_method(&mut context, &parsed, owner_name, method_name);
                let store = context.store();
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                let before = (
                    store.type_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                );
                let StoredCallableSetValidation::Valid {
                    family,
                    projection,
                    edges,
                } = validate_stored_callable_set(store, method.type_)
                else {
                    panic!("expected authenticated {owner_name}.{method_name}")
                };
                assert_eq!(family, CallableFamily::DeclaredCallSignatures);
                assert_eq!(projection.owner, method.type_);
                assert!(projection.construct_signatures.is_empty());
                let [callable] = projection.call_signatures.as_ref() else {
                    panic!("expected one default-library method signature")
                };
                assert_eq!(callable.signature, method.signature);
                assert_eq!(callable.parameters.len(), parameter_count);
                assert_eq!(callable.min_argument_count, 0);
                assert_eq!(callable.return_type, Some(bootstrap.string_type));
                assert!(callable.rest_parameter.is_none());
                assert!(callable.strict_variance_exempt);
                assert_eq!(edges.last(), Some(&bootstrap.string_type));
                if let Some(parameter) = method.parameter {
                    let expected = store
                        .value_symbol_links(parameter)
                        .and_then(|links| links.resolved_type)
                        .unwrap();
                    assert_eq!(callable.parameters.as_slice(), &[expected]);
                    assert_eq!(edges.first(), Some(&expected));
                    if strict {
                        let TypeData::Union(union) = store.type_payload(expected).unwrap().data()
                        else {
                            panic!("strict optional parameters must include undefined")
                        };
                        assert!(union.union.types.contains(&bootstrap.number_type));
                        assert!(union.union.types.contains(&bootstrap.undefined_type));
                    } else {
                        assert_eq!(expected, bootstrap.number_type);
                    }
                }
                assert_eq!(
                    (
                        store.type_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.checker_link_allocated_lengths(),
                    ),
                    before,
                );
            }
        }
    }

    #[test]
    fn default_library_method_callables_authenticate_transient_merged_interface_owners() {
        let library = parse_source_file(DEFAULT_LIBRARY_METHODS);
        let augmentation = parse_source_file(concat!(
            "interface Number { marker: number } declare var Number: any; ",
            "interface String { marker: string } declare var String: any;",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(
            augmentation.diagnostics.is_empty(),
            "{:?}",
            augmentation.diagnostics,
        );
        let files = [
            (FileId::new(4_420), &library),
            (FileId::new(4_421), &augmentation),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/lib-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        true,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        for (owner_name, method_name) in [("Number", "toFixed"), ("String", "toLowerCase")] {
            let method =
                publish_default_library_method(&mut context, &library, owner_name, method_name);
            let store = context.store();
            let original_owner = store.symbol(method.method).unwrap().parent().unwrap();
            let owner = store.get_merged_symbol(original_owner).unwrap();
            assert_ne!(original_owner, owner);
            assert!(
                store
                    .symbol(owner)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::TRANSIENT)
            );
            assert!(matches!(
                validate_stored_callable_set(store, method.type_),
                StoredCallableSetValidation::Valid {
                    family: CallableFamily::DeclaredCallSignatures,
                    ..
                }
            ));
        }
    }

    #[test]
    fn default_library_method_callables_reject_forged_cache_and_global_ownership() {
        for poison in 0..5 {
            let parsed = parse_source_file(DEFAULT_LIBRARY_METHODS);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_414 + poison);
            let mut context = default_library_context(&parsed, file, true);
            let method = publish_default_library_method(&mut context, &parsed, "Number", "toFixed");
            let string_wrapper = context.global_types().string_type;
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let globals = bootstrap.globals;
            match poison {
                0 => {
                    assert!(store.set_value_symbol_links(
                        method.method,
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                1 => {
                    assert!(store.set_signature_flags(method.signature, SignatureFlags::CONSTRUCT));
                }
                2 => {
                    assert!(store.set_value_symbol_links(
                        method.parameter.unwrap(),
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                3 => {
                    assert!(store.set_type_node_links(
                        method.return_annotation,
                        TypeNodeLinks {
                            resolved_type: Some(number),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                4 => {
                    let string_owner = store
                        .type_payload(string_wrapper)
                        .and_then(TypeRecord::symbol)
                        .unwrap();
                    assert!(
                        store
                            .insert_symbol(globals, EscapedName::source("Number"), string_owner)
                            .is_some()
                    );
                }
                _ => unreachable!("poison cases are bounded"),
            }
            assert!(
                matches!(
                    validate_stored_callable_set(store, method.type_),
                    StoredCallableSetValidation::Malformed {
                        family: CallableFamily::DeclaredCallSignatures,
                    }
                ),
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn interface_method_overloads_preserve_order_rest_and_binder_parameter_types() {
        let parsed = parse_source_file(&format!(
            "{DEFAULT_LIBRARY_METHODS} \
             interface Contract {{ \
                 run(value: string): number; \
                 run(...args: any[]): void; \
             }}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_425);
        let mut context = default_library_context(&parsed, file, false);
        let method = publish_interface_method(&mut context, &parsed, "Contract", "run", true);
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let any_array = context.global_types().any_array_type;
        let before = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        for _ in 0..2 {
            let StoredCallableSetValidation::Valid {
                family,
                projection,
                edges,
            } = validate_stored_callable_set(store, method.type_)
            else {
                panic!("expected an authenticated overloaded interface method")
            };
            assert_eq!(family, CallableFamily::DeclaredCallSignatures);
            assert_eq!(projection.owner, method.type_);
            assert!(projection.construct_signatures.is_empty());
            let [fixed, rest] = projection.call_signatures.as_ref() else {
                panic!("expected both interface method overloads")
            };
            assert_eq!(fixed.signature, method.signatures[0]);
            assert_eq!(fixed.parameters.as_slice(), &[bootstrap.string_type]);
            assert_eq!(fixed.min_argument_count, 1);
            assert_eq!(fixed.return_type, Some(bootstrap.number_type));
            assert!(fixed.rest_parameter.is_none());
            assert!(fixed.strict_variance_exempt);
            assert_eq!(rest.signature, method.signatures[1]);
            assert!(rest.parameters.is_empty());
            assert_eq!(rest.rest_parameter, Some(any_array));
            assert_eq!(rest.min_argument_count, 0);
            assert_eq!(rest.return_type, Some(bootstrap.void_type));
            assert!(rest.strict_variance_exempt);
            assert_eq!(
                edges,
                vec![
                    bootstrap.string_type,
                    bootstrap.number_type,
                    any_array,
                    bootstrap.void_type,
                ],
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn interface_method_keywords_can_be_uncached_but_arrays_keep_exact_cached_types() {
        for poison in 0..3 {
            let parsed = parse_source_file(&format!(
                "{DEFAULT_LIBRARY_METHODS} \
                 interface Contract {{ \
                     run(value: string): number; \
                     run(...args: any[]): void; \
                 }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_430 + poison);
            let mut context = default_library_context(&parsed, file, false);
            let method = publish_interface_method(&mut context, &parsed, "Contract", "run", false);
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let number = bootstrap.number_type;
            let returns = method
                .declarations
                .iter()
                .map(|declaration| store.source_direct_type_annotation(*declaration).unwrap())
                .collect::<Vec<_>>();
            let annotations = method
                .parameters
                .iter()
                .map(|parameter| {
                    let declaration = store
                        .symbol(*parameter)
                        .unwrap()
                        .value_declaration()
                        .unwrap();
                    store.source_direct_type_annotation(declaration).unwrap()
                })
                .collect::<Vec<_>>();
            assert!(
                returns
                    .iter()
                    .all(|annotation| store.type_node_links(*annotation).is_none())
            );
            assert!(store.type_node_links(annotations[0]).is_none());
            assert!(
                store
                    .type_node_links(annotations[1])
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );

            let before = (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert!(matches!(
                    validate_stored_callable_set(store, method.type_),
                    StoredCallableSetValidation::Valid {
                        family: CallableFamily::DeclaredCallSignatures,
                        ..
                    }
                ));
                assert_eq!(
                    (
                        store.type_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.checker_link_allocated_lengths(),
                    ),
                    before,
                );
            }

            match poison {
                0 => {
                    assert!(store.set_type_node_links(
                        returns[0],
                        TypeNodeLinks {
                            resolved_type: Some(string),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                1 => {
                    assert!(store.set_type_node_links(
                        annotations[0],
                        TypeNodeLinks {
                            resolved_type: Some(number),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                2 => {
                    assert!(store.set_type_node_links(annotations[1], TypeNodeLinks::default(),));
                }
                _ => unreachable!("poison cases are bounded"),
            }
            assert!(
                matches!(
                    validate_stored_callable_set(store, method.type_),
                    StoredCallableSetValidation::Malformed {
                        family: CallableFamily::DeclaredCallSignatures,
                    }
                ),
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn interface_method_overloads_reject_forged_owner_parameter_and_signature_caches() {
        for poison in 0..4 {
            let parsed = parse_source_file(&format!(
                "{DEFAULT_LIBRARY_METHODS} \
                 interface Contract {{ \
                     run(value: string): number; \
                     run(...args: any[]): void; \
                 }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4_426 + poison);
            let mut context = default_library_context(&parsed, file, false);
            let method = publish_interface_method(&mut context, &parsed, "Contract", "run", true);
            let store = context.store_mut_for_test();
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            match poison {
                0 => {
                    assert!(store.set_value_symbol_links(
                        method.method,
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                1 => {
                    let string = store.intrinsic_bootstrap().unwrap().string_type;
                    assert!(store.set_value_symbol_links(
                        method.parameters[0],
                        ValueSymbolLinks {
                            resolved_type: Some(string),
                            target: Some(method.method),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                2 => {
                    assert!(store.set_structured_type_members(
                        method.type_,
                        None,
                        None,
                        Some(vec![method.signatures[1], method.signatures[0]]),
                        None,
                        None,
                    ));
                }
                3 => {
                    assert!(store.set_signature_links(
                        method.declarations[0],
                        SignatureLinks::default(),
                    ));
                }
                _ => unreachable!("poison cases are bounded"),
            }
            assert!(
                matches!(
                    validate_stored_callable_set(store, method.type_),
                    StoredCallableSetValidation::Malformed {
                        family: CallableFamily::DeclaredCallSignatures,
                    }
                ),
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn instantiated_array_methods_preserve_mapped_overloads_and_reject_forged_proxies() {
        let parsed = parse_source_file(concat!(
            "interface IArguments {} ",
            "interface ConcatArray<T> {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} ",
            "interface Object {} ",
            "interface Function {} ",
            "interface String { toLowerCase(): string } ",
            "interface Number { toFixed(fractionDigits?: number): string } ",
            "interface Boolean {} ",
            "interface RegExp {} ",
            "interface ReadonlyArray<T> {} ",
            "interface ThisType<T> {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_434);
        let mut context = default_library_context(&parsed, file, false);
        let global_types = context.global_types().clone();
        let concat_array = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("ConcatArray"))
            .unwrap();
        context.get_declared_type_of_symbol(concat_array).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let receiver = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = super::super::DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let source = super::super::object_members::materialize_global_array_concat_method(
            store,
            &host,
            &global_types,
            receiver,
        )
        .unwrap()
        .unwrap();
        let method = store.type_payload(source).unwrap().symbol().unwrap();
        let instantiated =
            super::super::instantiated_members::instantiate_published_generic_interface_method(
                store,
                &global_types,
                receiver,
                method,
            )
            .unwrap();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        let mut proxy = None;
        for _ in 0..2 {
            let StoredCallableSetValidation::Valid {
                family, projection, ..
            } = validate_stored_callable_set(store, instantiated)
            else {
                panic!("expected both receiver-specialized Array.concat overloads")
            };
            assert_eq!(family, CallableFamily::DeclaredCallSignatures);
            assert_eq!(projection.call_signatures.len(), 2);
            assert!(projection.construct_signatures.is_empty());
            for callable in &projection.call_signatures {
                assert!(callable.parameters.is_empty());
                assert!(callable.rest_parameter.is_some());
                assert_eq!(callable.return_type, Some(receiver));
                let [parameter] = store.signature(callable.signature).unwrap().parameters() else {
                    panic!("each specialized overload must retain its rest proxy")
                };
                proxy = Some(*parameter);
            }
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        let proxy = proxy.unwrap();
        let links = store.value_symbol_links(proxy).unwrap().clone();
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                mapper: None,
                ..links
            },
        ));
        assert!(matches!(
            validate_stored_callable_set(store, instantiated),
            StoredCallableSetValidation::Malformed {
                family: CallableFamily::DeclaredCallSignatures,
            }
        ));
    }

    #[test]
    fn readonly_array_concat_overloads_preserve_mutable_returns_and_warm_identity() {
        let parsed = parse_source_file(concat!(
            "interface IArguments {} ",
            "interface ConcatArray<T> {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} ",
            "interface Object {} ",
            "interface Function {} ",
            "interface String { toLowerCase(): string } ",
            "interface Number { toFixed(fractionDigits?: number): string } ",
            "interface Boolean {} ",
            "interface RegExp {} ",
            "interface ReadonlyArray<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} ",
            "interface ThisType<T> {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_435);
        let mut context = default_library_context(&parsed, file, false);
        let global_types = context.global_types().clone();
        let concat_array = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("ConcatArray"))
            .unwrap();
        context.get_declared_type_of_symbol(concat_array).unwrap();
        let (number, readonly_parameter) = {
            let store = context.store();
            let TypeData::Interface(readonly) = store
                .type_payload(global_types.readonly_array_type)
                .unwrap()
                .data()
            else {
                panic!("ReadonlyArray must retain its global interface identity")
            };
            (
                store.intrinsic_bootstrap().unwrap().number_type,
                readonly.reference.resolved_type_arguments.as_ref().unwrap()[0],
            )
        };
        let (readonly_receiver, mutable_return) = {
            let store = context.store_mut_for_test();
            (
                store
                    .create_canonical_array_type(&global_types, number, true)
                    .unwrap(),
                store
                    .create_canonical_array_type(&global_types, number, false)
                    .unwrap(),
            )
        };
        let bound = context.file(file).unwrap().1.clone();
        let host = super::super::DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let mutable_method = store
            .type_payload(global_types.array_type)
            .and_then(TypeRecord::symbol)
            .and_then(|owner| store.symbol(owner))
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("concat"))
            .unwrap();
        let source = super::super::object_members::materialize_global_array_concat_method(
            store,
            &host,
            &global_types,
            readonly_receiver,
        )
        .unwrap()
        .unwrap();
        let method = store.type_payload(source).unwrap().symbol().unwrap();
        let generic_return = store
            .create_canonical_array_type(&global_types, readonly_parameter, false)
            .unwrap();

        assert_ne!(method, mutable_method);
        assert!(store.value_symbol_links(mutable_method).is_none());
        assert_ne!(generic_return, global_types.readonly_array_type);
        let StoredCallableSetValidation::Valid {
            projection: original,
            ..
        } = validate_stored_callable_set(store, source)
        else {
            panic!("expected both authenticated readonly concat declarations")
        };
        assert_eq!(original.call_signatures.len(), 2);
        assert!(
            original
                .call_signatures
                .iter()
                .all(|callable| callable.return_type == Some(generic_return))
        );

        let instantiated =
            super::super::instantiated_members::instantiate_published_generic_interface_method(
                store,
                &global_types,
                readonly_receiver,
                method,
            )
            .unwrap();
        let StoredCallableSetValidation::Valid {
            family, projection, ..
        } = validate_stored_callable_set(store, instantiated)
        else {
            panic!("expected receiver-specialized readonly concat overloads")
        };
        assert_eq!(family, CallableFamily::DeclaredCallSignatures);
        let [arrays, values_or_arrays] = projection.call_signatures.as_ref() else {
            panic!("readonly concat must retain its two declaration overloads")
        };
        assert_eq!(arrays.return_type, Some(mutable_return));
        assert_eq!(values_or_arrays.return_type, Some(mutable_return));
        let arrays_element = store
            .canonical_array_element_type(&global_types, arrays.rest_parameter.unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            validate_direct_generic_reference(store, arrays_element)
                .unwrap()
                .type_arguments,
            vec![number],
        );
        let values_element = store
            .canonical_array_element_type(&global_types, values_or_arrays.rest_parameter.unwrap())
            .unwrap()
            .unwrap();
        let TypeData::Union(values) = store.type_payload(values_element).unwrap().data() else {
            panic!("the second overload must preserve its element-or-array union")
        };
        assert!(values.union.types.contains(&number));
        assert!(values.union.types.contains(&arrays_element));

        let resolution = resolve_direct_call(
            store,
            &global_types,
            false,
            DirectCallRequest {
                form: DirectCallForm::Call,
                optional_chain: false,
                type_argument_count: 0,
                has_spread_argument: false,
                callee: instantiated,
                arguments: &[],
            },
        )
        .unwrap();
        assert_eq!(resolution.projection.return_type, mutable_return);

        let warm = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            super::super::object_members::materialize_global_array_concat_method(
                store,
                &host,
                &global_types,
                readonly_receiver,
            ),
            Ok(Some(source)),
        );
        assert_eq!(
            super::super::instantiated_members::instantiate_published_generic_interface_method(
                store,
                &global_types,
                readonly_receiver,
                method,
            ),
            Ok(instantiated),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn inherited_interface_callables_keep_derived_signatures_before_base_signatures() {
        let parsed = parse_source_file(&format!(
            "{DEFAULT_LIBRARY_METHODS} \
             interface Base {{ (): string }} \
             interface Derived extends Base {{ (key: string): string }}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_419);
        let mut context = default_library_context(&parsed, file, false);
        let derived_symbol = {
            let store = context.store();
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source("Derived"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap()
        };
        let derived = context.get_declared_type_of_symbol(derived_symbol).unwrap();
        let TypeData::Interface(interface) = context.store().type_payload(derived).unwrap().data()
        else {
            panic!("expected a derived callable interface")
        };
        let expected = interface
            .reference
            .object
            .structured
            .signatures
            .as_deref()
            .unwrap();
        let StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        } = validate_stored_callable_set(context.store(), derived)
        else {
            panic!("expected an authenticated inherited callable interface")
        };

        assert_eq!(family, CallableFamily::DeclaredCallSignatures);
        assert_eq!(projection.owner, derived);
        assert!(projection.construct_signatures.is_empty());
        assert_eq!(projection.call_signatures.len(), 2);
        let actual = projection
            .call_signatures
            .iter()
            .map(|callable| callable.signature)
            .collect::<Vec<_>>();
        assert_eq!(actual.as_slice(), expected);
        assert_eq!(projection.call_signatures[0].parameters.len(), 1);
        assert!(projection.call_signatures[1].parameters.is_empty());
        assert_eq!(edges.len(), 3);
    }

    #[test]
    fn method_type_parameter_mapping_preserves_merged_mapper_order() {
        let mut store = initialized_store();
        let source = store.alloc_type_parameter(None).unwrap();
        let intermediate = store.alloc_type_parameter(None).unwrap();
        let target = store.alloc_type_parameter(None).unwrap();
        let first = store.new_simple_type_mapper(source, intermediate).unwrap();
        let second = store.new_simple_type_mapper(intermediate, target).unwrap();
        let merged = store.merge_type_mappers(Some(first), second).unwrap();

        assert_eq!(
            mapped_method_type_parameter(&store, merged, source),
            Some(target)
        );
    }

    #[test]
    fn generic_interface_null_overloads_preserve_source_identity_and_optional_arity() {
        let parsed = parse_source_file(concat!(
            "interface Thenable<Value> { ",
            "then(filter: null): Value; ",
            "then(filter?: null): Value; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_486);
        let mut context =
            source_callable_context(&parsed, file, CanonicalSourceLanguage::TypeScript);

        context.check_source_file(file).unwrap();

        let store = context.store();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let owner = store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("Thenable"))
            .unwrap();
        let method = store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("then"))
            .unwrap();
        let callable = store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let StoredCallableSetValidation::Valid {
            family, projection, ..
        } = validate_stored_callable_set(store, callable)
        else {
            panic!("null-valued then overloads must retain authenticated method callables")
        };
        assert_eq!(family, CallableFamily::DeclaredCallSignatures);
        let [required, optional] = projection.call_signatures.as_ref() else {
            panic!("the binder-owned then method must preserve both overload declarations")
        };
        let null = store.intrinsic_bootstrap().unwrap().null_type;
        assert_eq!(required.parameters, vec![null]);
        assert_eq!(required.min_argument_count, 1);
        assert_eq!(optional.parameters, vec![null]);
        assert_eq!(optional.min_argument_count, 0);
        let optional_parameter = store.signature(optional.signature).unwrap().parameters()[0];

        let warm = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());

        let original = context
            .store()
            .value_symbol_links(optional_parameter)
            .cloned()
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            optional_parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(matches!(
            validate_stored_callable_set(context.store(), callable),
            StoredCallableSetValidation::Malformed {
                family: CallableFamily::DeclaredCallSignatures,
            }
        ));
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(optional_parameter, original)
        );
        assert!(matches!(
            validate_stored_callable_set(context.store(), callable),
            StoredCallableSetValidation::Valid { .. }
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source check covers defaults, variance, and cache poison.
    fn generic_interface_methods_preserve_defaults_variance_and_authenticated_type_identity() {
        let parsed = parse_source_file(concat!(
            "interface Contract<Outer> { ",
            "map<Value = never>(value: Value): Outer; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_485);
        let mut context =
            source_callable_context(&parsed, file, CanonicalSourceLanguage::TypeScript);

        context.check_source_file(file).unwrap();

        let globals = context.store().intrinsic_bootstrap().unwrap().globals;
        let owner = context
            .store()
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("Contract"))
            .unwrap();
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("map"))
            .unwrap();
        let callable = context
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let StoredCallableSetValidation::Valid {
            family, projection, ..
        } = validate_stored_callable_set(context.store(), callable)
        else {
            panic!("a source generic interface method must retain callable authentication")
        };
        assert_eq!(family, CallableFamily::DeclaredCallSignatures);
        let [projected] = projection.call_signatures.as_ref() else {
            panic!("the method must expose exactly one generic signature")
        };
        assert!(projected.strict_variance_exempt);
        let signature = projected.signature;
        let [type_parameter] = context
            .store()
            .signature(signature)
            .unwrap()
            .type_parameters()
        else {
            panic!("the signature must retain its binder-owned method type parameter")
        };
        let type_parameter = *type_parameter;
        assert_eq!(projected.parameters, vec![type_parameter]);
        assert_eq!(
            context
                .store()
                .callable_signature_parameter_types(signature),
            Some([type_parameter].as_slice()),
        );
        assert_eq!(
            context.store().interface_method_linked_type(signature),
            Some(callable)
        );
        let TypeData::TypeParameter(data) =
            context.store().type_payload(type_parameter).unwrap().data()
        else {
            panic!("the method type parameter must retain its canonical payload")
        };
        assert_eq!(
            data.resolved_default_type,
            Some(context.store().intrinsic_bootstrap().unwrap().never_type),
        );

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());

        assert!(
            context
                .store_mut_for_test()
                .set_signature_type_parameters(signature, vec![type_parameter, type_parameter],)
        );
        assert!(matches!(
            validate_stored_callable_set(context.store(), callable),
            StoredCallableSetValidation::Malformed {
                family: CallableFamily::DeclaredCallSignatures,
            }
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep cold, warm, and poisoned identity checks together.
    fn validated_callable_intersections_preserve_signature_identity_and_reject_cache_poison() {
        let parsed = parse_source_file(concat!(
            "type Callback = (value: string) => void; ",
            "type Props = { label: string };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_411);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/callable-set-intersection.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();

        let alias_type = |name: &str| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            context
                .store()
                .type_alias_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap()
        };
        let callback = alias_type("Callback");
        let props = alias_type("Props");
        let signature = context
            .store()
            .type_payload(callback)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first().copied())
            .unwrap();
        context.get_return_type_of_signature(signature).unwrap();

        let store = context.store_mut_for_test();
        let intersection = store
            .canonical_intersection_type(&[callback, props], None)
            .unwrap();
        let before = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        let StoredCallableSetValidation::Valid {
            projection, edges, ..
        } = validate_stored_callable_set(store, intersection)
        else {
            panic!("a validated callable intersection must expose its call signatures")
        };
        assert_eq!(projection.owner, intersection);
        let [callable] = projection.call_signatures.as_ref() else {
            panic!("expected one preserved intersection signature")
        };
        assert_eq!(callable.signature, signature);
        assert_eq!(callable.owner, intersection);
        assert!(edges.contains(&callback));
        assert!(edges.contains(&props));
        assert!(matches!(
            validate_stored_single_callable(store, intersection),
            StoredSingleCallableValidation::Valid { callable, .. }
                if callable.signature == signature && callable.owner == intersection
        ));
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            before,
        );

        assert!(store.set_structured_type_members(intersection, None, None, None, None, None,));
        assert!(matches!(
            validate_stored_callable_set(store, intersection),
            StoredCallableSetValidation::Malformed { .. }
        ));
    }
}
