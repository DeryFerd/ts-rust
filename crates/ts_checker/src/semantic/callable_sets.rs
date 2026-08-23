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
    callables::{
        CallableFamily, StoredSingleCallableValidation, ValidatedSingleCallable,
        validate_stored_single_callable_provider,
    },
    classes::{ClassHeritageMembersValidation, validate_class_heritage_members},
    links::ValueSymbolLinks,
    object_members::{StoredDeclaredCallSetValidation, validate_stored_declared_call_set},
    signatures::SignatureFlags,
    source_overloads::{StoredSourceOverloadValidation, validate_stored_source_overload},
    store::SourceNodeParent,
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

    if let Some(validation) = validate_stored_default_library_method_callable_set(store, type_) {
        return validation;
    }

    if let Some(validation) = validate_stored_class_method_callable_set(store, type_) {
        return validation;
    }

    validate_stored_intersection_callable_set(store, type_)
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
                store
                    .callable_signature_parameter_types(signature)
                    .map(<[TypeId]>::to_vec)
                    .or_else(|| {
                        store
                            .signature(signature)?
                            .parameters()
                            .is_empty()
                            .then(Vec::new)
                    })
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
        Some((projection, return_type))
    })();

    Some(match authenticated {
        Some((projection, return_type)) => StoredCallableSetValidation::Valid {
            family,
            projection,
            edges: vec![return_type],
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
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SemanticStore,
        TypeRecord, bootstrap::UnionReduction, callables::validate_stored_single_callable,
        mapper::TypeMapper, types::ObjectFlags,
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
