use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{
    CanonicalCheckerContext, IntrinsicBootstrapOptions, TypeData,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    instantiate::InstantiationLimits,
    production::GlobalMergeCompletion,
    signatures::SignatureFlags,
    types::ObjectFlags,
};

fn context<'arena>(
    sources: &[(&'arena ParseResult, FileId)],
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (index, &(parsed, file)) in sources.iter().enumerate() {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/constructor-{index}.d.ts\"")),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .iter()
            .map(|&(parsed, file)| (file, &parsed.arena))
            .collect::<Vec<_>>(),
        options,
    )
    .unwrap()
}

fn global(store: &CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
    store
        .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
        .and_then(|globals| globals.get_source(name))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .unwrap()
}

fn counts(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize, usize, [usize; 26]) {
    (
        store.type_len(),
        store.signature_len(),
        store.symbol_len(),
        store.mapper_len(),
        store.callable_signature_parameter_types_len(),
        store.checker_link_allocated_lengths(),
    )
}

fn strict_options(strict: bool) -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: strict,
            exact_optional_property_types: strict,
        },
        ..CanonicalCheckerOptions::default()
    }
}

#[test]
fn constructor_value_and_return_identities_stay_separate_and_static_members_stay_lazy() {
    for (index, value_name) in ["Build", "Create"].into_iter().enumerate() {
        let parsed = parse_source_file(&format!(
            "interface Result {{ name: string }} interface Maker {{ new(message?: string, code?: number): Result; unused: Missing; }} declare var {value_name}: Maker;"
        ));
        let file = FileId::new(9_700 + u32::try_from(index).unwrap());
        let options = strict_options(true);
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let value_symbol = global(store, value_name);
        let before = counts(store);
        let plan = plan_declared_constructor_value(store, &host, value_symbol).unwrap();
        assert_eq!(plan.value_symbol(), value_symbol);
        assert_eq!(plan.owner_symbol(), global(store, "Maker"));
        assert_eq!(
            store.source_node_kind(plan.value_declaration()),
            Some(SyntaxKind::VariableDeclaration)
        );
        assert_eq!(
            store.source_node_kind(plan.value_annotation()),
            Some(SyntaxKind::TypeReference)
        );
        assert_eq!(plan.construct_declarations().len(), 1);
        let declaration = plan.construct_declarations().next().unwrap();
        assert_eq!(
            resolve_declared_constructor_value(store, &host, &plan),
            Ok(None)
        );
        assert_eq!(
            resolve_declared_construct_signature(store, &host, &plan, declaration),
            Ok(None)
        );
        assert_eq!(counts(store), before);
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let value = prepare_declared_constructor_value(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
        )
        .unwrap();
        assert_eq!(value.value_symbol(), value_symbol);
        assert_eq!(store.signature_len(), before.1);
        let signature = prepare_declared_construct_signature(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
            declaration,
        )
        .unwrap();
        assert_eq!(signature.value(), value);
        assert_eq!(signature.declaration(), declaration);
        assert_ne!(value.constructor_type(), signature.return_type());
        assert_eq!(
            store
                .type_payload(signature.return_type())
                .unwrap()
                .symbol(),
            Some(global(store, "Result"))
        );
        let constructor = store.type_payload(value.constructor_type()).unwrap();
        assert!(
            !constructor
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(
            constructor
                .data()
                .structured()
                .unwrap()
                .signatures
                .is_none()
        );
        let unused = &plan.owner.properties[0];
        assert!(store.value_symbol_links(unused.symbol).is_none());
        assert!(store.type_node_links(unused.type_node).is_none());
        assert!(
            store
                .declared_call_set_type_for_signature(signature.signature())
                .is_none()
        );
        let parameter_types = store
            .callable_signature_parameter_types(signature.signature())
            .unwrap();
        assert_eq!(parameter_types.len(), 2);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        for (&actual, annotation) in parameter_types
            .iter()
            .zip([bootstrap.string_type, bootstrap.number_type])
        {
            store
                .validate_optional_parameter_type_metadata(annotation, actual)
                .unwrap();
            let TypeData::Union(union) = store.type_payload(actual).unwrap().data() else {
                panic!("an optional primitive keeps its undefined union")
            };
            assert!(union.union.types.contains(&bootstrap.undefined_type));
            assert!(!union.union.types.contains(&bootstrap.missing_type));
        }
        assert_eq!(
            store
                .signature(signature.signature())
                .unwrap()
                .min_argument_count(),
            0
        );
        let warm = counts(store);
        for _ in 0..2 {
            assert_eq!(
                prepare_declared_constructor_value(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan
                ),
                Ok(value)
            );
            assert_eq!(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    declaration
                ),
                Ok(signature)
            );
            assert_eq!(counts(store), warm);
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn merged_constructor_overloads_keep_source_order_and_survive_partial_and_full_queries() {
    let first = parse_source_file(
        "interface Result { name: string } interface Maker { new(message?: string): Result; readonly label: string; } declare const Build: Maker;",
    );
    let second = parse_source_file(
        "interface Maker { new(code: number, extra?: number): number; version: number; }",
    );
    let first_file = FileId::new(9_711);
    let second_file = FileId::new(9_710);
    for reverse_sources in [false, true] {
        for full_first in [false, true] {
            let sources = if reverse_sources {
                [(&second, second_file), (&first, first_file)]
            } else {
                [(&first, first_file), (&second, second_file)]
            };
            let options = strict_options(true);
            let mut context = context(&sources, options);
            let first_bound = context.file(first_file).unwrap().1.clone();
            let second_bound = context.file(second_file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&first.arena, &first_bound), (&second.arena, &second_bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let globals = context.global_types().clone();
            let store = context.store_mut_for_test();
            let value = global(store, "Build");
            let plan = plan_declared_constructor_value(store, &host, value).unwrap();
            let declarations = plan.construct_declarations().collect::<Vec<_>>();
            assert_eq!(declarations.len(), 2);
            assert_eq!(
                declarations
                    .iter()
                    .map(|node| node.file)
                    .collect::<Vec<_>>(),
                sources.iter().map(|(_, file)| *file).collect::<Vec<_>>()
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            if full_first {
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(plan.owner_symbol())
                .unwrap();
            }
            let first_signature = prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declarations[0],
            )
            .unwrap();
            if !full_first {
                assert_eq!(
                    resolve_declared_construct_signature(store, &host, &plan, declarations[1]),
                    Ok(None)
                );
                for property in &plan.owner.properties {
                    assert!(store.value_symbol_links(property.symbol).is_none());
                }
            }
            let second_signature = prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declarations[1],
            )
            .unwrap();
            assert_ne!(first_signature.signature(), second_signature.signature());
            assert_ne!(
                first_signature.return_type(),
                second_signature.return_type()
            );
            let constructor_type = first_signature.value().constructor_type();
            assert_eq!(
                second_signature.value().constructor_type(),
                constructor_type
            );
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics
                )
                .unwrap()
                .get_declared_type_of_symbol(plan.owner_symbol()),
                Ok(constructor_type)
            );
            let StoredCallableSetValidation::Valid { projection, .. } =
                validate_stored_callable_set(store, constructor_type)
            else {
                panic!("the full merged owner has a source-checked callable set")
            };
            assert_eq!(
                projection.construct_signatures.as_ref(),
                &[first_signature.signature(), second_signature.signature()]
            );
            let warm = counts(store);
            for signature in [second_signature, first_signature] {
                assert_eq!(
                    resolve_declared_construct_signature(
                        store,
                        &host,
                        &plan,
                        signature.declaration()
                    ),
                    Ok(Some(signature))
                );
                assert_eq!(
                    prepare_declared_construct_signature(
                        store,
                        &host,
                        &globals,
                        options,
                        &mut session,
                        &mut diagnostics,
                        &plan,
                        signature.declaration()
                    ),
                    Ok(signature)
                );
            }
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics
                )
                .unwrap()
                .get_declared_type_of_symbol(plan.owner_symbol()),
                Ok(constructor_type)
            );
            assert_eq!(counts(store), warm);
            assert!(diagnostics.is_empty());
        }
    }
}

#[test]
fn constructor_interface_optional_call_and_construct_parameters_share_normal_union_rules() {
    for strict in [false, true] {
        let parsed = parse_source_file(
            "interface Maker { (message?: (string)): number; new(message?: (string)): string; } declare var Build: Maker;",
        );
        let file = FileId::new(9_720);
        let options = strict_options(strict);
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
        let declaration = plan.construct_declarations().next().unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let construct = prepare_declared_construct_signature(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
            declaration,
        )
        .unwrap();
        let constructor_type = construct.value().constructor_type();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(construct.return_type(), string);
        assert_eq!(
            CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics
            )
            .unwrap()
            .get_declared_type_of_symbol(plan.owner_symbol()),
            Ok(constructor_type)
        );
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, constructor_type)
        else {
            panic!("the full owner retains both signature families")
        };
        assert_eq!(projection.call_signatures.len(), 1);
        assert_eq!(
            projection.construct_signatures.as_ref(),
            &[construct.signature()]
        );
        let call = projection.call_signatures[0].signature;
        assert_eq!(
            store.callable_signature_parameter_types(call),
            store.callable_signature_parameter_types(construct.signature())
        );
        let &[parameter] = store.callable_signature_parameter_types(call).unwrap() else {
            panic!("one optional call parameter")
        };
        if strict {
            store
                .validate_optional_parameter_type_metadata(string, parameter)
                .unwrap();
        } else {
            assert_eq!(parameter, string);
        }
        let warm = counts(store);
        assert_eq!(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declaration
            ),
            Ok(construct)
        );
        assert_eq!(counts(store), warm);
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn constructor_provider_rejects_poisoned_value_signature_and_parameter_links_without_growth() {
    for poison in 0..6 {
        let parsed = parse_source_file(
            "interface Maker { new(message?: string): number; } declare var Build: Maker;",
        );
        let file = FileId::new(9_730 + poison);
        let options = strict_options(true);
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
        let declaration = plan.construct_declarations().next().unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let prepared = prepare_declared_construct_signature(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
            declaration,
        )
        .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        match poison {
            0 => assert!(store.set_type_node_links(
                plan.value_annotation(),
                TypeNodeLinks {
                    resolved_type: Some(string),
                    ..TypeNodeLinks::default()
                }
            )),
            1 => assert!(
                store.set_signature_resolved_return_type(prepared.signature(), Some(string))
            ),
            2 => assert!(store.set_signature_flags(prepared.signature(), SignatureFlags::NONE)),
            3 => assert!(store.set_value_symbol_links(
                plan.owner.call_signatures[0].parameters[0].symbol,
                ValueSymbolLinks {
                    resolved_type: Some(string),
                    ..ValueSymbolLinks::default()
                }
            )),
            4 => assert!(store.set_type_node_links(
                plan.owner.call_signatures[0].return_type,
                TypeNodeLinks {
                    resolved_type: Some(string),
                    ..TypeNodeLinks::default()
                }
            )),
            5 => assert!(store.set_type_node_links(
                plan.owner.call_signatures[0].parameters[0].type_node,
                TypeNodeLinks {
                    resolved_type: Some(prepared.return_type()),
                    ..TypeNodeLinks::default()
                }
            )),
            _ => unreachable!(),
        }
        let before = counts(store);
        for _ in 0..2 {
            assert!(
                resolve_declared_construct_signature(store, &host, &plan, declaration).is_err()
            );
            assert!(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    declaration
                )
                .is_err()
            );
            assert_eq!(counts(store), before);
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn constructor_value_rejects_a_conflicting_annotation_name_cache_and_reuses_restored_ids() {
    let parsed = parse_source_file(
        "interface Maker { new(): string } interface Other { new(): number } declare const Build: Maker;",
    );
    let file = FileId::new(9_737);
    let options = CanonicalCheckerOptions::default();
    let mut context = context(&[(&parsed, file)], options);
    let bound = context.file(file).unwrap().1.clone();
    let host = DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, &bound)],
        GlobalMergeCompletion::for_test(options.name_resolution),
    )
    .unwrap();
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
    let declaration = plan.construct_declarations().next().unwrap();
    let NodeData::TypeReferenceNode(reference) = &host.node(plan.value_annotation()).unwrap().data
    else {
        panic!("the value retains its original Maker annotation")
    };
    let name = NodeRef::new(plan.value_annotation().arena, file, reference.type_name);
    assert_eq!(store.source_node_kind(name), Some(SyntaxKind::Identifier));
    assert_eq!(store.source_identifier_text(name), Some("Maker"));
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let prepared = prepare_declared_construct_signature(
        store,
        &host,
        &globals,
        options,
        &mut session,
        &mut diagnostics,
        &plan,
        declaration,
    )
    .unwrap();
    let original = store.symbol_node_links(name).cloned().unwrap_or_default();
    let other = global(store, "Other");
    assert_ne!(other, plan.owner_symbol());
    assert!(store.set_symbol_node_links(
        name,
        SymbolNodeLinks {
            resolved_symbol: Some(other),
        }
    ));
    assert_eq!(
        store.symbol_node_links(plan.value_annotation()),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(plan.owner_symbol()),
        })
    );
    let invalid = DeclaredConstructorValueError::InvalidValue(plan.value_symbol());
    let poisoned = (counts(store), session.query_count(), diagnostics.clone());
    for _ in 0..2 {
        assert_eq!(
            resolve_declared_constructor_value(store, &host, &plan),
            Err(invalid)
        );
        assert_eq!(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declaration,
            ),
            Err(invalid)
        );
        assert_eq!(
            (counts(store), session.query_count(), diagnostics.clone()),
            poisoned
        );
    }
    assert!(store.set_symbol_node_links(name, original));
    let restored = (counts(store), session.query_count(), diagnostics.clone());
    assert_eq!(
        resolve_declared_constructor_value(store, &host, &plan),
        Ok(Some(prepared.value()))
    );
    assert_eq!(
        prepare_declared_construct_signature(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
            declaration,
        ),
        Ok(prepared)
    );
    assert_eq!(
        (counts(store), session.query_count(), diagnostics),
        restored
    );
}

#[test]
fn constructor_annotations_reject_conflicting_parenthesized_return_and_required_parameter_caches() {
    let parsed = parse_source_file(
        "interface Maker { new(value: (string)): (string) } declare const Build: Maker;",
    );
    let file = FileId::new(9_738);
    let options = strict_options(true);
    let mut context = context(&[(&parsed, file)], options);
    let bound = context.file(file).unwrap().1.clone();
    let host = DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, &bound)],
        GlobalMergeCompletion::for_test(options.name_resolution),
    )
    .unwrap();
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
    let declaration = plan.construct_declarations().next().unwrap();
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let prepared = prepare_declared_construct_signature(
        store,
        &host,
        &globals,
        options,
        &mut session,
        &mut diagnostics,
        &plan,
        declaration,
    )
    .unwrap();
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(prepared.return_type(), string);
    assert_eq!(
        store.callable_signature_parameter_types(prepared.signature()),
        Some([string].as_slice())
    );
    assert_eq!(
        store
            .signature(prepared.signature())
            .unwrap()
            .min_argument_count(),
        1
    );
    let planned = plan.signature(declaration).unwrap();
    for annotation in [planned.return_type, planned.parameters[0].type_node] {
        assert_eq!(
            store.source_node_kind(annotation),
            Some(SyntaxKind::ParenthesizedType)
        );
        let inner = store.source_direct_children(annotation).unwrap()[0];
        assert_eq!(
            store.source_node_kind(inner),
            Some(SyntaxKind::StringKeyword)
        );
        let original = store
            .type_node_links(annotation)
            .cloned()
            .unwrap_or_default();
        assert!(store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(store.source_direct_type_annotation_is_exact(inner, string));
        assert_eq!(
            object_members::cached_constructor_interface_annotation(store, annotation),
            None
        );
        let poisoned = (counts(store), session.query_count(), diagnostics.clone());
        for _ in 0..2 {
            assert!(matches!(
                resolve_declared_construct_signature(store, &host, &plan, declaration),
                Err(DeclaredConstructorValueError::Members(PropertyObjectError::InvalidCachedInterface { symbol, type_ }))
                    if symbol == plan.owner_symbol() && type_ == prepared.value().constructor_type()
            ));
            assert!(matches!(
                prepare_declared_construct_signature(
                    store, &host, &globals, options, &mut session, &mut diagnostics, &plan, declaration,
                ),
                Err(DeclaredConstructorValueError::Members(PropertyObjectError::InvalidCachedInterface { symbol, type_ }))
                    if symbol == plan.owner_symbol() && type_ == prepared.value().constructor_type()
            ));
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                poisoned
            );
        }
        assert!(store.set_type_node_links(annotation, original));
        let restored = (counts(store), session.query_count(), diagnostics.clone());
        assert_eq!(
            object_members::cached_constructor_interface_annotation(store, annotation),
            Some(string)
        );
        assert_eq!(
            resolve_declared_construct_signature(store, &host, &plan, declaration),
            Ok(Some(prepared))
        );
        assert_eq!(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declaration,
            ),
            Ok(prepared)
        );
        assert_eq!(
            (counts(store), session.query_count(), diagnostics.clone()),
            restored
        );
    }
    assert!(diagnostics.is_empty());
}

#[test]
fn constructor_generic_annotations_reject_coordinated_return_cache_changes_and_reuse_restored_ids()
{
    for (definition, name) in [
        ("interface Box<T> { value: T }", "Box"),
        ("type Identity<T> = T;", "Identity"),
    ] {
        let parsed = parse_source_file(&format!(
            "{definition} interface Maker {{ new(): {name}<string>; new(): {name}<number>; }} declare const Build: Maker;"
        ));
        let file = FileId::new(9_739);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
        let declarations = plan.construct_declarations().collect::<Vec<_>>();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut signatures = Vec::new();
        for &declaration in &declarations {
            signatures.push(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    declaration,
                )
                .unwrap(),
            );
        }
        let [first, second] = signatures.as_slice() else {
            panic!("both original overloads retain separate results")
        };
        assert_ne!(first.return_type(), second.return_type());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        for (signature, argument) in [(*first, string), (*second, number)] {
            let record = store.type_payload(signature.return_type()).unwrap();
            if name == "Identity" {
                assert_eq!(signature.return_type(), argument);
                assert!(record.alias().is_none());
            } else {
                let TypeData::TypeReference(reference) = record.data() else {
                    panic!("Box keeps its instantiated reference")
                };
                assert_eq!(record.symbol(), Some(global(store, name)));
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some([argument].as_slice())
                );
            }
        }
        let annotation = plan.signature(first.declaration()).unwrap().return_type;
        let original = store.type_node_links(annotation).cloned().unwrap();
        let owner = global(store, name);
        let source_arguments = store.source_direct_children(annotation).unwrap();
        let [_, argument] = source_arguments.as_slice() else {
            panic!("one source name and one original type argument")
        };
        assert_eq!(
            store.source_node_kind(*argument),
            Some(SyntaxKind::StringKeyword)
        );
        assert!(store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(second.return_type()),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(
            store.set_signature_resolved_return_type(first.signature(), Some(second.return_type()))
        );
        assert_eq!(
            store.symbol_node_links(annotation),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(owner)
            })
        );
        assert!(store.source_direct_type_annotation_is_exact(*argument, string));
        assert_eq!(
            object_members::cached_constructor_interface_annotation(store, annotation),
            None
        );
        let poisoned = (counts(store), session.query_count(), diagnostics.clone());
        for _ in 0..2 {
            assert!(matches!(
                resolve_declared_construct_signature(store, &host, &plan, first.declaration()),
                Err(DeclaredConstructorValueError::Members(PropertyObjectError::InvalidCachedInterface { symbol, type_ }))
                    if symbol == plan.owner_symbol() && type_ == first.value().constructor_type()
            ));
            assert!(matches!(
                prepare_declared_construct_signature(
                    store, &host, &globals, options, &mut session, &mut diagnostics, &plan, first.declaration(),
                ),
                Err(DeclaredConstructorValueError::Members(PropertyObjectError::InvalidCachedInterface { symbol, type_ }))
                    if symbol == plan.owner_symbol() && type_ == first.value().constructor_type()
            ));
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                poisoned
            );
        }
        assert!(store.set_type_node_links(annotation, original));
        assert!(
            store.set_signature_resolved_return_type(first.signature(), Some(first.return_type()))
        );
        let restored = (counts(store), session.query_count(), diagnostics.clone());
        for signature in [second, first] {
            assert_eq!(
                resolve_declared_construct_signature(store, &host, &plan, signature.declaration()),
                Ok(Some(*signature))
            );
            assert_eq!(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    signature.declaration(),
                ),
                Ok(*signature)
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                restored
            );
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn constructor_full_only_annotations_are_unsupported_before_partial_publication_or_reuse() {
    for (definition, annotation_name) in [
        ("interface Result<T = string> { value: T }", "Result"),
        ("type Result<T = string> = T;", "Result"),
        (
            "declare namespace Types { interface Result { value: string } }",
            "Types.Result",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "{definition} interface Maker {{ new(): {annotation_name} }} declare const Build: Maker;"
        ));
        let file = FileId::new(9_741);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
        let declaration = plan.construct_declarations().next().unwrap();
        let annotation = plan.signature(declaration).unwrap().return_type;
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let before = (counts(store), session.query_count(), diagnostics.clone());
        let unsupported = DeclaredConstructorValueError::Unsupported {
            node: annotation,
            kind: SyntaxKind::TypeReference,
        };
        for _ in 0..2 {
            assert_eq!(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    declaration,
                ),
                Err(unsupported),
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                before
            );
            assert!(
                store
                    .signature_links(declaration)
                    .is_none_or(|links| links == &super::super::SignatureLinks::default())
            );
            assert_eq!(
                resolve_declared_construct_signature(store, &host, &plan, declaration),
                Err(unsupported)
            );
        }
        let full = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(plan.owner_symbol())
        .unwrap();
        let signature = store
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let result = store
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        assert_eq!(
            store.declared_call_set_type_for_signature(signature),
            Some(full)
        );
        assert_eq!(
            store.callable_signature_parameter_types(signature),
            Some([].as_slice())
        );
        let warm = (counts(store), session.query_count(), diagnostics.clone());
        for _ in 0..2 {
            assert_eq!(
                resolve_declared_construct_signature(store, &host, &plan, declaration),
                Err(unsupported)
            );
            assert_eq!(
                prepare_declared_construct_signature(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    &plan,
                    declaration,
                ),
                Err(unsupported)
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                warm
            );
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(plan.owner_symbol()),
                Ok(full)
            );
            assert_eq!(
                store
                    .signature_links(declaration)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(signature)
            );
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                Some(result)
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                warm
            );
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn full_constructor_queries_keep_qualified_defaulted_and_explicit_annotations_source_checked() {
    for (definition, annotation, other_annotation) in [
        (
            "declare namespace Types { interface Result { value: string } } declare namespace Other { interface Result { value: number } }",
            "Types.Result",
            "Other.Result",
        ),
        ("type Result<T = string> = T;", "Result", "Result<number>"),
        (
            "interface Result<T = string> { value: T }",
            "Result",
            "Result<number>",
        ),
        (
            "interface Result<T> { value: T }",
            "Result<string>",
            "Result<number>",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "{definition} interface Maker {{ new(input: {annotation}): {annotation} }} interface OtherMaker {{ new(): {other_annotation} }}"
        ));
        let file = FileId::new(9_742);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let owner = global(store, "Maker");
        let other = global(store, "OtherMaker");
        let plan = plan_interface(store, &host, owner).unwrap();
        let other_plan = plan_interface(store, &host, other).unwrap();
        let planned = &plan.call_signatures[0];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(owner)
        .unwrap();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(other)
        .unwrap();
        let signature = store
            .signature_links(planned.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let other_signature = store
            .signature_links(other_plan.call_signatures[0].declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let result = store
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let other_result = store
            .signature(other_signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        assert_ne!(result, other_result);
        assert_eq!(
            store.callable_signature_parameter_types(signature),
            Some([result].as_slice())
        );
        assert_eq!(
            store.declared_call_set_type_for_signature(signature),
            Some(type_)
        );
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, type_)
        else {
            panic!("the full query retains its original constructor")
        };
        assert_eq!(projection.construct_signatures.as_ref(), &[signature]);
        let warm = (counts(store), session.query_count(), diagnostics.clone());
        assert_eq!(
            CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(owner),
            Ok(type_)
        );
        assert_eq!(
            (counts(store), session.query_count(), diagnostics.clone()),
            warm
        );
        for (annotation, change_return) in [
            (planned.return_type, true),
            (planned.parameters[0].type_node, false),
        ] {
            let original = store.type_node_links(annotation).cloned().unwrap();
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(other_result),
                    ..TypeNodeLinks::default()
                }
            ));
            if change_return {
                assert!(store.set_signature_resolved_return_type(signature, Some(other_result)));
            }
            let poisoned = (counts(store), session.query_count(), diagnostics.clone());
            for _ in 0..2 {
                let error = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner)
                .unwrap_err();
                assert!(match error {
                    DeclaredTypeError::Unavailable(
                        crate::semantic::declared::DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                            symbol,
                            declared_type,
                        },
                    ) => symbol == owner && declared_type == type_,
                    DeclaredTypeError::TypeNodeUnavailable(
                        crate::semantic::type_nodes::TypeNodeUnavailable::InvalidCachedTypeAlias(symbol)
                        | crate::semantic::type_nodes::TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(symbol),
                    ) => symbol == owner
                        || Some(symbol) == store.symbol_node_links(annotation).and_then(|links| links.resolved_symbol),
                    DeclaredTypeError::TypeNodeUnavailable(
                        crate::semantic::type_nodes::TypeNodeUnavailable::InvalidTypeReference(node),
                    ) => node == annotation,
                    _ => false,
                }, "{error:?}");
                assert_eq!(
                    (counts(store), session.query_count(), diagnostics.clone()),
                    poisoned
                );
            }
            assert!(store.set_type_node_links(annotation, original));
            if change_return {
                assert!(store.set_signature_resolved_return_type(signature, Some(result)));
            }
            let restored = (counts(store), session.query_count(), diagnostics.clone());
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner),
                Ok(type_)
            );
            assert_eq!(
                store
                    .signature_links(planned.declaration)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(signature)
            );
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                Some(result)
            );
            assert_eq!(
                store.callable_signature_parameter_types(signature),
                Some([result].as_slice())
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                restored
            );
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn full_constructor_queries_keep_ambient_import_names_and_reject_changed_import_caches() {
    for (import, annotation, import_kind, local) in [
        (
            "import * as Types from 'types';",
            "Types.Result",
            SyntaxKind::NamespaceImport,
            "Types",
        ),
        (
            "import { Result as Renamed } from 'types';",
            "Renamed",
            SyntaxKind::ImportSpecifier,
            "Renamed",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "declare module 'types' {{ export type Result = string; }} declare module 'forged-types' {{ export type Result = number; }} declare module 'consumer' {{ {import} export interface Maker {{ new(input: {annotation}): {annotation} }} }}"
        ));
        let file = FileId::new(9_743);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let named = |kind, expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    if record.kind != kind {
                        return None;
                    }
                    let name = match &record.data {
                        NodeData::InterfaceDeclaration(interface) => interface.name,
                        NodeData::ModuleDeclaration(module) => module.name,
                        NodeData::NamespaceImport(import) => import.name,
                        NodeData::ImportSpecifier(import) => import.name,
                        _ => return None,
                    };
                    let text = match &parsed.arena.get(name)?.data {
                        NodeData::Identifier(name) => name.text.as_str(),
                        NodeData::StringLiteral(name) => name.text.as_str(),
                        _ => return None,
                    };
                    (text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap()
        };
        let store = context.store_mut_for_test();
        let owner = store
            .get_merged_symbol(
                bound
                    .symbol(named(SyntaxKind::InterfaceDeclaration, "Maker"))
                    .unwrap(),
            )
            .unwrap();
        let alias = store
            .get_merged_symbol(bound.symbol(named(import_kind, local)).unwrap())
            .unwrap();
        let wrong_module = store
            .get_merged_symbol(
                bound
                    .symbol(named(SyntaxKind::ModuleDeclaration, "forged-types"))
                    .unwrap(),
            )
            .unwrap();
        let wrong_target = if import_kind == SyntaxKind::NamespaceImport {
            wrong_module
        } else {
            store
                .symbol(wrong_module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source("Result"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap()
        };
        let plan = plan_interface(store, &host, owner).unwrap();
        let planned = &plan.call_signatures[0];
        assert!(store.alias_symbol_links(alias).is_none());
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(owner)
        .unwrap();
        let signature = store
            .signature_links(planned.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            Some(string)
        );
        assert_eq!(
            store.callable_signature_parameter_types(signature),
            Some([string].as_slice())
        );
        assert_eq!(
            store.declared_call_set_type_for_signature(signature),
            Some(type_)
        );
        assert!(store.alias_symbol_links(alias).is_none());
        let warm = (counts(store), session.query_count(), diagnostics.clone());
        for _ in 0..2 {
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner),
                Ok(type_)
            );
            assert!(store.alias_symbol_links(alias).is_none());
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                warm
            );
        }
        for resolved_wrong_target in [false, true] {
            assert!(store.set_alias_symbol_links(
                alias,
                crate::semantic::AliasSymbolLinks {
                    immediate_target: Some(wrong_target),
                    alias_target: if resolved_wrong_target {
                        crate::semantic::AliasTargetState::Resolved(wrong_target)
                    } else {
                        crate::semantic::AliasTargetState::Unresolved
                    },
                    ..crate::semantic::AliasSymbolLinks::default()
                }
            ));
            let poisoned = (counts(store), session.query_count(), diagnostics.clone());
            for _ in 0..2 {
                let error = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner)
                .unwrap_err();
                assert!(
                    matches!(error, DeclaredTypeError::TypeNodeUnavailable(
                    crate::semantic::type_nodes::TypeNodeUnavailable::ImportAliasTypeReference { node, alias: actual }
                ) if actual == alias && [planned.return_type, planned.parameters[0].type_node].contains(&node)),
                    "{error:?}"
                );
                assert_eq!(
                    (counts(store), session.query_count(), diagnostics.clone()),
                    poisoned
                );
            }
            assert!(
                store.set_alias_symbol_links(alias, crate::semantic::AliasSymbolLinks::default())
            );
            let restored = (counts(store), session.query_count(), diagnostics.clone());
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner),
                Ok(type_)
            );
            assert_eq!(
                store
                    .signature_links(planned.declaration)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(signature)
            );
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                Some(string)
            );
            assert_eq!(
                store.callable_signature_parameter_types(signature),
                Some([string].as_slice())
            );
            assert_eq!(
                store.alias_symbol_links(alias),
                Some(&crate::semantic::AliasSymbolLinks::default())
            );
            assert_eq!(
                (counts(store), session.query_count(), diagnostics.clone()),
                restored
            );
        }
        assert!(diagnostics.is_empty());
    }
}

#[test]
fn constructor_provider_preserves_no_construct_identity_and_rejects_generic_owners() {
    for (source, supported) in [
        (
            "interface Value { tag: string } declare const Build: Value;",
            true,
        ),
        (
            "interface Value<T> { new(): T } declare const Build: Value<string>;",
            false,
        ),
        (
            "interface Value { new<T>(): T } declare const Build: Value;",
            false,
        ),
        (
            "interface Base { new(): string } interface Value extends Base {} declare const Build: Value;",
            false,
        ),
    ] {
        let parsed = parse_source_file(source);
        let file = FileId::new(9_740);
        let options = CanonicalCheckerOptions::default();
        let context = context(&[(&parsed, file)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let before = counts(context.store());
        let plan = plan_declared_constructor_value(
            context.store(),
            &host,
            global(context.store(), "Build"),
        );
        if supported {
            let plan = plan.unwrap();
            assert_eq!(plan.construct_declarations().len(), 0);
            assert_eq!(
                resolve_declared_constructor_value(context.store(), &host, &plan),
                Ok(None)
            );
        } else {
            assert!(plan.is_err(), "{source}");
        }
        assert_eq!(counts(context.store()), before);
    }
}

#[test]
fn constructor_annotation_queries_share_the_caller_session_and_diagnostics() {
    let parsed = parse_source_file(
        "type Identity<T> = T; type NeedsNumber<T extends number> = T; interface Maker { new(input: Identity<string>): string; new(input: Identity<number>): NeedsNumber<string>; } declare var Build: Maker;",
    );
    let file = FileId::new(9_750);
    let options = CanonicalCheckerOptions::default();
    let mut context = context(&[(&parsed, file)], options);
    let bound = context.file(file).unwrap().1.clone();
    let host = DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, &bound)],
        GlobalMergeCompletion::for_test(options.name_resolution),
    )
    .unwrap();
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
    let declarations = plan.construct_declarations().collect::<Vec<_>>();
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let first = prepare_declared_construct_signature(
        store,
        &host,
        &globals,
        options,
        &mut session,
        &mut diagnostics,
        &plan,
        declarations[0],
    )
    .unwrap();
    let first_count = session.query_count();
    assert_eq!(first_count, 0);
    assert!(diagnostics.is_empty());
    let second = prepare_declared_construct_signature(
        store,
        &host,
        &globals,
        options,
        &mut session,
        &mut diagnostics,
        &plan,
        declarations[1],
    )
    .unwrap();
    assert_eq!(session.query_count(), first_count);
    assert_eq!(session.total_count(), session.query_count());
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(first.return_type(), string);
    assert_eq!(second.return_type(), string);
    assert_eq!(
        store.callable_signature_parameter_types(first.signature()),
        Some([string].as_slice())
    );
    assert_eq!(
        store.callable_signature_parameter_types(second.signature()),
        Some([number].as_slice())
    );
    assert_eq!(
        diagnostics
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2344]
    );
    let warm = (counts(store), session.query_count(), diagnostics.clone());
    for signature in [second, first] {
        assert_eq!(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                signature.declaration()
            ),
            Ok(signature)
        );
    }
    assert_eq!((counts(store), session.query_count(), diagnostics), warm);
}

#[test]
fn constructor_union_annotations_charge_one_caller_session_and_reuse_warm_signatures() {
    let parsed = parse_source_file(
        "type Choice<Left, Right> = Left | Right; interface Maker { new(input: Choice<string, number>): string; new(input: Choice<number, string>): number; } declare const Build: Maker;",
    );
    let file = FileId::new(9_751);
    let options = CanonicalCheckerOptions::default();
    let mut context = context(&[(&parsed, file)], options);
    let bound = context.file(file).unwrap().1.clone();
    let host = DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, &bound)],
        GlobalMergeCompletion::for_test(options.name_resolution),
    )
    .unwrap();
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
    let declarations = plan.construct_declarations().collect::<Vec<_>>();
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let mut signatures = Vec::new();
    for (index, &declaration) in declarations.iter().enumerate() {
        signatures.push(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                declaration,
            )
            .unwrap(),
        );
        assert_eq!(session.query_count(), (index + 1) * 2);
        assert_eq!(session.total_count(), session.query_count());
    }
    let [first, second] = signatures.as_slice() else {
        panic!("both original overloads must be prepared")
    };
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let alias = global(store, "Choice");
    for (signature, arguments, result) in [
        (*first, [string, number], string),
        (*second, [number, string], number),
    ] {
        let &[parameter] = store
            .callable_signature_parameter_types(signature.signature())
            .unwrap()
        else {
            panic!("each overload has one named union parameter")
        };
        assert_eq!(
            store.validate_union_alias_identity(parameter, alias, &arguments),
            Ok(())
        );
        assert_eq!(signature.return_type(), result);
    }
    assert_ne!(
        store.callable_signature_parameter_types(first.signature()),
        store.callable_signature_parameter_types(second.signature())
    );
    assert!(diagnostics.is_empty());
    let warm = (
        counts(store),
        session.query_count(),
        session.total_count(),
        diagnostics.clone(),
    );
    for signature in [second, first, second] {
        assert_eq!(
            prepare_declared_construct_signature(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
                signature.declaration(),
            ),
            Ok(*signature)
        );
        assert_eq!(
            (
                counts(store),
                session.query_count(),
                session.total_count(),
                diagnostics.clone()
            ),
            warm
        );
    }
}

#[test]
fn partial_construct_parameter_setter_requires_the_original_owner_and_complete_source_signature() {
    let parsed = parse_source_file(
        "interface Maker { new(value: string): number } interface Other { new(value: string): number } declare var Build: Maker;",
    );
    let file = FileId::new(9_760);
    let options = CanonicalCheckerOptions::default();
    let mut context = context(&[(&parsed, file)], options);
    let bound = context.file(file).unwrap().1.clone();
    let host = DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, &bound)],
        GlobalMergeCompletion::for_test(options.name_resolution),
    )
    .unwrap();
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let plan = plan_declared_constructor_value(store, &host, global(store, "Build")).unwrap();
    let declaration = plan.construct_declarations().next().unwrap();
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let prepared = prepare_declared_construct_signature(
        store,
        &host,
        &globals,
        options,
        &mut session,
        &mut diagnostics,
        &plan,
        declaration,
    )
    .unwrap();
    let types = store
        .callable_signature_parameter_types(prepared.signature())
        .unwrap()
        .to_vec();
    let other = plan_interface(store, &host, global(store, "Other")).unwrap();
    let before = counts(store);
    assert!(!store.set_partial_declared_construct_parameter_types(
        &plan.owner,
        declaration,
        prepared.signature(),
        types.clone()
    ));
    assert!(
        !object_members::validate_partial_declared_construct_parameter_types(
            store,
            &other,
            declaration,
            prepared.signature(),
            &types
        )
    );
    assert!(
        !object_members::validate_partial_declared_construct_parameter_types(
            store,
            &plan.owner,
            declaration,
            prepared.signature(),
            &[prepared.return_type()]
        )
    );
    assert_eq!(counts(store), before);
}
