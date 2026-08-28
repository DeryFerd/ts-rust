fn wave148_recovery_rejects_without_writes(
    fixture: &mut PropertyRecoveryFixture<'_>,
    result: TypeId,
    session: &mut InstantiationSession,
    label: &str,
) {
    use crate::semantic::callable_sets::validate_stored_callable_set;
    let store = fixture.context.store_mut_for_test();
    let before = (
        property_recovery_store_counts(store),
        store.relation_state_snapshot(),
        store.value_symbol_links(fixture.proxy).cloned(),
        store.value_symbol_links(fixture.target).cloned(),
    );
    let counts = (session.query_count(), session.total_count());
    let mark = session.limit_event_mark();
    let mut retry = InstantiationSession::new(InstantiationLimits {
        max_count: 0,
        ..InstantiationLimits::default()
    });
    let retry_mark = retry.limit_event_mark();
    for _ in 0..3 {
        assert!(
            matches!(
                validate_stored_callable_set(store, result),
                StoredCallableSetValidation::Malformed {
                    family: CallableFamily::DeclaredCallSignatures
                }
            ),
            "{label}"
        );
        for caller in [&mut *session, &mut retry] {
            assert!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    caller,
                )
                .is_err(),
                "{label}"
            );
        }
        assert_eq!(
            (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
                store.value_symbol_links(fixture.proxy).cloned(),
                store.value_symbol_links(fixture.target).cloned(),
            ),
            before,
            "{label}"
        );
    }
    assert_eq!(
        (session.query_count(), session.total_count()),
        counts,
        "{label}"
    );
    assert_eq!(
        (retry.query_count(), retry.total_count()),
        (0, 0),
        "{label}"
    );
    assert!(!session.limit_event_occurred_since(mark), "{label}");
    assert!(!retry.limit_event_occurred_since(retry_mark), "{label}");
    eprintln!("wave148 rejection {label}: three retries, no store or session writes");
}

#[test]
fn property_recovery_wave148_owner_and_declaration_corruption() {
    for mutation in [
        "proxy_parent",
        "source_parent",
        "proxy_declaration",
        "source_declaration",
        "owner_type_symbol",
        "receiver_member_entry",
        "proxy_check_flags",
    ] {
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_401));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let foreign_owner = store
            .type_payload(fixture.receiver)
            .unwrap()
            .symbol()
            .unwrap();
        match mutation {
            "proxy_parent" | "source_parent" => {
                let symbol = if mutation == "proxy_parent" {
                    fixture.proxy
                } else {
                    fixture.target
                };
                let record = store.symbol(symbol).unwrap();
                let old = (
                    record.members(),
                    record.exports(),
                    record.parent(),
                    record.export_symbol(),
                );
                assert_ne!(old.2, Some(foreign_owner));
                assert!(store.set_symbol_relationships(
                    symbol,
                    old.0,
                    old.1,
                    Some(foreign_owner),
                    old.3
                ));
            }
            "proxy_declaration" | "source_declaration" => {
                let symbol = if mutation == "proxy_declaration" {
                    fixture.proxy
                } else {
                    fixture.target
                };
                let declaration = store
                    .symbol(fixture.sibling)
                    .unwrap()
                    .value_declaration()
                    .unwrap();
                assert_ne!(
                    store.symbol(symbol).unwrap().value_declaration(),
                    Some(declaration)
                );
                assert!(store.set_symbol_declarations(
                    symbol,
                    Some(vec![declaration]),
                    Some(declaration)
                ));
            }
            "owner_type_symbol" => {
                assert!(store.set_type_symbol(fixture.members.target(), Some(foreign_owner)));
            }
            "receiver_member_entry" => {
                assert_eq!(
                    store.insert_symbol(
                        fixture.members.members().unwrap(),
                        EscapedName::source("first"),
                        fixture.sibling
                    ),
                    Some(Some(fixture.proxy))
                );
            }
            "proxy_check_flags" => {
                let record = store.symbol(fixture.proxy).unwrap();
                let flags = record.flags();
                let checks = record.check_flags() | CheckFlags::READONLY;
                assert!(store.set_symbol_flags(fixture.proxy, flags, checks));
            }
            _ => unreachable!(),
        }
        wave148_recovery_rejects_without_writes(&mut fixture, result, &mut session, mutation);
    }
}

#[test]
fn property_recovery_wave148_parameter_return_and_callable_identity() {
    for mutation in [
        "copied_parameter_declaration",
        "source_parameter_declaration",
        "copied_parameter_parent",
        "copied_parameter_flags",
        "return_only",
        "this_parameter",
        "signature_flags",
        "signature_target_cycle",
        "isolated_callable",
        "same_shape_signature_copy",
    ] {
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_402));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let signature = store
            .type_payload(result)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let original = store.signature(signature).unwrap().target().unwrap();
        let parameter = store.signature(signature).unwrap().parameters()[0];
        let source_parameter = store.signature(original).unwrap().parameters()[0];
        assert_ne!(parameter, source_parameter);
        match mutation {
            "copied_parameter_declaration" | "source_parameter_declaration" => {
                let symbol = if mutation == "copied_parameter_declaration" {
                    parameter
                } else {
                    source_parameter
                };
                let declaration = store
                    .symbol(fixture.target)
                    .unwrap()
                    .value_declaration()
                    .unwrap();
                assert!(store.set_symbol_declarations(
                    symbol,
                    Some(vec![declaration]),
                    Some(declaration)
                ));
            }
            "copied_parameter_parent" => {
                let record = store.symbol(parameter).unwrap();
                let old = (
                    record.members(),
                    record.exports(),
                    record.parent(),
                    record.export_symbol(),
                );
                let owner = store
                    .type_payload(fixture.receiver)
                    .unwrap()
                    .symbol()
                    .unwrap();
                assert_ne!(old.2, Some(owner));
                assert!(store.set_symbol_relationships(
                    parameter,
                    old.0,
                    old.1,
                    Some(owner),
                    old.3
                ));
            }
            "copied_parameter_flags" => {
                let record = store.symbol(parameter).unwrap();
                let flags = record.flags().without(SymbolFlags::TRANSIENT);
                let checks = record.check_flags();
                assert!(store.set_symbol_flags(parameter, flags, checks));
            }
            "return_only" => {
                let number = store.intrinsic_bootstrap().unwrap().number_type;
                assert_ne!(
                    store.signature(signature).unwrap().resolved_return_type(),
                    Some(number)
                );
                assert!(store.set_signature_resolved_return_type(signature, Some(number)));
            }
            "this_parameter" => {
                assert!(store.set_signature_this_parameter(signature, Some(parameter)));
            }
            "signature_flags" => {
                let flags =
                    store.signature(signature).unwrap().flags() | SignatureFlags::HAS_LITERAL_TYPES;
                assert!(store.set_signature_flags(signature, flags));
            }
            "signature_target_cycle" => {
                let mapper = store.signature(signature).unwrap().mapper();
                assert!(store.set_signature_target_and_mapper(signature, Some(signature), mapper));
            }
            "isolated_callable" => {
                assert!(store.set_signature_isolated_type(signature, Some(result)));
            }
            "same_shape_signature_copy" => {
                let record = store.signature(signature).unwrap();
                let fields = (
                    record.flags(),
                    record.declaration(),
                    record.type_parameters().to_vec(),
                    record.this_parameter(),
                    record.parameters().to_vec(),
                    record.resolved_return_type(),
                    record.resolved_type_predicate(),
                    record.min_argument_count(),
                    record.target(),
                    record.mapper(),
                );
                let copied = store
                    .alloc_signature(
                        fields.0, fields.1, fields.2, fields.3, fields.4, fields.5, fields.6,
                        fields.7,
                    )
                    .unwrap();
                assert_ne!(copied, signature);
                assert!(store.set_signature_target_and_mapper(copied, fields.8, fields.9));
                assert!(store.set_structured_type_members(
                    result,
                    None,
                    None,
                    Some(vec![copied]),
                    None,
                    None
                ));
            }
            _ => unreachable!(),
        }
        wave148_recovery_rejects_without_writes(&mut fixture, result, &mut session, mutation);
    }
}

#[test]
fn property_recovery_wave148_parameter_revocation_survives_restore() {
    for source in [false, true] {
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_403));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let actual = store
            .type_payload(result)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let signature = if source {
            store.signature(actual).unwrap().target().unwrap()
        } else {
            actual
        };
        let parameter = store.signature(signature).unwrap().parameters()[0];
        let links = store.value_symbol_links(parameter).cloned().unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: None,
                ..links.clone()
            }
        ));
        assert!(store.set_value_symbol_links(parameter, links));
        assert!(
            store
                .instantiated_property_method_recovery(result)
                .is_some()
        );
        wave148_recovery_rejects_without_writes(
            &mut fixture,
            result,
            &mut session,
            if source {
                "restored_source_parameter"
            } else {
                "restored_copied_parameter"
            },
        );
    }
}

#[test]
fn property_recovery_wave148_ordinary_proof_remains_separate() {
    use crate::semantic::callable_sets::{
        validate_stored_callable_set, validate_stored_declared_method_callable_set,
    };
    let parsed = property_recovery_source("first(value: T): T;");
    let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_404));
    let (recovered, mut recovery_session) = recover_first_method(&mut fixture);
    let store = fixture.context.store_mut_for_test();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let (error, string) = (bootstrap.error_type, bootstrap.string_type);
    assert!(matches!(
        validate_stored_declared_method_callable_set(store, fixture.template),
        Some(StoredCallableSetValidation::Valid { .. })
    ));
    assert!(!matches!(
        validate_stored_declared_method_callable_set(store, recovered),
        Some(StoredCallableSetValidation::Valid { .. })
    ));
    assert!(!cached_instantiated_interface_method_type_matches(
        store,
        fixture.template,
        recovered,
        fixture.mapper,
        Some(fixture.array_targets)
    ));
    let reference = store
        .create_direct_generic_reference_type(fixture.members.target(), &[string])
        .unwrap();
    let members =
        resolve_members_with_array_targets(store, reference, Some(fixture.array_targets)).unwrap();
    let proxy = store
        .symbol_table(members.members().unwrap())
        .unwrap()
        .get_source("first")
        .unwrap();
    let mut ordinary_session = InstantiationSession::new(InstantiationLimits::default());
    let ordinary = demand_instantiated_property_type(
        store,
        reference,
        proxy,
        Some(fixture.array_targets),
        &mut ordinary_session,
    )
    .unwrap();
    assert_ne!(ordinary, recovered);
    assert!(
        store
            .instantiated_property_method_recovery(ordinary)
            .is_none()
    );
    for (type_, expected) in [(recovered, error), (ordinary, string)] {
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, type_)
        else {
            panic!("both producers must remain valid")
        };
        assert_eq!(projection.call_signatures.len(), 1);
        assert_eq!(projection.call_signatures[0].parameters, vec![expected]);
        assert_eq!(projection.call_signatures[0].return_type, Some(expected));
    }
    let links = store.value_symbol_links(fixture.proxy).cloned().unwrap();
    assert!(store.set_value_symbol_links(fixture.proxy, links));
    wave148_recovery_rejects_without_writes(
        &mut fixture,
        recovered,
        &mut recovery_session,
        "revoked_recovery_does_not_fall_through",
    );
    let store = fixture.context.store_mut_for_test();
    assert!(matches!(
        validate_stored_callable_set(store, ordinary),
        StoredCallableSetValidation::Valid { .. }
    ));
    assert!(matches!(
        validate_stored_declared_method_callable_set(store, fixture.template),
        Some(StoredCallableSetValidation::Valid { .. })
    ));
}

#[test]
fn property_recovery_wave148_recursive_graph_retains_array_mode() {
    use crate::semantic::callable_sets::validate_stored_callable_set;
    for arrays in [false, true] {
        let member = if arrays {
            "first(value: Array<T>): Array<T>;"
        } else {
            "first(value: T): T;"
        };
        let parsed = parse_source_file(&format!(
            "interface Array<T> {{}} interface ReadonlyArray<T> {{}} interface Box<T> {{ {member} second: T; }} interface Derived extends Box<Derived> {{}}"
        ));
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_405));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let before = (
            property_recovery_store_counts(store),
            store.relation_state_snapshot(),
        );
        let mark = session.limit_event_mark();
        for _ in 0..4 {
            assert!(matches!(
                validate_stored_callable_set(store, result),
                StoredCallableSetValidation::Valid { .. }
            ));
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(
                    fixture.array_targets,
                    result
                ),
                Ok(())
            );
            assert_eq!(
                store.validate_cached_array_capability(result).is_err(),
                arrays
            );
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    &mut session
                ),
                Ok(result)
            );
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before
            );
        }
        assert!(!session.limit_event_occurred_since(mark));
        eprintln!("wave148 recursive graph arrays={arrays}: four stable passes");
    }
}
