use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    bootstrap::UnionReduction, production::GlobalMergeCompletion,
};

const FILE: FileId = FileId::new(96_601);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/super-views.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let bound = context.file(FILE).unwrap().1;
    context
        .store()
        .symbol_table(bound.locals(bound.source_file()).unwrap())
        .and_then(|table| table.get_source(name))
        .unwrap()
}

fn host<'a>(parsed: &'a ParseResult, bound: &'a ts_binder::BoundFile) -> DeclaredTypeHost<'a> {
    DeclaredTypeHost::new_after_global_merge(
        [(&parsed.arena, bound)],
        GlobalMergeCompletion::for_test(ts_binder::CanonicalNameResolverOptions::default()),
    )
    .unwrap()
}

fn mapped_super_identity(
    store: &CanonicalTypeMapperStore,
    view: ClassInstanceSuperView,
) -> (TypeId, TypeMapperId) {
    let base_this =
        exact_class_instance_identity(store, view.origin.base_symbol, view.origin.base_instance)
            .expect("the fixture retains its real base class")
            .this_type
            .expect("the base class retains its polymorphic this type");
    assert_eq!(view.origin.base_this, Some(base_this));
    let mapper = view
        .mapper
        .expect("the class super view retains its mapper");
    assert_eq!(
        store.type_mapper_has_exact_endpoints(mapper, &[base_this], &[view.origin.this_type]),
        Some(true),
    );
    (base_this, mapper)
}

#[test]
fn class_polymorphic_super_pending_header_and_completed_class_share_the_reference() {
    let parsed =
        parse_source_file("class Base {} class Derived extends Base { read() { return this; } }");
    assert!(parsed.diagnostics.is_empty());
    let mut context = context(&parsed);
    let base = symbol(&context, "Base");
    let derived = symbol(&context, "Derived");
    let bound = context.file(FILE).unwrap().1.clone();
    let host = host(&parsed, &bound);
    let type_context = ClassTypeQueryContext::new(context.global_types(), context.options());
    let base_plan = plan_source_class_members_with_type_context(
        context.store(),
        &host,
        base,
        Some(&type_context),
    )
    .unwrap();
    let prepared_base =
        prepare_source_class_members(context.store_mut_for_test(), &host, &base_plan).unwrap();
    finish_source_class_members(
        context.store_mut_for_test(),
        &host,
        &base_plan,
        &prepared_base,
    )
    .unwrap();
    let plan = plan_source_class_members_with_type_context(
        context.store(),
        &host,
        derived,
        Some(&type_context),
    )
    .unwrap();
    let prepared =
        prepare_source_class_members(context.store_mut_for_test(), &host, &plan).unwrap();
    let access = prepared
        .body_access(context.store(), &host, &plan.bodies()[0])
        .unwrap();
    let this_type = class_body_identities(context.store(), &host, &access)
        .unwrap()
        .this_type;
    let globals = context.global_types().clone();
    assert_eq!(
        context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &globals,
                &[this_type],
                UnionReduction::Subtype,
            ),
        Ok(this_type),
        "the exact pending synthetic this is a valid inferred return",
    );
    assert_eq!(context.type_to_string(this_type).unwrap(), "this");
    assert_ne!(
        validate_class_heritage_members(context.store(), prepared.instance_type),
        ClassHeritageMembersValidation::Valid,
        "admitting synthetic this must not complete the pending class",
    );
    let view = prepare_class_instance_super_view(
        context.store_mut_for_test(),
        &host,
        derived,
        Some(&access),
    )
    .unwrap();
    assert_eq!(view.origin.base_instance, prepared_base.instance_type);
    assert_eq!(view.origin.instance_type, prepared.instance_type);
    let (base_this, mapper) = mapped_super_identity(context.store(), view);
    let undefined = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    let base_union = context
        .store_mut_for_test()
        .expression_union_type_with_global_types(
            &globals,
            &[base_this, undefined],
            UnionReduction::Literal,
        )
        .unwrap();
    let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
    let mapped_union = instantiate_type_with_vector_and_session(
        context.store_mut_for_test(),
        base_union,
        &[base_this],
        &[this_type],
        targets,
        &mut InstantiationSession::new(InstantiationLimits::default()),
    )
    .unwrap();
    let TypeData::Union(mapped) = context.store().type_payload(mapped_union).unwrap().data() else {
        panic!("mapping this keeps the undefined union member")
    };
    assert_eq!(mapped.union.types.len(), 2);
    assert!(mapped.union.types.contains(&this_type));
    assert!(mapped.union.types.contains(&undefined));
    assert!(!mapped.union.types.contains(&base_this));
    assert_eq!(
        instantiated_member_type_matches(
            context.store(),
            base_union,
            mapped_union,
            mapper,
            targets,
        ),
        Ok(true),
    );
    assert!(
        !context
            .store()
            .source_class_provenance(prepared.instance_type)
            .unwrap()
            .complete
    );
    assert_eq!(
        validate_class_instance_super_view(
            context.store(),
            &host,
            derived,
            Some(&access),
            view.reference
        ),
        Ok(view),
    );
    assert!(
        prepare_class_instance_super_view(context.store_mut_for_test(), &host, derived, None)
            .is_err()
    );

    context.check_source_file(FILE).unwrap();

    assert!(
        context
            .store()
            .source_class_provenance(prepared.instance_type)
            .unwrap()
            .complete
    );
    assert_eq!(
        prepare_class_instance_super_view(context.store_mut_for_test(), &host, derived, None),
        Ok(view),
    );
    assert_eq!(
        context
            .store()
            .source_class_provenance(prepared.instance_type)
            .unwrap()
            .prepared,
        prepared
    );
}

#[test]
fn class_polymorphic_super_rejects_changed_view_and_signature_provenance() {
    #[derive(Clone, Copy, Debug)]
    enum Poison {
        ReceiverTarget,
        ThisArgument,
        ReceiverFlags,
        MethodTarget,
        MethodMapper,
        SignatureTarget,
        SignatureMapper,
        SignatureReturn,
        ThisParameterDefault,
        ThisParameterOwner,
        BaseInstantiation,
    }
    for poison in [
        Poison::ReceiverTarget,
        Poison::ThisArgument,
        Poison::ReceiverFlags,
        Poison::MethodTarget,
        Poison::MethodMapper,
        Poison::SignatureTarget,
        Poison::SignatureMapper,
        Poison::SignatureReturn,
        Poison::ThisParameterDefault,
        Poison::ThisParameterOwner,
        Poison::BaseInstantiation,
    ] {
        let parsed = parse_source_file(concat!(
            "class Base { self() { return this; } } ",
            "class Derived extends Base { read() { return super.self(); } }",
        ));
        assert!(parsed.diagnostics.is_empty());
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let derived = symbol(&context, "Derived");
        let instance = context
            .store()
            .declared_type_links(derived)
            .unwrap()
            .declared_type
            .unwrap();
        let view = context
            .store()
            .class_instance_super_view_for_instance(instance)
            .unwrap();
        let (base_this, _) = mapped_super_identity(context.store(), view);
        let member = context
            .store()
            .symbol(view.origin.base_symbol)
            .unwrap()
            .members()
            .and_then(|table| context.store().symbol_table(table))
            .and_then(|table| table.get_source("self"))
            .unwrap();
        let retained = context
            .store()
            .class_instance_super_member(view.reference, member)
            .unwrap()
            .clone();
        let instantiated_signature = retained.callable.as_ref().unwrap().signature;
        let original = retained.source_callable.as_ref().unwrap().signature;
        assert!(matches!(
            validate_stored_callable_set(context.store(), retained.type_),
            StoredCallableSetValidation::Valid { projection, .. }
                if projection.call_signatures[0].signature == instantiated_signature,
        ));
        let bound = context.file(FILE).unwrap().1.clone();
        let host = host(&parsed, &bound);
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        match poison {
            Poison::ReceiverTarget => {
                assert!(store.set_object_target_and_mapper(view.reference, Some(instance), None));
            }
            Poison::ThisArgument => assert!(store.set_type_reference_resolution(
                view.reference,
                None,
                Some(vec![base_this])
            )),
            Poison::ReceiverFlags => assert!(store.set_type_object_flags(
                view.reference,
                ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED
            )),
            Poison::MethodTarget => assert!(store.set_object_target_and_mapper(
                retained.type_,
                Some(retained.type_),
                Some(retained.mapper)
            )),
            Poison::MethodMapper => {
                let mapper = store
                    .new_type_mapper(vec![base_this], vec![base_this])
                    .unwrap();
                assert!(store.set_object_target_and_mapper(
                    retained.type_,
                    Some(retained.source_type),
                    Some(mapper)
                ));
            }
            Poison::SignatureTarget => assert!(store.set_signature_target_and_mapper(
                instantiated_signature,
                Some(instantiated_signature),
                Some(retained.mapper)
            )),
            Poison::SignatureMapper => {
                let mapper = store
                    .new_type_mapper(vec![base_this], vec![base_this])
                    .unwrap();
                assert!(store.set_signature_target_and_mapper(
                    instantiated_signature,
                    Some(original),
                    Some(mapper)
                ));
            }
            Poison::SignatureReturn => assert!(
                store.set_signature_resolved_return_type(instantiated_signature, Some(base_this))
            ),
            Poison::ThisParameterDefault => assert!(store.set_type_parameter_resolution(
                view.origin.this_type,
                Some(instance),
                None,
                None,
                Some(store.intrinsic_bootstrap().unwrap().number_type),
            )),
            Poison::ThisParameterOwner => {
                assert!(
                    store.set_type_symbol(view.origin.this_type, Some(view.origin.base_symbol))
                );
            }
            Poison::BaseInstantiation => {
                let unbranded = store
                    .alloc_type_reference(ObjectFlags::NONE, Some(view.origin.base_symbol))
                    .unwrap();
                assert!(store.set_object_target_and_mapper(
                    unbranded,
                    Some(view.origin.base_instance),
                    None,
                ));
                assert!(store.set_type_reference_resolution(
                    unbranded,
                    None,
                    Some(vec![base_this]),
                ));
                assert_eq!(
                    store.insert_object_instantiation(
                        view.origin.base_instance,
                        type_list_key(&[base_this]),
                        unbranded,
                    ),
                    Some(unbranded),
                );
            }
        }
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                store.class_instance_super_view(view.reference),
                store
                    .class_instance_super_member(view.reference, member)
                    .cloned(),
            )
        };
        let before = snapshot(store);
        for _ in 0..2 {
            let result =
                prepare_class_instance_super_view(store, &host, derived, None).and_then(|view| {
                    prepare_class_instance_super_member_type(
                        store,
                        &host,
                        Some(&globals),
                        view,
                        member,
                    )
                });
            assert!(result.is_err(), "{poison:?}");
            assert!(
                matches!(
                    validate_stored_callable_set(store, retained.type_),
                    StoredCallableSetValidation::Malformed { .. },
                ),
                "{poison:?}"
            );
            assert_eq!(snapshot(store), before, "{poison:?}");
        }
    }
}

#[test]
fn class_polymorphic_super_synthetic_this_requires_its_stored_source_header() {
    let parsed = parse_source_file("class Owner { read() { return this; } }");
    assert!(parsed.diagnostics.is_empty());
    let mut context = context(&parsed);
    let owner = symbol(&context, "Owner");
    let bound = context.file(FILE).unwrap().1.clone();
    let host = host(&parsed, &bound);
    let plan = plan_source_class_members(context.store(), &host, owner).unwrap();
    let prepared =
        prepare_source_class_members(context.store_mut_for_test(), &host, &plan).unwrap();
    let this_type = context
        .store()
        .source_class_provenance(prepared.instance_type)
        .unwrap()
        .this_type;
    assert_eq!(
        source_class_this_type_owner(context.store(), this_type),
        Some(owner)
    );

    let store = context.store_mut_for_test();
    let counterfeit_class = store
        .alloc_interface_type(ObjectFlags::CLASS, Some(owner))
        .unwrap();
    let counterfeit_this = store.alloc_type_parameter(Some(owner)).unwrap();
    assert!(store.initialize_interface_type_parameters(
        counterfeit_class,
        vec![counterfeit_this],
        0,
        counterfeit_this,
        type_list_key(&[]),
    ));
    assert_eq!(source_class_this_type_owner(store, counterfeit_this), None);
    assert!(store.validate_union_constituent(counterfeit_this).is_err());
    assert_eq!(source_class_this_type_owner(store, this_type), Some(owner));
    assert!(context.type_to_string(counterfeit_this).is_err());

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert!(context.store_mut_for_test().set_type_parameter_resolution(
        this_type,
        Some(prepared.instance_type),
        None,
        None,
        Some(number),
    ));
    let globals = context.global_types().clone();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        )
    };
    let before = snapshot(&context);
    for _ in 0..2 {
        assert_eq!(
            source_class_this_type_owner(context.store(), this_type),
            None
        );
        assert!(
            context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &globals,
                    &[this_type],
                    UnionReduction::Subtype,
                )
                .is_err()
        );
        assert!(context.type_to_string(this_type).is_err());
        assert_eq!(snapshot(&context), before);
    }
}

#[test]
fn class_polymorphic_super_does_not_preserve_an_object_with_mapped_this() {
    let parsed = parse_source_file(concat!(
        "class Base { wrapped() { return { value: { self: this } }; } } ",
        "class Derived extends Base {}",
    ));
    assert!(parsed.diagnostics.is_empty());
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let base = symbol(&context, "Base");
    let derived = symbol(&context, "Derived");
    let member = context
        .store()
        .symbol(base)
        .unwrap()
        .members()
        .and_then(|table| context.store().symbol_table(table))
        .and_then(|table| table.get_source("wrapped"))
        .unwrap();
    let bound = context.file(FILE).unwrap().1.clone();
    let host = host(&parsed, &bound);
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let view = prepare_class_instance_super_view(store, &host, derived, None).unwrap();
    let (base_this, _) = mapped_super_identity(store, view);
    let template = class_super_member_template(store, &host, view, member).unwrap();
    let returned = template.callable.as_ref().unwrap().return_type.unwrap();
    assert!(
        store
            .validate_union_constituent_with_global_types(&globals, returned)
            .is_ok()
    );
    assert!(!class_super_member_type_is_unchanged(
        store,
        returned,
        &[base_this],
        Some(CanonicalArrayTargets::from_global_types(&globals)),
    ));
    let snapshot = |store: &CanonicalTypeMapperStore| {
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        )
    };
    let before = snapshot(store);
    for _ in 0..2 {
        assert_eq!(
            prepare_class_instance_super_member_type(store, &host, Some(&globals), view, member),
            Err(ClassError::Unsupported(ClassUnsupported::Member {
                node: template.source.declaration,
                kind: SyntaxKind::MethodDeclaration,
            })),
        );
        assert!(
            store
                .class_instance_super_member(view.reference, member)
                .is_none()
        );
        assert_eq!(snapshot(store), before);
    }
}

#[test]
fn class_polymorphic_super_rejects_a_changed_object_return() {
    let parsed = parse_source_file(concat!(
        "class Base { objectMethod() { return { value: 1 }; } } ",
        "class Derived extends Base { read() { return super.objectMethod(); } }",
    ));
    assert!(parsed.diagnostics.is_empty());
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let derived = symbol(&context, "Derived");
    let bound = context.file(FILE).unwrap().1.clone();
    let host = host(&parsed, &bound);
    let globals = context.global_types().clone();
    let store = context.store_mut_for_test();
    let view = prepare_class_instance_super_view(store, &host, derived, None).unwrap();
    let (base_this, _) = mapped_super_identity(store, view);
    let member = store
        .symbol(view.origin.base_symbol)
        .unwrap()
        .members()
        .and_then(|table| store.symbol_table(table))
        .and_then(|table| table.get_source("objectMethod"))
        .unwrap();
    let retained = validated_class_instance_super_member(store, &host, view, member).unwrap();
    assert_eq!(retained.type_, retained.source_type);
    let returned = retained.callable.as_ref().unwrap().return_type.unwrap();
    let TypeData::Object(object) = store.type_payload(returned).unwrap().data() else {
        panic!("the method returns a checked object literal")
    };
    let property = object.structured.properties.as_ref().unwrap()[0];
    let mut links = store.value_symbol_links(property).unwrap().clone();
    links.resolved_type = Some(base_this);
    assert!(store.set_value_symbol_links(property, links));
    let snapshot = |store: &CanonicalTypeMapperStore| {
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
            store
                .class_instance_super_member(view.reference, member)
                .cloned(),
        )
    };
    let before = snapshot(store);
    for _ in 0..2 {
        assert!(validated_class_instance_super_member(store, &host, view, member).is_err());
        assert!(
            prepare_class_instance_super_member_type(store, &host, Some(&globals), view, member,)
                .is_err()
        );
        assert_eq!(snapshot(store), before);
    }
}

#[test]
fn class_polymorphic_super_wrong_cold_property_receiver_is_rejected_without_writes() {
    use crate::semantic::{
        source::{PlannedExpression, PlannedExpressionKind},
        source_flow::{ClassInitializationFrame, SourceFlowPlan, SourceFlowTypes},
        source_properties::{
            SourcePropertyError, attach_class_access_context, check_class_receiver,
            check_direct_source_property_with_class_context, finish_direct_source_property_plan,
            plan_class_access_context, plan_direct_source_property_syntax,
        },
    };

    let parsed =
        parse_source_file("class Base {} class Derived extends Base { read() { super.missing; } }");
    assert!(parsed.diagnostics.is_empty());
    let mut context = context(&parsed);
    let base = symbol(&context, "Base");
    let derived = symbol(&context, "Derived");
    let bound = context.file(FILE).unwrap().1.clone();
    let host = host(&parsed, &bound);
    let globals = context.global_types().clone();
    let options = context.options();
    let base_plan = plan_source_class_members(context.store(), &host, base).unwrap();
    let prepared_base =
        prepare_source_class_members(context.store_mut_for_test(), &host, &base_plan).unwrap();
    finish_source_class_members(
        context.store_mut_for_test(),
        &host,
        &base_plan,
        &prepared_base,
    )
    .unwrap();

    let access = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .unwrap();
    let syntax =
        plan_direct_source_property_syntax(&parsed.arena, context.store(), access).unwrap();
    let receiver = plan_class_access_context(context.store(), &host, syntax.receiver())
        .unwrap()
        .unwrap();
    assert_eq!(receiver.class_symbol(), derived);
    let plan = plan_source_class_members(context.store(), &host, derived).unwrap();
    let body = plan
        .bodies()
        .iter()
        .find(|body| body.declaration == receiver.body_declaration())
        .unwrap();
    let flow_plan = SourceFlowPlan::preflight_class_body(
        &parsed.arena,
        &bound,
        context.store(),
        &host,
        body,
        [access],
        [],
        [],
    )
    .unwrap();
    let prepared =
        prepare_source_class_members(context.store_mut_for_test(), &host, &plan).unwrap();
    let token = prepared.body_access(context.store(), &host, body).unwrap();
    let mut flow =
        ClassInitializationFrame::new(body, &flow_plan, &bound, token, SourceFlowTypes::new())
            .unwrap();
    let expression = PlannedExpression::new(
        syntax.receiver(),
        PlannedExpressionKind::ClassReceiver(receiver),
    );
    let mut property = finish_direct_source_property_plan(&syntax, expression).unwrap();
    attach_class_access_context(context.store(), &host, &mut property).unwrap();
    let wrong_receiver = context.store().intrinsic_bootstrap().unwrap().number_type;
    let snapshot = |store: &CanonicalTypeMapperStore| {
        let TypeData::Interface(base) = store
            .type_payload(prepared_base.instance_type)
            .unwrap()
            .data()
        else {
            panic!("the base keeps its class payload")
        };
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            base.reference.object.instantiations.clone(),
            store.class_instance_super_view_for_instance(prepared.instance_type),
            store.type_node_links(syntax.receiver()).cloned(),
            store.symbol_node_links(syntax.receiver()).cloned(),
            store.type_node_links(access).cloned(),
            store.symbol_node_links(access).cloned(),
        )
    };
    let before = snapshot(context.store());
    assert!(before.6.is_none());
    for _ in 0..2 {
        let result = check_direct_source_property_with_class_context(
            context.store_mut_for_test(),
            &host,
            Some(&globals),
            options,
            &property,
            wrong_receiver,
            Some(&mut flow),
        );
        assert!(matches!(
            result,
            Err(SourcePropertyError::InvalidCache(node)) if node == syntax.receiver()
        ));
        assert_eq!(snapshot(context.store()), before);
    }

    let checked_receiver = check_class_receiver(
        context.store_mut_for_test(),
        &host,
        &globals,
        options,
        &receiver,
        Some(&mut flow),
    )
    .unwrap();
    assert!(checked_receiver.diagnostics.is_empty());
    let view = context
        .store()
        .class_instance_super_view_for_instance(prepared.instance_type)
        .unwrap();
    assert_eq!(checked_receiver.type_, view.receiver_type());
    assert_eq!(view.lookup_type(), prepared_base.instance_type);
    assert_ne!(checked_receiver.type_, view.lookup_type());
    let checked_property = check_direct_source_property_with_class_context(
        context.store_mut_for_test(),
        &host,
        Some(&globals),
        options,
        &property,
        checked_receiver.type_,
        Some(&mut flow),
    )
    .unwrap();
    assert_eq!(
        checked_property.type_,
        context.store().intrinsic_bootstrap().unwrap().error_type,
    );
    assert_eq!(checked_property.diagnostics.len(), 1);
    let warm = snapshot(context.store());
    for _ in 0..2 {
        assert!(matches!(
            check_direct_source_property_with_class_context(
                context.store_mut_for_test(),
                &host,
                Some(&globals),
                options,
                &property,
                wrong_receiver,
                Some(&mut flow),
            ),
            Err(SourcePropertyError::InvalidCache(node)) if node == syntax.receiver()
        ));
        assert_eq!(snapshot(context.store()), warm);
        let replayed_receiver = check_class_receiver(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &receiver,
            Some(&mut flow),
        )
        .unwrap();
        assert_eq!(replayed_receiver.type_, checked_receiver.type_);
        let replayed_property = check_direct_source_property_with_class_context(
            context.store_mut_for_test(),
            &host,
            Some(&globals),
            options,
            &property,
            replayed_receiver.type_,
            Some(&mut flow),
        )
        .unwrap();
        assert_eq!(replayed_property.type_, checked_property.type_);
        assert_eq!(replayed_property.diagnostics, checked_property.diagnostics);
        assert_eq!(snapshot(context.store()), warm);
    }
}
