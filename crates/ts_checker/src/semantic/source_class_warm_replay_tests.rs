mod source_class_warm_replay_tests {
    use super::*;
    use crate::semantic::{
        DeclaredTypeLinks, classes::SourceClassProvenance,
        instantiate::instantiate_type_with_vector_and_session,
        module_resolution::CanonicalModuleResolutionManifest, type_records::TypeParameterData,
    };

    fn class_declaration(source: &ParseResult, file: FileId, name: &str) -> NodeRef {
        source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let name_node = NodeRef::new(source.arena.id(), file, class.name?);
                (node_text(source, name_node) == name).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap()
    }

    // Use the real source checker and its success-only completion publisher.
    fn check_with_caller(
        context: &mut CanonicalCheckerContext<'_>,
        source: &ParseResult,
        file: FileId,
        caller: &mut InstantiationSession,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<(), SourceCheckError> {
        let bound = context.file(file).unwrap().1.clone();
        let source_file = context.source_file(file).unwrap();
        let options = context.options();
        let globals = context.global_types().clone();
        let manifest = CanonicalModuleResolutionManifest::unavailable();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&source.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap()
        .with_module_resolutions(&manifest);
        let mut aliases =
            ProductionAliasTargetHost::new(context.store(), [(&source.arena, &bound)], &manifest)
                .unwrap();
        let demand = RefCell::new(None);
        let result = check_source_file(
            &source.arena,
            &bound,
            source_file,
            &host,
            &mut aliases,
            &globals,
            context.store_mut_for_test(),
            options,
            None,
            caller,
            diagnostics,
            &[],
            &demand,
        );
        assert!(demand.borrow().is_none());
        result.and_then(|()| publish_type_checked(context.store_mut_for_test(), source_file))
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct RetainedClass {
        declaration: NodeRef,
        owner: SemanticSymbolId,
        instance: TypeId,
        value: TypeId,
        formals: Vec<(NodeRef, SemanticSymbolId, TypeId, TypeParameterData)>,
        constructor: SignatureId,
        provenance: SourceClassProvenance,
    }

    #[allow(clippy::too_many_lines)] // Read the complete class identity without a new accessor.
    fn retained_class(
        context: &CanonicalCheckerContext<'_>,
        source: &ParseResult,
        file: FileId,
        name: &str,
    ) -> RetainedClass {
        let declaration = class_declaration(source, file, name);
        let bound = context.file(file).unwrap().1;
        let owner = bound.symbol(declaration).unwrap();
        let store = context.store();
        assert_eq!(store.symbol(owner).unwrap().flags(), SymbolFlags::CLASS);
        let instance = store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        let value = store
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        let NodeData::ClassDeclaration(class) = &source.arena.get(declaration.node).unwrap().data
        else {
            panic!("the class must keep its real declaration")
        };
        let formals = class
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|&node| {
                let node = NodeRef::new(source.arena.id(), file, node);
                let symbol = bound.symbol(node).unwrap();
                let type_ = store
                    .declared_type_links(symbol)
                    .unwrap()
                    .declared_type
                    .unwrap();
                let record = store.type_payload(type_).unwrap();
                let TypeData::TypeParameter(data) = record.data() else {
                    panic!("the real class formal must keep its type parameter")
                };
                assert_eq!(record.symbol(), Some(symbol));
                assert_eq!(store.get_parent_of_symbol(symbol), Some(owner));
                (node, symbol, type_, data.clone())
            })
            .collect::<Vec<_>>();
        let formal_types = formals.iter().map(|row| row.2).collect::<Vec<_>>();
        let TypeData::Interface(instance_data) = store.type_payload(instance).unwrap().data()
        else {
            panic!("the class must keep its instance interface")
        };
        assert_eq!(
            instance_data.reference.resolved_type_arguments.as_deref(),
            Some(formal_types.as_slice())
        );
        assert!(!formal_types.contains(&instance_data.this_type.unwrap()));
        let constructor_node = class
            .members
            .nodes
            .iter()
            .find(|&&node| source.arena.get(node).unwrap().kind == SyntaxKind::Constructor)
            .copied()
            .unwrap();
        let constructor = store
            .signature_links(NodeRef::new(source.arena.id(), file, constructor_node))
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let signature = store.signature(constructor).unwrap();
        assert_eq!(signature.type_parameters(), formal_types);
        assert_eq!(signature.resolved_return_type(), Some(instance));
        assert_eq!(signature.target(), None);
        assert_eq!(signature.mapper(), None);
        let [parameter] = signature.parameters() else {
            panic!("the constructor has one real value parameter")
        };
        assert_eq!(
            store.value_symbol_links(*parameter).unwrap().resolved_type,
            Some(formals[0].2)
        );
        let field = declared_object_property_symbol(context, instance, "value");
        assert_eq!(
            store.value_symbol_links(field).unwrap().resolved_type,
            Some(formals[0].2)
        );
        let provenance = store
            .source_class_provenance_for_symbol(owner)
            .unwrap()
            .clone();
        assert_eq!(provenance.symbol(), owner);
        assert_eq!(provenance.instance_type(), instance);
        assert_eq!(store.source_class_provenance(instance), Some(&provenance));
        assert!(store.source_class_annotation_scope(instance).is_none());
        RetainedClass {
            declaration,
            owner,
            instance,
            value,
            formals,
            constructor,
            provenance,
        }
    }

    fn assert_failed_replay(
        context: &mut CanonicalCheckerContext<'_>,
        source: &ParseResult,
        file: FileId,
        caller: &mut InstantiationSession,
        diagnostics: &mut CanonicalCheckerDiagnostics,
        expected: SourceCheckError,
    ) {
        mark_source_unchecked(context, file);
        let store = format!("{:?}", context.store());
        let caller_state = format!("{caller:?}");
        let saved_diagnostics = diagnostics.clone();
        for _ in 0..2 {
            assert_eq!(
                check_with_caller(context, source, file, caller, diagnostics),
                Err(expected)
            );
            assert_eq!(format!("{:?}", context.store()), store);
            assert_eq!(format!("{caller:?}"), caller_state);
            assert_eq!(*diagnostics, saved_diagnostics);
            assert!(!is_type_checked(context, file));
        }
    }

    fn spent_caller(
        context: &mut CanonicalCheckerContext<'_>,
        formal: TypeId,
    ) -> InstantiationSession {
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let error = bootstrap.error_type;
        let arrays = Some(CanonicalArrayTargets::from_global_types(
            context.global_types(),
        ));
        let mut caller = InstantiationSession::new_recovering(
            context.store(),
            InstantiationLimits {
                max_count: 1,
                ..InstantiationLimits::default()
            },
            error,
        )
        .unwrap();
        for expected in [number, error] {
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    context.store_mut_for_test(),
                    formal,
                    &[formal],
                    &[number],
                    arrays,
                    &mut caller,
                ),
                Ok(expected)
            );
        }
        assert_eq!(
            (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_count()
            ),
            (1, 1, 1)
        );
        caller
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both source routes keep the same real class and caller.
    fn source_class_warm_replay_routes_exported_and_local_unconstrained_headers() {
        for exported in [false, true] {
            let prefix = if exported { "export " } else { "" };
            let source = parsed(&format!(
                "{prefix}class Box<T, U = T> {{ value: T; \
                 constructor(value: T) {{ this.value = value; }} }} class Plain {{}}"
            ));
            let file = FileId::new(202_1860 + u32::from(exported));
            let options = CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_property_initialization: true,
                ..CanonicalCheckerOptions::default()
            };
            let mut context = context_with_module_state(
                &[(file, &source)],
                if exported {
                    CanonicalModuleState::External
                } else {
                    CanonicalModuleState::Script
                },
                options,
            );
            let declaration = class_declaration(&source, file, "Box");
            let plain = class_declaration(&source, file, "Plain");
            let bound = context.file(file).unwrap().1.clone();
            let owner = bound.symbol(declaration).unwrap();
            let plain_owner = bound.symbol(plain).unwrap();
            let NodeData::ClassDeclaration(class) =
                &source.arena.get(declaration.node).unwrap().data
            else {
                panic!("Box must retain its real class declaration")
            };
            assert!(
                !crate::semantic::classes::source_class_needs_early_constructor_plan(
                    &source.arena,
                    &class.members.nodes,
                )
            );
            assert!(
                context
                    .store()
                    .source_class_provenance_for_symbol(owner)
                    .is_none()
            );
            if exported {
                let local = bound.local_symbol(declaration).unwrap();
                assert_ne!(local, owner);
                assert_eq!(
                    context.store().symbol(local).unwrap().export_symbol(),
                    Some(owner)
                );
            }
            let mut caller = InstantiationSession::new(InstantiationLimits::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            check_with_caller(&mut context, &source, file, &mut caller, &mut diagnostics).unwrap();
            assert!(is_type_checked(&context, file));
            assert!(diagnostics.is_empty());
            let retained = retained_class(&context, &source, file, "Box");
            let no_constraint = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .no_constraint_type;
            let [first, second] = retained.formals.as_slice() else {
                panic!("Box keeps both ordered written formals")
            };
            for (row, default) in [(first, no_constraint), (second, first.2)] {
                assert_eq!(row.3.constraint, Some(no_constraint));
                assert_eq!(row.3.resolved_default_type, Some(default));
                assert_eq!(
                    row.3.constrained.resolved_base_constraint,
                    Some(no_constraint)
                );
                assert_eq!(row.3.target, None);
                assert_eq!(row.3.mapper, None);
            }
            let globals = context.global_types().clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&source.arena, &bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let warm = observable_state(&context, file);
            for _ in 0..2 {
                mark_source_unchecked(&mut context, file);
                let plan = SourcePlanner::new_semantic_with_global_types(
                    &source.arena,
                    &bound,
                    context.source_file(file).unwrap(),
                    context.store(),
                    &host,
                    &globals,
                    options,
                )
                .finish()
                .unwrap();
                assert!(matches!(plan.statements.as_slice(),
                    [PlannedStatement::SourceClass(source_class), PlannedStatement::Class(plain_class)]
                        if source_class.source.symbol() == owner && plain_class.symbol() == plain_owner));
                check_with_caller(&mut context, &source, file, &mut caller, &mut diagnostics)
                    .unwrap();
                assert_eq!(retained_class(&context, &source, file, "Box"), retained);
                assert_eq!(observable_state(&context, file), warm);
                assert!(
                    context
                        .store()
                        .source_class_provenance_for_symbol(plain_owner)
                        .is_none()
                );
                assert!(diagnostics.is_empty());
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Every poison and restore uses the original class records.
    fn source_class_warm_replay_rejects_formal_and_provenance_damage() {
        enum Damage {
            Constraint(Option<TypeId>),
            Default(Option<TypeId>),
            Base(Option<TypeId>),
            FormalOwner,
        }
        let source = parsed(concat!(
            "export class Box<T, U = T> { value: T; ",
            "constructor(value: T) { this.value = value; } } ",
            "export class Other<V> { value: V; ",
            "constructor(value: V) { this.value = value; } }",
        ));
        let file = FileId::new(202_1862);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_property_initialization: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let saved = retained_class(&context, &source, file, "Box");
        let other = retained_class(&context, &source, file, "Other");
        assert_ne!(saved.owner, other.owner);
        assert_ne!(saved.instance, other.instance);
        assert_ne!(saved.constructor, other.constructor);
        let (parameter, symbol, formal, data) = saved.formals[1].clone();
        let links = context.store().declared_type_links(symbol).unwrap().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let mut caller = spent_caller(&mut context, saved.formals[0].2);
        let recovery = caller.recovery_error_type();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        for damage in [
            Damage::Constraint(None),
            Damage::Constraint(Some(number)),
            Damage::Default(None),
            Damage::Default(Some(number)),
            Damage::Base(None),
            Damage::Base(Some(number)),
            Damage::FormalOwner,
        ] {
            let mut changed = data.clone();
            let expected = match damage {
                Damage::Constraint(value) => {
                    changed.constraint = value;
                    SourceCheckError::Class(saved.declaration)
                }
                Damage::Default(value) => {
                    changed.resolved_default_type = value;
                    SourceCheckError::Class(saved.declaration)
                }
                Damage::Base(value) => {
                    changed.constrained.resolved_base_constraint = value;
                    SourceCheckError::Class(saved.declaration)
                }
                Damage::FormalOwner => {
                    assert!(context.store_mut_for_test().set_declared_type_links(
                        symbol,
                        DeclaredTypeLinks {
                            declared_type: Some(other.formals[0].2),
                            ..links.clone()
                        }
                    ));
                    SourceCheckError::Class(parameter)
                }
            };
            let store = context.store_mut_for_test();
            assert!(store.set_type_parameter_resolution(
                formal,
                changed.constraint,
                changed.target,
                changed.mapper,
                changed.resolved_default_type
            ));
            assert!(store.set_resolved_base_constraint(
                formal,
                changed.constrained.resolved_base_constraint
            ));
            assert_failed_replay(
                &mut context,
                &source,
                file,
                &mut caller,
                &mut diagnostics,
                expected,
            );
            let store = context.store_mut_for_test();
            assert!(store.set_declared_type_links(symbol, links.clone()));
            assert!(store.set_type_parameter_resolution(
                formal,
                data.constraint,
                data.target,
                data.mapper,
                data.resolved_default_type
            ));
            assert!(
                store.set_resolved_base_constraint(
                    formal,
                    data.constrained.resolved_base_constraint
                )
            );
            assert_eq!(retained_class(&context, &source, file, "Box"), saved);
            for _ in 0..2 {
                mark_source_unchecked(&mut context, file);
                check_with_caller(&mut context, &source, file, &mut caller, &mut diagnostics)
                    .unwrap();
                assert_eq!(retained_class(&context, &source, file, "Box"), saved);
                assert_eq!(retained_class(&context, &source, file, "Other"), other);
                assert!(is_type_checked(&context, file));
                assert!(diagnostics.is_empty());
                assert_eq!(caller.recovery_error_type(), recovery);
            }
        }

        *context
            .store_mut_for_test()
            .source_class_provenance_mut(saved.instance)
            .unwrap() = other.provenance.clone();
        mark_source_unchecked(&mut context, file);
        let damaged = format!("{:?}", context.store());
        let caller_state = format!("{caller:?}");
        for _ in 0..2 {
            // This reader checks the requested instance against the real retained row.
            assert_eq!(
                crate::semantic::classes::class_instance_type_edges(
                    context.store(),
                    saved.instance
                ),
                Err(crate::semantic::classes::ClassError::Invariant(
                    crate::semantic::classes::ClassInvariant::InvalidInstanceMembers(other.owner),
                ))
            );
            assert_eq!(format!("{:?}", context.store()), damaged);
            assert_eq!(format!("{caller:?}"), caller_state);
            assert!(!is_type_checked(&context, file));
            assert!(diagnostics.is_empty());
        }
        *context
            .store_mut_for_test()
            .source_class_provenance_mut(saved.instance)
            .unwrap() = saved.provenance.clone();
        assert_eq!(retained_class(&context, &source, file, "Box"), saved);
        for _ in 0..2 {
            mark_source_unchecked(&mut context, file);
            check_with_caller(&mut context, &source, file, &mut caller, &mut diagnostics).unwrap();
            assert_eq!(retained_class(&context, &source, file, "Box"), saved);
            assert_eq!(retained_class(&context, &source, file, "Other"), other);
            assert!(is_type_checked(&context, file));
            assert!(diagnostics.is_empty());
            assert_eq!(caller.recovery_error_type(), recovery);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both real constructor maps stay visible across poison and restore.
    fn source_class_warm_replay_rejects_a_foreign_constructor_mapper() {
        let source = parsed(concat!(
            "export class Box<T> { value: T; constructor(value: T) { this.value = value; } } ",
            "const text = new Box<string>('text'); const count = new Box<number>(1);",
        ));
        let file = FileId::new(202_1863);
        let mut context = context_with_module_state(
            &[(file, &source)],
            CanonicalModuleState::External,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_property_initialization: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let saved = retained_class(&context, &source, file, "Box");
        let text = variable_initializer(&source, file, "text");
        let count = variable_initializer(&source, file, "count");
        let signature_for = |node| {
            context
                .store()
                .signature_links(node)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap()
        };
        let text_signature = signature_for(text);
        let count_signature = signature_for(count);
        assert_ne!(text_signature, count_signature);
        let text_mapper = context
            .store()
            .signature(text_signature)
            .unwrap()
            .mapper()
            .unwrap();
        let count_mapper = context
            .store()
            .signature(count_signature)
            .unwrap()
            .mapper()
            .unwrap();
        assert_ne!(text_mapper, count_mapper);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context.store().map_type(text_mapper, saved.formals[0].2),
            Some(bootstrap.string_type)
        );
        assert_eq!(
            context.store().map_type(count_mapper, saved.formals[0].2),
            Some(bootstrap.number_type)
        );
        let text_instance = resolved_node_type(&context, text);
        let count_instance = resolved_node_type(&context, count);
        assert_ne!(text_instance, count_instance);
        for (signature, instance) in [
            (text_signature, text_instance),
            (count_signature, count_instance),
        ] {
            let signature = context.store().signature(signature).unwrap();
            assert_eq!(signature.target(), Some(saved.constructor));
            assert_eq!(signature.resolved_return_type(), Some(instance));
        }
        let maps = format!(
            "{:?}",
            (
                context.store().mapper_payload(text_mapper).unwrap(),
                context.store().mapper_payload(count_mapper).unwrap(),
            )
        );
        let mut caller = spent_caller(&mut context, saved.formals[0].2);
        let recovery = caller.recovery_error_type();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            context
                .store_mut_for_test()
                .set_signature_target_and_mapper(
                    text_signature,
                    Some(saved.constructor),
                    Some(count_mapper),
                )
        );
        assert_failed_replay(
            &mut context,
            &source,
            file,
            &mut caller,
            &mut diagnostics,
            SourceCheckError::Call(text),
        );
        assert!(
            context
                .store_mut_for_test()
                .set_signature_target_and_mapper(
                    text_signature,
                    Some(saved.constructor),
                    Some(text_mapper),
                )
        );
        for _ in 0..2 {
            mark_source_unchecked(&mut context, file);
            check_with_caller(&mut context, &source, file, &mut caller, &mut diagnostics).unwrap();
            assert_eq!(retained_class(&context, &source, file, "Box"), saved);
            for (node, signature, instance, mapper) in [
                (text, text_signature, text_instance, text_mapper),
                (count, count_signature, count_instance, count_mapper),
            ] {
                assert_eq!(
                    context
                        .store()
                        .signature_links(node)
                        .unwrap()
                        .resolved_signature
                        .signature(),
                    Some(signature)
                );
                assert_eq!(resolved_node_type(&context, node), instance);
                let signature = context.store().signature(signature).unwrap();
                assert_eq!(signature.target(), Some(saved.constructor));
                assert_eq!(signature.mapper(), Some(mapper));
                assert_eq!(signature.resolved_return_type(), Some(instance));
            }
            assert_eq!(
                format!(
                    "{:?}",
                    (
                        context.store().mapper_payload(text_mapper).unwrap(),
                        context.store().mapper_payload(count_mapper).unwrap(),
                    )
                ),
                maps
            );
            assert_eq!(caller.recovery_error_type(), recovery);
            assert!(is_type_checked(&context, file));
            assert!(diagnostics.is_empty());
        }
    }
}
