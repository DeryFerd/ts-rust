use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeNodeLinks,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(
    parsed: &ParseResult,
    file: FileId,
    intrinsic: IntrinsicBootstrapOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/constructor-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic,
            strict_property_initialization: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn class_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    name: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn constructions(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect()
}

fn value_access(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "value").then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, access.name),
            ))
        })
        .unwrap()
}

#[test]
#[allow(clippy::too_many_lines)] // Each option checks errors, member identity, and source replay.
fn parameter_property_reads_report_visibility_without_losing_type_or_symbol() {
    for (visibility, code, message) in [
        ("public", None, ""),
        (
            "private",
            Some(2341),
            "Property 'value' is private and only accessible within class 'Model'.",
        ),
        (
            "protected",
            Some(2445),
            "Property 'value' is protected and only accessible within class 'Model' and its subclasses.",
        ),
    ] {
        for parameter in ["value?: number", "readonly value: number = 1"] {
            for exact_optional_property_types in [false, true] {
                let parsed = parse_source_file(&format!(
                    "class Model {{ constructor({visibility} {parameter}) {{}} }} \
                     const model = new Model(); const copy = model.value;",
                ));
                assert!(parsed.diagnostics.is_empty());
                let file = FileId::new(4_203);
                let mut context = context(
                    &parsed,
                    file,
                    IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types,
                    },
                );
                let owner = class_symbol(&parsed, file, &context, "Model");
                let (access, name) = value_access(&parsed, file);
                context.check_source_file(file).unwrap();
                let members = context.get_nongeneric_class_members(owner).unwrap();
                let [property] = members.declared_instance_properties() else {
                    panic!("the constructor declares one parameter property")
                };
                let property = *property;
                let expected_type = context
                    .store()
                    .value_symbol_links(property)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert_eq!(
                    context
                        .diagnostics()
                        .as_slice()
                        .iter()
                        .map(|diagnostic| diagnostic.diagnostic.code())
                        .collect::<Vec<_>>(),
                    code.into_iter().collect::<Vec<_>>(),
                );
                if code.is_some() {
                    let diagnostic = &context.diagnostics().as_slice()[0];
                    assert_eq!(diagnostic.node, Some(name));
                    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
                }
                assert_eq!(context.get_type_at_location(access).unwrap(), expected_type);
                assert_eq!(context.get_type_at_location(name).unwrap(), expected_type);
                assert_eq!(
                    context
                        .store()
                        .symbol_node_links(access)
                        .and_then(|links| links.resolved_symbol),
                    Some(property),
                );
                let warm = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                );
                context.recheck_source_file(file).unwrap();
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    warm,
                );
                assert_eq!(context.diagnostics().len(), usize::from(code.is_some()));
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Instance and static cases share the source and cache checks.
fn inherited_field_visibility_uses_the_declaring_class_for_instance_and_static_reads() {
    for (visibility, code, message) in [
        ("public", None, ""),
        (
            "private",
            Some(2341),
            "Property 'value' is private and only accessible within class 'Base'.",
        ),
        (
            "protected",
            Some(2445),
            "Property 'value' is protected and only accessible within class 'Base' and its subclasses.",
        ),
    ] {
        for static_side in [false, true] {
            let static_modifier = if static_side { "static" } else { "" };
            let receiver = if static_side { "Derived" } else { "model" };
            let parsed = parse_source_file(&format!(
                "class Base {{ {visibility} {static_modifier} value = 1; }} \
                 class Derived extends Base {{}} \
                 const model = new Derived(); const copy = {receiver}.value;",
            ));
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(4_204);
            let mut context = context(
                &parsed,
                file,
                IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: true,
                },
            );
            let (access, name) = value_access(&parsed, file);
            context.check_source_file(file).unwrap();
            assert_eq!(
                context
                    .diagnostics()
                    .as_slice()
                    .iter()
                    .map(|diagnostic| diagnostic.diagnostic.code())
                    .collect::<Vec<_>>(),
                code.into_iter().collect::<Vec<_>>(),
            );
            if code.is_some() {
                assert_eq!(context.diagnostics().as_slice()[0].node, Some(name));
                assert_eq!(
                    context.diagnostics().as_slice()[0]
                        .diagnostic
                        .render()
                        .unwrap(),
                    message,
                );
            }
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(context.get_type_at_location(access).unwrap(), number);
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                ),
                warm,
            );
        }
    }
}

#[test]
fn invalid_visibility_overrides_stay_unsupported_before_class_publication() {
    for static_modifier in ["", "static"] {
        for (base_visibility, derived_visibility) in
            [("private", "public"), ("public", "protected")]
        {
            let parsed = parse_source_file(&format!(
                "class Base {{ {base_visibility} {static_modifier} value = 1; }} \
                 class Derived extends Base {{ {derived_visibility} {static_modifier} value = 2; }}",
            ));
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(4_205);
            let mut context = context(&parsed, file, IntrinsicBootstrapOptions::default());
            let cold = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_)),
            ));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
            );
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each option proves source checking, type identity, and warm replay.
fn optional_primitive_constructor_parameters_keep_annotation_and_value_types() {
    for (strict_null_checks, exact_optional_property_types) in
        [(false, false), (true, false), (true, true)]
    {
        for (annotation, argument) in [
            ("number", Some("2")),
            ("string", Some("'ready'")),
            ("boolean", Some("true")),
            ("any", Some("true")),
            ("unknown", Some("true")),
            ("bigint", None),
            ("symbol", None),
            ("object", None),
            ("void", None),
            ("undefined", None),
            ("never", None),
        ] {
            let supplied =
                argument.map_or_else(String::new, |argument| format!("new Model({argument});"));
            let source = format!(
                "class Model {{ constructor(public value?: {annotation}) {{}} }} new Model(); {supplied}",
            );
            let parsed = parse_source_file(&source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(4_200);
            let mut context = context(
                &parsed,
                file,
                IntrinsicBootstrapOptions {
                    strict_null_checks,
                    exact_optional_property_types,
                },
            );
            let owner = class_symbol(&parsed, file, &context, "Model");

            context.check_source_file(file).unwrap();

            let members = context.get_nongeneric_class_members(owner).unwrap();
            let store = context.store();
            let signature = store
                .signature(members.default_construct_signature())
                .unwrap();
            let [local] = signature.parameters() else {
                panic!("the constructor must keep one local parameter")
            };
            assert_eq!(signature.min_argument_count(), 0);
            let parameter = store.symbol(*local).unwrap().value_declaration().unwrap();
            let NodeData::ParameterDeclaration(data) =
                &parsed.arena.get(parameter.node).unwrap().data
            else {
                panic!("the local symbol must retain its source parameter")
            };
            let annotation_node = NodeRef::new(parsed.arena.id(), file, data.type_.unwrap());
            let annotation_type = store
                .type_node_links(annotation_node)
                .unwrap()
                .resolved_type
                .unwrap();
            let value_type = store
                .value_symbol_links(*local)
                .unwrap()
                .resolved_type
                .unwrap();
            let [property] = members.declared_instance_properties() else {
                panic!("the parameter property must retain one member symbol")
            };
            assert_ne!(local, property);
            assert_eq!(
                store.symbol(*property).unwrap().flags(),
                SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL
            );
            assert_eq!(
                store.value_symbol_links(*property),
                store.value_symbol_links(*local)
            );
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            if !strict_null_checks || matches!(annotation, "any" | "unknown") {
                assert_eq!(value_type, annotation_type, "{source}");
            } else if matches!(annotation, "undefined" | "never") {
                assert_eq!(value_type, bootstrap.undefined_type, "{source}");
            } else {
                let TypeData::Union(union) = store.type_payload(value_type).unwrap().data() else {
                    panic!("{annotation} must include undefined when optional")
                };
                let mut expected = if annotation == "boolean" {
                    vec![bootstrap.regular_false_type, bootstrap.regular_true_type]
                } else {
                    vec![annotation_type]
                };
                expected.push(bootstrap.undefined_type);
                expected.sort_unstable();
                assert_eq!(union.union.types, expected, "{source}");
                assert!(!union.union.types.contains(&bootstrap.missing_type));
            }
            for construction in constructions(&parsed, file) {
                assert_eq!(
                    store.type_node_links(construction),
                    Some(&TypeNodeLinks {
                        resolved_type: Some(members.shells().instance_type()),
                        ..TypeNodeLinks::default()
                    })
                );
                assert_eq!(
                    store
                        .signature_links(construction)
                        .unwrap()
                        .resolved_signature
                        .signature(),
                    Some(members.default_construct_signature())
                );
            }
            assert!(context.diagnostics().is_empty(), "{source}");
            let warm = (store.type_len(), store.signature_len(), store.symbol_len());

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len()
                ),
                warm,
                "{source}"
            );
            assert!(context.diagnostics().is_empty(), "{source}");
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The source calls and relation share the same private member identities.
fn defaulted_constructor_properties_preserve_visibility_and_local_identity() {
    for modifiers in [
        "public",
        "protected",
        "private",
        "public readonly",
        "protected readonly",
        "private readonly",
    ] {
        let source = format!(
            concat!(
                "class First {{ constructor({0} value: number = 1) {{}} }} ",
                "class Second {{ constructor({0} value: number = 1) {{}} }} ",
                "new First(); new First(2); new Second();",
            ),
            modifiers
        );
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let file = FileId::new(4_201);
        let mut context = context(
            &parsed,
            file,
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
        );
        let first = class_symbol(&parsed, file, &context, "First");
        let second = class_symbol(&parsed, file, &context, "Second");

        context.check_source_file(file).unwrap();

        let first_members = context.get_nongeneric_class_members(first).unwrap();
        let second_members = context.get_nongeneric_class_members(second).unwrap();
        for (owner, members) in [(first, &first_members), (second, &second_members)] {
            let store = context.store();
            let signature = store
                .signature(members.default_construct_signature())
                .unwrap();
            let [local] = signature.parameters() else {
                panic!("the constructor must keep one local parameter")
            };
            let [property] = members.declared_instance_properties() else {
                panic!("the constructor must keep one parameter property")
            };
            assert_eq!(signature.min_argument_count(), 0);
            assert_ne!(local, property);
            assert_eq!(store.symbol(*property).unwrap().parent(), Some(owner));
            assert_eq!(
                store.symbol(*property).unwrap().check_flags(),
                if modifiers.contains("readonly") {
                    CheckFlags::READONLY
                } else {
                    CheckFlags::NONE
                }
            );
            assert_eq!(
                store.value_symbol_links(*local).unwrap().resolved_type,
                Some(store.intrinsic_bootstrap().unwrap().number_type)
            );
            assert_eq!(
                store.value_symbol_links(*property),
                store.value_symbol_links(*local)
            );
        }
        let first_type = first_members.shells().instance_type();
        let second_type = second_members.shells().instance_type();
        let public = modifiers.starts_with("public");
        assert_eq!(
            context.is_type_assignable_to(first_type, second_type),
            Ok(public),
            "{modifiers}"
        );
        assert_eq!(
            context.is_type_assignable_to(second_type, first_type),
            Ok(public),
            "{modifiers}"
        );
        assert!(context.diagnostics().is_empty(), "{source}");
        let warm = (context.store().type_len(), context.store().signature_len());

        context.recheck_source_file(file).unwrap();

        assert_eq!(
            (context.store().type_len(), context.store().signature_len()),
            warm,
            "{source}"
        );
    }
}

#[test]
fn unsupported_constructor_parameter_types_and_arguments_leave_caches_cold() {
    for source in [
        "class Date {} class Model { constructor(value?: Date) {} } new Model();",
        "class Model { constructor(value?: bigint) {} } new Model(1n);",
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(4_202);
        let mut context = context(
            &parsed,
            file,
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
        );
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        );

        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_))
            ),
            "{source}"
        );

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len()
            ),
            cold,
            "{source}"
        );
        for construction in constructions(&parsed, file) {
            assert!(context.store().type_node_links(construction).is_none());
            assert!(context.store().signature_links(construction).is_none());
        }
        assert!(context.diagnostics().is_empty());
    }
}
