use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, ResolvedSignatureState, SignatureLinks, signatures::SignatureFlags,
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_source_file};

fn checker_context(
    parsed: &ParseResult,
    file: FileId,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-second-wave.ts\""),
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
        options,
    )
    .unwrap()
}

fn class_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name.and_then(|name| parsed.arena.get(name))?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing class {expected}"))
}

fn class_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = class_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn class_constructor(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = class_declaration(parsed, file, expected);
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("class lookup returned a class declaration")
    };
    class
        .members
        .nodes
        .iter()
        .find(|member| {
            parsed
                .arena
                .get(**member)
                .is_some_and(|record| record.kind == SyntaxKind::Constructor)
        })
        .map_or_else(
            || panic!("missing constructor in {expected}"),
            |member| NodeRef::new(parsed.arena.id(), file, *member),
        )
}

fn first_new_expression(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("fixture contains a new expression")
}

#[test]
fn explicit_public_constructor_publishes_its_declaration_signature() {
    let parsed = parse_source_file(concat!(
        "class Model { public constructor() {} value!: string; }\n",
        "const value = new Model();\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_101);
    let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
    let owner = class_symbol(&parsed, file, &context, "Model");
    let constructor = class_constructor(&parsed, file, "Model");
    let construction = first_new_expression(&parsed, file);

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signature = members.default_construct_signature();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.declaration(), Some(constructor));
    assert_eq!(
        record.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    assert_eq!(
        context.store().signature_links(constructor),
        Some(&SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        })
    );
    assert_eq!(
        context
            .store()
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature()),
        Some(signature)
    );
    let declared = context.store().symbol(owner).unwrap().members().unwrap();
    let declared = context.store().symbol_table(declared).unwrap();
    assert!(
        declared
            .get(InternalSymbolName::Constructor.as_ref())
            .is_some()
    );
    let resolved = context
        .store()
        .symbol_table(members.instance_members().unwrap())
        .unwrap();
    assert!(
        resolved
            .get(InternalSymbolName::Constructor.as_ref())
            .is_none()
    );
    assert!(resolved.get_source("value").is_some());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().signature_links(constructor).cloned(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().signature_links(constructor).cloned(),
        ),
        warm
    );
}

#[test]
fn protected_base_constructor_declaration_is_retained_by_subclass_signature() {
    let parsed = parse_source_file(concat!(
        "class Base { protected constructor() {} value!: string; }\n",
        "class Derived extends Base { own!: number; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_102);
    let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let constructor = class_constructor(&parsed, file, "Base");

    context.check_source_file(file).unwrap();

    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    assert_ne!(
        base.default_construct_signature(),
        derived.default_construct_signature()
    );
    assert_eq!(
        context
            .store()
            .signature(base.default_construct_signature())
            .and_then(ts_checker::semantic::signatures::Signature::declaration),
        Some(constructor)
    );
    assert_eq!(
        context
            .store()
            .signature(derived.default_construct_signature())
            .and_then(ts_checker::semantic::signatures::Signature::declaration),
        Some(constructor)
    );
    assert_eq!(
        context.is_type_assignable_to(
            derived.shells().instance_type(),
            base.shells().instance_type(),
        ),
        Ok(true)
    );
    let resolved = context
        .store()
        .symbol_table(derived.instance_members().unwrap())
        .unwrap();
    assert!(resolved.get_source("value").is_some());
    assert!(resolved.get_source("own").is_some());
    assert!(
        resolved
            .get(InternalSymbolName::Constructor.as_ref())
            .is_none()
    );
}

#[test]
fn inaccessible_constructors_report_external_construction_diagnostics() {
    for (index, visibility) in ["private", "protected"].into_iter().enumerate() {
        let source = format!(
            "class Secret {{ {visibility} constructor() {{}} }} const secret = new Secret();"
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_103 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = class_symbol(&parsed, file, &context, "Secret");
        let construction = first_new_expression(&parsed, file);
        let NodeData::NewExpression(expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            unreachable!("the helper selected a new expression")
        };
        let constructor = NodeRef::new(parsed.arena.id(), file, expression.expression);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the inaccessible constructor must produce one diagnostic")
        };
        assert_eq!(
            diagnostic.diagnostic.code(),
            if index == 0 { 2673 } else { 2674 }
        );
        assert_eq!(diagnostic.diagnostic.arguments, ["Secret"]);
        assert_eq!(diagnostic.node, Some(construction));
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor)
                .and_then(|links| links.resolved_symbol),
            Some(owner),
        );
        assert!(context.store().declared_type_links(owner).is_some());
        assert!(context.store().value_symbol_links(owner).is_some());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }
}

#[test]
fn explicit_constructor_keeps_strict_field_initialization_diagnostics() {
    let parsed = parse_source_file("class Model { constructor() {} value: string; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_105);
    let mut context = checker_context(
        &parsed,
        file,
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

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("an empty constructor does not initialize the required field")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2564);
    assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
}

#[test]
#[allow(clippy::too_many_lines)] // Each original input checks cold identity, diagnostics, and replay.
fn constructor_bodies_preserve_class_identities_and_diagnostics() {
    let cases: [(&str, &[u32]); 3] = [
        (
            concat!(
                "class Base { constructor(public value: string) {} } ",
                "class Model extends Base { constructor(value: string) { super(value); } }",
            ),
            &[],
        ),
        ("class Model { constructor() { const value = 1; } }", &[]),
        (
            "class Base {} class Model extends Base { constructor() {} }",
            &[2377],
        ),
    ];
    for (index, (source, expected_codes)) in cases.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_106 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = class_symbol(&parsed, file, &context, "Model");

        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());

        context
            .check_source_file(file)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            expected_codes,
            "{source}",
        );
        for diagnostic in context.diagnostics().as_slice() {
            assert_eq!(
                diagnostic.node,
                Some(class_constructor(&parsed, file, "Model"))
            );
            assert_eq!(
                diagnostic.range_override,
                Some(CanonicalCheckerDiagnosticRange::new(
                    class_constructor(&parsed, file, "Model"),
                    TextRange::new(TextPos::new(41), TextPos::new(52)),
                )),
            );
            assert!(diagnostic.diagnostic.arguments.is_empty());
            assert!(diagnostic.related_information.is_empty());
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Constructors for derived classes must contain a 'super' call.",
            );
        }
        let instance = context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .expect("the checked constructor must retain its class instance");
        let value = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .expect("the checked constructor must retain its class value");
        assert_ne!(instance, value);
        assert_eq!(
            context.store().type_payload(instance).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            context.store().type_payload(value).unwrap().symbol(),
            Some(owner)
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            context
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type,
            Some(instance),
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(value),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.diagnostics().clone(),
            ),
            warm,
            "{source}",
        );
    }
}

#[test]
fn primitive_constructor_parameters_publish_their_required_signature() {
    for (index, (annotation, expected)) in [("string", "string"), ("number", "number")]
        .into_iter()
        .enumerate()
    {
        let source = format!("class Model {{ constructor(value: {annotation}) {{}} }}");
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_120 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = class_symbol(&parsed, file, &context, "Model");
        let constructor = class_constructor(&parsed, file, "Model");

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let members = context.get_nongeneric_class_members(owner).unwrap();
        let signature = context
            .store()
            .signature(members.default_construct_signature())
            .unwrap();
        assert_eq!(signature.declaration(), Some(constructor));
        assert_eq!(signature.min_argument_count(), 1);
        let [parameter] = signature.parameters() else {
            panic!("the constructor must retain its one required parameter")
        };
        let parameter_type = context
            .store()
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(parameter_type).unwrap(), expected);

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }
}

#[test]
fn unsupported_class_grammar_reports_exact_modifier_accessor_and_heritage_errors() {
    let cases: &[(&str, &[(u32, &str)])] = &[
        (
            "class Model { constructor(public static value: number) {} }",
            &[(1090, "static")],
        ),
        (
            "class Model { constructor(private public value: number) {} }",
            &[(1028, "public")],
        ),
        (
            "class Model { in input = 1; out output = 2; }",
            &[(1274, "in"), (1274, "out")],
        ),
        (
            "class Model { set value(input = 0) {} static set value(input = 0) {} }",
            &[(1052, "value"), (1052, "value")],
        ),
        (
            "class First {} class Second {} class Model extends First, Second {}",
            &[(1174, "Second")],
        ),
        (
            "class Model { value: number = 2; accessor value: number = 3; }",
            &[(2300, "value"), (2300, "value")],
        ),
    ];

    for (index, (source, expected)) in cases.iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_130 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let actual = context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| {
                let range = parsed
                    .arena
                    .get(diagnostic.node.unwrap().node)
                    .unwrap()
                    .range;
                (
                    diagnostic.diagnostic.code(),
                    &source[range.start.get() as usize..range.end.get() as usize],
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, *expected, "source: {source}");

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().clone(),
            ),
            warm,
            "source: {source}",
        );
    }
}

#[test]
fn recovered_constructor_diagnostic_underlines_only_its_keyword() {
    let source = "class Model { value = 42; constructor\n}";
    let parsed = parse_source_file(source);
    assert_eq!(parsed.diagnostics.len(), 1);
    assert_eq!(parsed.diagnostics[0].code, Some(1005));
    let file = FileId::new(2_140);
    let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("a recovered constructor must report its missing implementation")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2390);
    let range = diagnostic
        .range_override
        .expect("the constructor keyword needs a precise range")
        .range();
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "constructor",
    );

    let warm = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &warm);
}

#[test]
fn indexed_classes_report_only_uninitialized_private_fields() {
    let source = concat!(
        "class Model {\n",
        "  [key: string]: number;\n",
        "  #missing: boolean;\n",
        "  #ready = false;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_141);
    let mut context = checker_context(
        &parsed,
        file,
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

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the uninitialized private field requires a diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2564);
    assert_eq!(diagnostic.diagnostic.arguments, ["#missing"]);
    let range = parsed
        .arena
        .get(diagnostic.node.unwrap().node)
        .unwrap()
        .range;
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "#missing",
    );

    let warm = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &warm);
}

#[test]
fn recovered_conflict_marker_classes_check_the_live_method_body() {
    let sources = [
        concat!(
            "class Model {\n",
            "  foo() {\n",
            "<<<<<<< ours\n",
            "    a();\n",
            "  }\n",
            "=======\n",
            "    b();\n",
            "  }\n",
            ">>>>>>> theirs\n",
            "  public bar() {}\n",
            "}\n",
        ),
        concat!(
            "class Model {\n",
            "  foo() {\n",
            "<<<<<<< ours\n",
            "    a();\n",
            "  }\n",
            "||||||| base\n",
            "    c();\n",
            "  }\n",
            "=======\n",
            "    b();\n",
            "  }\n",
            ">>>>>>> theirs\n",
            "  public bar() {}\n",
            "}\n",
        ),
    ];

    for (index, source) in sources.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(!parsed.diagnostics.is_empty());
        assert!(
            parsed
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code == Some(1185))
        );
        let file = FileId::new(2_142 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the retained unresolved call should be checked")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2304);
        assert_eq!(diagnostic.diagnostic.arguments, ["a"]);

        let warm = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &warm);
    }
}

#[test]
fn class_method_generic_arity_and_static_name_diagnostics_keep_all_arguments() {
    let cases = [
        (
            "class Model { public run(value: Array) {} }",
            2314,
            "Array",
            vec!["Array<T>", "1", "1"],
        ),
        (
            "class C { static foo: string; bar() { let k = foo; } }",
            2662,
            "foo",
            vec!["foo", "C"],
        ),
    ];

    for (index, (source, code, expected_node, arguments)) in cases.into_iter().enumerate() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let parsed = parse_source_file(source);
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let library_file = FileId::new(2_150 + u32::try_from(index).unwrap());
        let file = FileId::new(2_144 + u32::try_from(index).unwrap());
        let mut binder = CanonicalBinder::new();
        for (input, current, name, declaration, default_library) in [
            (&library, library_file, "\"/project/lib.d.ts\"", true, true),
            (
                &parsed,
                file,
                "\"/project/class-second-wave.ts\"",
                false,
                false,
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    &input.arena,
                    input.source_file,
                    current,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(name),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&input.arena, current)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(library_file, &library.arena), (file, &parsed.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the class must produce exactly one supported grammar diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        let range = parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .range;
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            expected_node,
        );

        let warm = context.diagnostics().clone();
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics(), &warm);
    }
}

#[test]
fn ambient_getter_reports_its_circular_type_annotation_once() {
    let source = "declare class Model { get value(): typeof this.value; }";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_146);
    let mut context = checker_context(
        &parsed,
        file,
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    );

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the circular getter requires one declaration diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2502);
    assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
    let range = parsed
        .arena
        .get(diagnostic.node.unwrap().node)
        .unwrap()
        .range;
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "value",
    );

    let warm = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &warm);
}

#[test]
fn decorated_constructor_parameter_publishes_its_annotated_signature() {
    let parsed = parse_source_file(concat!(
        "declare function decorate(target: any, key: string | symbol | undefined, index: number): void;\n",
        "class Model { constructor(@decorate value: string) {} }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_110);
    let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
    let owner = class_symbol(&parsed, file, &context, "Model");
    let constructor = class_constructor(&parsed, file, "Model");

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signature = context
        .store()
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(signature.declaration(), Some(constructor));
    assert_eq!(signature.parameters().len(), 1);
    assert_eq!(signature.min_argument_count(), 1);
    let parameter = signature.parameters()[0];
    assert_eq!(
        context
            .store()
            .value_symbol_links(parameter)
            .and_then(|links| links.resolved_type),
        Some(context.store().intrinsic_bootstrap().unwrap().string_type),
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn valid_array_method_annotation_keeps_real_target_and_queries() {
    use ts_checker::semantic::TypeData;

    let source = "class Model { public run(value: Array<string>) {} }";
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let parsed = parse_source_file(source);
    let file = FileId::new(2_160);
    let library_file = FileId::new(2_170);
    assert!(parsed.diagnostics.is_empty());
    assert!(library.diagnostics.is_empty());
    let make_context = || {
        let mut binder = CanonicalBinder::new();
        for (input, current, name, declaration, default_library) in [
            (&library, library_file, "\"/project/lib.d.ts\"", true, true),
            (&parsed, file, "\"/project/class-second-wave.ts\"", false, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &input.arena,
                    input.source_file,
                    current,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(name),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder.bind_typescript_declaration_slice(&input.arena, current).unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            [(library_file, &library.arena), (file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    };
    let nodes = parsed.arena.iter().map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node)).collect::<Vec<_>>();
    let method = nodes.iter().copied().find(|node| parsed.arena.get(node.node).unwrap().kind == SyntaxKind::MethodDeclaration).unwrap();
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else { unreachable!() };
    let name = NodeRef::new(method.arena, file, data.name);
    let parameter = NodeRef::new(method.arena, file, data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data else { unreachable!() };
    let parameter_name = NodeRef::new(method.arena, file, data.name);
    let annotation = NodeRef::new(method.arena, file, data.type_.unwrap());
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [store.type_len(), store.symbol_len(), store.signature_len(), store.mapper_len(), store.type_alias_len(), store.index_info_len(), store.symbol_store().symbol_table_len(), store.type_predicate_len()],
            store.relation_state_snapshot(),
            nodes.iter().map(|node| (*node, store.node_links(*node).cloned(), store.type_node_links(*node).cloned(), store.symbol_node_links(*node).cloned(), store.signature_links(*node).cloned())).collect::<Vec<_>>(),
            nodes.iter().filter_map(|node| context.file(file).unwrap().1.symbol(*node)).map(|symbol| (symbol, store.value_symbol_links(symbol).cloned())).collect::<Vec<_>>(),
            store.source_file_links(context.source_file(file).unwrap()).cloned(),
            context.diagnostics().clone(),
        )
    };
    for first in [None, Some(method), Some(name), Some(parameter), Some(parameter_name), Some(annotation)] {
        let mut context = make_context();
        let early = first.map(|node| context.get_type_at_location(node).unwrap());
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let array_type = context.get_type_at_location(annotation).unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        let TypeData::TypeReference(array) = context.store().type_payload(array_type).unwrap().data() else {
            panic!("the valid annotation must retain its canonical Array target")
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(array.resolved_type_arguments.as_deref(), Some(&[string][..]));
        assert_eq!(context.type_to_string(array_type).unwrap(), "string[]");
        let parameter_symbol = context.file(file).unwrap().1.symbol(parameter).unwrap();
        assert_eq!(context.store().value_symbol_links(parameter_symbol).unwrap().resolved_type, Some(array_type));
        assert_eq!(context.get_type_at_location(parameter), Ok(array_type));
        assert_eq!(context.get_type_at_location(parameter_name), Ok(array_type));
        assert_eq!(context.get_symbol_at_location(parameter_name), Ok(Some(parameter_symbol)));
        let callable = context.get_type_at_location(method).unwrap();
        assert_eq!(context.get_type_at_location(name), Ok(callable));
        assert_eq!(context.type_to_string(callable).unwrap(), "(value: string[]) => void");
        let signature = context.store().signature_links(method).unwrap().resolved_signature.signature().unwrap();
        let ts_checker::semantic::TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
            panic!("the callable must retain its declaration signature")
        };
        assert_eq!(
            (object.structured.signatures.as_deref(), object.structured.call_signature_count),
            (Some(&[signature][..]), 1),
        );
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(method));
        assert_eq!(record.parameters(), &[parameter_symbol]);
        assert_eq!(record.min_argument_count(), 1);
        assert!(!record.has_rest_parameter());
        assert_eq!(context.get_return_type_of_signature(signature), Ok(void));
        if let Some(node) = first { assert_eq!(context.get_type_at_location(node), Ok(early.unwrap())); }
        let warm = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_at_location(annotation), Ok(array_type));
            assert_eq!(context.get_type_at_location(parameter), Ok(array_type));
            assert_eq!(context.get_type_at_location(parameter_name), Ok(array_type));
            assert_eq!(context.get_type_at_location(method), Ok(callable));
            assert_eq!(context.get_type_at_location(name), Ok(callable));
            assert_eq!(context.store().signature_links(method).unwrap().resolved_signature.signature(), Some(signature));
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
            assert!(snapshot(&context) == warm);
        }
    }
}

#[test]
fn invalid_array_method_annotation_recovers_and_checks_later_error() {
    let source = concat!(
        "class Model { public run(value: Array) {} }\n",
        "declare const model: Model;\n",
        "model.run(1);\n",
        "const later: string = 1;\n",
    );
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let parsed = parse_source_file(source);
    let file = FileId::new(2_161);
    let library_file = FileId::new(2_171);
    assert!(parsed.diagnostics.is_empty());
    assert!(library.diagnostics.is_empty());
    let make_context = || {
        let mut binder = CanonicalBinder::new();
        for (input, current, name, declaration, default_library) in [
            (&library, library_file, "\"/project/lib.d.ts\"", true, true),
            (&parsed, file, "\"/project/class-second-wave.ts\"", false, false),
        ] {
            binder.bind_source_file_with_facts(
                &input.arena, input.source_file, current,
                CanonicalSourceFileFacts::new_with_default_library(EscapedName::source(name), CanonicalSourceLanguage::TypeScript, declaration, default_library, CanonicalModuleState::Script),
            ).unwrap();
            binder.bind_typescript_declaration_slice(&input.arena, current).unwrap();
        }
        CanonicalCheckerContext::new(binder.finish(), [(library_file, &library.arena), (file, &parsed.arena)].into_iter().collect(), CanonicalCheckerOptions::default()).unwrap()
    };
    let nodes = parsed.arena.iter().map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node)).collect::<Vec<_>>();
    let method = nodes.iter().copied().find(|node| parsed.arena.get(node.node).unwrap().kind == SyntaxKind::MethodDeclaration).unwrap();
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else { unreachable!() };
    let name = NodeRef::new(method.arena, file, data.name);
    let parameter = NodeRef::new(method.arena, file, data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data else { unreachable!() };
    let parameter_name = NodeRef::new(method.arena, file, data.name);
    let annotation = NodeRef::new(method.arena, file, data.type_.unwrap());
    let call = nodes.iter().copied().find(|node| parsed.arena.get(node.node).unwrap().kind == SyntaxKind::CallExpression).unwrap();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [store.type_len(), store.symbol_len(), store.signature_len(), store.mapper_len(), store.type_alias_len(), store.index_info_len(), store.symbol_store().symbol_table_len(), store.type_predicate_len()],
            store.relation_state_snapshot(),
            nodes.iter().map(|node| (*node, store.node_links(*node).cloned(), store.type_node_links(*node).cloned(), store.symbol_node_links(*node).cloned(), store.signature_links(*node).cloned())).collect::<Vec<_>>(),
            nodes.iter().filter_map(|node| context.file(file).unwrap().1.symbol(*node)).map(|symbol| (symbol, store.value_symbol_links(symbol).cloned())).collect::<Vec<_>>(),
            store.source_file_links(context.source_file(file).unwrap()).cloned(), context.diagnostics().clone(),
        )
    };
    for first in [None, Some(method), Some(name), Some(parameter), Some(parameter_name), Some(annotation)] {
        let mut context = make_context();
        let early = first.map(|node| context.get_type_at_location(node).unwrap());
        context.check_source_file(file).unwrap();
        let actual = context.diagnostics().as_slice().iter().map(|diagnostic| {
            let node = diagnostic.node.unwrap();
            let range = diagnostic.range_override.map_or_else(|| parsed.arena.get(node.node).unwrap().range, |range| range.range());
            assert!(diagnostic.related_information.is_empty());
            (diagnostic.diagnostic.code(), range.start.get(), range.end.get(), diagnostic.diagnostic.arguments.iter().map(String::as_str).collect::<Vec<_>>(), diagnostic.diagnostic.render().unwrap())
        }).collect::<Vec<_>>();
        assert_eq!(actual, [
            (2314, 32, 37, vec!["Array<T>", "1", "1"], "Generic type 'Array<T>' requires 1 type argument(s).".to_owned()),
            (2322, 92, 97, vec!["number", "string"], "Type 'number' is not assignable to type 'string'.".to_owned()),
        ]);
        let error = context.store().intrinsic_bootstrap().unwrap().error_type;
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(context.get_type_at_location(annotation), Ok(error));
        assert_eq!(context.get_type_at_location(parameter), Ok(error));
        assert_eq!(context.get_type_at_location(parameter_name), Ok(error));
        let parameter_symbol = context.file(file).unwrap().1.symbol(parameter).unwrap();
        assert_eq!(context.store().value_symbol_links(parameter_symbol).unwrap().resolved_type, Some(error));
        assert_eq!(context.get_symbol_at_location(parameter_name), Ok(Some(parameter_symbol)));
        let callable = context.get_type_at_location(method).unwrap();
        assert_eq!(context.get_type_at_location(name), Ok(callable));
        assert_eq!(context.type_to_string(callable).unwrap(), "(value: any) => void");
        assert_eq!(context.get_type_at_location(call), Ok(void));
        let declaration_signature = context.store().signature_links(method).unwrap().resolved_signature.signature().unwrap();
        let call_signature = context.store().signature_links(call).unwrap().resolved_signature.signature().unwrap();
        let ts_checker::semantic::TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
            panic!("the callable must retain its declaration signature")
        };
        assert_eq!(
            (object.structured.signatures.as_deref(), object.structured.call_signature_count),
            (Some(&[declaration_signature][..]), 1),
        );
        let declaration = context.store().signature(declaration_signature).unwrap();
        let selected = context.store().signature(call_signature).unwrap();
        assert_eq!(declaration.declaration(), Some(method));
        assert_eq!(selected.declaration(), Some(method));
        assert_eq!(declaration.parameters(), &[parameter_symbol]);
        assert_eq!(selected.parameters().len(), 1);
        let selected_parameter = selected.parameters()[0];
        assert_eq!(
            context.store().symbol(selected_parameter).unwrap().declarations(),
            context.store().symbol(parameter_symbol).unwrap().declarations(),
        );
        assert_eq!(
            context.store().symbol(selected_parameter).unwrap().value_declaration(),
            Some(parameter),
        );
        let selected_links = context.store().value_symbol_links(selected_parameter).unwrap();
        assert_eq!(selected_links.resolved_type, Some(error));
        if selected_parameter != parameter_symbol {
            assert_eq!(selected_links.target, Some(parameter_symbol));
            assert_eq!(selected_links.mapper, selected.mapper());
        }
        assert_eq!(declaration.min_argument_count(), 1);
        assert_eq!(selected.min_argument_count(), 1);
        assert!(!declaration.has_rest_parameter());
        assert!(!selected.has_rest_parameter());
        assert_eq!(context.get_return_type_of_signature(declaration_signature), Ok(void));
        assert_eq!(context.get_return_type_of_signature(call_signature), Ok(void));
        if let Some(node) = first { assert_eq!(context.get_type_at_location(node), Ok(early.unwrap())); }
        let warm = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_at_location(annotation), Ok(error));
            assert_eq!(context.get_type_at_location(parameter_name), Ok(error));
            assert_eq!(context.get_type_at_location(method), Ok(callable));
            assert_eq!(context.get_type_at_location(name), Ok(callable));
            assert_eq!(context.get_type_at_location(call), Ok(void));
            assert_eq!(context.store().signature_links(method).unwrap().resolved_signature.signature(), Some(declaration_signature));
            assert_eq!(context.store().signature_links(call).unwrap().resolved_signature.signature(), Some(call_signature));
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
            assert!(snapshot(&context) == warm);
        }
    }
}
