use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    SourceCheckError, TypeData, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::TypeCacheState,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Model {\n",
    "  readonly value?: string;\n",
    "  definite!: number;\n",
    "  static readonly count: number;\n",
    "}\n",
);

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    checker_context_with_module_state(parsed, file, CanonicalModuleState::Script)
}

fn checker_context_with_module_state(
    parsed: &ParseResult,
    file: FileId,
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'_> {
    checker_context_with_options(
        parsed,
        file,
        module_state,
        CanonicalCheckerOptions::default(),
    )
}

fn checker_context_with_options(
    parsed: &ParseResult,
    file: FileId,
    module_state: CanonicalModuleState,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-members.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module_state,
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

fn strict_property_options() -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            ..IntrinsicBootstrapOptions::default()
        },
        strict_property_initialization: true,
        ..CanonicalCheckerOptions::default()
    }
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

fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn type_alias_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn property_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_node, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(property.name)?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then(|| {
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    property.type_.expect("fixture properties are annotated"),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn source_check_materializes_class_members_and_accepts_unmarked_static_fields() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let symbol = class_symbol(&parsed, file, &context, "Model");

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(symbol).unwrap();
    assert_eq!(members.instance_properties().len(), 2);
    assert_eq!(members.static_properties().len(), 1);
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().len(),
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(symbol).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().len(),
            context
                .source_file(file)
                .and_then(|source| context.store().source_file_links(source))
                .is_some_and(|links| links.type_checked),
        ),
        warm
    );
}

#[test]
fn paired_class_accessors_share_the_getter_type_and_infer_setter_parameter() {
    let parsed =
        parse_source_file("class Model { get value(): number { return 1; } set value(next) {} }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(90);
    let mut context = checker_context(&parsed, file);
    let owner = class_symbol(&parsed, file, &context, "Model");

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let [accessor] = members.instance_properties() else {
        panic!("getter and setter must share one class member")
    };
    let accessor = *accessor;
    let symbol = context.store().symbol(accessor).unwrap();
    assert_eq!(
        symbol.flags(),
        SymbolFlags::GET_ACCESSOR | SymbolFlags::SET_ACCESSOR
    );
    assert_eq!(symbol.declarations().unwrap().len(), 2);
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        context
            .store()
            .value_symbol_links(accessor)
            .and_then(|links| links.resolved_type),
        Some(number),
    );

    let setter_parameter = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(parameter.name)?.data else {
                return None;
            };
            (name.text == "next").then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let setter_symbol = context
        .file(file)
        .unwrap()
        .1
        .symbol(setter_parameter)
        .unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(setter_symbol)
            .and_then(|links| links.resolved_type),
        Some(number),
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
fn supported_classes_execute_at_their_lexical_statement_positions() {
    let parsed = parse_source_file(concat!(
        "class First { value?: string; }\n",
        "type Between = { marker: string };\n",
        "class Second { value!: number; static count: number; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let first = class_symbol(&parsed, file, &context, "First");
    let between = type_alias_symbol(&parsed, file, &context, "Between");
    let second = class_symbol(&parsed, file, &context, "Second");

    context.check_source_file(file).unwrap();

    let first = context.get_nongeneric_class_members(first).unwrap();
    let between = context
        .store()
        .type_alias_links(between)
        .and_then(|links| links.declared_type)
        .expect("the intervening type alias must be materialized");
    let second = context.get_nongeneric_class_members(second).unwrap();
    assert!(first.shells().value_type().get() < between.get());
    assert!(between.get() < second.shells().instance_type().get());
    assert!(first.default_construct_signature().get() < second.default_construct_signature().get());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn loose_options_admit_bare_instance_fields_and_replay_without_growth() {
    let parsed = parse_source_file(concat!(
        "class Loose {\n",
        "  bare: string;\n",
        "  optional?: number;\n",
        "  definite!: boolean;\n",
        "  static count: number;\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    for (index, options) in [
        CanonicalCheckerOptions::default(),
        CanonicalCheckerOptions {
            strict_property_initialization: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    ]
    .into_iter()
    .enumerate()
    {
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context =
            checker_context_with_options(&parsed, file, CanonicalModuleState::Script, options);
        let symbol = class_symbol(&parsed, file, &context, "Loose");

        context.check_source_file(file).unwrap();

        let members = context.get_nongeneric_class_members(symbol).unwrap();
        assert_eq!(members.instance_properties().len(), 3);
        assert_eq!(members.static_properties().len(), 1);
        assert!(is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            members.clone(),
        );

        context.recheck_source_file(file).unwrap();
        let replayed = context.get_nongeneric_class_members(symbol).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                replayed,
            ),
            warm
        );
        assert!(is_type_checked(&context, file));
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn strict_property_options_report_later_unsafe_field_without_rejecting_classes() {
    let parsed = parse_source_file(concat!(
        "class Early { value?: string; }\n",
        "class Later { value: string; static count: number; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );
    let early = class_symbol(&parsed, file, &context, "Early");
    let later_symbol = class_symbol(&parsed, file, &context, "Later");

    context.check_source_file(file).unwrap();

    for symbol in [early, later_symbol] {
        assert!(context.store().declared_type_links(symbol).is_some());
        assert!(context.store().value_symbol_links(symbol).is_some());
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one strict property initialization diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2564);
    assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Property 'value' has no initializer and is not definitely assigned in the constructor."
    );
    let NodeData::Identifier(name) = &parsed
        .arena
        .get(
            diagnostic
                .node
                .expect("field diagnostic has an anchor")
                .node,
        )
        .unwrap()
        .data
    else {
        panic!("field diagnostic must point to its name")
    };
    assert_eq!(name.text, "value");
    assert!(is_type_checked(&context, file));

    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics().len(), 1);
}

#[test]
fn numeric_class_field_initializers_infer_number_and_avoid_ts2564() {
    let parsed = parse_source_file("class Model { value = 1; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(98);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );
    let owner = class_symbol(&parsed, file, &context, "Model");
    let initializer = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            property
                .initializer
                .map(|node| NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let [property] = members.instance_properties() else {
        panic!("expected one initialized numeric field")
    };
    assert_eq!(
        context
            .type_to_string(
                context
                    .store()
                    .value_symbol_links(*property)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
            )
            .unwrap(),
        "number",
    );
    assert_eq!(
        context
            .type_to_string(
                context
                    .store()
                    .type_node_links(initializer)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
            )
            .unwrap(),
        "1",
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn string_class_fields_preserve_inferred_and_readonly_types_across_source_replay() {
    let parsed = parse_source_file(concat!(
        "class Z { public x = \"\"; }\n",
        "class Model {\n",
        "  label: string = 'ready';\n",
        "  readonly exact = 'fixed';\n",
        "  static shared = 'shared';\n",
        "  static readonly constant = 'constant';\n",
        "}\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(101);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    for (class_name, property_name, value, static_field, readonly) in [
        ("Z", "x", "", false, false),
        ("Model", "label", "ready", false, false),
        ("Model", "exact", "fixed", false, true),
        ("Model", "shared", "shared", true, false),
        ("Model", "constant", "constant", true, true),
    ] {
        let owner = class_symbol(&parsed, file, &context, class_name);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let table = if static_field {
            Some(members.static_members())
        } else {
            members.instance_members()
        };
        let symbol = table
            .and_then(|table| context.store().symbol_table(table))
            .and_then(|table| table.get_source(property_name))
            .expect("the class member table retains the initialized string field");
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = if readonly {
            bootstrap.cached_string_literal_type(value).unwrap()
        } else {
            bootstrap.string_type
        };
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(expected),
            "{class_name}.{property_name}",
        );
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::PropertyDeclaration(property) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                    return None;
                };
                (name.text == property_name)
                    .then_some(property.initializer?)
                    .map(|node| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let initializer_type = context
            .store()
            .type_node_links(initializer)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            context
                .store()
                .type_payload(initializer_type)
                .unwrap()
                .flags(),
            TypeFlags::STRING_LITERAL,
            "{class_name}.{property_name}",
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn annotated_numeric_class_fields_preserve_annotation_and_literal_caches() {
    let parsed = parse_source_file("class Model { value: number = 1; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(99);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );
    let owner = class_symbol(&parsed, file, &context, "Model");
    let (annotation, initializer) = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), file, property.type_?),
                NodeRef::new(parsed.arena.id(), file, property.initializer?),
            ))
        })
        .unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let [property] = members.instance_properties() else {
        panic!("expected one annotated numeric field")
    };
    for (type_, expected) in [
        (
            context
                .store()
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type)
                .unwrap(),
            "number",
        ),
        (
            context
                .store()
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type)
                .unwrap(),
            "number",
        ),
        (
            context
                .store()
                .type_node_links(initializer)
                .and_then(|links| links.resolved_type)
                .unwrap(),
            "1",
        ),
    ] {
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
    }

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn class_field_initializers_cannot_capture_constructor_parameters() {
    let source = concat!(
        "const value = 1;\n",
        "class Model {\n",
        "  property = value;\n",
        "  constructor(value: string) {}\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(100);
    let mut context = checker_context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("constructor-parameter capture must report one TS2301 diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2301);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Initializer of instance member variable 'property' cannot reference identifier 'value' declared in the constructor."
    );
    let range = parsed
        .arena
        .get(diagnostic.node.unwrap().node)
        .unwrap()
        .range;
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "value",
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
fn later_unannotated_variable_keeps_classes_and_field_diagnostics_cold_across_retries() {
    let parsed = parse_source_file(concat!(
        "class Loose { bare: string; optional?: number; static count: number; }\n",
        "var missing;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    for (index, options) in [
        CanonicalCheckerOptions::default(),
        strict_property_options(),
    ]
    .into_iter()
    .enumerate()
    {
        let file = FileId::new(13 + u32::try_from(index).unwrap());
        let mut context =
            checker_context_with_options(&parsed, file, CanonicalModuleState::Script, options);
        let class = class_symbol(&parsed, file, &context, "Loose");
        let missing = variable_declaration(&parsed, file, "missing");
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );

        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::MissingVariableInitializer(missing)
                ))
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().relation_state_snapshot(),
                ),
                cold
            );
            assert!(context.store().declared_type_links(class).is_none());
            assert!(context.store().value_symbol_links(class).is_none());
            assert!(!is_type_checked(&context, file));
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One fixture verifies ambient class and method identities.
fn ambient_class_methods_preserve_parameter_identities_and_replay_warm() {
    let source = concat!(
        "declare class Point { ",
        "add(dx: number, dy: number): void; ",
        "label(): string; ",
        "value: number; ",
        "}",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(71);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::Script,
        strict_property_options(),
    );
    let owner = class_symbol(&parsed, file, &context, "Point");
    let declaration = class_declaration(&parsed, file, "Point");
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("Point must retain its class declaration")
    };
    let method = NodeRef::new(parsed.arena.id(), file, class.members.nodes[0]);
    let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).unwrap().data
    else {
        panic!("Point.add must retain its method declaration")
    };
    let parameter_declarations = method_data
        .parameters
        .nodes
        .iter()
        .map(|parameter| NodeRef::new(parsed.arena.id(), file, *parameter))
        .collect::<Vec<_>>();
    let parameter_symbols = parameter_declarations
        .iter()
        .map(|parameter| context.file(file).unwrap().1.symbol(*parameter).unwrap())
        .collect::<Vec<_>>();

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let names = members
        .instance_properties()
        .iter()
        .map(|symbol| {
            context
                .store()
                .symbol(*symbol)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["add", "label", "value"]);
    assert!(context.diagnostics().is_empty());

    let add = members.instance_properties()[0];
    let add_type = context
        .store()
        .value_symbol_links(add)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let TypeData::Object(callable) = context.store().type_payload(add_type).unwrap().data() else {
        panic!("Point.add must retain one callable object")
    };
    let [signature] = callable.structured.signatures.as_deref().unwrap() else {
        panic!("Point.add must retain exactly one signature")
    };
    let signature = context.store().signature(*signature).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(signature.flags(), SignatureFlags::NONE);
    assert_eq!(signature.declaration(), Some(method));
    assert_eq!(signature.parameters(), parameter_symbols.as_slice());
    assert_eq!(signature.min_argument_count(), 2);
    assert_eq!(signature.resolved_return_type(), Some(bootstrap.void_type));
    for symbol in parameter_symbols {
        assert_eq!(
            context.store().value_symbol_links(symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(bootstrap.number_type),
                ..ValueSymbolLinks::default()
            }),
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn exported_ambient_classes_publish_their_existing_local_alias() {
    let parsed = parse_source_file(concat!(
        "export declare class Point { ",
        "readonly value: number; ",
        "getValue(): number; ",
        "}",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(72);
    let mut context = checker_context_with_options(
        &parsed,
        file,
        CanonicalModuleState::External,
        strict_property_options(),
    );
    let declaration = class_declaration(&parsed, file, "Point");
    let bound = context.file(file).unwrap().1;
    let owner = bound.symbol(declaration).unwrap();
    let local = bound.local_symbol(declaration).unwrap();
    assert_ne!(owner, local);

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let expected = ValueSymbolLinks {
        resolved_type: Some(members.shells().value_type()),
        ..ValueSymbolLinks::default()
    };
    assert_eq!(context.store().value_symbol_links(owner), Some(&expected));
    assert_eq!(context.store().value_symbol_links(local), Some(&expected));
    assert_eq!(members.instance_properties().len(), 2);
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn exported_ambient_declaration_file_private_fields_preserve_implicit_any() {
    let parsed = parse_source_file("export declare class C {\n  private p;\n}\n");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(82);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/node_modules/pkg/index.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        strict_property_options(),
    )
    .unwrap();
    let declaration = class_declaration(&parsed, file, "C");
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the package declaration must retain its class")
    };
    let field = NodeRef::new(parsed.arena.id(), file, class.members.nodes[0]);
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(field.node).unwrap().data
    else {
        panic!("the package class must retain its private field")
    };
    let name = NodeRef::new(parsed.arena.id(), file, property.name);
    let bound = context.file(file).unwrap().1;
    let owner = bound.symbol(declaration).unwrap();
    let local = bound.local_symbol(declaration).unwrap();
    let private = bound.symbol(field).unwrap();

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(owner).unwrap();
    assert_eq!(members.instance_properties(), &[private]);
    assert_eq!(
        context.store().symbol(private).unwrap().name().as_utf8(),
        Some("p")
    );
    assert_eq!(
        context.store().value_symbol_links(private),
        Some(&ValueSymbolLinks {
            resolved_type: Some(context.store().intrinsic_bootstrap().unwrap().any_type),
            ..ValueSymbolLinks::default()
        }),
    );
    assert!(context.store().type_node_links(name).is_none());
    let class_value = ValueSymbolLinks {
        resolved_type: Some(members.shells().value_type()),
        ..ValueSymbolLinks::default()
    };
    assert_eq!(
        context.store().value_symbol_links(owner),
        Some(&class_value)
    );
    assert_eq!(
        context.store().value_symbol_links(local),
        Some(&class_value)
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn separate_package_declarations_preserve_distinct_private_field_symbols() {
    let first = parse_source_file("export declare class C { private p; }");
    let second = parse_source_file("export declare class C { private p; }");
    assert!(first.diagnostics.is_empty(), "{:?}", first.diagnostics);
    assert!(second.diagnostics.is_empty(), "{:?}", second.diagnostics);
    let first_file = FileId::new(85);
    let second_file = FileId::new(86);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path) in [
        (&first, first_file, "\"/node_modules/pkg/index.d.ts\""),
        (
            &second,
            second_file,
            "\"/node_modules/pkg/dist/index.d.ts\"",
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (parsed, file) in [(&first, first_file), (&second, second_file)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(first_file, &first.arena), (second_file, &second.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(first_file).unwrap();
    context.check_source_file(second_file).unwrap();

    let first_owner = class_symbol(&first, first_file, &context, "C");
    let second_owner = class_symbol(&second, second_file, &context, "C");
    assert_ne!(first_owner, second_owner);
    let first_members = context.get_nongeneric_class_members(first_owner).unwrap();
    let second_members = context.get_nongeneric_class_members(second_owner).unwrap();
    let first_private = first_members.instance_properties()[0];
    let second_private = second_members.instance_properties()[0];
    assert_ne!(first_private, second_private);
    let any = context.store().intrinsic_bootstrap().unwrap().any_type;
    for (owner, private) in [(first_owner, first_private), (second_owner, second_private)] {
        assert_eq!(
            context.store().symbol(private).unwrap().parent(),
            Some(owner)
        );
        assert_eq!(
            context.store().value_symbol_links(private),
            Some(&ValueSymbolLinks {
                resolved_type: Some(any),
                ..ValueSymbolLinks::default()
            }),
        );
    }
    assert!(context.diagnostics().is_empty());
}

#[test]
fn unannotated_non_private_and_non_ambient_fields_remain_unsupported() {
    for (index, source) in ["declare class C { p; }", "class C { private p; }"]
        .into_iter()
        .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(83 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "C");

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(_)
            ))
        ));
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn ambient_keyword_visibility_fields_keep_their_declared_type() {
    for (visibility, code) in [("private", 2341), ("protected", 2445)] {
        let parsed = parse_source_file(&format!(
            "declare class Model {{ {visibility} value: number; }} \
             declare const instance: Model; const result = instance.value;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(85);
        let mut context = checker_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");

        context.check_source_file(file).unwrap();

        let members = context.get_nongeneric_class_members(owner).unwrap();
        let [field] = members.instance_properties() else {
            panic!("the class must retain its one declared field")
        };
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context.store().symbol(*field).unwrap().parent(),
            Some(owner)
        );
        assert_eq!(
            context.store().value_symbol_links(*field),
            Some(&ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            }),
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the field read must report its visibility error")
        };
        assert_eq!(diagnostic.diagnostic.code(), code);

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.diagnostics().clone(),
            ),
            warm,
        );
    }
}

#[test]
fn unsupported_ambient_class_shapes_leave_class_publication_cold() {
    let cases = [
        ("declare class Generic<T extends string> {}", "Generic"),
        (
            concat!(
                "declare class Overloaded { ",
                "value(input: string): void; ",
                "value(input: number): void; ",
                "}",
            ),
            "Overloaded",
        ),
        (
            "declare class Executable { value(): void {} }",
            "Executable",
        ),
    ];

    for (index, (source, name)) in cases.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(73 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, name);
        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );

        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Class(_)
                ))
            ),
            "{source}",
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
            ),
            cold,
            "{source}",
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
    }
}

struct ExportedClassIdentities {
    owner: SemanticSymbolId,
    local: SemanticSymbolId,
    field: SemanticSymbolId,
    annotation: NodeRef,
}

fn assert_cold_exported_class_identities(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
) -> ExportedClassIdentities {
    let declaration = class_declaration(parsed, file, "Exported");
    let bound = context.file(file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let locals = bound.locals(bound.source_file()).unwrap();
    let owner = context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap();
    let local = context
        .store()
        .get_merged_symbol(bound.local_symbol(declaration).unwrap())
        .unwrap();
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the exported declaration must remain a class")
    };
    let field_declaration = NodeRef::new(parsed.arena.id(), file, class.members.nodes[0]);
    let field = bound.symbol(field_declaration).unwrap();
    let annotation = property_type_node(parsed, file, "value");

    assert_ne!(owner, local);
    assert_eq!(
        context.store().symbol(owner).unwrap().parent(),
        Some(module)
    );
    assert_eq!(
        context.store().symbol(local).unwrap().export_symbol(),
        Some(owner),
    );
    assert_eq!(
        context.store().symbol(local).unwrap().flags(),
        SymbolFlags::EXPORT_VALUE,
    );
    assert_eq!(
        context
            .store()
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| context.store().symbol_table(exports))
            .and_then(|exports| exports.get_source("Exported")),
        Some(owner),
    );
    assert_eq!(
        context
            .store()
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Exported")),
        Some(local),
    );
    for symbol in [owner, local] {
        assert!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }
    assert!(
        context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    assert!(!is_type_checked(context, file));

    ExportedClassIdentities {
        owner,
        local,
        field,
        annotation,
    }
}

fn assert_published_exported_class(
    context: &mut CanonicalCheckerContext<'_>,
    file: FileId,
    identities: &ExportedClassIdentities,
) -> (ClassMembers, ValueSymbolLinks) {
    let members = context
        .get_nongeneric_class_members(identities.owner)
        .unwrap();
    let instance = members.shells().instance_type();
    let value = members.shells().value_type();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let class_value = ValueSymbolLinks {
        resolved_type: Some(value),
        ..ValueSymbolLinks::default()
    };
    assert_eq!(members.declared_instance_properties(), &[identities.field]);
    assert!(members.declared_static_properties().is_empty());
    assert_eq!(
        context
            .store()
            .declared_type_links(identities.owner)
            .and_then(|links| links.declared_type),
        Some(instance),
    );
    assert!(
        context
            .store()
            .declared_type_links(identities.local)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    assert_eq!(
        context.store().value_symbol_links(identities.owner),
        Some(&class_value)
    );
    assert_eq!(
        context.store().value_symbol_links(identities.local),
        Some(&class_value)
    );
    assert_eq!(
        context.store().symbol(identities.field).unwrap().flags(),
        SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
    );
    assert_eq!(
        context.store().symbol(identities.field).unwrap().parent(),
        Some(identities.owner),
    );
    assert_eq!(
        context.store().value_symbol_links(identities.field),
        Some(&ValueSymbolLinks {
            resolved_type: Some(string),
            ..ValueSymbolLinks::default()
        }),
    );
    assert_eq!(
        context.store().type_node_links(identities.annotation),
        Some(&TypeNodeLinks {
            resolved_type: Some(string),
            ..TypeNodeLinks::default()
        }),
    );
    assert_eq!(
        context
            .store()
            .symbol_table(members.instance_members().unwrap())
            .and_then(|members| members.get_source("value")),
        Some(identities.field),
    );
    assert!(is_type_checked(context, file));
    assert!(context.diagnostics().is_empty());

    (members, class_value)
}

#[test]
fn exported_class_publishes_owner_local_alias_and_optional_member_once() {
    let parsed = parse_source_file("export class Exported { value?: string; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context =
        checker_context_with_module_state(&parsed, file, CanonicalModuleState::External);
    let identities = assert_cold_exported_class_identities(&parsed, file, &context);

    context.check_source_file(file).unwrap();

    let (members, class_value) = assert_published_exported_class(&mut context, file, &identities);
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context
            .get_nongeneric_class_members(identities.owner)
            .unwrap(),
        members,
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.diagnostics().clone(),
        ),
        warm,
    );
    assert_eq!(
        context.store().value_symbol_links(identities.owner),
        Some(&class_value)
    );
    assert_eq!(
        context.store().value_symbol_links(identities.local),
        Some(&class_value)
    );
    assert!(is_type_checked(&context, file));
}

#[test]
fn anonymous_decorated_class_reports_grammar_without_publishing_class_types() {
    let parsed = parse_source_file("class {\n  @x\n  m() {}\n};");
    let file = FileId::new(0);
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("fixture has one anonymous class declaration");
    let mut context = checker_context(&parsed, file);
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        before
    );
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].diagnostic.code(), 1211);
    assert_eq!(diagnostics[0].node, Some(declaration));
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "A class declaration without the 'default' modifier must have a name.",
    );
    assert_eq!(diagnostics[1].diagnostic.code(), 2304);
    assert_eq!(
        diagnostics[1].diagnostic.render().unwrap(),
        "Cannot find name 'x'.",
    );
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    );

    let warm = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &warm);
}

#[test]
#[allow(clippy::too_many_lines)] // Class values, instances, and constructors share one identity.
fn public_class_member_query_materializes_both_sides_and_default_constructor() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = checker_context(&parsed, file);
    let symbol = class_symbol(&parsed, file, &context, "Model");
    let class_record = context.store().symbol(symbol).unwrap();
    let declared_members = class_record.members().unwrap();
    let static_members = class_record.exports().unwrap();
    let counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );

    let members = context.get_nongeneric_class_members(symbol).unwrap();

    assert_eq!(context.store().type_len(), counts.0 + 3);
    assert_eq!(context.store().signature_len(), counts.1 + 1);
    assert_eq!(context.store().symbol_len(), counts.2);
    assert_eq!(
        context.store().symbol_store().symbol_table_len(),
        counts.3 + 1
    );
    assert_ne!(members.instance_members(), Some(declared_members));
    assert_eq!(members.static_members(), static_members);
    assert_eq!(members.instance_properties().len(), 2);
    assert_eq!(members.static_properties().len(), 1);

    let instance_table = context
        .store()
        .symbol_table(members.instance_members().unwrap())
        .unwrap();
    assert_eq!(instance_table.len(), 2);
    assert_eq!(
        instance_table.get_source("value"),
        Some(members.instance_properties()[0])
    );
    assert_eq!(
        instance_table.get_source("definite"),
        Some(members.instance_properties()[1])
    );
    let static_table = context.store().symbol_table(static_members).unwrap();
    assert_eq!(
        static_table.get_source("count"),
        Some(members.static_properties()[0])
    );
    assert_eq!(
        static_table.get_source("prototype"),
        Some(members.prototype())
    );

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string_type = bootstrap.string_type;
    let number_type = bootstrap.number_type;
    let undefined_type = bootstrap.undefined_type;
    let property_expectations = [
        (
            members.instance_properties()[0],
            "value",
            string_type,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
            CheckFlags::READONLY,
        ),
        (
            members.instance_properties()[1],
            "definite",
            number_type,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ),
        (
            members.static_properties()[0],
            "count",
            number_type,
            SymbolFlags::PROPERTY,
            CheckFlags::READONLY,
        ),
    ];
    for (property, name, type_, flags, check_flags) in property_expectations {
        let record = context.store().symbol(property).unwrap();
        assert_eq!(record.flags(), flags);
        assert_eq!(record.check_flags(), check_flags);
        assert_eq!(
            context.store().value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            context
                .store()
                .type_node_links(property_type_node(&parsed, file, name)),
            Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
        );
    }

    let shells = members.shells();
    let instance_record = context
        .store()
        .type_payload(shells.instance_type())
        .unwrap();
    assert_eq!(
        instance_record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Interface(instance) = instance_record.data() else {
        panic!("class instance must use interface storage")
    };
    assert!(instance.base_types_resolved);
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(undefined_type)
    );
    assert_eq!(instance.resolved_base_types, None);
    assert!(instance.declared_members_resolved);
    assert_eq!(instance.declared_members, Some(declared_members));
    assert_eq!(instance.declared_call_signatures, None);
    assert_eq!(instance.declared_construct_signatures, None);
    assert_eq!(instance.declared_index_infos, None);
    assert_eq!(
        instance.reference.object.structured.members,
        members.instance_members()
    );
    assert_eq!(
        instance.reference.object.structured.properties.as_deref(),
        Some(members.instance_properties())
    );
    assert_eq!(instance.reference.object.structured.signatures, None);
    assert_eq!(instance.reference.object.structured.call_signature_count, 0);
    assert_eq!(instance.reference.object.structured.index_infos, None);
    assert_eq!(instance.reference.resolved_type_arguments, Some(Vec::new()));
    let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
    else {
        panic!("class instance owns its self-instantiation")
    };
    assert_eq!(instantiations.len(), 1);

    let value_record = context.store().type_payload(shells.value_type()).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        value_record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Object(value) = value_record.data() else {
        panic!("class value must use object storage")
    };
    assert_eq!(value.structured.members, Some(static_members));
    assert_eq!(
        value.structured.properties.as_deref(),
        Some(&[members.static_properties()[0], members.prototype()][..])
    );
    assert_eq!(value.structured.call_signature_count, 0);
    assert_eq!(
        value.structured.signatures.as_deref(),
        Some(&[members.default_construct_signature()][..])
    );
    assert_eq!(value.structured.index_infos, None);

    let signature = context
        .store()
        .signature(members.default_construct_signature())
        .unwrap();
    assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(signature.declaration(), None);
    assert!(signature.type_parameters().is_empty());
    assert!(signature.parameters().is_empty());
    assert_eq!(signature.this_parameter(), None);
    assert_eq!(
        signature.resolved_return_type(),
        Some(shells.instance_type())
    );
    assert_eq!(signature.resolved_type_predicate(), None);
    assert_eq!(signature.min_argument_count(), 0);
    assert_eq!(signature.resolved_min_argument_count(), -1);
    assert_eq!(signature.target(), None);
    assert_eq!(signature.mapper(), None);
    assert_eq!(signature.isolated_signature_type(), None);
    assert_eq!(signature.composite(), None);

    let warm_counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    assert_eq!(
        context.get_nongeneric_class_members(symbol).unwrap(),
        members
    );
    assert_eq!(context.get_nongeneric_class_shells(symbol).unwrap(), shells);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        warm_counts
    );
    assert!(context.diagnostics().is_empty());
}
