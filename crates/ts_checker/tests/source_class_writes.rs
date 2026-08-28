use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(61_300);

fn context(parsed: &ParseResult, exact: bool) -> CanonicalCheckerContext<'_> {
    context_with_module(parsed, exact, CanonicalModuleState::Script)
}

fn context_with_module(
    parsed: &ParseResult,
    exact: bool,
    module: CanonicalModuleState,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-writes.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module,
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
                exact_optional_property_types: exact,
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name).unwrap().data else {
                return None;
            };
            (name.text == expected)
                .then(|| NodeRef::new(parsed.arena.id(), FILE, variable.initializer.unwrap()))
        })
        .unwrap()
}

fn owner(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn property(context: &CanonicalCheckerContext<'_>, class: &str, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol(owner(context, class))
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source(name))
        .unwrap()
}

#[test]
fn constructor_property_writes_track_types_without_changing_declared_fields() {
    for exact in [false, true] {
        let parsed = parse_source_file(concat!(
            "class Counter { value?: number; constructor() { ",
            "const before = this.value; ",
            "this.value = 1; const first: number = this.value; ",
            "this.value = 2; const second: number = this.value; ",
            "} read() { return this.value; } }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = context(&parsed, exact);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        for (name, expected) in [
            ("before", "number | undefined"),
            ("first", "number"),
            ("second", "number"),
        ] {
            let value = resolved_type(&context, initializer(&parsed, name));
            assert_eq!(context.type_to_string(value).unwrap(), expected, "{name}");
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let field = property(&context, "Counter", "value");
        assert_eq!(
            context
                .store()
                .value_symbol_links(field)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        let method_read = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ReturnStatement(returned) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), FILE, returned.expression?))
            })
            .unwrap();
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, method_read))
                .unwrap(),
            "number | undefined"
        );
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            context
                .store()
                .value_symbol_links(field)
                .unwrap()
                .resolved_type,
            Some(number)
        );
    }
}

#[test]
fn constructor_property_writes_keep_readonly_and_private_field_ownership() {
    for source in [
        "class Model { readonly value: number; constructor() { this.value = 1; this.value = 2; const n: number = this.value; } }",
        "class Model { private value: number; constructor() { this.value = 1; const n: number = this.value; } }",
        "class Model { #value: number; constructor() { this.#value = 1; const n: number = this.#value; } }",
        "class Model { constructor(public readonly value: number) { const n: number = this.value; } }",
        "class Model { constructor(public readonly value: number) { this.value = 2; const n: number = this.value; } }",
        "class Model { constructor(public value: number) { this.value = 2; const n: number = this.value; } }",
        "class Model { value: number; constructor(input: number) { this.value = input; const n: number = this.value; } }",
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = context(&parsed, false);
        context
            .check_source_file(FILE)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            context.diagnostics().is_empty(),
            "{source}: {:?}",
            context.diagnostics()
        );
        let read = initializer(&parsed, "n");
        let field = context
            .store()
            .symbol_node_links(read)
            .unwrap()
            .resolved_symbol
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(resolved_type(&context, read), number);
        assert_eq!(
            context.store().symbol(field).unwrap().parent(),
            Some(owner(&context, "Model"))
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(field)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        if source.contains("readonly") {
            assert!(
                context
                    .store()
                    .symbol(field)
                    .unwrap()
                    .check_flags()
                    .contains(CheckFlags::READONLY)
            );
        }
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn exported_constructor_parameter_property_writes_keep_member_identity() {
    let parsed = parse_source_file(concat!(
        "export class Model { constructor(public readonly value: number) { ",
        "this.value = 2; const n: number = this.value; } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context_with_module(&parsed, false, CanonicalModuleState::External);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let read = initializer(&parsed, "n");
    let field = context
        .store()
        .symbol_node_links(read)
        .unwrap()
        .resolved_symbol
        .unwrap();
    let field_record = context.store().symbol(field).unwrap();
    assert!(field_record.check_flags().contains(CheckFlags::READONLY));
    let class = context
        .store()
        .symbol(field_record.parent().unwrap())
        .unwrap();
    let declaration = class.value_declaration().unwrap();
    assert!(
        matches!(parsed.arena.get(declaration.node).map(|record| &record.data),
        Some(NodeData::ClassDeclaration(data)) if data.name
            .and_then(|name| parsed.arena.get(name))
            .is_some_and(|record| matches!(&record.data, NodeData::Identifier(name) if name.text == "Model")))
    );
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(resolved_type(&context, read), number);
    assert_eq!(
        context
            .store()
            .value_symbol_links(field)
            .unwrap()
            .resolved_type,
        Some(number)
    );
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn constructor_property_writes_track_string_and_boolean_assignments() {
    let parsed = parse_source_file(concat!(
        "class Model { text?: string; ready?: boolean; constructor() { ",
        "this.text = 'set'; const text: string = this.text; ",
        "this.text = undefined; const absent = this.text; ",
        "this.ready = true; const ready: boolean = this.ready; ",
        "this.ready = false; const cleared: boolean = this.ready; } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, false);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    for (name, expected) in [
        ("text", "string"),
        ("absent", "undefined"),
        ("ready", "true"),
        ("cleared", "false"),
    ] {
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, initializer(&parsed, name)))
                .unwrap(),
            expected
        );
    }
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (name, declared) in [
        ("text", bootstrap.string_type),
        ("ready", bootstrap.boolean_type),
    ] {
        assert_eq!(
            context
                .store()
                .value_symbol_links(property(&context, "Model", name))
                .unwrap()
                .resolved_type,
            Some(declared)
        );
    }
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn constructor_property_writes_keep_assignment_and_initialization_diagnostics() {
    for (source, expected) in [
        (
            "class Model { value: number; constructor() { this.value; this.value = 1; } }",
            vec![2565],
        ),
        (
            "class Model { value: number; constructor() { this.value = this.value; } }",
            vec![2565],
        ),
        (
            "class Model { value?: number; constructor() { this.value = 'bad'; const n: number = this.value; } }",
            vec![2322, 2322],
        ),
        (
            "class Base {} class Model extends Base { value: number; constructor() { this.value = 1; super(); const n: number = this.value; } }",
            vec![17009],
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = context(&parsed, false);
        context.check_source_file(FILE).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            expected,
            "{source}: {:?}",
            context.diagnostics()
        );
        let diagnostics = context.diagnostics().clone();
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn constructor_property_writes_keep_exact_optional_write_types() {
    for source in [
        "class Model { value?: number; constructor() { this.value = undefined; this.value = 1; const n: number = this.value; } }",
        "class Model { private value?: number; constructor() { this.value = undefined; this.value = 1; const n: number = this.value; } }",
    ] {
        for exact in [false, true] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = context(&parsed, exact);
            context
                .check_source_file(FILE)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let expected = if exact { vec![2412] } else { vec![] };
            assert_eq!(
                context
                    .diagnostics()
                    .as_slice()
                    .iter()
                    .map(|diagnostic| diagnostic.diagnostic.code())
                    .collect::<Vec<_>>(),
                expected,
                "{source}"
            );
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let read = initializer(&parsed, "n");
            assert_eq!(resolved_type(&context, read), number);
            let field = context
                .store()
                .symbol_node_links(read)
                .unwrap()
                .resolved_symbol
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(field)
                    .unwrap()
                    .resolved_type,
                Some(number)
            );
            let diagnostics = context.diagnostics().clone();
            let warm = counts(&context);
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), warm);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn method_property_writes_do_not_initialize_required_fields() {
    let parsed = parse_source_file("class Model { value: number; method() { this.value = 1; } }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, false);
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one uninitialized-field diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2564);
    assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.range_override.is_none());
    let name = parsed.arena.get(diagnostic.node.unwrap().node).unwrap();
    assert!(matches!(&name.data, NodeData::Identifier(name) if name.text == "value"));

    let field = property(&context, "Model", "value");
    assert_eq!(
        name.parent,
        context
            .store()
            .symbol(field)
            .unwrap()
            .value_declaration()
            .map(|node| node.node)
    );
    let field_links = context.store().value_symbol_links(field).unwrap().clone();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(field_links.resolved_type, Some(number));
    let method = property(&context, "Model", "method");
    let method_type = context
        .store()
        .value_symbol_links(method)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(context.type_to_string(method_type).unwrap(), "() => void");
    let nodes = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            Some(
                [node, binary.left, binary.right]
                    .map(|node| NodeRef::new(parsed.arena.id(), FILE, node)),
            )
        })
        .unwrap();
    let types = nodes.map(|node| resolved_type(&context, node));
    for (type_, expected) in types.into_iter().zip(["1", "number", "1"]) {
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
    }
    assert_eq!(
        context
            .store()
            .symbol_node_links(nodes[1])
            .unwrap()
            .resolved_symbol,
        Some(field)
    );

    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(
        context.store().value_symbol_links(field),
        Some(&field_links)
    );
    assert_eq!(nodes.map(|node| resolved_type(&context, node)), types);
    assert_eq!(
        context
            .store()
            .value_symbol_links(method)
            .unwrap()
            .resolved_type,
        Some(method_type)
    );
}

#[test]
fn unsupported_class_property_writes_fail_before_class_preparation() {
    for source in [
        "class Model { static value = 1; constructor() { Model.value = 2; } }",
        "class Model { value: number; constructor() { this['value'] = 1; } }",
        "class Model { value: number; constructor() { this.value += 1; } }",
        "class Model { value: number; constructor() { if (true) { this.value = 1; } } }",
        "class Model { value: number; constructor() { while (true) { this.value = 1; } } }",
        "class Model { value: number; constructor() { const write = () => { this.value = 1; }; } }",
        "class Model { value: number; constructor() { function write() { this.value = 1; } } }",
        "class Base { value = 1; } class Model extends Base { constructor() { super(); this.value = 2; } }",
        "class Model { get value(): number { return 1; } constructor() { this.value = 2; } }",
        "class Model { constructor() { this.missing = 1; } }",
        "class Model { value: number; other: number; constructor() { this.value = (this.other = 1); } }",
        "class Model { #value?: number; constructor() { this.#value = undefined; } }",
    ] {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let mut context = context(&parsed, false);
        let cold = counts(&context);
        assert!(
            matches!(
                context.check_source_file(FILE),
                Err(SourceCheckError::Unsupported(_))
            ),
            "{source}"
        );
        assert_eq!(counts(&context), cold, "{source}");
        for (node, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::ClassDeclaration {
                continue;
            }
            let declaration = NodeRef::new(parsed.arena.id(), FILE, node);
            let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
            assert!(
                context.store().declared_type_links(symbol).is_none(),
                "{source}"
            );
            assert!(
                context.store().value_symbol_links(symbol).is_none(),
                "{source}"
            );
        }
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Flow and replay checks share the same constructor and mapped call.
fn constructor_write_flow_survives_a_mapped_instance_super_call() {
    let parsed = parse_source_file(concat!(
        "class Base { self() { return this; } } ",
        "class Model extends Base { value?: number; constructor() { ",
        "super(); this.value = 1; const before: number = this.value; ",
        "super.self(); const after: number = this.value; ",
        "} read() { return this.value; } }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut context = context(&parsed, false);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let base = context
        .store()
        .declared_type_links(owner(&context, "Base"))
        .unwrap()
        .declared_type
        .unwrap();
    let model = context
        .store()
        .declared_type_links(owner(&context, "Model"))
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(model_class) = context.store().type_payload(model).unwrap().data()
    else {
        panic!("Model retains its class instance type")
    };
    let model_this = model_class.this_type.unwrap();
    let (call, access, receiver) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(call.expression)?.data
            else {
                return None;
            };
            (parsed.arena.get(access.expression)?.kind == SyntaxKind::SuperKeyword).then_some((
                NodeRef::new(parsed.arena.id(), FILE, node),
                NodeRef::new(parsed.arena.id(), FILE, call.expression),
                NodeRef::new(parsed.arena.id(), FILE, access.expression),
            ))
        })
        .unwrap();
    let receiver_type = resolved_type(&context, receiver);
    let TypeData::TypeReference(reference) =
        context.store().type_payload(receiver_type).unwrap().data()
    else {
        panic!("instance super retains a mapped base reference")
    };
    assert_eq!(reference.object.target, Some(base));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[model_this][..])
    );
    assert_eq!(resolved_type(&context, call), model_this);
    assert_eq!(
        context
            .store()
            .symbol_node_links(access)
            .unwrap()
            .resolved_symbol,
        Some(property(&context, "Base", "self")),
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for name in ["before", "after"] {
        assert_eq!(resolved_type(&context, initializer(&parsed, name)), number);
    }
    let field = property(&context, "Model", "value");
    assert_eq!(
        context
            .store()
            .value_symbol_links(field)
            .unwrap()
            .resolved_type,
        Some(number)
    );
    let deferred_read = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ReturnStatement(returned) = &record.data else {
                return None;
            };
            let expression = returned.expression?;
            (parsed.arena.get(expression)?.kind == SyntaxKind::PropertyAccessExpression)
                .then_some(NodeRef::new(parsed.arena.id(), FILE, expression))
        })
        .unwrap();
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, deferred_read))
            .unwrap(),
        "number | undefined",
    );

    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(resolved_type(&context, call), model_this);
    assert_eq!(resolved_type(&context, receiver), receiver_type);
    for name in ["before", "after"] {
        assert_eq!(resolved_type(&context, initializer(&parsed, name)), number);
    }
    assert_eq!(
        context
            .store()
            .value_symbol_links(field)
            .unwrap()
            .resolved_type,
        Some(number)
    );
    assert!(context.diagnostics().is_empty());
}
