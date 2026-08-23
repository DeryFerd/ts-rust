use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    ResolvedSignatureState, SignatureLinks, SourceCheckError, UnsupportedSourceSyntax,
    signatures::SignatureFlags,
};
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
fn inaccessible_constructors_reject_external_construction_before_publication() {
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

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                constructor,
            )))
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
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
fn unsupported_constructor_parameters_and_nonempty_bodies_leave_classes_cold() {
    for (index, source) in [
        "class Model { constructor(public value: string) {} }",
        concat!(
            "class Base { constructor(public value: string) {} } ",
            "class Model extends Base { constructor(value: string) { super(value); } }",
        ),
        "class Model { constructor() { const value = 1; } }",
        "class Base {} class Model extends Base { constructor() {} }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_106 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = class_symbol(&parsed, file, &context, "Model");

        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(_)
            ))
        ));
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
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
