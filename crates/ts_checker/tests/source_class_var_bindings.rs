use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, TypeId,
    UnsupportedSourceSyntax,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_840);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/class-var.ts\""),
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
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn variables(parsed: &ParseResult, expected: &str) -> Vec<NodeRef> {
    let mut variables = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    variables.sort_by_key(|(start, _)| *start);
    variables.into_iter().map(|(_, node)| node).collect()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().index_info_len(),
    )
}

#[test]
fn constructor_and_method_super_collision_shapes_check_with_var() {
    for source in [
        concat!(
            "var _super = 10;\n",
            "class Foo { constructor() { var _super = 10; } }\n",
            "class b extends Foo { constructor() { super(); var _super = 10; } }\n",
            "class c extends Foo { constructor() { super(); var x = () => { var _super = 10; }; } }",
        ),
        concat!(
            "var _super = 10;\n",
            "class Foo { x() { var _super = 10; } }\n",
            "class b extends Foo { public foo() { var _super = 10; } }\n",
            "class c extends Foo { public foo() { var x = () => { var _super = 10; }; } }",
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn class_var_shadowing_keeps_each_callable_local_type() {
    let parsed = parse_source_file(concat!(
        "var value: string = \"outer\";\n",
        "class Model {\n",
        "  constructor() { var value: number = 1; var copy: number = value; }\n",
        "  method(): boolean { var value: boolean = true; var copy: boolean = value; return copy; }\n",
        "}\n",
        "var after: string = value;",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let declarations = variables(&parsed, "value");
    assert_eq!(declarations.len(), 3);
    let bound = context.file(FILE).unwrap().1;
    let symbols = declarations
        .iter()
        .map(|node| bound.symbol(*node).unwrap())
        .collect::<Vec<_>>();
    assert_ne!(symbols[0], symbols[1]);
    assert_ne!(symbols[0], symbols[2]);
    assert_ne!(symbols[1], symbols[2]);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let expected = [
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.boolean_type,
    ];
    for ((declaration, symbol), expected) in declarations.iter().zip(&symbols).zip(expected) {
        assert_eq!(value_type(&context, *symbol), expected);
        let record = context.store().symbol(*symbol).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[*declaration][..]));
        assert_eq!(record.value_declaration(), Some(*declaration));
        let callable = bound.container(*declaration).unwrap();
        let locals = bound.locals(callable).unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(locals)
                .unwrap()
                .get_source("value"),
            Some(*symbol),
        );
    }
    assert_eq!(
        parsed
            .arena
            .get(bound.container(declarations[1]).unwrap().node)
            .unwrap()
            .kind,
        SyntaxKind::Constructor,
    );
    assert_eq!(
        parsed
            .arena
            .get(bound.container(declarations[2]).unwrap().node)
            .unwrap()
            .kind,
        SyntaxKind::MethodDeclaration,
    );
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
    for (symbol, expected) in symbols.into_iter().zip(expected) {
        assert_eq!(value_type(&context, symbol), expected);
    }
}

#[test]
fn class_var_initializers_keep_their_type_errors() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  constructor() { var wrong: string = 1; }\n",
        "  method() { var wrong: number = \"value\"; }\n",
        "}",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declarations = variables(&parsed, "wrong");
    assert_eq!(declarations.len(), 2);
    let expected_nodes = declarations
        .iter()
        .map(|declaration| {
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            NodeRef::new(parsed.arena.id(), FILE, variable.name)
        })
        .collect::<Vec<_>>();
    let actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| (diagnostic.node, diagnostic.diagnostic.code()))
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        vec![
            (Some(expected_nodes[0]), 2322),
            (Some(expected_nodes[1]), 2322)
        ]
    );
    let diagnostics = context.diagnostics().clone();
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn class_var_boundaries_remain_unsupported_before_publication() {
    for source in [
        "class Model { constructor() { { var value = 1; } } }",
        "class Model { method() { var value = 1; var value = 2; } }",
        "class Model { method() { var { value } = { value: 1 }; } }",
        "class Model { static { var value = 1; } }",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let class = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    node,
                ))
            })
            .unwrap();
        let owner = context.file(FILE).unwrap().1.symbol(class).unwrap();
        let cold = counts(&context);
        assert!(matches!(
            context.check_source_file(FILE),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(_)
            )),
        ));
        assert_eq!(counts(&context), cold);
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.diagnostics().is_empty());
    }
}
