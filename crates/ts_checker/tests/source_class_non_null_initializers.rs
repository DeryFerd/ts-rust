use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    RelationUnavailable, SourceCheckError, TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_211);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-non-null.ts\""),
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    let [found] = found.as_slice() else {
        panic!("expected one {kind:?}");
    };
    *found
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(declaration)
        .and_then(|symbol| checker.store().get_merged_symbol(symbol))
        .unwrap()
}

struct Field {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: NodeRef,
    operand: NodeRef,
}

fn field(parsed: &ParseResult, expected: &str) -> Field {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::PropertyDeclaration(data) = &record.data else {
                return None;
            };
            let name = match &parsed.arena.get(data.name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::PrivateIdentifier(name) => &name.text,
                _ => return None,
            };
            if name != expected {
                return None;
            }
            let initializer = data.initializer.unwrap();
            let NodeData::NonNullExpression(assertion) =
                &parsed.arena.get(initializer).unwrap().data
            else {
                panic!("{expected} must have a non-null assertion");
            };
            Some(Field {
                declaration: node(parsed, id),
                name: node(parsed, data.name),
                annotation: node(parsed, data.type_.unwrap()),
                initializer: node(parsed, initializer),
                operand: node(parsed, assertion.expression),
            })
        })
        .unwrap_or_else(|| panic!("missing field {expected}"))
}

fn cached_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fields: &[SemanticSymbolId],
    error: Option<&SourceCheckError>,
) {
    assert_eq!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .is_some_and(|links| links.type_checked),
        error.is_none(),
    );
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
            ],
            parsed
                .arena
                .iter()
                .map(|(id, _)| {
                    let node = node(parsed, id);
                    (
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            fields
                .iter()
                .map(|&symbol| store.value_symbol_links(symbol).cloned())
                .collect::<Vec<_>>(),
            store
                .source_file_links(checker.source_file(FILE).unwrap())
                .cloned(),
            checker.diagnostics().clone(),
        )
    };
    let baseline = snapshot(checker);
    for _ in 0..2 {
        match error {
            Some(error) => assert_eq!(&checker.recheck_source_file(FILE).unwrap_err(), error),
            None => {
                checker.recheck_source_file(FILE).unwrap();
            }
        }
        assert_eq!(snapshot(checker), baseline);
    }
}

#[test]
fn private_generic_field_keeps_its_annotation_after_undefined_assertion() {
    let parsed = parse_source_file(concat!(
        "class Holder<T> {\n",
        "  #current: T = undefined!;\n",
        "  read(): T { return this.#current; }\n",
        "}\n",
        "declare const holder: Holder<number>;\n",
        "const value: number = holder.read();\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty());

    let current = field(&parsed, "#current");
    let field_symbol = symbol(&checker, current.declaration);
    let formal_symbol = symbol(&checker, only(&parsed, SyntaxKind::TypeParameter));
    let formal = cached_type(&checker, current.annotation);
    let record = checker.store().type_payload(formal).unwrap();
    assert!(matches!(record.data(), TypeData::TypeParameter(_)));
    assert_eq!(record.symbol(), Some(formal_symbol));
    assert_eq!(checker.get_type_at_location(current.name).unwrap(), formal);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(field_symbol)
            .unwrap()
            .resolved_type,
        Some(formal),
    );
    assert!(
        checker
            .store()
            .symbol(field_symbol)
            .unwrap()
            .name()
            .is_private_identifier(),
    );
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        cached_type(&checker, current.operand),
        bootstrap.undefined_type,
    );
    assert_eq!(
        cached_type(&checker, current.initializer),
        bootstrap.never_type,
    );
    let number = bootstrap.number_type;
    let call = only(&parsed, SyntaxKind::CallExpression);
    assert_eq!(cached_type(&checker, call), number);
    let signature = checker
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let signature = checker.store().signature(signature).unwrap();
    assert_eq!(
        signature.declaration(),
        Some(only(&parsed, SyntaxKind::MethodDeclaration)),
    );
    assert_eq!(signature.resolved_return_type(), Some(number));
    assert_replay(&mut checker, &parsed, &[field_symbol], None);
}

#[test]
fn concrete_nullable_initializers_keep_types_and_native_assignment_error() {
    let parsed = parse_source_file(concat!(
        "declare const maybe: number | undefined;\n",
        "class Values {\n",
        "  current: number = maybe!;\n",
        "  wrong: string = maybe!;\n",
        "}\n",
        "declare const values: Values;\n",
        "const current: number = values.current;\n",
    ));
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, string, undefined) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.undefined_type,
    );
    let current = field(&parsed, "current");
    let wrong = field(&parsed, "wrong");
    let fields = [&current, &wrong].map(|field| symbol(&checker, field.declaration));
    for field in [&current, &wrong] {
        let operand = cached_type(&checker, field.operand);
        let TypeData::Union(union) = checker.store().type_payload(operand).unwrap().data() else {
            panic!("the operand must retain number | undefined");
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&number));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(cached_type(&checker, field.initializer), number);
    }
    for (field, expected) in [(&current, number), (&wrong, string)] {
        assert_eq!(cached_type(&checker, field.annotation), expected);
        assert_eq!(checker.get_type_at_location(field.name).unwrap(), expected);
    }
    assert_eq!(
        cached_type(&checker, only(&parsed, SyntaxKind::PropertyAccessExpression)),
        number,
    );
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one assignment error");
    };
    assert_eq!(diagnostic.node, Some(wrong.name));
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'.",
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert_replay(&mut checker, &parsed, &fields, None);
}

#[test]
fn generic_non_null_operands_keep_the_unsupported_type_without_publication() {
    for annotation in ["T", "T | undefined"] {
        let parsed = parse_source_file(&format!(
            "class Deferred<T> {{ #input: {annotation} = undefined!; #current: T = this.#input!; }}",
        ));
        let mut checker = context(&parsed);
        let error = checker.check_source_file(FILE).unwrap_err();
        let SourceCheckError::RelationUnavailable(
            RelationUnavailable::UnsupportedStructuredType(actual),
        ) = &error else {
            panic!("expected the unfinished NonNullable type, got {error:?}");
        };
        let formal_symbol = symbol(&checker, only(&parsed, SyntaxKind::TypeParameter));
        let record = checker.store().type_payload(*actual).unwrap();
        assert!(matches!(record.data(), TypeData::TypeParameter(_)));
        assert_eq!(record.symbol(), Some(formal_symbol));
        let current = field(&parsed, "#current");
        assert_eq!(cached_type(&checker, current.annotation), *actual);
        let operand = cached_type(&checker, current.operand);
        if annotation == "T" {
            assert_eq!(operand, *actual);
        } else {
            let TypeData::Union(union) = checker.store().type_payload(operand).unwrap().data() else {
                panic!("the rejected operand must retain T | undefined");
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(actual));
            assert!(union.union.types.contains(
                &checker.store().intrinsic_bootstrap().unwrap().undefined_type,
            ));
        }
        assert!(
            checker
                .store()
                .type_node_links(current.initializer)
                .is_none_or(|links| links.resolved_type.is_none()),
        );
        assert!(
            checker
                .store()
                .value_symbol_links(symbol(&checker, current.declaration))
                .is_none_or(|links| links.resolved_type.is_none()),
        );
        let fields = [field(&parsed, "#input"), current]
            .map(|field| symbol(&checker, field.declaration));
        assert_replay(&mut checker, &parsed, &fields, Some(&error));
    }
}
