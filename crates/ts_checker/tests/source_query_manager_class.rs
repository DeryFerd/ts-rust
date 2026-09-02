use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(300_480);
const SOURCE: &str = r"type Listener = (online: boolean) => void;
type SetupFn = (listener: Listener) => void;
class Manager {
  #setup: SetupFn;
  constructor() {
    this.#setup = (listener) => { listener(true); };
  }
}
";

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/query-manager-class.ts\""),
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
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
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
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)));
    let result = nodes.next().unwrap();
    assert!(nodes.next().is_none(), "more than one {kind:?}");
    result
}

fn alias_body(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::TypeAliasDeclaration(alias) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, alias.type_))
    });
    let result = nodes.next().unwrap();
    assert!(nodes.next().is_none());
    result
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a canonical callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature")
    };
    *signature
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn check_assignment_context(parsed: &ParseResult, wrong_argument: bool) {
    let class = only(parsed, SyntaxKind::ClassDeclaration);
    let constructor = only(parsed, SyntaxKind::Constructor);
    let field = only(parsed, SyntaxKind::PropertyDeclaration);
    let arrow = only(parsed, SyntaxKind::ArrowFunction);
    let access = only(parsed, SyntaxKind::PropertyAccessExpression);
    let call = only(parsed, SyntaxKind::CallExpression);
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let [parameter] = arrow_data.parameters.nodes.as_slice() else {
        panic!("expected the unannotated listener parameter")
    };
    let parameter = node(parsed, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.type_.is_none());
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("expected one listener argument")
    };
    let argument = node(parsed, *argument);
    let callee = node(parsed, call_data.expression);
    let mut checker = context(parsed);
    checker.check_source_file(FILE).unwrap();
    if wrong_argument {
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected one argument error: {:?}", checker.diagnostics())
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    } else {
        assert!(
            checker.diagnostics().as_slice().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
    }

    let owner = symbol(&checker, class);
    let field_symbol = symbol(&checker, field);
    let arrow_symbol = symbol(&checker, arrow);
    let parameter_symbol = symbol(&checker, parameter);
    let listener = checker
        .get_type_from_type_node(alias_body(parsed, "Listener"))
        .unwrap();
    let setup = checker
        .get_type_from_type_node(alias_body(parsed, "SetupFn"))
        .unwrap();
    let arrow_type = checker.get_type_at_location(arrow).unwrap();
    let listener_signature = signature(&checker, listener);
    let setup_signature = signature(&checker, setup);
    let arrow_signature = signature(&checker, arrow_type);
    let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    let listener_parameter = checker
        .store()
        .signature(listener_signature)
        .unwrap()
        .parameters()[0];
    let setup_parameter = checker
        .store()
        .signature(setup_signature)
        .unwrap()
        .parameters()[0];
    for (parameter, expected) in [
        (listener_parameter, boolean),
        (setup_parameter, listener),
        (parameter_symbol, listener),
        (field_symbol, setup),
    ] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
    assert_eq!(
        checker.store().symbol(field_symbol).unwrap().parent(),
        Some(owner)
    );
    assert_eq!(
        checker
            .store()
            .symbol(field_symbol)
            .unwrap()
            .value_declaration(),
        Some(field)
    );
    assert_eq!(
        checker.file(FILE).unwrap().1.container(parameter),
        Some(arrow)
    );
    assert_eq!(
        checker.file(FILE).unwrap().1.container(access),
        Some(constructor)
    );
    assert_eq!(
        checker.store().type_payload(arrow_type).unwrap().symbol(),
        Some(arrow_symbol)
    );
    assert_ne!(arrow_type, setup);
    assert_ne!(arrow_signature, setup_signature);
    let arrow_record = checker.store().signature(arrow_signature).unwrap();
    assert_eq!(arrow_record.declaration(), Some(arrow));
    assert_eq!(arrow_record.parameters(), [parameter_symbol]);
    assert!(arrow_record.type_parameters().is_empty());
    assert_eq!(arrow_record.min_argument_count(), 1);
    let locations = [
        (access, setup),
        (arrow, arrow_type),
        (callee, listener),
        (call, void),
    ];
    for &(location, expected) in &locations {
        assert_eq!(checker.get_type_at_location(location), Ok(expected));
    }
    assert_eq!(
        checker.get_symbol_at_location(access),
        Ok(Some(field_symbol))
    );
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(parameter_symbol))
    );
    for signature in [listener_signature, setup_signature, arrow_signature] {
        assert_eq!(checker.get_return_type_of_signature(signature), Ok(void));
    }

    let links = |checker: &CanonicalCheckerContext<'_>| {
        locations.map(|(location, _)| {
            (
                checker.store().type_node_links(location).cloned(),
                checker.store().symbol_node_links(location).cloned(),
                checker.store().signature_links(location).cloned(),
            )
        })
    };
    let values = |checker: &CanonicalCheckerContext<'_>| {
        [field_symbol, parameter_symbol, arrow_symbol].map(|symbol| {
            (
                checker.store().declared_type_links(symbol).cloned(),
                checker.store().value_symbol_links(symbol).cloned(),
            )
        })
    };
    let warm = (counts(&checker), links(&checker), values(&checker));
    let diagnostics = checker.diagnostics().clone();
    let source = checker.source_file(FILE).unwrap();
    let source_links = checker.store().source_file_links(source).cloned();
    assert!(source_links.as_ref().unwrap().type_checked);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        assert_eq!(
            checker.get_symbol_at_location(access),
            Ok(Some(field_symbol))
        );
        assert_eq!(
            checker.get_symbol_at_location(callee),
            Ok(Some(parameter_symbol))
        );
        for signature in [listener_signature, setup_signature, arrow_signature] {
            assert_eq!(checker.get_return_type_of_signature(signature), Ok(void));
        }
        assert_eq!((counts(&checker), links(&checker), values(&checker)), warm);
        assert_eq!(
            checker.store().source_file_links(source),
            source_links.as_ref()
        );
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn private_constructor_assignment_context_types_the_listener() {
    check_assignment_context(&parse_source_file(SOURCE), false);
}

#[test]
fn private_constructor_assignment_keeps_the_native_argument_error() {
    let source = SOURCE.replace("listener(true)", "listener(\"offline\")");
    check_assignment_context(&parse_source_file(&source), true);
}
