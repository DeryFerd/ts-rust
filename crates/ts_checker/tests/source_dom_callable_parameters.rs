use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(300_410);
const DOM_FILE: FileId = FileId::new(300_411);
const AUGMENT_FILE: FileId = FileId::new(300_412);
const SOURCE_FILE: FileId = FileId::new(300_413);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DOM: &str = include_str!("../../ts_bundled/libs/lib.dom.d.ts");

// These fresh declarations merge with the unchanged DOM functions.
const AUGMENT: &str = concat!(
    "declare function setTimeout(handler: 'immediate'): 42;\n",
    "declare namespace setTimeout { const tag: string; }\n",
    "declare function setInterval(handler: 'immediate'): 42;\n",
    "declare namespace setInterval { const tag: string; }\n",
);

fn context<'a>(
    es5: &'a ParseResult,
    dom: &'a ParseResult,
    augment: &'a ParseResult,
    source: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, es5, "\"/lib/lib.es5.d.ts\""),
        (DOM_FILE, dom, "\"/lib/lib.dom.d.ts\""),
        (AUGMENT_FILE, augment, "\"/project/timer-augmentation.d.ts\""),
        (SOURCE_FILE, source, "\"/project/dom-callable-parameters.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != SOURCE_FILE,
                    file == ES5_FILE || file == DOM_FILE,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

struct Function {
    declaration: NodeRef,
    name: NodeRef,
    parameters: Vec<NodeRef>,
}

fn function(parsed: &ParseResult, file: FileId, expected: &str) -> Function {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name_id = function.name?;
            let NodeData::Identifier(name) = &parsed.arena.get(name_id)?.data else {
                return None;
            };
            (name.text == expected).then(|| Function {
                declaration: NodeRef::new(parsed.arena.id(), file, id),
                name: NodeRef::new(parsed.arena.id(), file, name_id),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&id| NodeRef::new(parsed.arena.id(), file, id))
                    .collect(),
            })
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression)
                .then_some(NodeRef::new(parsed.arena.id(), SOURCE_FILE, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the actual declaration or call must retain its signature")
}

fn assert_dom_signature(
    checker: &mut CanonicalCheckerContext<'_>,
    dom: &ParseResult,
    original: &Function,
    extra: &Function,
) -> SignatureId {
    let owner = symbol(checker, original.declaration);
    assert_eq!(symbol(checker, extra.declaration), owner);
    let flags = checker.store().symbol(owner).unwrap().flags();
    assert!(flags.contains(SymbolFlags::FUNCTION));
    assert!(flags.intersects(SymbolFlags::VALUE_MODULE | SymbolFlags::NAMESPACE_MODULE));
    let declarations = checker
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap()
        .iter()
        .copied()
        .filter(|node| {
            checker.file(node.file).unwrap().0.get(node.node).unwrap().kind
                == SyntaxKind::FunctionDeclaration
        })
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    assert!(declarations.contains(&original.declaration));
    assert!(declarations.contains(&extra.declaration));
    let expected = declarations
        .iter()
        .map(|&declaration| signature(checker, declaration))
        .collect::<Vec<_>>();
    let callable = checker.get_type_at_location(original.name).unwrap();
    let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data() else {
        panic!("the merged global must retain its real callable type");
    };
    assert_eq!(object.structured.call_signature_count, 2);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(expected.as_slice())
    );

    let selected = signature(checker, original.declaration);
    let expected_parameters = original
        .parameters
        .iter()
        .map(|&parameter| symbol(checker, parameter))
        .collect::<Vec<_>>();
    let record = checker.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(original.declaration));
    assert_eq!(record.parameters(), expected_parameters);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.has_rest_parameter());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    let types = record
        .parameters()
        .iter()
        .map(|&parameter| {
            checker
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .collect::<Vec<_>>();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (string, number, undefined, any) = (
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.undefined_type,
        bootstrap.any_type,
    );
    let TypeData::Union(handler) = checker.store().type_payload(types[0]).unwrap().data() else {
        panic!("TimerHandler must retain its string and Function union");
    };
    assert_eq!(handler.union.types.len(), 2);
    assert!(handler.union.types.contains(&string));
    let function_type = *handler
        .union
        .types
        .iter()
        .find(|&&type_| type_ != string)
        .unwrap();
    let function_owner = checker
        .store()
        .type_payload(function_type)
        .unwrap()
        .symbol()
        .unwrap();
    let function_symbol = checker.store().symbol(function_owner).unwrap();
    assert_eq!(function_symbol.name(), "Function");
    assert!(
        function_symbol
            .declarations()
            .unwrap()
            .iter()
            .all(|node| node.file == ES5_FILE)
    );
    let TypeData::Union(timeout) = checker.store().type_payload(types[1]).unwrap().data() else {
        panic!("the optional timeout must retain undefined");
    };
    assert_eq!(timeout.union.types.len(), 2);
    assert!(timeout.union.types.contains(&number));
    assert!(timeout.union.types.contains(&undefined));
    let TypeData::TypeReference(rest) = checker.store().type_payload(types[2]).unwrap().data()
    else {
        panic!("the written rest annotation must retain its array type");
    };
    assert_eq!(rest.resolved_type_arguments.as_deref(), Some(&[any][..]));
    let rest = original.parameters[2];
    let record = dom.arena.get(rest.node).unwrap();
    assert_eq!(record.parent, Some(original.declaration.node));
    let start = usize::try_from(record.range.start.get()).unwrap();
    let end = usize::try_from(record.range.end.get()).unwrap();
    assert_eq!(&DOM[start..end], "...arguments: any[]");
    let NodeData::ParameterDeclaration(parameter) = &record.data else {
        unreachable!();
    };
    assert!(parameter.dot_dot_dot_token.is_some());
    assert!(parameter.question_token.is_none());
    assert_eq!(
        checker.get_type_from_type_node(NodeRef::new(
            dom.arena.id(),
            DOM_FILE,
            parameter.type_.unwrap()
        )),
        Ok(types[2])
    );
    assert_eq!(checker.get_return_type_of_signature(selected), Ok(number));
    selected
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    calls: &[NodeRef],
    declarations: &[NodeRef],
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        calls
            .iter()
            .map(|&call| {
                (
                    store.type_node_links(call).cloned(),
                    store.signature_links(call).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        declarations
            .iter()
            .map(|&declaration| store.signature_links(declaration).cloned())
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

#[test]
fn bundled_dom_rest_parameters_keep_merged_overloads_and_variable_arity_calls() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let augment = parse_source_file(AUGMENT);
    let source = parse_source_file(concat!(
        "const short = setTimeout('tick');\n",
        "const payload = setTimeout('tick', undefined, 1, 'payload', null);\n",
        "const repeat = setInterval('tick', 10, true);\n",
        "const immediate = setTimeout('immediate');\n",
    ));
    let timeout = function(&dom, DOM_FILE, "setTimeout");
    let interval = function(&dom, DOM_FILE, "setInterval");
    let extra_timeout = function(&augment, AUGMENT_FILE, "setTimeout");
    let extra_interval = function(&augment, AUGMENT_FILE, "setInterval");
    let calls = calls(&source);
    assert_eq!(calls.len(), 4);
    let declarations = [
        timeout.declaration,
        interval.declaration,
        extra_timeout.declaration,
        extra_interval.declaration,
    ];
    for call_first in [false, true] {
        let mut checker = context(&es5, &dom, &augment, &source);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        if call_first {
            assert_eq!(checker.get_type_at_location(calls[1]), Ok(number));
        }
        checker.check_source_file(SOURCE_FILE).unwrap();
        let timeout_signature =
            assert_dom_signature(&mut checker, &dom, &timeout, &extra_timeout);
        let interval_signature =
            assert_dom_signature(&mut checker, &dom, &interval, &extra_interval);
        for (index, selected) in [timeout_signature, timeout_signature, interval_signature]
            .into_iter()
            .enumerate()
        {
            assert_eq!(checker.get_type_at_location(calls[index]), Ok(number));
            assert_eq!(signature(&checker, calls[index]), selected);
        }
        let immediate = checker.get_type_at_location(calls[3]).unwrap();
        assert_ne!(immediate, number);
        assert_eq!(checker.type_to_string(immediate).unwrap(), "42");
        assert_eq!(
            signature(&checker, calls[3]),
            signature(&checker, extra_timeout.declaration)
        );
        assert!(checker.diagnostics().is_empty());
        let before = snapshot(&checker, &calls, &declarations);
        for _ in 0..2 {
            checker.check_source_file(SOURCE_FILE).unwrap();
            checker.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(checker.get_type_at_location(calls[1]), Ok(number));
            assert_eq!(checker.get_type_at_location(calls[3]), Ok(immediate));
            assert_eq!(snapshot(&checker, &calls, &declarations), before);
        }
    }
}

#[test]
fn bundled_dom_rest_calls_keep_native_timeout_argument_errors() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let augment = parse_source_file(AUGMENT);
    let source = parse_source_file(concat!(
        "declare const delay: string;\n",
        "setTimeout('tick', delay, 'payload');\n",
        "setInterval('tick', delay, 'payload');\n",
    ));
    let calls = calls(&source);
    assert_eq!(calls.len(), 2);
    let declarations = [
        function(&dom, DOM_FILE, "setTimeout").declaration,
        function(&dom, DOM_FILE, "setInterval").declaration,
        function(&augment, AUGMENT_FILE, "setTimeout").declaration,
        function(&augment, AUGMENT_FILE, "setInterval").declaration,
    ];
    let mut checker = context(&es5, &dom, &augment, &source);
    checker.check_source_file(SOURCE_FILE).unwrap();
    assert_eq!(checker.diagnostics().as_slice().len(), 2);
    for (&call, diagnostic) in calls.iter().zip(checker.diagnostics().as_slice()) {
        let NodeData::CallExpression(call) = &source.arena.get(call.node).unwrap().data else {
            unreachable!();
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(
            diagnostic.node,
            Some(NodeRef::new(
                source.arena.id(),
                SOURCE_FILE,
                call.arguments.nodes[1]
            ))
        );
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
    }
    let before = snapshot(&checker, &calls, &declarations);
    for _ in 0..2 {
        checker.check_source_file(SOURCE_FILE).unwrap();
        checker.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(snapshot(&checker, &calls, &declarations), before);
    }
}
