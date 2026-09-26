use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, TypeData, TypeId,
    TypeNodeLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_810);
const DECLARATIONS: FileId = FileId::new(202_811);
const SOURCE: FileId = FileId::new(202_812);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECLARATION_TEXT: &str = concat!(
    "interface Payload { firstKey: number; secondKey: string }\n",
    "interface Methods {\n",
    "  m<T>(value: T): keyof T;\n",
    "  m(a: number, b: number): number;\n",
    "  nested<T>(value: T): Array<keyof T>;\n",
    "  nested(a: number, b: number): number;\n",
    "}\n",
    "declare const methods: Methods;\n",
    "declare const payload: Payload;\n",
    "declare const wrong: string;\n",
);
const SOURCE_TEXT: &str = concat!(
    "const inferred = methods.m(payload);\n",
    "const explicit = methods.m<Payload>(payload);\n",
    "const nested = methods.nested(payload);\n",
    "const explicitNested = methods.nested<Payload>(payload);\n",
    "const ordinary = methods.m(1, 2);\n",
    "const ordinaryNested = methods.nested(1, 2);\n",
    "const invalid = methods.m(1, wrong);\n",
);

fn context<'arena>(
    library: &'arena ParseResult,
    declarations: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true, true),
        (
            DECLARATIONS,
            declarations,
            "\"/project/methods.d.ts\"",
            true,
            false,
        ),
        (SOURCE, source, "\"/project/mapped-keyof.ts\"", false, false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, declaration_file, default_library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _, _)| (file, &parsed.arena))
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

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| panic!("missing signature for {node:?}"))
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::TypeReference(reference) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected a canonical Array reference");
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type)
    );
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("Array must retain its one mapped element type");
    };
    *element
}

fn index_target(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::Index(index) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a retained keyof Index type");
    };
    index.target
}

fn assert_key_union(context: &CanonicalCheckerContext<'_>, type_: TypeId, payload: TypeId) {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("Payload must produce a two-key union");
    };
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let mut expected = [
        bootstrap.cached_string_literal_type("firstKey").unwrap(),
        bootstrap.cached_string_literal_type("secondKey").unwrap(),
    ];
    expected.sort_unstable();
    let mut actual = union.union.types.clone();
    actual.sort_unstable();
    assert_eq!(actual, expected);
    assert_eq!(index_target(context, union.origin.unwrap()), payload);
    assert_eq!(context.type_to_string(type_).unwrap(), "keyof Payload");
}

fn assert_selected_method(
    context: &CanonicalCheckerContext<'_>,
    selected: SignatureId,
    original: SignatureId,
    payload: TypeId,
) {
    assert_ne!(selected, original);
    let selected = context.store().signature(selected).unwrap();
    let original_record = context.store().signature(original).unwrap();
    assert_eq!(selected.target(), Some(original));
    let mapper = selected.mapper().unwrap();
    let [source_parameter] = original_record.type_parameters() else {
        panic!("the source generic overload must retain its own T");
    };
    assert_eq!(
        context.store().map_type(mapper, *source_parameter),
        Some(payload)
    );
    assert!(selected.type_parameters().is_empty());
    assert_eq!(selected.declaration(), original_record.declaration());
    let [parameter] = selected.parameters() else {
        panic!("the selected generic overload has one value parameter");
    };
    assert_eq!(
        context
            .store()
            .value_symbol_links(*parameter)
            .unwrap()
            .resolved_type,
        Some(payload),
    );
}

fn assert_argument_diagnostic(context: &CanonicalCheckerContext<'_>, source: &ParseResult) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the wrong second argument must produce exactly one diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'.",
    );
    let node = diagnostic.node.unwrap();
    assert_eq!(node.file, SOURCE);
    assert_eq!(node.arena, source.arena.id());
    let range = source.arena.get(node.node).unwrap().range;
    assert_eq!(
        &SOURCE_TEXT[range.start.get() as usize..range.end.get() as usize],
        "wrong",
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) -> Snapshot {
    let store = context.store();
    let nodes = files
        .iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        sources: files
            .iter()
            .map(|(file, _)| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep selected returns and replay on the same source graph.
fn mapped_keyof_method_returns_keep_source_types_and_query_replay() {
    let library = parse_source_file(ES5);
    let declarations = parse_source_file(DECLARATION_TEXT);
    let source = parse_source_file(SOURCE_TEXT);
    let methods = nodes(&declarations, DECLARATIONS, SyntaxKind::MethodSignature);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(methods.len(), 4);
    assert_eq!(calls.len(), 7);

    for query_first in [false, true] {
        let mut context = context(&library, &declarations, &source);
        let mut queries = Vec::new();
        let mut returns = Vec::new();
        if query_first {
            for &method in &methods {
                queries.push((method, context.get_type_at_location(method).unwrap()));
                let original = signature(&context, method);
                returns.push((
                    original,
                    context.get_return_type_of_signature(original).unwrap(),
                ));
            }
        }
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(SOURCE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        for &call in &calls {
            assert!(context.store().signature_links(call).is_none());
            assert!(context.store().type_node_links(call).is_none());
        }

        context.check_source_file(SOURCE).unwrap();
        assert_argument_diagnostic(&context, &source);
        let mut originals = Vec::new();
        for &method in &methods {
            queries.push((method, context.get_type_at_location(method).unwrap()));
            let original = signature(&context, method);
            let returned = context.get_return_type_of_signature(original).unwrap();
            returns.push((original, returned));
            originals.push((original, returned));
        }

        let payload_node = nodes(
            &declarations,
            DECLARATIONS,
            SyntaxKind::InterfaceDeclaration,
        )[0];
        let payload_symbol = context
            .file(DECLARATIONS)
            .unwrap()
            .1
            .symbol(payload_node)
            .unwrap();
        let payload = context.get_declared_type_of_symbol(payload_symbol).unwrap();
        let mut selected = Vec::new();
        for &call in &calls {
            let returned = context.get_type_at_location(call).unwrap();
            let selected_signature = signature(&context, call);
            assert_eq!(
                context.get_return_type_of_signature(selected_signature),
                Ok(returned)
            );
            queries.push((call, returned));
            returns.push((selected_signature, returned));
            selected.push((selected_signature, returned));
        }

        let keys = selected[0].1;
        assert_key_union(&context, keys, payload);
        assert_eq!(selected[1].1, keys);
        assert_eq!(selected[2].1, selected[3].1);
        assert_eq!(array_element(&context, selected[2].1), keys);
        for (index, original) in [
            (0, originals[0].0),
            (1, originals[0].0),
            (2, originals[2].0),
            (3, originals[2].0),
        ] {
            assert_selected_method(&context, selected[index].0, original, payload);
        }
        for (index, returned) in [
            (0, originals[0].1),
            (2, array_element(&context, originals[2].1)),
        ] {
            let [parameter] = context
                .store()
                .signature(originals[index].0)
                .unwrap()
                .type_parameters()
            else {
                panic!("the source overload must retain its own T");
            };
            assert_eq!(index_target(&context, returned), *parameter);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for (call, original) in [
            (4, originals[1].0),
            (5, originals[3].0),
            (6, originals[1].0),
        ] {
            assert_eq!(selected[call], (original, number));
            assert!(
                context
                    .store()
                    .signature(original)
                    .unwrap()
                    .target()
                    .is_none()
            );
        }

        for access in nodes(&source, SOURCE, SyntaxKind::PropertyAccessExpression) {
            queries.push((access, context.get_type_at_location(access).unwrap()));
        }
        let files = [(DECLARATIONS, &declarations), (SOURCE, &source)];
        let warm = snapshot(&context, &files);
        for recheck in [false, true, true] {
            if recheck {
                context.recheck_source_file(SOURCE).unwrap();
            } else {
                context.check_source_file(SOURCE).unwrap();
            }
            for &(node, expected) in &queries {
                assert_eq!(context.get_type_at_location(node), Ok(expected));
            }
            for &(signature, expected) in &returns {
                assert_eq!(
                    context.get_return_type_of_signature(signature),
                    Ok(expected)
                );
            }
            assert_eq!(snapshot(&context, &files), warm);
        }
    }
}
