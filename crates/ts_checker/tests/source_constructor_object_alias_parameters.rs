use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, signatures::SignatureFlags,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_270);
const LIBRARY: FileId = FileId::new(204_271);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const CLASS: &str = concat!(
    "type Options = { message?: string };\n",
    "export class Model { constructor(options?: Options) {} }\n",
);

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/constructor-object-alias.ts\""),
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
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
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

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, id),
            ))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn check_case(calls: &str, invalid: bool) {
    let source = format!("{CLASS}{calls}");
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    let classes = nodes(&parsed, SyntaxKind::ClassDeclaration);
    let constructors = nodes(&parsed, SyntaxKind::Constructor);
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    let ([class], [constructor], [parameter]) = (
        classes.as_slice(),
        constructors.as_slice(),
        parameters.as_slice(),
    ) else {
        panic!("expected one class, constructor and parameter")
    };
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.question_token.is_some());
    assert!(data.initializer.is_none());
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(constructor.node)
    );
    let annotation = NodeRef::new(parsed.arena.id(), FILE, data.type_.unwrap());
    let parameter_name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let constructions = nodes(&parsed, SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), if invalid { 1 } else { 3 });

    for members_first in [false, true] {
        let mut checker = context(&parsed, &library);
        assert!(checker.global_types().diagnostics().is_empty());
        let owner = symbol(&checker, *class);
        let early = members_first.then(|| checker.get_nongeneric_class_members(owner).unwrap());
        checker.check_source_file(FILE).unwrap();
        let members = checker.get_nongeneric_class_members(owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, members);
        }
        assert!(members.declared_instance_properties().is_empty());
        let selected = members.default_construct_signature();
        assert_eq!(signature(&checker, *constructor), selected);
        let parameter_symbol = symbol(&checker, *parameter);
        let record = checker.store().signature(selected).unwrap();
        assert_eq!(record.declaration(), Some(*constructor));
        assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(record.parameters(), [parameter_symbol]);
        assert_eq!(record.min_argument_count(), 0);
        assert_eq!(
            record.resolved_return_type(),
            Some(members.shells().instance_type())
        );

        let alias_type = checker.get_type_from_type_node(annotation).unwrap();
        let parameter_type = checker
            .store()
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            checker.get_type_at_location(parameter_name).unwrap(),
            parameter_type
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        assert_ne!(alias_type, bootstrap.any_type);
        assert_ne!(parameter_type, bootstrap.any_type);
        let TypeData::Union(union) = checker.store().type_payload(parameter_type).unwrap().data()
        else {
            panic!("the optional parameter must keep its canonical union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&alias_type));
        assert!(union.union.types.contains(&bootstrap.undefined_type));
        for &construction in &constructions {
            assert_eq!(signature(&checker, construction), selected);
            assert_eq!(
                checker.get_type_at_location(construction).unwrap(),
                members.shells().instance_type()
            );
        }

        if invalid {
            let NodeData::NewExpression(call) =
                &parsed.arena.get(constructions[0].node).unwrap().data
            else {
                unreachable!()
            };
            let [argument] = call.arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("expected the invalid object argument")
            };
            let argument = NodeRef::new(parsed.arena.id(), FILE, *argument);
            let range = parsed.arena.get(argument.node).unwrap().range;
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                "wrong"
            );
            let argument_type = checker.get_type_at_location(argument).unwrap();
            let argument_display = checker.type_to_string(argument_type).unwrap();
            let target_display = checker.type_to_string(alias_type).unwrap();
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("expected one constructor argument diagnostic")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(
                diagnostic.diagnostic.arguments,
                [argument_display, target_display]
            );
            assert!(diagnostic.range_override.is_none());
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }

        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.type_resolution_len(),
                ],
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = NodeRef::new(parsed.arena.id(), FILE, id);
                        (
                            store.type_node_links(node).cloned(),
                            store.signature_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                store
                    .symbol_store()
                    .symbols()
                    .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
                    .collect::<Vec<_>>(),
                checker.diagnostics().clone(),
                store
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .cloned(),
            )
        };
        let before = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(
                checker.get_nongeneric_class_members(owner).unwrap(),
                members
            );
            assert_eq!(
                checker.get_type_from_type_node(annotation).unwrap(),
                alias_type
            );
            assert_eq!(
                checker.get_type_at_location(parameter_name).unwrap(),
                parameter_type
            );
            for &construction in &constructions {
                assert_eq!(signature(&checker, construction), selected);
                assert_eq!(
                    checker.get_type_at_location(construction).unwrap(),
                    members.shells().instance_type()
                );
            }
            assert_eq!(snapshot(&checker), before);
        }
    }
}

#[test]
fn optional_constructor_object_alias_accepts_omitted_and_supplied_arguments() {
    check_case(
        "new Model();\nnew Model({});\nnew Model({ message: \"ok\" });\n",
        false,
    );
}

#[test]
fn optional_constructor_object_alias_rejects_wrong_property_and_keeps_identity() {
    check_case("const wrong = { message: 1 };\nnew Model(wrong);\n", true);
}
