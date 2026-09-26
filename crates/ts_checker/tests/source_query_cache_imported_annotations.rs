use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks,
    SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeMapperId,
    TypeNodeLinks, ValueSymbolLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const PROVIDER: FileId = FileId::new(203_090);
const CONSUMER: FileId = FileId::new(203_091);
const BOX: &str = concat!(
    "export class Box<A, B, C, D> {\n",
    "  constructor() {}\n",
    "  first(value: A): A { return value; }\n",
    "  second(value: B): B { return value; }\n",
    "  third(value: C): C { return value; }\n",
    "  fourth(value: D): D { return value; }\n",
    "}\n",
);
const SOURCE: &str = concat!(
    "import { Box as ImportedBox } from './box';\n",
    "interface Event { item: ImportedBox<string, number, boolean, null>; }\n",
    "declare const event: Event;\n",
    "const text: string = event.item.first('ok');\n",
    "const count: number = event.item.second(2);\n",
    "const flag: boolean = event.item.third(true);\n",
    "const empty: null = event.item.fourth(null);\n",
    "const bad: string = event.item.first(1);\n",
);

fn context<'arena>(
    provider: &'arena ParseResult,
    consumer: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (PROVIDER, provider, "\"/project/box.ts\""),
        (CONSUMER, consumer, "\"/project/consumer.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let import = only_node(consumer, CONSUMER, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &consumer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(consumer.arena.id(), CONSUMER, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::ImportSpecifier(import) => import.name,
                NodeData::MethodDeclaration(method) => method.name,
                NodeData::TypeParameterDeclaration(parameter) => parameter.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {name}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let node = declaration(parsed, CONSUMER, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), CONSUMER, variable.initializer.unwrap())
}

type NodeState = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolState = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<AliasSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 9],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    sources: [Option<SourceFileLinks>; 2],
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
) -> Snapshot {
    let store = checker.store();
    let sources = [(PROVIDER, provider), (CONSUMER, consumer)];
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.merged_symbol_len(),
            store.type_resolution_len(),
        ],
        nodes: sources
            .iter()
            .flat_map(|&(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.alias_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        sources: sources.map(|(file, _)| {
            store
                .source_file_links(checker.source_file(file).unwrap())
                .cloned()
        }),
        diagnostics: checker.diagnostics().clone(),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct AnnotationProof {
    applied: TypeId,
    calls: Vec<(TypeId, SignatureId, TypeMapperId)>,
}

#[allow(clippy::too_many_lines)] // Keep the property, source formals, and substitutions together.
fn assert_annotation(
    checker: &mut CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
) -> AnnotationProof {
    let class = symbol(checker, declaration(provider, PROVIDER, "Box"));
    let import = symbol(checker, declaration(consumer, CONSUMER, "ImportedBox"));
    assert_ne!(class, import);
    assert_eq!(
        checker.store().symbol(import).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    let alias = checker.store().alias_symbol_links(import).unwrap();
    assert_eq!(alias.immediate_target, Some(class));
    assert_eq!(alias.alias_target, AliasTargetState::Resolved(class));
    assert_eq!(alias.type_only_declaration, None);

    let target = checker.get_declared_type_of_symbol(class).unwrap();
    let TypeData::Interface(class_type) = checker.store().type_payload(target).unwrap().data()
    else {
        panic!("the provider keeps its declared class type")
    };
    let formals = class_type
        .reference
        .resolved_type_arguments
        .clone()
        .unwrap();
    assert_eq!(formals.len(), 4);
    for (&formal, name) in formals.iter().zip(["A", "B", "C", "D"]) {
        assert_eq!(
            checker.store().type_payload(formal).unwrap().symbol(),
            Some(symbol(checker, declaration(provider, PROVIDER, name)))
        );
    }
    let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
    let arguments = [
        intrinsic.string_type,
        intrinsic.number_type,
        intrinsic.boolean_type,
        intrinsic.null_type,
    ];
    assert!(arguments.iter().all(|argument| !formals.contains(argument)));

    let property = only_node(consumer, CONSUMER, SyntaxKind::PropertyDeclaration);
    let NodeData::PropertyDeclaration(field) =
        &consumer.arena.get(property.node).unwrap().data
    else {
        unreachable!()
    };
    let interface = declaration(consumer, CONSUMER, "Event");
    assert_eq!(
        consumer.arena.get(property.node).unwrap().parent,
        Some(interface.node)
    );
    let annotation = NodeRef::new(consumer.arena.id(), CONSUMER, field.type_.unwrap());
    assert_eq!(
        consumer.arena.get(annotation.node).unwrap().parent,
        Some(property.node)
    );
    let NodeData::TypeReferenceNode(written) = &consumer.arena.get(annotation.node).unwrap().data
    else {
        panic!("the interface field keeps its written generic reference")
    };
    let written_arguments = written.type_arguments.as_ref().unwrap();
    assert_eq!(written_arguments.nodes.len(), 4);
    for (&node, &argument) in written_arguments.nodes.iter().zip(&arguments) {
        let node = NodeRef::new(consumer.arena.id(), CONSUMER, node);
        assert_eq!(checker.get_type_from_type_node(node), Ok(argument));
    }
    let applied = checker.get_type_from_type_node(annotation).unwrap();
    assert_ne!(applied, target);
    let TypeData::TypeReference(reference) = checker.store().type_payload(applied).unwrap().data()
    else {
        panic!("the field resolves to an applied class reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(arguments.as_slice())
    );
    let property_symbol = symbol(checker, property);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(property_symbol)
            .unwrap()
            .resolved_type,
        Some(applied)
    );

    let mut calls = Vec::new();
    for (result, method_name, index) in [
        ("text", "first", 0),
        ("count", "second", 1),
        ("flag", "third", 2),
        ("empty", "fourth", 3),
        ("bad", "first", 0),
    ] {
        let method = declaration(provider, PROVIDER, method_name);
        let original = checker
            .store()
            .signature_links(method)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(
            checker
                .store()
                .signature(original)
                .unwrap()
                .resolved_return_type(),
            Some(formals[index])
        );
        let call = initializer(consumer, result);
        let NodeData::CallExpression(call_data) = &consumer.arena.get(call.node).unwrap().data
        else {
            unreachable!()
        };
        let access = NodeRef::new(consumer.arena.id(), CONSUMER, call_data.expression);
        let NodeData::PropertyAccessExpression(access_data) =
            &consumer.arena.get(access.node).unwrap().data
        else {
            unreachable!()
        };
        let receiver = NodeRef::new(consumer.arena.id(), CONSUMER, access_data.expression);
        assert_eq!(
            checker.get_symbol_at_location(receiver),
            Ok(Some(property_symbol))
        );
        assert_eq!(checker.get_type_at_location(receiver), Ok(applied));
        let callable = checker.get_type_at_location(access).unwrap();
        let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data()
        else {
            panic!("the applied class method is callable")
        };
        assert_eq!(object.structured.call_signature_count, 1);
        let [signature] = object.structured.signatures.as_deref().unwrap() else {
            panic!("each identity method has one signature")
        };
        let signature_id = *signature;
        let signature = checker.store().signature(signature_id).unwrap();
        assert_eq!(signature.declaration(), Some(method));
        assert_eq!(signature.target(), Some(original));
        assert_eq!(signature.resolved_return_type(), Some(arguments[index]));
        let mapper = signature.mapper().unwrap();
        let [parameter] = signature.parameters() else {
            panic!("each identity method has one parameter")
        };
        assert_eq!(
            checker
                .store()
                .value_symbol_links(*parameter)
                .unwrap()
                .resolved_type,
            Some(arguments[index])
        );
        assert_eq!(checker.get_type_at_location(call), Ok(arguments[index]));
        calls.push((callable, signature_id, mapper));
    }
    assert_eq!(calls[0], calls[4]);
    AnnotationProof { applied, calls }
}

fn assert_native_error(checker: &CanonicalCheckerContext<'_>, consumer: &ParseResult) {
    let call = initializer(consumer, "bad");
    let NodeData::CallExpression(call) = &consumer.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = call.arguments.nodes.as_slice() else {
        panic!("the invalid call has one argument")
    };
    let bad = NodeRef::new(consumer.arena.id(), CONSUMER, *argument);
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("only the number passed to first must fail")
    };
    assert_eq!(diagnostic.node, Some(bad));
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
    let range = consumer.arena.get(bad.node).unwrap().range;
    assert_eq!(
        diagnostic.range_override.map_or(range, |span| span.range()),
        range
    );
    assert!(diagnostic.related_information.is_empty());
}

#[test]
fn imported_generic_class_interface_property_keeps_substitution_and_native_error() {
    let provider = parse_source_file(BOX);
    let consumer = parse_source_file(SOURCE);
    for provider_first in [false, true] {
        let mut checker = context(&provider, &consumer);
        if provider_first {
            checker.check_source_file(PROVIDER).unwrap();
        }
        checker.check_source_file(CONSUMER).unwrap();
        checker.check_source_file(PROVIDER).unwrap();
        let proof = assert_annotation(&mut checker, &provider, &consumer);
        assert_native_error(&checker, &consumer);
        let warm = snapshot(&checker, &provider, &consumer);
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            checker.recheck_source_file(PROVIDER).unwrap();
            assert_eq!(assert_annotation(&mut checker, &provider, &consumer), proof);
            assert_native_error(&checker, &consumer);
            assert_eq!(snapshot(&checker, &provider, &consumer), warm);
        }
    }
}
