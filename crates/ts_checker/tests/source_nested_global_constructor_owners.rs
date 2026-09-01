use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(286_000);
const ADDRESS: FileId = FileId::new(286_001);
const CODEC: FileId = FileId::new(286_002);
const EVENT: FileId = FileId::new(286_003);
const SOURCE: FileId = FileId::new(286_004);

// These authored declarations retain each contributor in the DOM/Node owner shapes.
// They are not a substitute for checking the complete original library files.
const LIBRARY_TEXT: &str = r#"
interface Array<T> {}
interface ReadonlyArray<T> {}
interface Locator { browser: string; }
declare var Locator: { prototype: Locator; new(value: string): Locator; };
interface Reader { decoded: number; }
declare var Reader: { prototype: Reader; new(label?: string): Reader; };
interface Writer { encoded: boolean; }
declare var Writer: { prototype: Writer; new(): Writer; };
interface Notice { browserEvent: number; }
declare var Notice: { prototype: Notice; new(): Notice; };
"#;
const ADDRESS_TEXT: &str = r#"
declare module "address-provider" {
    var LocalLocator: { new(value: string): Locator; };
    global {
        interface Locator { server: number; }
        var Locator: typeof globalThis extends { onmessage: any; Locator: infer T }
            ? T : typeof LocalLocator;
    }
}
"#;
const CODEC_TEXT: &str = r#"
declare module "codec-provider" {
    var LocalReader: { new(label?: string): Reader; };
    var LocalWriter: { new(): Writer; };
    global {
        var Reader: typeof globalThis extends { onmessage: any; Reader: infer T }
            ? T : typeof LocalReader;
        var Writer: typeof globalThis extends { onmessage: any; Writer: infer T }
            ? T : typeof LocalWriter;
    }
}
"#;
const EVENT_TEXT: &str = r#"
export {};
declare global {
    interface Notice { serverEvent: string; }
    var Notice: typeof globalThis extends { onmessage: any; Notice: infer T } ? T : never;
}
"#;
const SOURCE_TEXT: &str = r#"
const address = new Locator("https://example.test");
const reader = new Reader("utf-8");
const omitted = new Reader();
const writer = new Writer();
const notice = new Notice();
const browser = address.browser;
const server = address.server;
const decoded = reader.decoded;
const encoded = writer.encoded;
const browserEvent = notice.browserEvent;
const serverEvent = notice.serverEvent;
"#;

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
}

fn inputs(augmentation_first: bool, source: &str) -> Vec<Input> {
    let mut inputs = [
        (LIBRARY, "\"/lib/constructors.d.ts\"", LIBRARY_TEXT),
        (ADDRESS, "\"/types/address.d.ts\"", ADDRESS_TEXT),
        (CODEC, "\"/types/codec.d.ts\"", CODEC_TEXT),
        (EVENT, "\"/types/event.d.ts\"", EVENT_TEXT),
    ]
    .into_iter()
    .map(|(file, path, text)| Input {
        file,
        path,
        parsed: parse_source_file(text),
    })
    .collect::<Vec<_>>();
    if augmentation_first {
        inputs.rotate_left(1);
    }
    inputs.push(Input {
        file: SOURCE,
        path: "\"/project/constructors.ts\"",
        parsed: parse_source_file(source),
    });
    inputs
}

fn context(inputs: &[Input]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{:?}",
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.file != SOURCE,
                    input.file == LIBRARY,
                    if input.file == EVENT {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for input in inputs {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..Default::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            no_emit: true,
            ..Default::default()
        },
    )
    .unwrap()
}

fn reference(checker: &CanonicalCheckerContext<'_>, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(checker.file(file).unwrap().0.id(), file, node)
}

fn named(
    checker: &CanonicalCheckerContext<'_>,
    file: FileId,
    kind: SyntaxKind,
    text: &str,
) -> NodeRef {
    let arena = checker.file(file).unwrap().0;
    arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::ModuleDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &arena.get(name)?.data else {
                return None;
            };
            (name.text == text).then_some(reference(checker, file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {text}"))
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker
        .store()
        .get_merged_symbol(raw_symbol(checker, node))
        .unwrap()
}

fn annotation(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(data) = &checker
        .file(declaration.file)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    reference(checker, declaration.file, data.type_.unwrap())
}

fn initializer(checker: &CanonicalCheckerContext<'_>, name: &str) -> NodeRef {
    let node = named(checker, SOURCE, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) =
        &checker.file(SOURCE).unwrap().0.get(node.node).unwrap().data
    else {
        unreachable!()
    };
    reference(checker, SOURCE, data.initializer.unwrap())
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_cold_annotation(checker: &CanonicalCheckerContext<'_>, root: NodeRef) {
    let arena = checker.file(root.file).unwrap().0;
    let range = arena.get(root.node).unwrap().range;
    for (id, _) in arena
        .iter()
        .filter(|(_, node)| node.range.start >= range.start && node.range.end <= range.end)
    {
        let node = reference(checker, root.file, id);
        assert!(
            checker
                .store()
                .type_node_links(node)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(
            checker
                .store()
                .symbol_node_links(node)
                .is_none_or(|links| links.resolved_symbol.is_none())
        );
        assert!(
            checker
                .store()
                .signature_links(node)
                .is_none_or(|links| links.resolved_signature.signature().is_none())
        );
    }
}

#[allow(clippy::too_many_lines)] // Keep each complete declaration group beside its raw and local owners.
fn assert_owners(checker: &CanonicalCheckerContext<'_>) -> Vec<(SemanticSymbolId, NodeRef)> {
    let mut result = Vec::new();
    for (name, file, has_interface) in [
        ("Locator", ADDRESS, true),
        ("Reader", CODEC, false),
        ("Writer", CODEC, false),
        ("Notice", EVENT, true),
    ] {
        let interface = named(checker, LIBRARY, SyntaxKind::InterfaceDeclaration, name);
        let selected = named(checker, LIBRARY, SyntaxKind::VariableDeclaration, name);
        let contributed = named(checker, file, SyntaxKind::VariableDeclaration, name);
        let owner = symbol(checker, interface);
        let mut declarations = vec![interface, selected];
        let mut node_declarations = Vec::new();
        if has_interface {
            node_declarations.push(named(checker, file, SyntaxKind::InterfaceDeclaration, name));
        }
        node_declarations.push(contributed);
        declarations.extend_from_slice(&node_declarations);
        let record = checker.store().symbol(owner).unwrap();
        assert_eq!(record.declarations(), Some(declarations.as_slice()));
        assert_eq!(record.value_declaration(), Some(selected));
        assert_eq!(
            record.flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
        );
        assert!(record.parent().is_none());
        assert!(record.export_symbol().is_none());
        let table = checker
            .store()
            .symbol_table(checker.globals())
            .unwrap()
            .get_source(name)
            .unwrap();
        assert_eq!(checker.store().get_merged_symbol(table), Some(owner));
        for declaration in &declarations {
            assert_eq!(symbol(checker, *declaration), owner);
        }

        let global = named(checker, file, SyntaxKind::ModuleDeclaration, "global");
        let namespace = symbol(checker, global);
        let namespace_record = checker.store().symbol(namespace).unwrap();
        assert_eq!(namespace_record.name(), InternalSymbolName::Global.as_ref());
        let raw = raw_symbol(checker, contributed);
        assert_ne!(raw, owner);
        assert_eq!(
            checker
                .store()
                .symbol_table(namespace_record.exports().unwrap())
                .unwrap()
                .get_source(name),
            Some(raw)
        );
        let raw_record = checker.store().symbol(raw).unwrap();
        assert_eq!(
            raw_record.declarations(),
            Some(node_declarations.as_slice())
        );
        assert_eq!(raw_record.value_declaration(), Some(contributed));
        assert_eq!(
            raw_record
                .parent()
                .and_then(|id| checker.store().get_merged_symbol(id)),
            Some(namespace)
        );
        let local = checker
            .file(file)
            .unwrap()
            .1
            .local_symbol(contributed)
            .unwrap();
        assert_ne!(local, raw);
        assert_ne!(local, owner);
        let local_record = checker.store().symbol(local).unwrap();
        assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
        assert_eq!(local_record.export_symbol(), Some(raw));
        assert_eq!(
            local_record.declarations(),
            Some(node_declarations.as_slice())
        );
        assert!(local_record.value_declaration().is_none());
        for declaration in node_declarations {
            assert_eq!(raw_symbol(checker, declaration), raw);
            assert_eq!(
                checker.file(file).unwrap().1.local_symbol(declaration),
                Some(local)
            );
        }
        let arena = checker.file(file).unwrap().0;
        let parent = arena.get(global.node).unwrap().parent.unwrap();
        if file == EVENT {
            assert_eq!(arena.get(parent).unwrap().kind, SyntaxKind::SourceFile);
        } else {
            assert_eq!(arena.get(parent).unwrap().kind, SyntaxKind::ModuleBlock);
            let outer = arena.get(parent).unwrap().parent.unwrap();
            let NodeData::ModuleDeclaration(module) = &arena.get(outer).unwrap().data else {
                unreachable!()
            };
            assert_eq!(
                arena.get(module.name).unwrap().kind,
                SyntaxKind::StringLiteral
            );
            assert_eq!(
                arena
                    .get(arena.get(outer).unwrap().parent.unwrap())
                    .unwrap()
                    .kind,
                SyntaxKind::SourceFile
            );
        }
        assert_cold_annotation(checker, annotation(checker, contributed));
        result.push((owner, annotation(checker, selected)));
    }
    for file in [LIBRARY, ADDRESS, CODEC, EVENT] {
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
    result
}

#[allow(clippy::too_many_lines)] // Check each real call against its selected value and return owner.
fn assert_constructions(checker: &mut CanonicalCheckerContext<'_>) -> Vec<TypeId> {
    let owners = assert_owners(checker);
    let mut results = Vec::new();
    for (index, variable) in [
        (0, "address"),
        (1, "reader"),
        (1, "omitted"),
        (2, "writer"),
        (3, "notice"),
    ] {
        let (owner, annotation) = owners[index];
        let result = checker.get_declared_type_of_symbol(owner).unwrap();
        let call = initializer(checker, variable);
        assert_eq!(checker.get_type_at_location(call).unwrap(), result);
        assert_eq!(
            value_type(
                checker,
                symbol(
                    checker,
                    named(checker, SOURCE, SyntaxKind::VariableDeclaration, variable)
                )
            ),
            result
        );
        let signature = checker
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let record = checker.store().signature(signature).unwrap();
        assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(record.resolved_return_type(), Some(result));
        assert!(record.type_parameters().is_empty());
        let declaration = record.declaration().unwrap();
        assert_eq!(declaration.file, LIBRARY);
        assert_eq!(
            checker
                .file(LIBRARY)
                .unwrap()
                .0
                .get(declaration.node)
                .unwrap()
                .parent,
            Some(annotation.node)
        );
        assert_eq!(
            checker.get_return_type_of_signature(signature).unwrap(),
            result
        );
        let value = value_type(checker, owner);
        assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), value);
        let TypeData::Object(object) = checker.store().type_payload(value).unwrap().data() else {
            panic!("expected the selected TypeLiteral constructor");
        };
        assert_eq!(object.structured.call_signature_count, 0);
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some([signature].as_slice())
        );
        let NodeData::NewExpression(data) =
            &checker.file(SOURCE).unwrap().0.get(call.node).unwrap().data
        else {
            unreachable!()
        };
        let expression = reference(checker, SOURCE, data.expression);
        assert_eq!(
            checker.get_symbol_at_location(expression).unwrap(),
            Some(owner)
        );
        results.push(result);
    }
    let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
    for (name, expected) in [
        ("browser", intrinsic.string_type),
        ("server", intrinsic.number_type),
        ("decoded", intrinsic.number_type),
        ("encoded", intrinsic.boolean_type),
        ("browserEvent", intrinsic.number_type),
        ("serverEvent", intrinsic.string_type),
    ] {
        assert_eq!(
            value_type(
                checker,
                symbol(
                    checker,
                    named(checker, SOURCE, SyntaxKind::VariableDeclaration, name)
                )
            ),
            expected
        );
    }
    assert_owners(checker);
    results
}

fn snapshot(checker: &CanonicalCheckerContext<'_>) -> String {
    let store = checker.store();
    format!(
        "{:#?}",
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.merged_symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.type_resolution_len(),
                store.symbol_store().symbol_table_len(),
                store.conditional_root_len(),
            ],
            store.relation_state_snapshot(),
            checker.diagnostics(),
            checker
                .file_order()
                .iter()
                .map(|&file| {
                    (
                        file,
                        store.source_file_links(checker.source_file(file).unwrap()),
                    )
                })
                .collect::<Vec<_>>(),
            checker
                .file_order()
                .iter()
                .flat_map(|&file| {
                    checker.file(file).unwrap().0.iter().map(move |(node, _)| {
                        let node = reference(checker, file, node);
                        (
                            node,
                            store.node_links(node),
                            store.type_node_links(node),
                            store.symbol_node_links(node),
                            store.signature_links(node),
                        )
                    })
                })
                .collect::<Vec<_>>(),
            store
                .symbol_store()
                .symbols()
                .map(|(symbol, record)| {
                    (
                        symbol,
                        record,
                        store.value_symbol_links(symbol),
                        store.declared_type_links(symbol),
                        store.type_alias_links(symbol),
                    )
                })
                .collect::<Vec<_>>(),
            store.types().collect::<Vec<_>>(),
            store.signatures().collect::<Vec<_>>(),
        )
    )
}

#[test]
fn nested_global_constructors_keep_all_contributors_and_top_level_augmentation() {
    for augmentation_first in [false, true] {
        for annotation_first in [false, true] {
            let inputs = inputs(augmentation_first, SOURCE_TEXT);
            let mut checker = context(&inputs);
            let owners = assert_owners(&checker);
            let early = annotation_first.then(|| {
                owners
                    .iter()
                    .map(|(_, annotation)| checker.get_type_from_type_node(*annotation).unwrap())
                    .collect::<Vec<_>>()
            });
            assert_owners(&checker);
            checker.check_source_file(SOURCE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let results = assert_constructions(&mut checker);
            if let Some(early) = early {
                assert_eq!(
                    early,
                    owners
                        .iter()
                        .map(|(owner, _)| value_type(&checker, *owner))
                        .collect::<Vec<_>>()
                );
            }
            let warm = snapshot(&checker);
            for _ in 0..2 {
                checker.recheck_source_file(SOURCE).unwrap();
                assert_eq!(assert_constructions(&mut checker), results);
                assert_eq!(snapshot(&checker), warm);
            }
        }
    }
}

#[test]
fn nested_global_constructor_checks_the_real_argument_and_replays_its_diagnostic() {
    let inputs = inputs(true, "const invalid = new Locator(123);");
    let mut checker = context(&inputs);
    assert_owners(&checker);
    checker.check_source_file(SOURCE).unwrap();
    let call = initializer(&checker, "invalid");
    let NodeData::NewExpression(data) =
        &checker.file(SOURCE).unwrap().0.get(call.node).unwrap().data
    else {
        unreachable!()
    };
    let argument = reference(&checker, SOURCE, data.arguments.as_ref().unwrap().nodes[0]);
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one argument diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
    assert_owners(&checker);
    let warm = snapshot(&checker);
    for _ in 0..2 {
        checker.recheck_source_file(SOURCE).unwrap();
        assert_owners(&checker);
        assert_eq!(snapshot(&checker), warm);
    }
}
