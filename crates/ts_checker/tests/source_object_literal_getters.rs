use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks, signatures::SignatureFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const FILE: FileId = FileId::new(2);
const IMPORTER: FileId = FileId::new(3);

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    context_with_importer(library, source, None)
}

fn context_with_importer<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    importer: Option<&'arena ParseResult>,
) -> CanonicalCheckerContext<'arena> {
    let mut files = vec![
        (library, FileId::new(0), "\"/lib.es5.d.ts\"", true),
        (source, FILE, "\"/getters.ts\"", false),
    ];
    if let Some(importer) = importer {
        files.push((importer, IMPORTER, "\"/consumer.ts\"", false));
    }
    let mut binder = CanonicalBinder::new();
    for &(parsed, file, path, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(ModuleKind::EsNext),
            )
            .unwrap();
    }
    for &(parsed, file, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = importer.into_iter().map(|parsed| {
        let imports = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(import.module_specifier)
            })
            .collect::<Vec<_>>();
        let [specifier] = imports.as_slice() else {
            panic!("the consumer has one actual import");
        };
        CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(parsed.arena.id(), IMPORTER, *specifier),
            CanonicalResolvedModuleInput::new(
                FILE,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(parsed, file, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2025,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
    });
    let node = nodes.next().expect("the source contains this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn name<'a>(parsed: &'a ParseResult, node: NodeRef) -> &'a str {
    let NodeData::Identifier(identifier) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the control uses an ordinary identifier");
    };
    &identifier.text
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, Option<NodeRef>) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
            let name_node = node_ref(variable.name);
            (name(parsed, name_node) == expected).then(|| {
                (
                    node_ref(node),
                    name_node,
                    variable.initializer.map(node_ref),
                )
            })
        })
        .expect("the source contains the requested variable")
}

#[derive(Clone, Copy)]
struct Getter {
    object: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    return_statement: NodeRef,
    expression: NodeRef,
    annotation: Option<NodeRef>,
}

fn getter(parsed: &ParseResult) -> Getter {
    let declaration = only_node(parsed, SyntaxKind::GetAccessor);
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::GetAccessorDeclaration(accessor) = &record.data else {
        unreachable!();
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let NodeData::Block(body) = &parsed.arena.get(accessor.body.unwrap()).unwrap().data else {
        panic!("the getter has a block body");
    };
    let [returned] = body.statements.nodes.as_slice() else {
        panic!("the getter has exactly one return");
    };
    let return_statement = node_ref(*returned);
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*returned).unwrap().data else {
        unreachable!();
    };
    Getter {
        object: node_ref(record.parent.unwrap()),
        declaration,
        name: node_ref(accessor.name),
        return_statement,
        expression: node_ref(returned.expression.unwrap()),
        annotation: accessor.type_.map(node_ref),
    }
}

fn source_members(
    parsed: &ParseResult,
    getter: Getter,
) -> Vec<(NodeRef, NodeRef, Option<NodeRef>)> {
    let NodeData::ObjectLiteralExpression(object) =
        &parsed.arena.get(getter.object.node).unwrap().data
    else {
        panic!("the getter belongs to the actual object literal");
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    object
        .properties
        .nodes
        .iter()
        .map(|&node| {
            let (name, initializer) = match &parsed.arena.get(node).unwrap().data {
                NodeData::PropertyAssignment(property) => {
                    (property.name, Some(property.initializer))
                }
                NodeData::GetAccessorDeclaration(accessor) => (accessor.name, None),
                _ => panic!("the control contains only eager properties and its getter"),
            };
            (node_ref(node), node_ref(name), initializer.map(node_ref))
        })
        .collect()
}

fn allocations(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct GetterState {
    object: TypeId,
    symbol: SemanticSymbolId,
    signature: SignatureId,
    read: TypeId,
    expression: TypeNodeLinks,
    expression_symbol: Option<SymbolNodeLinks>,
    value: ValueSymbolLinks,
    signature_links: SignatureLinks,
    members: Vec<SemanticSymbolId>,
}

fn getter_state(checker: &mut CanonicalCheckerContext<'_>, getter: Getter) -> GetterState {
    let object = checker.get_type_at_location(getter.object).unwrap();
    let symbol = checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(getter.declaration)
        .unwrap();
    assert_eq!(
        checker.get_symbol_at_location(getter.name),
        Ok(Some(symbol))
    );
    let signature_links = checker
        .store()
        .signature_links(getter.declaration)
        .unwrap()
        .clone();
    let signature = signature_links.resolved_signature.signature().unwrap();
    let before = allocations(checker);
    let read = checker.get_return_type_of_signature(signature).unwrap();
    assert_eq!(allocations(checker), before);
    let store = checker.store();
    let record = store.symbol(symbol).unwrap();
    assert_eq!(record.flags(), SymbolFlags::GET_ACCESSOR);
    assert_eq!(record.check_flags(), CheckFlags::NONE);
    assert_eq!(record.declarations(), Some(&[getter.declaration][..]));
    assert_eq!(record.value_declaration(), Some(getter.declaration));
    assert_eq!(
        record.parent(),
        store.type_payload(object).unwrap().symbol()
    );
    let signature_record = store.signature(signature).unwrap();
    assert_eq!(signature_record.flags(), SignatureFlags::NONE);
    assert_eq!(signature_record.declaration(), Some(getter.declaration));
    assert!(signature_record.parameters().is_empty());
    assert!(signature_record.type_parameters().is_empty());
    assert_eq!(signature_record.this_parameter(), None);
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    assert_eq!(signature_record.resolved_return_type(), Some(read));
    let value = store.value_symbol_links(symbol).unwrap().clone();
    assert_eq!(value.resolved_type, Some(read));
    assert_eq!(value.target, None);
    GetterState {
        object,
        symbol,
        signature,
        read,
        expression: store.type_node_links(getter.expression).unwrap().clone(),
        expression_symbol: store.symbol_node_links(getter.expression).cloned(),
        value,
        signature_links,
        members: store
            .type_payload(object)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .properties
            .clone()
            .unwrap(),
    }
}

fn assert_replay(checker: &mut CanonicalCheckerContext<'_>, getter: Getter, reads: &[NodeRef]) {
    let expected = getter_state(checker, getter);
    let types = reads
        .iter()
        .map(|&node| checker.get_type_at_location(node).unwrap())
        .collect::<Vec<_>>();
    let display = checker.type_to_string(expected.object).unwrap();
    let diagnostics = checker.diagnostics().clone();
    let before = allocations(checker);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(getter_state(checker, getter), expected);
        for (&node, &type_) in reads.iter().zip(&types) {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(checker.type_to_string(expected.object).unwrap(), display);
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(allocations(checker), before);
    }
}

#[test]
fn interleaved_getter_diagnostics_keep_source_member_indices() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "interface Shape { before: string; readonly middle: 2; after: boolean }\n",
        "const object: Shape = { before: 1, get middle() { return 2; }, after: 3 };",
    ));
    let mut checker = context(&library, &source);
    checker.check_source_file(FILE).unwrap();
    assert!(checker.global_type_diagnostics().next().is_none());
    let getter = getter(&source);
    let members = source_members(&source, getter);
    let state = getter_state(&mut checker, getter);
    assert_eq!(members.len(), 3);
    assert_eq!(state.members.len(), 3);
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
    for (index, (expected_name, expected_target)) in
        [("before", "string"), ("middle", "2"), ("after", "boolean")]
            .into_iter()
            .enumerate()
    {
        let (declaration, name_node, initializer) = members[index];
        assert_eq!(name(&source, name_node), expected_name);
        assert_eq!(initializer.is_none(), index == 1);
        let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
        let published = state.members[index];
        assert_eq!(
            checker.store().symbol(published).unwrap().name().as_utf8(),
            Some(expected_name)
        );
        if index == 1 {
            assert_eq!(published, raw);
            assert_eq!(published, state.symbol);
        } else {
            assert_ne!(published, raw);
            assert!(
                checker
                    .store()
                    .symbol(published)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::PROPERTY)
            );
        }
        let diagnostic = &diagnostics[index];
        assert_eq!(diagnostic.node, Some(name_node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Type 'number' is not assignable to type '{expected_target}'.")
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("each error must retain its expected Shape property");
        };
        let target_name = source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::PropertySignature(property) = &record.data else {
                    return None;
                };
                let node = NodeRef::new(source.arena.id(), FILE, property.name);
                (name(&source, node) == expected_name).then_some(node)
            })
            .unwrap();
        assert_eq!(related.node, Some(target_name));
        assert_eq!(related.diagnostic.code(), 6500);
        assert_eq!(related.diagnostic.arguments, [expected_name, "Shape"]);
    }
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(state.read, number);
    assert_eq!(
        checker
            .type_to_string(state.expression.resolved_type.unwrap())
            .unwrap(),
        "2"
    );
    assert_replay(&mut checker, getter, &[getter.expression]);
}

#[test]
fn const_object_keeps_eager_literals_and_widens_getter_returns() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "const object = { eager: 1, get current() { return 2; } } as const;\n",
        "const eager = object.eager; const current = object.current;",
    ));
    let mut checker = context(&library, &source);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let getter = getter(&source);
    let state = getter_state(&mut checker, getter);
    let eager = variable(&source, "eager").2.unwrap();
    let current = variable(&source, "current").2.unwrap();
    let eager_type = checker.get_type_at_location(eager).unwrap();
    assert_eq!(checker.type_to_string(eager_type).unwrap(), "1");
    assert_eq!(checker.get_type_at_location(current), Ok(state.read));
    assert_eq!(
        checker.get_symbol_at_location(current),
        Ok(Some(state.symbol))
    );
    assert_eq!(
        checker.type_to_string(state.object).unwrap(),
        "{ readonly eager: 1; readonly current: number; }"
    );
    assert!(
        checker
            .store()
            .symbol(state.members[0])
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    assert_replay(&mut checker, getter, &[eager, current, getter.expression]);
}

#[test]
fn generic_factory_getter_keeps_outer_observer_array_identity() {
    let library = parse_source_file(ES5);
    let source = parse_source_file(concat!(
        "interface Observer<T> { value: T }\n",
        "function createSubject<T>(initial: Observer<T>[]): { readonly observers: Observer<T>[] } {\n",
        "  let _observers: Observer<T>[] = initial;\n",
        "  return { get observers() { return _observers; } };\n",
        "}",
    ));
    let mut checker = context(&library, &source);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let getter = getter(&source);
    let state = getter_state(&mut checker, getter);
    let (local, _, _) = variable(&source, "_observers");
    let local_symbol = checker.file(FILE).unwrap().1.symbol(local).unwrap();
    assert_eq!(
        state.expression_symbol.as_ref().unwrap().resolved_symbol,
        Some(local_symbol)
    );
    assert_eq!(state.expression.resolved_type, Some(state.read));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(local_symbol)
            .unwrap()
            .resolved_type,
        Some(state.read)
    );
    let function = only_node(&source, SyntaxKind::FunctionDeclaration);
    let signature = checker
        .store()
        .signature_links(function)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let [outer_t] = checker
        .store()
        .signature(signature)
        .unwrap()
        .type_parameters()
    else {
        panic!("the factory must retain its one outer type parameter");
    };
    let outer_t = *outer_t;
    let TypeData::TypeReference(array) = checker.store().type_payload(state.read).unwrap().data()
    else {
        panic!("the getter must retain the real array reference");
    };
    assert_eq!(array.object.target, Some(checker.global_types().array_type));
    let [observer] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("the array must retain one Observer<T> element");
    };
    let TypeData::TypeReference(observer) = checker.store().type_payload(*observer).unwrap().data()
    else {
        panic!("the element must retain its generic Observer reference");
    };
    assert_eq!(
        observer.resolved_type_arguments.as_deref(),
        Some(&[outer_t][..])
    );
    assert_eq!(checker.type_to_string(state.read).unwrap(), "Observer<T>[]");
    assert_replay(&mut checker, getter, &[getter.expression]);
}

#[test]
fn written_getter_return_survives_body_and_later_assignment_errors() {
    let library = parse_source_file(ES5);
    for (prefix, expression, raw_display, source_display) in [
        ("", "'wrong'", "\"wrong\"", "string"),
        (
            "const values: number[] = [1];",
            "values",
            "number[]",
            "number[]",
        ),
    ] {
        let source = parse_source_file(&format!(
            "{prefix}\nconst object = {{ get count(): number {{ return {expression}; }} }};\n\
             const current = object.count;\nconst later: string = 1;"
        ));
        let mut checker = context(&library, &source);
        checker.check_source_file(FILE).unwrap();
        let getter = getter(&source);
        let state = getter_state(&mut checker, getter);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(state.read, number);
        assert_eq!(
            checker.get_type_from_type_node(getter.annotation.unwrap()),
            Ok(number)
        );
        let raw = state.expression.resolved_type.unwrap();
        assert_ne!(raw, number);
        assert_eq!(checker.type_to_string(raw).unwrap(), raw_display);
        if source_display == "number[]" {
            let TypeData::TypeReference(array) = checker.store().type_payload(raw).unwrap().data()
            else {
                panic!("the rejected return must retain its checked array edge");
            };
            assert_eq!(array.object.target, Some(checker.global_types().array_type));
            assert_eq!(
                array.resolved_type_arguments.as_deref(),
                Some(&[number][..])
            );
        }
        let current = variable(&source, "current").2.unwrap();
        assert_eq!(checker.get_type_at_location(current), Ok(number));
        assert_eq!(
            checker.get_symbol_at_location(current),
            Ok(Some(state.symbol))
        );
        let diagnostics = checker.diagnostics().as_slice();
        let [body, later] = diagnostics else {
            panic!("the getter mismatch must not skip the later diagnostic: {diagnostics:?}");
        };
        assert_eq!(body.node, Some(getter.return_statement));
        assert_eq!(body.diagnostic.code(), 2322);
        assert_eq!(
            body.diagnostic.render().unwrap(),
            format!("Type '{source_display}' is not assignable to type 'number'.")
        );
        assert_eq!(later.node, Some(variable(&source, "later").1));
        assert_eq!(later.diagnostic.code(), 2322);
        assert_eq!(
            later.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_replay(&mut checker, getter, &[getter.expression, current]);
    }
}

#[test]
fn getter_capture_keeps_eager_flow_and_restores_only_unstable_bindings() {
    let library = parse_source_file(ES5);
    for (case, text, declared_capture) in [
        (
            "const local",
            "const factory = <T>(seed: T): T => { const value: string | number = 1; const result = { now: value, get read() { return value; } }; return seed; };",
            false,
        ),
        (
            "private module let",
            "let value: string | number = 1; export default <T>(seed: T): T => { const result = { now: value, get read() { return value; } }; return seed; };",
            false,
        ),
        (
            "parameter after last write",
            "function factory(value: string | number): number { value = 1; const result = { now: value, get read() { return value; } }; return 1; }",
            false,
        ),
        (
            "parameter with later write",
            "function factory(value: string | number): number { value = 1; const result = { now: value, get read() { return value; } }; value = 'later'; return 1; }",
            true,
        ),
        (
            "var after eager truthy check",
            "var value: number | false = 1; export default <T>(seed: T): T => { const result = value && { now: value, get read() { return value; } }; return seed; };",
            true,
        ),
    ] {
        let source = parse_source_file(text);
        let mut checker = context(&library, &source);
        checker
            .check_source_file(FILE)
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert!(
            checker.diagnostics().is_empty(),
            "{case}: {:?}",
            checker.diagnostics()
        );
        let getter = getter(&source);
        let state = getter_state(&mut checker, getter);
        let members = source_members(&source, getter);
        let eager = members[0].2.unwrap();
        assert_eq!(name(&source, members[0].1), "now");
        assert_eq!(members[1].2, None);
        assert_eq!(state.members[1], state.symbol);
        let captured = state
            .expression_symbol
            .as_ref()
            .unwrap()
            .resolved_symbol
            .unwrap();
        assert_eq!(
            checker
                .store()
                .symbol_node_links(eager)
                .unwrap()
                .resolved_symbol,
            Some(captured),
            "{case}"
        );
        let declared = checker
            .store()
            .value_symbol_links(captured)
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(
            matches!(
                checker.store().type_payload(declared).unwrap().data(),
                TypeData::Union(_)
            ),
            "{case}"
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let expected = if declared_capture { declared } else { number };
        assert_eq!(state.expression.resolved_type, Some(expected), "{case}");
        assert_eq!(state.read, expected, "{case}");
        assert_eq!(checker.get_type_at_location(eager), Ok(number), "{case}");
        assert_replay(&mut checker, getter, &[eager, getter.expression]);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(captured)
                .unwrap()
                .resolved_type,
            Some(declared),
            "{case}"
        );
    }
}

#[test]
fn imported_getter_array_read_uses_an_already_checked_target() {
    let library = parse_source_file(ES5);
    let provider = parse_source_file(concat!(
        "const values: number[] = [1];\n",
        "export const object = { get values() { return values; } };",
    ));
    let importer =
        parse_source_file("import { object } from './getters'; const values = object.values;");
    let mut checker = context_with_importer(&library, &provider, Some(&importer));
    let getter = getter(&provider);
    assert!(
        checker
            .store()
            .signature_links(getter.declaration)
            .is_none()
    );

    checker.check_source_file(FILE).unwrap();
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    let target = getter_state(&mut checker, getter);
    checker.check_source_file(IMPORTER).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let access = importer
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                importer.arena.id(),
                IMPORTER,
                node,
            ))
        })
        .unwrap();
    assert_eq!(checker.get_type_at_location(access), Ok(target.read));
    assert_eq!(
        checker.get_symbol_at_location(access),
        Ok(Some(target.symbol))
    );
    assert_eq!(checker.type_to_string(target.read).unwrap(), "number[]");
    let TypeData::TypeReference(array) = checker.store().type_payload(target.read).unwrap().data()
    else {
        panic!("the import must retain the provider's array reference");
    };
    assert_eq!(array.object.target, Some(checker.global_types().array_type));
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some(&[number][..])
    );
    assert_replay(&mut checker, getter, &[getter.expression]);
    let before = allocations(&checker);
    for _ in 0..2 {
        checker.recheck_source_file(IMPORTER).unwrap();
        assert_eq!(checker.get_type_at_location(access), Ok(target.read));
        assert_eq!(
            checker.get_symbol_at_location(access),
            Ok(Some(target.symbol))
        );
        assert_eq!(getter_state(&mut checker, getter), target);
        assert_eq!(allocations(&checker), before);
        assert!(checker.diagnostics().is_empty());
    }
}
