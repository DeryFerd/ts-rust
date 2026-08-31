use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, SignatureId, SignatureLinks,
    SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks, signatures::SignatureFlags,
    type_records::StructuredTypeData,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_710);
const LIBRARY_FILE: FileId = FileId::new(202_711);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(
    parsed: &'a ParseResult,
    library: Option<&'a ParseResult>,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let mut files = Vec::new();
    if let Some(library) = library {
        files.push((library, LIBRARY_FILE, "\"/lib/lib.es5.d.ts\"", true));
    }
    files.push((
        parsed,
        FILE,
        "\"/project/class-named-method-returns.ts\"",
        false,
    ));
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
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(parsed, file, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_function_types: true,
            strict_property_initialization: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn named_declaration(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected)
                .then_some((reference(parsed, id), reference(parsed, name)))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

struct Method {
    class: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    text: String,
    parameters: Vec<NodeRef>,
    annotation: NodeRef,
    static_: bool,
}

fn method(parsed: &ParseResult, expected: &str) -> Method {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::MethodDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| Method {
                class: reference(parsed, record.parent.unwrap()),
                declaration: reference(parsed, id),
                name: reference(parsed, method.name),
                text: name.text.clone(),
                parameters: method
                    .parameters
                    .nodes
                    .iter()
                    .map(|&parameter| reference(parsed, parameter))
                    .collect(),
                annotation: reference(parsed, method.type_.unwrap()),
                static_: method.modifiers.as_ref().is_some_and(|modifiers| {
                    modifiers.list.nodes.iter().any(|&modifier| {
                        parsed.arena.get(modifier).unwrap().kind == SyntaxKind::StaticKeyword
                    })
                }),
            })
        })
        .unwrap_or_else(|| panic!("missing method {expected}"))
}

fn returned(parsed: &ParseResult, method: &Method) -> Option<(NodeRef, Option<NodeRef>)> {
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.declaration.node)?.data else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body?)?.data else {
        unreachable!()
    };
    let [statement] = body.statements.nodes.as_slice() else {
        assert!(body.statements.nodes.is_empty());
        return None;
    };
    let NodeData::ReturnStatement(data) = &parsed.arena.get(*statement)?.data else {
        panic!("the method must retain its real return statement")
    };
    Some((
        reference(parsed, *statement),
        data.expression.map(|node| reference(parsed, node)),
    ))
}

fn structured(data: &TypeData) -> &StructuredTypeData {
    match data {
        TypeData::Object(data) => &data.structured,
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        _ => panic!("expected the real class or method object"),
    }
}

fn check_in_order(
    context: &mut CanonicalCheckerContext<'_>,
    class_name: NodeRef,
    query_first: bool,
) {
    let file = context.source_file(FILE).unwrap();
    assert!(
        context
            .store()
            .source_file_links(file)
            .is_none_or(|links| !links.type_checked)
    );
    if query_first {
        context.get_type_at_location(class_name).unwrap();
    } else {
        context.check_source_file(FILE).unwrap();
    }
    assert!(
        context
            .store()
            .source_file_links(file)
            .unwrap()
            .type_checked
    );
}

#[allow(clippy::too_many_lines)] // Keep the real source, member table and signature checks together.
fn assert_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    expected_return: TypeId,
) -> (TypeId, SignatureId) {
    let owner = symbol(context, method.declaration);
    let class = symbol(context, method.class);
    let parameters = method
        .parameters
        .iter()
        .map(|&declaration| symbol(context, declaration))
        .collect::<Vec<_>>();
    let store = context.store();
    let member = store.symbol(owner).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.name().as_utf8(), Some(method.text.as_str()));
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.declarations(), Some(&[method.declaration][..]));
    assert_eq!(member.value_declaration(), Some(method.declaration));
    let class_type = if method.static_ {
        store
            .value_symbol_links(class)
            .unwrap()
            .resolved_type
            .unwrap()
    } else {
        store
            .declared_type_links(class)
            .unwrap()
            .declared_type
            .unwrap()
    };
    let members = structured(store.type_payload(class_type).unwrap().data())
        .members
        .unwrap();
    assert_eq!(
        store.symbol_table(members).unwrap().get(member.name()),
        Some(owner)
    );
    let callable = store
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let signature = store
        .signature_links(method.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the method must retain its callable object")
    };
    assert!(object.target.is_none());
    assert!(object.mapper.is_none());
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let record = store.signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), parameters);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_min_argument_count(), -1);
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert_eq!(record.resolved_return_type(), Some(expected_return));
    for (&declaration, &parameter) in method.parameters.iter().zip(&parameters) {
        let record = context.store().symbol(parameter).unwrap();
        assert_eq!(record.declarations(), Some(&[declaration][..]));
        assert_eq!(record.value_declaration(), Some(declaration));
        let NodeData::ParameterDeclaration(data) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let type_ = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context
                .get_type_from_type_node(reference(parsed, data.type_.unwrap()))
                .unwrap(),
            type_
        );
        assert_eq!(
            context
                .get_type_at_location(reference(parsed, data.name))
                .unwrap(),
            type_
        );
    }
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    assert_eq!(
        context.get_type_from_type_node(method.annotation).unwrap(),
        expected_return
    );
    assert_eq!(
        context.get_class_query_member_type(owner).unwrap(),
        callable
    );
    assert_eq!(context.get_type_at_location(method.name).unwrap(), callable);
    assert_eq!(
        context.get_return_type_of_signature(signature).unwrap(),
        expected_return
    );
    (callable, signature)
}

type NodePublication = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<TypeAliasLinks>,
);
type SignaturePublication = (
    SignatureId,
    Option<NodeRef>,
    SignatureFlags,
    Vec<SemanticSymbolId>,
    i32,
    Option<TypeId>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    signatures: Vec<SignaturePublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.properties_type_cache_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = reference(parsed, node);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
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
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect(),
        signatures: parsed
            .arena
            .iter()
            .filter_map(|(node, _)| {
                let signature = store
                    .signature_links(reference(parsed, node))?
                    .resolved_signature
                    .signature()?;
                let record = store.signature(signature)?;
                Some((
                    signature,
                    record.declaration(),
                    record.flags(),
                    record.parameters().to_vec(),
                    record.min_argument_count(),
                    record.resolved_return_type(),
                ))
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay<const N: usize>(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    methods: &[Method; N],
    returns: &[TypeId; N],
) {
    let identities = methods
        .iter()
        .zip(returns)
        .map(|(method, &returned)| assert_method(context, parsed, method, returned))
        .collect::<Vec<_>>();
    let warm = publication(context, parsed);
    for _ in 0..2 {
        for ((method, &returned), &expected) in methods.iter().zip(returns).zip(&identities) {
            assert_eq!(assert_method(context, parsed, method, returned), expected);
        }
        assert_eq!(publication(context, parsed), warm);
        context.check_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
    }
}

#[test]
fn named_method_returns_keep_source_owners_and_canonical_queries() {
    let source = concat!(
        "interface Payload { value: number; }\n",
        "type Mirror = Payload;\n",
        "class Receiver {\n",
        "  value: Payload;\n",
        "  constructor(value: Payload) { this.value = value; }\n",
        "  get(): Payload { return this.value; }\n",
        "  read(value: { value: number }): Payload { return value; }\n",
        "  static copy(value: { value: number }): Mirror { return value; }\n",
        "}\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, None);
        let (class, class_name) =
            named_declaration(&parsed, SyntaxKind::ClassDeclaration, "Receiver");
        let (payload, _) = named_declaration(&parsed, SyntaxKind::InterfaceDeclaration, "Payload");
        let (mirror, _) = named_declaration(&parsed, SyntaxKind::TypeAliasDeclaration, "Mirror");
        let methods = [
            method(&parsed, "get"),
            method(&parsed, "read"),
            method(&parsed, "copy"),
        ];
        assert_eq!(
            methods.each_ref().map(|method| method.parameters.len()),
            [0, 1, 1]
        );
        check_in_order(&mut context, class_name, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let payload_owner = symbol(&context, payload);
        let payload_type = context.get_declared_type_of_symbol(payload_owner).unwrap();
        assert_eq!(
            context.store().type_payload(payload_type).unwrap().symbol(),
            Some(payload_owner)
        );
        let mirror_owner = symbol(&context, mirror);
        assert_eq!(
            context.get_declared_type_of_symbol(mirror_owner).unwrap(),
            payload_type
        );
        let class_owner = symbol(&context, class);
        let field = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::PropertyDeclaration
                    && record.parent == Some(class.node))
                .then_some(reference(&parsed, node))
            })
            .unwrap();
        let field_owner = symbol(&context, field);
        assert_eq!(
            context.store().symbol(field_owner).unwrap().parent(),
            Some(class_owner)
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(field_owner)
                .unwrap()
                .resolved_type,
            Some(payload_type)
        );
        let (_, Some(read)) = returned(&parsed, &methods[0]).unwrap() else {
            unreachable!()
        };
        assert_eq!(context.get_type_at_location(read).unwrap(), payload_type);
        assert_eq!(
            context.get_symbol_at_location(read).unwrap(),
            Some(field_owner)
        );
        for method in &methods[1..] {
            let (_, Some(expression)) = returned(&parsed, method).unwrap() else {
                unreachable!()
            };
            let actual = context.get_type_at_location(expression).unwrap();
            assert!(context.is_type_assignable_to(actual, payload_type).unwrap());
        }
        assert_replay(&mut context, &parsed, &methods, &[payload_type; 3]);
    }
}

#[test]
fn named_method_array_alias_returns_keep_the_real_array_target() {
    let source = concat!(
        "type Names = string[];\n",
        "class Receiver {\n",
        "  read(values: string[]): Names { return values; }\n",
        "  static copy(values: string[]): Names { return values; }\n",
        "}\n",
    );
    let library = parse_source_file(ES5);
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, Some(&library));
        let (_, class_name) = named_declaration(&parsed, SyntaxKind::ClassDeclaration, "Receiver");
        let (names, _) = named_declaration(&parsed, SyntaxKind::TypeAliasDeclaration, "Names");
        let methods = [method(&parsed, "read"), method(&parsed, "copy")];
        check_in_order(&mut context, class_name, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let names_owner = symbol(&context, names);
        let result = context.get_declared_type_of_symbol(names_owner).unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let TypeData::TypeReference(array) = context.store().type_payload(result).unwrap().data()
        else {
            panic!("the named return must retain its canonical array reference")
        };
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some(&[string][..])
        );
        let target = array.target;
        let owner = context
            .store()
            .type_payload(target)
            .unwrap()
            .symbol()
            .unwrap();
        assert_eq!(
            context.store().symbol(owner).unwrap().name().as_utf8(),
            Some("Array")
        );
        let declarations = context
            .store()
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap();
        assert!(!declarations.is_empty());
        for &declaration in declarations {
            assert_eq!(declaration.file, LIBRARY_FILE);
            let NodeData::InterfaceDeclaration(data) =
                &library.arena.get(declaration.node).unwrap().data
            else {
                panic!("Array must come from its actual bundled interface")
            };
            let NodeData::Identifier(name) = &library.arena.get(data.name).unwrap().data else {
                unreachable!()
            };
            assert_eq!(name.text, "Array");
        }
        assert_eq!(context.get_declared_type_of_symbol(owner).unwrap(), target);
        for method in &methods {
            let (_, Some(expression)) = returned(&parsed, method).unwrap() else {
                unreachable!()
            };
            let actual = context.get_type_at_location(expression).unwrap();
            let TypeData::TypeReference(parameter) =
                context.store().type_payload(actual).unwrap().data()
            else {
                panic!("the method parameter must retain its written array")
            };
            assert_eq!(parameter.target, target);
            assert_eq!(
                parameter.resolved_type_arguments.as_deref(),
                Some(&[string][..])
            );
            assert!(context.is_type_assignable_to(actual, result).unwrap());
        }
        assert_replay(&mut context, &parsed, &methods, &[result; 2]);
    }
}

#[test]
fn named_alias_return_errors_keep_written_types_and_real_sites() {
    let source = concat!(
        "type Text = string;\n",
        "class Receiver {\n",
        "  wrong(): Text { return 1; }\n",
        "  bare(): Text { return; }\n",
        "  missing(): Text {}\n",
        "}\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, None);
        let (_, class_name) = named_declaration(&parsed, SyntaxKind::ClassDeclaration, "Receiver");
        let methods = [
            method(&parsed, "wrong"),
            method(&parsed, "bare"),
            method(&parsed, "missing"),
        ];
        check_in_order(&mut context, class_name, query_first);
        let sites = [
            returned(&parsed, &methods[0]).unwrap().0,
            returned(&parsed, &methods[1]).unwrap().0,
            methods[2].annotation,
        ];
        let expected: [(u32, &[&str], &str); 3] = [
            (
                2322,
                &["number", "string"],
                "Type 'number' is not assignable to type 'string'.",
            ),
            (
                2322,
                &["undefined", "string"],
                "Type 'undefined' is not assignable to type 'string'.",
            ),
            (
                2355,
                &[],
                "A function whose declared type is neither 'undefined', 'void', nor 'any' must return a value.",
            ),
        ];
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
        for ((diagnostic, &site), &(code, arguments, message)) in
            diagnostics.iter().zip(&sites).zip(&expected)
        {
            assert_eq!(diagnostic.node, Some(site));
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                arguments
                    .iter()
                    .map(|argument| (*argument).to_owned())
                    .collect::<Vec<_>>()
            );
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.diagnostic.details.is_empty());
            assert!(diagnostic.related_information.is_empty());
        }
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_replay(&mut context, &parsed, &methods, &[string; 3]);
    }
}

#[test]
fn named_method_returns_leave_generic_methods_unavailable() {
    let source = "type Text = string; class Receiver { read<T>(value: T): Text { return value; } }";
    let parsed = parse_source_file(source);
    let method = method(&parsed, "read");
    let mut context = context(&parsed, None);
    let cold = publication(&context, &parsed);
    let expected =
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(method.declaration));
    for _ in 0..2 {
        assert_eq!(context.check_source_file(FILE), Err(expected));
        assert_eq!(publication(&context, &parsed), cold);
        assert_eq!(context.recheck_source_file(FILE), Err(expected));
        assert_eq!(publication(&context, &parsed), cold);
    }
}
