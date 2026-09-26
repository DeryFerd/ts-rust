use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFlowGraph, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, RelationStateSnapshot, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_690);
const ES5_FILE: FileId = FileId::new(202_691);
const DOM_FILE: FileId = FileId::new(202_692);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DOM: &str = include_str!("../../ts_bundled/libs/lib.dom.d.ts");

// These are the unchanged fixture source units after the harness removes directives
// and normalizes line endings. The options below retain those directives.
const TYPEOF_SOURCE: &str = concat!(
    "// https://github.com/microsoft/typescript-go/issues/3909\n",
    "\n",
    "function f(x: string | number) {\n",
    "  switch (typeof x) {\n",
    "    case \"\":\n",
    "    case \"string\":\n",
    "      x.charAt(0);\n",
    "      break;\n",
    "  }\n",
    "}\n",
);
const REACHABILITY_SOURCE: &str = concat!(
    "// https://github.com/microsoft/TypeScript/issues/55562\n",
    "\n",
    "function g(str: string) {\n",
    "  switch (str) {\n",
    "    case \"a\":\n",
    "      return;\n",
    "      console.log(\"1\");\n",
    "      console.log(\"2\");\n",
    "    case \"b\":\n",
    "      console.log(\"3\");\n",
    "  }\n",
    "}\n",
    "\n",
    "function h(str: string) {\n",
    "  switch (str) {\n",
    "    case \"a\":\n",
    "      console.log(\"1\");\n",
    "    default:\n",
    "      return;\n",
    "      console.log(\"2\");\n",
    "      console.log(\"3\");\n",
    "    case \"b\":\n",
    "      console.log(\"4\");\n",
    "  }\n",
    "}\n",
);

fn options(allow_unreachable_code: Option<bool>) -> CanonicalCheckerOptions {
    // The pinned compiler defaults to strict checking and ES2025.
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            ..IntrinsicBootstrapOptions::default()
        },
        strict_bind_call_apply: true,
        strict_builtin_iterator_return: true,
        strict_function_types: true,
        strict_property_initialization: true,
        use_unknown_in_catch_variables: true,
        no_implicit_any: true,
        no_implicit_this: true,
        allow_unreachable_code,
        no_emit: true,
        check_bigint_target: true,
        ..CanonicalCheckerOptions::default()
    }
}

fn context<'a>(
    source: &'a ParseResult,
    es5: &'a ParseResult,
    dom: Option<&'a ParseResult>,
    source_path: &str,
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'a> {
    let mut files = vec![(es5, ES5_FILE, "\"/lib.es5.d.ts\"", true)];
    if let Some(dom) = dom {
        files.push((dom, DOM_FILE, "\"/lib.dom.d.ts\"", true));
    }
    files.push((source, FILE, source_path, false));
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
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for &(parsed, file, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let context = CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(parsed, file, _, _)| (file, &parsed.arena))
            .collect(),
        options,
    )
    .unwrap();
    assert_eq!(context.options(), options);
    context
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
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

fn source_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Clone, Copy, Debug)]
struct Access {
    statement: NodeRef,
    call: NodeRef,
    property: NodeRef,
    name: NodeRef,
    receiver: NodeRef,
    argument: NodeRef,
}

fn accesses(parsed: &ParseResult) -> Vec<Access> {
    let mut accesses = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::PropertyAccessExpression(property) =
                &parsed.arena.get(call.expression)?.data
            else {
                return None;
            };
            let [argument] = call.arguments.nodes.as_slice() else {
                panic!("the original calls each have one argument")
            };
            let statement = record.parent.unwrap();
            assert_eq!(
                parsed.arena.get(statement).unwrap().kind,
                SyntaxKind::ExpressionStatement
            );
            Some(Access {
                statement: node(parsed, FILE, statement),
                call: node(parsed, FILE, id),
                property: node(parsed, FILE, call.expression),
                name: node(parsed, FILE, property.name),
                receiver: node(parsed, FILE, property.expression),
                argument: node(parsed, FILE, *argument),
            })
        })
        .collect::<Vec<_>>();
    accesses.sort_by_key(|access| parsed.arena.get(access.call.node).unwrap().range.start);
    accesses
}

struct LibraryMethod {
    owner: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
}

impl LibraryMethod {
    fn nodes(&self) -> [NodeRef; 7] {
        [
            self.owner,
            self.declaration,
            self.name,
            self.parameter,
            self.parameter_name,
            self.parameter_annotation,
            self.return_annotation,
        ]
    }
}

fn library_method(
    parsed: &ParseResult,
    file: FileId,
    owner_name: &str,
    method_name: &str,
) -> LibraryMethod {
    for (owner, record) in parsed.arena.iter() {
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            continue;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(interface.name).unwrap().data else {
            unreachable!()
        };
        if name.text != owner_name {
            continue;
        }
        for &id in &interface.members.nodes {
            let NodeData::MethodSignatureDeclaration(method) = &parsed.arena.get(id).unwrap().data
            else {
                continue;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(method.name).unwrap().data else {
                continue;
            };
            if name.text != method_name {
                continue;
            }
            let [parameter] = method.parameters.nodes.as_slice() else {
                panic!("the selected library method has one written parameter")
            };
            let NodeData::ParameterDeclaration(data) = &parsed.arena.get(*parameter).unwrap().data
            else {
                unreachable!()
            };
            return LibraryMethod {
                owner: node(parsed, file, owner),
                declaration: node(parsed, file, id),
                name: node(parsed, file, method.name),
                parameter: node(parsed, file, *parameter),
                parameter_name: node(parsed, file, data.name),
                parameter_annotation: node(parsed, file, data.type_.unwrap()),
                return_annotation: node(parsed, file, method.type_.unwrap()),
            };
        }
    }
    panic!("missing real library method {owner_name}.{method_name}")
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
);
type SignaturePublication = (
    SignatureId,
    SignatureFlags,
    Option<NodeRef>,
    Vec<SemanticSymbolId>,
    i32,
    i32,
    Option<TypeId>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    relations: RelationStateSnapshot,
    flow: BoundFlowGraph,
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    signatures: Vec<SignaturePublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    method: &LibraryMethod,
) -> Publication {
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
        relations: store.relation_state_snapshot(),
        flow: context.file(FILE).unwrap().1.flow_graph().clone(),
        nodes: source
            .arena
            .iter()
            .map(|(id, _)| node(source, FILE, id))
            .chain(method.nodes())
            .map(|node| {
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
                )
            })
            .collect(),
        signatures: store
            .signatures()
            .map(|(signature, record)| {
                (
                    signature,
                    record.flags(),
                    record.declaration(),
                    record.parameters().to_vec(),
                    record.min_argument_count(),
                    record.resolved_min_argument_count(),
                    record.resolved_return_type(),
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn single_signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the method or source function keeps its canonical callable object")
    };
    let structured = &object.structured;
    assert_eq!(structured.call_signature_count, 1);
    let [signature] = structured.signatures.as_deref().unwrap() else {
        panic!("the real method has one call signature")
    };
    *signature
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MethodArtifact {
    type_: TypeId,
    signature: SignatureId,
    parameter: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the library method, parameter, and signature together.
fn assert_method(
    context: &mut CanonicalCheckerContext<'_>,
    method: &LibraryMethod,
    type_: TypeId,
    rest: bool,
) -> MethodArtifact {
    let owner = symbol(context, method.owner);
    let method_symbol = symbol(context, method.declaration);
    let parameter_symbol = symbol(context, method.parameter);
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().flags(),
        SymbolFlags::METHOD
    );
    assert_eq!(
        context
            .store()
            .symbol(method_symbol)
            .unwrap()
            .parent()
            .and_then(|parent| context.store().get_merged_symbol(parent)),
        Some(owner)
    );
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(method_symbol)
    );
    assert_eq!(
        context.get_symbol_declarations(method_symbol).unwrap(),
        &[method.declaration]
    );
    assert_eq!(
        context.get_symbol_declarations(parameter_symbol).unwrap(),
        &[method.parameter]
    );
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(method_symbol)
    );
    let parameter = context
        .get_type_from_type_node(method.parameter_annotation)
        .unwrap();
    assert_eq!(
        context.get_type_at_location(method.parameter_name).unwrap(),
        parameter
    );
    let return_type = context
        .get_type_from_type_node(method.return_annotation)
        .unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    if rest {
        let TypeData::TypeReference(array) =
            context.store().type_payload(parameter).unwrap().data()
        else {
            panic!("Console.log keeps its real any[] rest annotation")
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some(&[bootstrap.any_type][..])
        );
        assert_eq!(return_type, bootstrap.void_type);
    } else {
        assert_eq!(parameter, bootstrap.number_type);
        assert_eq!(return_type, bootstrap.string_type);
    }
    let signature = single_signature(context, type_);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.parameters(), [parameter_symbol]);
    assert_eq!(record.min_argument_count(), i32::from(!rest));
    assert_eq!(record.resolved_return_type(), Some(return_type));
    assert_eq!(
        record.flags(),
        if rest {
            SignatureFlags::HAS_REST_PARAMETER
        } else {
            SignatureFlags::NONE
        }
    );
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert_eq!(
        context
            .store()
            .signature_links(method.declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    for (symbol, expected) in [(method_symbol, type_), (parameter_symbol, parameter)] {
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(expected)
        );
    }
    MethodArtifact {
        type_,
        signature,
        parameter,
    }
}

fn assert_function(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    name: &str,
    display: &str,
) -> (TypeId, TypeId, SemanticSymbolId) {
    let (declaration, function) = source
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &source.arena.get(function.name?)?.data else {
                return None;
            };
            (identifier.text == name).then_some((node(source, FILE, id), function))
        })
        .unwrap();
    let [parameter] = function.parameters.nodes.as_slice() else {
        unreachable!()
    };
    let parameter = node(source, FILE, *parameter);
    let parameter_symbol = symbol(context, parameter);
    let parameter_type = context.get_type_at_location(parameter).unwrap();
    let type_ = context
        .get_type_at_location(node(source, FILE, function.name.unwrap()))
        .unwrap();
    assert_eq!(context.type_to_string(type_).unwrap(), display);
    let signature = single_signature(context, type_);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), [parameter_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(
        record.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().void_type)
    );
    assert_eq!(
        context.get_symbol_declarations(parameter_symbol).unwrap(),
        &[parameter]
    );
    (type_, parameter_type, parameter_symbol)
}

fn assert_typeof_diagnostic(context: &CanonicalCheckerContext<'_>, source: &ParseResult) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the original empty case has exactly one diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2678);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Type '\"\"' is not comparable to type '",
            "\"bigint\" | \"boolean\" | \"function\" | \"number\" | ",
            "\"object\" | \"string\" | \"symbol\" | \"undefined\"'.",
        )
    );
    let location = diagnostic.node.unwrap();
    assert_eq!(location.file, FILE);
    assert_eq!(
        source.arena.get(location.node).unwrap().kind,
        SyntaxKind::StringLiteral
    );
    let range = source.arena.get(location.node).unwrap().range;
    assert_eq!((range.start.get(), range.end.get()), (123, 125));
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
}

fn assert_reachability(context: &CanonicalCheckerContext<'_>, accesses: &[Access]) {
    assert_eq!(accesses.len(), 7);
    let flow = context.file(FILE).unwrap().1.flow_graph();
    assert!(flow.is_complete());
    for (access, unreachable) in accesses
        .iter()
        .zip([true, true, false, false, true, true, false])
    {
        assert_eq!(flow.is_unreachable(access.statement), Some(unreachable));
    }
    let [first, second] = context.diagnostics().as_slice() else {
        panic!("the original switches have two unreachable ranges")
    };
    for (diagnostic, start) in [(first, 134), (second, 335)] {
        assert_eq!(diagnostic.diagnostic.code(), 7027);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Unreachable code detected."
        );
        let range = diagnostic.range_override.unwrap();
        assert_eq!(Some(range.anchor()), diagnostic.node);
        assert_eq!(range.anchor().file, FILE);
        assert_eq!(
            (range.range().start.get(), range.range().end.get()),
            (start, start + 41)
        );
        assert!(diagnostic.related_information.is_empty());
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckOrder {
    Source,
    Property,
    PropertyName,
}

const CHECK_ORDERS: [CheckOrder; 3] = [
    CheckOrder::Source,
    CheckOrder::Property,
    CheckOrder::PropertyName,
];

fn start(
    context: &mut CanonicalCheckerContext<'_>,
    access: Access,
    order: CheckOrder,
) -> Option<TypeId> {
    assert!(!source_checked(context));
    let queried = match order {
        CheckOrder::Source => {
            context.check_source_file(FILE).unwrap();
            None
        }
        CheckOrder::Property => Some(context.get_type_at_location(access.property).unwrap()),
        CheckOrder::PropertyName => Some(context.get_type_at_location(access.name).unwrap()),
    };
    assert!(source_checked(context));
    queried
}

fn assert_typeof_artifacts(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    access: Access,
    method: &LibraryMethod,
) -> (MethodArtifact, TypeId, TypeId) {
    assert_typeof_diagnostic(context, source);
    let method_type = context.get_type_at_location(access.property).unwrap();
    assert_eq!(
        context.get_type_at_location(access.name).unwrap(),
        method_type
    );
    assert_eq!(
        context
            .type_to_string_at_location(method_type, access.property)
            .unwrap(),
        "(pos: number) => string"
    );
    let method_artifact = assert_method(context, method, method_type, false);
    let method_symbol = symbol(context, method.declaration);
    for location in [access.property, access.name] {
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(method_symbol)
        );
    }
    let (function, parameter_type, parameter_symbol) =
        assert_function(context, source, "f", "(x: string | number) => void");
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (string, number, typeof_type) = (
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.typeof_type,
    );
    let TypeData::Union(union) = context.store().type_payload(parameter_type).unwrap().data()
    else {
        panic!("the parameter keeps its written string | number type")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&string));
    assert!(union.union.types.contains(&number));
    for (id, record) in source.arena.iter() {
        let location = node(source, FILE, id);
        if let NodeData::Identifier(identifier) = &record.data
            && identifier.text == "x"
        {
            assert_eq!(
                context.get_type_at_location(location).unwrap(),
                if location == access.receiver {
                    string
                } else {
                    parameter_type
                }
            );
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(parameter_symbol)
            );
        }
        if record.kind == SyntaxKind::TypeOfExpression {
            assert_eq!(context.get_type_at_location(location).unwrap(), typeof_type);
        }
    }
    assert_eq!(context.get_type_at_location(access.call).unwrap(), string);
    assert_eq!(
        context
            .store()
            .signature_links(access.call)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(method_artifact.signature)
    );
    let argument = context.get_type_at_location(access.argument).unwrap();
    assert_eq!(context.type_to_string(argument).unwrap(), "0");
    assert_eq!(
        context
            .file(FILE)
            .unwrap()
            .1
            .flow_graph()
            .is_unreachable(access.statement),
        Some(false)
    );
    (method_artifact, function, parameter_type)
}

#[test]
fn typeof_switch_property_artifacts_keep_the_checked_string_branch() {
    let es5 = parse_source_file(ES5);
    let source = parse_source_file(TYPEOF_SOURCE);
    let all_accesses = accesses(&source);
    let [access] = all_accesses.as_slice() else {
        panic!("the original typeof switch has one method call")
    };
    let access = *access;
    let method = library_method(&es5, ES5_FILE, "String", "charAt");
    for order in CHECK_ORDERS {
        let mut context = context(
            &source,
            &es5,
            None,
            "\"/.src/typeofSwitchEmptyStringCase.ts\"",
            options(None),
        );
        let first = start(&mut context, access, order);
        let identities = assert_typeof_artifacts(&mut context, &source, access, &method);
        if let Some(first) = first {
            assert_eq!(first, identities.0.type_);
        }
        let warm = publication(&context, &source, &method);
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_typeof_artifacts(&mut context, &source, access, &method),
                identities
            );
            assert_eq!(publication(&context, &source, &method), warm);
        }
    }
}

fn assert_console_artifacts(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    accesses: &[Access],
    method: &LibraryMethod,
) -> (MethodArtifact, TypeId, TypeId, TypeId) {
    assert_reachability(context, accesses);
    let method_type = context.get_type_at_location(accesses[0].property).unwrap();
    let artifact = assert_method(context, method, method_type, true);
    let method_symbol = symbol(context, method.declaration);
    let owner = symbol(context, method.owner);
    let console_type = context.get_type_at_location(accesses[0].receiver).unwrap();
    assert_eq!(context.type_to_string(console_type).unwrap(), "Console");
    assert_eq!(
        context.store().type_payload(console_type).unwrap().symbol(),
        Some(owner)
    );
    let console_symbol = context
        .get_symbol_at_location(accesses[0].receiver)
        .unwrap()
        .unwrap();
    let console_declarations = context.get_symbol_declarations(console_symbol).unwrap();
    assert_eq!(console_declarations.len(), 1);
    assert_eq!(console_declarations[0].file, DOM_FILE);
    let void = context.store().intrinsic_bootstrap().unwrap().void_type;
    for (access, text) in accesses.iter().zip(["1", "2", "3", "1", "2", "3", "4"]) {
        for location in [access.property, access.name] {
            assert_eq!(context.get_type_at_location(location).unwrap(), method_type);
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(method_symbol)
            );
            assert_eq!(
                context
                    .type_to_string_at_location(method_type, location)
                    .unwrap(),
                "(...data: any[]) => void"
            );
        }
        assert_eq!(
            context.get_type_at_location(access.receiver).unwrap(),
            console_type
        );
        assert_eq!(
            context.get_symbol_at_location(access.receiver).unwrap(),
            Some(console_symbol)
        );
        assert_eq!(context.get_type_at_location(access.call).unwrap(), void);
        let literal = context.get_type_at_location(access.argument).unwrap();
        assert_eq!(
            context.type_to_string(literal).unwrap(),
            format!("\"{text}\"")
        );
    }
    let (g, g_parameter, _) = assert_function(context, source, "g", "(str: string) => void");
    let (h, h_parameter, _) = assert_function(context, source, "h", "(str: string) => void");
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(g_parameter, string);
    assert_eq!(h_parameter, string);
    let members = context.store().symbol(owner).unwrap().members().unwrap();
    let count = context
        .store()
        .symbol_table(members)
        .unwrap()
        .get_source("count")
        .unwrap();
    assert!(
        context
            .store()
            .value_symbol_links(count)
            .and_then(|links| links.resolved_type)
            .is_none(),
        "querying log does not resolve an unrelated Console method"
    );
    assert_reachability(context, accesses);
    (artifact, console_type, g, h)
}

#[test]
fn console_property_artifacts_keep_unreachable_calls_and_real_method_identity() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let source = parse_source_file(REACHABILITY_SOURCE);
    let accesses = accesses(&source);
    assert_eq!(accesses.len(), 7);
    let method = library_method(&dom, DOM_FILE, "Console", "log");
    for order in CHECK_ORDERS {
        let mut context = context(
            &source,
            &es5,
            Some(&dom),
            "\"/.src/reachabilityChecks9.ts\"",
            options(Some(false)),
        );
        // Property-first starts after a return. Name-first starts in the next case.
        let first_access = if order == CheckOrder::PropertyName {
            accesses[2]
        } else {
            accesses[0]
        };
        let first = start(&mut context, first_access, order);
        if order == CheckOrder::Source {
            let owner = symbol(&context, method.owner);
            assert!(
                context
                    .store()
                    .declared_type_links(owner)
                    .and_then(|links| links.declared_type)
                    .is_none()
            );
        }
        let identities = assert_console_artifacts(&mut context, &source, &accesses, &method);
        if let Some(first) = first {
            assert_eq!(first, identities.0.type_);
        }
        let warm = publication(&context, &source, &method);
        for _ in 0..2 {
            for access in accesses.iter().rev() {
                assert_eq!(
                    context.get_type_at_location(access.name).unwrap(),
                    identities.0.type_
                );
            }
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_console_artifacts(&mut context, &source, &accesses, &method),
                identities
            );
            assert_eq!(publication(&context, &source, &method), warm);
        }
    }
}
