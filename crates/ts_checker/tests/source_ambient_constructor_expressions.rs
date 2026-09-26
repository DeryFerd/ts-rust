use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalGlobalTypes, DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureId,
    SignatureLinks, SourceCheckError, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    UnsupportedSourceSyntax, ValueSymbolLinks, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(261_200);
const SOURCE_FILE: FileId = FileId::new(261_201);

const GLOBALS: &str = concat!(
    "interface IArguments {} ",
    "interface Array<T> { length: number; [index: number]: T; } ",
    "interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } ",
    "interface Object {} interface Function {} ",
    "interface CallableFunction {} interface NewableFunction {} ",
    "interface String {} interface Number {} interface Boolean {} ",
    "interface RegExp {} interface ThisType<T> {} ",
);

// These real declaration controls do not replace the full Node/DOM input.
const BUILD_LIBRARY: &str = concat!(
    "interface BuildResult { body: string; }\n",
    "interface HeaderBag { token: string; }\n",
    "interface BuildInit { status?: number; headers?: HeaderBag; labels?: string[]; }\n",
    "declare var BuildValue: {\n",
    "  prototype: BuildResult;\n",
    "  new(body?: string, init?: BuildInit): BuildResult;\n",
    "  empty(): BuildResult;\n",
    "};\n",
    "declare var RequiredBuild: {\n",
    "  prototype: BuildResult;\n",
    "  new(body: string, init: BuildInit): BuildResult;\n",
    "};\n",
);

const OVERLOAD_LIBRARY: &str = concat!(
    "interface TextResult { text: string; }\n",
    "interface ReadyResult { ready: boolean; }\n",
    "interface CountResult { count: number; }\n",
    "declare var ChoiceValue: {\n",
    "  prototype: TextResult;\n",
    "  new(value: string): TextResult;\n",
    "  new(value: 'ready'): ReadyResult;\n",
    "  new(value: number): CountResult;\n",
    "  empty(): TextResult;\n",
    "};\n",
);

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration) in [
        (library, LIBRARY_FILE, "\"/lib/constructors.d.ts\"", true),
        (source, SOURCE_FILE, "\"/project/constructions.ts\"", false),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    declaration,
                    CanonicalModuleState::Script,
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (parsed, file) in [(library, LIBRARY_FILE), (source, SOURCE_FILE)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &source.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((record.range.start, node(parsed, file, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    let found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::MethodDeclaration(data) => data.name,
                NodeData::PropertyDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [found] = found.as_slice() else {
        panic!("expected one {kind:?} named {name}, got {found:?}")
    };
    *found
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

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature_at(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn annotation(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a variable declaration")
    };
    node(parsed, declaration.file, data.type_.unwrap())
}

fn initializer(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a variable declaration")
    };
    node(parsed, declaration.file, data.initializer.unwrap())
}

fn new_parts(parsed: &ParseResult, construction: NodeRef) -> (NodeRef, Vec<NodeRef>) {
    let NodeData::NewExpression(data) = &parsed.arena.get(construction.node).unwrap().data else {
        panic!("expected the real NewExpression")
    };
    (
        node(parsed, construction.file, data.expression),
        data.arguments
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|&id| node(parsed, construction.file, id))
            .collect(),
    )
}

fn construct_declarations(parsed: &ParseResult, annotation: NodeRef) -> Vec<NodeRef> {
    let NodeData::TypeLiteralNode(data) = &parsed.arena.get(annotation.node).unwrap().data else {
        panic!("the library value must keep its full TypeLiteral annotation")
    };
    data.members
        .nodes
        .iter()
        .filter(|&&id| parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
        .map(|&id| node(parsed, annotation.file, id))
        .collect()
}

fn declared_type(
    context: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    name: &str,
) -> TypeId {
    let declaration = named(
        library,
        LIBRARY_FILE,
        SyntaxKind::InterfaceDeclaration,
        name,
    );
    let owner = symbol(context, declaration);
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    type_
}

fn assert_construct_signature(
    context: &CanonicalCheckerContext<'_>,
    library: &ParseResult,
    declaration: NodeRef,
    result: TypeId,
    optional: bool,
) -> SignatureId {
    let NodeData::ConstructSignatureDeclaration(data) =
        &library.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a construct signature declaration")
    };
    let signature = signature_at(context, declaration);
    let record = context.store().signature(signature).unwrap();
    assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
    assert!(
        !record
            .flags()
            .intersects(SignatureFlags::ABSTRACT | SignatureFlags::HAS_REST_PARAMETER)
    );
    assert_eq!(record.declaration(), Some(declaration));
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert_eq!(record.resolved_return_type(), Some(result));
    assert_eq!(
        cached_type(context, node(library, LIBRARY_FILE, data.type_.unwrap())),
        result
    );
    assert_eq!(record.parameters().len(), data.parameters.nodes.len());
    assert_eq!(
        record.min_argument_count(),
        if optional {
            0
        } else {
            i32::try_from(data.parameters.nodes.len()).unwrap()
        },
    );
    for (&parameter, &id) in record.parameters().iter().zip(&data.parameters.nodes) {
        let declaration = node(library, LIBRARY_FILE, id);
        assert_eq!(symbol(context, declaration), parameter);
        let NodeData::ParameterDeclaration(data) = &library.arena.get(id).unwrap().data else {
            panic!("expected the written parameter")
        };
        assert_eq!(data.question_token.is_some(), optional);
        let intrinsic = context.store().intrinsic_bootstrap().unwrap();
        let written = match library.arena.get(data.type_.unwrap()).unwrap().kind {
            SyntaxKind::StringKeyword => intrinsic.string_type,
            SyntaxKind::NumberKeyword => intrinsic.number_type,
            _ => cached_type(context, node(library, LIBRARY_FILE, data.type_.unwrap())),
        };
        let value = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        if optional {
            let TypeData::Union(union) = context.store().type_payload(value).unwrap().data() else {
                panic!("the optional parameter must keep its undefined union")
            };
            let mut expected = [
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_type,
                written,
            ];
            expected.sort_unstable();
            assert_eq!(union.union.types, expected);
        } else {
            assert_eq!(value, written);
        }
    }
    signature
}

fn assert_value_members(context: &CanonicalCheckerContext<'_>, value: TypeId, result: TypeId) {
    let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
        panic!("the constructor value must remain the declared object, not its return")
    };
    assert_eq!(object.structured.call_signature_count, 0);
    let members = context
        .store()
        .symbol_table(object.structured.members.unwrap())
        .unwrap();
    let prototype = members.get_source("prototype").unwrap();
    let prototype_symbol = context.store().symbol(prototype).unwrap();
    assert!(
        !prototype_symbol
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(prototype)
            .unwrap()
            .resolved_type,
        Some(result)
    );
    let method = members.get_source("empty").unwrap();
    assert!(
        context
            .store()
            .symbol(method)
            .unwrap()
            .flags()
            .contains(SymbolFlags::METHOD)
    );
    assert!(
        context
            .store()
            .value_symbol_links(method)
            .unwrap()
            .resolved_type
            .is_some()
    );
}

fn assert_new_identity(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    construction: NodeRef,
    owner: SemanticSymbolId,
    value: TypeId,
    signature: SignatureId,
    result: TypeId,
) {
    let (constructor, _) = new_parts(source, construction);
    assert_ne!(value, result);
    assert_eq!(
        context
            .store()
            .symbol_node_links(constructor)
            .unwrap()
            .resolved_symbol,
        Some(owner)
    );
    assert_eq!(cached_type(context, constructor), value);
    assert_eq!(signature_at(context, construction), signature);
    assert_eq!(cached_type(context, construction), result);
    assert_eq!(context.get_type_at_location(construction).unwrap(), result);
    assert_eq!(context.get_type_at_location(constructor).unwrap(), value);
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    signature: Option<SignatureLinks>,
    symbol: Option<SymbolNodeLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct ReplayState {
    counts: [usize; 5],
    globals: CanonicalGlobalTypes,
    types: String,
    signatures: String,
    nodes: Vec<NodeState>,
    symbols: Vec<(
        SemanticSymbolId,
        Option<ValueSymbolLinks>,
        Option<DeclaredTypeLinks>,
    )>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn replay_state(
    context: &CanonicalCheckerContext<'_>,
    library: &ParseResult,
    source: &ParseResult,
) -> ReplayState {
    let store = context.store();
    let mut nodes = Vec::new();
    let mut symbols = Vec::new();
    for (parsed, file) in [(library, LIBRARY_FILE), (source, SOURCE_FILE)] {
        let bound = context.file(file).unwrap().1;
        for (id, _) in parsed.arena.iter() {
            let node = node(parsed, file, id);
            nodes.push(NodeState {
                node,
                type_: store.type_node_links(node).cloned(),
                signature: store.signature_links(node).cloned(),
                symbol: store.symbol_node_links(node).cloned(),
            });
            if let Some(raw) = bound.symbol(node) {
                symbols.push(store.get_merged_symbol(raw).unwrap());
            }
        }
    }
    symbols.sort_unstable();
    symbols.dedup();
    ReplayState {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        ],
        globals: context.global_types().clone(),
        types: format!("{:?}", store.types().collect::<Vec<_>>()),
        signatures: format!("{:?}", store.signatures().collect::<Vec<_>>()),
        nodes,
        symbols: symbols
            .into_iter()
            .map(|symbol| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                )
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    source: &ParseResult,
) {
    let before = replay_state(context, library, source);
    for _ in 0..2 {
        for construction in nodes(source, SOURCE_FILE, SyntaxKind::NewExpression) {
            let (constructor, _) = new_parts(source, construction);
            for node in [construction, constructor] {
                let expected = cached_type(context, node);
                assert_eq!(context.get_type_at_location(node).unwrap(), expected);
            }
        }
        assert_eq!(replay_state(context, library, source), before);
        context.check_source_file(SOURCE_FILE).unwrap();
        assert_eq!(replay_state(context, library, source), before);
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(replay_state(context, library, source), before);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both orders retain the complete class and library identities.
fn ambient_constructor_expressions_keep_class_positions_and_optional_argument_identity() {
    let library = parse_source_file(&format!("{GLOBALS}{BUILD_LIBRARY}"));
    let source = parse_source_file(
        r#"class Builder {
  body!: string;
  status!: number;
  headers!: HeaderBag;
  labels!: string[];
  bodyText(): string { return this.body; }
  local(flag: boolean): BuildResult {
    if (flag) {
      const result = new BuildValue(this.body, { status: this.status, headers: this.headers, labels: this.labels });
      return result;
    }
    return new BuildValue(this.body);
  }
  direct(): BuildResult { return new BuildValue(this.bodyText(), { status: this.status }); }
  empty(): BuildResult { return new BuildValue(); }
  single(): BuildResult { return new BuildValue(this.body); }
}
declare const builder: Builder;
const local = builder.local(true);
const direct = builder.direct();
const empty = builder.empty();
const single = builder.single();
const body = local.body;
"#,
    );
    let declaration = named(
        &library,
        LIBRARY_FILE,
        SyntaxKind::VariableDeclaration,
        "BuildValue",
    );
    let literal = annotation(&library, declaration);
    let constructors = construct_declarations(&library, literal);
    let [constructor] = constructors.as_slice() else {
        panic!("the library has one visible construct signature")
    };
    let constructions = nodes(&source, SOURCE_FILE, SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), 5);
    let local_result = named(
        &source,
        SOURCE_FILE,
        SyntaxKind::VariableDeclaration,
        "result",
    );
    assert_eq!(initializer(&source, local_result), constructions[0]);
    let declaration_list = source.arena.get(local_result.node).unwrap().parent.unwrap();
    assert_eq!(
        source.arena.get(declaration_list).unwrap().kind,
        SyntaxKind::VariableDeclarationList
    );
    let statement = source.arena.get(declaration_list).unwrap().parent.unwrap();
    assert_eq!(
        source.arena.get(statement).unwrap().kind,
        SyntaxKind::VariableStatement
    );
    let block = source.arena.get(statement).unwrap().parent.unwrap();
    assert_eq!(source.arena.get(block).unwrap().kind, SyntaxKind::Block);
    assert_eq!(
        source
            .arena
            .get(source.arena.get(block).unwrap().parent.unwrap())
            .unwrap()
            .kind,
        SyntaxKind::IfStatement
    );
    for construction in &constructions[1..] {
        let parent = source.arena.get(construction.node).unwrap().parent.unwrap();
        assert_eq!(
            source.arena.get(parent).unwrap().kind,
            SyntaxKind::ReturnStatement
        );
    }

    for annotation_first in [false, true] {
        let mut context = context(&library, &source);
        let options = context.options();
        let array = context.global_types().array_type;
        let owner = symbol(&context, declaration);
        assert!(
            !context
                .store()
                .symbol(owner)
                .unwrap()
                .flags()
                .contains(SymbolFlags::CLASS)
        );
        let early = annotation_first.then(|| context.get_type_from_type_node(literal).unwrap());

        context.check_source_file(SOURCE_FILE).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let value = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(context.get_type_from_type_node(literal).unwrap(), value);
        if let Some(early) = early {
            assert_eq!(early, value);
        }
        let result = declared_type(&mut context, &library, "BuildResult");
        let signature = assert_construct_signature(&context, &library, *constructor, result, true);
        let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
            panic!("the full constructor literal must remain an object")
        };
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some([signature].as_slice())
        );
        assert_value_members(&context, value, result);
        for &construction in &constructions {
            assert_new_identity(
                &mut context,
                &source,
                construction,
                owner,
                value,
                signature,
                result,
            );
        }
        let (_, arguments) = new_parts(&source, constructions[0]);
        assert_eq!(arguments.len(), 2);
        assert_eq!(
            cached_type(&context, arguments[0]),
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        let NodeData::ObjectLiteralExpression(init) =
            &source.arena.get(arguments[1].node).unwrap().data
        else {
            panic!("the init argument must remain its real object literal")
        };
        assert_eq!(init.properties.nodes.len(), 3);
        let NodeData::PropertyAssignment(labels) =
            &source.arena.get(init.properties.nodes[2]).unwrap().data
        else {
            panic!("the third init property must retain its labels initializer")
        };
        let labels = cached_type(&context, node(&source, SOURCE_FILE, labels.initializer));
        let TypeData::TypeReference(reference) =
            context.store().type_payload(labels).unwrap().data()
        else {
            panic!("the labels argument must retain its canonical Array reference")
        };
        assert_eq!(reference.object.target, Some(array));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some([context.store().intrinsic_bootstrap().unwrap().string_type].as_slice())
        );
        let headers = declared_type(&mut context, &library, "HeaderBag");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let TypeData::Object(init_type) = context
            .store()
            .type_payload(cached_type(&context, arguments[1]))
            .unwrap()
            .data()
        else {
            panic!("the checked init argument must retain its own object type")
        };
        let members = context
            .store()
            .symbol_table(init_type.structured.members.unwrap())
            .unwrap();
        for (&id, (name, expected)) in init.properties.nodes.iter().zip([
            ("status", number),
            ("headers", headers),
            ("labels", labels),
        ]) {
            let NodeData::PropertyAssignment(property) = &source.arena.get(id).unwrap().data else {
                panic!("the init argument must retain all three property assignments")
            };
            let NodeData::Identifier(written_name) = &source.arena.get(property.name).unwrap().data
            else {
                panic!("each init property has a written identifier name")
            };
            assert_eq!(written_name.text, name);
            let field = named(&source, SOURCE_FILE, SyntaxKind::PropertyDeclaration, name);
            let field = symbol(&context, field);
            let property_symbol = members.get_source(name).unwrap();
            assert_eq!(
                property_symbol,
                symbol(&context, node(&source, SOURCE_FILE, id))
            );
            assert_ne!(property_symbol, field);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(field)
                    .unwrap()
                    .resolved_type,
                Some(expected)
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(property_symbol)
                    .unwrap()
                    .resolved_type,
                Some(expected)
            );
            assert_eq!(
                cached_type(&context, node(&source, SOURCE_FILE, property.initializer)),
                expected
            );
        }
        let call_argument = new_parts(&source, constructions[2]).1[0];
        assert_eq!(
            source.arena.get(call_argument.node).unwrap().kind,
            SyntaxKind::CallExpression
        );
        let body_text = named(
            &source,
            SOURCE_FILE,
            SyntaxKind::MethodDeclaration,
            "bodyText",
        );
        assert_eq!(
            signature_at(&context, call_argument),
            signature_at(&context, body_text)
        );
        assert_eq!(
            cached_type(&context, call_argument),
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol(&context, local_result))
                .unwrap()
                .resolved_type,
            Some(result)
        );
        for name in ["local", "direct", "empty", "single"] {
            let variable = named(&source, SOURCE_FILE, SyntaxKind::VariableDeclaration, name);
            assert_eq!(
                context
                    .get_type_at_location(initializer(&source, variable))
                    .unwrap(),
                result
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol(&context, variable))
                    .unwrap()
                    .resolved_type,
                Some(result)
            );
        }
        let body = named(
            &source,
            SOURCE_FILE,
            SyntaxKind::VariableDeclaration,
            "body",
        );
        assert_eq!(
            context
                .get_type_at_location(initializer(&source, body))
                .unwrap(),
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        assert_eq!(context.options(), options);
        assert_eq!(context.global_types().array_type, array);
        assert_replay(&mut context, &library, &source);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each diagnostic keeps its actual argument and source order.
fn ambient_constructor_expressions_keep_diagnostic_order_and_ranges() {
    let library = parse_source_file(&format!("{GLOBALS}{BUILD_LIBRARY}"));
    let source = parse_source_file(
        r#"class InvalidBuilder {
  body!: string;
  wrong!: number;
  status!: number;
  wrongBody(): BuildResult { return new BuildValue(this.wrong, {}); }
  optionalExcess(): BuildResult { return new BuildValue(this.body, { status: this.status, extra: 1 }); }
  requiredExcess(): BuildResult { return new RequiredBuild(this.body, { status: this.status, extra: 1 }); }
  extraArgument(): BuildResult { return new BuildValue(this.body, {}, true); }
}
"#,
    );
    let constructions = nodes(&source, SOURCE_FILE, SyntaxKind::NewExpression);
    let [wrong, optional_excess, required_excess, extra] = constructions.as_slice() else {
        panic!("the complete source has four wrong constructions")
    };
    let optional_decl = named(
        &library,
        LIBRARY_FILE,
        SyntaxKind::VariableDeclaration,
        "BuildValue",
    );
    let required_decl = named(
        &library,
        LIBRARY_FILE,
        SyntaxKind::VariableDeclaration,
        "RequiredBuild",
    );

    for annotation_first in [false, true] {
        let mut context = context(&library, &source);
        if annotation_first {
            context
                .get_type_from_type_node(annotation(&library, optional_decl))
                .unwrap();
            context
                .get_type_from_type_node(annotation(&library, required_decl))
                .unwrap();
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        let [body, optional, required, arity] = diagnostics else {
            panic!("expected four ordered argument diagnostics, got {diagnostics:?}")
        };
        assert_eq!(
            diagnostics.iter().map(|diagnostic| (diagnostic.diagnostic.code(), diagnostic.diagnostic.render().unwrap())).collect::<Vec<_>>(),
            [
                (2345, "Argument of type 'number' is not assignable to parameter of type 'string | undefined'.".to_owned()),
                // The existing diagnostic reader does not peel the optional union.
                (2345, "Argument of type '{ status: number; extra: number; }' is not assignable to parameter of type 'BuildInit | undefined'.".to_owned()),
                (2353, "Object literal may only specify known properties, and 'extra' does not exist in type 'BuildInit'.".to_owned()),
                (2554, "Expected 0-2 arguments, but got 3.".to_owned()),
            ],
        );
        assert_eq!(body.node, Some(new_parts(&source, *wrong).1[0]));
        assert_eq!(
            optional.node,
            Some(new_parts(&source, *optional_excess).1[1])
        );
        let required_object = new_parts(&source, *required_excess).1[1];
        let NodeData::ObjectLiteralExpression(object) =
            &source.arena.get(required_object.node).unwrap().data
        else {
            panic!("expected the complete init object")
        };
        let NodeData::PropertyAssignment(property) =
            &source.arena.get(object.properties.nodes[1]).unwrap().data
        else {
            panic!("expected the excess property")
        };
        assert_eq!(
            required.node,
            Some(node(&source, SOURCE_FILE, property.name))
        );
        for diagnostic in [body, optional, required] {
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
        }
        assert_eq!(arity.node, Some(*extra));
        let range = arity.range_override.unwrap();
        assert_eq!(range.anchor(), *extra);
        let extra_argument = new_parts(&source, *extra).1[2];
        assert_eq!(
            range.range(),
            source.arena.get(extra_argument.node).unwrap().range
        );
        assert!(arity.related_information.is_empty());

        let result = declared_type(&mut context, &library, "BuildResult");
        for (&construction, declaration) in
            constructions
                .iter()
                .zip([optional_decl, optional_decl, required_decl, optional_decl])
        {
            let owner = symbol(&context, declaration);
            let value = context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap();
            let declarations = construct_declarations(&library, annotation(&library, declaration));
            let [construct] = declarations.as_slice() else {
                panic!("each diagnostic uses one actual public construct signature")
            };
            let signature = assert_construct_signature(
                &context,
                &library,
                *construct,
                result,
                declaration == optional_decl,
            );
            assert_new_identity(
                &mut context,
                &source,
                construction,
                owner,
                value,
                signature,
                result,
            );
        }
        assert_replay(&mut context, &library, &source);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both orders keep three original construct returns distinct.
fn ambient_constructor_overloads_keep_selected_construct_returns() {
    let library = parse_source_file(&format!("{GLOBALS}{OVERLOAD_LIBRARY}"));
    let source = parse_source_file(
        r#"class Chooser {
  text!: string;
  count!: number;
  literal(): ReadyResult { return new ChoiceValue('ready'); }
  general(): TextResult { const result = new ChoiceValue(this.text); return result; }
  numeric(): CountResult { return new ChoiceValue(this.count); }
}
declare const chooser: Chooser;
const ready = chooser.literal();
const text = chooser.general();
const count = chooser.numeric();
"#,
    );
    let declaration = named(
        &library,
        LIBRARY_FILE,
        SyntaxKind::VariableDeclaration,
        "ChoiceValue",
    );
    let literal = annotation(&library, declaration);
    let declarations = construct_declarations(&library, literal);
    assert_eq!(declarations.len(), 3);
    let constructions = nodes(&source, SOURCE_FILE, SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), 3);

    for annotation_first in [false, true] {
        let mut context = context(&library, &source);
        if annotation_first {
            context.get_type_from_type_node(literal).unwrap();
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let owner = symbol(&context, declaration);
        let value = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(context.get_type_from_type_node(literal).unwrap(), value);
        let results = [
            declared_type(&mut context, &library, "TextResult"),
            declared_type(&mut context, &library, "ReadyResult"),
            declared_type(&mut context, &library, "CountResult"),
        ];
        assert_ne!(results[0], results[1]);
        assert_ne!(results[0], results[2]);
        assert_ne!(results[1], results[2]);
        let signatures = declarations
            .iter()
            .zip(results)
            .map(|(&declaration, result)| {
                assert_construct_signature(&context, &library, declaration, result, false)
            })
            .collect::<Vec<_>>();
        let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
            panic!("expected the actual library constructor value")
        };
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(signatures.as_slice())
        );
        assert_value_members(&context, value, results[0]);
        assert!(
            context
                .store()
                .signature(signatures[1])
                .unwrap()
                .flags()
                .contains(SignatureFlags::HAS_LITERAL_TYPES)
        );
        for (&construction, selected) in constructions.iter().zip([1, 0, 2]) {
            assert_new_identity(
                &mut context,
                &source,
                construction,
                owner,
                value,
                signatures[selected],
                results[selected],
            );
            assert_eq!(
                context
                    .store()
                    .signature(signature_at(&context, construction))
                    .unwrap()
                    .declaration(),
                Some(declarations[selected])
            );
        }
        for (name, selected) in [("ready", 1), ("text", 0), ("count", 2)] {
            let variable = named(&source, SOURCE_FILE, SyntaxKind::VariableDeclaration, name);
            assert_eq!(
                context
                    .get_type_at_location(initializer(&source, variable))
                    .unwrap(),
                results[selected]
            );
        }
        assert_replay(&mut context, &library, &source);
    }
}

#[test]
fn ambient_constructor_expressions_keep_generic_and_failed_overload_boundaries() {
    for (declarations, text) in [
        (BUILD_LIBRARY, "const value = new BuildValue<string>();"),
        (
            OVERLOAD_LIBRARY,
            "declare const flag: boolean; const value = new ChoiceValue(flag);",
        ),
    ] {
        let library = parse_source_file(&format!("{GLOBALS}{declarations}"));
        let source = parse_source_file(text);
        let constructions = nodes(&source, SOURCE_FILE, SyntaxKind::NewExpression);
        let [construction] = constructions.as_slice() else {
            panic!("each boundary keeps one real construction")
        };
        let mut context = context(&library, &source);
        let mut warm = None;
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(SOURCE_FILE),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                    *construction
                ))),
                "{text}",
            );
            assert!(
                context
                    .store()
                    .signature_links(*construction)
                    .is_none_or(|links| links == &SignatureLinks::default())
            );
            assert!(
                context
                    .store()
                    .type_node_links(*construction)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );
            assert!(context.diagnostics().is_empty());
            assert!(
                !context
                    .store()
                    .source_file_links(context.source_file(SOURCE_FILE).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
            let current = replay_state(&context, &library, &source);
            if let Some(warm) = &warm {
                assert_eq!(&current, warm);
            } else {
                warm = Some(current);
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both orders keep the executor's fresh cache and selected return.
fn ambient_constructor_templates_keep_fresh_cache_and_regular_argument_result() {
    use ts_checker::semantic::type_records::LiteralValue;

    let library = parse_source_file(&format!("{GLOBALS}{BUILD_LIBRARY}"));
    let source = parse_source_file(concat!(
        "class Templated { build(): BuildResult { ",
        "return new BuildValue(`hello${'world'}`); } } ",
        "declare const builder: Templated; const value = builder.build();",
    ));
    let declaration = named(
        &library,
        LIBRARY_FILE,
        SyntaxKind::VariableDeclaration,
        "BuildValue",
    );
    let literal = annotation(&library, declaration);
    let declarations = construct_declarations(&library, literal);
    let [construct_declaration] = declarations.as_slice() else {
        panic!("the library keeps one original construct signature")
    };
    let constructions = nodes(&source, SOURCE_FILE, SyntaxKind::NewExpression);
    let [construction] = constructions.as_slice() else {
        panic!("the method keeps one real New expression")
    };
    let (_, arguments) = new_parts(&source, *construction);
    let [argument] = arguments.as_slice() else {
        panic!("the constructor keeps one real template argument")
    };
    let NodeData::TemplateExpression(template) = &source.arena.get(argument.node).unwrap().data
    else {
        panic!("the argument must reach the contextual template executor")
    };
    let [span] = template.template_spans.nodes.as_slice() else {
        panic!("the template has one written substitution")
    };
    let NodeData::TemplateSpan(span) = &source.arena.get(*span).unwrap().data else {
        panic!("the template keeps its real span")
    };
    let NodeData::StringLiteral(substitution) = &source.arena.get(span.expression).unwrap().data
    else {
        panic!("the substitution is the original string literal")
    };
    assert_eq!(substitution.text, "world");

    for annotation_first in [false, true] {
        let mut context = context(&library, &source);
        let options = context.options();
        let globals = context.global_types().clone();
        let owner = symbol(&context, declaration);
        let early = annotation_first.then(|| context.get_type_from_type_node(literal).unwrap());
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let value_type = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context.get_type_from_type_node(literal).unwrap(),
            value_type
        );
        if let Some(early) = early {
            assert_eq!(early, value_type);
        }
        let result = declared_type(&mut context, &library, "BuildResult");
        let signature =
            assert_construct_signature(&context, &library, *construct_declaration, result, true);
        let raw = cached_type(&context, *argument);
        let TypeData::Literal(fresh) = context.store().type_payload(raw).unwrap().data() else {
            panic!("the executor must keep the fresh template cache")
        };
        let regular = fresh.regular_type;
        assert_ne!(raw, regular);
        assert_eq!(fresh.value, LiteralValue::String("helloworld".to_owned()));
        assert_eq!(fresh.fresh_type, Some(raw));
        let TypeData::Literal(regular_record) =
            context.store().type_payload(regular).unwrap().data()
        else {
            panic!("the contextual argument keeps its canonical regular literal")
        };
        assert_eq!(regular_record.value, fresh.value);
        assert_eq!(regular_record.regular_type, regular);
        assert_eq!(regular_record.fresh_type, Some(raw));
        assert_new_identity(
            &mut context,
            &source,
            *construction,
            owner,
            value_type,
            signature,
            result,
        );
        let value = named(
            &source,
            SOURCE_FILE,
            SyntaxKind::VariableDeclaration,
            "value",
        );
        assert_eq!(
            context
                .get_type_at_location(initializer(&source, value))
                .unwrap(),
            result
        );
        assert_eq!(context.options(), options);
        assert_eq!(context.global_types(), &globals);
        assert_replay(&mut context, &library, &source);
    }
}
