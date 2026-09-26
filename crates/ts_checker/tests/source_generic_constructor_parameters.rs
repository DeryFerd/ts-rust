use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(93_211);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

const LIBRARIES: &[(&str, &str)] = libraries!(
    "es5",
    "es2015",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "decorators",
    "decorators.legacy",
);

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            source: parse_source_file(source),
            libraries: LIBRARIES
                .iter()
                .map(|(_, text)| parse_source_file(text))
                .collect(),
        }
    }

    fn node(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), FILE, node)
    }

    fn nodes(&self, kind: SyntaxKind) -> Vec<NodeRef> {
        let mut nodes = self
            .source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == kind).then_some((record.range.start, self.node(node)))
            })
            .collect::<Vec<_>>();
        nodes.sort_by_key(|(start, _)| *start);
        nodes.into_iter().map(|(_, node)| node).collect()
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([(
                FILE,
                &self.source,
                "\"/generic-constructors.ts\"".to_owned(),
                false,
            )])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                strict_function_types: true,
                strict_builtin_iterator_return: true,
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn global(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let raw = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature_at(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the real declaration or call has its canonical signature")
}

fn parameter_type(context: &CanonicalCheckerContext<'_>, parameter: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(parameter)
        .and_then(|links| links.resolved_type)
        .expect("the canonical parameter type is published")
}

fn assert_formal(
    context: &mut CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    minimum: i32,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
) -> (SignatureId, TypeId, SemanticSymbolId) {
    let (arena, _) = context.file(declaration.file).unwrap();
    let NodeData::ConstructSignatureDeclaration(data) = &arena.get(declaration.node).unwrap().data
    else {
        panic!("the signature must use the real construct declaration")
    };
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("one declaration-owned type parameter")
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("one real constructor parameter")
    };
    let formal = NodeRef::new(declaration.arena, declaration.file, *formal);
    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
    let formal_symbol = symbol(context, formal);
    let parameter_symbol = symbol(context, parameter);
    let formal_type = context.get_declared_type_of_symbol(formal_symbol).unwrap();
    let signature = signature_at(context, declaration);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.type_parameters(), &[formal_type]);
    assert_eq!(record.parameters(), &[parameter_symbol]);
    assert_eq!(record.min_argument_count(), minimum);
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    let payload = context.store().type_payload(formal_type).unwrap();
    assert_eq!(payload.symbol(), Some(formal_symbol));
    let TypeData::TypeParameter(data) = payload.data() else {
        panic!("the formal must retain its canonical type parameter")
    };
    assert_eq!(data.constraint, constraint);
    assert_eq!(data.resolved_default_type, default);
    assert!(!data.is_this_type);
    assert!(data.target.is_none());
    assert!(data.mapper.is_none());
    (signature, formal_type, parameter_symbol)
}

fn assert_optional_type(
    context: &CanonicalCheckerContext<'_>,
    actual: TypeId,
    expected: &[TypeId],
) {
    let TypeData::Union(union) = context.store().type_payload(actual).unwrap().data() else {
        panic!("the optional parameter retains its canonical union")
    };
    let elements = &union.union.types;
    assert_eq!(elements.len(), expected.len());
    for type_ in expected {
        assert!(elements.contains(type_), "missing canonical union member");
    }
}

fn arguments(context: &CanonicalCheckerContext<'_>, construction: NodeRef) -> Vec<NodeRef> {
    let (arena, _) = context.file(construction.file).unwrap();
    let NodeData::NewExpression(data) = &arena.get(construction.node).unwrap().data else {
        panic!("the call retains its real new expression")
    };
    data.arguments
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|&node| NodeRef::new(construction.arena, construction.file, node))
        .collect()
}

fn assert_calls(
    context: &mut CanonicalCheckerContext<'_>,
    constructions: &[NodeRef],
    declarations: &[SignatureId],
    expected: TypeId,
) {
    for &construction in constructions {
        assert_eq!(
            context.get_type_at_location(construction).unwrap(),
            expected
        );
        let signature = context
            .store()
            .signature(signature_at(context, construction))
            .unwrap();
        assert!(
            declarations.contains(&signature.target().expect("instantiated generic signature"))
        );
        assert!(signature.type_parameters().is_empty());
        assert_eq!(signature.resolved_return_type(), Some(expected));
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    constructions: &[NodeRef],
    declarations: &[SignatureId],
) {
    let types = constructions
        .iter()
        .map(|&node| context.get_type_at_location(node).unwrap())
        .collect::<Vec<_>>();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        fixture
            .source
            .arena
            .iter()
            .map(|(node, _)| {
                let node = fixture.node(node);
                (
                    context.store().type_node_links(node).cloned(),
                    context.store().signature_links(node).cloned(),
                    context.store().symbol_node_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let declaration_snapshot = |context: &CanonicalCheckerContext<'_>| {
        declarations
            .iter()
            .map(|&id| {
                let record = context.store().signature(id).unwrap();
                let declaration = record.declaration().unwrap();
                let formals = record
                    .type_parameters()
                    .iter()
                    .map(|&formal| {
                        let payload = context.store().type_payload(formal).unwrap();
                        let symbol = payload.symbol().unwrap();
                        let TypeData::TypeParameter(data) = payload.data() else {
                            panic!("the declared signature keeps its canonical formal")
                        };
                        (
                            formal,
                            symbol,
                            data.constraint,
                            data.resolved_default_type,
                            data.is_this_type,
                            data.target,
                            data.mapper,
                            context
                                .store()
                                .declared_type_links(symbol)
                                .and_then(|links| links.declared_type),
                        )
                    })
                    .collect::<Vec<_>>();
                let parameters = record
                    .parameters()
                    .iter()
                    .map(|&parameter| {
                        (
                            parameter,
                            context.store().value_symbol_links(parameter).cloned(),
                        )
                    })
                    .collect::<Vec<_>>();
                (
                    id,
                    (
                        record.flags(),
                        record.declaration(),
                        record.min_argument_count(),
                        record.resolved_return_type(),
                        record.target(),
                        record.mapper(),
                    ),
                    context.store().signature_links(declaration).cloned(),
                    context.store().type_node_links(declaration).cloned(),
                    formals,
                    parameters,
                )
            })
            .collect::<Vec<_>>()
    };
    let declared = declaration_snapshot(context);
    let before = counts(context);
    let links = snapshot(context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(FILE).unwrap();
    for (&node, type_) in constructions.iter().zip(types) {
        assert_eq!(context.get_type_at_location(node).unwrap(), type_);
    }
    assert_eq!(counts(context), before);
    assert_eq!(snapshot(context), links);
    assert_eq!(declaration_snapshot(context), declared);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn required_generic_constructor_keeps_formal_parameter_and_argument_errors() {
    let fixture = Fixture::new(concat!(
        "interface RequiredConstructor { new<T extends number>(value: T): T; }\n",
        "declare const required: RequiredConstructor;\n",
        "new required<number>(1);\n",
        "new required<number>('bad');\n",
        "new required<number>();\n",
    ));
    let declaration = fixture.nodes(SyntaxKind::ConstructSignature)[0];
    let interface = fixture.nodes(SyntaxKind::InterfaceDeclaration)[0];
    let constructions = fixture.nodes(SyntaxKind::NewExpression);
    let [_, invalid, missing] = constructions.as_slice() else {
        panic!("one valid call and both invalid calls remain present")
    };
    for declaration_first in [false, true] {
        let mut context = fixture.context();
        if declaration_first {
            let owner = symbol(&context, interface);
            context.get_declared_type_of_symbol(owner).unwrap();
        }
        context.check_source_file(FILE).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let (signature, formal, parameter) =
            assert_formal(&mut context, declaration, 1, Some(number), None);
        assert_eq!(parameter_type(&context, parameter), formal);
        assert_calls(&mut context, &constructions, &[signature], number);
        let [argument_error, arity_error] = context.diagnostics().as_slice() else {
            panic!(
                "one argument error and one missing-argument error: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(argument_error.diagnostic.code(), 2345);
        assert_eq!(argument_error.node, Some(arguments(&context, *invalid)[0]));
        assert_eq!(argument_error.range_override, None);
        assert!(argument_error.related_information.is_empty());
        assert_eq!(
            argument_error.diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        assert_eq!(arity_error.diagnostic.code(), 2554);
        assert_eq!(arity_error.node, Some(*missing));
        assert_eq!(arity_error.range_override, None);
        assert_eq!(
            arity_error.diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 0."
        );
        let [note] = arity_error.related_information.as_slice() else {
            panic!("the missing argument identifies its actual parameter")
        };
        assert_eq!(note.diagnostic.code(), 6210);
        assert_eq!(note.node, Some(fixture.nodes(SyntaxKind::Parameter)[0]));
        assert_eq!(
            note.diagnostic.render().unwrap(),
            "An argument for 'value' was not provided."
        );
        assert_replay(&mut context, &fixture, &constructions, &[signature]);
    }
}

#[test]
fn optional_generic_constructor_keeps_default_and_undefined_parameter_type() {
    let fixture = Fixture::new(concat!(
        "interface OptionalConstructor { new<T extends number = number>(value?: T): T; }\n",
        "declare const optional: OptionalConstructor;\n",
        "new optional();\n",
        "new optional<number>(1);\n",
        "new optional<number>(undefined);\n",
    ));
    let declaration = fixture.nodes(SyntaxKind::ConstructSignature)[0];
    let interface = fixture.nodes(SyntaxKind::InterfaceDeclaration)[0];
    let constructions = fixture.nodes(SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), 3);
    for declaration_first in [false, true] {
        let mut context = fixture.context();
        if declaration_first {
            let owner = symbol(&context, interface);
            context.get_declared_type_of_symbol(owner).unwrap();
        }
        context.check_source_file(FILE).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, undefined) = (bootstrap.number_type, bootstrap.undefined_type);
        let (signature, formal, parameter) =
            assert_formal(&mut context, declaration, 0, Some(number), Some(number));
        assert_optional_type(
            &context,
            parameter_type(&context, parameter),
            &[formal, undefined],
        );
        assert_calls(&mut context, &constructions, &[signature], number);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_replay(&mut context, &fixture, &constructions, &[signature]);
    }
}

fn native_set_declarations(context: &CanonicalCheckerContext<'_>) -> Vec<NodeRef> {
    let owner = global(context, "SetConstructor");
    let declarations = context
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap();
    let signatures = declarations
        .iter()
        .flat_map(|&owner| {
            let (arena, _) = context.file(owner.file).unwrap();
            let NodeData::InterfaceDeclaration(data) = &arena.get(owner.node).unwrap().data else {
                panic!("the native constructor keeps its actual interface declarations")
            };
            data.members
                .nodes
                .iter()
                .filter_map(|&node| {
                    (arena.get(node).unwrap().kind == SyntaxKind::ConstructSignature)
                        .then_some(NodeRef::new(owner.arena, owner.file, node))
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(signatures.len(), 2);
    signatures
}

fn assert_native_set_signatures(context: &mut CanonicalCheckerContext<'_>) -> Vec<SignatureId> {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (undefined, null, any) = (
        bootstrap.undefined_type,
        bootstrap.null_type,
        bootstrap.any_type,
    );
    let readonly_array = context
        .store()
        .declared_type_links(global(context, "ReadonlyArray"))
        .and_then(|links| links.declared_type)
        .expect("the native parameter has published the ReadonlyArray target");
    let iterable = context
        .store()
        .declared_type_links(global(context, "Iterable"))
        .and_then(|links| links.declared_type)
        .expect("the native parameter has published the Iterable target");
    let mut signatures = Vec::new();
    let (mut defaults, mut arrays, mut iterables) = (0, 0, 0);
    for declaration in native_set_declarations(context) {
        let (arena, _) = context.file(declaration.file).unwrap();
        let NodeData::ConstructSignatureDeclaration(data) =
            &arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let formal_node = data.type_parameters.as_ref().unwrap().nodes[0];
        let NodeData::TypeParameterDeclaration(formal_data) = &arena.get(formal_node).unwrap().data
        else {
            unreachable!()
        };
        let default = formal_data.default_type.map(|node| {
            assert_eq!(arena.get(node).unwrap().kind, SyntaxKind::AnyKeyword);
            any
        });
        defaults += usize::from(default.is_some());
        let (signature, formal, parameter) = assert_formal(context, declaration, 0, None, default);
        signatures.push(signature);
        let type_ = parameter_type(context, parameter);
        let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
            panic!("the native parameter retains its canonical union")
        };
        let elements = &union.union.types;
        assert_eq!(elements.len(), 3);
        assert!(elements.contains(&undefined));
        assert!(elements.contains(&null));
        let element = *elements
            .iter()
            .find(|&&type_| type_ != undefined && type_ != null)
            .unwrap();
        let TypeData::TypeReference(reference) =
            context.store().type_payload(element).unwrap().data()
        else {
            panic!("the native parameter retains its array or iterable reference")
        };
        if reference.object.target == Some(readonly_array) {
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[formal][..])
            );
            arrays += 1;
        } else {
            assert_eq!(reference.object.target, Some(iterable));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[formal, any, any][..])
            );
            iterables += 1;
        }
    }
    assert_eq!(defaults, 1);
    assert_eq!((arrays, iterables), (1, 1));
    assert_ne!(signatures[0], signatures[1]);
    signatures
}

#[test]
fn native_set_constructor_keeps_real_optional_generic_signatures() {
    let fixture = Fixture::new("new Set<number>();\nnew Set<number>(null);\n");
    let constructions = fixture.nodes(SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), 2);
    for declaration_first in [false, true] {
        let mut context = fixture.context();
        let constructor_owner = global(&context, "SetConstructor");
        if declaration_first {
            context
                .get_declared_type_of_symbol(constructor_owner)
                .unwrap();
        }
        context.check_source_file(FILE).unwrap();
        let signatures = assert_native_set_signatures(&mut context);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let set = global(&context, "Set");
        let target = context.get_declared_type_of_symbol(set).unwrap();
        let result = context.get_type_at_location(constructions[0]).unwrap();
        let TypeData::TypeReference(reference) =
            context.store().type_payload(result).unwrap().data()
        else {
            panic!("the native result is a canonical Set reference")
        };
        assert_eq!(reference.object.target, Some(target));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[number][..])
        );
        assert_calls(&mut context, &constructions, &signatures, result);
        assert_eq!(context.type_to_string(result).unwrap(), "Set<number>");
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_replay(&mut context, &fixture, &constructions, &signatures);
    }
}
