use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalImportCallMode, ConditionalRootId,
    DeclaredTypeError, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    TypeNodeUnavailable, ValueSymbolLinks,
    signatures::TypePredicateKind,
    type_records::{StructuredTypeData, TypeCacheState},
    types::TypeFlags,
};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE_FILE: FileId = FileId::new(202_260);

// The full ES2015 default-library closure, in the existing compiler test order.
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es6.d.ts",
        include_str!("../../ts_bundled/libs/lib.es6.d.ts"),
    ),
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.es2015.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.d.ts"),
    ),
    (
        "lib.dom.d.ts",
        include_str!("../../ts_bundled/libs/lib.dom.d.ts"),
    ),
    (
        "lib.dom.iterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.dom.iterable.d.ts"),
    ),
    (
        "lib.webworker.importscripts.d.ts",
        include_str!("../../ts_bundled/libs/lib.webworker.importscripts.d.ts"),
    ),
    (
        "lib.scripthost.d.ts",
        include_str!("../../ts_bundled/libs/lib.scripthost.d.ts"),
    ),
    (
        "lib.es2015.core.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts"),
    ),
    (
        "lib.es2015.collection.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.collection.d.ts"),
    ),
    (
        "lib.es2015.generator.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.generator.d.ts"),
    ),
    (
        "lib.es2015.iterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.iterable.d.ts"),
    ),
    (
        "lib.es2015.promise.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.promise.d.ts"),
    ),
    (
        "lib.es2015.proxy.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.proxy.d.ts"),
    ),
    (
        "lib.es2015.reflect.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.reflect.d.ts"),
    ),
    (
        "lib.es2015.symbol.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
    ),
    (
        "lib.es2015.symbol.wellknown.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.wellknown.d.ts"),
    ),
    (
        "lib.es2018.asynciterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2018.asynciterable.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let source = parse_source_file(source);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let libraries = LIBRARIES
            .iter()
            .map(|(name, text)| {
                let parsed = parse_source_file(text);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{name}: {:?}",
                    parsed.diagnostics
                );
                parsed
            })
            .collect();
        Self { source, libraries }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let options = CompilerOptions {
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        };
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
            .chain(std::iter::once((
                SOURCE_FILE,
                &self.source,
                "\"/project/conditional-signature-demand.ts\"".to_owned(),
                false,
            )))
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
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
                    strict_null_checks: options.strict_null_checks,
                    exact_optional_property_types: options.exact_optional_property_types,
                },
                strict_bind_call_apply: options.strict_bind_call_apply,
                strict_builtin_iterator_return: options.strict_builtin_iterator_return,
                strict_function_types: options.strict_function_types,
                strict_property_initialization: options.strict_property_initialization,
                use_unknown_in_catch_variables: options.use_unknown_in_catch_variables,
                no_implicit_any: options.no_implicit_any,
                no_implicit_this: options.no_implicit_this,
                module_kind: options.module,
                import_call_mode: CanonicalImportCallMode::Unsupported,
                check_bigint_target: true,
                name_resolution: (&options).into(),
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn node(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), SOURCE_FILE, node)
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

    fn named(&self, kind: SyntaxKind, expected: &str) -> NodeRef {
        self.nodes(kind)
            .into_iter()
            .find(|node| {
                let name = match &self.source.arena.get(node.node).unwrap().data {
                    NodeData::InterfaceDeclaration(data) => data.name,
                    NodeData::VariableDeclaration(data) => data.name,
                    _ => panic!("named lookup requires an interface or variable"),
                };
                matches!(&self.source.arena.get(name).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
    }

    fn variable_annotation(&self, name: &str) -> NodeRef {
        let variable = self.named(SyntaxKind::VariableDeclaration, name);
        let NodeData::VariableDeclaration(data) =
            &self.source.arena.get(variable.node).unwrap().data
        else {
            unreachable!()
        };
        self.node(data.type_.unwrap())
    }

    fn initializer(&self, name: &str) -> NodeRef {
        let variable = self.named(SyntaxKind::VariableDeclaration, name);
        let NodeData::VariableDeclaration(data) =
            &self.source.arena.get(variable.node).unwrap().data
        else {
            unreachable!()
        };
        self.node(data.initializer.unwrap())
    }
}

const fn structured_data(data: &TypeData) -> Option<&StructuredTypeData> {
    match data {
        TypeData::Object(data) => Some(&data.structured),
        TypeData::TypeReference(data) => Some(&data.object.structured),
        TypeData::Interface(data) => Some(&data.reference.object.structured),
        TypeData::Tuple(data) => Some(&data.interface.reference.object.structured),
        TypeData::InstantiationExpression(data) => Some(&data.object.structured),
        TypeData::Mapped(data) => Some(&data.object.structured),
        TypeData::ReverseMapped(data) => Some(&data.object.structured),
        TypeData::EvolvingArray(data) => Some(&data.object.structured),
        TypeData::Union(data) => Some(&data.union.structured),
        TypeData::Intersection(data) => Some(&data.intersection.structured),
        _ => None,
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn declared_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .declared_type_links(symbol(context, node))
        .and_then(|links| links.declared_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert!(record.alias().is_none());
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("the conditional must return an instantiated interface, not a fallback intrinsic")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([argument].as_slice())
    );
}

fn conditional_source(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    conditional: NodeRef,
) -> (TypeId, ConditionalRootId, Vec<TypeId>) {
    let type_ = context.get_type_from_type_node(conditional).unwrap();
    let method = fixture.node(
        fixture
            .source
            .arena
            .get(conditional.node)
            .unwrap()
            .parent
            .unwrap(),
    );
    let interface = fixture.node(
        fixture
            .source
            .arena
            .get(method.node)
            .unwrap()
            .parent
            .unwrap(),
    );
    let NodeData::MethodSignatureDeclaration(method_data) =
        &fixture.source.arena.get(method.node).unwrap().data
    else {
        panic!("the conditional must remain the direct method return annotation")
    };
    let NodeData::InterfaceDeclaration(interface_data) =
        &fixture.source.arena.get(interface.node).unwrap().data
    else {
        panic!("the method must retain its source interface")
    };
    let parameters = interface_data
        .type_parameters
        .iter()
        .chain(method_data.type_parameters.iter())
        .flat_map(|parameters| &parameters.nodes)
        .map(|node| {
            let node = fixture.node(*node);
            let owner = symbol(context, node);
            let type_ = declared_type(context, node);
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(owner));
            assert_eq!(context.get_symbol_declarations(owner).unwrap(), [node]);
            let TypeData::TypeParameter(data) = record.data() else {
                unreachable!()
            };
            assert!(!data.is_this_type);
            assert!(data.target.is_none());
            assert!(data.mapper.is_none());
            type_
        })
        .collect::<Vec<_>>();
    assert!(!parameters.is_empty());
    for (index, parameter) in parameters.iter().enumerate() {
        assert!(!parameters[..index].contains(parameter));
    }
    let record = context.store().type_payload(type_).unwrap();
    assert!(record.alias().is_none());
    let TypeData::Conditional(data) = record.data() else {
        panic!("the source return must stay deferred after instance specialization")
    };
    let root = context.store().conditional_root(data.root).unwrap();
    assert_eq!(root.node(), conditional);
    assert_eq!(root.check_type(), parameters[0]);
    assert_eq!(
        root.extends_type(),
        context.store().intrinsic_bootstrap().unwrap().any_type
    );
    assert_eq!(root.outer_type_parameters(), Some(parameters.as_slice()));
    assert!(root.is_distributive());
    (type_, data.root, parameters)
}

#[derive(Debug, Eq, PartialEq)]
struct NodePublication {
    node: NodeRef,
    common: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    nodes: Vec<NodePublication>,
    source: Option<SourceFileLinks>,
}

fn publication(context: &CanonicalCheckerContext<'_>, fixture: &Fixture) -> Publication {
    let store = context.store();
    let bound = context.file(SOURCE_FILE).unwrap().1;
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_predicate_len(),
            store.conditional_root_len(),
            store.type_alias_len(),
            store.index_info_len(),
        ],
        nodes: fixture
            .source
            .arena
            .iter()
            .map(|(node, _)| {
                let node = fixture.node(node);
                let owner = bound
                    .symbol(node)
                    .and_then(|raw| store.get_merged_symbol(raw));
                NodePublication {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                    value: owner
                        .and_then(|owner| store.value_symbol_links(owner))
                        .cloned(),
                    declared: owner
                        .and_then(|owner| store.declared_type_links(owner))
                        .cloned(),
                }
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(SOURCE_FILE).unwrap())
            .cloned(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    locations: &[(NodeRef, TypeId)],
    returns: &[(SignatureId, TypeId)],
    root: ConditionalRootId,
) {
    for &(node, type_) in locations {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    for &(signature, returned) in returns {
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(returned)
        );
    }
    let warm = publication(context, fixture);
    let root_cache = context
        .store()
        .conditional_root(root)
        .unwrap()
        .instantiations()
        .clone();
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        for &(signature, returned) in returns.iter().rev() {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(returned)
            );
        }
        for &(node, type_) in locations.iter().rev() {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert_eq!(publication(context, fixture), warm);
        assert_eq!(
            context
                .store()
                .conditional_root(root)
                .unwrap()
                .instantiations(),
            &root_cache
        );
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

fn assert_bullean_constructor(context: &CanonicalCheckerContext<'_>, fixture: &Fixture) {
    let constructor = fixture.named(SyntaxKind::InterfaceDeclaration, "BulleanConstructor");
    let type_ = declared_type(context, constructor);
    let TypeData::Interface(interface) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the constructor must retain its source interface")
    };
    let [call] = interface.declared_call_signatures.as_deref().unwrap() else {
        panic!("the constructor must retain its generic predicate call")
    };
    let [construct] = interface.declared_construct_signatures.as_deref().unwrap() else {
        panic!("the constructor must retain its construct signature")
    };
    assert_eq!(
        interface.reference.object.structured.signatures.as_deref(),
        Some([*call, *construct].as_slice())
    );
    let call = context.store().signature(*call).unwrap();
    assert_eq!(
        call.declaration(),
        Some(fixture.nodes(SyntaxKind::CallSignature)[0])
    );
    assert_eq!(call.parameters().len(), 1);
    assert_eq!(call.min_argument_count(), 0);
    let [parameter] = call.type_parameters() else {
        panic!("the predicate call is generic")
    };
    let predicate = call
        .resolved_type_predicate()
        .and_then(|predicate| context.store().type_predicate(predicate))
        .unwrap();
    assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
    assert_eq!(predicate.parameter_name(), "v2");
    assert_eq!(predicate.parameter_index(), 0);
    assert_eq!(predicate.type_id(), Some(*parameter));
    assert_eq!(
        call.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().boolean_type)
    );
    let construct = context.store().signature(*construct).unwrap();
    assert_eq!(
        construct.declaration(),
        Some(fixture.nodes(SyntaxKind::ConstructSignature)[0])
    );
    assert_eq!(construct.parameters().len(), 1);
    assert_eq!(construct.min_argument_count(), 0);
    assert_eq!(
        construct.resolved_return_type(),
        Some(declared_type(
            context,
            fixture.named(SyntaxKind::InterfaceDeclaration, "Bullean")
        ))
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Source, instance, overload, and capture identities belong to the same query.
fn ari_any_property_read_demands_inline_conditional_method_returns() {
    // These are the original declarations. The property read isolates the
    // return-demand prerequisite before the unchanged corpus's mixed callback call.
    let fixture = Fixture::new(concat!(
        "// @target: es2015\r\n",
        "interface Bullean { }\n",
        "interface BulleanConstructor {\n",
        "    new(v1?: any): Bullean;\n",
        "    <T>(v2?: T): v2 is T;\n",
        "}\n\n",
        "interface Ari<T> {\n",
        "    filter<S extends T>(cb1: (value: T) => value is S): T extends any ? Ari<any> : Ari<S>;\r\n",
        "    filter(cb2: (value: T) => unknown): Ari<T>;\r\n",
        "}\n",
        "declare var Bullean: BulleanConstructor;\n",
        "declare let anys: Ari<any>;\n",
        "var xs: Ari<any>;\n",
        "const selected = anys.filter;\n",
    ));
    let conditional = fixture.nodes(SyntaxKind::ConditionalType)[0];
    let methods = fixture.nodes(SyntaxKind::MethodSignature);
    assert_eq!(methods.len(), 2);
    let property = fixture.initializer("selected");
    for source_first in [false, true] {
        let mut context = fixture.context();
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        } else {
            let (template, _, _) = conditional_source(&mut context, &fixture, conditional);
            let TypeData::Conditional(data) =
                context.store().type_payload(template).unwrap().data()
            else {
                unreachable!()
            };
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
            context.get_type_at_location(property).unwrap();
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let (template, root, parameters) = conditional_source(&mut context, &fixture, conditional);
        let receiver = context
            .get_type_from_type_node(fixture.variable_annotation("anys"))
            .unwrap();
        let any = context.store().intrinsic_bootstrap().unwrap().any_type;
        let target = declared_type(
            &context,
            fixture.named(SyntaxKind::InterfaceDeclaration, "Ari"),
        );
        assert_reference(&context, receiver, target, any);
        let callable = checked_type(&context, property);
        let method_owner = symbol(&context, methods[0]);
        assert_eq!(symbol(&context, methods[1]), method_owner);
        let source_callable = context
            .store()
            .value_symbol_links(method_owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let record = context.store().type_payload(callable).unwrap();
        assert_eq!(record.symbol(), Some(method_owner));
        let TypeData::Object(object) = record.data() else {
            panic!("the property must be a mapped method")
        };
        assert_eq!(object.target, Some(source_callable));
        assert!(object.mapper.is_some());
        assert_eq!(object.structured.call_signature_count, 2);
        let signatures = object.structured.signatures.clone().unwrap();
        assert_eq!(signatures.len(), 2);
        let mut returns = Vec::new();
        for (&mapped, &method) in signatures.iter().zip(&methods) {
            let original = signature(&context, method);
            let record = context.store().signature(mapped).unwrap();
            assert_eq!(record.declaration(), Some(method));
            assert_eq!(record.target(), Some(original));
            assert!(record.mapper().is_some());
            assert_eq!(record.resolved_return_type(), Some(receiver));
            returns.push((mapped, receiver));
        }
        let source_signature = signature(&context, methods[0]);
        assert_eq!(
            context
                .store()
                .signature(source_signature)
                .unwrap()
                .resolved_return_type(),
            Some(template)
        );
        let [fresh] = context
            .store()
            .signature(signatures[0])
            .unwrap()
            .type_parameters()
        else {
            panic!("the first overload must keep its generic method parameter")
        };
        assert_ne!(*fresh, parameters[1]);
        let TypeData::TypeParameter(data) = context.store().type_payload(*fresh).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.target, Some(parameters[1]));
        assert_eq!(data.constraint, Some(any));
        assert!(
            context
                .store()
                .signature(signatures[1])
                .unwrap()
                .type_parameters()
                .is_empty()
        );
        assert_bullean_constructor(&context, &fixture);
        returns.push((source_signature, template));
        assert_replay(
            &mut context,
            &fixture,
            &[(property, callable), (conditional, template)],
            &returns,
            root,
        );
        assert_eq!(
            conditional_source(&mut context, &fixture, conditional),
            (template, root, parameters)
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the real proxy, conditional return, and call identities together.
fn explicit_generic_receiver_calls_keep_inline_conditional_returns_and_exact_errors() {
    let fixture = Fixture::new(concat!(
        "interface Choice<T> { select<S>(value: S): T extends any ? Choice<any> : Choice<S>; }\n",
        "declare const anys: Choice<any>;\n",
        "const selected = anys.select<string>('x');\n",
        "declare const count: number;\n",
        "const wrong = anys.select<string>(count);\n",
    ));
    let conditional = fixture.nodes(SyntaxKind::ConditionalType)[0];
    let method = fixture.nodes(SyntaxKind::MethodSignature)[0];
    let calls = [
        fixture.initializer("selected"),
        fixture.initializer("wrong"),
    ];
    let NodeData::CallExpression(first) = &fixture.source.arena.get(calls[0].node).unwrap().data
    else {
        unreachable!()
    };
    let property = fixture.node(first.expression);
    for source_first in [false, true] {
        let mut context = fixture.context();
        if !source_first {
            conditional_source(&mut context, &fixture, conditional);
            let receiver = context
                .get_type_from_type_node(fixture.variable_annotation("anys"))
                .unwrap();
            let callable = context.get_type_at_location(property).unwrap();
            let [mapped] = structured_data(context.store().type_payload(callable).unwrap().data())
                .unwrap()
                .signatures
                .as_deref()
                .unwrap()
            else {
                panic!("select must retain one mapped method signature")
            };
            let mapped = *mapped;
            assert_eq!(context.get_return_type_of_signature(mapped), Ok(receiver));
        }
        let result = context.check_source_file(SOURCE_FILE);
        let (template, root, parameters) = conditional_source(&mut context, &fixture, conditional);
        assert_eq!(parameters.len(), 2);
        let receiver = context
            .get_type_from_type_node(fixture.variable_annotation("anys"))
            .unwrap();
        let target = declared_type(
            &context,
            fixture.named(SyntaxKind::InterfaceDeclaration, "Choice"),
        );
        let any = context.store().intrinsic_bootstrap().unwrap().any_type;
        assert_reference(&context, receiver, target, any);
        let source_owner = symbol(&context, method);
        let source_callable = context
            .store()
            .value_symbol_links(source_owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let members = context
            .store()
            .type_payload(receiver)
            .and_then(|record| structured_data(record.data()))
            .and_then(|members| members.members)
            .and_then(|members| context.store().symbol_table(members))
            .unwrap();
        let proxy = members.get_source("select").unwrap();
        assert_ne!(proxy, source_owner);
        let proxy_links = context.store().value_symbol_links(proxy).unwrap();
        assert_eq!(proxy_links.target, Some(source_owner));
        assert!(proxy_links.mapper.is_some());
        let callable = proxy_links.resolved_type.unwrap();
        let record = context.store().type_payload(callable).unwrap();
        assert_eq!(record.symbol(), Some(source_owner));
        let TypeData::Object(object) = record.data() else {
            panic!("select must retain its mapped method object")
        };
        assert_eq!(object.target, Some(source_callable));
        assert_eq!(object.mapper, proxy_links.mapper);
        assert_eq!(object.structured.call_signature_count, 1);
        let [mapped] = object.structured.signatures.as_deref().unwrap() else {
            panic!("select must retain one mapped method signature")
        };
        let mapped = *mapped;
        let source_signature = signature(&context, method);
        let mapped_record = context.store().signature(mapped).unwrap();
        assert_eq!(mapped_record.declaration(), Some(method));
        assert_eq!(mapped_record.target(), Some(source_signature));
        assert!(mapped_record.mapper().is_some());
        assert_eq!(mapped_record.resolved_return_type(), Some(receiver));
        let [fresh] = mapped_record.type_parameters() else {
            panic!("the mapped method must retain its own generic parameter")
        };
        assert_ne!(*fresh, parameters[1]);
        let fresh = *fresh;
        let receiver_mapper = mapped_record.mapper().unwrap();
        let receiver_parameter = mapped_record.parameters()[0];
        let TypeData::TypeParameter(data) = context.store().type_payload(fresh).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.target, Some(parameters[1]));
        assert_eq!(data.mapper, Some(receiver_mapper));
        assert_eq!(context.get_return_type_of_signature(mapped), Ok(receiver));
        assert_eq!(
            context.get_return_type_of_signature(source_signature),
            Ok(template)
        );
        assert_eq!(checked_type(&context, property), callable);
        assert_eq!(
            context
                .store()
                .symbol_node_links(property)
                .and_then(|links| links.resolved_symbol),
            Some(proxy)
        );

        assert_eq!(result, Ok(()));
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let source_parameter = context
            .store()
            .signature(source_signature)
            .unwrap()
            .parameters()[0];
        let selected = calls.map(|call| signature(&context, call));
        assert_ne!(selected[0], selected[1]);
        for (index, call) in calls.into_iter().enumerate() {
            assert_eq!(checked_type(&context, call), receiver);
            assert_eq!(context.get_type_at_location(call), Ok(receiver));
            assert_eq!(
                context.get_return_type_of_signature(selected[index]),
                Ok(receiver)
            );
            let store = context.store();
            let record = store.signature(selected[index]).unwrap();
            assert_ne!(selected[index], mapped);
            assert_eq!(record.target(), Some(mapped));
            assert_eq!(record.declaration(), Some(method));
            assert!(record.type_parameters().is_empty());
            assert_eq!(record.resolved_return_type(), Some(receiver));
            let call_mapper = record.mapper().unwrap();
            assert_eq!(
                store.mapper_kind(call_mapper),
                Some(ts_checker::semantic::TypeMapperKind::Simple)
            );
            assert_eq!(store.map_type(call_mapper, fresh), Some(string));
            assert_eq!(
                store.map_type(call_mapper, parameters[1]),
                Some(parameters[1])
            );
            assert_eq!(
                store.map_type(call_mapper, parameters[0]),
                Some(parameters[0])
            );
            let [parameter] = record.parameters() else {
                panic!("select must keep one value parameter")
            };
            assert_ne!(*parameter, source_parameter);
            assert_ne!(*parameter, receiver_parameter);
            let links = store.value_symbol_links(*parameter).unwrap();
            assert_eq!(links.target, Some(source_parameter));
            let composed = links.mapper.unwrap();
            assert_ne!(composed, call_mapper);
            assert_ne!(composed, receiver_mapper);
            assert_eq!(
                store.mapper_kind(composed),
                Some(ts_checker::semantic::TypeMapperKind::Unknown)
            );
            assert_eq!(links.resolved_type, (index == 0).then_some(string));
            let NodeData::CallExpression(call_data) =
                &fixture.source.arena.get(call.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                context.get_type_at_location(fixture.node(call_data.expression)),
                Ok(callable)
            );
        }
        assert!(
            context
                .store()
                .source_file_links(context.source_file(SOURCE_FILE).unwrap())
                .is_some_and(|links| links.type_checked)
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the wrong argument must report one error")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        let NodeData::CallExpression(wrong) =
            &fixture.source.arena.get(calls[1].node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            diagnostic.node,
            Some(fixture.node(wrong.arguments.nodes[0]))
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        let selected_state = |context: &CanonicalCheckerContext<'_>| {
            calls.map(|call| {
                let selected = signature(context, call);
                let record = context.store().signature(selected).unwrap();
                (
                    selected,
                    record.target(),
                    record.mapper(),
                    record.resolved_return_type(),
                    record.type_parameters().to_vec(),
                    record
                        .parameters()
                        .iter()
                        .map(|&parameter| {
                            (
                                parameter,
                                context.store().value_symbol_links(parameter).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
        };
        let warm = publication(&context, &fixture);
        let warm_selected = selected_state(&context);
        let diagnostics = context.diagnostics().clone();
        let root_cache = context
            .store()
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone();
        for _ in 0..2 {
            for (index, call) in calls.into_iter().enumerate().rev() {
                assert_eq!(
                    context.get_return_type_of_signature(selected[index]),
                    Ok(receiver)
                );
                assert_eq!(context.get_type_at_location(call), Ok(receiver));
            }
            assert_eq!(context.get_type_at_location(property), Ok(callable));
            assert_eq!(context.get_return_type_of_signature(mapped), Ok(receiver));
            assert_eq!(
                context.get_return_type_of_signature(source_signature),
                Ok(template)
            );
            assert_eq!(context.check_source_file(SOURCE_FILE), Ok(()));
            assert_eq!(context.recheck_source_file(SOURCE_FILE), Ok(()));
            assert_eq!(publication(&context, &fixture), warm);
            assert_eq!(selected_state(&context), warm_selected);
            assert_eq!(
                context
                    .store()
                    .conditional_root(root)
                    .unwrap()
                    .instantiations(),
                &root_cache
            );
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the specialized return and exact argument diagnostic together.
fn nongeneric_method_calls_use_evaluated_inline_conditional_returns() {
    let fixture = Fixture::new(concat!(
        "interface ConcreteChoice<T> { select(value: string): T extends any ? ConcreteChoice<any> : ConcreteChoice<T>; }\n",
        "declare const anys: ConcreteChoice<any>;\n",
        "const selected = anys.select('x');\n",
        "declare const count: number;\n",
        "const wrong = anys.select(count);\n",
    ));
    let conditional = fixture.nodes(SyntaxKind::ConditionalType)[0];
    let method = fixture.nodes(SyntaxKind::MethodSignature)[0];
    let calls = [
        fixture.initializer("selected"),
        fixture.initializer("wrong"),
    ];
    for source_first in [false, true] {
        let mut context = fixture.context();
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        } else {
            context.get_type_at_location(calls[0]).unwrap();
        }
        context.check_source_file(SOURCE_FILE).unwrap();
        let (template, root, parameters) = conditional_source(&mut context, &fixture, conditional);
        assert_eq!(parameters.len(), 1);
        let receiver = context
            .get_type_from_type_node(fixture.variable_annotation("anys"))
            .unwrap();
        let target = declared_type(
            &context,
            fixture.named(SyntaxKind::InterfaceDeclaration, "ConcreteChoice"),
        );
        let any = context.store().intrinsic_bootstrap().unwrap().any_type;
        assert_reference(&context, receiver, target, any);
        let source_signature = signature(&context, method);
        let mut returns = Vec::new();
        for call in calls {
            assert_eq!(checked_type(&context, call), receiver);
            let selected = signature(&context, call);
            let selected_record = context.store().signature(selected).unwrap();
            assert_eq!(selected_record.declaration(), Some(method));
            assert!(selected_record.type_parameters().is_empty());
            assert!(selected_record.mapper().is_some());
            assert_eq!(selected_record.target(), Some(source_signature));
            assert_eq!(selected_record.resolved_return_type(), Some(receiver));
            let NodeData::CallExpression(call_data) =
                &fixture.source.arena.get(call.node).unwrap().data
            else {
                unreachable!()
            };
            let callee = fixture.node(call_data.expression);
            let TypeData::Object(object) = context
                .store()
                .type_payload(checked_type(&context, callee))
                .unwrap()
                .data()
            else {
                unreachable!()
            };
            let [mapped] = object.structured.signatures.as_deref().unwrap() else {
                panic!("select has one mapped method signature")
            };
            assert_eq!(selected, *mapped);
            assert_eq!(selected_record.mapper(), object.mapper);
            returns.push((selected, receiver));
        }
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the wrong argument must report one error")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        let NodeData::CallExpression(wrong) =
            &fixture.source.arena.get(calls[1].node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            diagnostic.node,
            Some(fixture.node(wrong.arguments.nodes[0]))
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            context
                .store()
                .signature(source_signature)
                .unwrap()
                .resolved_return_type(),
            Some(template)
        );
        returns.push((source_signature, template));
        assert_replay(
            &mut context,
            &fixture,
            &[
                (calls[0], receiver),
                (calls[1], receiver),
                (conditional, template),
            ],
            &returns,
            root,
        );
    }
}

#[test]
fn generic_inline_method_returns_stay_deferred_without_instance_demand() {
    let fixture = Fixture::new(
        "interface Choice<T> { select<S>(value: S): T extends any ? Choice<any> : Choice<S>; }",
    );
    let conditional = fixture.nodes(SyntaxKind::ConditionalType)[0];
    let method = fixture.nodes(SyntaxKind::MethodSignature)[0];
    for source_first in [false, true] {
        let mut context = fixture.context();
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        }
        let (template, root, parameters) = conditional_source(&mut context, &fixture, conditional);
        context.check_source_file(SOURCE_FILE).unwrap();
        let source_signature = signature(&context, method);
        assert_eq!(
            context.get_return_type_of_signature(source_signature),
            Ok(template)
        );
        let TypeData::Conditional(data) = context.store().type_payload(template).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.check_type, parameters[0]);
        assert!(data.resolved_true_type.is_none());
        assert!(data.resolved_false_type.is_none());
        assert!(data.mapper.is_none());
        assert!(data.combined_mapper.is_none());
        let TypeCacheState::Allocated(cache) = context
            .store()
            .conditional_root(root)
            .unwrap()
            .instantiations()
        else {
            panic!("the deferred source must have its parameter-keyed root cache")
        };
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.values().copied().collect::<Vec<_>>(), [template]);
        assert!(context.diagnostics().is_empty());
        assert_replay(
            &mut context,
            &fixture,
            &[(conditional, template)],
            &[(source_signature, template)],
            root,
        );
    }
}

#[test]
fn unsupported_conditional_captures_reject_source_queries_without_publication() {
    for source in [
        "interface Choice<T> { select<S>(value: S): T extends this ? Choice<S> : Choice<T>; }",
        concat!(
            "interface Choice<T> { select<S>(value: S): T extends any ? Choice<any> : Choice<S>; } ",
            "interface Choice<T> { value: T; }",
        ),
    ] {
        let fixture = Fixture::new(source);
        let conditional = fixture.nodes(SyntaxKind::ConditionalType)[0];
        let interface = fixture.nodes(SyntaxKind::InterfaceDeclaration)[0];
        let mut context = fixture.context();
        let before = publication(&context, &fixture);
        for _ in 0..2 {
            assert_eq!(
                context.get_type_from_type_node(conditional),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax {
                        node: interface,
                        kind: SyntaxKind::InterfaceDeclaration,
                    }
                )),
            );
            assert_eq!(publication(&context, &fixture), before);
            assert!(context.diagnostics().is_empty());
        }
    }
}
