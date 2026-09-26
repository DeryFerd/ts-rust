use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_123);

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

const SOURCE: &str = r#"const target = { value: 1 };
const proxy = new Proxy(target, {
  get(_, prop) {
    const n: number = _.value;
    const key: string | symbol = prop;
    return key === "value" ? n : undefined;
  },
});
const result: number = proxy.value;
"#;

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parse = |name: &str, text: &str| {
            let parsed = parse_source_file(text);
            assert!(
                parsed.diagnostics.is_empty(),
                "{name}: {:?}",
                parsed.diagnostics
            );
            parsed
        };
        Self {
            source: parse("/proxy-contexts.ts", source),
            libraries: LIBRARIES
                .iter()
                .map(|(name, text)| parse(name, text))
                .collect(),
        }
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
                "\"/proxy-contexts.ts\"".to_owned(),
                false,
            )])
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

    fn proxy_library(&self) -> (FileId, &ParseResult) {
        let index = LIBRARIES
            .iter()
            .position(|(name, _)| *name == "lib.es2015.proxy.d.ts")
            .unwrap();
        (
            FileId::new(u32::try_from(index).unwrap()),
            &self.libraries[index],
        )
    }

    fn binding(&self, name: &str) -> Binding {
        let declaration = named(&self.source, FILE, name, SyntaxKind::VariableDeclaration);
        let NodeData::VariableDeclaration(variable) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        Binding {
            declaration,
            name: node(&self.source, FILE, variable.name),
            annotation: variable.type_.map(|id| node(&self.source, FILE, id)),
            initializer: node(&self.source, FILE, variable.initializer.unwrap()),
        }
    }

    fn construction(&self) -> (NodeRef, NodeRef, [NodeRef; 2], NodeRef) {
        let construction = self.binding("proxy").initializer;
        let NodeData::NewExpression(expression) =
            &self.source.arena.get(construction.node).unwrap().data
        else {
            panic!("query the actual NewExpression, not a later value or assertion")
        };
        let [target, handler] = expression.arguments.as_ref().unwrap().nodes.as_slice() else {
            panic!("the real Proxy call has two arguments")
        };
        let handler = node(&self.source, FILE, *handler);
        assert_eq!(
            self.source.arena.get(handler.node).unwrap().kind,
            SyntaxKind::ObjectLiteralExpression
        );
        let methods = self
            .source
            .arena
            .iter()
            .filter_map(|(id, record)| {
                (record.kind == SyntaxKind::MethodDeclaration
                    && record.parent == Some(handler.node))
                .then_some(node(&self.source, FILE, id))
            })
            .collect::<Vec<_>>();
        let [method] = methods.as_slice() else {
            panic!("the handler contains one actual source method")
        };
        (
            construction,
            node(&self.source, FILE, expression.expression),
            [node(&self.source, FILE, *target), handler],
            *method,
        )
    }

    fn library_members(&self) -> (NodeRef, NodeRef, NodeRef, NodeRef, NodeRef) {
        let (file, parsed) = self.proxy_library();
        let value = named(parsed, file, "Proxy", SyntaxKind::VariableDeclaration);
        let constructor = named(
            parsed,
            file,
            "ProxyConstructor",
            SyntaxKind::InterfaceDeclaration,
        );
        let handler = named(
            parsed,
            file,
            "ProxyHandler",
            SyntaxKind::InterfaceDeclaration,
        );
        let NodeData::InterfaceDeclaration(interface) =
            &parsed.arena.get(constructor.node).unwrap().data
        else {
            unreachable!()
        };
        let signatures = interface
            .members
            .nodes
            .iter()
            .filter_map(|&id| {
                (parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
                    .then_some(node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        let [signature] = signatures.as_slice() else {
            panic!("the real Proxy constructor has one construct declaration")
        };
        let get = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(method.name).unwrap().data
                else {
                    return None;
                };
                (record.parent == Some(handler.node) && name.text == "get").then(|| {
                    assert_eq!(method.parameters.nodes.len(), 3);
                    node(parsed, file, id)
                })
            })
            .collect::<Vec<_>>();
        let [get] = get.as_slice() else {
            panic!("use the original optional ProxyHandler.get declaration")
        };
        (value, constructor, handler, *signature, *get)
    }
}

struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, name: &str, kind: SyntaxKind) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name_id = match &record.data {
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_id).unwrap().data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = matches.as_slice() else {
        panic!("one actual declaration of {name}")
    };
    *declaration
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

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, id: SignatureId) -> Vec<TypeId> {
    context
        .store()
        .signature(id)
        .unwrap()
        .parameters()
        .iter()
        .map(|&parameter| {
            context
                .store()
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type)
                .unwrap()
        })
        .collect()
}

fn member(context: &CanonicalCheckerContext<'_>, owner: TypeId, name: &str) -> SemanticSymbolId {
    let structured = match context.store().type_payload(owner).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("the real object must retain its members"),
    };
    context
        .store()
        .symbol_table(structured.members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn only_signature(
    context: &CanonicalCheckerContext<'_>,
    owner: TypeId,
    construct: bool,
) -> SignatureId {
    let structured = match context.store().type_payload(owner).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("the actual callable must remain a structured type"),
    };
    assert_eq!(
        structured.call_signature_count,
        if construct { 0 } else { 1 }
    );
    let [signature] = structured.signatures.as_deref().unwrap() else {
        panic!("one real signature")
    };
    *signature
}

fn assert_union(context: &CanonicalCheckerContext<'_>, actual: TypeId, expected: &[TypeId]) {
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    let record = context.store().type_payload(actual).unwrap();
    let TypeData::Union(union) = record.data() else {
        panic!("the actual result must retain its canonical union")
    };
    assert!(record.alias().is_none());
    assert_eq!(union.union.types, expected);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert!(!union.union.types.contains(&bootstrap.missing_type));
    assert_eq!(bootstrap.cached_union_type(&expected), Some(actual));
}

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    target: TypeId,
    result: TypeId,
    selected: SignatureId,
    handler: TypeId,
    handler_context: TypeId,
    raw_method_context: TypeId,
    context_signature: SignatureId,
    method_owner: SemanticSymbolId,
    method_signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

fn observe(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    negative: bool,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let (construction, callee, [target_argument, handler_argument], method) =
        fixture.construction();
    let (
        proxy_declaration,
        constructor_declaration,
        handler_declaration,
        construct_declaration,
        get_declaration,
    ) = fixture.library_members();
    let target = fixture.binding("target");
    let target_owner = symbol(context, target.declaration);
    let target_type = context.get_type_at_location(target.name).unwrap();
    assert_eq!(
        context.get_type_at_location(target_argument),
        Ok(target_type)
    );
    assert_eq!(
        context.get_symbol_at_location(target_argument),
        Ok(Some(target_owner))
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(target_owner)
            .unwrap()
            .resolved_type,
        Some(target_type)
    );
    let result = context.get_type_at_location(construction).unwrap();
    assert_eq!(result, target_type);
    assert_eq!(
        context.get_type_at_location(fixture.binding("proxy").name),
        Ok(target_type)
    );

    let proxy_owner = symbol(context, proxy_declaration);
    assert_eq!(
        context.get_symbol_at_location(callee),
        Ok(Some(proxy_owner))
    );
    assert_eq!(
        context.get_symbol_declarations(proxy_owner).unwrap(),
        [proxy_declaration]
    );
    let constructor_owner = symbol(context, constructor_declaration);
    assert_eq!(
        context.get_symbol_declarations(constructor_owner).unwrap(),
        [constructor_declaration]
    );
    let constructor_type = context.get_type_at_location(callee).unwrap();
    assert_eq!(
        context.get_declared_type_of_symbol(constructor_owner),
        Ok(constructor_type)
    );
    assert_eq!(
        context
            .store()
            .type_payload(constructor_type)
            .unwrap()
            .symbol(),
        Some(constructor_owner)
    );
    let original = only_signature(context, constructor_type, true);
    assert_eq!(original, signature(context, construct_declaration));
    let original_record = context.store().signature(original).unwrap();
    assert_eq!(original_record.declaration(), Some(construct_declaration));
    let [formal] = original_record.type_parameters() else {
        panic!("the real constructor has exactly one generic formal")
    };
    let formal = *formal;
    assert_eq!(original_record.parameters().len(), 2);
    assert_eq!(original_record.min_argument_count(), 2);
    assert_eq!(original_record.target(), None);
    assert_eq!(original_record.mapper(), None);

    let selected = signature(context, construction);
    let selected_record = context.store().signature(selected).unwrap();
    assert_eq!(selected_record.target(), Some(original));
    assert_eq!(selected_record.declaration(), Some(construct_declaration));
    assert!(selected_record.type_parameters().is_empty());
    assert_eq!(selected_record.parameters().len(), 2);
    assert_eq!(selected_record.min_argument_count(), 2);
    assert_eq!(selected_record.resolved_return_type(), Some(result));
    let mapper = selected_record.mapper().unwrap();
    assert!(context.store().mapper_payload(mapper).is_some());
    assert_eq!(context.store().map_type(mapper, formal), Some(target_type));
    let selected_parameters = parameter_types(context, selected);
    let [selected_target, handler_context] = selected_parameters.as_slice() else {
        panic!("two actual instantiated constructor parameters")
    };
    assert_eq!(*selected_target, target_type);
    let handler_context = *handler_context;
    let handler_owner = symbol(context, handler_declaration);
    assert_eq!(
        context.get_symbol_declarations(handler_owner).unwrap(),
        [handler_declaration]
    );
    let handler_target = context.get_declared_type_of_symbol(handler_owner).unwrap();
    let TypeData::TypeReference(reference) = context
        .store()
        .type_payload(handler_context)
        .unwrap()
        .data()
    else {
        panic!("the handler context must be the real ProxyHandler reference")
    };
    assert_eq!(reference.object.target, Some(handler_target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[target_type][..])
    );
    let get_property = member(context, handler_context, "get");
    assert_eq!(
        context.get_symbol_declarations(get_property).unwrap(),
        [get_declaration]
    );
    let raw_method_context = context
        .store()
        .value_symbol_links(get_property)
        .unwrap()
        .resolved_type
        .unwrap();

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (string, number, es_symbol, undefined, any) = (
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.es_symbol_type,
        bootstrap.undefined_type,
        bootstrap.any_type,
    );
    let TypeData::Union(optional) = context
        .store()
        .type_payload(raw_method_context)
        .unwrap()
        .data()
    else {
        panic!("the real get context must retain optional undefined")
    };
    let callable_arms = optional
        .union
        .types
        .iter()
        .copied()
        .filter(|&type_| type_ != undefined)
        .collect::<Vec<_>>();
    let [context_callable] = callable_arms.as_slice() else {
        panic!("exactly one callable arm")
    };
    let context_callable = *context_callable;
    assert_union(context, raw_method_context, &[context_callable, undefined]);
    let context_signature = only_signature(context, context_callable, false);
    let context_record = context.store().signature(context_signature).unwrap();
    assert_eq!(context_record.declaration(), Some(get_declaration));
    assert_eq!(context_record.parameters().len(), 3);
    assert_eq!(context_record.min_argument_count(), 3);
    assert!(context_record.type_parameters().is_empty());
    assert_eq!(
        context.get_return_type_of_signature(context_signature),
        Ok(any)
    );
    let key = fixture.binding("key");
    let key_type = context
        .get_type_from_type_node(key.annotation.unwrap())
        .unwrap();
    assert_union(context, key_type, &[string, es_symbol]);
    assert_eq!(
        parameter_types(context, context_signature),
        [target_type, key_type, any]
    );

    let handler = context.get_type_at_location(handler_argument).unwrap();
    let NodeData::MethodDeclaration(method_data) =
        &fixture.source.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(method_data.parameters.nodes.len(), 2);
    let method_name = node(&fixture.source, FILE, method_data.name);
    let method_owner = symbol(context, method);
    assert_eq!(member(context, handler, "get"), method_owner);
    assert_eq!(
        context.get_symbol_at_location(method_name),
        Ok(Some(method_owner))
    );
    let method_type = context.get_type_at_location(method).unwrap();
    assert_eq!(context.get_type_at_location(method_name), Ok(method_type));
    let owner_record = context.store().symbol(method_owner).unwrap();
    assert_eq!(owner_record.declarations(), Some(&[method][..]));
    assert_eq!(owner_record.value_declaration(), Some(method));
    assert_eq!(
        context
            .store()
            .value_symbol_links(method_owner)
            .unwrap()
            .resolved_type,
        Some(method_type)
    );
    assert_eq!(
        context.store().type_payload(method_type).unwrap().symbol(),
        Some(method_owner)
    );
    let method_signature = signature(context, method);
    assert_eq!(
        only_signature(context, method_type, false),
        method_signature
    );
    assert_ne!(method_signature, context_signature);
    let parameters = method_data
        .parameters
        .nodes
        .iter()
        .map(|&id| {
            let declaration = node(&fixture.source, FILE, id);
            let NodeData::ParameterDeclaration(parameter) =
                &fixture.source.arena.get(id).unwrap().data
            else {
                panic!("actual source parameters")
            };
            assert!(parameter.type_.is_none());
            assert!(parameter.initializer.is_none());
            let name = node(&fixture.source, FILE, parameter.name);
            let owner = symbol(context, declaration);
            let type_ = context.get_type_at_location(name).unwrap();
            assert_ne!(type_, any);
            assert_eq!(context.get_type_at_location(declaration), Ok(type_));
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(owner)));
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
            (owner, type_)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        parameters
            .iter()
            .map(|&(_, type_)| type_)
            .collect::<Vec<_>>(),
        [target_type, key_type]
    );
    let returned = context
        .get_return_type_of_signature(method_signature)
        .unwrap();
    let method_record = context.store().signature(method_signature).unwrap();
    assert_eq!(method_record.declaration(), Some(method));
    assert_eq!(
        method_record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>()
    );
    assert_eq!(method_record.min_argument_count(), 2);
    assert!(method_record.type_parameters().is_empty());
    assert_eq!(method_record.this_parameter(), None);
    assert_eq!(method_record.target(), None);
    assert_eq!(method_record.mapper(), None);
    assert_eq!(method_record.resolved_return_type(), Some(returned));
    assert_ne!(returned, any);
    assert_union(
        context,
        returned,
        &[if negative { string } else { number }, undefined],
    );

    let n = fixture.binding("n");
    assert_eq!(
        context.get_type_at_location(n.name),
        Ok(if negative { string } else { number })
    );
    assert_eq!(context.get_type_at_location(n.initializer), Ok(number));
    assert_eq!(context.get_type_at_location(key.name), Ok(key_type));
    assert_eq!(context.get_type_at_location(key.initializer), Ok(key_type));
    let returns = fixture
        .source
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::ConditionalExpression).then_some(node(
                &fixture.source,
                FILE,
                id,
            ))
        })
        .collect::<Vec<_>>();
    let [returned_expression] = returns.as_slice() else {
        panic!("the method keeps its actual conditional return")
    };
    assert_eq!(
        context.get_type_at_location(*returned_expression),
        Ok(returned)
    );
    let result_binding = fixture.binding("result");
    assert_eq!(
        context.get_type_at_location(result_binding.name),
        Ok(number)
    );
    assert_eq!(
        context.get_type_at_location(result_binding.initializer),
        Ok(number)
    );

    (
        Observation {
            target: target_type,
            result,
            selected,
            handler,
            handler_context,
            raw_method_context,
            context_signature,
            method_owner,
            method_signature,
            parameters,
            returned,
        },
        mapper,
    )
}

fn assert_diagnostics(fixture: &Fixture, context: &CanonicalCheckerContext<'_>, negative: bool) {
    if !negative {
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        return;
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the checked method body must report exactly one assignment error")
    };
    let name = fixture.binding("n").name;
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    let range = fixture.source.arena.get(name.node).unwrap().range;
    assert_eq!((range.start.get(), range.end.get()), (90, 91));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        fixture
            .source
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(&fixture.source, FILE, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| (owner, store.value_symbol_links(owner).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        context.file(FILE).unwrap().1.flow_graph().clone(),
        context.diagnostics().clone(),
    )
}

fn check(source: &str, negative: bool) {
    let fixture = Fixture::new(source);
    let (construction, _, _, _) = fixture.construction();
    for query_first in [false, true] {
        let mut context = fixture.context();
        let source_root = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source_root)
                .is_some_and(|links| links.type_checked)
        );
        let queried = query_first.then(|| context.get_type_at_location(construction).unwrap());
        context.check_source_file(FILE).unwrap();
        assert_diagnostics(&fixture, &context, negative);
        assert!(
            context
                .store()
                .source_file_links(source_root)
                .unwrap()
                .type_checked
        );
        let observed = observe(&fixture, &mut context, negative);
        if let Some(queried) = queried {
            assert_eq!(context.get_type_at_location(construction), Ok(queried));
        }
        assert_diagnostics(&fixture, &context, negative);
        let warm = snapshot(&context, &fixture);
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_diagnostics(&fixture, &context, negative);
            assert_eq!(observe(&fixture, &mut context, negative), observed);
            assert_eq!(snapshot(&context, &fixture), warm);
        }
    }
}

#[test]
fn real_proxy_constructor_checks_inferred_handler_context_and_body() {
    check(SOURCE, false);
}

#[test]
fn real_proxy_constructor_keeps_handler_assignment_error_with_any_return() {
    let source = SOURCE.replacen("n: number", "n: string", 1);
    check(&source, true);
}
