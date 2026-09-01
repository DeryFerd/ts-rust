use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_180);

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

const SOURCE: &str = r#"export {};
const _path = { value: 1 };
const _platforms: { [key: PropertyKey]: number | undefined } = {};
const mix = (del: number = 0) => {
  return new Proxy(_path, {
    get(_, prop) {
      const checked: number = _.value;
      if (prop === "delimiter") return del;
      if (prop === "posix") return posix;
      if (prop === "win32") return win32;
      return _platforms[prop] || _path[prop as keyof typeof _path];
    },
  });
};
export const posix: number = 2;
export const win32: number = 3;
const result: number = mix().value;
"#;

const CAPTURES: &str = "export const posix: number = 2;\nexport const win32: number = 3;\n";

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
            source: parse("/object-method-statements.ts", source),
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
                "\"/object-method-statements.ts\"".to_owned(),
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
                        if *library {
                            CanonicalModuleState::Script
                        } else {
                            CanonicalModuleState::External
                        },
                    )
                    .with_always_strict(true),
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
                no_unchecked_indexed_access: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn node(&self, id: NodeId) -> NodeRef {
        node(&self.source, FILE, id)
    }

    fn only(&self, kind: SyntaxKind) -> NodeRef {
        let nodes = self
            .source
            .arena
            .iter()
            .filter_map(|(id, record)| (record.kind == kind).then_some(self.node(id)))
            .collect::<Vec<_>>();
        let [node] = nodes.as_slice() else {
            panic!("expected one {kind:?}")
        };
        *node
    }

    fn binding(&self, name: &str) -> Binding {
        let declaration = named(&self.source, FILE, name, SyntaxKind::VariableDeclaration);
        let NodeData::VariableDeclaration(data) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        Binding {
            declaration,
            name: self.node(data.name),
            initializer: self.node(data.initializer.unwrap()),
        }
    }

    fn construction(&self) -> (NodeRef, NodeRef, [NodeRef; 2], NodeRef) {
        let construction = self.only(SyntaxKind::NewExpression);
        let NodeData::NewExpression(data) = &self.source.arena.get(construction.node).unwrap().data
        else {
            unreachable!()
        };
        let [target, handler] = data.arguments.as_ref().unwrap().nodes.as_slice() else {
            panic!("the Proxy construction must keep both actual arguments")
        };
        let handler = self.node(*handler);
        assert_eq!(
            self.source.arena.get(handler.node).unwrap().kind,
            SyntaxKind::ObjectLiteralExpression
        );
        let method = self.only(SyntaxKind::MethodDeclaration);
        assert_eq!(
            self.source.arena.get(method.node).unwrap().parent,
            Some(handler.node)
        );
        (
            construction,
            self.node(data.expression),
            [self.node(*target), handler],
            method,
        )
    }

    fn library_members(&self) -> (NodeRef, NodeRef, NodeRef, NodeRef, NodeRef) {
        let index = LIBRARIES
            .iter()
            .position(|(name, _)| *name == "lib.es2015.proxy.d.ts")
            .unwrap();
        let file = FileId::new(u32::try_from(index).unwrap());
        let parsed = &self.libraries[index];
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
        let NodeData::InterfaceDeclaration(data) =
            &parsed.arena.get(constructor.node).unwrap().data
        else {
            unreachable!()
        };
        let signatures = data
            .members
            .nodes
            .iter()
            .filter_map(|&id| {
                (parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
                    .then_some(node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        let [construct] = signatures.as_slice() else {
            panic!("the real Proxy constructor has one construct signature")
        };
        let methods = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
                    return None;
                };
                (record.parent == Some(handler.node) && name.text == "get")
                    .then_some(node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        let [get] = methods.as_slice() else {
            panic!("use the real optional ProxyHandler.get declaration")
        };
        (value, constructor, handler, *construct, *get)
    }
}

struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, expected: &str, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = nodes.as_slice() else {
        panic!("expected one declaration of {expected}")
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

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, signature: SignatureId) -> Vec<TypeId> {
    context
        .store()
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|&owner| {
            context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .collect()
}

fn member(context: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    let structured = match context.store().type_payload(type_).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("expected the actual structured type"),
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
    type_: TypeId,
    construct: bool,
) -> SignatureId {
    let structured = match context.store().type_payload(type_).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("expected the actual callable type"),
    };
    assert_eq!(
        structured.call_signature_count,
        if construct { 0 } else { 1 }
    );
    let [signature] = structured.signatures.as_deref().unwrap() else {
        panic!("expected one actual signature")
    };
    *signature
}

fn assert_union(context: &CanonicalCheckerContext<'_>, actual: TypeId, expected: &[TypeId]) {
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    let TypeData::Union(union) = context.store().type_payload(actual).unwrap().data() else {
        panic!("expected a canonical union")
    };
    assert_eq!(union.union.types, expected);
    assert_eq!(
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .cached_union_type(&expected),
        Some(actual)
    );
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    target: TypeId,
    construction: SignatureId,
    handler: TypeId,
    handler_context: TypeId,
    raw_method_context: TypeId,
    context_signature: SignatureId,
    method_owner: SemanticSymbolId,
    method_type: TypeId,
    method_signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
    captures: Vec<(NodeRef, SemanticSymbolId, TypeId)>,
    body_types: Vec<(NodeRef, TypeId)>,
}

fn observe(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    negative: bool,
    later_captures: bool,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let (construction, callee, [target_argument, handler_argument], method) =
        fixture.construction();
    let (proxy, constructor, handler_declaration, construct_declaration, get_declaration) =
        fixture.library_members();
    let target = fixture.binding("_path");
    let target_type = context.get_type_at_location(target.name).unwrap();
    assert_eq!(
        context.get_type_at_location(target_argument),
        Ok(target_type)
    );
    assert_eq!(
        context.get_symbol_at_location(target_argument),
        Ok(Some(symbol(context, target.declaration)))
    );
    assert_eq!(context.get_type_at_location(construction), Ok(target_type));
    assert_eq!(
        context.get_symbol_at_location(callee),
        Ok(Some(symbol(context, proxy)))
    );
    assert_eq!(
        context
            .get_symbol_declarations(symbol(context, proxy))
            .unwrap(),
        [proxy]
    );

    let constructor_type = context.get_type_at_location(callee).unwrap();
    assert_eq!(
        context.get_declared_type_of_symbol(symbol(context, constructor)),
        Ok(constructor_type)
    );
    let original = only_signature(context, constructor_type, true);
    assert_eq!(original, signature(context, construct_declaration));
    let original_record = context.store().signature(original).unwrap();
    assert_eq!(original_record.declaration(), Some(construct_declaration));
    assert_eq!(original_record.parameters().len(), 2);
    assert_eq!(original_record.min_argument_count(), 2);
    let [formal] = original_record.type_parameters() else {
        panic!("the real Proxy constructor has one generic formal")
    };
    let formal = *formal;
    assert_eq!(original_record.target(), None);
    assert_eq!(original_record.mapper(), None);

    let selected = signature(context, construction);
    let selected_record = context.store().signature(selected).unwrap();
    assert_eq!(selected_record.target(), Some(original));
    assert_eq!(selected_record.declaration(), Some(construct_declaration));
    assert!(selected_record.type_parameters().is_empty());
    assert_eq!(selected_record.min_argument_count(), 2);
    assert_eq!(selected_record.resolved_return_type(), Some(target_type));
    let mapper = selected_record.mapper().unwrap();
    assert!(context.store().mapper_payload(mapper).is_some());
    assert_eq!(context.store().map_type(mapper, formal), Some(target_type));
    let selected_parameters = parameter_types(context, selected);
    let [selected_target, handler_context] = selected_parameters.as_slice() else {
        panic!("the selected constructor must keep both instantiated parameters")
    };
    assert_eq!(*selected_target, target_type);
    let handler_context = *handler_context;
    let handler_target = context
        .get_declared_type_of_symbol(symbol(context, handler_declaration))
        .unwrap();
    let TypeData::TypeReference(reference) = context
        .store()
        .type_payload(handler_context)
        .unwrap()
        .data()
    else {
        panic!("the handler must use the real ProxyHandler reference")
    };
    assert_eq!(reference.object.target, Some(handler_target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[target_type][..])
    );
    let get_member = member(context, handler_context, "get");
    assert_eq!(
        context.get_symbol_declarations(get_member).unwrap(),
        [get_declaration]
    );
    let raw_method_context = context
        .store()
        .value_symbol_links(get_member)
        .unwrap()
        .resolved_type
        .unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (number, string, es_symbol, undefined, any) = (
        bootstrap.number_type,
        bootstrap.string_type,
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
        panic!("the optional get context must keep its undefined arm")
    };
    let callable = optional
        .union
        .types
        .iter()
        .copied()
        .filter(|&type_| type_ != undefined)
        .collect::<Vec<_>>();
    let [callable] = callable.as_slice() else {
        panic!("the optional get context has one callable arm")
    };
    let callable = *callable;
    assert_union(context, raw_method_context, &[callable, undefined]);
    let context_signature = only_signature(context, callable, false);
    let context_record = context.store().signature(context_signature).unwrap();
    assert_eq!(context_record.declaration(), Some(get_declaration));
    assert_eq!(context_record.parameters().len(), 3);
    assert_eq!(context_record.min_argument_count(), 3);
    assert!(context_record.type_parameters().is_empty());
    assert!(context_record.target().is_some());
    assert!(context_record.mapper().is_some());
    assert_eq!(
        context
            .store()
            .signature(context_record.target().unwrap())
            .unwrap()
            .declaration(),
        Some(get_declaration)
    );
    assert_eq!(
        context.get_return_type_of_signature(context_signature),
        Ok(any)
    );
    let context_parameters = parameter_types(context, context_signature);
    let [context_target, key_type, receiver_type] = context_parameters.as_slice() else {
        panic!("the context must retain all three library parameters")
    };
    assert_eq!(*context_target, target_type);
    assert_eq!(*receiver_type, any);
    let key_type = *key_type;
    assert_union(context, key_type, &[string, es_symbol]);

    let handler = context.get_type_at_location(handler_argument).unwrap();
    let NodeData::MethodDeclaration(data) = &fixture.source.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(data.parameters.nodes.len(), 2);
    assert!(data.type_.is_none());
    assert!(data.type_parameters.is_none());
    let method_name = fixture.node(data.name);
    let method_owner = symbol(context, method);
    assert_eq!(member(context, handler, "get"), method_owner);
    assert_eq!(
        context.get_symbol_at_location(method_name),
        Ok(Some(method_owner))
    );
    let method_type = context.get_type_at_location(method).unwrap();
    assert_eq!(context.get_type_at_location(method_name), Ok(method_type));
    let owner = context.store().symbol(method_owner).unwrap();
    assert!(owner.flags().contains(SymbolFlags::METHOD));
    assert_eq!(owner.parent(), Some(symbol(context, handler_argument)));
    assert_eq!(owner.declarations(), Some(&[method][..]));
    assert_eq!(owner.value_declaration(), Some(method));
    assert_eq!(
        context.store().type_payload(method_type).unwrap().symbol(),
        Some(method_owner)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(method_owner)
            .unwrap()
            .resolved_type,
        Some(method_type)
    );
    let method_signature = signature(context, method);
    assert_eq!(
        only_signature(context, method_type, false),
        method_signature
    );
    assert_ne!(method_signature, context_signature);
    let parameters = data
        .parameters
        .nodes
        .iter()
        .map(|&id| {
            let declaration = fixture.node(id);
            let NodeData::ParameterDeclaration(parameter) =
                &fixture.source.arena.get(id).unwrap().data
            else {
                panic!("expected a real source method parameter")
            };
            assert!(parameter.type_.is_none());
            assert!(parameter.initializer.is_none());
            assert_eq!(
                fixture.source.arena.get(id).unwrap().parent,
                Some(method.node)
            );
            let name = fixture.node(parameter.name);
            let owner = symbol(context, declaration);
            let type_ = context.get_type_at_location(name).unwrap();
            assert_ne!(type_, any);
            assert_eq!(context.get_type_at_location(declaration), Ok(type_));
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(owner)));
            let record = context.store().symbol(owner).unwrap();
            assert_eq!(record.declarations(), Some(&[declaration][..]));
            assert_eq!(record.value_declaration(), Some(declaration));
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
    assert_ne!(parameters[0].0, parameters[1].0);
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
    assert_eq!(returned, number);
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
    assert_eq!(method_record.resolved_return_type(), Some(number));

    let mix = fixture.binding("mix");
    let NodeData::ArrowFunction(arrow) =
        &fixture.source.arena.get(mix.initializer.node).unwrap().data
    else {
        panic!("the handler must keep its real enclosing arrow")
    };
    assert!(arrow.type_.is_none());
    let [del] = arrow.parameters.nodes.as_slice() else {
        panic!("the enclosing arrow must retain its captured parameter")
    };
    let del = fixture.node(*del);
    let del_owner = symbol(context, del);
    assert_eq!(context.get_type_at_location(del), Ok(number));
    let platforms = fixture.binding("_platforms");
    let platforms_type = context.get_type_at_location(platforms.name).unwrap();
    let checked = fixture.binding("checked");
    let checked_type = if negative { string } else { number };
    assert_eq!(context.get_type_at_location(checked.name), Ok(checked_type));
    assert_eq!(
        context.get_type_at_location(checked.initializer),
        Ok(number)
    );
    let posix = fixture.binding("posix");
    let win32 = fixture.binding("win32");
    let mix_range = fixture
        .source
        .arena
        .get(mix.declaration.node)
        .unwrap()
        .range;
    for binding in [&posix, &win32] {
        let range = fixture
            .source
            .arena
            .get(binding.declaration.node)
            .unwrap()
            .range;
        assert_eq!(range.start > mix_range.end, later_captures);
        assert_eq!(context.get_type_at_location(binding.name), Ok(number));
    }
    let expected_symbols = [
        ("_", parameters[0].0, target_type),
        ("prop", parameters[1].0, key_type),
        ("del", del_owner, number),
        ("_path", symbol(context, target.declaration), target_type),
        (
            "_platforms",
            symbol(context, platforms.declaration),
            platforms_type,
        ),
        ("posix", symbol(context, posix.declaration), number),
        ("win32", symbol(context, win32.declaration), number),
        (
            "checked",
            symbol(context, checked.declaration),
            checked_type,
        ),
    ];
    for binding in [&target, &platforms, &posix, &win32, &checked] {
        let owner = symbol(context, binding.declaration);
        assert_eq!(
            context.get_symbol_at_location(binding.name),
            Ok(Some(owner))
        );
        assert_eq!(
            context.get_symbol_declarations(owner).unwrap(),
            [binding.declaration]
        );
    }
    let range = fixture.source.arena.get(method.node).unwrap().range;
    let mut captures = Vec::new();
    for (id, record) in fixture.source.arena.iter() {
        if record.range.start < range.start || record.range.end > range.end {
            continue;
        }
        let NodeData::Identifier(name) = &record.data else {
            continue;
        };
        let Some(&(_, owner, type_)) = expected_symbols
            .iter()
            .find(|&&(expected, _, _)| expected == name.text)
        else {
            continue;
        };
        let location = fixture.node(id);
        assert_eq!(context.get_symbol_at_location(location), Ok(Some(owner)));
        assert_eq!(
            context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(type_)
        );
        captures.push((location, owner, type_));
    }
    for (_, owner, _) in expected_symbols {
        assert!(captures.iter().any(|&(_, actual, _)| actual == owner));
    }

    let mut returns = fixture
        .source
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.range.start < range.start || record.range.end > range.end {
                return None;
            }
            let NodeData::ReturnStatement(data) = &record.data else {
                return None;
            };
            Some((
                record.range.start,
                fixture.node(id),
                fixture.node(data.expression.unwrap()),
            ))
        })
        .collect::<Vec<_>>();
    returns.sort_by_key(|&(start, _, _)| start);
    assert_eq!(returns.len(), 4);
    let branches = fixture
        .source
        .arena
        .iter()
        .filter_map(|(_, record)| {
            if record.range.start < range.start || record.range.end > range.end {
                return None;
            }
            let NodeData::IfStatement(data) = &record.data else {
                return None;
            };
            assert!(data.else_statement.is_none());
            Some((
                fixture.node(data.expression),
                fixture.node(data.then_statement),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(branches.len(), 3);
    let mut body_types = Vec::new();
    for (condition, branch_return) in branches {
        assert!(
            returns[..3]
                .iter()
                .any(|&(_, actual, _)| actual == branch_return)
        );
        let condition_type = context.get_type_at_location(condition).unwrap();
        assert_eq!(
            condition_type,
            context.store().intrinsic_bootstrap().unwrap().boolean_type
        );
        body_types.push((condition, condition_type));
    }
    for &(_, _, expression) in &returns {
        assert_eq!(context.get_type_at_location(expression), Ok(number));
        body_types.push((expression, number));
    }
    let fallback = returns[3].2;
    let NodeData::BinaryExpression(binary) = &fixture.source.arena.get(fallback.node).unwrap().data
    else {
        panic!("the last return must retain its logical fallback")
    };
    assert_eq!(
        fixture
            .source
            .arena
            .get(binary.operator_token)
            .unwrap()
            .kind,
        SyntaxKind::BarBarToken
    );
    let left = fixture.node(binary.left);
    let right = fixture.node(binary.right);
    let NodeData::ElementAccessExpression(left_access) =
        &fixture.source.arena.get(left.node).unwrap().data
    else {
        panic!("the fallback must retain its PropertyKey index access")
    };
    let NodeData::ElementAccessExpression(right_access) =
        &fixture.source.arena.get(right.node).unwrap().data
    else {
        panic!("the fallback must retain its target index access")
    };
    assert_eq!(
        context.get_symbol_at_location(fixture.node(left_access.expression)),
        Ok(Some(symbol(context, platforms.declaration)))
    );
    assert_eq!(
        context.get_symbol_at_location(fixture.node(right_access.expression)),
        Ok(Some(symbol(context, target.declaration)))
    );
    let left_type = context.get_type_at_location(left).unwrap();
    assert_union(context, left_type, &[number, undefined]);
    assert_eq!(context.get_type_at_location(right), Ok(number));
    body_types.extend([(left, left_type), (right, number)]);
    let result = fixture.binding("result");
    assert_eq!(context.get_type_at_location(result.name), Ok(number));
    assert_eq!(context.get_type_at_location(result.initializer), Ok(number));

    (
        Observation {
            target: target_type,
            construction: selected,
            handler,
            handler_context,
            raw_method_context,
            context_signature,
            method_owner,
            method_type,
            method_signature,
            parameters,
            returned,
            captures,
            body_types,
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
        panic!("the complete method body must issue exactly one local assignment error")
    };
    let name = fixture.binding("checked").name;
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.node, Some(name));
    assert_eq!(diagnostic.range_override, None);
    let range = fixture.source.arena.get(name.node).unwrap().range;
    assert_eq!((range.start.get(), range.end.get()), (200, 207));
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
                let location = fixture.node(id);
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

fn check(source: &str, negative: bool, later_captures: bool) {
    let fixture = Fixture::new(source);
    let (construction, _, _, method) = fixture.construction();
    let NodeData::MethodDeclaration(data) = &fixture.source.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::ParameterDeclaration(parameter) = &fixture
        .source
        .arena
        .get(data.parameters.nodes[0])
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let first_parameter = fixture.node(parameter.name);
    for first_query in [None, Some(construction), Some(first_parameter)] {
        let mut context = fixture.context();
        let source_root = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source_root)
                .is_some_and(|links| links.type_checked)
        );
        let queried = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(FILE).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_root)
                .unwrap()
                .type_checked
        );
        assert_diagnostics(&fixture, &context, negative);
        let observed = observe(&fixture, &mut context, negative, later_captures);
        if let Some((node, type_)) = queried {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        assert_diagnostics(&fixture, &context, negative);
        let warm = snapshot(&context, &fixture);
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                observe(&fixture, &mut context, negative, later_captures),
                observed
            );
            assert_diagnostics(&fixture, &context, negative);
            assert_eq!(snapshot(&context, &fixture), warm);
        }
    }
}

#[test]
fn proxy_method_statements_check_all_returns_and_indexed_fallback() {
    assert_eq!(SOURCE.matches(CAPTURES).count(), 1);
    let source =
        SOURCE
            .replacen(CAPTURES, "", 1)
            .replacen("const mix", &format!("{CAPTURES}const mix"), 1);
    check(&source, false, false);
}

#[test]
fn proxy_method_statements_keep_later_exported_capture_symbols() {
    assert_eq!(SOURCE.len(), 539);
    check(SOURCE, false, true);
}

#[test]
fn proxy_method_statements_report_local_assignment_error_with_contextual_any() {
    assert_eq!(SOURCE.matches("checked: number").count(), 1);
    let source = SOURCE.replacen("checked: number", "checked: string", 1);
    assert_eq!(source.len(), 539);
    check(&source, true, true);
}
