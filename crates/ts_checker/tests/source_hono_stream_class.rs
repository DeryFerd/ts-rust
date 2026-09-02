use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(204_200);
const FILE: FileId = FileId::new(204_201);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

struct Fixture {
    library: ParseResult,
    source: ParseResult,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let library = parse_source_file(ES5);
        let source = parse_source_file(source);
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        Self { library, source }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in [
            (LIBRARY, &self.library, "\"/lib/lib.es5.d.ts\"", true),
            (FILE, &self.source, "\"/project/stream-async.ts\"", false),
        ] {
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
            [(LIBRARY, &self.library.arena), (FILE, &self.source.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                no_implicit_any: true,
                no_implicit_this: true,
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
}

fn reference(parsed: &ParseResult, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, node)
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

struct Method {
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    parameter_type: NodeRef,
    annotation: Option<NodeRef>,
    returned: NodeRef,
    expression: NodeRef,
    operand: NodeRef,
}

fn methods(parsed: &ParseResult) -> (NodeRef, NodeRef, Vec<Method>) {
    let classes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == SyntaxKind::ClassDeclaration).then_some(id))
        .collect::<Vec<_>>();
    let [class] = classes.as_slice() else {
        panic!("expected one real class declaration");
    };
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(*class).unwrap().data else {
        unreachable!()
    };
    let class_name = reference(parsed, FILE, data.name.unwrap());
    let methods = data
        .members
        .nodes
        .iter()
        .map(|&id| {
            let record = parsed.arena.get(id).unwrap();
            assert_eq!(record.parent, Some(*class));
            let NodeData::MethodDeclaration(method) = &record.data else {
                panic!("expected an async method");
            };
            let modifiers = method.modifiers.as_ref().unwrap();
            let [modifier] = modifiers.list.nodes.as_slice() else {
                panic!("expected the actual async modifier");
            };
            assert_eq!(
                parsed.arena.get(*modifier).unwrap().kind,
                SyntaxKind::AsyncKeyword
            );
            let [parameter] = method.parameters.nodes.as_slice() else {
                panic!("expected one actual value parameter");
            };
            let parameter_record = parsed.arena.get(*parameter).unwrap();
            assert_eq!(parameter_record.parent, Some(id));
            let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
                unreachable!()
            };
            let body = method.body.unwrap();
            let NodeData::Block(block) = &parsed.arena.get(body).unwrap().data else {
                unreachable!()
            };
            let [returned] = block.statements.nodes.as_slice() else {
                panic!("expected one actual return statement");
            };
            let return_record = parsed.arena.get(*returned).unwrap();
            assert_eq!(return_record.parent, Some(body));
            let NodeData::ReturnStatement(return_data) = &return_record.data else {
                unreachable!()
            };
            let expression = return_data.expression.unwrap();
            assert_eq!(
                parsed.arena.get(expression).unwrap().parent,
                Some(*returned)
            );
            let operand = match &parsed.arena.get(expression).unwrap().data {
                NodeData::AwaitExpression(awaited) => {
                    assert_eq!(
                        parsed.arena.get(awaited.expression).unwrap().parent,
                        Some(expression)
                    );
                    awaited.expression
                }
                NodeData::Identifier(_) => expression,
                _ => panic!("expected a parameter read or an awaited parameter read"),
            };
            Method {
                declaration: reference(parsed, FILE, id),
                name: reference(parsed, FILE, method.name),
                parameter: reference(parsed, FILE, *parameter),
                parameter_type: reference(parsed, FILE, parameter_data.type_.unwrap()),
                annotation: method.type_.map(|id| reference(parsed, FILE, id)),
                returned: reference(parsed, FILE, *returned),
                expression: reference(parsed, FILE, expression),
                operand: reference(parsed, FILE, operand),
            }
        })
        .collect();
    (reference(parsed, FILE, *class), class_name, methods)
}

fn promise_target(fixture: &Fixture, context: &mut CanonicalCheckerContext<'_>) -> TypeId {
    let declaration = fixture
        .library
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &fixture.library.arena.get(interface.name)?.data
            else {
                return None;
            };
            (name.text == "Promise").then_some(reference(&fixture.library, LIBRARY, id))
        })
        .unwrap();
    let owner = symbol(context, declaration);
    assert_eq!(
        context.store().symbol(owner).unwrap().flags(),
        SymbolFlags::INTERFACE
    );
    context.get_declared_type_of_symbol(owner).unwrap()
}

fn assert_methods(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    class: NodeRef,
    methods: &[Method],
    invalid: bool,
) -> Vec<(SemanticSymbolId, TypeId, SignatureId, TypeId)> {
    let target = promise_target(fixture, context);
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let class_symbol = symbol(context, class);
    let mut identities = Vec::new();
    for method in methods {
        let method_symbol = symbol(context, method.declaration);
        let parameter = symbol(context, method.parameter);
        let callable = context.get_type_at_location(method.name).unwrap();
        let signature = context
            .store()
            .signature_links(method.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let result = context.get_return_type_of_signature(signature).unwrap();
        let store = context.store();
        let member = store.symbol(method_symbol).unwrap();
        assert_eq!(member.flags(), SymbolFlags::METHOD);
        assert_eq!(member.parent(), Some(class_symbol));
        assert_eq!(member.value_declaration(), Some(method.declaration));
        assert_eq!(
            store
                .value_symbol_links(method_symbol)
                .unwrap()
                .resolved_type,
            Some(callable)
        );
        let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
            panic!("expected the canonical method callable");
        };
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some([signature].as_slice())
        );
        let checked = store.signature(signature).unwrap();
        assert_eq!(checked.declaration(), Some(method.declaration));
        assert_eq!(checked.this_parameter(), None);
        assert_eq!(checked.parameters(), [parameter]);
        assert_eq!(checked.resolved_return_type(), Some(result));
        let TypeData::TypeReference(promise) = store.type_payload(result).unwrap().data() else {
            panic!("expected a real Promise<number> reference");
        };
        assert_eq!(promise.object.target, Some(target));
        assert_eq!(
            promise.resolved_type_arguments.as_deref(),
            Some([number].as_slice())
        );

        let parameter_type = match fixture
            .source
            .arena
            .get(method.parameter_type.node)
            .unwrap()
            .kind
        {
            SyntaxKind::NumberKeyword => number,
            SyntaxKind::StringKeyword => string,
            SyntaxKind::TypeReference => result,
            _ => panic!("unexpected fixture parameter annotation"),
        };
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            Some(parameter_type)
        );
        assert_eq!(
            context.get_symbol_at_location(method.operand).unwrap(),
            Some(parameter)
        );
        assert_eq!(
            context.get_type_at_location(method.operand),
            Ok(parameter_type)
        );
        let expression_type = if method.expression == method.operand {
            parameter_type
        } else {
            number
        };
        assert_eq!(
            context.get_type_at_location(method.expression),
            Ok(expression_type)
        );
        identities.push((method_symbol, callable, signature, result));
    }
    let diagnostics = context.diagnostics().as_slice();
    if invalid {
        assert_eq!(methods.len(), 1);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.node, Some(methods[0].returned));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
    } else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
    identities
}

fn check(source: &str, invalid: bool) {
    let fixture = Fixture::new(source);
    let (class, class_name, methods) = methods(&fixture.source);
    assert_eq!(methods.len(), if invalid { 1 } else { 3 });
    assert_eq!(
        methods
            .iter()
            .filter(|method| method.annotation.is_none())
            .count(),
        usize::from(!invalid)
    );
    for query_first in [false, true] {
        let mut context = fixture.context();
        let early = query_first.then(|| context.get_type_at_location(class_name).unwrap());
        context.check_source_file(FILE).unwrap();
        let identities = assert_methods(&fixture, &mut context, class, &methods, invalid);
        if let Some(early) = early {
            assert_eq!(context.get_type_at_location(class_name), Ok(early));
        }
        let diagnostics = context.diagnostics().clone();
        for recheck in [false, true, true] {
            if recheck {
                context.recheck_source_file(FILE).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            assert_eq!(
                assert_methods(&fixture, &mut context, class, &methods, invalid),
                identities
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn async_class_methods_keep_real_promises_awaited_values_and_inferred_returns() {
    check(
        concat!(
            "class Stream {\n",
            "  async read(value: Promise<number>): Promise<number> { return await value; }\n",
            "  async inferred(value: number) { return value; }\n",
            "  async pass(value: Promise<number>): Promise<number> { return value; }\n",
            "}\n",
        ),
        false,
    );
}

#[test]
fn async_class_return_mismatch_keeps_native_ts2322() {
    check(
        concat!(
            "class Stream {\n",
            "  async read(value: string): Promise<number> { return value; }\n",
            "}\n",
        ),
        true,
    );
}
