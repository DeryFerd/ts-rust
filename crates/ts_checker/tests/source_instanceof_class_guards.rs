use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
    signatures::TypePredicateKind,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(93_310);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
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

#[derive(Clone, Copy)]
struct Guard {
    expression: NodeRef,
    left: NodeRef,
    right: NodeRef,
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
            source: parse("/instanceof-guards.ts", source),
            libraries: LIBRARIES
                .iter()
                .map(|(name, text)| parse(name, text))
                .collect(),
        }
    }

    fn node(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), FILE, node)
    }

    fn declaration(&self, expected: &str) -> NodeRef {
        self.source
            .arena
            .iter()
            .find_map(|(id, record)| {
                let name = match &record.data {
                    NodeData::ClassDeclaration(class) => class.name,
                    NodeData::FunctionDeclaration(function) => function.name,
                    _ => None,
                }?;
                let NodeData::Identifier(name) = &self.source.arena.get(name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(self.node(id))
            })
            .unwrap_or_else(|| panic!("missing declaration {expected}"))
    }

    fn initializer(&self, expected: &str) -> NodeRef {
        self.source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then(|| self.node(variable.initializer.unwrap()))
            })
            .unwrap_or_else(|| panic!("missing initialized variable {expected}"))
    }

    fn guard(&self) -> Guard {
        let guards = self
            .source
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::BinaryExpression(expression) = &record.data else {
                    return None;
                };
                (self.source.arena.get(expression.operator_token)?.kind
                    == SyntaxKind::InstanceOfKeyword)
                .then_some(Guard {
                    expression: self.node(id),
                    left: self.node(expression.left),
                    right: self.node(expression.right),
                })
            })
            .collect::<Vec<_>>();
        let [guard] = guards.as_slice() else {
            panic!("one instanceof expression")
        };
        *guard
    }

    fn check(&self) -> CanonicalCheckerContext<'_> {
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
                "\"/instanceof-guards.ts\"".to_owned(),
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
        let mut context = CanonicalCheckerContext::new(
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
        .unwrap();
        let source = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source)
                .is_some_and(|links| links.type_checked)
        );
        assert!(
            context
                .store()
                .type_node_links(self.guard().expression)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        context.check_source_file(FILE).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source)
                .unwrap()
                .type_checked
        );
        context
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
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

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn class_types(
    context: &mut CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    name: &str,
) -> (SemanticSymbolId, TypeId, TypeId) {
    let declaration = fixture.declaration(name);
    let owner = symbol(context, declaration);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let shells = members.shells();
    assert_eq!(shells.symbol(), owner);
    assert_eq!(shells.declaration(), declaration);
    let instance = shells.instance_type();
    let constructor = shells.value_type();
    assert_ne!(instance, constructor);
    assert_eq!(
        context.store().type_payload(instance).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context.store().type_payload(constructor).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context
            .store()
            .signature(members.default_construct_signature())
            .unwrap()
            .resolved_return_type(),
        Some(instance),
    );
    (owner, instance, constructor)
}

fn assert_boolean(context: &mut CanonicalCheckerContext<'_>, guard: Guard) {
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    assert_eq!(resolved_type(context, guard.expression), boolean);
    assert_eq!(context.get_type_at_location(guard.expression), Ok(boolean));
}

fn assert_diagnostic(context: &CanonicalCheckerContext<'_>, code: u32, node: NodeRef, text: &str) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("one operand diagnostic: {:?}", context.diagnostics())
    };
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.diagnostic.render().unwrap(), text);
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, fixture: &Fixture) {
    let counts = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_predicate_len(),
            store.symbol_store().symbol_table_len(),
        ]
    };
    let links = |context: &CanonicalCheckerContext<'_>| {
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
                    context.store().array_literal_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let expected_counts = counts(context);
    let expected_links = links(context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(context), expected_counts);
    assert_eq!(links(context), expected_links);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn declared_instanceof_predicate_keeps_class_and_boolean_identity() {
    let fixture = Fixture::new(concat!(
        "class CancelledError extends Error { reason: string = \"cancelled\"; }\n",
        "function isCancelledError(value: any): value is CancelledError {\n",
        "  return value instanceof CancelledError;\n",
        "}\n",
    ));
    let guard = fixture.guard();
    let mut context = fixture.check();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let (owner, instance, constructor) = class_types(&mut context, &fixture, "CancelledError");
    let base = context
        .get_nongeneric_class_members(owner)
        .unwrap()
        .base()
        .unwrap();
    let error = global(&context, "Error");
    assert_eq!(base.symbol(), error);
    assert_eq!(
        context.store().declared_type_links(error).unwrap().declared_type,
        Some(base.instance_type())
    );
    assert_eq!(
        context.store().value_symbol_links(error).unwrap().resolved_type,
        Some(base.value_type())
    );
    assert_eq!(base.applied_instance_type(), base.instance_type());
    assert_ne!(base.instance_type(), instance);
    assert_boolean(&mut context, guard);
    assert_eq!(resolved_type(&context, guard.right), constructor);
    assert_eq!(
        context
            .store()
            .symbol_node_links(guard.right)
            .unwrap()
            .resolved_symbol,
        Some(owner)
    );
    assert_eq!(
        resolved_type(&context, guard.left),
        context.store().intrinsic_bootstrap().unwrap().any_type
    );
    let function = fixture.declaration("isCancelledError");
    let NodeData::FunctionDeclaration(data) =
        &fixture.source.arena.get(function.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("one declared predicate parameter")
    };
    let parameter = symbol(&context, fixture.node(*parameter));
    let signature = context
        .store()
        .signature_links(function)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    assert_eq!(context.get_return_type_of_signature(signature), Ok(boolean));
    let signature = context.store().signature(signature).unwrap();
    assert_eq!(signature.declaration(), Some(function));
    assert_eq!(signature.parameters(), &[parameter]);
    assert_eq!(signature.resolved_return_type(), Some(boolean));
    let predicate = context
        .store()
        .type_predicate(signature.resolved_type_predicate().unwrap())
        .unwrap();
    assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
    assert_eq!(predicate.parameter_index(), 0);
    assert_eq!(predicate.parameter_name(), "value");
    assert_eq!(predicate.type_id(), Some(instance));
    assert_replay(&mut context, &fixture);
}

#[test]
fn instanceof_class_guard_narrows_both_branches_and_replays() {
    let fixture = Fixture::new(concat!(
        "class CancelledError { reason: string = \"cancelled\"; }\n",
        "class NetworkError { status: number = 500; }\n",
        "function classify(value: CancelledError | NetworkError): CancelledError | NetworkError {\n",
        "  if (value instanceof CancelledError) {\n",
        "    const matched: CancelledError = value;\n",
        "    return matched;\n",
        "  } else {\n",
        "    const unmatched: NetworkError = value;\n",
        "    return unmatched;\n",
        "  }\n",
        "}\n",
    ));
    let guard = fixture.guard();
    let mut context = fixture.check();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let (_, cancelled, constructor) = class_types(&mut context, &fixture, "CancelledError");
    let (_, network, _) = class_types(&mut context, &fixture, "NetworkError");
    assert_ne!(cancelled, network);
    assert_boolean(&mut context, guard);
    assert_eq!(resolved_type(&context, guard.right), constructor);
    assert_eq!(
        resolved_type(&context, fixture.initializer("matched")),
        cancelled
    );
    assert_eq!(
        resolved_type(&context, fixture.initializer("unmatched")),
        network
    );
    assert_replay(&mut context, &fixture);
}

#[test]
fn instanceof_reports_a_primitive_left_operand() {
    let fixture = Fixture::new(concat!(
        "class Box { value: number = 1; }\n",
        "function invalidLeft(value: string): boolean { return value instanceof Box; }\n",
    ));
    let guard = fixture.guard();
    let mut context = fixture.check();
    assert_diagnostic(
        &context,
        2358,
        guard.left,
        "The left-hand side of an 'instanceof' expression must be of type 'any', an object type or a type parameter.",
    );
    let (_, _, constructor) = class_types(&mut context, &fixture, "Box");
    assert_eq!(resolved_type(&context, guard.right), constructor);
    assert_boolean(&mut context, guard);
    assert_replay(&mut context, &fixture);
}

#[test]
fn instanceof_reports_a_primitive_right_operand() {
    let fixture = Fixture::new(concat!(
        "class Box { value: number = 1; }\n",
        "function invalidRight(value: Box, constructor: number): boolean {\n",
        "  return value instanceof constructor;\n",
        "}\n",
    ));
    let guard = fixture.guard();
    let mut context = fixture.check();
    assert_diagnostic(
        &context,
        2359,
        guard.right,
        "The right-hand side of an 'instanceof' expression must be either of type 'any', a class, function, or other type assignable to the 'Function' interface type, or an object type with a 'Symbol.hasInstance' method.",
    );
    let (_, instance, _) = class_types(&mut context, &fixture, "Box");
    assert_eq!(resolved_type(&context, guard.left), instance);
    assert_eq!(
        resolved_type(&context, guard.right),
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert_boolean(&mut context, guard);
    assert_replay(&mut context, &fixture);
}
