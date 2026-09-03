use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SourceCheckError, TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(0);
const DECORATORS: FileId = FileId::new(1);
const LEGACY: FileId = FileId::new(2);
const GLOBALS: FileId = FileId::new(3);
const SOURCE: FileId = FileId::new(4);
const DECLARATIONS: &str = concat!(
    "interface NumberOperations { select(left: number, right: number): number; }\n",
    "declare var numbers: NumberOperations;\n",
    "declare var fallback: number;\n",
);
const CONSUMER: &str = concat!(
    "export {};\n",
    "class Usage {\n",
    "  delay!: number;\n",
    "  update(value: number | undefined, flag: boolean, bad: string): void {\n",
    "    numbers.select(this.delay || 0, value ?? (flag ? fallback : 5 * 60 * 1000));\n",
    "    numbers.select(bad, fallback);\n",
    "  }\n",
    "}\n",
);

struct Inputs {
    library: ParseResult,
    decorators: ParseResult,
    legacy: ParseResult,
    globals: ParseResult,
    source: ParseResult,
}

impl Inputs {
    fn new(source: &str) -> Self {
        Self {
            library: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.d.ts"
            )),
            legacy: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.legacy.d.ts"
            )),
            globals: parse_source_file(DECLARATIONS),
            source: parse_source_file(source),
        }
    }

    fn files(&self) -> [(FileId, &ParseResult, &str); 5] {
        [
            (LIBRARY, &self.library, "/lib.es5.d.ts"),
            (DECORATORS, &self.decorators, "/lib.decorators.d.ts"),
            (LEGACY, &self.legacy, "/lib.decorators.legacy.d.ts"),
            (GLOBALS, &self.globals, "/values.d.ts"),
            (SOURCE, &self.source, "/consumer.ts"),
        ]
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in self.files() {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        file != SOURCE,
                        file != SOURCE && file != GLOBALS,
                        if file == SOURCE {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _) in self.files() {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            self.files()
                .into_iter()
                .map(|(file, parsed, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_function_types: true,
                strict_property_initialization: true,
                no_implicit_any: true,
                no_implicit_this: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.diagnostics().is_empty());
        context
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let mut found = parsed.arena.iter().filter_map(|(id, record)| {
        let name = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::PropertyDeclaration(data) => data.name,
            NodeData::MethodSignatureDeclaration(data) => data.name,
            NodeData::MethodDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == expected).then(|| node(parsed, file, id))
    });
    let result = found
        .next()
        .unwrap_or_else(|| panic!("missing declaration {expected}"));
    assert!(found.next().is_none());
    result
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

fn cached_type(context: &CanonicalCheckerContext<'_>, expression: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(expression)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, call: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(call)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression).then(|| node(parsed, SOURCE, id))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn global_type(context: &mut CanonicalCheckerContext<'_>, inputs: &Inputs, name: &str) -> TypeId {
    let declaration = declaration(&inputs.globals, GLOBALS, name);
    let NodeData::VariableDeclaration(data) =
        &inputs.globals.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.initializer.is_none());
    let annotation = node(&inputs.globals, GLOBALS, data.type_.unwrap());
    assert_eq!(
        inputs.globals.arena.get(annotation.node).unwrap().parent,
        Some(declaration.node)
    );
    let owner = symbol(context, declaration);
    let globals = context.store().intrinsic_bootstrap().unwrap().globals;
    assert_eq!(
        context
            .store()
            .symbol_table(globals)
            .unwrap()
            .get_source(name),
        Some(owner)
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().value_declaration(),
        Some(declaration)
    );
    let type_ = context.get_type_from_type_node(annotation).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    for (id, record) in inputs.source.arena.iter() {
        if let NodeData::Identifier(identifier) = &record.data
            && identifier.text == name
        {
            let read = node(&inputs.source, SOURCE, id);
            assert_eq!(context.get_symbol_at_location(read), Ok(Some(owner)));
            assert_eq!(context.get_type_at_location(read), Ok(type_));
            assert_eq!(cached_type(context, read), type_);
        }
    }
    type_
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    inputs: &Inputs,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        [(GLOBALS, &inputs.globals), (SOURCE, &inputs.source)]
            .into_iter()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(id, _)| {
                    let node = node(parsed, file, id);
                    (
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        inputs.files().map(|(file, _, _)| {
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned()
        }),
        context.diagnostics().clone(),
    )
}

#[test]
#[allow(clippy::too_many_lines)]
fn class_global_values_keep_declared_types_argument_errors_and_replay() {
    let inputs = Inputs::new(CONSUMER);
    let mut context = inputs.context();
    context.check_source_file(SOURCE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let receiver = global_type(&mut context, &inputs, "numbers");
    assert_eq!(global_type(&mut context, &inputs, "fallback"), number);
    let interface = declaration(&inputs.globals, GLOBALS, "NumberOperations");
    assert_eq!(
        context.store().type_payload(receiver).unwrap().symbol(),
        Some(symbol(&context, interface))
    );
    let method = declaration(&inputs.globals, GLOBALS, "select");
    let NodeData::InterfaceDeclaration(interface_data) =
        &inputs.globals.arena.get(interface.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(interface_data.members.nodes.contains(&method.node));
    assert_eq!(
        inputs.globals.arena.get(method.node).unwrap().parent,
        Some(interface.node)
    );
    let method_symbol = symbol(&context, method);
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().parent(),
        Some(symbol(&context, interface))
    );
    let calls = calls(&inputs.source);
    assert_eq!(calls.len(), 2);
    let selected = signature(&context, calls[0]);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(method));
    assert_eq!(record.parameters().len(), 2);
    assert_eq!(record.min_argument_count(), 2);
    assert_eq!(record.resolved_return_type(), Some(number));
    for parameter in record.parameters() {
        assert_eq!(
            context
                .store()
                .value_symbol_links(*parameter)
                .unwrap()
                .resolved_type,
            Some(number)
        );
    }
    let mut argument_nodes = Vec::new();
    for call in &calls {
        assert_eq!(signature(&context, *call), selected);
        assert_eq!(context.get_type_at_location(*call), Ok(number));
        let NodeData::CallExpression(data) = &inputs.source.arena.get(call.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(data.arguments.nodes.len(), 2);
        let access = node(&inputs.source, SOURCE, data.expression);
        assert_eq!(
            context.get_symbol_at_location(access),
            Ok(Some(method_symbol))
        );
        argument_nodes.extend(
            data.arguments
                .nodes
                .iter()
                .map(|id| node(&inputs.source, SOURCE, *id)),
        );
    }
    assert_eq!(
        argument_nodes
            .iter()
            .map(|node| cached_type(&context, *node))
            .collect::<Vec<_>>(),
        [number, number, string, number]
    );
    let NodeData::BinaryExpression(nullish) = &inputs
        .source
        .arena
        .get(argument_nodes[1].node)
        .unwrap()
        .data
    else {
        panic!("the global fallback stays inside the nullish argument");
    };
    let value = node(&inputs.source, SOURCE, nullish.left);
    let TypeData::Union(union) = context
        .store()
        .type_payload(cached_type(&context, value))
        .unwrap()
        .data()
    else {
        panic!("the parameter keeps its declared nullable type before the branch");
    };
    let mut declared = vec![
        number,
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type,
    ];
    declared.sort_unstable();
    assert_eq!(union.union.types, declared);
    let field = symbol(&context, declaration(&inputs.source, SOURCE, "delay"));
    assert_eq!(context.get_class_query_member_type(field), Ok(number));
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one argument error: {:?}", context.diagnostics())
    };
    assert_eq!(diagnostic.node, Some(argument_nodes[2]));
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    let warm = snapshot(&context, &inputs);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(global_type(&mut context, &inputs, "numbers"), receiver);
        assert_eq!(global_type(&mut context, &inputs, "fallback"), number);
        for call in &calls {
            assert_eq!(context.get_type_at_location(*call), Ok(number));
            assert_eq!(signature(&context, *call), selected);
        }
        assert_eq!(context.get_class_query_member_type(field), Ok(number));
        assert_eq!(snapshot(&context, &inputs), warm);
        assert!(context.store().type_resolution_is_empty());
    }
    for file in [LIBRARY, DECORATORS, LEGACY, GLOBALS] {
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked)
        );
    }
}

#[test]
fn mutable_source_local_capture_stays_unsupported() {
    let inputs = Inputs::new(concat!(
        "export {};\n",
        "let current: number | undefined = 1;\n",
        "class Usage { read(): number | undefined { return current; } }\n",
        "current = undefined;\n",
    ));
    let mut context = inputs.context();
    let returned = inputs
        .source
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ReturnStatement(data) = &record.data else {
                return None;
            };
            data.expression.map(|id| node(&inputs.source, SOURCE, id))
        })
        .unwrap();
    assert!(matches!(context.check_source_file(SOURCE),
        Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(node))) if node == returned));
    assert!(context.store().type_resolution_is_empty());
}
