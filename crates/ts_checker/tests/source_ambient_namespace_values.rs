use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARATIONS: FileId = FileId::new(202_960);
const SOURCE: FileId = FileId::new(202_961);
const AMBIENT: &str = concat!(
    "declare namespace Runtime {\n",
    "  function open(path: string): string;\n",
    "  const version: number;\n",
    "  const errors: { code: string };\n",
    "  interface TypeOnly { name: string; }\n",
    "}\n",
);
const PROGRAM: &str = concat!(
    "const { open, version, errors } = Runtime;\n",
    "const runtime = Runtime;\n",
    "const content: string = open(\"data\");\n",
    "const code: string = errors.code;\n",
    "const copiedVersion: number = runtime.version;\n",
);
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
    declarations: ParseResult,
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parse = |text: &str| {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            parsed
        };
        Self {
            declarations: parse(AMBIENT),
            source: parse(source),
            libraries: LIBRARIES.iter().map(|(_, text)| parse(text)).collect(),
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
                    true,
                )
            })
            .chain([
                (
                    DECLARATIONS,
                    &self.declarations,
                    "\"/runtime.d.ts\"".to_owned(),
                    true,
                    false,
                ),
                (
                    SOURCE,
                    &self.source,
                    "\"/consumer.ts\"".to_owned(),
                    false,
                    false,
                ),
            ])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, declaration, library) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *declaration,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                strict_function_types: true,
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn declaration(&self, file: FileId, name: &str) -> NodeRef {
        let parsed = if file == DECLARATIONS {
            &self.declarations
        } else {
            &self.source
        };
        parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let name_node = match &record.data {
                    NodeData::ModuleDeclaration(data) => data.name,
                    NodeData::FunctionDeclaration(data) => data.name?,
                    NodeData::InterfaceDeclaration(data) => data.name,
                    NodeData::VariableDeclaration(data) => data.name,
                    NodeData::BindingElement(data) => data.name?,
                    NodeData::ParameterDeclaration(data) => data.name,
                    NodeData::PropertyDeclaration(data) => data.name,
                    NodeData::PropertySignatureDeclaration(data) => data.name,
                    _ => return None,
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, id))
            })
            .unwrap_or_else(|| panic!("missing {name} declaration"))
    }

    fn initializer(&self, name: &str) -> NodeRef {
        let declaration = self.declaration(SOURCE, name);
        let NodeData::VariableDeclaration(data) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected a variable initializer")
        };
        self.source_node(data.initializer.unwrap())
    }

    fn source_node(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), SOURCE, node)
    }
}

fn owner(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_namespace(
    context: &CanonicalCheckerContext<'_>,
    symbol: SemanticSymbolId,
    expected: &[SemanticSymbolId],
) -> TypeId {
    let type_ = value_type(context, symbol);
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(symbol));
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert!(record.object_flags().contains(ObjectFlags::ANONYMOUS));
    let TypeData::Object(object) = record.data() else {
        panic!("the namespace value must remain its canonical object")
    };
    assert_eq!(object.structured.call_signature_count, 0);
    assert!(
        object.structured.signatures.as_ref().is_none_or(Vec::is_empty)
    );
    let properties = object.structured.properties.as_ref().unwrap();
    assert_eq!(properties.len(), expected.len());
    for &member in expected {
        assert!(properties.contains(&member));
        assert_eq!(
            context.store().symbol(member).unwrap().parent(),
            Some(symbol)
        );
        let exports = context.store().symbol(symbol).unwrap().exports().unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source(context.store().symbol(member).unwrap().name().as_utf8().unwrap()),
            Some(member),
        );
    }
    type_
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        [(DECLARATIONS, &fixture.declarations), (SOURCE, &fixture.source)]
            .into_iter()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, id);
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
    )
}

#[allow(clippy::too_many_lines)] // Check source ownership, member types and both query orders together.
fn check_namespace_values(source: &str, invalid: bool) {
    let fixture = Fixture::new(source);
    for query_first in [false, true] {
        let mut context = fixture.context();
        let runtime_read = fixture.initializer("runtime");
        let binding_read = fixture
            .source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                matches!(
                    fixture.source.arena.get(variable.name)?.data,
                    NodeData::BindingPattern(_)
                )
                .then(|| fixture.source_node(variable.initializer.unwrap()))
            })
            .unwrap();
        let queried = query_first.then(|| context.get_type_at_location(runtime_read).unwrap());
        context.check_source_file(SOURCE).unwrap();
        if invalid {
            let declaration = fixture.declaration(SOURCE, "content");
            let NodeData::VariableDeclaration(data) =
                &fixture.source.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("one assignment diagnostic: {:?}", context.diagnostics())
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.node, Some(fixture.source_node(data.name)));
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'string' is not assignable to type 'number'."
            );
        } else {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
        let namespace = owner(&context, fixture.declaration(DECLARATIONS, "Runtime"));
        let open = owner(&context, fixture.declaration(DECLARATIONS, "open"));
        let version = owner(&context, fixture.declaration(DECLARATIONS, "version"));
        let errors = owner(&context, fixture.declaration(DECLARATIONS, "errors"));
        let code = owner(&context, fixture.declaration(DECLARATIONS, "code"));
        let type_only = owner(&context, fixture.declaration(DECLARATIONS, "TypeOnly"));
        assert!(
            context
                .store()
                .symbol(namespace)
                .unwrap()
                .flags()
                .contains(SymbolFlags::VALUE_MODULE)
        );
        let runtime_type = assert_namespace(&context, namespace, &[open, version, errors]);
        let errors_type = value_type(&context, errors);
        let TypeData::Object(error_object) =
            context.store().type_payload(errors_type).unwrap().data()
        else {
            panic!("the exported object must keep its declared property type")
        };
        assert_eq!(
            error_object.structured.properties.as_deref(),
            Some([code].as_slice())
        );
        assert_eq!(checked_type(&context, runtime_read), runtime_type);
        assert_eq!(checked_type(&context, binding_read), runtime_type);
        assert_eq!(
            value_type(
                &context,
                owner(&context, fixture.declaration(SOURCE, "runtime")),
            ),
            runtime_type
        );
        assert!(queried.is_none_or(|type_| type_ == runtime_type));
        assert_eq!(
            context
                .store()
                .symbol_node_links(runtime_read)
                .unwrap()
                .resolved_symbol,
            Some(namespace)
        );
        let exports = context.store().symbol(namespace).unwrap().exports().unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("TypeOnly"),
            Some(type_only)
        );
        assert!(
            context
                .store()
                .value_symbol_links(type_only)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let open_type = value_type(&context, open);
        for (name, expected) in [
            ("open", open_type),
            ("version", number),
            ("errors", errors_type),
        ] {
            let binding = owner(&context, fixture.declaration(SOURCE, name));
            assert_ne!(binding, namespace);
            assert_eq!(value_type(&context, binding), expected);
        }
        assert_eq!(value_type(&context, version), number);
        assert_eq!(value_type(&context, code), string);
        let open_declaration = fixture.declaration(DECLARATIONS, "open");
        let signature = context
            .store()
            .signature_links(open_declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let signature_record = context.store().signature(signature).unwrap();
        assert_eq!(signature_record.declaration(), Some(open_declaration));
        let parameter = owner(&context, fixture.declaration(DECLARATIONS, "path"));
        assert_eq!(signature_record.parameters(), &[parameter]);
        assert_eq!(value_type(&context, parameter), string);
        assert_eq!(signature_record.resolved_return_type(), Some(string));
        let call = fixture.initializer("content");
        assert_eq!(checked_type(&context, call), string);
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
        assert_eq!(checked_type(&context, fixture.initializer("code")), string);
        assert_eq!(
            checked_type(&context, fixture.initializer("copiedVersion")),
            number
        );
        let warm = snapshot(&context, &fixture);
        for _ in 0..2 {
            assert_eq!(context.get_type_at_location(runtime_read), Ok(runtime_type));
            assert_eq!(context.get_type_at_location(call), Ok(string));
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(snapshot(&context, &fixture), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn ambient_namespace_values_keep_export_types_and_replay() {
    check_namespace_values(PROGRAM, false);
}

#[test]
fn ambient_namespace_values_report_member_result_assignment_errors() {
    let invalid = PROGRAM.replace("content: string", "content: number");
    assert_ne!(invalid, PROGRAM);
    check_namespace_values(&invalid, true);
}
