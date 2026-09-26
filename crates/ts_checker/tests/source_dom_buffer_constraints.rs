use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(6);
const LIBRARIES: [(&str, &str); 6] = [
    ("es5", include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
    (
        "decorators",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "decorators.legacy",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
    (
        "es2015.symbol",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
    ),
    (
        "es2015.symbol.wellknown",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.wellknown.d.ts"),
    ),
    (
        "es2017.sharedmemory",
        include_str!("../../ts_bundled/libs/lib.es2017.sharedmemory.d.ts"),
    ),
];

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

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/lib.{}.d.ts\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([(
                FILE,
                &self.source,
                "\"/project/buffer-constraints.ts\"".to_owned(),
                false,
            )])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
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
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn variable_nodes(&self, expected: &str) -> (Option<NodeRef>, Option<NodeRef>) {
        self.source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(data) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(data.name)?.data else {
                    return None;
                };
                (name.text == expected).then(|| {
                    let reference = |node| NodeRef::new(self.source.arena.id(), FILE, node);
                    (data.type_.map(reference), data.initializer.map(reference))
                })
            })
            .unwrap_or_else(|| panic!("missing variable {expected}"))
    }

    fn annotation(&self, name: &str) -> NodeRef {
        self.variable_nodes(name).0.unwrap()
    }

    fn type_of(&self, context: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
        context
            .get_type_from_type_node(self.annotation(name))
            .unwrap()
    }

    fn read_type(&self, context: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
        let expression = self.variable_nodes(name).1.unwrap();
        assert!(matches!(
            self.source.arena.get(expression.node).unwrap().data,
            NodeData::PropertyAccessExpression(_)
        ));
        context.get_type_at_location(expression).unwrap()
    }
}

fn interface_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
    argument: TypeId,
    constraint: TypeId,
) {
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(type_).unwrap().data() else {
        panic!("expected a real generic interface reference");
    };
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([argument].as_slice())
    );
    let target = reference.object.target.unwrap();
    assert_eq!(store.type_payload(target).unwrap().symbol(), Some(owner));
    let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
        panic!("expected the declared interface target");
    };
    let [parameter] = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .unwrap()
    else {
        panic!("expected the declared interface formal");
    };
    let TypeData::TypeParameter(parameter) = store.type_payload(*parameter).unwrap().data() else {
        panic!("expected a real type parameter");
    };
    assert_eq!(parameter.constraint, Some(constraint));
}

fn assert_replay(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    annotations: &[(&str, TypeId)],
    reads: &[(&str, TypeId)],
) {
    let queries = |context: &mut CanonicalCheckerContext<'_>| {
        for &(name, expected) in annotations {
            assert_eq!(fixture.type_of(context, name), expected, "{name}");
        }
        for &(name, expected) in reads {
            assert_eq!(fixture.read_type(context, name), expected, "{name}");
        }
    };
    let counts = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.type_alias_len(),
        ]
    };
    queries(context);
    let warm = counts(context);
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        queries(context);
        assert_eq!(counts(context), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn buffer_views_keep_library_constraints_and_resolved_buffer_types() {
    let fixture = Fixture::new(concat!(
        "declare const array: ArrayBuffer;\n",
        "declare const shared: SharedArrayBuffer;\n",
        "declare const constraint: ArrayBufferLike;\n",
        "declare const view: ArrayBufferView<ArrayBuffer>;\n",
        "declare const sharedView: ArrayBufferView<SharedArrayBuffer>;\n",
        "const buffer = view.buffer;\n",
        "const sharedBuffer = sharedView.buffer;\n",
        "const length = view.byteLength;\n",
    ));
    let mut context = fixture.context();
    let view = fixture.type_of(&mut context, "view");
    let shared_view = fixture.type_of(&mut context, "sharedView");
    let array = fixture.type_of(&mut context, "array");
    let shared = fixture.type_of(&mut context, "shared");
    let constraint = fixture.type_of(&mut context, "constraint");
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let owner = interface_symbol(
        &context,
        &fixture.libraries[0],
        FileId::new(0),
        "ArrayBufferView",
    );
    assert_reference(&context, view, owner, array, constraint);
    assert_reference(&context, shared_view, owner, shared, constraint);
    let merged = interface_symbol(
        &context,
        &fixture.libraries[0],
        FileId::new(0),
        "ArrayBufferTypes",
    );
    assert_eq!(
        interface_symbol(
            &context,
            &fixture.libraries[5],
            FileId::new(5),
            "ArrayBufferTypes"
        ),
        merged
    );
    assert_eq!(
        context
            .store()
            .symbol(merged)
            .unwrap()
            .declarations()
            .unwrap()
            .len(),
        2
    );
    let TypeData::Union(union) = context.store().type_payload(constraint).unwrap().data() else {
        panic!("the library constraint must include both buffer types");
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&array));
    assert!(union.union.types.contains(&shared));
    assert_replay(
        &fixture,
        &mut context,
        &[
            ("array", array),
            ("shared", shared),
            ("constraint", constraint),
            ("view", view),
            ("sharedView", shared_view),
        ],
        &[("buffer", array), ("sharedBuffer", shared), ("length", number)],
    );
}

#[test]
fn merged_interface_indexed_aliases_supply_generic_constraints() {
    let fixture = Fixture::new(concat!(
        "interface Choices { text: string; }\n",
        "interface Choices { count: number; }\n",
        "type Choice = Choices[keyof Choices];\n",
        "interface Box<T extends Choice> { readonly value: T; }\n",
        "declare const constraint: Choice;\n",
        "declare const text: Box<string>;\n",
        "declare const count: Box<number>;\n",
        "const textValue = text.value;\n",
        "const countValue = count.value;\n",
    ));
    let mut context = fixture.context();
    let text = fixture.type_of(&mut context, "text");
    let count = fixture.type_of(&mut context, "count");
    let constraint = fixture.type_of(&mut context, "constraint");
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let choices = interface_symbol(&context, &fixture.source, FILE, "Choices");
    assert_eq!(
        context
            .store()
            .symbol(choices)
            .unwrap()
            .declarations()
            .unwrap()
            .len(),
        2
    );
    let owner = interface_symbol(&context, &fixture.source, FILE, "Box");
    assert_reference(&context, text, owner, string, constraint);
    assert_reference(&context, count, owner, number, constraint);
    let TypeData::Union(union) = context.store().type_payload(constraint).unwrap().data() else {
        panic!("the merged interface must contribute both value types");
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&string));
    assert!(union.union.types.contains(&number));
    assert_replay(
        &fixture,
        &mut context,
        &[("constraint", constraint), ("text", text), ("count", count)],
        &[("textValue", string), ("countValue", number)],
    );
}

#[test]
fn invalid_buffer_view_argument_keeps_the_native_constraint_diagnostic() {
    let fixture = Fixture::new("declare const invalid: ArrayBufferView<number>;\n");
    let mut context = fixture.context();
    let invalid = fixture.type_of(&mut context, "invalid");
    context.check_source_file(FILE).unwrap();
    let annotation = fixture.annotation("invalid");
    let NodeData::TypeReferenceNode(reference) =
        &fixture.source.arena.get(annotation.node).unwrap().data
    else {
        panic!("expected the written buffer view reference");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one written type argument");
    };
    let argument = NodeRef::new(annotation.arena, annotation.file, *argument);
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.diagnostic.code(), 2344);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "ArrayBufferLike"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'ArrayBufferLike'."
    );
    assert_replay(&fixture, &mut context, &[("invalid", invalid)], &[]);
}
