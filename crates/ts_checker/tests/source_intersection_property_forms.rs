use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(20_451);
const SOURCE: &str = concat!(
    "interface Registry { decimal: never; percent: never }\n",
    "type Style = keyof Registry;\n",
    "type Grouping = \"on\" extends \"on\" ? boolean : { unused: string };\n",
    "interface Left {\n",
    "  mode: \"lookup\" | \"best fit\" | undefined;\n",
    "  style: Style;\n",
    "  grouping: Grouping;\n",
    "}\n",
    "interface Right { marker: number }\n",
    "type Options = Left & Right;\n",
    "declare const options: Options;\n",
    "const readMode = options.mode;\n",
    "const readStyle = options.style;\n",
    "const readGrouping = options.grouping;\n",
    "const readMarker = options.marker;\n",
    "const invalid: number = options.grouping;\n",
);

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/project/intersection-property-forms.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::PropertyDeclaration(data)
                    if record.kind == SyntaxKind::PropertyDeclaration
                        && data.initializer.is_none()
                        && data.type_.is_some() =>
                {
                    let parent = parsed.arena.get(record.parent?)?;
                    let NodeData::InterfaceDeclaration(interface) = &parent.data else {
                        return None;
                    };
                    if parent.kind != SyntaxKind::InterfaceDeclaration
                        || !interface.members.nodes.contains(&id)
                    {
                        return None;
                    }
                    data.name
                }
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn annotation(parsed: &ParseResult, expected: &str) -> NodeRef {
    let declaration = declaration(parsed, expected);
    let type_node = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::TypeAliasDeclaration(data) => data.type_,
        NodeData::PropertyDeclaration(data) => data.type_.unwrap(),
        _ => panic!("expected an alias or property annotation for {expected}"),
    };
    assert_eq!(
        parsed.arena.get(type_node).unwrap().parent,
        Some(declaration.node)
    );
    node(parsed, type_node)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn variable_type(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol(context, declaration(parsed, expected)))
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing variable type for {expected}"))
}

fn assert_union(context: &mut CanonicalCheckerContext<'_>, type_: TypeId, expected: &[&str]) {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected the canonical union")
    };
    let members = union.union.types.clone();
    let mut actual = members
        .into_iter()
        .map(|member| context.type_to_string(member).unwrap())
        .collect::<Vec<_>>();
    actual.sort();
    assert_eq!(actual, expected);
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    aliases: Vec<Option<TypeAliasLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(parsed: &ParseResult, context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: parsed
            .arena
            .iter()
            .map(|(id, _)| store.type_node_links(node(parsed, id)).cloned())
            .collect(),
        symbols: parsed
            .arena
            .iter()
            .map(|(id, _)| store.symbol_node_links(node(parsed, id)).cloned())
            .collect(),
        values: [
            "options",
            "readMode",
            "readStyle",
            "readGrouping",
            "readMarker",
            "invalid",
        ]
        .map(|name| {
            store
                .value_symbol_links(symbol(context, declaration(parsed, name)))
                .cloned()
        })
        .into(),
        aliases: ["Style", "Grouping", "Options"]
            .map(|name| {
                store
                    .type_alias_links(symbol(context, declaration(parsed, name)))
                    .cloned()
            })
            .into(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
fn intersection_property_forms_keep_cold_and_warm_types_and_assignment_errors() {
    let parsed = parse_source_file(SOURCE);
    let options_node = annotation(&parsed, "Options");
    let properties = ["mode", "style", "grouping"].map(|name| annotation(&parsed, name));
    let grouping_node = annotation(&parsed, "Grouping");
    let NodeData::ConditionalTypeNode(conditional) =
        &parsed.arena.get(grouping_node.node).unwrap().data
    else {
        panic!("Grouping must be the written conditional")
    };
    let unused = node(&parsed, conditional.false_type);

    for prewarm_properties in [false, true] {
        let mut context = context(&parsed);
        if prewarm_properties {
            for property in properties {
                context.get_type_from_type_node(property).unwrap();
            }
        }
        let options = context.get_type_from_type_node(options_node).unwrap();
        assert!(matches!(
            context.store().type_payload(options).unwrap().data(),
            TypeData::Intersection(_)
        ));
        assert!(context.diagnostics().is_empty());
        assert!(context.store().type_node_links(unused).is_none());

        let property_types =
            properties.map(|property| context.get_type_from_type_node(property).unwrap());
        context.check_source_file(FILE).unwrap();
        assert_eq!(variable_type(&parsed, &context, "options"), options);
        for (name, expected) in ["readMode", "readStyle", "readGrouping"]
            .into_iter()
            .zip(property_types)
        {
            assert_eq!(variable_type(&parsed, &context, name), expected);
        }
        assert_union(
            &mut context,
            property_types[0],
            &["\"best fit\"", "\"lookup\"", "undefined"],
        );
        assert_union(
            &mut context,
            property_types[1],
            &["\"decimal\"", "\"percent\""],
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(property_types[2], bootstrap.boolean_type);
        assert_eq!(
            variable_type(&parsed, &context, "readMarker"),
            bootstrap.number_type
        );
        assert!(context.store().type_node_links(unused).is_none());

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["boolean", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'boolean' is not assignable to type 'number'."
        );
        let invalid = declaration(&parsed, "invalid");
        let NodeData::VariableDeclaration(invalid) = &parsed.arena.get(invalid.node).unwrap().data
        else {
            panic!("invalid must be the written variable declaration")
        };
        assert_eq!(diagnostic.node, Some(node(&parsed, invalid.name)));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());

        let warm = snapshot(&parsed, &context);
        for _ in 0..2 {
            assert_eq!(context.get_type_from_type_node(options_node), Ok(options));
            for (property, expected) in properties.into_iter().zip(property_types) {
                assert_eq!(context.get_type_from_type_node(property), Ok(expected));
            }
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(snapshot(&parsed, &context), warm);
        }
    }
}
