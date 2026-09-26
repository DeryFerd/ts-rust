use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(260_921);
const SOURCE: &str = concat!(
    "interface InitialPageParam<TPageParam = unknown> { initialPageParam: TPageParam }\n",
    "interface InfiniteQueryPageParamsOptions<\n",
    "  TQueryFnData = unknown,\n",
    "  TPageParam = number,\n",
    "> extends InitialPageParam<TPageParam> {}\n",
    "declare const defaults: InfiniteQueryPageParamsOptions;\n",
    "declare const explicit: InfiniteQueryPageParamsOptions<boolean, string>;\n",
    "const defaultValue: number = defaults.initialPageParam;\n",
    "const explicitValue: string = explicit.initialPageParam;\n",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/interface-heritage-trailing-comma.ts\""),
                CanonicalSourceLanguage::TypeScript,
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn interface(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn declared(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap()
}

fn formal_types(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
) -> Vec<TypeId> {
    let NodeData::InterfaceDeclaration(interface) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected an interface declaration")
    };
    interface
        .type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|node| {
            let node = NodeRef::new(parsed.arena.id(), FILE, *node);
            assert_eq!(
                parsed.arena.get(node.node).unwrap().parent,
                Some(declaration.node),
            );
            let owner = symbol(context, node);
            let type_ = declared(context, owner);
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(owner));
            let TypeData::TypeParameter(parameter) = record.data() else {
                panic!("the declaration must retain its own formal")
            };
            assert!(!parameter.is_this_type);
            assert_eq!(parameter.target, None);
            assert_eq!(parameter.mapper, None);
            type_
        })
        .collect()
}

fn annotation(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then(|| NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing annotation for {expected}"))
}

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    assert_eq!(node.arena, parsed.arena.id());
    assert_eq!(node.file, FILE);
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()
        [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_property_read(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
    type_: TypeId,
) {
    let read = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(&record.data, NodeData::PropertyAccessExpression(_))
                .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .find(|node| node_text(parsed, *node) == expected)
        .unwrap_or_else(|| panic!("missing property read {expected}"));
    assert_eq!(
        context.store().type_node_links(read).unwrap().resolved_type,
        Some(type_),
    );
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // One graph checks the caller formal, defaults, and replay.
fn owner_formal_trailing_comma_preserves_inherited_types() {
    let parsed = parse_source_file(SOURCE);
    let base_node = interface(&parsed, "InitialPageParam");
    let owner_node = interface(&parsed, "InfiniteQueryPageParamsOptions");
    let NodeData::InterfaceDeclaration(owner_source) =
        &parsed.arena.get(owner_node.node).unwrap().data
    else {
        panic!("expected the caller interface")
    };
    let source_parameters = owner_source.type_parameters.as_ref().unwrap();
    assert_eq!(source_parameters.nodes.len(), 2);
    assert!(source_parameters.has_trailing_comma);

    for query_first in [false, true] {
        let mut context = context(&parsed);
        let owner = symbol(&context, owner_node);
        let queried = query_first.then(|| context.get_declared_type_of_symbol(owner).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
        let owner_type = declared(&context, owner);
        if let Some(queried) = queried {
            assert_eq!(queried, owner_type);
        }
        let base_type = declared(&context, symbol(&context, base_node));
        let base_formals = formal_types(&parsed, &context, base_node);
        let owner_formals = formal_types(&parsed, &context, owner_node);
        let [base_formal] = base_formals.as_slice() else {
            panic!("the base has one formal")
        };
        let [data_formal, page_formal] = owner_formals.as_slice() else {
            panic!("the caller has two ordered formals")
        };
        assert_ne!(base_formal, data_formal);
        assert_ne!(base_formal, page_formal);
        assert_ne!(data_formal, page_formal);
        let TypeData::Interface(owner_data) =
            context.store().type_payload(owner_type).unwrap().data()
        else {
            panic!("the caller must retain its interface type")
        };
        assert!(owner_data.base_types_resolved);
        let [base_reference] = owner_data.resolved_base_types.as_deref().unwrap() else {
            panic!("expected one inherited base")
        };
        let TypeData::TypeReference(base_reference) =
            context.store().type_payload(*base_reference).unwrap().data()
        else {
            panic!("the base must retain its instantiated reference")
        };
        assert_eq!(base_reference.object.target, Some(base_type));
        assert_eq!(
            base_reference.resolved_type_arguments.as_deref(),
            Some([*page_formal].as_slice()),
        );

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (unknown, number, boolean, string) = (
            bootstrap.unknown_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
            bootstrap.string_type,
        );
        for (formal, default_type) in [(*data_formal, unknown), (*page_formal, number)] {
            let TypeData::TypeParameter(parameter) =
                context.store().type_payload(formal).unwrap().data()
            else {
                panic!("expected the caller's formal type")
            };
            assert_eq!(parameter.resolved_default_type, Some(default_type));
        }
        let mut references = Vec::new();
        for (name, arguments, value) in [
            ("defaults", [unknown, number], number),
            ("explicit", [boolean, string], string),
        ] {
            let node = annotation(&parsed, name);
            let type_ = context.get_type_from_type_node(node).unwrap();
            let TypeData::TypeReference(reference) =
                context.store().type_payload(type_).unwrap().data()
            else {
                panic!("expected the caller's instantiated reference")
            };
            assert_eq!(reference.object.target, Some(owner_type));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(arguments.as_slice()),
            );
            assert_property_read(&parsed, &context, &format!("{name}.initialPageParam"), value);
            references.push((node, type_));
        }
        assert_ne!(references[0].1, references[1].1);
        let before = snapshot(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(owner_type));
            for &(node, type_) in &references {
                assert_eq!(context.get_type_from_type_node(node), Ok(type_));
            }
            assert_eq!(snapshot(&context), before);
        }
    }
}

#[test]
fn owner_formal_trailing_comma_keeps_native_property_mismatch() {
    let parsed = parse_source_file(&format!(
        "{SOURCE}const bad: number = explicit.initialPageParam;\n"
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected only the incompatible inherited-property diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(node_text(&parsed, diagnostic.node.unwrap()), "bad");
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'.",
    );
    let before = snapshot(&context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&context), before);
    }
}
