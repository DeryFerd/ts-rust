use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_910);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/mutable-object-rest.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
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
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, id: NodeId, expected: &str) -> bool {
    matches!(&parsed.arena.get(id).unwrap().data, NodeData::Identifier(name) if name.text == expected)
}

fn binding(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::BindingElement(element) = &record.data else {
                return None;
            };
            let local = element.name?;
            named(parsed, local, name).then_some((node(parsed, id), node(parsed, local)))
        })
        .unwrap_or_else(|| panic!("missing binding {name}"))
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            named(parsed, variable.name, name).then(|| node(parsed, variable.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing initializer for {name}"))
}

fn assignment(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            (parsed.arena.get(binary.operator_token)?.kind == SyntaxKind::EqualsToken
                && named(parsed, binary.left, name))
            .then_some((node(parsed, binary.left), node(parsed, binary.right)))
        })
        .unwrap_or_else(|| panic!("missing assignment to {name}"))
}

fn alias_type(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> TypeId {
    let location = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            named(parsed, alias.name, name).then_some(node(parsed, alias.type_))
        })
        .unwrap_or_else(|| panic!("missing alias {name}"));
    checker.get_type_at_location(location).unwrap()
}

fn assert_binding(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> (SemanticSymbolId, TypeId) {
    let (element, local) = binding(parsed, name);
    let raw = checker.file(FILE).unwrap().1.symbol(element).unwrap();
    let symbol = checker.store().get_merged_symbol(raw).unwrap();
    assert_eq!(checker.get_symbol_at_location(local), Ok(Some(symbol)));
    let record = checker.store().symbol(symbol).unwrap();
    assert_eq!(record.declarations(), Some(&[element][..]));
    assert_eq!(record.value_declaration(), Some(element));
    let type_ = checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    (symbol, type_)
}

fn start<'a>(
    parsed: &'a ParseResult,
    first: NodeRef,
    query_first: bool,
) -> CanonicalCheckerContext<'a> {
    let mut checker = context(parsed);
    let queried = query_first.then(|| checker.get_type_at_location(first).unwrap());
    checker.check_source_file(FILE).unwrap();
    if let Some(type_) = queried {
        assert_eq!(checker.get_type_at_location(first), Ok(type_));
    }
    checker
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, id);
                (
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    reads: &[(NodeRef, TypeId)],
) {
    for &(location, type_) in reads {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
    }
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(location, type_) in reads {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

#[test]
fn mutable_selected_binding_keeps_its_symbol_and_changes_flow_after_assignment() {
    for header in [
        "function run(props: Props, replacement: number): number",
        "const run = (props: Props, replacement: number): number =>",
    ] {
        let parsed = parse_source_file(&format!(
            "type Props = {{ onLoad: string | number; kept: number; [key: string]: string | number }};\n\
             {header} {{\n\
               let {{ onLoad, ...restProps }} = props;\n\
               const before = onLoad;\n\
               onLoad = replacement;\n\
               const after = onLoad;\n\
               return after;\n\
             }};"
        ));
        let before = initializer(&parsed, "before");
        let after = initializer(&parsed, "after");
        let target = assignment(&parsed, "onLoad").0;
        for query_first in [false, true] {
            let mut checker = start(&parsed, after, query_first);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let (symbol, declared) = assert_binding(&mut checker, &parsed, "onLoad");
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let TypeData::Union(union) = checker.store().type_payload(declared).unwrap().data()
            else {
                panic!("the selected binding keeps its declared union")
            };
            assert!(union.union.types.contains(&number));
            assert!(
                union
                    .union
                    .types
                    .contains(&checker.store().intrinsic_bootstrap().unwrap().string_type)
            );
            for location in [before, target, after] {
                assert_eq!(checker.get_symbol_at_location(location), Ok(Some(symbol)));
                assert!(checker.file(FILE).unwrap().1.flow_at(location).is_some());
            }
            replay(
                &mut checker,
                &parsed,
                &[(before, declared), (after, number)],
            );
            assert_eq!(
                assert_binding(&mut checker, &parsed, "onLoad"),
                (symbol, declared)
            );
        }
    }
}

#[test]
fn index_only_props_supply_the_selected_binding_and_the_rest_index() {
    let parsed = parse_source_file(concat!(
        "type Props = { [key: string]: number };\n",
        "const run = (props: Props, key: string): number => {\n",
        "  let { onLoad, ...restProps } = props;\n",
        "  const selected = onLoad;\n",
        "  const indexed = restProps[key];\n",
        "  return indexed;\n",
        "};\n",
    ));
    let selected = initializer(&parsed, "selected");
    let indexed = initializer(&parsed, "indexed");
    for query_first in [false, true] {
        let mut checker = start(&parsed, indexed, query_first);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let props = alias_type(&mut checker, &parsed, "Props");
        let (selected_symbol, selected_type) = assert_binding(&mut checker, &parsed, "onLoad");
        let (rest_symbol, rest) = assert_binding(&mut checker, &parsed, "restProps");
        assert_ne!(selected_symbol, rest_symbol);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        assert_eq!(selected_type, number);
        assert_ne!(rest, bootstrap.empty_object_type);
        let TypeData::Object(source) = checker.store().type_payload(props).unwrap().data() else {
            panic!("Props is a real source object")
        };
        let TypeData::Object(rest_object) = checker.store().type_payload(rest).unwrap().data()
        else {
            panic!("rest keeps an object type even without named properties")
        };
        assert_eq!(
            rest_object.structured.index_infos,
            source.structured.index_infos
        );
        assert!(
            rest_object
                .structured
                .properties
                .as_ref()
                .unwrap()
                .is_empty()
        );
        let [index] = source.structured.index_infos.as_deref().unwrap() else {
            panic!("Props has one source index signature")
        };
        let info = checker.store().index_info(*index).unwrap();
        assert_eq!(info.key_type(), bootstrap.string_type);
        assert_eq!(info.value_type(), number);
        assert!(!info.is_readonly());
        let index_declaration = info.declaration().unwrap();
        assert_eq!(index_declaration.file, FILE);
        assert_eq!(
            parsed.arena.get(index_declaration.node).unwrap().kind,
            SyntaxKind::IndexSignature
        );
        replay(
            &mut checker,
            &parsed,
            &[(selected, number), (indexed, number)],
        );
        assert_eq!(
            assert_binding(&mut checker, &parsed, "restProps"),
            (rest_symbol, rest)
        );
    }
}

#[test]
fn mutable_rest_accepts_a_compatible_object_without_restoring_excluded_members() {
    let parsed = parse_source_file(concat!(
        "type Props = { onLoad: number; kept: number; [key: string]: number };\n",
        "function run(props: Props, replacement: Props, key: string): number {\n",
        "  let { onLoad, ...restProps } = props;\n",
        "  const before = restProps;\n",
        "  restProps = replacement;\n",
        "  const after = restProps;\n",
        "  const indexed = restProps[key];\n",
        "  return indexed;\n",
        "}\n",
    ));
    let before = initializer(&parsed, "before");
    let after = initializer(&parsed, "after");
    let indexed = initializer(&parsed, "indexed");
    for query_first in [false, true] {
        let mut checker = start(&parsed, after, query_first);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let props = alias_type(&mut checker, &parsed, "Props");
        let (symbol, rest) = assert_binding(&mut checker, &parsed, "restProps");
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let TypeData::Object(source) = checker.store().type_payload(props).unwrap().data() else {
            panic!("Props is a source object")
        };
        let TypeData::Object(rest_object) = checker.store().type_payload(rest).unwrap().data()
        else {
            panic!("rest has its own object type")
        };
        assert_eq!(
            rest_object.structured.index_infos,
            source.structured.index_infos
        );
        let members = checker
            .store()
            .symbol_table(rest_object.structured.members.unwrap())
            .unwrap();
        assert_eq!(members.get_source("onLoad"), None);
        let kept = members.get_source("kept").unwrap();
        assert_eq!(
            checker
                .store()
                .value_symbol_links(kept)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        let source_members = checker
            .store()
            .symbol_table(source.structured.members.unwrap())
            .unwrap();
        assert_ne!(Some(kept), source_members.get_source("kept"));
        for location in [before, assignment(&parsed, "restProps").0, after] {
            assert_eq!(checker.get_symbol_at_location(location), Ok(Some(symbol)));
        }
        replay(
            &mut checker,
            &parsed,
            &[(before, rest), (after, rest), (indexed, number)],
        );
        assert_eq!(
            assert_binding(&mut checker, &parsed, "restProps"),
            (symbol, rest)
        );
    }
}

#[test]
fn invalid_selected_and_rest_assignments_keep_native_errors_and_declared_types() {
    let parsed = parse_source_file(concat!(
        "type Props = { onLoad: number; kept: number; [key: string]: number };\n",
        "type Replacement = { kept: number; [key: string]: string | number };\n",
        "function run(props: Props, replacement: Replacement, text: string): number {\n",
        "  let { onLoad, ...restProps } = props;\n",
        "  onLoad = text;\n",
        "  restProps = replacement;\n",
        "  const selected: number = onLoad;\n",
        "  const indexed: number = restProps['extra'];\n",
        "  return selected;\n",
        "}\n",
    ));
    let selected = initializer(&parsed, "selected");
    let indexed = initializer(&parsed, "indexed");
    let selected_target = assignment(&parsed, "onLoad").0;
    let (rest_target, replacement) = assignment(&parsed, "restProps");
    for query_first in [false, true] {
        let mut checker = start(&parsed, selected, query_first);
        let (selected_symbol, selected_type) = assert_binding(&mut checker, &parsed, "onLoad");
        let (rest_symbol, rest) = assert_binding(&mut checker, &parsed, "restProps");
        let replacement_type = checker.get_type_at_location(replacement).unwrap();
        let rest_arguments = [
            checker.type_to_string(replacement_type).unwrap(),
            checker.type_to_string(rest).unwrap(),
        ];
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for (diagnostic, target) in diagnostics.iter().zip([selected_target, rest_target]) {
            assert_eq!(diagnostic.node, Some(target));
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
        assert_eq!(diagnostics[0].diagnostic.arguments, ["string", "number"]);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(diagnostics[1].diagnostic.arguments, rest_arguments);
        assert_eq!(
            checker.get_symbol_at_location(selected_target),
            Ok(Some(selected_symbol))
        );
        assert_eq!(
            checker.get_symbol_at_location(rest_target),
            Ok(Some(rest_symbol))
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(selected_type, number);
        replay(
            &mut checker,
            &parsed,
            &[(selected, number), (indexed, number)],
        );
        assert_eq!(
            assert_binding(&mut checker, &parsed, "onLoad"),
            (selected_symbol, number)
        );
        assert_eq!(
            assert_binding(&mut checker, &parsed, "restProps"),
            (rest_symbol, rest)
        );
    }
}
