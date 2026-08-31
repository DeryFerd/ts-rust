use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, TypeData, TypeId,
    type_records::InterfaceTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(470_100);
const PROVIDER: FileId = FileId::new(470_101);
const OTHER: FileId = FileId::new(470_102);

fn context<'a>(
    source: &'a ParseResult,
    provider: &'a ParseResult,
    other: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (SOURCE, source, "\"/project/source.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
        (OTHER, other, "\"/project/other.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let (specifier, _) = import_nodes(source);
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn import_nodes(parsed: &ParseResult) -> (NodeRef, NodeRef) {
    let mut imports = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::ImportDeclaration(import) = &record.data else {
            return None;
        };
        let NodeData::ImportClause(clause) = &parsed
            .arena
            .get(import.import_clause.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected import clause")
        };
        let NodeData::NamedImports(named) = &parsed
            .arena
            .get(clause.named_bindings.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected named import")
        };
        let [binding] = named.elements.nodes.as_slice() else {
            panic!("expected one binding")
        };
        Some((
            NodeRef::new(parsed.arena.id(), SOURCE, import.module_specifier),
            NodeRef::new(parsed.arena.id(), SOURCE, *binding),
        ))
    });
    let result = imports.next().unwrap();
    assert!(imports.next().is_none());
    result
}

fn interface(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn assert_heritage(parsed: &ParseResult, owner: NodeRef, expected: &str, argument: Option<&str>) {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("expected derived interface")
    };
    let [clause] = interface
        .heritage_clauses
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("expected one heritage clause")
    };
    let clause_record = parsed.arena.get(*clause).unwrap();
    assert_eq!(clause_record.parent, Some(owner.node));
    let NodeData::HeritageClause(clause_data) = &clause_record.data else {
        panic!("expected heritage clause")
    };
    let [base] = clause_data.types.nodes.as_slice() else {
        panic!("expected one written base")
    };
    let base_record = parsed.arena.get(*base).unwrap();
    assert_eq!(base_record.parent, Some(*clause));
    assert!(base_record.range.start >= clause_record.range.start);
    assert!(base_record.range.end <= clause_record.range.end);
    let NodeData::ExpressionWithTypeArguments(base_data) = &base_record.data else {
        panic!("heritage must retain its real expression owner")
    };
    assert_eq!(
        text(parsed, NodeRef::new(owner.arena, owner.file, *base)),
        expected
    );
    assert_eq!(
        parsed.arena.get(base_data.expression).unwrap().parent,
        Some(*base)
    );
    match (argument, &base_data.type_arguments) {
        (None, None) => {}
        (Some(expected), Some(arguments)) => {
            let [argument] = arguments.nodes.as_slice() else {
                panic!("expected one argument")
            };
            assert_eq!(parsed.arena.get(*argument).unwrap().parent, Some(*base));
            assert_eq!(
                text(parsed, NodeRef::new(owner.arena, owner.file, *argument)),
                expected
            );
        }
        _ => panic!("written type argument presence changed"),
    }
}

fn declared(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap()
}

fn interface_data<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected interface payload")
    };
    data
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn text(parsed: &ParseResult, node: NodeRef) -> &str {
    assert_eq!(node.arena, parsed.arena.id());
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()
        [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_import_owner(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: NodeRef,
) {
    let imported = symbol(context, import_nodes(source).1);
    let owner = symbol(context, provider);
    assert_ne!(imported, owner);
    assert_eq!(
        context
            .store()
            .alias_symbol_links(imported)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(owner),
    );
    assert!(context.store().value_symbol_links(imported).is_none());
    assert_eq!(
        context
            .store()
            .type_payload(declared(context, owner))
            .unwrap()
            .symbol(),
        Some(owner),
    );
}

fn assert_read(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    expected_text: &str,
    expected_type: TypeId,
) {
    let node = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::PropertyAccessExpression(_))
                .then_some(NodeRef::new(source.arena.id(), SOURCE, node))
                .filter(|node| text(source, *node) == expected_text)
        })
        .unwrap();
    assert_eq!(
        context.store().type_node_links(node).unwrap().resolved_type,
        Some(expected_type),
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

fn assert_warm(context: &mut CanonicalCheckerContext<'_>) {
    let before = snapshot(context);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

#[test]
fn renamed_imported_base_keeps_provider_identity_and_inherited_diagnostics() {
    let source = parse_source_file(concat!(
        "import type { Base as ImportedBase } from './provider';\n",
        "interface Derived extends ImportedBase { label: string }\n",
        "const ok: Derived = { id: 1, label: 'x' };\n",
        "const bad: Derived = { label: 'x' };\n",
        "function read(value: Derived): number { return value.id; }\n",
    ));
    let provider = parse_source_file("export interface Base { id: number }");
    let other = parse_source_file("export interface Base { id: string }");
    for (provider_first, query_first) in [(false, false), (false, true), (true, false)] {
        let mut context = context(&source, &provider, &other);
        let base_node = interface(&provider, PROVIDER, "Base");
        let base_owner = symbol(&context, base_node);
        let other_owner = symbol(&context, interface(&other, OTHER, "Base"));
        let derived_node = interface(&source, SOURCE, "Derived");
        assert_heritage(&source, derived_node, "ImportedBase", None);
        let derived_owner = symbol(&context, derived_node);
        assert_ne!(base_owner, other_owner);
        assert!(
            context
                .store()
                .alias_symbol_links(symbol(&context, import_nodes(&source).1))
                .is_none()
        );
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        let queried =
            query_first.then(|| context.get_declared_type_of_symbol(derived_owner).unwrap());
        assert!(!checked(&context, SOURCE));
        context.check_source_file(SOURCE).unwrap();
        assert!(checked(&context, SOURCE));
        assert_eq!(checked(&context, PROVIDER), provider_first);
        assert!(!checked(&context, OTHER));
        assert_import_owner(&context, &source, base_node);
        assert!(context.store().declared_type_links(other_owner).is_none());
        assert_missing_inherited_property(&context, &source, &provider);

        let base = declared(&context, base_owner);
        let derived = declared(&context, derived_owner);
        if let Some(queried) = queried {
            assert_eq!(queried, derived);
        }
        let data = interface_data(&context, derived);
        assert!(data.base_types_resolved);
        assert_eq!(data.resolved_base_types.as_deref(), Some([base].as_slice()));
        let own = context
            .store()
            .symbol_table(data.declared_members.unwrap())
            .unwrap();
        assert_eq!(own.len(), 1);
        let label = own.get_source("label").unwrap();
        let base_members = interface_data(&context, base).declared_members.unwrap();
        let id = context
            .store()
            .symbol_table(base_members)
            .unwrap()
            .get_source("id")
            .unwrap();
        assert_eq!(
            data.reference.object.structured.properties.as_deref(),
            Some([label, id].as_slice()),
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_read(&context, &source, "value.id", number);
        assert_eq!(context.is_type_assignable_to(derived, base), Ok(true));
        assert_eq!(context.is_type_assignable_to(base, derived), Ok(false));
        assert_warm(&mut context);
        assert_import_owner(&context, &source, base_node);
    }
}

fn assert_missing_inherited_property(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected exactly one inherited-property diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2741);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["id", "{ label: string; }", "Derived"]
    );
    let anchor = diagnostic.node.unwrap();
    assert_eq!(anchor.file, SOURCE);
    assert_eq!(text(source, anchor), "bad");
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("expected the actual inherited declaration");
    };
    assert_eq!(related.diagnostic.code(), 2728);
    assert_eq!(related.diagnostic.arguments, ["id"]);
    let anchor = related.node.unwrap();
    assert_eq!(anchor.file, PROVIDER);
    assert_eq!(text(provider, anchor), "id");
}

#[test]
fn imported_generic_base_keeps_its_omitted_unknown_default() {
    let source = parse_source_file(concat!(
        "import type { Base } from './provider';\n",
        "interface Defaulted extends Base { own: number }\n",
        "interface Explicit extends Base<string> { own: number }\n",
        "function read(unknownValue: Defaulted): unknown { return unknownValue.value; }\n",
        "function exact(stringValue: Explicit): string { return stringValue.value; }\n",
    ));
    let provider = parse_source_file("export interface Base<T = unknown> { value: T }");
    let other = parse_source_file("export interface Base<T = number> { value: T }");
    for (provider_first, query_first) in [(false, false), (false, true), (true, false)] {
        let mut context = context(&source, &provider, &other);
        let defaulted = interface(&source, SOURCE, "Defaulted");
        let explicit = interface(&source, SOURCE, "Explicit");
        assert_heritage(&source, defaulted, "Base", None);
        assert_heritage(&source, explicit, "Base<string>", Some("string"));
        let defaulted_owner = symbol(&context, defaulted);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        let queried = query_first.then(|| {
            context
                .get_declared_type_of_symbol(defaulted_owner)
                .unwrap()
        });
        assert!(!checked(&context, SOURCE));
        context.check_source_file(SOURCE).unwrap();
        if let Some(queried) = queried {
            assert_eq!(queried, declared(&context, defaulted_owner));
        }
        assert!(context.diagnostics().is_empty());
        let base_node = interface(&provider, PROVIDER, "Base");
        assert_import_owner(&context, &source, base_node);
        assert_eq!(checked(&context, PROVIDER), provider_first);
        assert!(!checked(&context, OTHER));
        assert!(
            context
                .store()
                .declared_type_links(symbol(&context, interface(&other, OTHER, "Base")))
                .is_none()
        );
        assert_default_owner(&context, &provider, base_node);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (unknown, string) = (bootstrap.unknown_type, bootstrap.string_type);
        let target = declared(&context, symbol(&context, base_node));
        for (name, argument) in [("Defaulted", unknown), ("Explicit", string)] {
            let derived = declared(&context, symbol(&context, interface(&source, SOURCE, name)));
            let [base] = interface_data(&context, derived)
                .resolved_base_types
                .as_deref()
                .unwrap()
            else {
                panic!("expected one imported generic base")
            };
            let TypeData::TypeReference(reference) =
                context.store().type_payload(*base).unwrap().data()
            else {
                panic!("expected actual instantiated base reference")
            };
            assert_eq!(reference.object.target, Some(target));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some([argument].as_slice())
            );
        }
        assert_read(&context, &source, "unknownValue.value", unknown);
        assert_read(&context, &source, "stringValue.value", string);
        assert_warm(&mut context);
        assert_default_owner(&context, &provider, base_node);
    }
}

fn assert_default_owner(
    context: &CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    base: NodeRef,
) {
    let NodeData::InterfaceDeclaration(declaration) = &provider.arena.get(base.node).unwrap().data
    else {
        panic!("expected provider interface")
    };
    let [parameter] = declaration
        .type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("expected one written formal")
    };
    let formal_node = NodeRef::new(base.arena, base.file, *parameter);
    let NodeData::TypeParameterDeclaration(parameter) =
        &provider.arena.get(*parameter).unwrap().data
    else {
        panic!("expected written type parameter")
    };
    let default = NodeRef::new(base.arena, base.file, parameter.default_type.unwrap());
    assert_eq!(text(provider, default), "unknown");
    assert_eq!(
        provider.arena.get(default.node).unwrap().parent,
        Some(formal_node.node)
    );
    let formal_owner = symbol(context, formal_node);
    let formal = declared(context, formal_owner);
    assert_eq!(
        context.store().type_payload(formal).unwrap().symbol(),
        Some(formal_owner)
    );
    let TypeData::TypeParameter(data) = context.store().type_payload(formal).unwrap().data() else {
        panic!("expected original formal type")
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert_eq!(
        data.resolved_default_type,
        Some(context.store().intrinsic_bootstrap().unwrap().unknown_type),
    );
}

#[test]
fn a_missing_export_does_not_use_the_same_name_from_another_module() {
    let source = parse_source_file(concat!(
        "import type { Base } from './provider';\n",
        "interface Derived extends Base { own: number }\n",
    ));
    let provider = parse_source_file("export interface Other { id: number }");
    let other = parse_source_file("export interface Base { id: number }");
    let mut context = context(&source, &provider, &other);
    let imported = symbol(&context, import_nodes(&source).1);
    let derived = symbol(&context, interface(&source, SOURCE, "Derived"));
    let decoy = symbol(&context, interface(&other, OTHER, "Base"));
    let before = snapshot(&context);
    let error = context
        .check_source_file(SOURCE)
        .expect_err("the selected module has no Base export");
    assert_eq!(snapshot(&context), before);
    assert!(context.store().alias_symbol_links(imported).is_none());
    assert!(context.store().declared_type_links(derived).is_none());
    assert!(context.store().declared_type_links(decoy).is_none());
    for _ in 0..2 {
        assert_eq!(context.check_source_file(SOURCE), Err(error));
        assert_eq!(snapshot(&context), before);
        assert!(!checked(&context, SOURCE));
        assert!(!checked(&context, PROVIDER));
        assert!(!checked(&context, OTHER));
    }
}
