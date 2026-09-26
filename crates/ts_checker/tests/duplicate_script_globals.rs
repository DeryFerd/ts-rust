use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    CanonicalCheckerRelatedInformation, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::StructuredTypeData,
    types::ObjectFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(99_171);
const CORE_FILE: FileId = FileId::new(99_172);
const SOURCE_FILE: FileId = FileId::new(99_173);
const FIRST_FILE: FileId = FileId::new(99_174);
const SECOND_FILE: FileId = FileId::new(99_175);
const THIRD_FILE: FileId = FileId::new(99_176);

#[derive(Clone, Copy)]
struct Declaration {
    node: NodeRef,
    name: NodeRef,
}

fn context<'a>(files: &[(FileId, &'a ParseResult, bool, &str)]) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, declaration, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    declaration,
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
        files
            .iter()
            .map(|(file, parsed, _, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, file: FileId, expected: &str) -> Declaration {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::EnumDeclaration(enumeration) => enumeration.name,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(Declaration {
                node: NodeRef::new(parsed.arena.id(), file, node),
                name: NodeRef::new(parsed.arena.id(), file, name),
            })
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn alias_body(parsed: &ParseResult, declaration: Declaration) -> NodeRef {
    let NodeData::TypeAliasDeclaration(alias) =
        &parsed.arena.get(declaration.node.node).unwrap().data
    else {
        panic!("expected a type alias");
    };
    NodeRef::new(parsed.arena.id(), declaration.node.file, alias.type_)
}

fn bound_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn global_symbol(checker: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    checker
        .store()
        .symbol_table(checker.globals())
        .unwrap()
        .get_source(name)
        .unwrap()
}

fn assert_name(
    checker: &CanonicalCheckerContext<'_>,
    node: NodeRef,
    written: &str,
    range: (u32, u32),
) {
    let (arena, _) = checker.file(node.file).unwrap();
    assert_eq!(arena.id(), node.arena);
    let record = arena.get(node.node).unwrap();
    assert!(matches!(record.data, NodeData::Identifier(_)));
    assert_eq!((record.range.start.get(), record.range.end.get()), range);
    let start = usize::try_from(range.0).unwrap();
    let end = usize::try_from(range.1).unwrap();
    assert_eq!(arena.source_text().unwrap().get(start..end), Some(written));
}

fn duplicate_diagnostic(
    node: NodeRef,
    related: NodeRef,
    code: u32,
    written: &str,
) -> CanonicalCheckerDiagnostic {
    CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(message_by_code(code).unwrap(), [written]),
        related_information: vec![CanonicalCheckerRelatedInformation {
            node: Some(related),
            diagnostic: Diagnostic::with_arguments(message_by_code(6203).unwrap(), [written]),
        }],
    }
}

fn assert_kept_duplicate(
    checker: &CanonicalCheckerContext<'_>,
    name: &str,
    first: Declaration,
    later: Declaration,
) {
    let first_symbol = bound_symbol(checker, first.node);
    let later_symbol = bound_symbol(checker, later.node);
    assert_ne!(first_symbol, later_symbol);
    assert_eq!(global_symbol(checker, name), first_symbol);
    for (declaration, symbol) in [(first, first_symbol), (later, later_symbol)] {
        assert_eq!(checker.store().get_merged_symbol(symbol), Some(symbol));
        let record = checker.store().symbol(symbol).unwrap();
        assert_eq!(record.name(), EscapedName::source(name).as_ref());
        assert_eq!(record.declarations(), Some([declaration.node].as_slice()));
    }
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.symbol_store().symbol_table_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
    ]
}

fn keys_parameter(core: &ParseResult) -> NodeRef {
    core.arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &core.arena.get(method.name)?.data else {
                return None;
            };
            let NodeData::InterfaceDeclaration(interface) =
                &core.arena.get(record.parent?)?.data
            else {
                return None;
            };
            let NodeData::Identifier(owner) = &core.arena.get(interface.name)?.data else {
                return None;
            };
            if owner.text != "ObjectConstructor" || name.text != "keys" {
                return None;
            }
            assert_eq!(method.parameters.nodes.len(), 1);
            let NodeData::ParameterDeclaration(parameter) =
                &core.arena.get(method.parameters.nodes[0]).unwrap().data
            else {
                panic!("Object.keys must retain its written parameter");
            };
            Some(NodeRef::new(
                core.arena.id(),
                CORE_FILE,
                parameter.type_.unwrap(),
            ))
        })
        .expect("missing ObjectConstructor.keys")
}

fn object_members<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the source object's canonical type");
    };
    &object.structured
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original query order and its replay in one control.
fn duplicate_library_alias_reports_both_names_and_keeps_direct_queries() {
    let es5 = parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts"));
    let core = parse_source_file(include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts"));
    let source = parse_source_file(concat!(
        "type Required = { id: number };\n",
        "type Callable = () => number;\n",
        "type Indexed = { [key: string]: number };\n",
        "const fresh = {};\n",
    ));
    let mut checker = context(&[
        (ES5_FILE, &es5, true, "\"/lib/lib.es5.d.ts\""),
        (CORE_FILE, &core, true, "\"/lib/lib.es2015.core.d.ts\""),
        (SOURCE_FILE, &source, false, "\"/cold-wrapper-relations.ts\""),
    ]);
    assert_eq!(checker.file_order(), [ES5_FILE, CORE_FILE, SOURCE_FILE]);
    let library_alias = declaration(&es5, ES5_FILE, "Required");
    let aliases = ["Required", "Callable", "Indexed"]
        .map(|name| declaration(&source, SOURCE_FILE, name));
    let bodies = aliases.map(|alias| alias_body(&source, alias));
    assert_name(&checker, aliases[0].name, "Required", (5, 13));
    assert_name(&checker, library_alias.name, "Required", (73_870, 73_878));
    assert_eq!(
        checker.diagnostics().as_slice(),
        [
            duplicate_diagnostic(aliases[0].name, library_alias.name, 2300, "Required"),
            duplicate_diagnostic(library_alias.name, aliases[0].name, 2300, "Required"),
        ],
    );
    assert_kept_duplicate(&checker, "Required", library_alias, aliases[0]);
    let symbols = aliases.map(|alias| bound_symbol(&checker, alias.node));
    let library_symbol = bound_symbol(&checker, library_alias.node);
    for symbol in [library_symbol, symbols[0]] {
        assert_eq!(
            checker.store().symbol(symbol).unwrap().flags(),
            SymbolFlags::TYPE_ALIAS,
        );
        assert!(checker.store().type_alias_links(symbol).is_none());
    }

    // This is the original query order. Reporting must not prepare these types.
    let parameter = keys_parameter(&core);
    let target = checker.get_type_from_type_node(parameter).unwrap();
    let [required, callable, indexed] =
        bodies.map(|body| checker.get_type_from_type_node(body).unwrap());
    let fresh_declaration = declaration(&source, SOURCE_FILE, "fresh");
    let NodeData::VariableDeclaration(variable) =
        &source.arena.get(fresh_declaration.node.node).unwrap().data
    else {
        unreachable!()
    };
    let fresh_node = NodeRef::new(
        source.arena.id(),
        SOURCE_FILE,
        variable.initializer.unwrap(),
    );
    assert!(matches!(
        source.arena.get(fresh_node.node).unwrap().data,
        NodeData::ObjectLiteralExpression(_)
    ));
    let fresh = checker.get_type_at_location(fresh_node).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    assert_eq!(target, bootstrap.empty_type_literal_type);
    assert_ne!(target, bootstrap.empty_object_type);
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let types = [required, callable, indexed];
    for ((symbol, body), type_) in symbols.into_iter().zip(bodies).zip(types) {
        assert_eq!(checker.get_declared_type_of_symbol(symbol).unwrap(), type_);
        let record = checker.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(bound_symbol(&checker, body)));
        assert_eq!(
            checker
                .store()
                .type_alias(record.alias().unwrap())
                .unwrap()
                .symbol(),
            Some(symbol),
        );
    }
    let id = bound_symbol(&checker, declaration(&source, SOURCE_FILE, "id").node);
    let required_members = object_members(&checker, required);
    assert_eq!(required_members.properties.as_deref(), Some([id].as_slice()));
    let members = checker
        .store()
        .symbol_table(required_members.members.unwrap())
        .unwrap();
    assert_eq!(members.len(), 1);
    assert_eq!(members.get_source("id"), Some(id));
    assert_eq!(
        checker.store().value_symbol_links(id).unwrap().resolved_type,
        Some(number),
    );
    let callable_members = object_members(&checker, callable);
    assert_eq!(callable_members.call_signature_count, 1);
    let [signature] = callable_members.signatures.as_deref().unwrap() else {
        panic!("Callable must retain its one source signature");
    };
    let signature = checker.store().signature(*signature).unwrap();
    assert_eq!(signature.declaration(), Some(bodies[1]));
    assert!(signature.parameters().is_empty());
    assert_eq!(signature.resolved_return_type(), None);
    let [index] = object_members(&checker, indexed)
        .index_infos
        .as_deref()
        .unwrap()
    else {
        panic!("Indexed must retain its one source index signature");
    };
    let index = checker.store().index_info(*index).unwrap();
    assert_eq!(index.key_type(), string);
    assert_eq!(index.value_type(), number);
    let index_node = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (matches!(record.data, NodeData::IndexSignatureDeclaration(_))
                && record.parent == Some(bodies[2].node))
            .then_some(NodeRef::new(source.arena.id(), SOURCE_FILE, node))
        })
        .unwrap();
    assert_eq!(index.declaration(), Some(index_node));
    assert!(
        checker
            .store()
            .type_payload(fresh)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::FRESH_LITERAL)
    );
    assert_eq!(
        checker
            .store()
            .type_payload(checker.global_types().number_type)
            .unwrap()
            .object_flags(),
        ObjectFlags::INTERFACE,
    );
    assert!(checker.store().type_alias_links(library_symbol).is_none());

    let diagnostics = checker.diagnostics().clone();
    let warm = counts(&checker);
    for _ in 0..2 {
        assert_eq!(checker.get_type_from_type_node(parameter).unwrap(), target);
        for (body, type_) in bodies.into_iter().zip(types) {
            assert_eq!(checker.get_type_from_type_node(body).unwrap(), type_);
        }
        assert_eq!(checker.get_type_at_location(fresh_node).unwrap(), fresh);
        for (symbol, type_) in symbols.into_iter().zip(types) {
            assert_eq!(checker.get_declared_type_of_symbol(symbol).unwrap(), type_);
        }
        assert_kept_duplicate(&checker, "Required", library_alias, aliases[0]);
        assert!(checker.store().type_alias_links(library_symbol).is_none());
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(counts(&checker), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep collision order and later merging in one control.
fn duplicate_script_codes_and_order_follow_each_collision() {
    for (first_source, later_source, name, written, code, first_range, later_range) in [
        (
            "type Alias = string;\n",
            "type Ali\\u0061s = number;\n",
            "Alias",
            "Ali\\u0061s",
            2300,
            (5, 10),
            (5, 15),
        ),
        (
            "var Block: number;\n",
            "let Bl\\u006fck: number;\n",
            "Block",
            "Bl\\u006fck",
            2451,
            (4, 9),
            (4, 14),
        ),
        (
            "enum Kind { First }\n",
            "let K\\u0069nd: number;\n",
            "Kind",
            "K\\u0069nd",
            2567,
            (5, 9),
            (4, 13),
        ),
        (
            "let Kind: number;\n",
            "enum K\\u0069nd { First }\n",
            "Kind",
            "K\\u0069nd",
            2567,
            (4, 8),
            (5, 14),
        ),
    ] {
        let first = parse_source_file(first_source);
        let later = parse_source_file(later_source);
        let checker = context(&[
            (FIRST_FILE, &first, false, "\"/first.ts\""),
            (SECOND_FILE, &later, false, "\"/second.ts\""),
        ]);
        let first = declaration(&first, FIRST_FILE, name);
        let later = declaration(&later, SECOND_FILE, name);
        assert_name(&checker, first.name, name, first_range);
        assert_name(&checker, later.name, written, later_range);
        assert_eq!(
            checker.diagnostics().as_slice(),
            [
                duplicate_diagnostic(later.name, first.name, code, written),
                duplicate_diagnostic(first.name, later.name, code, written),
            ],
        );
        for diagnostic in checker.diagnostics().as_slice() {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.arguments, [written]);
            if code == 2567 {
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Enum declarations can only merge with namespace or other enum declarations.",
                );
            }
        }
        assert_kept_duplicate(&checker, name, first, later);
    }

    let first = parse_source_file(concat!(
        "type Repeated = string;\n",
        "interface ZShared { left: string; }\n",
    ));
    let second = parse_source_file("type Repeated = number;\n");
    let third = parse_source_file(concat!(
        "type Repeated = boolean;\n",
        "interface ZShared { right: number; }\n",
    ));
    let mut checker = context(&[
        (FIRST_FILE, &first, false, "\"/first.ts\""),
        (SECOND_FILE, &second, false, "\"/second.ts\""),
        (THIRD_FILE, &third, false, "\"/third.ts\""),
    ]);
    assert_eq!(checker.file_order(), [FIRST_FILE, SECOND_FILE, THIRD_FILE]);
    let parsed = [
        (&first, FIRST_FILE),
        (&second, SECOND_FILE),
        (&third, THIRD_FILE),
    ];
    let aliases = parsed.map(|(source, file)| declaration(source, file, "Repeated"));
    for alias in aliases {
        assert_name(&checker, alias.name, "Repeated", (5, 13));
    }
    assert_eq!(
        checker.diagnostics().as_slice(),
        [
            duplicate_diagnostic(aliases[1].name, aliases[0].name, 2300, "Repeated"),
            duplicate_diagnostic(aliases[0].name, aliases[1].name, 2300, "Repeated"),
            duplicate_diagnostic(aliases[2].name, aliases[0].name, 2300, "Repeated"),
            duplicate_diagnostic(aliases[0].name, aliases[2].name, 2300, "Repeated"),
        ],
    );
    for later in &aliases[1..] {
        assert_kept_duplicate(&checker, "Repeated", aliases[0], *later);
    }
    // ZShared sorts after Repeated, so its merge follows the last collision.
    let interfaces = [
        declaration(&first, FIRST_FILE, "ZShared"),
        declaration(&third, THIRD_FILE, "ZShared"),
    ];
    let merged = global_symbol(&checker, "ZShared");
    for interface in interfaces {
        let raw = bound_symbol(&checker, interface.node);
        assert_ne!(raw, merged);
        assert_eq!(checker.store().get_merged_symbol(raw), Some(merged));
    }
    let record = checker.store().symbol(merged).unwrap();
    assert!(
        record
            .flags()
            .contains(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
    );
    let merged_declarations = interfaces.map(|interface| interface.node);
    assert_eq!(record.declarations(), Some(merged_declarations.as_slice()));
    let merged_members = record.members().unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let types = [
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.boolean_type,
    ];
    let bodies = parsed
        .map(|(source, file)| alias_body(source, declaration(source, file, "Repeated")));
    let symbols = aliases.map(|alias| bound_symbol(&checker, alias.node));
    for ((body, symbol), type_) in bodies.into_iter().zip(symbols).zip(types) {
        assert_eq!(checker.get_type_from_type_node(body).unwrap(), type_);
        assert_eq!(checker.get_declared_type_of_symbol(symbol).unwrap(), type_);
    }
    let merged_type = checker.get_declared_type_of_symbol(merged).unwrap();
    let record = checker.store().type_payload(merged_type).unwrap();
    assert_eq!(record.symbol(), Some(merged));
    let TypeData::Interface(interface) = record.data() else {
        panic!("the later compatible merge must retain its interface type");
    };
    assert!(!interface.declared_members_resolved);
    assert_eq!(checker.store().symbol_table(merged_members).unwrap().len(), 2);
    let properties = [
        ("left", &first, FIRST_FILE, types[0]),
        ("right", &third, THIRD_FILE, types[1]),
    ]
    .map(|(name, source, file, type_)| {
        let declaration = declaration(source, file, name);
        let symbol = bound_symbol(&checker, declaration.node);
        assert_eq!(
            checker
                .store()
                .symbol_table(merged_members)
                .unwrap()
                .get_source(name),
            Some(symbol),
        );
        assert_eq!(checker.store().get_parent_of_symbol(symbol), Some(merged));
        (declaration, symbol, type_)
    });
    for (property, symbol, type_) in properties {
        assert_eq!(checker.get_type_at_location(property.name).unwrap(), type_);
        assert_eq!(
            checker.store().value_symbol_links(symbol).unwrap().resolved_type,
            Some(type_),
        );
    }
    let diagnostics = checker.diagnostics().clone();
    let warm = counts(&checker);
    for _ in 0..2 {
        for ((body, symbol), type_) in bodies.into_iter().zip(symbols).zip(types) {
            assert_eq!(checker.get_type_from_type_node(body).unwrap(), type_);
            assert_eq!(checker.get_declared_type_of_symbol(symbol).unwrap(), type_);
        }
        assert_eq!(
            checker.get_declared_type_of_symbol(merged).unwrap(),
            merged_type,
        );
        for (property, _, type_) in properties {
            assert_eq!(checker.get_type_at_location(property.name).unwrap(), type_);
        }
        assert_eq!(global_symbol(&checker, "ZShared"), merged);
        assert_eq!(
            checker.store().symbol(merged).unwrap().declarations(),
            Some(merged_declarations.as_slice()),
        );
        for later in &aliases[1..] {
            assert_kept_duplicate(&checker, "Repeated", aliases[0], *later);
        }
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(counts(&checker), warm);
    }
}
