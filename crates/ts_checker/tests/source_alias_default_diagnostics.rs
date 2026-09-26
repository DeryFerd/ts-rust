use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, TypeData, TypeId,
    type_records::LiteralValue,
};
use ts_parser::{ParseResult, parse_source_file};

const LOCAL: FileId = FileId::new(9_209);
const CONSUMER: FileId = FileId::new(9_210);
const PROVIDER: FileId = FileId::new(9_211);
const LOCAL_SOURCE: &str = concat!(
    "type Broken<T extends string = number> = T;\n",
    "type Valid<T extends string = 'ready'> = T;\n",
    "type Other<T extends number = string> = T;\n",
    "type Free<T = number> = T;\n",
);
const PROVIDER_SOURCE: &str = concat!(
    "export type Broken<T extends string = number> = T;\n",
    "export type Valid<T extends string = 'ready'> = T;\n",
    "export declare function readBroken(): Broken;\n",
    "export declare function readValid(): Valid;\n",
);
const CONSUMER_SOURCE: &str = concat!(
    "import { readBroken, readValid } from './provider';\n",
    "const used = readBroken();\n",
    "const good = readValid();\n",
);

#[derive(Clone, Copy)]
struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    constraint: Option<NodeRef>,
    default: Option<NodeRef>,
}

struct Alias {
    declaration: NodeRef,
    name: NodeRef,
    body: NodeRef,
    parameters: Vec<Parameter>,
}

#[derive(Clone, Copy)]
enum QueryOrder {
    Source,
    Alias,
    Default,
}

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str)],
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in files {
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
                    module_state,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = files.iter().flat_map(|&(file, parsed, _)| {
        parsed.arena.iter().filter_map(move |(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(parsed.arena.id(), file, import.module_specifier),
                CanonicalResolvedModuleInput::new(
                    PROVIDER,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ))
        })
    });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let parameters = alias
                .type_parameters
                .as_ref()
                .map_or(&[][..], |list| &list.nodes);
            Some(Alias {
                declaration: node_ref(node),
                name: node_ref(alias.name),
                body: node_ref(alias.type_),
                parameters: parameters
                    .iter()
                    .map(|&node| {
                        let NodeData::TypeParameterDeclaration(parameter) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected a source type parameter")
                        };
                        Parameter {
                            declaration: node_ref(node),
                            name: node_ref(parameter.name),
                            constraint: parameter.constraint.map(node_ref),
                            default: parameter.default_type.map(node_ref),
                        }
                    })
                    .collect(),
            })
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let symbol = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(symbol).unwrap()
}

fn query_alias(checker: &mut CanonicalCheckerContext<'_>, alias: &Alias) -> TypeId {
    let owner = symbol(checker, alias.declaration);
    let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        checker
            .store()
            .type_alias_links(owner)
            .unwrap()
            .declared_type,
        Some(type_)
    );
    type_
}

fn assert_checked(checker: &CanonicalCheckerContext<'_>, file: FileId, expected: bool) {
    let source = checker.source_file(file).unwrap();
    assert_eq!(
        checker
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked),
        expected
    );
}

fn assert_alias_default(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    alias: &Alias,
    constraint: Option<TypeId>,
    default: TypeId,
) {
    let [parameter] = alias.parameters.as_slice() else {
        panic!("expected one declared type parameter")
    };
    let alias_owner = symbol(checker, alias.declaration);
    let owner = symbol(checker, parameter.declaration);
    assert_ne!(owner, alias_owner);
    assert_eq!(
        parsed.arena.get(parameter.declaration.node).unwrap().parent,
        Some(alias.declaration.node)
    );
    let type_ = query_alias(checker, alias);
    assert_eq!(
        checker
            .store()
            .type_alias_links(alias_owner)
            .unwrap()
            .type_parameters
            .as_deref(),
        Some(&[type_][..])
    );
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("the alias body must retain its own type parameter")
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    if let Some(constraint) = constraint {
        assert_eq!(data.constraint, Some(constraint));
        assert_eq!(
            parsed
                .arena
                .get(parameter.constraint.unwrap().node)
                .unwrap()
                .parent,
            Some(parameter.declaration.node)
        );
        assert_eq!(
            checker.get_type_from_type_node(parameter.constraint.unwrap()),
            Ok(constraint)
        );
    } else {
        assert_eq!(parameter.constraint, None);
    }
    let default_node = parameter.default.unwrap();
    assert_eq!(
        parsed.arena.get(default_node.node).unwrap().parent,
        Some(parameter.declaration.node)
    );
    assert_eq!(checker.get_type_from_type_node(default_node), Ok(default));
    assert_eq!(checker.get_type_from_type_node(alias.body), Ok(type_));
    assert_eq!(
        checker.get_symbol_at_location(alias.name),
        Ok(Some(alias_owner))
    );
    assert_eq!(
        checker.get_symbol_at_location(parameter.name),
        Ok(Some(owner))
    );
    assert_eq!(checker.get_symbol_at_location(alias.body), Ok(Some(owner)));
}

fn assert_errors(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    expected: &[(&Alias, &str, &str)],
) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, &(alias, default, constraint)) in diagnostics.iter().zip(expected) {
        let node = alias.parameters[0].default.unwrap();
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2344);
        assert_eq!(diagnostic.diagnostic.arguments, [default, constraint]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!("Type '{default}' does not satisfy the constraint '{constraint}'.")
        );
        assert!(diagnostic.related_information.is_empty());
        let declaration = parsed.arena.get(alias.declaration.node).unwrap().range;
        let start = usize::try_from(declaration.start.get()).unwrap();
        let end = usize::try_from(declaration.end.get()).unwrap();
        let offset = start + source[start..end].find(&format!("= {default}")).unwrap() + 2;
        let range = parsed.arena.get(node.node).unwrap().range;
        assert_eq!(usize::try_from(range.start.get()).unwrap(), offset);
        assert_eq!(
            usize::try_from(range.end.get()).unwrap(),
            offset + default.len()
        );
        assert_eq!(&source[offset..offset + default.len()], default);
    }
}

fn assert_recheck_stable(
    checker: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
) {
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.relation_state_snapshot(),
            files
                .iter()
                .flat_map(|&(file, parsed)| {
                    parsed.arena.iter().map(move |(node, _)| {
                        let node = NodeRef::new(parsed.arena.id(), file, node);
                        (
                            node,
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
                .map(|(symbol, _)| {
                    (
                        symbol,
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            files
                .iter()
                .map(|(file, _)| {
                    store
                        .source_file_links(checker.source_file(*file).unwrap())
                        .cloned()
                })
                .collect::<Vec<_>>(),
            checker.diagnostics().clone(),
        )
    };
    let before = snapshot(checker);
    for _ in 0..2 {
        for &(file, _) in files {
            checker.check_source_file(file).unwrap();
            assert_checked(checker, file, true);
            assert_eq!(snapshot(checker), before);
            checker.recheck_source_file(file).unwrap();
            assert_checked(checker, file, true);
            assert_eq!(snapshot(checker), before);
        }
    }
}

fn function(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), PROVIDER, node))
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

fn call_result(
    checker: &mut CanonicalCheckerContext<'_>,
    consumer: &ParseResult,
    provider: &ParseResult,
    expected: &str,
    callee: &str,
) -> TypeId {
    let (node, variable) = consumer
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &consumer.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some((NodeRef::new(consumer.arena.id(), CONSUMER, node), variable))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"));
    let owner = symbol(checker, node);
    let name = NodeRef::new(node.arena, node.file, variable.name);
    let call = NodeRef::new(node.arena, node.file, variable.initializer.unwrap());
    let type_ = checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(checker.get_type_at_location(name), Ok(type_));
    assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
    assert_eq!(checker.get_type_at_location(call), Ok(type_));
    let signature = checker
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let signature = checker.store().signature(signature).unwrap();
    assert_eq!(signature.declaration(), Some(function(provider, callee)));
    assert_eq!(signature.resolved_return_type(), Some(type_));
    assert!(signature.type_parameters().is_empty());
    assert!(signature.parameters().is_empty());
    type_
}

fn assert_import_targets(
    checker: &CanonicalCheckerContext<'_>,
    consumer: &ParseResult,
    provider: &ParseResult,
) {
    let imports = consumer
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::ImportSpecifier(import) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &consumer.arena.get(import.name)?.data else {
                return None;
            };
            Some((
                NodeRef::new(consumer.arena.id(), CONSUMER, node),
                name.text.as_str(),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(imports.len(), 2);
    for (binding, name) in imports {
        let target = symbol(checker, function(provider, name));
        let imported = symbol(checker, binding);
        let links = checker.store().alias_symbol_links(imported).unwrap();
        assert_eq!(links.immediate_target, Some(target));
        assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    }
}

#[test]
fn alias_defaults_report_declaration_errors_in_source_order_after_lazy_queries() {
    let parsed = parse_source_file(LOCAL_SOURCE);
    let broken = alias(&parsed, LOCAL, "Broken");
    let valid = alias(&parsed, LOCAL, "Valid");
    let other = alias(&parsed, LOCAL, "Other");
    let free = alias(&parsed, LOCAL, "Free");
    for order in [QueryOrder::Source, QueryOrder::Alias, QueryOrder::Default] {
        let mut checker = context(
            &[(LOCAL, &parsed, "\"/project/alias-defaults.ts\"")],
            CanonicalModuleState::Script,
        );
        for alias in [&free, &other, &valid, &broken] {
            if matches!(order, QueryOrder::Default) {
                checker
                    .get_type_from_type_node(alias.parameters[0].default.unwrap())
                    .unwrap();
            }
            if !matches!(order, QueryOrder::Source) {
                query_alias(&mut checker, alias);
            }
        }
        assert_checked(&checker, LOCAL, false);
        assert!(checker.diagnostics().is_empty());
        checker.check_source_file(LOCAL).unwrap();
        assert_checked(&checker, LOCAL, true);
        assert_errors(
            &checker,
            &parsed,
            LOCAL_SOURCE,
            &[(&broken, "number", "string"), (&other, "string", "number")],
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_alias_default(&mut checker, &parsed, &broken, Some(string), number);
        assert_alias_default(&mut checker, &parsed, &other, Some(number), string);
        assert_alias_default(&mut checker, &parsed, &free, None, number);
        let ready = checker
            .get_type_from_type_node(valid.parameters[0].default.unwrap())
            .unwrap();
        let TypeData::Literal(literal) = checker.store().type_payload(ready).unwrap().data() else {
            panic!("the valid default must keep its string literal")
        };
        assert_eq!(literal.value, LiteralValue::String("ready".to_owned()));
        assert_eq!(literal.regular_type, ready);
        assert_alias_default(&mut checker, &parsed, &valid, Some(string), ready);
        assert_errors(
            &checker,
            &parsed,
            LOCAL_SOURCE,
            &[(&broken, "number", "string"), (&other, "string", "number")],
        );
        assert_recheck_stable(&mut checker, &[(LOCAL, &parsed)]);
    }
}

#[test]
fn imported_alias_defaults_wait_for_provider_checking_and_do_not_duplicate_errors() {
    let consumer = parse_source_file(CONSUMER_SOURCE);
    let provider = parse_source_file(PROVIDER_SOURCE);
    let broken = alias(&provider, PROVIDER, "Broken");
    let valid = alias(&provider, PROVIDER, "Valid");
    for provider_first in [false, true] {
        let mut checker = context(
            &[
                (CONSUMER, &consumer, "\"/project/consumer.ts\""),
                (PROVIDER, &provider, "\"/project/provider.ts\""),
            ],
            CanonicalModuleState::External,
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_ne!(query_alias(&mut checker, &broken), number);
        query_alias(&mut checker, &valid);
        assert_checked(&checker, CONSUMER, false);
        assert_checked(&checker, PROVIDER, false);
        assert!(checker.diagnostics().is_empty());
        if provider_first {
            checker.check_source_file(PROVIDER).unwrap();
            assert_errors(
                &checker,
                &provider,
                PROVIDER_SOURCE,
                &[(&broken, "number", "string")],
            );
        }
        checker.check_source_file(CONSUMER).unwrap();
        assert_checked(&checker, CONSUMER, true);
        assert_checked(&checker, PROVIDER, provider_first);
        assert_eq!(
            call_result(&mut checker, &consumer, &provider, "used", "readBroken"),
            number
        );
        let ready = call_result(&mut checker, &consumer, &provider, "good", "readValid");
        assert_eq!(checker.type_to_string(ready).unwrap(), "\"ready\"");
        if !provider_first {
            assert!(checker.diagnostics().is_empty());
            checker.recheck_source_file(CONSUMER).unwrap();
            assert_checked(&checker, PROVIDER, false);
            assert!(checker.diagnostics().is_empty());
            checker.check_source_file(PROVIDER).unwrap();
        }
        assert_checked(&checker, PROVIDER, true);
        assert_errors(
            &checker,
            &provider,
            PROVIDER_SOURCE,
            &[(&broken, "number", "string")],
        );
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_alias_default(&mut checker, &provider, &broken, Some(string), number);
        assert_alias_default(&mut checker, &provider, &valid, Some(string), ready);
        assert_eq!(
            call_result(&mut checker, &consumer, &provider, "used", "readBroken"),
            number
        );
        assert_eq!(
            call_result(&mut checker, &consumer, &provider, "good", "readValid"),
            ready
        );
        assert_import_targets(&checker, &consumer, &provider);
        assert_recheck_stable(
            &mut checker,
            &[(CONSUMER, &consumer), (PROVIDER, &provider)],
        );
        assert_errors(
            &checker,
            &provider,
            PROVIDER_SOURCE,
            &[(&broken, "number", "string")],
        );
    }
}
