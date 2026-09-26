use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, EffectsSignatureState, IntrinsicBootstrapOptions, NodeLinks,
    RelationStateSnapshot, SignatureLinks, SourceCheckError, SourceFileLinks, SymbolNodeLinks,
    TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    types::ObjectFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(203_480);
const PROVIDER_FILE: FileId = FileId::new(203_481);
const AUGMENTATION_FILE: FileId = FileId::new(203_482);
const FILE: FileId = FileId::new(203_483);
const DEFAULT_PROVIDER_FILE: FileId = FileId::new(203_484);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const CONSUMER: &str = concat!(
    "class Holder {\n",
    "  value?: ConditionValue;\n",
    "  observe(): void {\n",
    "    const before = this.value;\n",
    "    if (this.value) { const present = this.value; }\n",
    "    else { const absent = this.value; }\n",
    "    const after = this.value;\n",
    "  }\n",
    "}\n",
);
const ERROR_CONSUMER: &str = concat!(
    "class Holder {\n",
    "  value?: Error;\n",
    "  observe(): void {\n",
    "    const before = this.value;\n",
    "    if (this.value) { const present = this.value; }\n",
    "    else { const absent = this.value; }\n",
    "    const after = this.value;\n",
    "  }\n",
    "}\n",
);
const DIAGNOSTIC_PROVIDER: &str = concat!(
    "interface DeferredCallback { new (); }\n",
    "interface Error {\n",
    "  untyped;\n",
    "  callback: DeferredCallback;\n",
    "  inspect(): void;\n",
    "}\n",
);

fn context<'a>(files: &[(FileId, &'a ParseResult)], exact: bool) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed) in files {
        let (path, declaration, default_library, module) = match file {
            ES5_FILE => (
                "\"/lib/lib.es5.d.ts\"",
                true,
                true,
                CanonicalModuleState::Script,
            ),
            DEFAULT_PROVIDER_FILE => (
                "\"/lib/lib.condition.d.ts\"",
                true,
                true,
                CanonicalModuleState::Script,
            ),
            PROVIDER_FILE => (
                "\"/project/provider.d.ts\"",
                true,
                false,
                CanonicalModuleState::Script,
            ),
            AUGMENTATION_FILE => (
                "\"/project/augmentation.d.ts\"",
                true,
                false,
                CanonicalModuleState::External,
            ),
            FILE => (
                "\"/project/condition.ts\"",
                false,
                false,
                CanonicalModuleState::Script,
            ),
            _ => panic!("unexpected source file"),
        };
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
                    default_library,
                    module,
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
            .map(|&(file, parsed)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: exact,
            },
            strict_property_initialization: true,
            strict_function_types: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, node)
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| (record.kind == kind).then_some(reference(parsed, file, node)))
        .collect::<Vec<_>>();
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn interface(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(reference(parsed, file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"))
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::InterfaceDeclaration(data) = &parsed.arena.get(owner.node).unwrap().data else {
        panic!("expected the real interface")
    };
    data.members
        .nodes
        .iter()
        .find_map(|&node| {
            let name = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                _ => return None,
            };
            let NodeData::Identifier(name_data) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name_data.text == expected).then_some((
                reference(parsed, owner.file, node),
                reference(parsed, owner.file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn raw_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn local_read(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| reference(parsed, FILE, data.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing local {expected}"))
}

fn field(parsed: &ParseResult) -> (NodeRef, NodeRef, NodeRef) {
    let declaration = only_node(parsed, FILE, SyntaxKind::PropertyDeclaration);
    let NodeData::PropertyDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.postfix_token.is_some());
    (
        declaration,
        reference(parsed, FILE, data.name),
        reference(parsed, FILE, data.type_.unwrap()),
    )
}

fn guard(parsed: &ParseResult) -> NodeRef {
    let branch = only_node(parsed, FILE, SyntaxKind::IfStatement);
    let NodeData::IfStatement(data) = &parsed.arena.get(branch.node).unwrap().data else {
        unreachable!()
    };
    reference(parsed, FILE, data.expression)
}

fn assert_members(checker: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let mut actual = match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Union(data) => data.union.types.clone(),
        _ => vec![type_],
    };
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    assert_eq!(actual, expected);
}

fn assert_cold_interface(checker: &CanonicalCheckerContext<'_>, type_: TypeId) {
    let record = checker.store().type_payload(type_).unwrap();
    let TypeData::Interface(data) = record.data() else {
        panic!("expected the actual interface identity")
    };
    assert!(
        !record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    );
    assert!(!data.declared_members_resolved);
    assert!(data.declared_call_signatures.is_none());
    assert!(data.declared_construct_signatures.is_none());
    assert!(data.declared_index_infos.is_none());
    assert!(data.reference.object.structured.members.is_none());
    assert!(data.reference.object.structured.signatures.is_none());
}

fn assert_provider_unchecked(checker: &CanonicalCheckerContext<'_>, file: FileId) {
    assert_eq!(
        checker
            .store()
            .source_file_links(checker.source_file(file).unwrap()),
        None
    );
}

fn assert_member_unread(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) {
    let member = symbol(checker, declaration);
    assert_eq!(checker.store().value_symbol_links(member), None);
    assert_eq!(checker.store().type_node_links(declaration), None);
    assert_eq!(checker.store().signature_links(declaration), None);
}

fn assert_library_owners(checker: &CanonicalCheckerContext<'_>, library: &ParseResult) {
    let store = checker.store();
    let globals = store.symbol_table(checker.globals()).unwrap();
    for (name, type_) in [
        ("Array", checker.global_types().array_type),
        ("ReadonlyArray", checker.global_types().readonly_array_type),
        ("Object", checker.global_types().object_type),
    ] {
        let owner = store
            .get_merged_symbol(globals.get_source(name).unwrap())
            .unwrap();
        assert_eq!(store.type_payload(type_).unwrap().symbol(), Some(owner));
        let declaration = interface(library, ES5_FILE, name);
        assert_eq!(symbol(checker, declaration), owner);
        assert!(
            store
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()
                .contains(&declaration)
        );
        assert_eq!(
            store.declared_type_links(owner).unwrap().declared_type,
            Some(type_)
        );
    }
    assert_ne!(
        checker.global_types().array_type,
        checker.global_types().readonly_array_type
    );
}

fn assert_merged_error_owner(
    checker: &CanonicalCheckerContext<'_>,
    library: &ParseResult,
    provider: &ParseResult,
) -> SemanticSymbolId {
    let original = interface(library, ES5_FILE, "Error");
    let added = interface(provider, PROVIDER_FILE, "Error");
    let owner = symbol(checker, original);
    assert_eq!(symbol(checker, added), owner);
    let value = library
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == "Error").then_some(reference(library, ES5_FILE, node))
        })
        .unwrap();
    assert_eq!(symbol(checker, value), owner);
    let record = checker.store().symbol(owner).unwrap();
    assert!(record.flags().contains(
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
    ));
    assert_eq!(record.declarations(), Some(&[original, value, added][..]));
    assert_eq!(record.value_declaration(), Some(value));
    assert_eq!(
        checker
            .store()
            .symbol_table(checker.globals())
            .unwrap()
            .get_source("Error"),
        Some(owner)
    );
    owner
}

fn assert_field_owner(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> TypeId {
    let class = only_node(parsed, FILE, SyntaxKind::ClassDeclaration);
    let class_owner = symbol(checker, class);
    let (declaration, _, _) = field(parsed);
    let member = symbol(checker, declaration);
    let record = checker.store().symbol(member).unwrap();
    assert_eq!(record.parent(), Some(class_owner));
    assert_eq!(record.value_declaration(), Some(declaration));
    assert_eq!(
        parsed.arena.get(declaration.node).unwrap().parent,
        Some(class.node)
    );
    let table = checker
        .store()
        .symbol(class_owner)
        .unwrap()
        .members()
        .unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(table)
            .unwrap()
            .get(record.name()),
        Some(member)
    );
    let instance = checker
        .store()
        .declared_type_links(class_owner)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(data) = checker.store().type_payload(instance).unwrap().data() else {
        panic!("expected the real class instance")
    };
    data.this_type.unwrap()
}

type NodePublication = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<TypeAliasLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 9],
    relation: RelationStateSnapshot,
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    files: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(
    checker: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
) -> Publication {
    let store = checker.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_predicate_len(),
            store.index_info_len(),
            store.type_resolution_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relation: store.relation_state_snapshot(),
        nodes: files
            .iter()
            .flat_map(|&(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = reference(parsed, file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect(),
        files: files
            .iter()
            .map(|&(file, _)| {
                store
                    .source_file_links(checker.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_flow(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    owner: SemanticSymbolId,
) -> Vec<(NodeRef, TypeId, SemanticSymbolId)> {
    let (declaration, name, annotation) = field(parsed);
    let field_symbol = symbol(checker, declaration);
    let this_type = assert_field_owner(checker, parsed);
    let field_record = checker.store().symbol(field_symbol).unwrap();
    assert!(
        field_record
            .flags()
            .contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
    );
    assert_eq!(field_record.declarations(), Some(&[declaration][..]));
    let type_ = checker
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(raw_type(checker, annotation), type_);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(field_symbol)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    assert_eq!(
        checker.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    let optional = raw_type(checker, guard(parsed));
    let sentinel = checker
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_or_missing_type;
    assert_members(checker, optional, &[type_, sentinel]);
    let edges = checker
        .file(FILE)
        .unwrap()
        .1
        .flow_graph()
        .nodes()
        .iter()
        .filter(|flow| {
            flow.payload == Some(FlowNodePayload::Ast(guard(parsed)))
                && flow
                    .flags
                    .intersects(FlowFlags::TRUE_CONDITION | FlowFlags::FALSE_CONDITION)
        })
        .collect::<Vec<_>>();
    assert_eq!(edges.len(), 2);
    assert!(
        edges
            .iter()
            .any(|edge| edge.flags.contains(FlowFlags::TRUE_CONDITION))
    );
    assert!(
        edges
            .iter()
            .any(|edge| edge.flags.contains(FlowFlags::FALSE_CONDITION))
    );
    assert_eq!(edges[0].antecedent, edges[1].antecedent);
    assert!(edges[0].antecedent.is_some());
    let mut queries = vec![(name, optional, field_symbol)];
    for (node, expected) in [
        (guard(parsed), optional),
        (local_read(parsed, "before"), optional),
        (local_read(parsed, "present"), type_),
        (local_read(parsed, "absent"), sentinel),
        (local_read(parsed, "after"), optional),
    ] {
        let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(node.node).unwrap().data
        else {
            panic!("expected the actual field access")
        };
        let receiver = reference(parsed, FILE, access.expression);
        assert_eq!(
            parsed.arena.get(receiver.node).unwrap().kind,
            SyntaxKind::ThisKeyword
        );
        assert_eq!(raw_type(checker, receiver), this_type);
        assert_eq!(raw_type(checker, node), expected);
        assert_eq!(
            checker
                .store()
                .symbol_node_links(node)
                .unwrap()
                .resolved_symbol,
            Some(field_symbol)
        );
        queries.push((node, expected, field_symbol));
    }
    queries
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    queries: &[(NodeRef, TypeId, SemanticSymbolId)],
) {
    let checked = checker.source_file(FILE).unwrap();
    assert!(
        checker
            .store()
            .source_file_links(checked)
            .unwrap()
            .type_checked
    );
    let before = publication(checker, files);
    for forced in [false, true, true] {
        if forced {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for &(node, type_, symbol) in queries {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(node), Ok(Some(symbol)));
        }
        assert_eq!(publication(checker, files), before);
    }
}

#[test]
fn interface_conditions_keep_cold_method_headers_and_real_flow_reads() {
    for query_first in [false, true] {
        for exact in [false, true] {
            let library = parse_source_file(ES5);
            let provider = parse_source_file(
                "interface Error { label: string; inspect(values: number[]): void; }",
            );
            let parsed = parse_source_file(ERROR_CONSUMER);
            let files = [
                (ES5_FILE, &library),
                (PROVIDER_FILE, &provider),
                (FILE, &parsed),
            ];
            let mut checker = context(&files, exact);
            assert_library_owners(&checker, &library);
            let declaration = interface(&provider, PROVIDER_FILE, "Error");
            let owner = assert_merged_error_owner(&checker, &library, &provider);
            let inspect = member(&provider, declaration, "inspect");
            let label = member(&provider, declaration, "label");
            if query_first {
                let (field, _, annotation) = field(&parsed);
                let type_ = checker.get_type_from_type_node(annotation).unwrap();
                let field_symbol = symbol(&checker, field);
                assert_eq!(checker.get_class_query_member_type(field_symbol), Ok(type_));
                assert_cold_interface(&checker, type_);
                assert_provider_unchecked(&checker, FILE);
            }
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let queries = assert_flow(&checker, &parsed, owner);
            let type_ = raw_type(&checker, field(&parsed).2);
            assert_cold_interface(&checker, type_);
            assert_provider_unchecked(&checker, PROVIDER_FILE);
            assert_member_unread(&checker, inspect.0);
            assert_member_unread(&checker, label.0);
            assert_replay(&mut checker, &files, &queries);

            let callable = checker.get_type_at_location(inspect.1).unwrap();
            let signature = checker
                .store()
                .signature_links(inspect.0)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            let record = checker.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(inspect.0));
            assert_eq!(
                record.resolved_return_type(),
                Some(checker.store().intrinsic_bootstrap().unwrap().void_type)
            );
            let parameter = record.parameters()[0];
            let array = checker
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::TypeReference(data) = checker.store().type_payload(array).unwrap().data()
            else {
                panic!("expected the real Array parameter")
            };
            assert_eq!(data.object.target, Some(checker.global_types().array_type));
            assert_eq!(
                data.resolved_type_arguments.as_deref(),
                Some(&[checker.store().intrinsic_bootstrap().unwrap().number_type][..])
            );
            assert_eq!(checker.get_type_at_location(inspect.1), Ok(callable));
            assert_provider_unchecked(&checker, PROVIDER_FILE);
            assert_member_unread(&checker, label.0);
            assert_replay(&mut checker, &files, &queries);
        }
    }
}

fn assert_provider_diagnostics(checker: &CanonicalCheckerContext<'_>, provider: &ParseResult) {
    let owner = interface(provider, PROVIDER_FILE, "Error");
    let untyped = member(provider, owner, "untyped").1;
    let call = only_node(provider, PROVIDER_FILE, SyntaxKind::ConstructSignature);
    let expected = [
        (
            call,
            7013,
            "Construct signature, which lacks return-type annotation, implicitly has an 'any' return type.",
        ),
        (
            untyped,
            7008,
            "Member 'untyped' implicitly has an 'any' type.",
        ),
    ];
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, (node, code, message)) in diagnostics.iter().zip(expected) {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), code);
        let arguments = if code == 7008 {
            vec!["untyped", "any"]
        } else {
            Vec::new()
        };
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
    }
}

#[test]
fn interface_conditions_leave_provider_diagnostics_to_the_real_source_check() {
    for provider_first in [false, true] {
        let library = parse_source_file(ES5);
        let provider = parse_source_file(DIAGNOSTIC_PROVIDER);
        let parsed = parse_source_file(ERROR_CONSUMER);
        let files = [
            (ES5_FILE, &library),
            (PROVIDER_FILE, &provider),
            (FILE, &parsed),
        ];
        let mut checker = context(&files, false);
        let declaration = interface(&provider, PROVIDER_FILE, "Error");
        let owner = assert_merged_error_owner(&checker, &library, &provider);
        if provider_first {
            checker.check_source_file(PROVIDER_FILE).unwrap();
            assert_provider_diagnostics(&checker, &provider);
        }
        checker.check_source_file(FILE).unwrap();
        let queries = assert_flow(&checker, &parsed, owner);
        if !provider_first {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            assert_provider_unchecked(&checker, PROVIDER_FILE);
            assert_cold_interface(&checker, raw_type(&checker, field(&parsed).2));
            for name in ["untyped", "callback", "inspect"] {
                assert_member_unread(&checker, member(&provider, declaration, name).0);
            }
            let callback = interface(&provider, PROVIDER_FILE, "DeferredCallback");
            assert_eq!(
                checker
                    .store()
                    .declared_type_links(symbol(&checker, callback)),
                None
            );
            assert_eq!(
                checker.store().signature_links(only_node(
                    &provider,
                    PROVIDER_FILE,
                    SyntaxKind::ConstructSignature
                )),
                None
            );
            assert_replay(&mut checker, &files, &queries);
            checker.check_source_file(PROVIDER_FILE).unwrap();
        }
        assert_provider_diagnostics(&checker, &provider);
        assert_replay(&mut checker, &files, &queries);
        let before = publication(&checker, &files);
        checker.recheck_source_file(PROVIDER_FILE).unwrap();
        assert_eq!(publication(&checker, &files), before);
        assert_provider_diagnostics(&checker, &provider);
    }
}

fn assert_resolved_alias_receiver(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    alias: SemanticSymbolId,
    alias_root: NodeRef,
) -> TypeId {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        unreachable!()
    };
    let this_type = data.this_type.unwrap();
    let TypeData::TypeParameter(this) = checker.store().type_payload(this_type).unwrap().data()
    else {
        panic!("the alias base must retain the actual synthetic this")
    };
    assert!(this.is_this_type);
    assert_eq!(this.constraint, Some(type_));
    let alias_type = checker
        .store()
        .type_alias_links(alias)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(
        alias_type,
        checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_type_literal_type
    );
    assert_eq!(raw_type(checker, alias_root), alias_type);
    alias_type
}

#[test]
fn interface_conditions_keep_the_merged_owner_and_real_conditional_alias_base() {
    for query_first in [false, true] {
        let library = parse_source_file(ES5);
        let provider = parse_source_file(concat!(
            "interface ConditionBody { body: number; }\n",
            "interface ConditionValue extends ConditionBody { inspect(): void; }\n",
            "declare var ConditionValue: { readonly prototype: ConditionValue; new (): ConditionValue; };\n",
        ));
        let augmentation = parse_source_file(concat!(
            "type LocalConditionBase = {} extends {} ? {} : { fallback: number; };\n",
            "export {};\n",
            "declare global { interface ConditionValue extends LocalConditionBase {} }\n",
        ));
        let parsed = parse_source_file(CONSUMER);
        let files = [
            (ES5_FILE, &library),
            (DEFAULT_PROVIDER_FILE, &provider),
            (AUGMENTATION_FILE, &augmentation),
            (FILE, &parsed),
        ];
        let mut checker = context(&files, false);
        assert_library_owners(&checker, &library);
        let original = interface(&provider, DEFAULT_PROVIDER_FILE, "ConditionValue");
        let added = interface(&augmentation, AUGMENTATION_FILE, "ConditionValue");
        let owner = symbol(&checker, original);
        assert_eq!(symbol(&checker, added), owner);
        let record = checker.store().symbol(owner).unwrap();
        assert!(record.flags().contains(
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
        ));
        assert!(record.declarations().unwrap().contains(&original));
        assert!(record.declarations().unwrap().contains(&added));
        let alias_declaration = only_node(
            &augmentation,
            AUGMENTATION_FILE,
            SyntaxKind::TypeAliasDeclaration,
        );
        let NodeData::TypeAliasDeclaration(alias_data) =
            &augmentation.arena.get(alias_declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let alias_root = reference(&augmentation, AUGMENTATION_FILE, alias_data.type_);
        let alias = symbol(&checker, alias_declaration);
        if query_first {
            let type_ = checker.get_type_from_type_node(field(&parsed).2).unwrap();
            assert_cold_interface(&checker, type_);
            assert!(
                checker
                    .store()
                    .type_alias_links(alias)
                    .is_none_or(|links| links.declared_type.is_none())
            );
            assert!(
                checker
                    .store()
                    .type_node_links(alias_root)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );
            assert_provider_unchecked(&checker, FILE);
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let queries = assert_flow(&checker, &parsed, owner);
        let type_ = raw_type(&checker, field(&parsed).2);
        let alias_type = assert_resolved_alias_receiver(&checker, type_, alias, alias_root);
        assert!(
            checker
                .store()
                .value_symbol_links(owner)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
        assert_provider_unchecked(&checker, DEFAULT_PROVIDER_FILE);
        assert_provider_unchecked(&checker, AUGMENTATION_FILE);
        assert_member_unread(&checker, member(&provider, original, "inspect").0);
        assert_replay(&mut checker, &files, &queries);
        let before = publication(&checker, &files);
        assert_eq!(checker.get_type_from_type_node(alias_root), Ok(alias_type));
        assert_eq!(checker.get_type_from_type_node(field(&parsed).2), Ok(type_));
        assert_eq!(publication(&checker, &files), before);
    }
}

fn assert_special_member_rejection(provider: &str, augmentation: &str) {
    let library = parse_source_file(ES5);
    let provider = parse_source_file(provider);
    let augmentation = parse_source_file(augmentation);
    let parsed = parse_source_file(CONSUMER);
    let files = [
        (ES5_FILE, &library),
        (PROVIDER_FILE, &provider),
        (AUGMENTATION_FILE, &augmentation),
        (FILE, &parsed),
    ];
    let mut checker = context(&files, false);
    assert_library_owners(&checker, &library);
    let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(guard(&parsed)));
    assert_eq!(checker.check_source_file(FILE), Err(error));
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    assert_provider_unchecked(&checker, PROVIDER_FILE);
    assert_provider_unchecked(&checker, AUGMENTATION_FILE);
    assert_eq!(
        checker
            .store()
            .type_node_links(local_read(&parsed, "present")),
        None
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(local_read(&parsed, "after")),
        None
    );
    let before = publication(&checker, &files);
    for _ in 0..2 {
        assert_eq!(checker.check_source_file(FILE), Err(error));
        assert_eq!(checker.recheck_source_file(FILE), Err(error));
        assert_eq!(publication(&checker, &files), before);
    }
}

#[test]
fn interface_conditions_require_inherited_and_augmented_special_members_to_be_absent() {
    for provider in [
        "interface ConditionValue { inspect(): void; then: number; }",
        "interface ConditionValue { inspect(): void; bind: number; }",
        "interface ConditionValue { inspect(): void; (): void; }",
        "interface ConditionValue { inspect(): void; new (): {}; }",
        "interface ConditionValue { inspect(): void; [key: string]: unknown; }",
        "interface Parent { then: number; } interface ConditionValue extends Parent { inspect(): void; }",
    ] {
        assert_special_member_rejection(provider, "export {};");
    }
    for augmentation in [
        "export {}; declare global { interface ConditionValue { then: number; } }",
        "export {}; declare global { interface Object { then: number; } }",
    ] {
        assert_special_member_rejection(
            "interface ConditionValue { inspect(): void; }",
            augmentation,
        );
    }
}

#[test]
fn interface_conditions_keep_completed_ordinary_calls_separate_from_the_header() {
    let library = parse_source_file(ES5);
    let provider = parse_source_file("interface ConditionValue { inspect(): void; }");
    let source = format!(
        "declare function touch(): void;\n{}",
        CONSUMER.replace("{ const present", "{ touch(); const present"),
    );
    let parsed = parse_source_file(&source);
    let files = [
        (ES5_FILE, &library),
        (PROVIDER_FILE, &provider),
        (FILE, &parsed),
    ];
    let mut checker = context(&files, false);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let owner = symbol(
        &checker,
        interface(&provider, PROVIDER_FILE, "ConditionValue"),
    );
    let queries = assert_flow(&checker, &parsed, owner);
    let call = only_node(&parsed, FILE, SyntaxKind::CallExpression);
    let declaration = only_node(&parsed, FILE, SyntaxKind::FunctionDeclaration);
    let links = checker.store().signature_links(call).unwrap();
    assert_eq!(links.effects_signature, EffectsSignatureState::Unresolved);
    let signature = links.resolved_signature.signature().unwrap();
    assert_eq!(
        checker.store().signature(signature).unwrap().declaration(),
        Some(declaration)
    );
    assert_eq!(
        checker
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    assert_eq!(
        raw_type(&checker, call),
        checker.store().intrinsic_bootstrap().unwrap().void_type
    );
    assert_provider_unchecked(&checker, PROVIDER_FILE);
    assert_replay(&mut checker, &files, &queries);
}
