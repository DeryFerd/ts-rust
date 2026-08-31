use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags, canonical_has_syntactic_modifier,
};
use ts_checker::semantic::{
    CanonicalArtifactQueryError, CanonicalCheckerContext, CanonicalCheckerOptions,
    DeclaredTypeError, IntrinsicBootstrapOptions, TypeData, TypeId, TypeNodeUnavailable,
    type_records::{InterfaceTypeData, StructuredTypeData},
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(203_160);
const AUGMENTATION: FileId = FileId::new(203_161);
const CONSUMER: FileId = FileId::new(203_162);

#[derive(Clone, Copy)]
struct Input<'a> {
    file: FileId,
    parsed: &'a ParseResult,
    path: &'static str,
    declaration: bool,
    default_library: bool,
    module: CanonicalModuleState,
}

fn context<'a>(inputs: &[Input<'a>]) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{:?}",
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.declaration,
                    input.default_library,
                    input.module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
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

fn input(parsed: &ParseResult, file: FileId) -> Input<'_> {
    match file {
        LIBRARY => Input {
            file,
            parsed,
            path: "\"/lib/lib.packet.d.ts\"",
            declaration: true,
            default_library: true,
            module: CanonicalModuleState::Script,
        },
        AUGMENTATION => Input {
            file,
            parsed,
            path: "\"/types/packet-extra.d.ts\"",
            declaration: true,
            default_library: false,
            module: CanonicalModuleState::External,
        },
        CONSUMER => Input {
            file,
            parsed,
            path: "\"/project/packet-consumer.ts\"",
            declaration: false,
            default_library: false,
            module: CanonicalModuleState::Script,
        },
        _ => panic!("unknown test input"),
    }
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::ModuleDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name}"))
}

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker
        .store()
        .get_merged_symbol(raw_symbol(checker, node))
        .unwrap()
}

fn alias(parsed: &ParseResult, file: FileId, name: &str) -> (NodeRef, NodeRef) {
    let declaration = declaration(parsed, file, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    (
        declaration,
        NodeRef::new(parsed.arena.id(), file, data.type_),
    )
}

fn variable_annotation(parsed: &ParseResult, file: FileId, name: &str) -> (NodeRef, NodeRef) {
    let declaration = declaration(parsed, file, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    (
        declaration,
        NodeRef::new(parsed.arena.id(), file, data.type_.unwrap()),
    )
}

fn member(parsed: &ParseResult, owner: NodeRef, name: &str) -> (NodeRef, NodeRef) {
    let members = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::InterfaceDeclaration(data) => &data.members.nodes,
        NodeData::TypeLiteralNode(data) => &data.members.nodes,
        _ => panic!("a member must have its actual interface or type-literal owner"),
    };
    members
        .iter()
        .find_map(|node| {
            let name_node = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(data) => data.name,
                NodeData::PropertySignatureDeclaration(data) => data.name,
                NodeData::MethodSignatureDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some((
                NodeRef::new(owner.arena, owner.file, *node),
                NodeRef::new(owner.arena, owner.file, name_node),
            ))
        })
        .unwrap_or_else(|| panic!("missing member {name}"))
}

fn access(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), CONSUMER, node))
        })
        .unwrap_or_else(|| panic!("missing property read {name}"))
}

fn heritage_name(parsed: &ParseResult, owner: NodeRef, expected: &str) -> NodeRef {
    let NodeData::InterfaceDeclaration(data) = &parsed.arena.get(owner.node).unwrap().data else {
        panic!("the written base must belong to its actual interface")
    };
    let [clause] = data.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
        panic!("the fixture has one extends clause")
    };
    let NodeData::HeritageClause(clause) = &parsed.arena.get(*clause).unwrap().data else {
        unreachable!()
    };
    clause
        .types
        .nodes
        .iter()
        .find_map(|node| {
            let NodeData::ExpressionWithTypeArguments(base) = &parsed.arena.get(*node)?.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(base.expression)?.data else {
                return None;
            };
            (base.type_arguments.is_none() && name.text == expected).then_some(NodeRef::new(
                owner.arena,
                owner.file,
                base.expression,
            ))
        })
        .unwrap_or_else(|| panic!("missing written base {expected}"))
}

fn assert_heritage_artifact(
    checker: &mut CanonicalCheckerContext<'_>,
    expression: NodeRef,
    owner: SemanticSymbolId,
    result: TypeId,
) {
    assert_eq!(checker.get_symbol_at_location(expression), Ok(Some(owner)));
    assert_eq!(checker.get_type_at_location(expression), Ok(result));
}

fn assert_heritage_artifact_unavailable(
    checker: &mut CanonicalCheckerContext<'_>,
    expression: NodeRef,
    owner_type: TypeId,
) {
    let error = CanonicalArtifactQueryError::InvalidType {
        node: expression,
        type_: owner_type,
    };
    assert_eq!(checker.get_symbol_at_location(expression), Err(error));
    assert_eq!(checker.get_type_at_location(expression), Err(error));
}

fn interface<'a>(checker: &'a CanonicalCheckerContext<'_>, type_: TypeId) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the declared interface must retain its canonical identity")
    };
    data
}

fn structured<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::Object(data) => &data.structured,
        _ => panic!("an interface base must have the actual object result"),
    }
}

fn property(checker: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    checker
        .store()
        .symbol_table(structured(checker, type_).members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("missing resolved property {name}"))
}

fn node_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<TypeId> {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
}

fn alias_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> Option<TypeId> {
    checker
        .store()
        .type_alias_links(owner)
        .and_then(|links| links.declared_type)
}

fn assert_unchecked(checker: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_this_identity(
    checker: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    type_: TypeId,
) {
    let record = checker.store().type_payload(type_).unwrap();
    let data = interface(checker, type_);
    let this = data
        .this_type
        .expect("a written alias base retains synthetic this");
    assert_eq!(record.symbol(), Some(owner));
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
    );
    assert_eq!(data.reference.object.target, Some(type_));
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some([].as_slice())
    );
    assert_eq!(data.all_type_parameters.as_deref(), Some([this].as_slice()));
    assert_eq!(data.outer_type_parameter_count, 0);
    let this_record = checker.store().type_payload(this).unwrap();
    assert_eq!(this_record.symbol(), Some(owner));
    let TypeData::TypeParameter(parameter) = this_record.data() else {
        panic!("synthetic this must remain a type parameter")
    };
    assert!(parameter.is_this_type);
    assert_eq!(parameter.constraint, Some(type_));
    assert!(parameter.target.is_none());
    assert!(parameter.mapper.is_none());
}

fn assert_alias_result(
    checker: &CanonicalCheckerContext<'_>,
    alias: (NodeRef, NodeRef),
    literal: NodeRef,
    result: TypeId,
) {
    let owner = symbol(checker, alias.0);
    assert_eq!(alias_type(checker, owner), Some(result));
    assert_eq!(node_type(checker, alias.1), Some(result));
    assert_eq!(node_type(checker, literal), Some(result));
    assert_eq!(
        checker.store().symbol(owner).unwrap().flags(),
        SymbolFlags::TYPE_ALIAS
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().declarations(),
        Some([alias.0].as_slice())
    );
    let record = checker.store().type_payload(result).unwrap();
    assert!(matches!(record.data(), TypeData::Object(_)));
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
    );
    assert!(
        !record
            .object_flags()
            .intersects(ObjectFlags::INTERFACE | ObjectFlags::CLASS)
    );
    let empty = checker.store().intrinsic_bootstrap().unwrap();
    if result == empty.empty_type_literal_type {
        assert_eq!(record.symbol(), Some(empty.empty_type_literal_symbol));
        assert!(record.alias().is_none());
        assert!(structured(checker, result).properties.is_none());
        assert!(
            checker
                .store()
                .symbol(empty.empty_type_literal_symbol)
                .unwrap()
                .declarations()
                .is_none()
        );
    } else {
        assert_eq!(record.symbol(), Some(symbol(checker, literal)));
        assert_ne!(record.symbol(), Some(owner));
        if alias.1 == literal {
            let identity = checker.store().type_alias(record.alias().unwrap()).unwrap();
            assert_eq!(identity.symbol(), Some(owner));
        }
    }
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    inputs: &[Input<'_>],
    types: &[TypeId],
    symbols: &[SemanticSymbolId],
) -> String {
    let store = checker.store();
    let counts = [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.merged_symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
        store.conditional_root_len(),
    ];
    let nodes = inputs
        .iter()
        .flat_map(|input| {
            input.parsed.arena.iter().map(move |(node, _)| {
                let node = NodeRef::new(input.parsed.arena.id(), input.file, node);
                (
                    node,
                    store.type_node_links(node),
                    store.symbol_node_links(node),
                    store.signature_links(node),
                )
            })
        })
        .collect::<Vec<_>>();
    let owners = symbols
        .iter()
        .map(|symbol| {
            (
                symbol,
                store.symbol(*symbol),
                store.declared_type_links(*symbol),
                store.type_alias_links(*symbol),
                store.value_symbol_links(*symbol),
            )
        })
        .collect::<Vec<_>>();
    let types = types
        .iter()
        .map(|type_| {
            let record = store.type_payload(*type_).unwrap();
            (
                record,
                record.alias().and_then(|alias| store.type_alias(alias)),
                structured(checker, *type_)
                    .members
                    .and_then(|members| store.symbol_table(members)),
            )
        })
        .collect::<Vec<_>>();
    let files = inputs
        .iter()
        .map(|input| store.source_file_links(checker.source_file(input.file).unwrap()))
        .collect::<Vec<_>>();
    format!(
        "{:#?}",
        (counts, nodes, owners, types, files, checker.diagnostics())
    )
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both merge phases, source owners, and the query-order matrix together.
fn merged_global_alias_bases_keep_all_declarations_and_inherited_owners() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Root { readonly root: number; }\n",
        "interface Packet extends Root { method(): number; }\n",
        "declare var Packet: { prototype: Packet; new(): Packet; };\n",
    ));
    let augmentation = parse_source_file(concat!(
        "export {};\n",
        "type Added = { readonly extra: string; optional?: number; };\n",
        "declare global {\n",
        "  interface Packet extends Added { added: boolean; }\n",
        "  var Packet: { prototype: Packet; new(): Packet; };\n",
        "}\n",
    ));
    let consumer = parse_source_file(concat!(
        "interface Packet { late: boolean; }\n",
        "declare const packet: Packet;\n",
        "const baseRead: number = packet.root;\n",
        "const aliasRead: string = packet.extra;\n",
        "const methodRead: number = packet.method();\n",
    ));
    let library_input = input(&library, LIBRARY);
    let augmentation_input = input(&augmentation, AUGMENTATION);
    let consumer_input = input(&consumer, CONSUMER);
    let interfaces = [
        declaration(
            &library,
            LIBRARY,
            SyntaxKind::InterfaceDeclaration,
            "Packet",
        ),
        declaration(
            &consumer,
            CONSUMER,
            SyntaxKind::InterfaceDeclaration,
            "Packet",
        ),
        declaration(
            &augmentation,
            AUGMENTATION,
            SyntaxKind::InterfaceDeclaration,
            "Packet",
        ),
    ];
    let values = [
        variable_annotation(&library, LIBRARY, "Packet"),
        variable_annotation(&augmentation, AUGMENTATION, "Packet"),
    ];
    let root = declaration(&library, LIBRARY, SyntaxKind::InterfaceDeclaration, "Root");
    let added = alias(&augmentation, AUGMENTATION, "Added");
    let extra = member(&augmentation, added.1, "extra");
    let optional = member(&augmentation, added.1, "optional");
    let root_property = member(&library, root, "root");
    let namespace = declaration(
        &augmentation,
        AUGMENTATION,
        SyntaxKind::ModuleDeclaration,
        "global",
    );
    let reads = [access(&consumer, "root"), access(&consumer, "extra")];
    let written_bases = [
        heritage_name(&library, interfaces[0], "Root"),
        heritage_name(&augmentation, interfaces[2], "Added"),
    ];

    for augmentation_first in [false, true] {
        let inputs = if augmentation_first {
            [augmentation_input, library_input, consumer_input]
        } else {
            [library_input, augmentation_input, consumer_input]
        };
        for first in ["consumer", "identity", "alias-root"] {
            let mut checker = context(&inputs);
            let owner = symbol(&checker, interfaces[0]);
            let alias_owner = symbol(&checker, added.0);
            let base_owner = symbol(&checker, root);
            let raw_augmentation = raw_symbol(&checker, interfaces[2]);
            let raw_namespace = raw_symbol(&checker, namespace);
            let exports = checker
                .store()
                .symbol(raw_namespace)
                .unwrap()
                .exports()
                .unwrap();
            let assert_owners = |checker: &CanonicalCheckerContext<'_>| {
                let store = checker.store();
                let record = store.symbol(owner).unwrap();
                assert_eq!(
                    record.flags(),
                    SymbolFlags::INTERFACE
                        | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        | SymbolFlags::TRANSIENT
                );
                assert_eq!(
                    record.declarations(),
                    Some(
                        [
                            interfaces[0],
                            values[0].0,
                            interfaces[1],
                            interfaces[2],
                            values[1].0
                        ]
                        .as_slice()
                    )
                );
                assert_eq!(record.value_declaration(), Some(values[0].0));
                for node in interfaces.into_iter().chain(values.map(|value| value.0)) {
                    assert_eq!(symbol(checker, node), owner);
                }
                let globals = store.intrinsic_bootstrap().unwrap().globals;
                let global_entry = store
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Packet")
                    .unwrap();
                assert_eq!(store.get_merged_symbol(global_entry), Some(owner));
                assert_ne!(raw_augmentation, owner);
                assert_eq!(
                    store.symbol_table(exports).unwrap().get_source("Packet"),
                    Some(raw_augmentation)
                );
                assert_eq!(
                    store.symbol(raw_augmentation).unwrap().parent(),
                    Some(raw_namespace)
                );
                assert_eq!(raw_symbol(checker, values[1].0), raw_augmentation);
                assert_ne!(alias_owner, owner);
                assert_ne!(alias_owner, raw_augmentation);
                let source = checker.source_file(AUGMENTATION).unwrap();
                let locals = checker
                    .file(AUGMENTATION)
                    .unwrap()
                    .1
                    .locals(source)
                    .unwrap();
                assert_eq!(
                    store.symbol_table(locals).unwrap().get_source("Added"),
                    Some(alias_owner)
                );
                assert_eq!(
                    store.symbol_table(globals).unwrap().get_source("Added"),
                    None
                );
                assert_eq!(
                    store.symbol(alias_owner).unwrap().declarations(),
                    Some([added.0].as_slice())
                );
                for (_, annotation) in values {
                    assert_eq!(node_type(checker, annotation), None);
                }
                assert!(
                    store
                        .value_symbol_links(owner)
                        .is_none_or(|links| links.resolved_type.is_none())
                );
                assert_unchecked(checker, LIBRARY);
                assert_unchecked(checker, AUGMENTATION);
            };
            assert_owners(&checker);
            let early = match first {
                "identity" => {
                    let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
                    assert_this_identity(&checker, owner, type_);
                    assert!(!interface(&checker, type_).declared_members_resolved);
                    assert!(!interface(&checker, type_).base_types_resolved);
                    assert_eq!(alias_type(&checker, alias_owner), None);
                    assert_eq!(node_type(&checker, added.1), None);
                    let header = snapshot(&checker, &inputs, &[type_], &[owner, alias_owner]);
                    assert_heritage_artifact_unavailable(&mut checker, written_bases[1], type_);
                    assert_eq!(
                        snapshot(&checker, &inputs, &[type_], &[owner, alias_owner]),
                        header
                    );
                    Some(type_)
                }
                "alias-root" => {
                    let result = checker.get_type_from_type_node(added.1).unwrap();
                    assert!(matches!(
                        checker.store().type_payload(result).unwrap().data(),
                        TypeData::Object(_)
                    ));
                    assert_eq!(node_type(&checker, added.1), Some(result));
                    None
                }
                "consumer" => None,
                _ => unreachable!(),
            };
            assert_owners(&checker);
            checker.check_source_file(CONSUMER).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let derived = checker.get_declared_type_of_symbol(owner).unwrap();
            let base = checker.get_declared_type_of_symbol(base_owner).unwrap();
            let alias_result = checker.get_declared_type_of_symbol(alias_owner).unwrap();
            if let Some(early) = early {
                assert_eq!(derived, early);
            }
            assert_alias_result(&checker, added, added.1, alias_result);
            assert_this_identity(&checker, owner, derived);
            let data = interface(&checker, derived);
            assert!(data.base_types_resolved && data.declared_members_resolved);
            assert_eq!(
                data.resolved_base_types.as_deref(),
                Some([base, alias_result].as_slice())
            );
            let properties = [
                member(&library, interfaces[0], "method").0,
                member(&consumer, interfaces[1], "late").0,
                member(&augmentation, interfaces[2], "added").0,
                root_property.0,
                extra.0,
                optional.0,
            ]
            .map(|node| symbol(&checker, node));
            assert_eq!(
                structured(&checker, derived).properties.as_deref(),
                Some(properties.as_slice())
            );
            assert_eq!(
                property(&checker, derived, "root"),
                symbol(&checker, root_property.0)
            );
            assert_eq!(
                property(&checker, derived, "extra"),
                symbol(&checker, extra.0)
            );
            assert_eq!(property(&checker, alias_result, "extra"), properties[4]);
            assert_eq!(
                checker.store().get_parent_of_symbol(properties[3]),
                Some(base_owner)
            );
            assert_eq!(
                checker.store().get_parent_of_symbol(properties[4]),
                Some(symbol(&checker, added.1))
            );
            assert!(
                checker
                    .store()
                    .symbol(properties[5])
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::OPTIONAL)
            );
            assert!(canonical_has_syntactic_modifier(
                &augmentation.arena,
                extra.0.node,
                SyntaxKind::ReadonlyKeyword
            ));
            assert!(canonical_has_syntactic_modifier(
                &library.arena,
                root_property.0.node,
                SyntaxKind::ReadonlyKeyword
            ));
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected_reads = [bootstrap.number_type, bootstrap.string_type];
            for ((read, expected), property) in reads
                .into_iter()
                .zip(expected_reads)
                .zip([properties[3], properties[4]])
            {
                assert_eq!(checker.get_symbol_at_location(read), Ok(Some(property)));
                assert_eq!(checker.get_type_at_location(read), Ok(expected));
            }
            // The second clause has local slot zero, but its retained merged slot is one.
            assert_heritage_artifact(&mut checker, written_bases[0], base_owner, base);
            assert_heritage_artifact(&mut checker, written_bases[1], alias_owner, alias_result);
            assert_owners(&checker);
            let symbols = [
                owner,
                alias_owner,
                base_owner,
                raw_augmentation,
                raw_namespace,
            ]
            .into_iter()
            .chain(properties)
            .collect::<Vec<_>>();
            let types = [derived, base, alias_result];
            let warm = snapshot(&checker, &inputs, &types, &symbols);
            for _ in 0..2 {
                checker.recheck_source_file(CONSUMER).unwrap();
                assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(derived));
                assert_eq!(
                    checker.get_declared_type_of_symbol(alias_owner),
                    Ok(alias_result)
                );
                assert_eq!(checker.get_type_from_type_node(added.1), Ok(alias_result));
                for (read, expected) in reads.into_iter().zip(expected_reads) {
                    assert_eq!(checker.get_type_at_location(read), Ok(expected));
                }
                assert_heritage_artifact(&mut checker, written_bases[1], alias_owner, alias_result);
                assert_heritage_artifact(&mut checker, written_bases[0], base_owner, base);
                assert_owners(&checker);
                assert_eq!(
                    snapshot(&checker, &inputs, &types, &symbols),
                    warm,
                    "{first}, augmentation_first={augmentation_first}"
                );
            }
        }
    }
}

fn conditional_branches(parsed: &ParseResult, root: NodeRef) -> [NodeRef; 2] {
    let NodeData::ConditionalTypeNode(data) = &parsed.arena.get(root.node).unwrap().data else {
        panic!("the source alias must retain its written conditional root")
    };
    [data.true_type, data.false_type].map(|node| NodeRef::new(root.arena, root.file, node))
}

#[test]
#[allow(clippy::too_many_lines)] // Compare separate source roots that share one canonical empty result.
fn conditional_alias_bases_keep_shared_empty_results_and_distinct_source_roots() {
    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "type EmptyOne = string extends string ? {} : { unusedOne: number };\n",
        "type EmptyTwo = number extends number ? {} : { unusedTwo: string };\n",
        "type Filled = string extends string ? { readonly value: string } : { unused: number };\n",
        "type DirectEmpty = {};\n",
        "interface First extends EmptyOne { first: number; }\n",
        "interface Second extends EmptyTwo { second: number; }\n",
        "interface Third extends Filled { third: number; }\n",
        "interface Fourth extends DirectEmpty { fourth: number; }\n",
        "declare const first: First; declare const second: Second;\n",
        "declare const third: Third; declare const fourth: Fourth;\n",
        "const firstRead: number = first.first; const secondRead: number = second.second;\n",
        "const valueRead: string = third.value; const fourthRead: number = fourth.fourth;\n",
    ));
    let inputs = [input(&parsed, CONSUMER)];
    let aliases = ["EmptyOne", "EmptyTwo", "Filled", "DirectEmpty"]
        .map(|name| alias(&parsed, CONSUMER, name));
    let declarations = ["First", "Second", "Third", "Fourth"]
        .map(|name| declaration(&parsed, CONSUMER, SyntaxKind::InterfaceDeclaration, name));
    let written_bases = ["EmptyOne", "EmptyTwo", "Filled", "DirectEmpty"]
        .into_iter()
        .zip(declarations)
        .map(|(name, owner)| heritage_name(&parsed, owner, name))
        .collect::<Vec<_>>();
    let literals = [
        conditional_branches(&parsed, aliases[0].1)[0],
        conditional_branches(&parsed, aliases[1].1)[0],
        conditional_branches(&parsed, aliases[2].1)[0],
        aliases[3].1,
    ];
    assert_ne!(aliases[0].1, aliases[1].1);
    assert_ne!(literals[0], literals[1]);
    for roots_first in [false, true] {
        let mut checker = context(&inputs);
        let alias_owners = aliases.map(|alias| symbol(&checker, alias.0));
        let owners = declarations.map(|node| symbol(&checker, node));
        assert_ne!(alias_owners[0], alias_owners[1]);
        let early = roots_first
            .then(|| aliases.map(|alias| checker.get_type_from_type_node(alias.1).unwrap()));
        checker.check_source_file(CONSUMER).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let results = alias_owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        let derived = owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        if let Some(early) = early {
            assert_eq!(early, results);
        }
        let empty = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_type_literal_type;
        assert_eq!(results[0], empty);
        assert_eq!(results[1], empty);
        assert_ne!(results[2], empty);
        assert_ne!(results[3], empty);
        for index in 0..aliases.len() {
            assert_alias_result(&checker, aliases[index], literals[index], results[index]);
            assert_this_identity(&checker, owners[index], derived[index]);
            assert_eq!(
                interface(&checker, derived[index])
                    .resolved_base_types
                    .as_deref(),
                Some([results[index]].as_slice())
            );
            assert_heritage_artifact(
                &mut checker,
                written_bases[index],
                alias_owners[index],
                results[index],
            );
        }
        let value = member(&parsed, literals[2], "value");
        let value_symbol = symbol(&checker, value.0);
        assert_eq!(property(&checker, derived[2], "value"), value_symbol);
        assert_eq!(property(&checker, results[2], "value"), value_symbol);
        assert_eq!(
            checker.store().get_parent_of_symbol(value_symbol),
            Some(symbol(&checker, literals[2]))
        );
        assert!(canonical_has_syntactic_modifier(
            &parsed.arena,
            value.0.node,
            SyntaxKind::ReadonlyKeyword
        ));
        let value_read = access(&parsed, "value");
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(checker.get_type_at_location(value_read), Ok(string));
        assert_eq!(
            checker.get_symbol_at_location(value_read),
            Ok(Some(value_symbol))
        );
        let symbols = alias_owners
            .into_iter()
            .chain(owners)
            .chain([value_symbol])
            .collect::<Vec<_>>();
        let types = results.into_iter().chain(derived).collect::<Vec<_>>();
        let warm = snapshot(&checker, &inputs, &types, &symbols);
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            for index in 0..aliases.len() {
                assert_eq!(
                    checker.get_declared_type_of_symbol(owners[index]),
                    Ok(derived[index])
                );
                assert_eq!(
                    checker.get_declared_type_of_symbol(alias_owners[index]),
                    Ok(results[index])
                );
                assert_eq!(
                    checker.get_type_from_type_node(aliases[index].1),
                    Ok(results[index])
                );
                assert_heritage_artifact(
                    &mut checker,
                    written_bases[index],
                    alias_owners[index],
                    results[index],
                );
            }
            assert_eq!(checker.get_type_at_location(value_read), Ok(string));
            assert_eq!(
                snapshot(&checker, &inputs, &types, &symbols),
                warm,
                "roots_first={roots_first}"
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the real global-dependent root and both public demand orders together.
fn global_dependent_alias_heritage_uses_the_queried_conditional_result() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "declare var evidence: number;\n",
        "interface Envelope { own: number; }\n",
        "declare var Envelope: { prototype: Envelope; new(): Envelope; };\n",
    ));
    let augmentation = parse_source_file(concat!(
        "export {};\n",
        "type Choice = typeof globalThis extends { evidence: number } ? { selected: string } : { fallback: boolean };\n",
        "declare global {\n",
        "  interface Envelope extends Choice {}\n",
        "  var Envelope: { prototype: Envelope; new(): Envelope; };\n",
        "}\n",
    ));
    let consumer = parse_source_file(concat!(
        "declare const envelope: Envelope;\n",
        "const selected: string = envelope.selected;\n",
    ));
    let inputs = [
        input(&augmentation, AUGMENTATION),
        input(&library, LIBRARY),
        input(&consumer, CONSUMER),
    ];
    let declared = declaration(
        &library,
        LIBRARY,
        SyntaxKind::InterfaceDeclaration,
        "Envelope",
    );
    let augmented = declaration(
        &augmentation,
        AUGMENTATION,
        SyntaxKind::InterfaceDeclaration,
        "Envelope",
    );
    let written_base = heritage_name(&augmentation, augmented, "Choice");
    let choice = alias(&augmentation, AUGMENTATION, "Choice");
    let [true_branch, false_branch] = conditional_branches(&augmentation, choice.1);
    let selected = member(&augmentation, true_branch, "selected");
    let fallback = member(&augmentation, false_branch, "fallback");
    let evidence = variable_annotation(&library, LIBRARY, "evidence");
    let values = [
        variable_annotation(&library, LIBRARY, "Envelope"),
        variable_annotation(&augmentation, AUGMENTATION, "Envelope"),
    ];
    let selected_read = access(&consumer, "selected");
    for root_first in [false, true] {
        let mut checker = context(&inputs);
        let owner = symbol(&checker, declared);
        let alias_owner = symbol(&checker, choice.0);
        let evidence_owner = symbol(&checker, evidence.0);
        let early = root_first.then(|| checker.get_type_from_type_node(choice.1).unwrap());
        checker.check_source_file(CONSUMER).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let derived = checker.get_declared_type_of_symbol(owner).unwrap();
        let result = checker.get_declared_type_of_symbol(alias_owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, result);
        }
        assert_alias_result(&checker, choice, true_branch, result);
        assert_this_identity(&checker, owner, derived);
        assert_eq!(
            interface(&checker, derived).resolved_base_types.as_deref(),
            Some([result].as_slice())
        );
        let selected_owner = symbol(&checker, selected.0);
        let fallback_owner = symbol(&checker, fallback.0);
        assert_eq!(property(&checker, derived, "selected"), selected_owner);
        assert_eq!(property(&checker, result, "selected"), selected_owner);
        let members = checker
            .store()
            .symbol_table(structured(&checker, derived).members.unwrap())
            .unwrap();
        assert_eq!(members.get_source("fallback"), None);
        assert_ne!(selected_owner, fallback_owner);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        assert_eq!(
            checker
                .store()
                .value_symbol_links(evidence_owner)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert_eq!(
            checker.get_symbol_at_location(selected_read),
            Ok(Some(selected_owner))
        );
        assert_eq!(checker.get_type_at_location(selected_read), Ok(string));
        for (_, annotation) in values {
            assert_eq!(node_type(&checker, annotation), None);
        }
        assert!(
            checker
                .store()
                .value_symbol_links(owner)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert_unchecked(&checker, LIBRARY);
        assert_unchecked(&checker, AUGMENTATION);
        let types = [derived, result];
        let symbols = [
            owner,
            alias_owner,
            evidence_owner,
            selected_owner,
            fallback_owner,
        ];
        // The read-only artifact entry cannot create the current query-local proof.
        let before_artifact = snapshot(&checker, &inputs, &types, &symbols);
        assert_heritage_artifact_unavailable(&mut checker, written_base, derived);
        assert_eq!(
            snapshot(&checker, &inputs, &types, &symbols),
            before_artifact
        );
        let warm = snapshot(&checker, &inputs, &types, &symbols);
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(derived));
            assert_eq!(checker.get_declared_type_of_symbol(alias_owner), Ok(result));
            assert_eq!(checker.get_type_from_type_node(choice.1), Ok(result));
            assert_eq!(checker.get_type_at_location(selected_read), Ok(string));
            assert_heritage_artifact_unavailable(&mut checker, written_base, derived);
            assert_eq!(
                snapshot(&checker, &inputs, &types, &symbols),
                warm,
                "root_first={root_first}"
            );
        }
    }
}

#[test]
fn non_literal_and_generic_alias_bases_keep_the_source_boundary() {
    for (source, name) in [
        (
            "type Base = number; interface Derived extends Base { own: number; }",
            "Base",
        ),
        (
            "type Base<T> = { value: T }; interface Derived extends Base<number> { own: number; }",
            "Base",
        ),
    ] {
        let parsed = parse_source_file(source);
        let inputs = [input(&parsed, CONSUMER)];
        let derived = declaration(
            &parsed,
            CONSUMER,
            SyntaxKind::InterfaceDeclaration,
            "Derived",
        );
        let expression = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(base.expression)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(
                    parsed.arena.id(),
                    CONSUMER,
                    base.expression,
                ))
            })
            .unwrap();
        let mut checker = context(&inputs);
        let owner = symbol(&checker, derived);
        let before = snapshot(&checker, &inputs, &[], &[owner]);
        let expected =
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::UnsupportedSyntax {
                node: expression,
                kind: SyntaxKind::Identifier,
            });
        assert_eq!(checker.get_declared_type_of_symbol(owner), Err(expected));
        assert_eq!(checker.get_declared_type_of_symbol(owner), Err(expected));
        assert_eq!(snapshot(&checker, &inputs, &[], &[owner]), before);
        assert!(
            checker
                .store()
                .declared_type_links(owner)
                .is_none_or(|links| links.declared_type.is_none())
        );
        assert_unchecked(&checker, CONSUMER);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the real proxy and both relation results in one caller path.
fn global_dependent_alias_heritage_keeps_the_inherited_generic_proxy() {
    use ts_binder::CheckFlags;

    let parsed = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "declare var marker: number;\n",
        "interface Generic<T> { value: T; }\n",
        "interface Parent extends Generic<string> {}\n",
        "type Branch = typeof globalThis extends { marker: number } ? {} : {};\n",
        "interface Derived extends Parent, Branch {}\n",
        "type StringTarget = { value: string };\n",
        "type NumberTarget = { value: number };\n",
    ));
    let inputs = [input(&parsed, CONSUMER)];
    let [generic_node, parent_node, derived_node] = ["Generic", "Parent", "Derived"]
        .map(|name| declaration(&parsed, CONSUMER, SyntaxKind::InterfaceDeclaration, name));
    let value_node = member(&parsed, generic_node, "value").0;
    let NodeData::InterfaceDeclaration(generic_source) =
        &parsed.arena.get(generic_node.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter_node] = generic_source
        .type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("Generic has its one written type parameter")
    };
    let parameter_node = NodeRef::new(parsed.arena.id(), CONSUMER, *parameter_node);
    let branch = alias(&parsed, CONSUMER, "Branch");
    let [true_branch, _] = conditional_branches(&parsed, branch.1);
    let string_target = alias(&parsed, CONSUMER, "StringTarget");
    let number_target = alias(&parsed, CONSUMER, "NumberTarget");
    let marker = variable_annotation(&parsed, CONSUMER, "marker");

    for source_first in [false, true] {
        let mut checker = context(&inputs);
        let [generic_owner, parent_owner, derived_owner] =
            [generic_node, parent_node, derived_node].map(|node| symbol(&checker, node));
        let parameter_owner = symbol(&checker, parameter_node);
        let value_owner = symbol(&checker, value_node);
        let branch_owner = symbol(&checker, branch.0);
        let marker_owner = symbol(&checker, marker.0);
        let target_owners = [string_target.0, number_target.0].map(|node| symbol(&checker, node));
        if source_first {
            checker.check_source_file(CONSUMER).unwrap();
        }
        let derived = checker.get_declared_type_of_symbol(derived_owner).unwrap();
        let parent = checker.get_declared_type_of_symbol(parent_owner).unwrap();
        let generic = checker.get_declared_type_of_symbol(generic_owner).unwrap();
        let result = checker.get_declared_type_of_symbol(branch_owner).unwrap();
        let [string_target, number_target] =
            target_owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        assert_eq!(result, bootstrap.empty_type_literal_type);
        assert_alias_result(&checker, branch, true_branch, result);
        assert_this_identity(&checker, derived_owner, derived);
        if !source_first {
            let identity = interface(&checker, derived);
            assert!(!identity.base_types_resolved);
            assert!(!identity.declared_members_resolved);
            assert!(identity.resolved_base_types.is_none());
            assert!(identity.reference.object.structured.members.is_none());
            assert!(identity.reference.object.structured.properties.is_none());
        }
        // The normal relation demand completes the Header before its identity result.
        assert_eq!(checker.is_type_assignable_to(derived, derived), Ok(true));
        assert_eq!(
            interface(&checker, derived).resolved_base_types.as_deref(),
            Some([parent, result].as_slice())
        );
        let [reference] = interface(&checker, parent)
            .resolved_base_types
            .as_deref()
            .unwrap()
        else {
            panic!("Parent retains its actual Generic<string> reference")
        };
        let reference = *reference;
        let TypeData::TypeReference(reference_data) =
            checker.store().type_payload(reference).unwrap().data()
        else {
            panic!("the generic base must retain its canonical reference")
        };
        assert_eq!(reference_data.object.target, Some(generic));
        assert_eq!(
            reference_data.resolved_type_arguments.as_deref(),
            Some([string].as_slice())
        );
        let proxy = property(&checker, derived, "value");
        assert_eq!(property(&checker, parent, "value"), proxy);
        assert_ne!(proxy, value_owner);
        let proxy_record = checker.store().symbol(proxy).unwrap();
        assert!(proxy_record.flags().contains(SymbolFlags::TRANSIENT));
        assert!(
            proxy_record
                .check_flags()
                .contains(CheckFlags::INSTANTIATED)
        );
        assert_eq!(
            checker.store().symbol(value_owner).unwrap().declarations(),
            Some([value_node].as_slice())
        );
        assert_eq!(
            checker.store().symbol(value_owner).unwrap().parent(),
            Some(generic_owner)
        );
        let proxy_links = checker.store().value_symbol_links(proxy).unwrap();
        assert_eq!(proxy_links.target, Some(value_owner));
        assert_eq!(proxy_links.resolved_type, None);
        let mapper = proxy_links.mapper.unwrap();
        let parameter = checker
            .store()
            .declared_type_links(parameter_owner)
            .unwrap()
            .declared_type
            .unwrap();
        let this = interface(&checker, generic).this_type.unwrap();
        assert_eq!(checker.store().map_type(mapper, parameter), Some(string));
        assert_eq!(checker.store().map_type(mapper, this), Some(reference));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(value_owner)
                .unwrap()
                .resolved_type,
            Some(parameter)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(marker_owner)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        if !source_first {
            assert_unchecked(&checker, CONSUMER);
        }

        // Both comparisons must keep Branch's current proof while reading Parent's proxy.
        assert_eq!(
            checker.is_type_assignable_to(derived, string_target),
            Ok(true)
        );
        assert_eq!(
            checker.is_type_assignable_to(derived, number_target),
            Ok(false)
        );
        let resolved_proxy = checker.store().value_symbol_links(proxy).unwrap().clone();
        assert_eq!(resolved_proxy.target, Some(value_owner));
        assert_eq!(resolved_proxy.mapper, Some(mapper));
        assert_eq!(resolved_proxy.resolved_type, Some(string));
        checker.check_source_file(CONSUMER).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );

        let types = [
            derived,
            parent,
            generic,
            result,
            string_target,
            number_target,
        ];
        let owners = [
            generic_owner,
            parent_owner,
            derived_owner,
            parameter_owner,
            value_owner,
            proxy,
            branch_owner,
            marker_owner,
            target_owners[0],
            target_owners[1],
        ];
        let warm = (
            snapshot(&checker, &inputs, &types, &owners),
            checker.store().type_payload(reference).cloned(),
            format!("{:?}", checker.store().mapper_payload(mapper)),
        );
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            assert_eq!(
                checker.get_declared_type_of_symbol(derived_owner),
                Ok(derived)
            );
            assert_eq!(
                checker.get_declared_type_of_symbol(parent_owner),
                Ok(parent)
            );
            assert_eq!(checker.get_type_from_type_node(branch.1), Ok(result));
            assert_eq!(
                checker.is_type_assignable_to(derived, string_target),
                Ok(true)
            );
            assert_eq!(
                checker.is_type_assignable_to(derived, number_target),
                Ok(false)
            );
            assert_eq!(
                checker.store().value_symbol_links(proxy),
                Some(&resolved_proxy)
            );
            assert_eq!(
                (
                    snapshot(&checker, &inputs, &types, &owners),
                    checker.store().type_payload(reference).cloned(),
                    format!("{:?}", checker.store().mapper_payload(mapper)),
                ),
                warm,
                "source_first={source_first}",
            );
        }
    }
}
