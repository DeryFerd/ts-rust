use std::collections::HashSet;

use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionLookup,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_options::ModuleKind;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(205_310);
const PROVIDER: FileId = FileId::new(205_311);
const SOURCE: FileId = FileId::new(205_312);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const OPTIONS: &str = "export type CancelOptions = { revert?: boolean; silent?: boolean };\n";

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, id),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn only(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let nodes = nodes(parsed, file, kind);
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
}

fn import_specifier(source: &ParseResult) -> NodeRef {
    let declaration = only(source, SOURCE, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &source.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(source.arena.id(), SOURCE, import.module_specifier)
}

fn context<'a>(
    library: &'a ParseResult,
    provider: &'a ParseResult,
    source: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (PROVIDER, provider, "\"/project/options.ts\""),
        (SOURCE, source, "\"/project/cancelled-error.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            no_implicit_this: true,
            strict_function_types: true,
            strict_property_initialization: true,
            module_kind: ModuleKind::Es2020,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            import_specifier(source),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn union_members(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<TypeId> {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Union(union) => union.union.types.clone(),
        _ => vec![type_],
    }
}

fn assert_optional_flow(
    checker: &CanonicalCheckerContext<'_>,
    constructor: NodeRef,
    super_call: NodeRef,
    conditions: &[NodeRef],
) {
    let graph = checker.file(SOURCE).unwrap().1.flow_graph();
    for &condition in conditions {
        assert_eq!(graph.flow_container(condition), Some(constructor));
    }
    let mut pending = vec![graph.container_return(constructor).unwrap()];
    let mut visited = HashSet::new();
    let mut found = vec![FlowFlags::NONE; conditions.len()];
    let mut found_super = false;
    while let Some(flow) = pending.pop() {
        if !visited.insert(flow) {
            continue;
        }
        let node = graph.nodes().get(flow).unwrap();
        if let Some(FlowNodePayload::Ast(payload)) = node.payload.as_ref() {
            if *payload == super_call && node.flags.contains(FlowFlags::CALL) {
                found_super = true;
            }
            if node.flags.intersects(FlowFlags::CONDITION)
                && let Some(index) = conditions.iter().position(|condition| condition == payload)
            {
                found[index] |= node.flags;
            }
        }
        pending.extend(node.antecedent);
        pending.extend(node.antecedents.iter().copied());
    }
    assert!(
        found_super,
        "the retained constructor flow must include super()"
    );
    for flags in found {
        assert!(flags.contains(FlowFlags::TRUE_CONDITION));
        assert!(flags.contains(FlowFlags::FALSE_CONDITION));
    }
}

fn check_case(invalid: bool) {
    let source_text = format!(
        "import type {{ CancelOptions }} from './options';\n\
         export class CancelledError extends Error {{\n\
           revert?: boolean;\n\
           silent?: boolean;\n\
           constructor(options?: CancelOptions) {{\n\
             super('CancelledError');\n\
             this.revert = options?.revert;\n\
             this.silent = options?.silent;\n\
             {}\n\
           }}\n\
         }}\n",
        if invalid { "this.revert = 'bad';" } else { "" },
    );
    let library = parse_source_file(ES5);
    let provider = parse_source_file(OPTIONS);
    let source = parse_source_file(&source_text);
    let class = only(&source, SOURCE, SyntaxKind::ClassDeclaration);
    let constructor = only(&source, SOURCE, SyntaxKind::Constructor);
    let parameter = only(&source, SOURCE, SyntaxKind::Parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &source.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(
        source.arena.get(parameter.node).unwrap().parent,
        Some(constructor.node)
    );
    assert!(parameter_data.question_token.is_some());
    assert!(parameter_data.initializer.is_none());
    let annotation = NodeRef::new(source.arena.id(), SOURCE, parameter_data.type_.unwrap());
    let parameter_name = NodeRef::new(source.arena.id(), SOURCE, parameter_data.name);
    let fields = nodes(&source, SOURCE, SyntaxKind::PropertyDeclaration);
    assert_eq!(fields.len(), 2);
    let field_annotations = fields
        .iter()
        .map(|field| {
            let NodeData::PropertyDeclaration(property) =
                &source.arena.get(field.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                source.arena.get(field.node).unwrap().parent,
                Some(class.node)
            );
            assert_eq!(
                source
                    .arena
                    .get(property.postfix_token.unwrap())
                    .unwrap()
                    .kind,
                SyntaxKind::QuestionToken
            );
            NodeRef::new(source.arena.id(), SOURCE, property.type_.unwrap())
        })
        .collect::<Vec<_>>();
    let writes = nodes(&source, SOURCE, SyntaxKind::BinaryExpression)
        .into_iter()
        .map(|expression| {
            let NodeData::BinaryExpression(binary) =
                &source.arena.get(expression.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                source.arena.get(binary.operator_token).unwrap().kind,
                SyntaxKind::EqualsToken
            );
            (
                expression,
                NodeRef::new(source.arena.id(), SOURCE, binary.left),
                NodeRef::new(source.arena.id(), SOURCE, binary.right),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(writes.len(), if invalid { 3 } else { 2 });
    let receivers = writes[..2]
        .iter()
        .enumerate()
        .map(|(index, (_, left, right))| {
            let NodeData::PropertyAccessExpression(read) =
                &source.arena.get(right.node).unwrap().data
            else {
                panic!("expected an optional property read")
            };
            assert!(read.question_dot_token.is_some());
            let NodeData::PropertyAccessExpression(write) =
                &source.arena.get(left.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                source.arena.get(write.expression).unwrap().kind,
                SyntaxKind::ThisKeyword
            );
            for name in [read.name, write.name] {
                let NodeData::Identifier(name) = &source.arena.get(name).unwrap().data else {
                    unreachable!()
                };
                assert_eq!(name.text, ["revert", "silent"][index]);
            }
            NodeRef::new(source.arena.id(), SOURCE, read.expression)
        })
        .collect::<Vec<_>>();
    let super_call = only(&source, SOURCE, SyntaxKind::CallExpression);
    let NodeData::CallExpression(call) = &source.arena.get(super_call.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        source.arena.get(call.expression).unwrap().kind,
        SyntaxKind::SuperKeyword
    );

    for members_first in [false, true] {
        let mut checker = context(&library, &provider, &source);
        assert!(checker.global_types().diagnostics().is_empty());
        assert_optional_flow(
            &checker,
            constructor,
            super_call,
            &[receivers[0], writes[0].2, receivers[1], writes[1].2],
        );
        let owner = symbol(&checker, class);
        let early = members_first.then(|| checker.get_nongeneric_class_members(owner).unwrap());
        checker.check_source_file(SOURCE).unwrap();
        let members = checker.get_nongeneric_class_members(owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, members);
        }
        let alias_owner = symbol(
            &checker,
            only(&provider, PROVIDER, SyntaxKind::TypeAliasDeclaration),
        );
        let alias = checker.get_declared_type_of_symbol(alias_owner).unwrap();
        assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), alias);
        let import_owner = symbol(&checker, only(&source, SOURCE, SyntaxKind::ImportSpecifier));
        assert_ne!(import_owner, alias_owner);
        assert_eq!(
            checker
                .store()
                .alias_symbol_links(import_owner)
                .unwrap()
                .alias_target,
            AliasTargetState::Resolved(alias_owner)
        );
        let CanonicalModuleResolutionLookup::Resolved(resolution) =
            checker.module_resolution(import_specifier(&source))
        else {
            panic!("expected the real module resolution")
        };
        assert_eq!(resolution.target_file(), PROVIDER);
        assert_eq!(
            checker.get_module_export_by_name(resolution.target_symbol(), "CancelOptions"),
            Ok(Some(alias_owner))
        );
        let parameter_symbol = symbol(&checker, parameter);
        let parameter_type = checker.get_type_at_location(parameter_name).unwrap();
        let undefined = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let parameter_union = union_members(&checker, parameter_type);
        assert_eq!(parameter_union.len(), 2);
        assert!(parameter_union.contains(&alias));
        assert!(parameter_union.contains(&undefined));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(parameter_symbol)
                .unwrap()
                .resolved_type,
            Some(parameter_type)
        );

        let boolean = checker
            .get_type_from_type_node(field_annotations[0])
            .unwrap();
        assert_eq!(checker.type_to_string(boolean).unwrap(), "boolean");
        assert_eq!(
            checker
                .get_type_from_type_node(field_annotations[1])
                .unwrap(),
            boolean
        );
        let mut expected = union_members(&checker, boolean);
        expected.push(undefined);
        let mut query_nodes = vec![parameter_name];
        for (index, &(expression, left, right)) in writes.iter().enumerate() {
            let field = symbol(&checker, fields[if index == 2 { 0 } else { index }]);
            assert_eq!(checker.get_symbol_at_location(left), Ok(Some(field)));
            let left_type = checker.get_type_at_location(left).unwrap();
            let field_union = union_members(&checker, left_type);
            assert_eq!(field_union.len(), expected.len());
            assert!(expected.iter().all(|type_| field_union.contains(type_)));
            let right_type = checker.get_type_at_location(right).unwrap();
            assert_eq!(checker.get_type_at_location(expression), Ok(right_type));
            if index < 2 {
                let actual = union_members(&checker, right_type);
                assert_eq!(actual.len(), expected.len());
                assert!(expected.iter().all(|type_| actual.contains(type_)));
                assert_eq!(
                    checker.get_symbol_at_location(receivers[index]),
                    Ok(Some(parameter_symbol))
                );
                query_nodes.push(receivers[index]);
            }
            query_nodes.extend([expression, left, right]);
        }
        let selected = checker
            .store()
            .signature_links(super_call)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let declaration = checker
            .store()
            .signature(selected)
            .unwrap()
            .declaration()
            .unwrap();
        assert_eq!(declaration.file, LIBRARY);
        let constructor_signature = checker
            .store()
            .signature_links(constructor)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let signature = checker.store().signature(constructor_signature).unwrap();
        assert_eq!(signature.parameters(), [parameter_symbol]);
        assert_eq!(signature.min_argument_count(), 0);
        assert_eq!(
            signature.resolved_return_type(),
            Some(members.shells().instance_type())
        );
        if invalid {
            let target = checker.get_type_at_location(writes[2].1).unwrap();
            assert_eq!(
                checker.type_to_string(target).unwrap(),
                "boolean | undefined"
            );
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!(
                    "expected one field assignment error: {:?}",
                    checker.diagnostics()
                )
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.node, Some(writes[2].1));
            assert_eq!(
                diagnostic.diagnostic.arguments,
                ["\"bad\"".to_owned(), "boolean | undefined".to_owned()]
            );
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type '\"bad\"' is not assignable to type 'boolean | undefined'."
            );
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        let diagnostics = checker.diagnostics().clone();
        let types = query_nodes
            .iter()
            .map(|&node| checker.get_type_at_location(node).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(checker.diagnostics(), &diagnostics);
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
                    store.type_resolution_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                checker
                    .file_order()
                    .iter()
                    .flat_map(|&file| {
                        let (arena, _) = checker.file(file).unwrap();
                        arena.iter().map(move |(id, _)| {
                            let node = NodeRef::new(arena.id(), file, id);
                            (
                                node,
                                store.type_node_links(node).cloned(),
                                store.signature_links(node).cloned(),
                                store.symbol_node_links(node).cloned(),
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
                            store.alias_symbol_links(symbol).cloned(),
                            store.type_alias_links(symbol).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                checker
                    .file_order()
                    .iter()
                    .map(|&file| {
                        store
                            .source_file_links(checker.source_file(file).unwrap())
                            .cloned()
                    })
                    .collect::<Vec<_>>(),
                checker.diagnostics().clone(),
            )
        };
        let before = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(SOURCE).unwrap();
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(
                checker.get_nongeneric_class_members(owner).unwrap(),
                members
            );
            assert_eq!(
                checker.get_declared_type_of_symbol(alias_owner).unwrap(),
                alias
            );
            assert_eq!(checker.get_type_from_type_node(annotation), Ok(alias));
            assert_eq!(
                checker
                    .store()
                    .signature_links(super_call)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(selected)
            );
            for (&node, &type_) in query_nodes.iter().zip(&types) {
                assert_eq!(checker.get_type_at_location(node), Ok(type_));
            }
            assert_eq!(snapshot(&checker), before);
        }
    }
}

#[test]
fn imported_optional_constructor_options_keep_both_field_reads_and_replay() {
    check_case(false);
}

#[test]
fn imported_optional_constructor_options_keep_the_incompatible_field_error() {
    check_case(true);
}
