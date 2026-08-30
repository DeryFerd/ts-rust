use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ConditionalRootId, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    MembersAndExportsLinks, SourceFileLinks, SymbolNodeLinks, TypeAliasId, TypeAliasLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::{
        ConditionalTypeData, InterfaceTypeData, ObjectTypeData, TupleTypeData, TypeCacheState,
        TypeParameterData, TypeReferenceData,
    },
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(46_240);
const SOURCE: FileId = FileId::new(46_241);
const PROVIDER: FileId = FileId::new(46_242);
const BARREL: FileId = FileId::new(46_243);
const LIBRARY_TEXT: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";
const PROVIDER_TEXT: &str = concat!(
    "export type Box<Value> = { value: Value };\n",
    "export type Bound<Value extends string = string> = { value: Value };\n",
);
const SOURCE_TEXT: &str = concat!(
    "import type { Box, Bound } from './provider';\n",
    "export type Direct<T> = Box<T>;\n",
    "export type Check<T> = Box<T> extends unknown ? T : never;\n",
    "export type Captured<T> = T extends infer Local ? Box<Local> : Box<T>;\n",
    "export type Constrained<T extends string> = Bound<T>;\n",
    "export type Defaulted = Bound;\n",
);
const CONDITIONAL_PROVIDER_TEXT: &str = concat!(
    "export type IsNever<T> = [T] extends [never] ? true : false;\n",
    "export type Empty<Value> = [Value] extends [never] ? true : false;\n",
);
const CONDITIONAL_SOURCE_TEXT: &str = concat!(
    "import type { IsNever, Empty } from './provider';\n",
    "export type NeverCheck<T> = IsNever<T> extends true ? T : never;\n",
    "export type RenamedCheck<T> = Empty<T> extends true ? T : never;\n",
    "export type Captured<T> = T extends infer Local ? Empty<Local> : never;\n",
);

#[derive(Clone, Copy)]
struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    parameter: Option<NodeRef>,
}

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str)],
    resolutions: &[(NodeRef, FileId)],
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
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions.iter().map(
            |&(specifier, target)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            },
        )),
    )
    .unwrap()
}

fn module_specifier(parsed: &ParseResult, file: FileId) -> NodeRef {
    let mut specifiers = parsed.arena.iter().filter_map(|(_, record)| {
        let node = match &record.data {
            NodeData::ImportDeclaration(import) => import.module_specifier,
            NodeData::ExportDeclaration(export) => export.module_specifier?,
            _ => return None,
        };
        Some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let specifier = specifiers.next().expect("the module has one specifier");
    assert!(specifiers.next().is_none());
    specifier
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
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
            let parameter = alias.type_parameters.as_ref().map(|parameters| {
                let [parameter] = parameters.nodes.as_slice() else {
                    panic!("the generic alias has one written parameter");
                };
                NodeRef::new(parsed.arena.id(), file, *parameter)
            });
            Some(Alias {
                declaration: NodeRef::new(parsed.arena.id(), file, node),
                body: NodeRef::new(parsed.arena.id(), file, alias.type_),
                parameter,
            })
        })
        .unwrap_or_else(|| panic!("the source declares type {expected}"))
}

fn import_binding(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(import) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(import.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source imports {expected}"))
}

fn reference_argument(parsed: &ParseResult, reference: NodeRef) -> NodeRef {
    let NodeData::TypeReferenceNode(reference_data) =
        &parsed.arena.get(reference.node).unwrap().data
    else {
        panic!("the request is a written type reference");
    };
    let [argument] = reference_data
        .type_arguments
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("the reference has one written argument");
    };
    NodeRef::new(parsed.arena.id(), reference.file, *argument)
}

fn conditional_nodes(parsed: &ParseResult, alias: Alias) -> [NodeRef; 4] {
    let NodeData::ConditionalTypeNode(conditional) =
        &parsed.arena.get(alias.body.node).unwrap().data
    else {
        panic!("the alias has a written conditional body");
    };
    [
        conditional.check_type,
        conditional.extends_type,
        conditional.true_type,
        conditional.false_type,
    ]
    .map(|node| NodeRef::new(parsed.arena.id(), alias.body.file, node))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .file(node.file)
        .unwrap()
        .1
        .symbol(node)
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<TypeId> {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
}

fn parameter(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> TypeId {
    let owner = symbol(context, declaration);
    let type_ = context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .unwrap();
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    assert!(matches!(
        context.store().type_payload(type_).unwrap().data(),
        TypeData::TypeParameter(_)
    ));
    type_
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_alias(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
    arguments: Option<&[TypeId]>,
) {
    let record = context.store().type_payload(type_).unwrap();
    let alias = context.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(alias.symbol(), Some(owner));
    assert_eq!(alias.type_arguments(), arguments);
}

fn assert_import(context: &CanonicalCheckerContext<'_>, binding: NodeRef, provider: Alias) {
    let imported = symbol(context, binding);
    let target = symbol(context, provider.declaration);
    assert_ne!(imported, target);
    let links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(links.immediate_target, Some(target));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert!(context.store().value_symbol_links(imported).is_none());
    assert!(context.store().value_symbol_links(target).is_none());
}

fn assert_object_instance(
    context: &CanonicalCheckerContext<'_>,
    provider: Alias,
    type_: TypeId,
    argument: TypeId,
    visible_owner: SemanticSymbolId,
    visible_arguments: Option<&[TypeId]>,
) {
    let store = context.store();
    let provider_owner = symbol(context, provider.declaration);
    let links = store.type_alias_links(provider_owner).unwrap();
    let target = links.declared_type.unwrap();
    let provider_parameter = parameter(context, provider.parameter.unwrap());
    assert_eq!(
        links.type_parameters.as_deref(),
        Some([provider_parameter].as_slice())
    );
    assert_alias(context, target, provider_owner, Some(&[provider_parameter]));
    let source_owner = symbol(context, provider.body);
    assert_eq!(
        store.type_payload(target).unwrap().symbol(),
        Some(source_owner)
    );
    let record = store.type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(source_owner));
    assert_alias(context, type_, visible_owner, visible_arguments);
    let TypeData::Object(object) = record.data() else {
        panic!("the imported property alias retains its object instance");
    };
    assert_eq!(object.target, Some(target));
    let substitution = object.mapper.unwrap();
    assert_eq!(
        store.map_type(substitution, provider_parameter),
        Some(argument)
    );
    assert!(object.structured.members.is_none());
    assert!(object.structured.properties.is_none());
    assert_eq!(node_type(context, provider.body), Some(target));
    assert!(
        links
            .instantiations
            .as_ref()
            .unwrap()
            .values()
            .any(|value| *value == type_)
    );
}

fn conditional<'context>(
    context: &'context CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'context ConditionalTypeData {
    let TypeData::Conditional(conditional) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("the generic conditional must retain its deferred identity");
    };
    conditional
}

fn assert_cold_branches(context: &CanonicalCheckerContext<'_>, type_: TypeId) {
    let conditional = conditional(context, type_);
    assert_eq!(conditional.resolved_true_type, None);
    assert_eq!(conditional.resolved_false_type, None);
    assert_eq!(conditional.resolved_inferred_true_type, None);
    assert_eq!(conditional.resolved_default_constraint, None);
    assert_eq!(conditional.resolved_constraint_of_distributive, None);
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    declared: Option<DeclaredTypeLinks>,
    type_alias: Option<TypeAliasLinks>,
    imported: Option<AliasSymbolLinks>,
    value: Option<ValueSymbolLinks>,
    exports: Option<MembersAndExportsLinks>,
}

#[derive(Debug, Eq, PartialEq)]
enum PayloadState {
    Object(Box<ObjectTypeData>),
    Reference(Box<TypeReferenceData>),
    Interface(Box<InterfaceTypeData>),
    Tuple(Box<TupleTypeData>),
    Parameter(Box<TypeParameterData>),
    Conditional(Box<ConditionalTypeData>),
    Other,
}

#[derive(Debug, Eq, PartialEq)]
struct TypeState {
    type_: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    alias_owner: Option<SemanticSymbolId>,
    alias_arguments: Option<Vec<TypeId>>,
    payload: PayloadState,
}

#[derive(Debug, Eq, PartialEq)]
struct RootState {
    root: ConditionalRootId,
    node: NodeRef,
    check: TypeId,
    extends: TypeId,
    distributive: bool,
    infer: Option<Vec<TypeId>>,
    outer: Option<Vec<TypeId>>,
    instantiations: TypeCacheState,
    alias: Option<TypeAliasId>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    types: Vec<TypeState>,
    roots: Vec<RootState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Snapshot the participating public caches as one state.
fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ],
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    NodeState {
                        node,
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                declared: store.declared_type_links(symbol).cloned(),
                type_alias: store.type_alias_links(symbol).cloned(),
                imported: store.alias_symbol_links(symbol).cloned(),
                value: store.value_symbol_links(symbol).cloned(),
                exports: store.members_and_exports_links(symbol).cloned(),
            })
            .collect(),
        types: store
            .types()
            .map(|(type_, record)| {
                let payload = match record.data() {
                    TypeData::Object(data) => PayloadState::Object(Box::new(data.clone())),
                    TypeData::TypeReference(data) => {
                        PayloadState::Reference(Box::new(data.clone()))
                    }
                    TypeData::Interface(data) => PayloadState::Interface(Box::new(data.clone())),
                    TypeData::Tuple(data) => PayloadState::Tuple(Box::new(data.clone())),
                    TypeData::TypeParameter(data) => {
                        PayloadState::Parameter(Box::new(data.clone()))
                    }
                    TypeData::Conditional(data) => {
                        PayloadState::Conditional(Box::new(data.clone()))
                    }
                    _ => PayloadState::Other,
                };
                let alias = record.alias().and_then(|alias| store.type_alias(alias));
                TypeState {
                    type_,
                    flags: record.flags(),
                    object_flags: record.object_flags(),
                    symbol: record.symbol(),
                    alias: record.alias(),
                    alias_owner: alias
                        .and_then(ts_checker::semantic::type_records::TypeAlias::symbol),
                    alias_arguments: alias
                        .and_then(|alias| alias.type_arguments().map(<[TypeId]>::to_vec)),
                    payload,
                }
            })
            .collect(),
        roots: store
            .types()
            .filter_map(|(_, record)| {
                let TypeData::Conditional(conditional) = record.data() else {
                    return None;
                };
                let root = store.conditional_root(conditional.root).unwrap();
                Some(RootState {
                    root: root.id(),
                    node: root.node(),
                    check: root.check_type(),
                    extends: root.extends_type(),
                    distributive: root.is_distributive(),
                    infer: root.infer_type_parameters().map(<[TypeId]>::to_vec),
                    outer: root.outer_type_parameters().map(<[TypeId]>::to_vec),
                    instantiations: root.instantiations().clone(),
                    alias: root.alias(),
                })
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[allow(clippy::too_many_lines)] // Keep source and query order checks together.
fn check_object_alias_order(query_first: bool) {
    let library = parse_source_file(LIBRARY_TEXT);
    let source = parse_source_file(SOURCE_TEXT);
    let provider = parse_source_file(PROVIDER_TEXT);
    let files = [
        (LIBRARY, &library, "\"/project/globals.ts\""),
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &provider, "\"/project/provider.ts\""),
    ];
    let mut context = context(&files, &[(module_specifier(&source, SOURCE), PROVIDER)]);
    let direct = alias(&source, SOURCE, "Direct");
    let check = alias(&source, SOURCE, "Check");
    let captured = alias(&source, SOURCE, "Captured");
    let constrained = alias(&source, SOURCE, "Constrained");
    let defaulted = alias(&source, SOURCE, "Defaulted");
    let provider_box = alias(&provider, PROVIDER, "Box");
    let provider_bound = alias(&provider, PROVIDER, "Bound");
    let box_import = import_binding(&source, SOURCE, "Box");
    let bound_import = import_binding(&source, SOURCE, "Bound");
    let initial = if query_first {
        let result = context.get_type_from_type_node(direct.body).unwrap();
        assert_unchecked(&context, SOURCE);
        assert_unchecked(&context, PROVIDER);
        Some(result)
    } else {
        context.check_source_file(SOURCE).unwrap();
        None
    };
    let aliases = [direct, check, captured, constrained, defaulted];
    let declared = aliases.map(|alias| {
        let owner = symbol(&context, alias.declaration);
        context.get_declared_type_of_symbol(owner).unwrap()
    });
    if let Some(initial) = initial {
        assert_eq!(declared[0], initial);
    }
    for (alias, type_) in aliases.into_iter().zip(declared) {
        assert_eq!(node_type(&context, alias.body), Some(type_));
    }
    let direct_parameter = parameter(&context, direct.parameter.unwrap());
    assert_object_instance(
        &context,
        provider_box,
        declared[0],
        direct_parameter,
        symbol(&context, direct.declaration),
        Some(&[direct_parameter]),
    );
    let check_node = conditional_nodes(&source, check)[0];
    let check_parameter = parameter(&context, check.parameter.unwrap());
    let check_argument = reference_argument(&source, check_node);
    assert_eq!(
        context.get_type_from_type_node(check_argument),
        Ok(check_parameter)
    );
    let check_instance = context.get_type_from_type_node(check_node).unwrap();
    assert_object_instance(
        &context,
        provider_box,
        check_instance,
        check_parameter,
        symbol(&context, provider_box.declaration),
        Some(&[check_parameter]),
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(check_node)
            .unwrap()
            .resolved_symbol,
        Some(symbol(&context, provider_box.declaration)),
    );

    let [_, infer_node, captured_true, captured_false] = conditional_nodes(&source, captured);
    let NodeData::InferTypeNode(infer) = &source.arena.get(infer_node.node).unwrap().data else {
        panic!("the conditional has a real infer declaration");
    };
    let infer_parameter = NodeRef::new(source.arena.id(), SOURCE, infer.type_parameter);
    let local = parameter(&context, infer_parameter);
    let captured_parameter = parameter(&context, captured.parameter.unwrap());
    assert_ne!(local, captured_parameter);
    let captured_data = conditional(&context, declared[2]);
    let root = context
        .store()
        .conditional_root(captured_data.root)
        .unwrap();
    assert_eq!(root.node(), captured.body);
    assert_eq!(
        root.outer_type_parameters(),
        Some([captured_parameter].as_slice())
    );
    assert_eq!(root.infer_type_parameters(), Some([local].as_slice()));
    assert_eq!(captured_data.check_type, captured_parameter);
    assert_eq!(captured_data.extends_type, local);
    assert_alias(
        &context,
        declared[2],
        symbol(&context, captured.declaration),
        Some(&[captured_parameter]),
    );
    assert_cold_branches(&context, declared[2]);
    assert_eq!(node_type(&context, captured_true), None);
    assert_eq!(node_type(&context, captured_false), None);
    let true_argument = reference_argument(&source, captured_true);
    assert_eq!(context.get_type_from_type_node(true_argument), Ok(local));
    let true_instance = context.get_type_from_type_node(captured_true).unwrap();
    assert_object_instance(
        &context,
        provider_box,
        true_instance,
        local,
        symbol(&context, provider_box.declaration),
        Some(&[local]),
    );
    assert_eq!(node_type(&context, captured_false), None);
    assert_cold_branches(&context, declared[2]);
    let false_instance = context.get_type_from_type_node(captured_false).unwrap();
    assert_object_instance(
        &context,
        provider_box,
        false_instance,
        captured_parameter,
        symbol(&context, provider_box.declaration),
        Some(&[captured_parameter]),
    );
    assert_ne!(true_instance, false_instance);
    assert_cold_branches(&context, declared[2]);

    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let constrained_parameter = parameter(&context, constrained.parameter.unwrap());
    let provider_parameter = parameter(&context, provider_bound.parameter.unwrap());
    for parameter in [constrained_parameter, provider_parameter] {
        let TypeData::TypeParameter(data) = context.store().type_payload(parameter).unwrap().data()
        else {
            unreachable!();
        };
        assert_eq!(data.constraint, Some(string));
    }
    assert_object_instance(
        &context,
        provider_bound,
        declared[3],
        constrained_parameter,
        symbol(&context, constrained.declaration),
        Some(&[constrained_parameter]),
    );
    assert_object_instance(
        &context,
        provider_bound,
        declared[4],
        string,
        symbol(&context, defaulted.declaration),
        None,
    );
    assert_import(&context, box_import, provider_box);
    assert_import(&context, bound_import, provider_bound);
    assert_unchecked(&context, PROVIDER);
    context.check_source_file(SOURCE).unwrap();
    assert!(context.diagnostics().is_empty());

    let before = snapshot(&context);
    for _ in 0..2 {
        for (alias, expected) in aliases.into_iter().zip(declared) {
            let owner = symbol(&context, alias.declaration);
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(expected));
            assert_eq!(context.get_type_from_type_node(alias.body), Ok(expected));
        }
        for (node, expected) in [
            (check_node, check_instance),
            (captured_true, true_instance),
            (captured_false, false_instance),
        ] {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(&context), before);
    }
}

#[test]
fn imported_alias_bodies_keep_identity_when_source_is_checked_first() {
    check_object_alias_order(false);
}

#[test]
fn imported_alias_bodies_keep_identity_when_the_rhs_is_queried_first() {
    check_object_alias_order(true);
}

#[test]
fn imported_alias_bodies_rename_the_import_without_changing_provider_identity() {
    for source_first in [false, true] {
        let library = parse_source_file(LIBRARY_TEXT);
        let source = parse_source_file(concat!(
            "import type { Box as RenamedBox } from './provider';\n",
            "export type Visible<T> = RenamedBox<T>;\n",
        ));
        let provider = parse_source_file(PROVIDER_TEXT);
        let files = [
            (LIBRARY, &library, "\"/project/globals.ts\""),
            (SOURCE, &source, "\"/project/source.ts\""),
            (PROVIDER, &provider, "\"/project/provider.ts\""),
        ];
        let mut context = context(&files, &[(module_specifier(&source, SOURCE), PROVIDER)]);
        let visible = alias(&source, SOURCE, "Visible");
        let provider_alias = alias(&provider, PROVIDER, "Box");
        let binding = import_binding(&source, SOURCE, "RenamedBox");
        let NodeData::ImportSpecifier(import) = &source.arena.get(binding.node).unwrap().data
        else {
            unreachable!();
        };
        let NodeData::Identifier(imported_name) = &source
            .arena
            .get(import.property_name.unwrap())
            .unwrap()
            .data
        else {
            unreachable!();
        };
        assert_eq!(imported_name.text, "Box");
        if source_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let instance = context.get_type_from_type_node(visible.body).unwrap();
        let visible_owner = symbol(&context, visible.declaration);
        assert_eq!(
            context.get_declared_type_of_symbol(visible_owner),
            Ok(instance)
        );
        let argument = parameter(&context, visible.parameter.unwrap());
        assert_object_instance(
            &context,
            provider_alias,
            instance,
            argument,
            visible_owner,
            Some(&[argument]),
        );
        assert_import(&context, binding, provider_alias);
        assert_eq!(
            context
                .store()
                .symbol_node_links(visible.body)
                .unwrap()
                .resolved_symbol,
            Some(symbol(&context, provider_alias.declaration)),
        );
        assert_unchecked(&context, PROVIDER);
        if !source_first {
            assert_unchecked(&context, SOURCE);
        }
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let before = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_from_type_node(visible.body), Ok(instance));
            assert_eq!(
                context.get_declared_type_of_symbol(visible_owner),
                Ok(instance)
            );
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(snapshot(&context), before);
        }
    }
}

fn assert_conditional_instance(
    context: &CanonicalCheckerContext<'_>,
    provider: Alias,
    type_: TypeId,
    argument: TypeId,
) -> ConditionalRootId {
    let owner = symbol(context, provider.declaration);
    let links = context.store().type_alias_links(owner).unwrap();
    let target = links.declared_type.unwrap();
    let source_parameter = parameter(context, provider.parameter.unwrap());
    let original = conditional(context, target);
    let instance = conditional(context, type_);
    assert_eq!(instance.root, original.root);
    let root = context.store().conditional_root(instance.root).unwrap();
    assert_eq!(root.node(), provider.body);
    assert_eq!(
        root.outer_type_parameters(),
        Some([source_parameter].as_slice())
    );
    assert!(!root.is_distributive());
    assert_eq!(
        context
            .store()
            .map_type(instance.mapper.unwrap(), source_parameter),
        Some(argument),
    );
    assert_alias(context, target, owner, Some(&[source_parameter]));
    assert_alias(context, type_, owner, Some(&[argument]));
    assert_cold_branches(context, target);
    assert_cold_branches(context, type_);
    instance.root
}

#[test]
#[allow(clippy::too_many_lines)] // Both conditional providers use the same identity checks.
fn imported_alias_bodies_keep_conditional_provider_and_local_capture_identity() {
    for source_first in [false, true] {
        let library = parse_source_file(LIBRARY_TEXT);
        let source = parse_source_file(CONDITIONAL_SOURCE_TEXT);
        let provider = parse_source_file(CONDITIONAL_PROVIDER_TEXT);
        let files = [
            (LIBRARY, &library, "\"/project/globals.ts\""),
            (SOURCE, &source, "\"/project/source.ts\""),
            (PROVIDER, &provider, "\"/project/provider.ts\""),
        ];
        let mut context = context(&files, &[(module_specifier(&source, SOURCE), PROVIDER)]);
        if source_first {
            context.check_source_file(SOURCE).unwrap();
        }
        let mut queried = Vec::new();
        let mut provider_roots = Vec::new();
        for (local_name, imported_name) in [("NeverCheck", "IsNever"), ("RenamedCheck", "Empty")] {
            let local_alias = alias(&source, SOURCE, local_name);
            let provider_alias = alias(&provider, PROVIDER, imported_name);
            let local_owner = symbol(&context, local_alias.declaration);
            let declared = context.get_declared_type_of_symbol(local_owner).unwrap();
            let [reference, _, true_node, false_node] = conditional_nodes(&source, local_alias);
            let argument = parameter(&context, local_alias.parameter.unwrap());
            let imported = context.get_type_from_type_node(reference).unwrap();
            assert_eq!(conditional(&context, declared).check_type, imported);
            assert_alias(&context, declared, local_owner, Some(&[argument]));
            assert_cold_branches(&context, declared);
            assert_eq!(node_type(&context, true_node), None);
            assert_eq!(node_type(&context, false_node), None);
            provider_roots.push(assert_conditional_instance(
                &context,
                provider_alias,
                imported,
                argument,
            ));
            assert_import(
                &context,
                import_binding(&source, SOURCE, imported_name),
                provider_alias,
            );
            queried.push((local_alias, declared, reference, imported));
        }
        assert_ne!(provider_roots[0], provider_roots[1]);

        let captured = alias(&source, SOURCE, "Captured");
        let captured_owner = symbol(&context, captured.declaration);
        let captured_type = context.get_declared_type_of_symbol(captured_owner).unwrap();
        let [_, infer_node, true_node, false_node] = conditional_nodes(&source, captured);
        let NodeData::InferTypeNode(infer) = &source.arena.get(infer_node.node).unwrap().data
        else {
            unreachable!();
        };
        let local = parameter(
            &context,
            NodeRef::new(source.arena.id(), SOURCE, infer.type_parameter),
        );
        let outer = parameter(&context, captured.parameter.unwrap());
        assert_ne!(local, outer);
        assert_cold_branches(&context, captured_type);
        assert_eq!(node_type(&context, true_node), None);
        assert_eq!(node_type(&context, false_node), None);
        let imported_capture = context.get_type_from_type_node(true_node).unwrap();
        assert_eq!(
            assert_conditional_instance(
                &context,
                alias(&provider, PROVIDER, "Empty"),
                imported_capture,
                local,
            ),
            provider_roots[1],
        );
        assert_eq!(node_type(&context, false_node), None);
        assert_cold_branches(&context, captured_type);
        if !source_first {
            assert_unchecked(&context, SOURCE);
        }
        assert_unchecked(&context, PROVIDER);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let before = snapshot(&context);
        for _ in 0..2 {
            for &(local_alias, declared, reference, imported) in &queried {
                let owner = symbol(&context, local_alias.declaration);
                assert_eq!(context.get_declared_type_of_symbol(owner), Ok(declared));
                assert_eq!(context.get_type_from_type_node(reference), Ok(imported));
            }
            assert_eq!(
                context.get_declared_type_of_symbol(captured_owner),
                Ok(captured_type)
            );
            assert_eq!(
                context.get_type_from_type_node(true_node),
                Ok(imported_capture)
            );
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(snapshot(&context), before);
        }
    }
}

#[test]
fn imported_alias_bodies_respect_a_local_parameter_with_the_imported_name() {
    let library = parse_source_file(LIBRARY_TEXT);
    let source = parse_source_file(concat!(
        "import type { Box } from './provider';\n",
        "export type Shadow<Box> = Box;\n",
    ));
    let provider = parse_source_file(PROVIDER_TEXT);
    let files = [
        (LIBRARY, &library, "\"/project/globals.ts\""),
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &provider, "\"/project/provider.ts\""),
    ];
    let mut context = context(&files, &[(module_specifier(&source, SOURCE), PROVIDER)]);
    let shadow = alias(&source, SOURCE, "Shadow");
    let imported = symbol(&context, import_binding(&source, SOURCE, "Box"));
    let local_owner = symbol(&context, shadow.parameter.unwrap());
    let provider_owner = symbol(&context, alias(&provider, PROVIDER, "Box").declaration);
    assert_ne!(imported, local_owner);
    let type_ = context.get_type_from_type_node(shadow.body).unwrap();
    assert_eq!(type_, parameter(&context, shadow.parameter.unwrap()));
    assert_eq!(
        context
            .store()
            .symbol_node_links(shadow.body)
            .unwrap()
            .resolved_symbol,
        Some(local_owner),
    );
    assert!(context.store().alias_symbol_links(imported).is_none());
    assert!(context.store().type_alias_links(provider_owner).is_none());
    let owner = symbol(&context, shadow.declaration);
    assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
    context.check_source_file(SOURCE).unwrap();
    assert!(context.diagnostics().is_empty());
    assert!(context.store().type_alias_links(provider_owner).is_none());
    let before = snapshot(&context);
    for _ in 0..2 {
        assert_eq!(context.get_type_from_type_node(shadow.body), Ok(type_));
        assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(&context), before);
    }
}

fn assert_provider_rejected_without_publication(
    context: &mut CanonicalCheckerContext<'_>,
    use_alias: Alias,
) {
    let before = snapshot(context);
    let owner = symbol(context, use_alias.declaration);
    let node_error = context
        .get_type_from_type_node(use_alias.body)
        .expect_err("an unavailable provider must not yield an imported type");
    assert_eq!(snapshot(context), before);
    let declared_error = context
        .get_declared_type_of_symbol(owner)
        .expect_err("an unavailable provider must not publish the local alias");
    assert_eq!(snapshot(context), before);
    let source_error = context
        .check_source_file(SOURCE)
        .expect_err("an unresolved provider must not mark the source as checked");
    assert_eq!(snapshot(context), before);
    assert_unchecked(context, SOURCE);
    for _ in 0..2 {
        assert_eq!(
            context.get_type_from_type_node(use_alias.body).unwrap_err(),
            node_error
        );
        assert_eq!(
            context.get_declared_type_of_symbol(owner).unwrap_err(),
            declared_error
        );
        assert_eq!(context.check_source_file(SOURCE).unwrap_err(), source_error);
        assert_eq!(snapshot(context), before);
    }
}

#[test]
fn imported_alias_bodies_reject_a_missing_export_without_publication() {
    let library = parse_source_file(LIBRARY_TEXT);
    let source = parse_source_file(concat!(
        "import type { Box } from './provider';\n",
        "export type Use<T> = Box<T>;\n",
    ));
    let provider = parse_source_file("export type Other<T> = { value: T };");
    let files = [
        (LIBRARY, &library, "\"/project/globals.ts\""),
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &provider, "\"/project/provider.ts\""),
    ];
    let mut context = context(&files, &[(module_specifier(&source, SOURCE), PROVIDER)]);
    assert_provider_rejected_without_publication(&mut context, alias(&source, SOURCE, "Use"));
}

#[test]
fn imported_alias_bodies_reject_a_cyclic_export_provider_without_publication() {
    let library = parse_source_file(LIBRARY_TEXT);
    let source = parse_source_file(concat!(
        "import type { Box } from './first';\n",
        "export type Use<T> = Box<T>;\n",
    ));
    let first = parse_source_file("export * from './second';");
    let second = parse_source_file("export * from './first';");
    let files = [
        (LIBRARY, &library, "\"/project/globals.ts\""),
        (SOURCE, &source, "\"/project/source.ts\""),
        (PROVIDER, &first, "\"/project/first.ts\""),
        (BARREL, &second, "\"/project/second.ts\""),
    ];
    let resolutions = [
        (module_specifier(&source, SOURCE), PROVIDER),
        (module_specifier(&first, PROVIDER), BARREL),
        (module_specifier(&second, BARREL), PROVIDER),
    ];
    let mut context = context(&files, &resolutions);
    assert_provider_rejected_without_publication(&mut context, alias(&source, SOURCE, "Use"));
}
