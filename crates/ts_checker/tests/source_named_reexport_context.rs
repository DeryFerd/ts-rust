use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeError, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    SignatureId, SignatureLinks, SourceCheckError, SourceFileLinks, SymbolNodeLinks,
    TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, TypeNodeUnavailable, ValueSymbolLinks,
    alias::{CanonicalAliasResolutionEvent, CanonicalAliasTargetUnavailable},
    type_records::StructuredTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(202_921);
const BARREL: FileId = FileId::new(202_922);
const RELAY: FileId = FileId::new(202_923);
const PROVIDER: FileId = FileId::new(202_924);
const CONTEXT: FileId = FileId::new(202_925);

const PROVIDER_TEXT: &str = concat!(
    "import type { Context } from './context';\n",
    "export interface ConnInfo { remote: { address: string; port: number } }\n",
    "export type GetConnInfo = (c: Context) => ConnInfo;\n",
);
const CONTEXT_TEXT: &str = "export interface Context { address: string; port: number }\n";

type File<'a> = (FileId, &'a ParseResult, &'static str);

#[derive(Clone, Copy)]
enum ExportRoute {
    Direct,
    Named,
    Renamed,
}

struct Inputs {
    source: ParseResult,
    barrel: ParseResult,
    relay: ParseResult,
    provider: ParseResult,
    context: ParseResult,
    entry: FileId,
}

impl Inputs {
    fn new(route: ExportRoute, wrong_port: bool) -> Self {
        let (imported, specifier, entry) = match route {
            ExportRoute::Direct => ("GetConnInfo", "./types", PROVIDER),
            ExportRoute::Named => ("GetConnInfo", "./index", BARREL),
            ExportRoute::Renamed => ("PublicInfo as GetConnInfo", "./renamed", RELAY),
        };
        let port = if wrong_port { "address" } else { "port" };
        let source = parse_source_file(&format!(
            "import type {{ {imported} }} from '{specifier}';\n\
             export const read: GetConnInfo = (c) => ({{\n\
               remote: {{ address: c.address, port: c.{port} }}\n\
             }});\n\
             read({{ address: 'loopback', port: 80 }});\n"
        ));
        let (barrel, relay) = match route {
            ExportRoute::Renamed => (
                "export { type GetConnInfo as ForwardedInfo } from './types';\n",
                "export { ForwardedInfo as PublicInfo } from './index';\n",
            ),
            ExportRoute::Direct | ExportRoute::Named => (
                "export type { GetConnInfo } from './types';\n",
                "export { GetConnInfo as PublicInfo } from './index';\n",
            ),
        };
        Self {
            source,
            barrel: parse_source_file(barrel),
            relay: parse_source_file(relay),
            provider: parse_source_file(PROVIDER_TEXT),
            context: parse_source_file(CONTEXT_TEXT),
            entry,
        }
    }

    fn files(&self) -> [File<'_>; 5] {
        [
            (SOURCE, &self.source, "\"/project/reader.ts\""),
            (BARREL, &self.barrel, "\"/project/index.ts\""),
            (RELAY, &self.relay, "\"/project/renamed.ts\""),
            (PROVIDER, &self.provider, "\"/project/types.ts\""),
            (CONTEXT, &self.context, "\"/project/context.ts\""),
        ]
    }

    fn checker(&self) -> CanonicalCheckerContext<'_> {
        make_context(
            &self.files(),
            &[
                (SOURCE, self.entry),
                (BARREL, PROVIDER),
                (RELAY, BARREL),
                (PROVIDER, CONTEXT),
            ],
        )
    }
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
    let specifier = specifiers.next().expect("the module has one dependency");
    assert!(specifiers.next().is_none());
    specifier
}

fn make_context<'a>(
    files: &[File<'a>],
    routes: &[(FileId, FileId)],
) -> CanonicalCheckerContext<'a> {
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
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = routes.iter().map(|&(source, target)| {
        let (_, parsed, _) = files.iter().find(|(file, _, _)| *file == source).unwrap();
        CanonicalModuleResolutionEntry::resolved(
            module_specifier(parsed, source),
            CanonicalResolvedModuleInput::new(
                target,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
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
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
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
                NodeData::ImportSpecifier(data) => data.name,
                NodeData::ExportSpecifier(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source declares {kind:?} {name}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn module_symbol(checker: &CanonicalCheckerContext<'_>, file: FileId) -> SemanticSymbolId {
    let bound = checker.file(file).unwrap().1;
    symbol(checker, bound.source_file())
}

fn exported(checker: &CanonicalCheckerContext<'_>, file: FileId, name: &str) -> SemanticSymbolId {
    checker
        .get_module_export_by_name(module_symbol(checker, file), name)
        .unwrap()
        .expect("the actual export table has the requested name")
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the checked source symbol has its actual value type")
}

fn members<'a>(checker: &'a CanonicalCheckerContext<'_>, type_: TypeId) -> &'a StructuredTypeData {
    match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        _ => panic!("the source must retain an object or interface type"),
    }
}

fn property_type(checker: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> TypeId {
    let property = members(checker, type_)
        .properties
        .as_ref()
        .unwrap()
        .iter()
        .copied()
        .find(|&property| checker.store().symbol(property).unwrap().name().as_utf8() == Some(name))
        .unwrap_or_else(|| panic!("the canonical type has property {name}"));
    value_type(checker, property)
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let object = members(checker, type_);
    assert_eq!(object.call_signature_count, 1);
    let [signature] = object.signatures.as_deref().unwrap() else {
        panic!("the original function type has one call signature");
    };
    *signature
}

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    arrow: NodeRef,
    callable: TypeId,
    target: TypeId,
    source_signature: SignatureId,
    target_signature: SignatureId,
    parameter: TypeId,
    returned: TypeId,
    target_return: TypeId,
    call: NodeRef,
}

#[allow(clippy::too_many_lines)] // Keep the source and target signature checks together.
fn observe(
    checker: &mut CanonicalCheckerContext<'_>,
    inputs: &Inputs,
    wrong_port: bool,
) -> CallableState {
    let parsed = &inputs.source;
    let node = |id| NodeRef::new(parsed.arena.id(), SOURCE, id);
    let variable = declaration(parsed, SOURCE, SyntaxKind::VariableDeclaration, "read");
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(variable.node).unwrap().data else {
        unreachable!();
    };
    let annotation = node(data.type_.unwrap());
    let arrow_node = node(data.initializer.unwrap());
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(arrow_node.node).unwrap().data else {
        panic!("the original initializer must be an arrow");
    };
    let [parameter_node] = arrow.parameters.nodes.as_slice() else {
        panic!("the arrow has one untyped parameter");
    };
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(*parameter_node).unwrap().data
    else {
        unreachable!();
    };
    assert!(parameter.type_.is_none());
    let parameter_symbol = symbol(checker, node(*parameter_node));
    let context_owner = exported(checker, CONTEXT, "Context");
    let info_owner = exported(checker, PROVIDER, "ConnInfo");
    let alias_owner = exported(checker, PROVIDER, "GetConnInfo");
    let context_type = checker.get_declared_type_of_symbol(context_owner).unwrap();
    let info_type = checker.get_declared_type_of_symbol(info_owner).unwrap();
    let target = checker.get_declared_type_of_symbol(alias_owner).unwrap();
    assert_eq!(
        checker
            .store()
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type),
        Some(target)
    );
    assert_eq!(
        checker
            .store()
            .symbol_node_links(annotation)
            .and_then(|links| links.resolved_symbol),
        Some(alias_owner)
    );
    assert_eq!(
        checker.get_type_at_location(node(parameter.name)),
        Ok(context_type)
    );
    assert_eq!(
        checker.get_symbol_at_location(node(parameter.name)),
        Ok(Some(parameter_symbol))
    );
    assert_eq!(value_type(checker, parameter_symbol), context_type);
    assert_eq!(
        checker.store().type_payload(context_type).unwrap().symbol(),
        Some(context_owner)
    );
    assert_eq!(
        checker.store().type_payload(info_type).unwrap().symbol(),
        Some(info_owner)
    );
    let alias = declaration(
        &inputs.provider,
        PROVIDER,
        SyntaxKind::TypeAliasDeclaration,
        "GetConnInfo",
    );
    let NodeData::TypeAliasDeclaration(alias_data) =
        &inputs.provider.arena.get(alias.node).unwrap().data
    else {
        unreachable!();
    };
    let function = NodeRef::new(inputs.provider.arena.id(), PROVIDER, alias_data.type_);
    let NodeData::FunctionTypeNode(function_data) =
        &inputs.provider.arena.get(function.node).unwrap().data
    else {
        panic!("GetConnInfo keeps its actual function type");
    };
    assert!(function_data.type_parameters.is_none());
    let [formal] = function_data.parameters.nodes.as_slice() else {
        panic!("GetConnInfo keeps its single Context parameter");
    };
    let formal = NodeRef::new(inputs.provider.arena.id(), PROVIDER, *formal);
    let formal_symbol = symbol(checker, formal);
    assert_ne!(formal_symbol, parameter_symbol);
    assert_eq!(checker.get_type_from_type_node(function), Ok(target));
    let target_record = checker.store().type_payload(target).unwrap();
    assert_eq!(target_record.symbol(), Some(symbol(checker, function)));
    assert_eq!(
        checker
            .store()
            .type_alias(target_record.alias().unwrap())
            .unwrap()
            .symbol(),
        Some(alias_owner)
    );
    let callable = checker.get_type_at_location(arrow_node).unwrap();
    assert_ne!(callable, target);
    assert_eq!(value_type(checker, symbol(checker, variable)), target);
    assert_eq!(value_type(checker, symbol(checker, arrow_node)), callable);
    let source_signature = callable_signature(checker, callable);
    let target_signature = callable_signature(checker, target);
    assert_ne!(source_signature, target_signature);
    let returned = checker
        .get_return_type_of_signature(source_signature)
        .unwrap();
    assert_eq!(
        checker.get_return_type_of_signature(target_signature),
        Ok(info_type)
    );
    for (signature, declaration, owner, return_type) in [
        (source_signature, arrow_node, parameter_symbol, returned),
        (target_signature, function, formal_symbol, info_type),
    ] {
        let record = checker.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.parameters(), &[owner]);
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.min_argument_count(), 1);
        assert!(!record.has_rest_parameter());
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        assert_eq!(record.resolved_return_type(), Some(return_type));
        assert_eq!(value_type(checker, owner), context_type);
    }
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    assert_eq!(
        members(checker, context_type)
            .properties
            .as_ref()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(property_type(checker, context_type, "address"), string);
    assert_eq!(property_type(checker, context_type, "port"), number);
    for (type_, port_type) in [
        (info_type, number),
        (returned, if wrong_port { string } else { number }),
    ] {
        assert_eq!(
            members(checker, type_).properties.as_ref().unwrap().len(),
            1
        );
        let remote = property_type(checker, type_, "remote");
        assert_eq!(
            members(checker, remote).properties.as_ref().unwrap().len(),
            2
        );
        assert_eq!(property_type(checker, remote, "address"), string);
        assert_eq!(property_type(checker, remote, "port"), port_type);
    }
    let calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            matches!(record.data, NodeData::CallExpression(_)).then_some(node(id))
        })
        .collect::<Vec<_>>();
    let [call] = calls.as_slice() else {
        panic!("the consumer makes one fresh call");
    };
    assert_eq!(checker.get_type_at_location(*call), Ok(info_type));
    assert_eq!(
        checker
            .store()
            .signature_links(*call)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(target_signature)
    );
    let context_binding = declaration(
        &inputs.provider,
        PROVIDER,
        SyntaxKind::ImportSpecifier,
        "Context",
    );
    let context_alias = symbol(checker, context_binding);
    let links = checker.store().alias_symbol_links(context_alias).unwrap();
    assert_eq!(
        links.alias_target,
        AliasTargetState::Resolved(context_owner)
    );
    assert_eq!(links.type_only_declaration, Some(context_binding));
    assert!(
        links
            .immediate_target
            .is_none_or(|target| target == context_owner)
    );
    assert!(checker.store().value_symbol_links(context_alias).is_none());
    CallableState {
        arrow: arrow_node,
        callable,
        target,
        source_signature,
        target_signature,
        parameter: context_type,
        returned,
        target_return: info_type,
        call: *call,
    }
}

fn assert_import_owner(checker: &CanonicalCheckerContext<'_>, inputs: &Inputs) {
    let binding = declaration(
        &inputs.source,
        SOURCE,
        SyntaxKind::ImportSpecifier,
        "GetConnInfo",
    );
    let alias = symbol(checker, binding);
    let exported_name = if inputs.entry == RELAY {
        "PublicInfo"
    } else {
        "GetConnInfo"
    };
    let immediate = exported(checker, inputs.entry, exported_name);
    let target = exported(checker, PROVIDER, "GetConnInfo");
    let links = checker.store().alias_symbol_links(alias).unwrap();
    assert_eq!(links.immediate_target, Some(immediate));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
    assert!(checker.store().value_symbol_links(alias).is_none());
    assert_eq!(
        checker.store().symbol(target).unwrap().flags(),
        SymbolFlags::TYPE_ALIAS
    );
    if inputs.entry == PROVIDER {
        assert_eq!(immediate, target);
    } else {
        assert_ne!(immediate, target);
        assert_eq!(
            checker.store().symbol(immediate).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        let marker_name = if inputs.entry == RELAY {
            "ForwardedInfo"
        } else {
            "GetConnInfo"
        };
        let marker = declaration(
            &inputs.barrel,
            BARREL,
            SyntaxKind::ExportSpecifier,
            marker_name,
        );
        let marker_alias = symbol(checker, marker);
        let links = checker.store().alias_symbol_links(immediate).unwrap();
        assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
        assert_eq!(links.type_only_declaration, Some(marker));
        if inputs.entry == RELAY {
            assert_ne!(immediate, marker_alias);
            let links = checker.store().alias_symbol_links(marker_alias).unwrap();
            assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
            assert_eq!(links.type_only_declaration, Some(marker));
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolState {
    symbol: SemanticSymbolId,
    alias: Option<AliasSymbolLinks>,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    type_alias: Option<TypeAliasLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, files: &[File<'_>]) -> Snapshot {
    let store = checker.store();
    let mut nodes = Vec::new();
    let mut symbols = Vec::new();
    for &(file, parsed, _) in files {
        let bound = checker.file(file).unwrap().1;
        for (id, _) in parsed.arena.iter() {
            let node = NodeRef::new(parsed.arena.id(), file, id);
            nodes.push(NodeState {
                node,
                type_: store.type_node_links(node).cloned(),
                symbol: store.symbol_node_links(node).cloned(),
                signature: store.signature_links(node).cloned(),
            });
            if let Some(raw) = bound.symbol(node) {
                let symbol = store.get_merged_symbol(raw).unwrap();
                symbols.push(SymbolState {
                    symbol,
                    alias: store.alias_symbol_links(symbol).cloned(),
                    value: store.value_symbol_links(symbol).cloned(),
                    declared: store.declared_type_links(symbol).cloned(),
                    type_alias: store.type_alias_links(symbol).cloned(),
                });
            }
        }
    }
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes,
        symbols,
        sources: files
            .iter()
            .map(|&(file, _, _)| {
                store
                    .source_file_links(checker.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    inputs: &Inputs,
    wrong_port: bool,
    state: &CallableState,
) {
    let warm = snapshot(checker, &inputs.files());
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(SOURCE).unwrap();
        } else {
            checker.check_source_file(SOURCE).unwrap();
        }
        assert_eq!(&observe(checker, inputs, wrong_port), state);
        assert_import_owner(checker, inputs);
        assert_eq!(snapshot(checker, &inputs.files()), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn named_reexport_context_keeps_immediate_and_final_callable_owners() {
    for route in [
        ExportRoute::Direct,
        ExportRoute::Named,
        ExportRoute::Renamed,
    ] {
        for target_first in [false, true] {
            let inputs = Inputs::new(route, false);
            let mut checker = inputs.checker();
            let binding = declaration(
                &inputs.source,
                SOURCE,
                SyntaxKind::ImportSpecifier,
                "GetConnInfo",
            );
            let imported = symbol(&checker, binding);
            let target = exported(&checker, PROVIDER, "GetConnInfo");
            assert!(checker.store().alias_symbol_links(imported).is_none());
            if target_first {
                checker.get_declared_type_of_symbol(target).unwrap();
                let resolved = checker.resolve_alias(imported).unwrap();
                assert_eq!(resolved.target, AliasTargetState::Resolved(target));
                assert!(resolved.events.is_empty());
            }
            checker.check_source_file(SOURCE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            assert_import_owner(&checker, &inputs);
            let state = observe(&mut checker, &inputs, false);
            for file in [BARREL, RELAY, PROVIDER, CONTEXT] {
                assert!(
                    checker
                        .store()
                        .source_file_links(checker.source_file(file).unwrap())
                        .is_none_or(|links| !links.type_checked)
                );
            }
            replay(&mut checker, &inputs, false, &state);
            if inputs.entry != PROVIDER {
                checker.check_source_file(BARREL).unwrap();
                let marker_name = if inputs.entry == RELAY {
                    "ForwardedInfo"
                } else {
                    "GetConnInfo"
                };
                let marker = declaration(
                    &inputs.barrel,
                    BARREL,
                    SyntaxKind::ExportSpecifier,
                    marker_name,
                );
                let marker_alias = symbol(&checker, marker);
                assert_eq!(
                    checker
                        .store()
                        .alias_symbol_links(marker_alias)
                        .unwrap()
                        .immediate_target,
                    Some(target)
                );
                if inputs.entry == RELAY {
                    checker.check_source_file(RELAY).unwrap();
                    let relay = exported(&checker, RELAY, "PublicInfo");
                    assert_eq!(
                        checker
                            .store()
                            .alias_symbol_links(relay)
                            .unwrap()
                            .immediate_target,
                        Some(marker_alias)
                    );
                }
                replay(&mut checker, &inputs, false, &state);
            }
        }
    }
}

#[test]
fn named_reexport_context_reports_the_actual_wrong_return_property() {
    let inputs = Inputs::new(ExportRoute::Renamed, true);
    let mut checker = inputs.checker();
    checker.check_source_file(SOURCE).unwrap();
    let state = observe(&mut checker, &inputs, true);
    assert_import_owner(&checker, &inputs);
    let source_display = checker.type_to_string(state.callable).unwrap();
    let target_display = checker.type_to_string(state.target).unwrap();
    assert!(source_display.contains("port: string"), "{source_display}");
    assert_eq!(target_display, "GetConnInfo");
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!(
            "only the wrong return property must fail: {:?}",
            checker.diagnostics()
        );
    };
    assert_eq!(diagnostic.node, Some(state.arrow));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        format!("Type '{source_display}' is not assignable to type '{target_display}'.")
    );
    assert!(diagnostic.related_information.is_empty());
    replay(&mut checker, &inputs, true, &state);
}

#[test]
fn named_reexport_context_rejects_real_cycles_without_publishing_a_callable() {
    let source = parse_source_file(concat!(
        "import type { GetConnInfo } from './index';\n",
        "export const read: GetConnInfo = (c) => c;\n",
    ));
    let barrel =
        parse_source_file("export type { ForwardedInfo as GetConnInfo } from './renamed';\n");
    let relay = parse_source_file("export type { GetConnInfo as ForwardedInfo } from './index';\n");
    let files = [
        (SOURCE, &source, "\"/project/cycle-reader.ts\""),
        (BARREL, &barrel, "\"/project/cycle-index.ts\""),
        (RELAY, &relay, "\"/project/cycle-renamed.ts\""),
    ];
    let mut checker = make_context(
        &files,
        &[(SOURCE, BARREL), (BARREL, RELAY), (RELAY, BARREL)],
    );
    let binding = declaration(&source, SOURCE, SyntaxKind::ImportSpecifier, "GetConnInfo");
    let imported = symbol(&checker, binding);
    let immediate = exported(&checker, BARREL, "GetConnInfo");
    let forwarded = exported(&checker, RELAY, "ForwardedInfo");
    let variable = declaration(&source, SOURCE, SyntaxKind::VariableDeclaration, "read");
    let variable_symbol = symbol(&checker, variable);
    let expected = SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
        TypeNodeUnavailable::OrdinaryImportTarget {
            node: binding,
            reason: CanonicalAliasTargetUnavailable::InvalidAliasLinks(immediate),
        },
    ));
    assert_eq!(checker.check_source_file(SOURCE), Err(expected));
    for alias in [imported, immediate, forwarded] {
        assert!(checker.store().alias_symbol_links(alias).is_none());
        assert!(checker.store().value_symbol_links(alias).is_none());
    }
    assert!(
        checker
            .store()
            .value_symbol_links(variable_symbol)
            .is_none()
    );
    assert!(checker.diagnostics().is_empty());
    assert!(checker.store().type_resolution_is_empty());
    let cold = snapshot(&checker, &files);
    assert_eq!(checker.check_source_file(SOURCE), Err(expected));
    assert_eq!(snapshot(&checker, &files), cold);
    let resolved = checker.resolve_alias(imported).unwrap();
    assert_eq!(resolved.target, AliasTargetState::Unknown);
    assert!(!resolved.events.is_empty());
    for event in resolved.events {
        assert_eq!(event.diagnostic_code(), 2303);
        let CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias } = event;
        assert!([imported, immediate, forwarded].contains(&alias));
    }
    let warm = snapshot(&checker, &files);
    let repeated = checker.resolve_alias(imported).unwrap();
    assert_eq!(repeated.target, AliasTargetState::Unknown);
    assert!(repeated.events.is_empty());
    assert_eq!(checker.check_source_file(SOURCE), Err(expected));
    assert_eq!(snapshot(&checker, &files), warm);
    assert!(
        checker
            .store()
            .value_symbol_links(variable_symbol)
            .is_none()
    );
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(SOURCE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    assert!(checker.diagnostics().is_empty());
    assert!(checker.store().type_resolution_is_empty());
}

#[test]
#[allow(clippy::too_many_lines)] // Check both parameter owners and their call caches.
fn named_reexport_probe_preserves_ordinary_function_and_arrow_parameters() {
    for (kind, declaration_text) in [
        (
            SyntaxKind::FunctionDeclaration,
            "export function read(value: Label): Label { return value; }\n",
        ),
        (
            SyntaxKind::ArrowFunction,
            "export const read = (value: Label): Label => value;\n",
        ),
    ] {
        let parsed = parse_source_file(&format!(
            "export type Label = string;\n{declaration_text}read('value');\n"
        ));
        let files = [(SOURCE, &parsed, "\"/project/local-parameters.ts\"")];
        let mut checker = make_context(&files, &[]);
        checker.check_source_file(SOURCE).unwrap();
        assert!(checker.diagnostics().is_empty());
        let node = |id| NodeRef::new(parsed.arena.id(), SOURCE, id);
        let (owner_node, parameters, return_annotation) = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                if record.kind != kind {
                    return None;
                }
                match &record.data {
                    NodeData::FunctionDeclaration(function) => {
                        Some((node(id), &function.parameters, function.type_))
                    }
                    NodeData::ArrowFunction(function) => {
                        Some((node(id), &function.parameters, function.type_))
                    }
                    _ => None,
                }
            })
            .unwrap();
        let [parameter_node] = parameters.nodes.as_slice() else {
            panic!("the existing callable has one parameter");
        };
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(*parameter_node).unwrap().data
        else {
            unreachable!();
        };
        assert_eq!(
            parsed.arena.get(*parameter_node).unwrap().parent,
            Some(owner_node.node)
        );
        let parameter_type = node(parameter.type_.unwrap());
        assert_eq!(
            parsed.arena.get(parameter_type.node).unwrap().kind,
            SyntaxKind::TypeReference
        );
        let parameter_owner = symbol(&checker, node(*parameter_node));
        let callable = value_type(&checker, symbol(&checker, owner_node));
        let signature = callable_signature(&checker, callable);
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            checker.get_declared_type_of_symbol(exported(&checker, SOURCE, "Label")),
            Ok(string)
        );
        assert_eq!(checker.get_type_from_type_node(parameter_type), Ok(string));
        assert_eq!(
            checker.get_type_from_type_node(node(return_annotation.unwrap())),
            Ok(string)
        );
        assert_eq!(
            checker.get_type_at_location(node(parameter.name)),
            Ok(string)
        );
        assert_eq!(value_type(&checker, parameter_owner), string);
        assert_eq!(checker.get_return_type_of_signature(signature), Ok(string));
        let record = checker.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(owner_node));
        assert_eq!(record.parameters(), &[parameter_owner]);
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.min_argument_count(), 1);
        let call = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                matches!(record.data, NodeData::CallExpression(_)).then_some(node(id))
            })
            .unwrap();
        assert_eq!(checker.get_type_at_location(call), Ok(string));
        assert_eq!(
            checker
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
        let warm = snapshot(&checker, &files);
        for recheck in [false, true] {
            if recheck {
                checker.recheck_source_file(SOURCE).unwrap();
            } else {
                checker.check_source_file(SOURCE).unwrap();
            }
            assert_eq!(checker.get_type_from_type_node(parameter_type), Ok(string));
            assert_eq!(checker.get_type_at_location(call), Ok(string));
            assert_eq!(snapshot(&checker, &files), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}
