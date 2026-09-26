use std::cmp::Ordering;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, TypeData, TypeId,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.d.ts");
const LEGACY_DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts");

const LIBRARY: FileId = FileId::new(203_900);
const DECORATOR_LIBRARY: FileId = FileId::new(203_400);
const LEGACY_LIBRARY: FileId = FileId::new(203_600);
const FIRST: FileId = FileId::new(203_800);
const SECOND: FileId = FileId::new(203_100);
const CONSUMER: FileId = FileId::new(203_200);

const FIRST_PROVIDER: &str = concat!(
    "declare var zeta: number;\n",
    "declare var list: number[];\n",
    "declare var merged: number;\n",
    "declare function uncalled(value: string): string;\n",
    "declare var sleeping: { later: string };\n",
    "interface VisibleShape { value: number; }\n",
    "type TypeOnly = { marker: string };\n",
    "declare const blocked: number;\n",
    "declare let blockedLet: number;\n",
    "declare class BlockedClass {}\n",
    "declare enum BlockedEnum { Item }\n",
    "declare namespace KeptNamespace { const member: number; }\n",
    "declare module 'ambient-provider' { export const member: number; }\n",
);

const SECOND_PROVIDER: &str = "declare var alpha: string;\ndeclare var merged: number;\n";

const MEMBER_QUERIES: &str = concat!(
    "export {};\n",
    "type Whole = typeof globalThis;\n",
    "type Self = typeof globalThis.globalThis;\n",
    "type Undef = typeof globalThis.undefined;\n",
    "type Numeric = typeof globalThis.zeta;\n",
    "type List = typeof globalThis.list;\n",
    "type Shape = globalThis.VisibleShape;\n",
    "const whole = globalThis;\n",
    "const self = globalThis.globalThis;\n",
    "const undef = globalThis.undefined;\n",
    "const numeric = globalThis.zeta;\n",
    "const list = globalThis.list;\n",
);

const SHADOW_QUERIES: &str = concat!(
    "export {};\n",
    "declare const globalThis: { marker: string };\n",
    "type Shadow = typeof globalThis;\n",
    "const shadow = globalThis;\n",
    "const marker = globalThis.marker;\n",
);

const MISSING_QUERIES: &str = concat!(
    "export {};\n",
    "type Blocked = typeof globalThis.blocked;\n",
    "type Absent = typeof globalThis.absent;\n",
    "const blockedRead = globalThis.blocked;\n",
    "const absentRead = globalThis.absent;\n",
);

struct Inputs {
    library: ParseResult,
    decorators: ParseResult,
    legacy: ParseResult,
    first: ParseResult,
    second: ParseResult,
    consumer: ParseResult,
}

struct Source<'a> {
    parsed: &'a ParseResult,
    file: FileId,
    path: &'static str,
    declaration: bool,
    library: bool,
    module: CanonicalModuleState,
}

impl Inputs {
    fn new(consumer: &str) -> Self {
        Self {
            library: parse_source_file(ES5),
            decorators: parse_source_file(DECORATORS),
            legacy: parse_source_file(LEGACY_DECORATORS),
            first: parse_source_file(FIRST_PROVIDER),
            second: parse_source_file(SECOND_PROVIDER),
            consumer: parse_source_file(consumer),
        }
    }

    fn context(&self, reverse: bool, no_implicit_any: bool) -> CanonicalCheckerContext<'_> {
        let mut sources = [
            Source {
                parsed: &self.library,
                file: LIBRARY,
                path: "/lib.es5.d.ts",
                declaration: true,
                library: true,
                module: CanonicalModuleState::Script,
            },
            Source {
                parsed: &self.decorators,
                file: DECORATOR_LIBRARY,
                path: "/lib.decorators.d.ts",
                declaration: true,
                library: true,
                module: CanonicalModuleState::Script,
            },
            Source {
                parsed: &self.legacy,
                file: LEGACY_LIBRARY,
                path: "/lib.decorators.legacy.d.ts",
                declaration: true,
                library: true,
                module: CanonicalModuleState::Script,
            },
            Source {
                parsed: &self.first,
                file: FIRST,
                path: "/first.d.ts",
                declaration: true,
                library: false,
                module: CanonicalModuleState::Script,
            },
            Source {
                parsed: &self.second,
                file: SECOND,
                path: "/second.d.ts",
                declaration: true,
                library: false,
                module: CanonicalModuleState::Script,
            },
            Source {
                parsed: &self.consumer,
                file: CONSUMER,
                path: "/consumer.ts",
                declaration: false,
                library: false,
                module: CanonicalModuleState::External,
            },
        ];
        if reverse {
            sources.swap(3, 4);
        }
        let mut binder = CanonicalBinder::new();
        for source in &sources {
            assert!(source.parsed.diagnostics.is_empty(), "{}", source.path);
            binder
                .bind_source_file_with_facts(
                    &source.parsed.arena,
                    source.parsed.source_file,
                    source.file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(source.path),
                        CanonicalSourceLanguage::TypeScript,
                        source.declaration,
                        source.library,
                        source.module,
                    ),
                )
                .unwrap();
        }
        for source in &sources {
            binder
                .bind_typescript_declaration_slice(&source.parsed.arena, source.file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|source| (source.file, &source.parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_function_types: true,
                strict_bind_call_apply: true,
                no_implicit_any,
                no_emit: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.diagnostics().is_empty());
        assert_eq!(
            context.file_order(),
            sources.iter().map(|source| source.file).collect::<Vec<_>>(),
        );
        context
    }
}

fn named_declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::FunctionDeclaration(data) => data.name?,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source contains {kind:?} {name}"))
}

fn alias_type(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named_declaration(parsed, CONSUMER, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), CONSUMER, data.type_)
}

fn type_query_name(parsed: &ParseResult, name: &str) -> NodeRef {
    let query = alias_type(parsed, name);
    let NodeData::TypeQueryNode(data) = &parsed.arena.get(query.node).unwrap().data else {
        panic!("the alias has a typeof annotation");
    };
    NodeRef::new(parsed.arena.id(), CONSUMER, data.expr_name)
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named_declaration(parsed, CONSUMER, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(parsed.arena.id(), CONSUMER, data.initializer.unwrap())
}

fn property_name(parsed: &ParseResult, access: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(access.node).unwrap().data {
        NodeData::PropertyAccessExpression(data) => data.name,
        NodeData::QualifiedName(data) => data.right,
        _ => panic!("the query uses a named member"),
    };
    NodeRef::new(parsed.arena.id(), access.file, name)
}

fn global(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("the real globals include {name}"))
}

fn canonical(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> SemanticSymbolId {
    context.store().get_merged_symbol(symbol).unwrap()
}

fn rows(
    context: &CanonicalCheckerContext<'_>,
    table: SymbolTableId,
) -> Vec<(EscapedName, SemanticSymbolId)> {
    let mut rows = context
        .store()
        .symbol_table(table)
        .unwrap()
        .iter()
        .map(|(name, symbol)| (name.to_owned(), symbol))
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
    rows
}

fn allocations(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn global_headers(
    context: &CanonicalCheckerContext<'_>,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    rows(context, context.globals())
        .into_iter()
        .map(|(name, original)| {
            let owner = canonical(context, original);
            let headers = [original, owner].map(|symbol| {
                let record = store.symbol(symbol).unwrap();
                (
                    record.flags(),
                    record.check_flags(),
                    record.parent(),
                    record.declarations().map(<[_]>::to_vec),
                    record.value_declaration(),
                    record.members(),
                    record.exports(),
                    record.export_symbol(),
                )
            });
            (name, original, owner, headers)
        })
        .collect::<Vec<_>>()
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let global_type = store
        .type_payload(context.global_types().global_this_value_type)
        .unwrap();
    let TypeData::Object(object) = global_type.data() else {
        panic!("globalThis keeps the bootstrap object");
    };
    (
        allocations(context),
        (
            global_type.flags(),
            global_type.object_flags(),
            global_type.symbol(),
            global_type.alias(),
            object.clone(),
        ),
        rows(context, context.globals()),
        context.diagnostics().clone(),
        store.relation_state_snapshot(),
        context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect::<Vec<_>>(),
        [FIRST, SECOND, CONSUMER]
            .into_iter()
            .flat_map(|file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
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
            .map(|(symbol, record)| {
                (
                    symbol,
                    (
                        record.name().to_owned(),
                        record.flags(),
                        record.check_flags(),
                        record.parent(),
                        record.declarations().map(<[_]>::to_vec),
                        record.value_declaration(),
                        record.members(),
                        record.exports(),
                        record.export_symbol(),
                    ),
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                        store.module_symbol_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn assert_cold_global(context: &CanonicalCheckerContext<'_>) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let symbol = bootstrap.global_this_symbol;
    assert_eq!(global(context, "globalThis"), symbol);
    let owner = store.symbol(symbol).unwrap();
    assert_eq!(owner.flags(), SymbolFlags::MODULE | SymbolFlags::TRANSIENT);
    assert_eq!(owner.check_flags(), CheckFlags::READONLY);
    assert!(owner.declarations().is_none());
    assert!(owner.value_declaration().is_none());
    assert!(owner.parent().is_none());
    assert!(owner.members().is_none());
    assert_eq!(owner.exports(), Some(context.globals()));
    let type_ = context.global_types().global_this_value_type;
    assert_eq!(
        store.value_symbol_links(symbol).unwrap().resolved_type,
        Some(type_),
    );
    let record = store.type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::OBJECT);
    assert_eq!(record.object_flags(), ObjectFlags::ANONYMOUS);
    assert_eq!(record.symbol(), Some(symbol));
    assert!(record.alias().is_none());
    let TypeData::Object(object) = record.data() else {
        unreachable!()
    };
    assert_eq!(object.structured, Default::default());
    assert!(object.target.is_none());
    assert!(object.mapper.is_none());
}

fn is_ambient_module(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> bool {
    let (arena, _) = context.file(declaration.file).unwrap();
    let NodeData::ModuleDeclaration(module) = &arena.get(declaration.node).unwrap().data else {
        return false;
    };
    module.keyword == SyntaxKind::GlobalKeyword
        || arena.get(module.name).unwrap().kind == SyntaxKind::StringLiteral
}

fn compare_members(
    context: &CanonicalCheckerContext<'_>,
    left: SemanticSymbolId,
    right: SemanticSymbolId,
) -> Ordering {
    let store = context.store();
    let left = store.symbol(left).unwrap();
    let right = store.symbol(right).unwrap();
    let first = |declarations: Option<&[NodeRef]>| {
        declarations.and_then(<[_]>::first).map(|node| {
            let file = context
                .file_order()
                .iter()
                .position(|file| *file == node.file)
                .unwrap();
            let (arena, _) = context.file(node.file).unwrap();
            (file, arena.get(node.node).unwrap().range.start.get())
        })
    };
    let order = match (first(left.declarations()), first(right.declarations())) {
        (Some(left), Some(right)) => left.cmp(&right),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    };
    order.then_with(|| left.name().as_bytes().cmp(right.name().as_bytes()))
}

#[allow(clippy::too_many_lines)] // Check the entire table and its distinct ordered value view together.
fn assert_members(
    context: &CanonicalCheckerContext<'_>,
    inputs: &Inputs,
    reverse: bool,
) -> SymbolTableId {
    let store = context.store();
    let record = store
        .type_payload(context.global_types().global_this_value_type)
        .unwrap();
    assert_eq!(
        record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED,
    );
    let TypeData::Object(object) = record.data() else {
        unreachable!()
    };
    let table = object.structured.members.unwrap();
    assert_ne!(table, context.globals());
    assert!(object.structured.signatures.is_none());
    assert_eq!(object.structured.call_signature_count, 0);
    assert!(object.structured.index_infos.is_none());
    let original = rows(context, context.globals());
    let expected = original
        .iter()
        .filter(|(_, symbol)| {
            let record = store.symbol(*symbol).unwrap();
            !record.flags().intersects(
                SymbolFlags::BLOCK_SCOPED_VARIABLE | SymbolFlags::CLASS | SymbolFlags::ENUM,
            ) && !(record.flags().intersects(SymbolFlags::VALUE_MODULE)
                && record.declarations().is_some_and(|declarations| {
                    !declarations.is_empty()
                        && declarations
                            .iter()
                            .all(|declaration| is_ambient_module(context, *declaration))
                }))
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(rows(context, table), expected);
    let mut expected_properties = expected
        .iter()
        .filter_map(|(name, symbol)| {
            let record = store.symbol(*symbol).unwrap();
            assert!(!record.flags().intersects(SymbolFlags::ALIAS));
            let reserved = name.as_ref().is_reserved_member_name();
            (!reserved && record.flags().intersects(SymbolFlags::VALUE)).then_some(*symbol)
        })
        .collect::<Vec<_>>();
    expected_properties.sort_by(|left, right| compare_members(context, *left, *right));
    assert_eq!(
        object.structured.properties.as_deref(),
        Some(expected_properties.as_slice())
    );
    let members = store.symbol_table(table).unwrap();
    for name in [
        "globalThis",
        "undefined",
        "zeta",
        "alpha",
        "list",
        "merged",
        "uncalled",
        "sleeping",
        "KeptNamespace",
    ] {
        assert_eq!(members.get_source(name), Some(global(context, name)));
        assert!(
            expected_properties.contains(&global(context, name)),
            "{name}"
        );
    }
    for name in ["VisibleShape", "TypeOnly"] {
        assert_eq!(members.get_source(name), Some(global(context, name)));
        assert!(!expected_properties.contains(&global(context, name)));
    }
    for name in ["blocked", "blockedLet", "BlockedClass", "BlockedEnum"] {
        assert!(members.get_source(name).is_none());
        assert!(!expected_properties.contains(&global(context, name)));
    }
    let ambient = original
        .iter()
        .find(|(_, symbol)| {
            store
                .symbol(*symbol)
                .unwrap()
                .declarations()
                .is_some_and(|declarations| {
                    declarations.iter().any(|declaration| {
                        declaration.file == FIRST && is_ambient_module(context, *declaration)
                    })
                })
        })
        .unwrap();
    assert!(members.get(ambient.0.as_ref()).is_none());
    let zeta = expected_properties
        .iter()
        .position(|symbol| *symbol == global(context, "zeta"))
        .unwrap();
    let alpha = expected_properties
        .iter()
        .position(|symbol| *symbol == global(context, "alpha"))
        .unwrap();
    assert_eq!(zeta < alpha, !reverse);

    let first = named_declaration(
        &inputs.first,
        FIRST,
        SyntaxKind::VariableDeclaration,
        "merged",
    );
    let second = named_declaration(
        &inputs.second,
        SECOND,
        SyntaxKind::VariableDeclaration,
        "merged",
    );
    let first_owner = context.file(FIRST).unwrap().1.symbol(first).unwrap();
    let second_owner = context.file(SECOND).unwrap().1.symbol(second).unwrap();
    assert_ne!(first_owner, second_owner);
    let owner = canonical(context, global(context, "merged"));
    assert_eq!(canonical(context, first_owner), owner);
    assert_eq!(canonical(context, second_owner), owner);
    let declarations = if reverse {
        [second, first]
    } else {
        [first, second]
    };
    assert_eq!(
        store.symbol(owner).unwrap().declarations(),
        Some(declarations.as_slice())
    );
    assert_eq!(
        store.symbol(owner).unwrap().value_declaration(),
        Some(declarations[0])
    );
    table
}

fn assert_unrelated_values_cold(context: &CanonicalCheckerContext<'_>, inputs: &Inputs) {
    for (parsed, file, name) in [
        (&inputs.first, FIRST, "sleeping"),
        (&inputs.first, FIRST, "merged"),
        (&inputs.second, SECOND, "merged"),
        (&inputs.second, SECOND, "alpha"),
    ] {
        let declaration = named_declaration(parsed, file, SyntaxKind::VariableDeclaration, name);
        let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let annotation = NodeRef::new(parsed.arena.id(), file, data.type_.unwrap());
        assert!(
            context
                .store()
                .type_node_links(annotation)
                .and_then(|links| links.resolved_type)
                .is_none(),
            "{name}"
        );
        let symbol = canonical(context, global(context, name));
        assert!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .is_none(),
            "{name}"
        );
    }
    let function = named_declaration(
        &inputs.first,
        FIRST,
        SyntaxKind::FunctionDeclaration,
        "uncalled",
    );
    assert!(context.store().signature_links(function).is_none());
    for name in ["uncalled", "KeptNamespace"] {
        assert!(
            context
                .store()
                .value_symbol_links(canonical(context, global(context, name)))
                .and_then(|links| links.resolved_type)
                .is_none(),
            "{name}"
        );
    }
    for file in [LIBRARY, DECORATOR_LIBRARY, LEGACY_LIBRARY, FIRST, SECOND] {
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked)
        );
    }
}

fn assert_value_query(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    type_: TypeId,
    symbol: SemanticSymbolId,
) {
    let expression = initializer(parsed, name);
    assert_eq!(context.get_type_at_location(expression), Ok(type_));
    assert_eq!(context.get_symbol_at_location(expression), Ok(Some(symbol)));
    if matches!(
        parsed.arena.get(expression.node).unwrap().data,
        NodeData::PropertyAccessExpression(_)
    ) {
        let property = property_name(parsed, expression);
        assert_eq!(context.get_type_at_location(property), Ok(type_));
        assert_eq!(context.get_symbol_at_location(property), Ok(Some(symbol)));
    }
}

fn assert_type_query(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    type_: TypeId,
    symbol: SemanticSymbolId,
) {
    let annotation = alias_type(parsed, name);
    assert_eq!(context.get_type_from_type_node(annotation), Ok(type_));
    assert_eq!(
        context
            .store()
            .type_node_links(annotation)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(type_query_name(parsed, name))
            .unwrap()
            .resolved_symbol,
        Some(symbol)
    );
}

#[allow(clippy::too_many_lines)] // Keep both query orders on the same complete source and identity assertions.
fn exercise_members(query_first: bool) {
    let inputs = Inputs::new(MEMBER_QUERIES);
    for reverse in [false, true] {
        let mut context = inputs.context(reverse, true);
        assert_cold_global(&context);
        assert_unrelated_values_cold(&context, &inputs);
        let headers = global_headers(&context);
        let whole = context.global_types().global_this_value_type;
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let global_symbol = bootstrap.global_this_symbol;
        let undefined_symbol = bootstrap.undefined_symbol;
        let undefined = bootstrap.undefined_type;
        let number = bootstrap.number_type;
        let numeric_symbol = canonical(&context, global(&context, "zeta"));
        let list_symbol = canonical(&context, global(&context, "list"));
        let shape_symbol = canonical(&context, global(&context, "VisibleShape"));
        if query_first {
            let before = allocations(&context);
            assert_type_query(
                &mut context,
                &inputs.consumer,
                "Whole",
                whole,
                global_symbol,
            );
            assert_eq!(allocations(&context), before);
            assert_cold_global(&context);
            assert!(
                !context
                    .store()
                    .source_file_links(context.source_file(CONSUMER).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
        } else {
            context.check_source_file(CONSUMER).unwrap();
        }
        assert_type_query(&mut context, &inputs.consumer, "Self", whole, global_symbol);
        let table = assert_members(&context, &inputs, reverse);
        assert_eq!(global_headers(&context), headers);
        assert_type_query(
            &mut context,
            &inputs.consumer,
            "Undef",
            undefined,
            undefined_symbol,
        );
        assert_type_query(
            &mut context,
            &inputs.consumer,
            "Numeric",
            number,
            numeric_symbol,
        );
        let list = context
            .get_type_from_type_node(alias_type(&inputs.consumer, "List"))
            .unwrap();
        assert_type_query(&mut context, &inputs.consumer, "List", list, list_symbol);
        let TypeData::TypeReference(array) = context.store().type_payload(list).unwrap().data()
        else {
            panic!("the member retains the real number[] reference");
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some([number].as_slice())
        );
        let shape = context
            .get_type_from_type_node(alias_type(&inputs.consumer, "Shape"))
            .unwrap();
        assert_eq!(context.get_declared_type_of_symbol(shape_symbol), Ok(shape));
        assert_eq!(
            context.store().type_payload(shape).unwrap().symbol(),
            Some(shape_symbol)
        );
        assert_unrelated_values_cold(&context, &inputs);
        context.check_source_file(CONSUMER).unwrap();
        for (name, type_, symbol) in [
            ("whole", whole, global_symbol),
            ("self", whole, global_symbol),
            ("undef", undefined, undefined_symbol),
            ("numeric", number, numeric_symbol),
            ("list", list, list_symbol),
        ] {
            assert_value_query(&mut context, &inputs.consumer, name, type_, symbol);
        }
        assert!(context.diagnostics().is_empty());
        assert_unrelated_values_cold(&context, &inputs);
        assert_eq!(global_headers(&context), headers);
        let warm = snapshot(&context);
        for _ in 0..2 {
            for (name, type_, symbol) in [
                ("Whole", whole, global_symbol),
                ("Self", whole, global_symbol),
                ("Undef", undefined, undefined_symbol),
                ("Numeric", number, numeric_symbol),
                ("List", list, list_symbol),
            ] {
                assert_type_query(&mut context, &inputs.consumer, name, type_, symbol);
            }
            assert_eq!(
                context.get_type_from_type_node(alias_type(&inputs.consumer, "Shape")),
                Ok(shape)
            );
            for (name, type_, symbol) in [
                ("whole", whole, global_symbol),
                ("self", whole, global_symbol),
                ("undef", undefined, undefined_symbol),
                ("numeric", number, numeric_symbol),
                ("list", list, list_symbol),
            ] {
                assert_value_query(&mut context, &inputs.consumer, name, type_, symbol);
            }
            assert_eq!(assert_members(&context, &inputs, reverse), table);
            assert_unrelated_values_cold(&context, &inputs);
            assert_eq!(snapshot(&context), warm);
        }
        context.recheck_source_file(CONSUMER).unwrap();
        assert_eq!(assert_members(&context, &inputs, reverse), table);
        assert_unrelated_values_cold(&context, &inputs);
        assert_eq!(global_headers(&context), headers);
        assert_eq!(snapshot(&context), warm);
    }
}

#[test]
fn global_this_members_keep_complete_order_and_lazy_values_query_first() {
    exercise_members(true);
}

#[test]
fn global_this_members_keep_complete_order_and_lazy_values_source_first() {
    exercise_members(false);
}

#[test]
fn global_this_members_keep_local_shadows_separate() {
    let inputs = Inputs::new(SHADOW_QUERIES);
    for query_first in [false, true] {
        let mut context = inputs.context(false, true);
        let declaration = named_declaration(
            &inputs.consumer,
            CONSUMER,
            SyntaxKind::VariableDeclaration,
            "globalThis",
        );
        let local = context
            .file(CONSUMER)
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        assert_ne!(
            local,
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .global_this_symbol
        );
        assert_cold_global(&context);
        if !query_first {
            context.check_source_file(CONSUMER).unwrap();
        }
        let shadow = context
            .get_type_from_type_node(alias_type(&inputs.consumer, "Shadow"))
            .unwrap();
        assert_ne!(shadow, context.global_types().global_this_value_type);
        assert_type_query(&mut context, &inputs.consumer, "Shadow", shadow, local);
        assert_cold_global(&context);
        context.check_source_file(CONSUMER).unwrap();
        assert_value_query(&mut context, &inputs.consumer, "shadow", shadow, local);
        let marker = initializer(&inputs.consumer, "marker");
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(context.get_type_at_location(marker), Ok(string));
        let property = context.get_symbol_at_location(marker).unwrap().unwrap();
        assert_eq!(
            context.store().symbol(property).unwrap().name().as_utf8(),
            Some("marker")
        );
        assert!(
            context
                .store()
                .symbol(property)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::PROPERTY)
        );
        assert_cold_global(&context);
        assert_unrelated_values_cold(&context, &inputs);
        assert!(context.diagnostics().is_empty());
        let warm = snapshot(&context);
        context.recheck_source_file(CONSUMER).unwrap();
        assert_type_query(&mut context, &inputs.consumer, "Shadow", shadow, local);
        assert_value_query(&mut context, &inputs.consumer, "shadow", shadow, local);
        assert_eq!(context.get_type_at_location(marker), Ok(string));
        assert_eq!(context.get_symbol_at_location(marker), Ok(Some(property)));
        assert_cold_global(&context);
        assert_eq!(snapshot(&context), warm);
    }
}

fn assert_missing_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    no_implicit_any: bool,
) {
    let mut expected = Vec::new();
    for (node, blocked) in [
        (type_query_name(parsed, "Blocked"), true),
        (type_query_name(parsed, "Absent"), false),
        (initializer(parsed, "blockedRead"), true),
        (initializer(parsed, "absentRead"), false),
    ] {
        if blocked || no_implicit_any {
            expected.push((
                property_name(parsed, node),
                if blocked { 2339 } else { 7017 },
            ));
        }
    }
    let actual = context.diagnostics().as_slice();
    assert_eq!(actual.len(), expected.len());
    for (diagnostic, (node, code)) in actual.iter().zip(expected) {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.code(), code);
        let message = if code == 2339 {
            "Property 'blocked' does not exist on type 'typeof globalThis'."
        } else {
            "Element implicitly has an 'any' type because type 'typeof globalThis' has no index signature."
        };
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
        let range = diagnostic.range_override.map_or(
            parsed.arena.get(node.node).unwrap().range,
            CanonicalCheckerDiagnosticRange::range,
        );
        let text = &MISSING_QUERIES[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()];
        assert_eq!(text, if code == 2339 { "blocked" } else { "absent" });
    }
}

#[test]
fn global_this_members_keep_missing_and_blocked_diagnostics_on_replay() {
    let inputs = Inputs::new(MISSING_QUERIES);
    for no_implicit_any in [false, true] {
        for query_first in [false, true] {
            let mut context = inputs.context(false, no_implicit_any);
            let any = context.store().intrinsic_bootstrap().unwrap().any_type;
            let original = rows(&context, context.globals());
            if query_first {
                for name in ["Blocked", "Absent"] {
                    assert_eq!(
                        context.get_type_from_type_node(alias_type(&inputs.consumer, name)),
                        Ok(any)
                    );
                }
            }
            context.check_source_file(CONSUMER).unwrap();
            for name in ["Blocked", "Absent"] {
                assert_eq!(
                    context.get_type_from_type_node(alias_type(&inputs.consumer, name)),
                    Ok(any)
                );
            }
            for name in ["blockedRead", "absentRead"] {
                let access = initializer(&inputs.consumer, name);
                assert_eq!(context.get_type_at_location(access), Ok(any));
                assert_eq!(
                    context.get_type_at_location(property_name(&inputs.consumer, access)),
                    Ok(any)
                );
            }
            assert_missing_diagnostics(&context, &inputs.consumer, no_implicit_any);
            assert_eq!(rows(&context, context.globals()), original);
            assert!(
                context
                    .store()
                    .symbol_table(context.globals())
                    .unwrap()
                    .get_source("absent")
                    .is_none()
            );
            let table = assert_members(&context, &inputs, false);
            assert!(
                context
                    .store()
                    .symbol_table(table)
                    .unwrap()
                    .get_source("blocked")
                    .is_none()
            );
            assert_unrelated_values_cold(&context, &inputs);
            let warm = snapshot(&context);
            context.recheck_source_file(CONSUMER).unwrap();
            for name in ["Blocked", "Absent"] {
                assert_eq!(
                    context.get_type_from_type_node(alias_type(&inputs.consumer, name)),
                    Ok(any)
                );
            }
            for name in ["blockedRead", "absentRead"] {
                assert_eq!(
                    context.get_type_at_location(initializer(&inputs.consumer, name)),
                    Ok(any)
                );
            }
            assert_missing_diagnostics(&context, &inputs.consumer, no_implicit_any);
            assert_eq!(assert_members(&context, &inputs, false), table);
            assert_unrelated_values_cold(&context, &inputs);
            assert_eq!(snapshot(&context), warm);
        }
    }
}
