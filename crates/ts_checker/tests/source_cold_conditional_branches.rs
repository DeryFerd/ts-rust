use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(20_421);

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/project/cold-conditional.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                false,
                CanonicalModuleState::Script,
            ),
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
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn named_declaration(parsed: &ParseResult, name: &str, alias: bool) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let (written_name, annotation) = match &record.data {
                NodeData::TypeAliasDeclaration(data) if alias => (data.name, data.type_),
                NodeData::VariableDeclaration(data) if !alias => (data.name, data.type_?),
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(written_name)?.data else {
                return None;
            };
            (identifier.text == name).then_some((node(parsed, id), node(parsed, annotation)))
        })
        .unwrap_or_else(|| panic!("missing declaration {name}"))
}

#[derive(Clone, Copy)]
struct ConditionalNodes {
    declaration: NodeRef,
    root: NodeRef,
    check: NodeRef,
    when_true: NodeRef,
    when_false: NodeRef,
}

fn conditional(parsed: &ParseResult) -> ConditionalNodes {
    let (declaration, root) = named_declaration(parsed, "Selected", true);
    let NodeData::ConditionalTypeNode(data) = &parsed.arena.get(root.node).unwrap().data else {
        panic!("Selected must own the written conditional")
    };
    for child in [
        data.check_type,
        data.extends_type,
        data.true_type,
        data.false_type,
    ] {
        assert_eq!(parsed.arena.get(child).unwrap().parent, Some(root.node));
    }
    ConditionalNodes {
        declaration,
        root,
        check: node(parsed, data.check_type),
        when_true: node(parsed, data.true_type),
        when_false: node(parsed, data.false_type),
    }
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, source: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(source)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing type for {source:?}"))
}

fn cached_value(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing value type for {symbol:?}"))
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_complete_global_members(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    check: NodeRef,
) {
    let store = context.store();
    let global_type = context.global_types().global_this_value_type;
    assert_eq!(cached_type(context, check), global_type);
    let globals = store.symbol_table(context.globals()).unwrap();
    let global_symbol = globals.get_source("globalThis").unwrap();
    let NodeData::TypeQueryNode(query) = &parsed.arena.get(check.node).unwrap().data else {
        panic!("the check operand must be the real globalThis type query")
    };
    assert_eq!(
        store
            .symbol_node_links(node(parsed, query.expr_name))
            .and_then(|links| links.resolved_symbol),
        Some(global_symbol)
    );
    let record = store.type_payload(global_type).unwrap();
    assert_eq!(record.symbol(), Some(global_symbol));
    assert_eq!(cached_value(context, global_symbol), global_type);
    let TypeData::Object(object) = record.data() else {
        panic!("globalThis must retain its bootstrap object")
    };
    let members = store
        .symbol_table(object.structured.members.unwrap())
        .unwrap();
    // These sources have only var and type-alias declarations. No entry is excluded.
    assert_eq!(members, globals);
    let expected = globals
        .iter()
        .filter_map(|(_, symbol)| {
            store
                .symbol(symbol)
                .unwrap()
                .flags()
                .intersects(SymbolFlags::VALUE)
                .then_some(symbol)
        })
        .collect::<HashSet<_>>();
    let properties = object.structured.properties.as_ref().unwrap();
    assert_eq!(properties.len(), expected.len());
    assert_eq!(properties.iter().copied().collect::<HashSet<_>>(), expected);
    assert!(properties.contains(&global_symbol));
}

fn assert_true_infer_owner(
    parsed: &ParseResult,
    context: &CanonicalCheckerContext<'_>,
    when_true: NodeRef,
) -> TypeId {
    let infer_nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::InferTypeNode(infer) = &record.data else {
                return None;
            };
            Some((node(parsed, id), node(parsed, infer.type_parameter)))
        })
        .collect::<Vec<_>>();
    let [(infer, parameter)] = infer_nodes.as_slice() else {
        panic!("the source must contain one real infer parameter")
    };
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(infer.node)
    );
    let inferred = cached_type(context, *infer);
    assert_eq!(cached_type(context, when_true), inferred);
    let record = context.store().type_payload(inferred).unwrap();
    assert!(matches!(record.data(), TypeData::TypeParameter(_)));
    assert_eq!(record.symbol(), Some(bound_symbol(context, *parameter)));
    inferred
}

#[derive(Debug, Eq, PartialEq)]
struct QuerySnapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    aliases: Vec<(SemanticSymbolId, Option<TypeAliasLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(parsed: &ParseResult, context: &CanonicalCheckerContext<'_>) -> QuerySnapshot {
    let store = context.store();
    let globals = store.symbol_table(context.globals()).unwrap();
    QuerySnapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.conditional_root_len(),
        ],
        types: parsed
            .arena
            .iter()
            .map(|(id, _)| store.type_node_links(node(parsed, id)).cloned())
            .collect(),
        symbols: parsed
            .arena
            .iter()
            .map(|(id, _)| store.symbol_node_links(node(parsed, id)).cloned())
            .collect(),
        values: globals
            .iter()
            .map(|(_, symbol)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        aliases: globals
            .iter()
            .map(|(_, symbol)| (symbol, store.type_alias_links(symbol).cloned()))
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
fn cold_conditional_true_branch_uses_the_real_global_value_and_keeps_import_cold() {
    let parsed = parse_source_file(concat!(
        "declare var ready: number;\n",
        "declare var payload: { code: string };\n",
        "type Selected = typeof globalThis extends { ready: number; payload: infer T } ",
        "? T : import(\"./cold\").Missing;\n",
    ));
    let mut context = context(&parsed);
    let conditional = conditional(&parsed);
    let (payload, annotation) = named_declaration(&parsed, "payload", false);
    let payload_symbol = bound_symbol(&context, payload);
    assert_eq!(
        parsed.arena.get(conditional.when_false.node).unwrap().kind,
        SyntaxKind::ImportType
    );
    assert!(context.store().type_node_links(conditional.root).is_none());
    assert!(
        context
            .store()
            .type_node_links(conditional.when_false)
            .is_none()
    );
    assert!(context.store().value_symbol_links(payload_symbol).is_none());
    let roots = context.store().conditional_root_len();

    let result = context.get_type_from_type_node(conditional.root).unwrap();
    assert_eq!(result, cached_type(&context, annotation));
    assert_eq!(result, cached_value(&context, payload_symbol));
    assert_eq!(
        context.store().type_payload(result).unwrap().symbol(),
        Some(bound_symbol(&context, annotation))
    );
    assert_eq!(context.type_to_string(result).unwrap(), "{ code: string; }");
    assert_ne!(
        assert_true_infer_owner(&parsed, &context, conditional.when_true),
        result
    );
    assert_complete_global_members(&parsed, &context, conditional.check);
    assert_eq!(context.store().conditional_root_len(), roots + 1);
    assert!(
        context
            .store()
            .type_node_links(conditional.when_false)
            .is_none()
    );
    assert!(context.diagnostics().is_empty());
    assert_unchecked(&context);

    let warm = snapshot(&parsed, &context);
    for _ in 0..2 {
        assert_eq!(
            context.get_type_from_type_node(conditional.root).unwrap(),
            result
        );
        assert_complete_global_members(&parsed, &context, conditional.check);
        assert_eq!(snapshot(&parsed, &context), warm);
        assert_unchecked(&context);
    }
}

#[test]
fn cold_conditional_missing_first_member_keeps_the_later_cycle_cold() {
    let parsed = parse_source_file(concat!(
        "declare var cycle: typeof cycle;\n",
        "type Selected = typeof globalThis extends { missing: any; cycle: infer T } ",
        "? T : \"absent\";\n",
    ));
    let mut context = context(&parsed);
    let conditional = conditional(&parsed);
    let (cycle, annotation) = named_declaration(&parsed, "cycle", false);
    let cycle_symbol = bound_symbol(&context, cycle);
    assert!(context.store().type_node_links(annotation).is_none());
    assert!(context.store().value_symbol_links(cycle_symbol).is_none());
    assert!(context.store().type_node_links(conditional.root).is_none());
    let roots = context.store().conditional_root_len();

    let result = context.get_type_from_type_node(conditional.root).unwrap();
    assert_eq!(result, cached_type(&context, conditional.when_false));
    assert_eq!(context.type_to_string(result).unwrap(), "\"absent\"");
    assert_complete_global_members(&parsed, &context, conditional.check);
    let globals = context.store().symbol_table(context.globals()).unwrap();
    assert!(globals.get_source("missing").is_none());
    assert_eq!(globals.get_source("cycle"), Some(cycle_symbol));
    assert!(context.store().type_node_links(annotation).is_none());
    assert!(context.store().value_symbol_links(cycle_symbol).is_none());
    assert!(
        context
            .store()
            .type_node_links(conditional.when_true)
            .is_none()
    );
    assert_eq!(context.store().conditional_root_len(), roots + 1);
    assert!(context.diagnostics().is_empty());
    assert_unchecked(&context);

    let warm = snapshot(&parsed, &context);
    for _ in 0..2 {
        assert_eq!(
            context.get_type_from_type_node(conditional.root).unwrap(),
            result
        );
        assert_eq!(snapshot(&parsed, &context), warm);
        assert_unchecked(&context);
    }
}

#[test]
fn cold_conditional_any_operand_demands_both_source_branches() {
    let parsed =
        parse_source_file("type Selected = any extends { value: infer T } ? \"true\" : \"false\";");
    let mut context = context(&parsed);
    let conditional = conditional(&parsed);
    for branch in [conditional.when_true, conditional.when_false] {
        assert!(context.store().type_node_links(branch).is_none());
    }
    let roots = context.store().conditional_root_len();
    let result = context.get_type_from_type_node(conditional.root).unwrap();
    let when_true = cached_type(&context, conditional.when_true);
    let when_false = cached_type(&context, conditional.when_false);
    assert_ne!(when_true, when_false);
    assert_eq!(context.type_to_string(when_true).unwrap(), "\"true\"");
    assert_eq!(context.type_to_string(when_false).unwrap(), "\"false\"");
    let TypeData::Union(union) = context.store().type_payload(result).unwrap().data() else {
        panic!("any must retain both real branch results")
    };
    assert_eq!(union.union.types.len(), 2);
    assert_eq!(
        union.union.types.iter().copied().collect::<HashSet<_>>(),
        HashSet::from([when_true, when_false])
    );
    assert_eq!(context.store().conditional_root_len(), roots + 1);
    assert!(context.diagnostics().is_empty());
    assert_unchecked(&context);

    let warm = snapshot(&parsed, &context);
    for _ in 0..2 {
        assert_eq!(
            context.get_type_from_type_node(conditional.root).unwrap(),
            result
        );
        assert_eq!(snapshot(&parsed, &context), warm);
    }
}

#[test]
fn cold_conditional_declarations_keep_strict_types_across_query_order() {
    let parsed = parse_source_file(concat!(
        "declare var ready: number;\n",
        "declare var payload: string | undefined;\n",
        "type Selected = typeof globalThis extends { ready: number; payload: infer T } ",
        "? T : never;\n",
        "declare var selected: Selected;\n",
    ));
    let conditional = conditional(&parsed);
    let (payload, annotation) = named_declaration(&parsed, "payload", false);
    let (selected, selected_annotation) = named_declaration(&parsed, "selected", false);
    for source_first in [true, false] {
        let mut context = context(&parsed);
        assert!(context.options().intrinsic.strict_null_checks);
        assert!(context.options().strict_function_types);
        assert!(context.options().no_implicit_any);
        assert!(context.store().type_node_links(conditional.root).is_none());
        if source_first {
            context.check_source_file(FILE).unwrap();
        }
        let result = context.get_type_from_type_node(conditional.root).unwrap();
        if !source_first {
            assert_unchecked(&context);
            context.check_source_file(FILE).unwrap();
        }
        let payload_symbol = bound_symbol(&context, payload);
        let selected_symbol = bound_symbol(&context, selected);
        let alias = bound_symbol(&context, conditional.declaration);
        assert_eq!(result, cached_type(&context, annotation));
        assert_eq!(result, cached_value(&context, payload_symbol));
        assert_eq!(result, cached_type(&context, selected_annotation));
        assert_eq!(result, cached_value(&context, selected_symbol));
        assert_eq!(
            context
                .store()
                .type_alias_links(alias)
                .and_then(|links| links.declared_type),
            Some(result)
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = HashSet::from([bootstrap.string_type, bootstrap.undefined_type]);
        let TypeData::Union(union) = context.store().type_payload(result).unwrap().data() else {
            panic!("strict null checks must preserve the declared undefined member")
        };
        assert_eq!(union.union.types.len(), 2);
        assert_eq!(
            union.union.types.iter().copied().collect::<HashSet<_>>(),
            expected
        );
        assert_ne!(
            assert_true_infer_owner(&parsed, &context, conditional.when_true),
            result
        );
        assert_complete_global_members(&parsed, &context, conditional.check);
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );

        let warm = snapshot(&parsed, &context);
        for _ in 0..2 {
            assert_eq!(
                context.get_type_from_type_node(conditional.root).unwrap(),
                result
            );
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(snapshot(&parsed, &context), warm);
        }
    }
}
