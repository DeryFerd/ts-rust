use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::LiteralValue,
};
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(206_730);

fn context(parsed: &ParseResult, exported: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/merged-type-value.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                if exported {
                    CanonicalModuleState::External
                } else {
                    CanonicalModuleState::Script
                },
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, id)
}

#[derive(Clone, Copy)]
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(data) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(data.name).unwrap().data else {
            return None;
        };
        (name.text == expected).then(|| {
            let declaration = node(parsed, id);
            Variable {
                declaration,
                name: child(parsed, declaration, data.name),
                annotation: data.type_.map(|id| child(parsed, declaration, id)),
                initializer: child(parsed, declaration, data.initializer.unwrap()),
            }
        })
    });
    let result = matches
        .next()
        .unwrap_or_else(|| panic!("missing {expected}"));
    assert!(matches.next().is_none());
    result
}

struct Pair {
    value: Variable,
    alias: NodeRef,
    alias_name: NodeRef,
    body: NodeRef,
    owner: SemanticSymbolId,
    resolved: SemanticSymbolId,
}

fn pair(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, exported: bool) -> Pair {
    let value = variable(parsed, "token");
    let mut aliases = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::TypeAliasDeclaration(data) = &record.data else {
            return None;
        };
        let alias = node(parsed, id);
        Some((
            alias,
            child(parsed, alias, data.name),
            child(parsed, alias, data.type_),
        ))
    });
    let (alias, alias_name, body) = aliases.next().unwrap();
    assert!(aliases.next().is_none());
    let NodeData::Identifier(name) = &parsed.arena.get(alias_name.node).unwrap().data else {
        panic!("the alias keeps its identifier")
    };
    assert_eq!(name.text, "token");
    assert_eq!(
        parsed.arena.get(alias.node).unwrap().parent,
        Some(parsed.source_file)
    );
    let bound = context.file(FILE).unwrap().1;
    let owner = bound.symbol(value.declaration).unwrap();
    assert_eq!(bound.symbol(alias), Some(owner));
    assert_eq!(context.store().get_merged_symbol(owner), Some(owner));
    let local = bound.local_symbol(value.declaration);
    assert_eq!(bound.local_symbol(alias), local);
    assert_eq!(local.is_some(), exported);
    let mut declarations = [value.declaration, alias];
    declarations.sort_by_key(|declaration| parsed.arena.get(declaration.node).unwrap().range.start);
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::TYPE_ALIAS | SymbolFlags::BLOCK_SCOPED_VARIABLE
    );
    assert_eq!(record.name().as_utf8(), Some("token"));
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert_eq!(record.value_declaration(), Some(value.declaration));
    assert_eq!(record.export_symbol(), None);
    let resolved = local.unwrap_or(owner);
    if let Some(local) = local {
        assert_ne!(local, owner);
        let record = context.store().symbol(local).unwrap();
        assert_eq!(record.flags(), SymbolFlags::EXPORT_VALUE);
        assert_eq!(record.declarations(), Some(declarations.as_slice()));
        assert_eq!(record.value_declaration(), None);
        assert_eq!(record.export_symbol(), Some(owner));
    }
    Pair {
        value,
        alias,
        alias_name,
        body,
        owner,
        resolved,
    }
}

fn assert_queries(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    pair: &Pair,
    value_type: TypeId,
    alias_type: TypeId,
) {
    let read = variable(parsed, "read").initializer;
    let annotation = variable(parsed, "typed").annotation.unwrap();
    assert_eq!(
        context.get_type_at_location(pair.value.name),
        Ok(value_type)
    );
    assert_eq!(context.get_type_at_location(read), Ok(value_type));
    assert_eq!(context.get_symbol_at_location(read), Ok(Some(pair.owner)));
    for name in [pair.value.name, pair.alias_name] {
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(pair.owner)));
    }
    assert_eq!(
        context.get_declared_type_of_symbol(pair.owner),
        Ok(alias_type)
    );
    assert_eq!(context.get_type_from_type_node(pair.body), Ok(alias_type));
    assert_eq!(context.get_type_from_type_node(annotation), Ok(alias_type));
    assert_eq!(
        context
            .store()
            .symbol_node_links(read)
            .unwrap()
            .resolved_symbol,
        Some(pair.resolved)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(pair.owner)
            .unwrap()
            .resolved_type,
        Some(value_type)
    );
    assert_eq!(
        context
            .store()
            .type_alias_links(pair.owner)
            .unwrap()
            .declared_type,
        Some(alias_type)
    );
    if let NodeData::TypeQueryNode(query) = &parsed.arena.get(pair.body.node).unwrap().data {
        let name = child(parsed, pair.body, query.expr_name);
        assert_eq!(
            context.get_symbol_at_location(name),
            Ok(Some(pair.resolved))
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(name)
                .unwrap()
                .resolved_symbol,
            Some(pair.resolved)
        );
    }
}

fn state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    pair: &Pair,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        [pair.owner, pair.resolved].map(|symbol| {
            let record = store.symbol(symbol).unwrap();
            (
                symbol,
                record.flags(),
                record.check_flags(),
                record.parent(),
                record.declarations().map(<[_]>::to_vec),
                record.value_declaration(),
                record.export_symbol(),
                store.value_symbol_links(symbol).cloned(),
                store.type_alias_links(symbol).cloned(),
            )
        }),
    )
}

#[derive(Clone, Copy)]
enum Expected {
    TypeofConst,
    StringAndConst,
    StringAndLet,
}

fn check_case(text: &str, exported: bool, expected: Expected) {
    let parsed = parse_source_file(text);
    let mut context = context(&parsed, exported);
    let pair = pair(&context, &parsed, exported);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    if !matches!(expected, Expected::TypeofConst) {
        assert_eq!(
            parsed.arena.get(pair.body.node).unwrap().kind,
            SyntaxKind::StringKeyword
        );
        // The independent alias can be queried before the value is checked.
        assert_eq!(context.get_declared_type_of_symbol(pair.owner), Ok(string));
    }
    context.check_source_file(FILE).unwrap();
    let value_type = context.get_type_at_location(pair.value.name).unwrap();
    match expected {
        Expected::TypeofConst | Expected::StringAndConst => {
            let TypeData::Literal(literal) = context.store().type_payload(value_type).unwrap().data()
            else {
                panic!("the const keeps its written number literal")
            };
            assert_eq!(literal.value, LiteralValue::Number(Number::new(1.0)));
            assert_eq!(context.type_to_string(value_type).unwrap(), "1");
        }
        Expected::StringAndLet => {
            assert_eq!(value_type, number);
            assert_eq!(context.type_to_string(value_type).unwrap(), "number");
        }
    }
    let alias_type = if matches!(expected, Expected::TypeofConst) {
        assert_eq!(
            parsed.arena.get(pair.body.node).unwrap().kind,
            SyntaxKind::TypeQuery
        );
        assert!(context.diagnostics().is_empty());
        value_type
    } else {
        assert_ne!(value_type, string);
        let rejected = variable(&parsed, "rejected");
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the numeric value assigned to the string alias must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(rejected.name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
        let range = parsed.arena.get(rejected.name.node).unwrap().range;
        assert_eq!(
            &text[range.start.get() as usize..range.end.get() as usize],
            "rejected"
        );
        string
    };
    assert_queries(&mut context, &parsed, &pair, value_type, alias_type);
    let before = state(&context, &parsed, &pair);
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        let replayed = self::pair(&context, &parsed, exported);
        assert_eq!(
            (replayed.owner, replayed.resolved, replayed.alias),
            (pair.owner, pair.resolved, pair.alias)
        );
        assert_queries(&mut context, &parsed, &pair, value_type, alias_type);
        assert_eq!(state(&context, &parsed, &pair), before);
    }
}

#[test]
fn exported_value_then_typeof_alias_keeps_both_symbols() {
    check_case(
        concat!(
            "export const token = 1;\n",
            "export type token = typeof token;\n",
            "const read = token;\n",
            "const typed: token = token;\n",
        ),
        true,
        Expected::TypeofConst,
    );
}

#[test]
fn exported_type_before_value_keeps_namespace_types_and_errors() {
    check_case(
        concat!(
            "export type token = string;\n",
            "export const token = 1;\n",
            "const read = token;\n",
            "const typed: token = 'ok';\n",
            "const rejected: token = token;\n",
        ),
        true,
        Expected::StringAndConst,
    );
}

#[test]
fn local_type_and_value_keep_both_declaration_orders() {
    for declarations in [
        "let token: number = 1;\ntype token = string;\n",
        "type token = string;\nlet token: number = 1;\n",
    ] {
        let text = format!(
            "{declarations}const read = token;\nconst typed: token = 'ok';\n\
             const rejected: token = token;\n"
        );
        check_case(&text, false, Expected::StringAndLet);
    }
}
