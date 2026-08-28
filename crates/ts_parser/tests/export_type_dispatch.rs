use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

#[test]
fn exported_as_recovers_as_a_type_only_export() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for (source, start, end) in [
            ("export type as<T> = T;", 12, 14),
            ("export type as = number;", 12, 14),
            ("export type /* name */ as<T> = T;", 23, 25),
            ("export /* declaration */ type as<T> = T;", 30, 32),
            (r"export type \u0061s<T> = T;", 12, 19),
            (r"export type \u{61}s<T> = T;", 12, 19),
            ("export type as", 12, 14),
            ("export type as;", 12, 14),
            ("export\ntype as<T> = T;", 12, 14),
            ("export type as\n<T> = T;", 12, 14),
        ] {
            let result = parse(source);
            assert_eq!(
                diagnostics(&result),
                [(1005, start, end, "'{' expected.")],
                "{source}"
            );
            let statements = source_statements(&result);
            assert_eq!(
                statement_kinds(&result, statements),
                [
                    SyntaxKind::ExportDeclaration,
                    SyntaxKind::ExpressionStatement
                ],
                "{source}"
            );
            assert_missing_type_export(&result, statements[0]);
        }
    }
}

#[test]
fn exported_as_recovery_keeps_the_following_alias() {
    let source = "export type as<T> = T; export type infer<T> = T;";
    for parse in [parse_source_file, parse_jsx_source_file] {
        let result = parse(source);
        assert_eq!(diagnostics(&result), [(1005, 12, 14, "'{' expected.")]);
        let statements = source_statements(&result);
        assert_eq!(
            statement_kinds(&result, statements),
            [
                SyntaxKind::ExportDeclaration,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::TypeAliasDeclaration,
            ]
        );
        assert_missing_type_export(&result, statements[0]);
        let NodeData::TypeAliasDeclaration(alias) = &result.arena.get(statements[2]).unwrap().data
        else {
            panic!("expected the following alias");
        };
        assert_eq!(identifier_text(&result, alias.name), "infer");
        assert!(alias.modifiers.is_some());
    }
}

#[test]
fn exported_as_recovers_inside_a_namespace() {
    let source = "namespace N { export type as<T> = T; type After = number; }";
    for parse in [parse_source_file, parse_jsx_source_file] {
        let result = parse(source);
        assert_eq!(diagnostics(&result), [(1005, 26, 28, "'{' expected.")]);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::ModuleDeclaration(module) = &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected namespace");
        };
        let NodeData::ModuleBlock(block) = &result.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected namespace body");
        };
        assert_eq!(
            statement_kinds(&result, &block.statements.nodes),
            [
                SyntaxKind::ExportDeclaration,
                SyntaxKind::ExpressionStatement,
                SyntaxKind::TypeAliasDeclaration,
            ]
        );
        assert_missing_type_export(&result, block.statements.nodes[0]);
        let NodeData::TypeAliasDeclaration(alias) =
            &result.arena.get(block.statements.nodes[2]).unwrap().data
        else {
            panic!("expected the following alias");
        };
        assert_eq!(identifier_text(&result, alias.name), "After");
    }
}

#[test]
fn a_line_break_after_export_type_keeps_expression_recovery() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for source in ["export type\nas<T> = T;", "export type /*\n*/ as<T> = T;"] {
            let result = parse(source);
            assert_eq!(
                diagnostics(&result),
                [(1128, 0, 6, "Declaration or statement expected.")],
                "{source}"
            );
            let statements = source_statements(&result);
            assert_eq!(
                statement_kinds(&result, statements),
                [
                    SyntaxKind::ExpressionStatement,
                    SyntaxKind::ExpressionStatement
                ],
                "{source}"
            );
            let NodeData::ExpressionStatement(first) =
                &result.arena.get(statements[0]).unwrap().data
            else {
                panic!("expected type expression");
            };
            assert_eq!(identifier_text(&result, first.expression), "type");
        }
    }
}

#[test]
fn contextual_type_aliases_keep_the_export_modifier() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for name in [
            "infer",
            "keyof",
            "readonly",
            "type",
            "satisfies",
            "asserts",
            "implements",
            "interface",
        ] {
            let source = format!("export type {name}<T> = T;");
            let result = parse(&source);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let statements = source_statements(&result);
            assert_eq!(statements.len(), 1, "{source}");
            let NodeData::TypeAliasDeclaration(alias) =
                &result.arena.get(statements[0]).unwrap().data
            else {
                panic!("expected alias for {source}");
            };
            assert_eq!(identifier_text(&result, alias.name), name);
            assert_eq!(
                statement_kinds(&result, &alias.modifiers.as_ref().unwrap().list.nodes),
                [SyntaxKind::ExportKeyword],
                "{source}"
            );
        }
    }
}

#[test]
fn plain_and_declared_as_aliases_remain_aliases() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for (source, modifiers) in [
            ("type as<T> = T;", &[][..]),
            (
                "export declare type as<T> = T;",
                &[SyntaxKind::ExportKeyword, SyntaxKind::DeclareKeyword][..],
            ),
        ] {
            let result = parse(source);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let statements = source_statements(&result);
            assert_eq!(statements.len(), 1, "{source}");
            let NodeData::TypeAliasDeclaration(alias) =
                &result.arena.get(statements[0]).unwrap().data
            else {
                panic!("expected alias for {source}");
            };
            assert_eq!(identifier_text(&result, alias.name), "as");
            let actual = alias.modifiers.as_ref().map_or_else(Vec::new, |modifiers| {
                statement_kinds(&result, &modifiers.list.nodes)
            });
            assert_eq!(actual, modifiers, "{source}");
        }
    }
}

#[test]
fn type_only_clauses_and_namespace_exports_keep_their_routes() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for (source, clause_kind) in [
            ("export type { as } from \"pkg\";", SyntaxKind::NamedExports),
            (
                "export type\n{ as } from \"pkg\";",
                SyntaxKind::NamedExports,
            ),
            (
                "export type * as as from \"pkg\";",
                SyntaxKind::NamespaceExport,
            ),
            (
                "export type\n* as as from \"pkg\";",
                SyntaxKind::NamespaceExport,
            ),
        ] {
            let result = parse(source);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let statements = source_statements(&result);
            assert_eq!(statements.len(), 1, "{source}");
            let NodeData::ExportDeclaration(declaration) =
                &result.arena.get(statements[0]).unwrap().data
            else {
                panic!("expected type-only export");
            };
            assert!(declaration.is_type_only);
            assert!(declaration.module_specifier.is_some());
            assert_eq!(
                result
                    .arena
                    .get(declaration.export_clause.unwrap())
                    .unwrap()
                    .kind,
                clause_kind
            );
        }
        let result = parse("export as namespace Library;");
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let NodeData::NamespaceExportDeclaration(declaration) =
            &result.arena.get(statements[0]).unwrap().data
        else {
            panic!("expected namespace export declaration");
        };
        assert_eq!(identifier_text(&result, declaration.name), "Library");
    }
}

#[test]
fn line_broken_cast_keywords_start_new_statements() {
    for parse in [parse_source_file, parse_jsx_source_file] {
        for (keyword, cast_kind) in [
            ("as", SyntaxKind::AsExpression),
            ("satisfies", SyntaxKind::SatisfiesExpression),
        ] {
            let source = format!("const value = source\n{keyword}(Target);");
            let result = parse(&source);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let statements = source_statements(&result);
            assert_eq!(
                statement_kinds(&result, statements),
                [
                    SyntaxKind::VariableStatement,
                    SyntaxKind::ExpressionStatement
                ],
                "{source}"
            );
            let NodeData::ExpressionStatement(statement) =
                &result.arena.get(statements[1]).unwrap().data
            else {
                panic!("expected call statement");
            };
            let NodeData::CallExpression(call) =
                &result.arena.get(statement.expression).unwrap().data
            else {
                panic!("expected keyword call");
            };
            assert_eq!(identifier_text(&result, call.expression), keyword);
            let source = format!("const value = source {keyword}\nTarget;");
            let result = parse(&source);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            assert_eq!(source_statements(&result).len(), 1, "{source}");
            assert!(
                result.arena.iter().any(|(_, node)| node.kind == cast_kind),
                "{source}"
            );
        }
    }
}

fn diagnostics(result: &ParseResult) -> Vec<(u32, u32, u32, &str)> {
    result
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.code.expect("expected catalog diagnostic"),
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
                diagnostic.message.as_str(),
            )
        })
        .collect()
}

fn source_statements(result: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(source) = &result.arena.get(result.source_file).unwrap().data else {
        panic!("expected source file");
    };
    &source.statements.nodes
}

fn statement_kinds(result: &ParseResult, nodes: &[NodeId]) -> Vec<SyntaxKind> {
    nodes
        .iter()
        .map(|node| result.arena.get(*node).unwrap().kind)
        .collect()
}

fn identifier_text(result: &ParseResult, identifier: NodeId) -> &str {
    let NodeData::Identifier(identifier) = &result.arena.get(identifier).unwrap().data else {
        panic!("expected identifier");
    };
    &identifier.text
}

fn assert_missing_type_export(result: &ParseResult, statement: NodeId) {
    let NodeData::ExportDeclaration(declaration) = &result.arena.get(statement).unwrap().data
    else {
        panic!("expected type-only export declaration");
    };
    assert!(declaration.is_type_only);
    assert!(declaration.modifiers.is_none());
    assert!(declaration.module_specifier.is_none());
    let clause = result
        .arena
        .get(declaration.export_clause.unwrap())
        .unwrap();
    assert_eq!(clause.parent, Some(statement));
    assert_eq!(clause.range.start, clause.range.end);
    assert_ne!(clause.flags.0 & (1 << 15), 0);
    let NodeData::NamedExports(bindings) = &clause.data else {
        panic!("expected missing named exports");
    };
    assert!(bindings.elements.nodes.is_empty());
}
