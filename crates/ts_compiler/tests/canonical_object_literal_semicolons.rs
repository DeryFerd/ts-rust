use ts_ast::NodeData;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn object_semicolons_report_exact_commas_and_keep_same_line_nodes() {
    for members in [
        "aa;",
        "a; b; c",
        "a;\r\n  b;\r\n  c;",
        "first: 1; second: 2",
        "method() {}; next: 1",
        "'\u{1f600}': 1 /* kept */; next: 2",
        "...donor; next: 2",
    ] {
        let prefix = "const value = { ";
        let source = format!("{prefix}{members} }}; const after = value;");
        let comma_source = format!(
            "{prefix}{} }}; const after = value;",
            members.replace(';', ",")
        );
        let expected = members
            .match_indices(';')
            .map(|(offset, _)| {
                let start = u32::try_from(prefix.len() + offset).unwrap();
                (1005, start, start + 1, "',' expected.")
            })
            .collect::<Vec<_>>();
        for (parsed, control) in [
            (parse_source_file(&source), parse_source_file(&comma_source)),
            (
                parse_javascript_source_file(&source),
                parse_javascript_source_file(&comma_source),
            ),
        ] {
            assert!(control.diagnostics.is_empty(), "{comma_source}");
            assert_eq!(
                parsed
                    .diagnostics
                    .iter()
                    .map(|error| (
                        error.code.unwrap(),
                        error.range.start.get(),
                        error.range.end.get(),
                        error.message.as_str(),
                    ))
                    .collect::<Vec<_>>(),
                expected,
                "{source}",
            );
            let shape = |parsed: &ParseResult| {
                parsed
                    .arena
                    .iter()
                    .map(|(_, node)| (node.kind, node.range, node.parent))
                    .collect::<Vec<_>>()
            };
            assert_eq!(shape(&parsed), shape(&control), "{source}");
            let object = parsed
                .arena
                .iter()
                .find_map(|(_, node)| match &node.data {
                    NodeData::ObjectLiteralExpression(object) => Some(object),
                    _ => None,
                })
                .unwrap();
            assert!(!object.properties.has_trailing_comma, "{source}");
        }
    }
}

#[test]
fn next_line_object_semicolon_keeps_the_comma_error_instead_of_an_eof_brace_error() {
    for source in ["var v = {\n  a\n;", "var v = {\r\n  a\r\n;"] {
        let parsed = parse_source_file(source);
        let [error] = parsed.diagnostics.as_slice() else {
            panic!("{source}: {:?}", parsed.diagnostics)
        };
        assert_eq!(error.code, Some(1005));
        assert_eq!(error.message, "',' expected.");
        assert_eq!(error.range.start.get() as usize, source.len() - 1);
        assert_eq!(error.range.end.get() as usize, source.len());
        let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file")
        };
        assert_eq!(file.statements.nodes.len(), 1);
        let statement = parsed.arena.get(file.statements.nodes[0]).unwrap();
        assert_eq!(statement.range.end.get() as usize, source.len());
    }
}

#[test]
fn object_semicolon_recovery_preserves_later_semantic_errors_and_replay() {
    let mut semantic_controls = Vec::new();
    for (separator, parse_errors) in [(";", 1), (",", 0)] {
        let source = format!(
            "const value = {{ missing{separator} present: 1 }};\nconst after = value.present;\nconst wrong: string = after;"
        );
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file("/project/input.ts", &source).unwrap();
        let (program, cold) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                lib: Some(vec!["es5".to_owned()]),
                skip_lib_check: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
            |_, queries| {
                let cold = queries.cold_diagnostic_snapshot();
                assert_eq!(queries.replay_sources().unwrap(), cold);
                cold
            },
        )
        .unwrap();
        assert_eq!(cold.as_deref(), Some(program.diagnostics()));
        assert_eq!(
            program
                .source_file("/project/input.ts")
                .unwrap()
                .parse
                .diagnostics
                .len(),
            parse_errors,
        );
        let semantics = program
            .diagnostics()
            .iter()
            .filter(|error| error.code != Some(1005))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(
            semantics.iter().map(|error| error.code).collect::<Vec<_>>(),
            [Some(18004), Some(2322)],
        );
        assert_eq!(program.diagnostics().len(), semantics.len() + parse_errors);
        semantic_controls.push(semantics);
    }
    assert_eq!(semantic_controls[0], semantic_controls[1]);
}
