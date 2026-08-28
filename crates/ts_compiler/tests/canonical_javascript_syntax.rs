use ts_ast::NodeData;
use ts_compiler::{Program, ProgramDiagnostic};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options() -> CompilerOptions {
    CompilerOptions {
        allow_js: true,
        target: ScriptTarget::Es2015,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn check(file_name: &str, source: &str, options: CompilerOptions) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(&format!("/project/{file_name}"), source)
        .unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &[file_name.to_owned()],
        options,
    )
    .unwrap_or_else(|error| panic!("{file_name}: {source}\n{error:?}"))
}

fn spans<'source>(
    diagnostics: &[ProgramDiagnostic],
    source: &'source str,
) -> Vec<(u32, &'source str)> {
    diagnostics
        .iter()
        .map(|diagnostic| {
            let range = diagnostic.range.unwrap();
            (
                diagnostic.code.unwrap(),
                &source[range.start.get() as usize..range.end.get() as usize],
            )
        })
        .collect()
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the source forms and their pinned diagnostic spans together.
fn typescript_syntax_in_javascript_uses_original_ast_spans() {
    let cases: &[(&str, &[(u32, &str)])] = &[
        ("import a = b;", &[(8002, "import a = b;")]),
        ("export = b;", &[(8003, "export = b;")]),
        ("class C<T> {}", &[(8004, "T")]),
        ("const C = class<T> {};", &[(8004, "T")]),
        ("function F<T>() {}", &[(8004, "T")]),
        ("class C implements D {}", &[(8005, "implements D")]),
        ("interface I {}", &[(8006, "I")]),
        ("enum E {}", &[(8006, "E")]),
        ("namespace M {}", &[(8006, "M")]),
        ("type A = string;", &[(8008, "A")]),
        ("declare var v;", &[(8009, "declare")]),
        (
            "abstract class C { abstract value; }",
            &[(8009, "abstract"), (8009, "abstract")],
        ),
        ("class C { public method() {} }", &[(8009, "public")]),
        ("function F(value?) {}", &[(8009, "?")]),
        (
            "class C { method?() {} value? = 1; }",
            &[(8009, "?"), (8009, "?")],
        ),
        ("var v: () => number;", &[(8010, "() => number")]),
        (
            "function F(value: number): string {}",
            &[(8010, "number"), (8010, "string")],
        ),
        (
            "class C { constructor(public readonly value) {} }",
            &[(8012, "public readonly")],
        ),
        ("function F();", &[(8017, "function F();")]),
        ("class C { method(); }", &[(8017, "method();")]),
        ("class C { constructor(); }", &[(8017, "constructor();")]),
    ];
    for &(source, expected) in cases {
        let program = check("input.js", source, options());
        assert_eq!(spans(program.diagnostics(), source), expected, "{source}");
    }
}

#[test]
fn javascript_signature_ranges_keep_typescript_ranges_and_asi_unchanged() {
    for (source, typescript, javascript) in [
        (
            "function F(); class C { method(); }",
            ["function F()", "method()"],
            ["function F();", "method();"],
        ),
        (
            "function F() /* terminator */ ; class C { method() /* terminator */ ; }",
            ["function F()", "method()"],
            [
                "function F() /* terminator */ ;",
                "method() /* terminator */ ;",
            ],
        ),
        (
            "function F(value: number): string; class C { method(value: number): string; }",
            [
                "function F(value: number): string",
                "method(value: number): string",
            ],
            [
                "function F(value: number): string;",
                "method(value: number): string;",
            ],
        ),
        (
            "function F()\nclass C { method()\n}",
            ["function F()", "method()"],
            ["function F()", "method()"],
        ),
    ] {
        let ranges = |parsed: &ParseResult| {
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}\n{:?}",
                parsed.diagnostics
            );
            parsed
                .arena
                .iter()
                .filter(|(_, node)| {
                    matches!(
                        node.data,
                        NodeData::FunctionDeclaration(_) | NodeData::MethodDeclaration(_)
                    )
                })
                .map(|(_, node)| {
                    &source[node.range.start.get() as usize..node.range.end.get() as usize]
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(ranges(&parse_source_file(source)), typescript, "{source}");
        assert_eq!(
            ranges(&parse_javascript_source_file(source)),
            javascript,
            "{source}"
        );
    }
}

#[test]
fn javascript_syntax_checks_do_not_depend_on_check_js() {
    for (prefix, check_js) in [
        ("", false),
        ("", true),
        ("// @ts-check\n", false),
        ("// @ts-nocheck\n", true),
    ] {
        let source = format!("{prefix}const value: number = 1;");
        let program = check(
            "input.js",
            &source,
            CompilerOptions {
                check_js,
                ..options()
            },
        );
        assert_eq!(spans(program.diagnostics(), &source), [(8010, "number")]);
    }
    let typed = check("input.ts", "const value: number = 1;", options());
    assert!(typed.diagnostics().is_empty());
}

#[test]
fn javascript_grammar_does_not_disable_semantic_checking() {
    for (check_js, expected) in [(false, Vec::new()), (true, vec![2322])] {
        let program = check(
            "input.js",
            "function work() {}\n/** @type {string} */\nwork.value = 1;\nconst copied = work.value;",
            CompilerOptions {
                check_js,
                module: ModuleKind::EsNext,
                module_specified: true,
                module_resolution: ModuleResolutionKind::Bundler,
                ..options()
            },
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code.unwrap())
                .collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn jsdoc_reparsed_types_are_not_reported_as_typescript_syntax() {
    let source = concat!(
        "/** @typedef {{value: number}} Entry */\n",
        "/**\n",
        " * @template T\n",
        " * @param {T} value\n",
        " * @returns {T}\n",
        " */\n",
        "const identity = value => value;\n",
    );
    let program = check("input.js", source, options());
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    let file = program.source_file("/project/input.js").unwrap();
    assert!(
        file.parse
            .arena
            .iter()
            .any(|(_, node)| { node.flags.0 & ts_ast::NodeFlags::REPARSED.0 != 0 })
    );
}

#[test]
fn javascript_parameter_decorators_keep_the_existing_option_behavior() {
    let source = "function dec() {} class C { method(@dec value) {} }";
    for experimental_decorators in [false, true] {
        let program = check(
            "input.js",
            source,
            CompilerOptions {
                experimental_decorators,
                ..options()
            },
        );
        let expected = if experimental_decorators {
            Vec::new()
        } else {
            vec![(1206, "@dec")]
        };
        assert_eq!(spans(program.diagnostics(), source), expected);
    }
}

#[test]
fn javascript_syntax_errors_keep_parser_and_output_diagnostics() {
    let program = check(
        "input.js",
        "const value: number = 1;",
        CompilerOptions {
            no_emit: false,
            ..options()
        },
    );
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code.unwrap())
            .collect::<Vec<_>>(),
        [5055, 8010]
    );

    let source = "const value: number = 0x;";
    let parsed = parse_javascript_source_file(source);
    assert!(!parsed.diagnostics.is_empty());
    let program = check("input.js", source, options());
    for parser_diagnostic in &parsed.diagnostics {
        assert!(program.diagnostics().iter().any(|diagnostic| {
            diagnostic.code == parser_diagnostic.code
                && diagnostic.range == Some(parser_diagnostic.range)
                && diagnostic.message == parser_diagnostic.message
        }));
    }
    assert!(
        program
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == Some(8010))
    );
}
