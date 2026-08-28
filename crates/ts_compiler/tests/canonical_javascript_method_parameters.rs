use ts_ast::NodeData;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn check(file_name: &str, source: &str, check_js: bool, no_implicit_any: bool) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(&format!("/project/{file_name}"), source)
        .unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &[file_name.to_owned()],
        CompilerOptions {
            allow_js: true,
            check_js,
            no_implicit_any,
            target: ScriptTarget::Es2015,
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
}

fn spans<'source>(program: &Program, source: &'source str) -> Vec<(u32, &'source str)> {
    program
        .diagnostics()
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
fn parameter_decorators_keep_checked_and_unchecked_javascript_spans() {
    let source = "function dec(target, key, index) {}\nclass Foo { method(@dec x) {} }";
    for check_js in [false, true] {
        let program = check("input.js", source, check_js, true);
        let expected = if check_js {
            vec![
                (7006, "target"),
                (7006, "key"),
                (7006, "index"),
                (1206, "@"),
                (7006, "@dec x"),
            ]
        } else {
            vec![(1206, "@dec")]
        };
        assert_eq!(spans(&program, source), expected);
        let file = program.source_file("/project/input.js").unwrap();
        assert_eq!(
            file.parse
                .arena
                .iter()
                .filter(|(_, node)| { matches!(node.data, NodeData::Decorator(_)) })
                .count(),
            1,
        );
    }
}

#[test]
fn checked_javascript_methods_keep_parameter_and_body_diagnostics() {
    for decorator in ["", "@dec "] {
        let source = format!(
            "function dec() {{}}\nclass Foo {{ method({decorator}x) {{ this.missing; return x; }} }}"
        );
        for no_implicit_any in [false, true] {
            let program = check("input.js", &source, true, no_implicit_any);
            let mut expected = Vec::new();
            if !decorator.is_empty() {
                expected.push((1206, "@"));
            }
            if no_implicit_any {
                expected.push((7006, if decorator.is_empty() { "x" } else { "@dec x" }));
            }
            expected.push((2339, "missing"));
            assert_eq!(spans(&program, &source), expected, "{source}");
        }
    }
}

#[test]
fn checked_javascript_methods_keep_all_parameters_and_typed_controls() {
    let source = "class Foo { method(first, second) { return second; } }";
    let program = check("input.js", source, true, true);
    assert_eq!(spans(&program, source), [(7006, "first"), (7006, "second")]);

    let source = "class Foo { method(value: number) { this.missing; return value; } }";
    let program = check("input.ts", source, true, true);
    assert_eq!(spans(&program, source), [(2339, "missing")]);
}
