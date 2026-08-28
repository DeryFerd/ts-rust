use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn check(source: &str, no_check: bool) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            lib: Some(vec!["es5".to_owned()]),
            no_implicit_any: true,
            strict_null_checks: true,
            no_emit: true,
            no_check,
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
fn reserved_identifier_diagnostics_keep_existing_name_errors() {
    for source in ["let;", "\"use strict\"; let;"] {
        let program = check(source, false);
        assert_eq!(spans(&program, source), [(1212, "let"), (2304, "let")]);
    }
    let source = "function let() {}";
    assert_eq!(spans(&check(source, false), source), [(1212, "let")]);
}

#[test]
fn interface_asi_keeps_reserved_name_and_assignment_diagnostics() {
    let source = "var interface: number, I: string;\ninterface\nI\n{}";
    let program = check(source, false);
    assert_eq!(
        spans(&program, source),
        [
            (1212, "interface"),
            (1212, "interface"),
            (2454, "interface"),
            (2454, "I")
        ]
    );
}

#[test]
fn namespace_interface_asi_checks_global_value_reads() {
    let source = "var interface: number, I: string;\nnamespace n { interface\nI\n{} }";
    assert_eq!(
        spans(&check(source, false), source),
        [(1212, "interface"), (1212, "interface")]
    );
    for source in [
        "var value: number; namespace n { value; }",
        "namespace n { value; } var value: number;",
        "var value: number; namespace n { namespace inner { value; {} } }",
    ] {
        assert!(check(source, false).diagnostics().is_empty(), "{source}");
    }
}

#[test]
fn reserved_identifier_diagnostics_keep_comment_and_no_check_behavior() {
    let source = "// @ts-expect-error\nlet;";
    assert!(check(source, false).diagnostics().is_empty());
    assert!(check("let;", true).diagnostics().is_empty());
}

#[test]
fn reserved_identifier_diagnostics_keep_identifier_names_and_source_spelling() {
    let source = "const object = { let: 1, interface: 2 }; object.let; object.interface;";
    assert!(check(source, false).diagnostics().is_empty());
    let source = "var l\\u0065t = 1;";
    let program = check(source, false);
    assert_eq!(spans(&program, source), [(1212, "l\\u0065t")]);
    assert_eq!(
        program.diagnostics()[0].message,
        "Identifier expected. 'l\\u0065t' is a reserved word in strict mode."
    );
}
