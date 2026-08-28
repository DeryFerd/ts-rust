use ts_ast::{NodeData, SyntaxKind};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

#[test]
fn unreachable_throw_directives_consume_only_reported_errors() {
    for (directive, allow_unreachable_code, expected) in [
        ("", false, vec![7027]),
        ("// @ts-ignore", false, vec![]),
        ("// @ts-expect-error", false, vec![]),
        ("// @ts-expect-error", true, vec![2578]),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        let source = format!(
            "function fail() {{\n  throw new Error(\"\");\n  {directive}\n  console.log(\"unreachable\");\n}}\n"
        );
        filesystem.write_file("/project/input.ts", &source).unwrap();
        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                allow_unreachable_code: Some(allow_unreachable_code),
                preserve_const_enums: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code.unwrap())
                .collect::<Vec<_>>(),
            expected,
            "{source}: {:?}",
            program.diagnostics(),
        );
    }
}

#[test]
fn throw_bodies_check_reachable_and_unreachable_arguments() {
    let filesystem = MemoryFileSystem::new(true);
    let source = concat!(
        "declare function numberOnly(value: number): void;\n",
        "declare function stringOnly(value: string): void;\n",
        "function fail(value: string | number) {\n",
        "  numberOnly('before');\n",
        "  value = 'narrowed';\n",
        "  throw new Error('stop');\n",
        "  stringOnly(value);\n",
        "}\n",
        "function reachable() {\n",
        "  // @ts-expect-error\n",
        "  console.log('reachable');\n",
        "}\n",
    );
    filesystem.write_file("/project/input.ts", source).unwrap();
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            allow_unreachable_code: Some(false),
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap();
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code.unwrap())
            .collect::<Vec<_>>(),
        [2345, 7027, 2345, 2578],
        "{:?}",
        program.diagnostics(),
    );
    assert!(program.diagnostics()[2].message.contains("string | number"));
}

#[test]
fn error_constructions_and_console_calls_retain_library_types() {
    for target in [ScriptTarget::Es5, ScriptTarget::Es2022] {
        let filesystem = MemoryFileSystem::new(true);
        let source = concat!(
            "function empty() { throw new Error(); }\n",
            "function message() {\n",
            "  console.log('reachable');\n",
            "  throw new Error('message');\n",
            "  // @ts-expect-error\n",
            "  console.log('unreachable');\n",
            "}\n",
        );
        filesystem.write_file("/project/input.ts", source).unwrap();
        let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["input.ts".to_owned()],
            CompilerOptions {
                target,
                allow_unreachable_code: Some(false),
                no_emit: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                let source = program.source_file("/project/input.ts").unwrap();
                let mut checked = 0;
                for (node, record) in source.parse.arena.iter() {
                    let expected = match &record.data {
                        NodeData::NewExpression(_) => "Error",
                        NodeData::Identifier(identifier) if identifier.text == "Error" => {
                            "ErrorConstructor"
                        }
                        NodeData::Identifier(identifier) if identifier.text == "console" => {
                            "Console"
                        }
                        NodeData::PropertyAccessExpression(_) => "(...data: any[]) => void",
                        NodeData::CallExpression(_)
                            if record.kind == SyntaxKind::CallExpression =>
                        {
                            "void"
                        }
                        _ => continue,
                    };
                    let node = source.node_ref(node).unwrap();
                    let type_ = queries.get_type_at_location(node).unwrap();
                    assert_eq!(queries.type_to_string(type_).unwrap(), expected);
                    checked += 1;
                }
                checked
            },
        )
        .unwrap();
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        assert_eq!(checked, Some(10));
    }
}
