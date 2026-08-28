use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn check(source: &str) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            lib: Some(vec!["es5".to_owned()]),
            strict_function_types: true,
            strict_null_checks: true,
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
}

#[test]
fn class_constructor_assignments_keep_arity_details_and_accept_matching_subclasses() {
    let source = r#"class A {
    constructor(public x: string) {
    }
}
class B extends A {
    constructor(x: string, public data: string) {
        super(x);
    }
}
class C extends A {
    constructor(x: string) {
        super(x);
    }
}

var r1: typeof A = B;
var r2: new (x: string) => A = B;
var r3: typeof A = C;"#;
    let program = check(source);
    let diagnostics = program.diagnostics();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, name, target) in [
        (&diagnostics[0], "r1", "typeof A"),
        (&diagnostics[1], "r2", "new (x: string) => A"),
    ] {
        let range = diagnostic.range.unwrap();
        assert_eq!(diagnostic.code, Some(2322));
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            name
        );
        assert_eq!(
            diagnostic.message,
            format!(
                "Type 'typeof B' is not assignable to type '{target}'.\n  Target signature provides too few arguments. Expected 2 or more, but got 1."
            )
        );
    }
}

#[test]
fn constructor_relations_keep_parameter_return_and_static_checks() {
    for (source, expected) in [
        (
            "class A { constructor(x: string) {} } class B { constructor(x: string) {} } var result: typeof A = B;",
            vec![],
        ),
        (
            "class A { constructor(x: string) {} } class B { constructor(x: number) {} } var result: typeof A = B;",
            vec![2322],
        ),
        (
            "class A { value = ''; } class B {} var result: typeof A = B;",
            vec![2322],
        ),
        (
            "class A { static value: string; } class B { static value: number; } var result: typeof A = B;",
            vec![2322],
        ),
        (
            "class A { constructor() {} } class B { private constructor() {} } var result: typeof A = B;",
            vec![2322],
        ),
        (
            "class A { private constructor() {} } class B { constructor() {} } var result: typeof A = B;",
            vec![],
        ),
        (
            "class A {} abstract class B {} var result: typeof A = B;",
            vec![2322],
        ),
        (
            "abstract class A {} class B {} var result: typeof A = B;",
            vec![],
        ),
    ] {
        let program = check(source);
        let actual = program
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code.unwrap())
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source}: {:?}", program.diagnostics());
    }
}
