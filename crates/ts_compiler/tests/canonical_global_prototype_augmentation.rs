use ts_ast::NodeData;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const ORIGINAL: &str = concat!(
    "interface Object { data: number; }\n",
    "interface Function { functionData: string; }\n",
    "var o = {};\n",
    "var f = function () { };\n",
    "var r1 = o['data'];\n",
    "var r2 = o['functionData'];\n",
    "var r3 = f['functionData'];\n",
    "var r4 = f['data'];\n",
);

fn check(source: &str, no_implicit_any: bool, codes: &[u32], types: &[(&str, &str)]) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            strict: false,
            no_implicit_any,
            no_emit: true,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let diagnostics = queries.cold_diagnostic_snapshot();
            assert_eq!(
                diagnostics
                    .iter()
                    .filter_map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                codes
            );
            let file = program.source_file("/project/input.ts").unwrap();
            let mut identities = Vec::new();
            for (name, expected) in types {
                let node = file
                    .parse
                    .arena
                    .iter()
                    .find_map(|(_, node)| {
                        let NodeData::VariableDeclaration(variable) = &node.data else {
                            return None;
                        };
                        let NodeData::Identifier(identifier) =
                            &file.parse.arena.get(variable.name)?.data
                        else {
                            return None;
                        };
                        (identifier.text == *name).then(|| file.node_ref(variable.name).unwrap())
                    })
                    .unwrap();
                let type_ = queries.get_type_at_location(node).unwrap();
                assert_eq!(
                    queries.type_to_string(type_).unwrap(),
                    *expected,
                    "{name}: {source}"
                );
                identities.push((node, type_));
            }
            assert_eq!(queries.replay_sources().unwrap(), diagnostics);
            for (node, type_) in identities {
                assert_eq!(queries.get_type_at_location(node).unwrap(), type_);
            }
        },
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    checked.expect("the canonical checker must run");
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .filter_map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        codes
    );
}

#[test]
fn bracket_reads_keep_global_declaration_types_and_the_real_callable() {
    check(
        &format!("{ORIGINAL}var called = f();"),
        false,
        &[],
        &[
            ("r1", "number"),
            ("r2", "any"),
            ("r3", "string"),
            ("r4", "number"),
            ("f", "() => void"),
            ("called", "void"),
        ],
    );
}

#[test]
fn missing_function_property_on_an_object_keeps_the_index_diagnostic() {
    check(
        ORIGINAL,
        true,
        &[7053],
        &[("r1", "number"), ("r3", "string"), ("r4", "number")],
    );
}

#[test]
fn own_properties_win_and_other_declared_names_keep_their_types() {
    check(
        concat!(
            "interface Object { total: number; } interface Function { label: string; } ",
            "var own = { total: 'own', label: false }; var f = function () {}; ",
            "var first = own['total']; var second = own['label']; var third = f['label'];",
        ),
        false,
        &[],
        &[
            ("first", "string"),
            ("second", "boolean"),
            ("third", "string"),
        ],
    );
}

#[test]
fn prototype_property_types_do_not_hide_assignment_errors() {
    check(
        concat!(
            "interface Object { total: number; } interface Function { label: string; } ",
            "var o = {}; var f = function () {}; ",
            "var wrongText: string = o['total']; var wrongNumber: number = f['label'];",
        ),
        false,
        &[2322, 2322],
        &[],
    );
}

#[test]
fn module_local_object_interfaces_do_not_augment_global_objects() {
    check(
        "export {}; interface Object { local: number; } var o = {}; var missing = o['local'];",
        false,
        &[],
        &[("missing", "any")],
    );
}

#[test]
fn cold_builtin_properties_without_augmentation() {
    check(
        "const method = ({})['toString'];\nconst ctor = ({})['constructor'];\n",
        false,
        &[],
        &[("method", "() => string"), ("ctor", "Function")],
    );
}

#[test]
fn cold_function_property_keeps_its_declared_type() {
    check(
        "var f = function () {}; var arity = f['length'];",
        false,
        &[],
        &[("f", "() => void"), ("arity", "number")],
    );
}

#[test]
fn own_properties_win_over_builtin_methods_and_properties() {
    check(
        concat!(
            "var own = { toString: 17, constructor: false }; ",
            "var method = own['toString']; var ctor = own['constructor'];",
        ),
        false,
        &[],
        &[("method", "number"), ("ctor", "boolean")],
    );
}

#[test]
fn augmentations_are_visible_before_the_declaration_and_in_function_bodies() {
    check(
        concat!(
            "var first = ({})['total']; ",
            "var read = function () { return ({})['total']; }; ",
            "interface Object { total: number; } var result = read();",
        ),
        false,
        &[],
        &[
            ("first", "number"),
            ("read", "() => number"),
            ("result", "number"),
        ],
    );
}
