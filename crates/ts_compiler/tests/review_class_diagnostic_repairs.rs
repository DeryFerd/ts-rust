use ts_ast::NodeData;
use ts_checker::semantic::SourceCheckError;
use ts_compiler::{CanonicalProgramCheckError, Program, ProgramDiagnostic};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::Category;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::parse_source_file;
use ts_vfs::{FileSystem, MemoryFileSystem};

struct Case {
    name: &'static str,
    source: &'static str,
    start: u32,
    end: u32,
}

fn check_case(case: &Case, code: u32, message: &str) {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/input.ts", case.source)
        .unwrap();
    let expected = vec![ProgramDiagnostic {
        file_name: Some("/project/input.ts".to_owned()),
        range: Some(TextRange::new(
            TextPos::new(case.start),
            TextPos::new(case.end),
        )),
        code: Some(code),
        category: Category::Error,
        message: message.to_owned(),
        related_information: Vec::new(),
    }];
    let (program, checked) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            strict: false,
            target: ScriptTarget::Es5,
            ..CompilerOptions::default()
        },
        |program, queries| {
            let cold = queries.cold_diagnostic_snapshot();
            let store = queries.semantic_store_id();
            let source = program.source_file("/project/input.ts").unwrap();
            assert!(source.parse.diagnostics.is_empty(), "{}", case.name);
            let unresolved = (code == 2662).then(|| {
                source
                    .parse
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::VariableDeclaration(variable) = &record.data else {
                            return None;
                        };
                        source.node_ref(variable.initializer?)
                    })
                    .unwrap()
            });
            let classes = source
                .parse
                .arena
                .iter()
                .filter_map(|(_, record)| {
                    let NodeData::ClassDeclaration(class) = &record.data else {
                        return None;
                    };
                    (code == 2377).then(|| source.node_ref(class.name.unwrap()).unwrap())
                })
                .map(|name| {
                    (
                        name,
                        queries.get_type_at_location(name).unwrap(),
                        queries.get_symbol_at_location(name).unwrap().unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            for pass in 0..3 {
                if pass != 0 {
                    assert_eq!(queries.replay_sources().unwrap(), cold, "{}", case.name);
                }
                assert_eq!(queries.semantic_store_id(), store, "{}", case.name);
                if let Some(reference) = unresolved {
                    assert_eq!(
                        queries.get_symbol_at_location(reference).unwrap(),
                        None,
                        "{}: the bare name must not bind to the static member",
                        case.name,
                    );
                }
                for (name, type_, symbol) in &classes {
                    assert_eq!(queries.get_type_at_location(*name).unwrap(), *type_);
                    assert_eq!(
                        queries.get_symbol_at_location(*name).unwrap(),
                        Some(*symbol),
                    );
                }
            }
            println!("{}: {cold:?}", case.name);
            assert_eq!(cold, expected, "{}", case.name);
        },
    )
    .unwrap_or_else(|error| panic!("{}: {error:?}", case.name));
    checked.expect("the canonical checker must run");
    assert_eq!(program.diagnostics(), expected, "{}", case.name);
}

#[test]
fn static_name_repairs_keep_full_records_and_unresolved_symbols() {
    for case in [
        Case {
            name: "static_original",
            source: "class C { static foo: string; bar() { let k = foo; } }",
            start: 46,
            end: 49,
        },
        Case {
            name: "exported_original",
            source: "export class C { static foo: string; bar() { let k = foo; } }",
            start: 53,
            end: 56,
        },
    ] {
        check_case(
            &case,
            2662,
            "Cannot find name 'foo'. Did you mean the static member 'C.foo'?",
        );
    }
    for case in [
        Case {
            name: "static_renamed",
            source: "/* class */ class Catalog { static title: string; read() { let result = /* value */ title; } }",
            start: 84,
            end: 89,
        },
        Case {
            name: "exported_renamed",
            source: "export /* class */ class Catalog { static title: string; read() { let result = /* value */ title; } }",
            start: 91,
            end: 96,
        },
    ] {
        check_case(
            &case,
            2662,
            "Cannot find name 'title'. Did you mean the static member 'Catalog.title'?",
        );
    }
}

#[test]
fn missing_super_repairs_skip_trivia_and_keep_class_identities() {
    for case in [
        Case {
            name: "constructor_original",
            source: "class Base {} class Model extends Base { constructor() {} }",
            start: 41,
            end: 52,
        },
        Case {
            name: "constructor_comment",
            source: "class Base {}\nclass Model extends Base {\n  /* constructor note */ constructor /* gap */ () {}\n}",
            start: 66,
            end: 77,
        },
    ] {
        check_case(
            &case,
            2377,
            "Constructors for derived classes must contain a 'super' call.",
        );
    }
}

#[test]
fn missing_super_public_constructor_range_matches_go() {
    check_case(
        &Case {
            name: "constructor_public",
            source: "class Base {} class Model extends Base { public constructor() {} }",
            start: 41,
            end: 59,
        },
        2377,
        "Constructors for derived classes must contain a 'super' call.",
    );
}

#[test]
fn missing_super_public_block_comment_range_matches_go() {
    check_case(
        &Case {
            name: "constructor_public_block",
            source: "class Base {} class Model extends Base { public /* constructor note */ constructor() {} }",
            start: 41,
            end: 82,
        },
        2377,
        "Constructors for derived classes must contain a 'super' call.",
    );
}

#[test]
fn line_break_after_public_retains_the_unsupported_field_boundary() {
    let source =
        "class Base {} class Model extends Base { public // constructor note\n constructor() {} }";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty());
    let class = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            (name.text == "Model").then_some(class)
        })
        .unwrap();
    let [field, constructor] = class.members.nodes.as_slice() else {
        panic!("the line break creates a field before the constructor")
    };
    let NodeData::PropertyDeclaration(field) = &parsed.arena.get(*field).unwrap().data else {
        panic!("public must be a field name, not a constructor modifier")
    };
    let NodeData::Identifier(name) = &parsed.arena.get(field.name).unwrap().data else {
        panic!("the field must have an identifier name")
    };
    assert_eq!(name.text, "public");
    assert!(field.type_.is_none());
    assert!(field.initializer.is_none());
    let NodeData::ConstructorDeclaration(constructor) =
        &parsed.arena.get(*constructor).unwrap().data
    else {
        panic!("the second member must be a constructor")
    };
    assert!(constructor.modifiers.is_none());

    let filesystem = MemoryFileSystem::new(true);
    filesystem.write_file("/project/input.ts", source).unwrap();
    let error = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["input.ts".to_owned()],
        CompilerOptions {
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            strict: false,
            target: ScriptTarget::Es5,
            ..CompilerOptions::default()
        },
    )
    .expect_err("the unannotated field must keep its unsupported boundary");
    assert!(matches!(
        error,
        CanonicalProgramCheckError::SourceCheck {
            file_name,
            error: SourceCheckError::Unsupported(_),
        } if file_name == "/project/input.ts"
    ));
    println!("constructor_public_line: unsupported unannotated field public");
}
