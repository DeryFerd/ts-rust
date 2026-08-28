use ts_ast::NodeData;
use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::parse_source_file;
use ts_vfs::{FileSystem, MemoryFileSystem};

// The source unit from accessorsInAmbientContext.ts after fixture directives are removed.
const ORIGINAL: &str = "declare namespace M {
    class C {
        get X() { return 1; }
        set X(v) { }

        static get Y() { return 1; }
        static set Y(v) { }
    }
}

declare class C {
    get X() { return 1; }
    set X(v) { }

    static get Y() { return 1; }
    static set Y(v) { }
}";

#[derive(Debug, PartialEq)]
struct ObservedDiagnostic {
    code: u32,
    start: usize,
    text: String,
    message: String,
}

fn check(source: &str) -> Vec<ObservedDiagnostic> {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/accessorsInAmbientContext.ts", source)
        .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        "/project",
        &["accessorsInAmbientContext.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            lib: Some(vec!["es5".to_owned()]),
            no_emit: true,
            ..CompilerOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    program
        .diagnostics()
        .iter()
        .map(|diagnostic| {
            assert_eq!(
                diagnostic.file_name.as_deref(),
                Some("/project/accessorsInAmbientContext.ts")
            );
            let range = diagnostic.range.unwrap();
            ObservedDiagnostic {
                code: diagnostic.code.unwrap(),
                start: range.start.get() as usize,
                text: source[range.start.get() as usize..range.end.get() as usize].to_owned(),
                message: diagnostic.message.clone(),
            }
        })
        .collect()
}

#[test]
fn original_ambient_accessor_fixture_keeps_all_eight_body_errors() {
    let parsed = parse_source_file(ORIGINAL);
    assert!(parsed.diagnostics.is_empty());
    let mut bodies = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| match &record.data {
            NodeData::GetAccessorDeclaration(accessor) => accessor.body,
            NodeData::SetAccessorDeclaration(accessor) => accessor.body,
            _ => None,
        })
        .map(|body| parsed.arena.get(body).unwrap().range.start.get() as usize)
        .collect::<Vec<_>>();
    bodies.sort_unstable();
    let diagnostics = check(ORIGINAL);
    assert_eq!(diagnostics.len(), 8, "{diagnostics:?}");
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.start)
            .collect::<Vec<_>>(),
        bodies
    );
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.code, 1183);
        assert_eq!(diagnostic.text, "{");
        assert_eq!(
            diagnostic.message,
            "An implementation cannot be declared in ambient contexts."
        );
    }
}

#[test]
fn ambient_accessor_body_errors_keep_circular_getter_errors() {
    let circular = check("declare class C { get X(): typeof this.X; }");
    assert_eq!(circular.len(), 1);
    assert_eq!(circular[0].code, 2502);
    for source in [
        "declare class C { get X(): typeof this.X; get Y() { return 1; } }",
        "declare class C { get X(): typeof this.X { return 1; } }",
        "declare namespace M { class C { get X(): typeof this.X; get Y() { return 1; } } }",
    ] {
        let diagnostics = check(source);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| (diagnostic.code, diagnostic.text.as_str()))
                .collect::<Vec<_>>(),
            [(2502, "X"), (1183, "{")],
            "{source}\n{diagnostics:?}"
        );
    }
}

#[test]
fn ambient_accessor_body_errors_do_not_hide_later_source_errors() {
    let source = format!("{ORIGINAL}\nconst later: number = 'wrong';");
    let diagnostics = check(&source);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [1183, 1183, 1183, 1183, 1183, 1183, 1183, 1183, 2322]
    );
}

#[test]
fn ordinary_accessor_bodies_remain_valid() {
    assert!(check("class C { get X(): number { return 1; } set X(v) {} }").is_empty());
}
