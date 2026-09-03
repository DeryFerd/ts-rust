use ts_compiler::{Program, ProgramDiagnostic};
use ts_diagnostics::Category;
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const SOURCE_PATH: &str = "/project/scripts/input.js";
const SOURCE: &str = "export const value = 1;\n";

fn options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn unlocated_error(code: u32, message: String) -> ProgramDiagnostic {
    ProgramDiagnostic {
        file_name: None,
        range: None,
        code: Some(code),
        category: Category::Error,
        message,
        related_information: Vec::new(),
    }
}

fn javascript_root_error(display_name: &str) -> ProgramDiagnostic {
    unlocated_error(
        6504,
        format!(
            "File '{display_name}' is a JavaScript file. Did you mean to enable the 'allowJs' option?\n  The file is in the program because:\n    Root file specified for compilation",
        ),
    )
}

#[test]
fn disallowed_javascript_roots_keep_supplied_path_spelling_in_ts6504() {
    for (root_name, display_name) in [
        ("/project/scripts/input.js", "/project/scripts/input.js"),
        ("scripts/input.js", "scripts/input.js"),
        ("./scripts/input.js", "./scripts/input.js"),
        ("scripts/../scripts/input.js", "scripts/../scripts/input.js"),
        (
            "/project/scripts/../scripts/input.js",
            "/project/scripts/../scripts/input.js",
        ),
        (
            r".\scripts\..\scripts\input.js",
            "./scripts/../scripts/input.js",
        ),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file(SOURCE_PATH, SOURCE).unwrap();

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &[root_name.to_owned()],
            options(),
        )
        .unwrap_or_else(|error| panic!("root {root_name:?}: {error:?}"));

        assert_eq!(
            program.diagnostics(),
            &[javascript_root_error(display_name)],
            "root {root_name:?}",
        );
        assert!(program.source_file(SOURCE_PATH).is_none());
        assert!(program.source_file(root_name).is_none());
        assert!(
            program
                .source_files()
                .iter()
                .all(|source| source.is_default_library),
            "root {root_name:?}",
        );
    }
}

#[test]
fn javascript_root_admission_keeps_allow_js_and_check_js_rules() {
    let root_name = r".\scripts\..\scripts\input.js";
    for (allow_js, allow_js_specified, check_js, admitted) in [
        (true, true, false, true),
        (true, true, true, true),
        (false, false, true, true),
        (false, true, true, false),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file(SOURCE_PATH, SOURCE).unwrap();
        let mut options = options();
        options.allow_js = allow_js;
        options.allow_js_specified = allow_js_specified;
        options.check_js = check_js;

        let program = Program::try_new_with_canonical_checker(
            &filesystem,
            "/project",
            &[root_name.to_owned()],
            options,
        )
        .unwrap_or_else(|error| {
            panic!(
                "allow_js={allow_js}, specified={allow_js_specified}, check_js={check_js}: {error:?}",
            )
        });

        let expected = if admitted {
            Vec::new()
        } else {
            vec![
                unlocated_error(
                    5052,
                    "Option 'checkJs' cannot be specified without specifying option 'allowJs'."
                        .to_owned(),
                ),
                javascript_root_error("./scripts/../scripts/input.js"),
            ]
        };
        assert_eq!(
            program.diagnostics(),
            expected,
            "allow_js={allow_js}, specified={allow_js_specified}, check_js={check_js}",
        );
        let sources = program
            .source_files()
            .iter()
            .filter(|source| !source.is_default_library)
            .collect::<Vec<_>>();
        assert_eq!(sources.len(), usize::from(admitted));
        if admitted {
            let source = program.source_file(SOURCE_PATH).unwrap();
            assert_eq!(source.file_name, SOURCE_PATH);
            assert_eq!(source.source_text, SOURCE);
            assert_eq!(program.source_file(root_name).unwrap().id, source.id);
            assert_eq!(sources[0].id, source.id);
        } else {
            assert!(program.source_file(SOURCE_PATH).is_none());
            assert!(program.source_file(root_name).is_none());
        }
    }
}
