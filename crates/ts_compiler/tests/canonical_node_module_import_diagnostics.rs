use ts_compiler::{Program, ProgramDiagnostic};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn options(module: ModuleKind) -> CompilerOptions {
    CompilerOptions {
        module,
        module_specified: true,
        module_resolution: if module == ModuleKind::NodeNext {
            ModuleResolutionKind::NodeNext
        } else {
            ModuleResolutionKind::Node16
        },
        target: ScriptTarget::Es2022,
        declaration: true,
        lib: Some(vec!["es5".to_owned()]),
        no_emit: true,
        ..CompilerOptions::default()
    }
}

fn message(code: u32, arguments: &[&str]) -> String {
    Diagnostic::with_arguments(message_by_code(code).unwrap(), arguments.iter().copied())
        .render()
        .unwrap()
}

fn check(filesystem: &MemoryFileSystem, roots: &[&str], options: CompilerOptions) -> Program {
    let module = options.module;
    let skip_lib_check = options.skip_lib_check;
    let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
        filesystem,
        "/project",
        &roots
            .iter()
            .map(|root| (*root).to_owned())
            .collect::<Vec<_>>(),
        options,
        |_, queries| queries.replay_sources().unwrap(),
    )
    .unwrap_or_else(|error| panic!("{module:?}, skipLibCheck={skip_lib_check}: {error:?}"));
    assert_eq!(program.diagnostics(), replay.unwrap());
    program
}

fn assert_specifier_span(program: &Program, diagnostic: &ProgramDiagnostic) {
    let source = program
        .source_file(diagnostic.file_name.as_deref().unwrap())
        .unwrap();
    let range = diagnostic.range.unwrap();
    assert_eq!(
        &source.source_text[range.start.get() as usize..range.end.get() as usize],
        "'./target.mjs'",
    );
    assert!(diagnostic.related_information.is_empty());
}

#[test]
fn node_module_import_diagnostics_follow_checked_source_and_target_modes() {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        ("target.mts", "export const value: number = 1;"),
        (
            "consumer.cts",
            "import * as ns from './target.mjs'; export const copied = ns;",
        ),
        (
            "consumer.mts",
            concat!(
                "import * as ns from './target.mjs'; ",
                "import { value } from './target.mjs'; ",
                "export const copied = ns; export const copy = value;",
            ),
        ),
        (
            "consumer.d.cts",
            "import * as ns from './target.mjs'; export const copied: typeof ns;",
        ),
        (
            "consumer.d.ts",
            "import * as ns from './target.mjs'; export const copied: typeof ns;",
        ),
    ] {
        filesystem
            .write_file(&format!("/project/{path}"), text)
            .unwrap();
    }
    let roots = [
        "target.mts",
        "consumer.cts",
        "consumer.mts",
        "consumer.d.cts",
        "consumer.d.ts",
    ];
    for module in [
        ModuleKind::Node16,
        ModuleKind::Node18,
        ModuleKind::Node20,
        ModuleKind::NodeNext,
    ] {
        for skip_lib_check in [false, true] {
            let mut options = options(module);
            options.skip_lib_check = skip_lib_check;
            let program = check(&filesystem, &roots, options);
            let expected = if matches!(module, ModuleKind::Node16 | ModuleKind::Node18) {
                if skip_lib_check { 1 } else { 3 }
            } else {
                0
            };
            assert_eq!(
                program.diagnostics().len(),
                expected,
                "{module:?}, skipLibCheck={skip_lib_check}"
            );
            for diagnostic in program.diagnostics() {
                assert_eq!(diagnostic.code, Some(1479));
                assert_eq!(diagnostic.message, message(1479, &["./target.mjs"]));
                assert_specifier_span(&program, diagnostic);
            }
        }
    }
}

#[test]
fn node_module_import_diagnostics_keep_package_format_details() {
    for (extension, package, detail_code, arguments) in [
        ("ts", None, 1480, vec![".mts"]),
        (
            "ts",
            Some("{}"),
            1481,
            vec![".mts", "/project/package.json"],
        ),
        ("ts", Some(r#"{"type":"commonjs"}"#), 1480, vec![".mts"]),
        ("tsx", None, 1483, Vec::new()),
        ("tsx", Some("{}"), 1482, vec!["/project/package.json"]),
    ] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file("/project/target.mts", "export const value: number = 1;")
            .unwrap();
        let consumer = format!("consumer.{extension}");
        filesystem
            .write_file(
                &format!("/project/{consumer}"),
                "import * as ns from './target.mjs'; export const copied = ns;",
            )
            .unwrap();
        if let Some(package) = package {
            filesystem
                .write_file("/project/package.json", package)
                .unwrap();
        }
        let program = check(
            &filesystem,
            &[&consumer, "target.mts"],
            options(ModuleKind::Node16),
        );
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected one module-format error: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(1479));
        assert_eq!(
            diagnostic.message,
            format!(
                "{}\n  {}",
                message(1479, &["./target.mjs"]),
                message(detail_code, &arguments),
            )
        );
        assert_specifier_span(&program, diagnostic);
    }
}

#[test]
fn node_module_import_diagnostics_respect_side_effect_import_checks() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file("/project/target.mts", "export const value: number = 1;")
        .unwrap();
    filesystem
        .write_file("/project/consumer.cts", "import './target.mjs';")
        .unwrap();
    for enabled in [false, true] {
        let mut options = options(ModuleKind::Node18);
        options.no_unchecked_side_effect_imports = enabled;
        options.no_unchecked_side_effect_imports_specified = true;
        let program = check(&filesystem, &["consumer.cts", "target.mts"], options);
        assert_eq!(program.diagnostics().len(), usize::from(enabled));
        for diagnostic in program.diagnostics() {
            assert_eq!(diagnostic.code, Some(1479));
            assert_eq!(diagnostic.message, message(1479, &["./target.mjs"]));
            assert_specifier_span(&program, diagnostic);
        }
    }
}
