use serde_json::{Value, json};
use ts_binder::CanonicalNameResolverOptions;
use ts_checker::semantic::{CanonicalCheckerOptions, IntrinsicBootstrapOptions};
use ts_compiler::Program;
use ts_options::{CompilerOptions, ModuleKind, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn config_program(options: &Value) -> Program {
    let file_system = MemoryFileSystem::new(true);
    let config = json!({
        "files": ["main.ts"],
        "compilerOptions": options,
    });
    file_system
        .write_file("/project/main.ts", "const value: number = 1;")
        .unwrap();
    file_system
        .write_file("/project/tsconfig.json", &config.to_string())
        .unwrap();
    Program::from_config(&file_system, "/project/tsconfig.json")
}

#[test]
fn canonical_option_adapters_preserve_the_shared_target() {
    assert_eq!(
        CanonicalNameResolverOptions::default().emit_target,
        ScriptTarget::Es2025
    );
    for checker in [
        CanonicalCheckerOptions::default(),
        CanonicalCheckerOptions::from(IntrinsicBootstrapOptions::default()),
    ] {
        assert_eq!(checker.name_resolution.emit_target, ScriptTarget::Es2025);
    }
    for target in [
        ScriptTarget::Es5,
        ScriptTarget::Es2015,
        ScriptTarget::Es2020,
        ScriptTarget::Es2025,
        ScriptTarget::EsNext,
    ] {
        let options = CompilerOptions {
            target,
            ..CompilerOptions::default()
        };
        let names = CanonicalNameResolverOptions::from(&options);
        assert_eq!(names.emit_target, target);
        assert_eq!(options.printer_settings().target, target);
        assert_eq!(options.target, target);
    }
}

#[test]
fn omitted_target_and_lib_load_the_es2025_default_library() {
    let program = config_program(&json!({}));
    assert_eq!(program.options().target, ScriptTarget::Es2025);
    assert_eq!(program.options().module, ModuleKind::None);
    assert!(!program.options().module_specified);
    assert_eq!(
        program
            .options()
            .module
            .effective_for_target(program.options().target),
        ModuleKind::Es2022
    );
    assert!(program.options().lib.is_none());
    assert!(!program.options().no_lib);
    assert!(!program.options().no_check);
    assert!(program.source_files().iter().any(|source| {
        source.is_default_library && source.file_name.ends_with("/lib.es2025.full.d.ts")
    }));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
}

#[test]
fn explicit_target_and_library_choices_override_the_default_library() {
    for (configured, target, library) in [
        (json!({"target":"es5"}), ScriptTarget::Es5, Some("lib.d.ts")),
        (
            json!({"target":"es2015"}),
            ScriptTarget::Es2015,
            Some("lib.es6.d.ts"),
        ),
        (
            json!({"target":"esnext"}),
            ScriptTarget::EsNext,
            Some("lib.esnext.full.d.ts"),
        ),
        (
            json!({"lib":["es5"]}),
            ScriptTarget::Es2025,
            Some("lib.es5.d.ts"),
        ),
        (json!({"lib":[]}), ScriptTarget::Es2025, None),
        (json!({"noLib":true}), ScriptTarget::Es2025, None),
    ] {
        let program = config_program(&configured);
        assert_eq!(program.options().target, target, "{configured}");
        assert!(!program.options().no_check);
        let libraries = program
            .source_files()
            .iter()
            .filter(|source| source.is_default_library)
            .collect::<Vec<_>>();
        if let Some(library) = library {
            let suffix = format!("/{library}");
            assert!(
                libraries
                    .iter()
                    .any(|source| source.file_name.ends_with(&suffix)),
                "{configured}"
            );
            assert!(
                program.diagnostics().is_empty(),
                "{configured}: {:?}",
                program.diagnostics()
            );
        } else {
            assert!(libraries.is_empty(), "{configured}");
        }
        if let Some(libraries) = configured.get("lib") {
            assert_eq!(
                serde_json::to_value(&program.options().lib).unwrap(),
                *libraries
            );
        }
        if configured.get("noLib").and_then(Value::as_bool) == Some(true) {
            assert!(program.options().no_lib);
        }
        assert!(
            !libraries
                .iter()
                .any(|source| source.file_name.ends_with("/lib.es2025.full.d.ts")),
            "{configured}"
        );
    }
}
