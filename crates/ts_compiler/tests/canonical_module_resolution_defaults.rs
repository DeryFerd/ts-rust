use std::collections::BTreeSet;

use ts_ast::{NodeData, NodeRef};
use ts_compiler::{CanonicalModuleResolutionLookup, Program, ProgramOptionsOverride};
use ts_module::{ModuleFormat, ResolutionMode, Resolver};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

const CONFIG: &str = "/project/tsconfig.json";
const MAIN: &str = "/project/main.ts";
const PUBLIC: &str = "/project/node_modules/pkg/public.d.ts";
const DEVELOPMENT: &str = "/project/node_modules/pkg/development.d.ts";

fn package_filesystem() -> MemoryFileSystem {
    let filesystem = MemoryFileSystem::new(true);
    for (path, text) in [
        (
            MAIN,
            "import { value } from 'pkg';\nconst actual: number = value;\n",
        ),
        (
            "/project/node_modules/pkg/package.json",
            r#"{"name":"pkg","exports":{".":{"development":"./development.d.ts","types":"./public.d.ts"}}}"#,
        ),
        (PUBLIC, "export declare const value: number;"),
        (DEVELOPMENT, "export declare const value: number;"),
        (
            "/project/node_modules/pkg/index.d.ts",
            "export declare const value: string;",
        ),
    ] {
        filesystem.write_file(path, text).unwrap();
    }
    filesystem
}

fn import_specifier(program: &Program, name: &str) -> NodeRef {
    let source = program.source_file(MAIN).unwrap();
    source
        .parse
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::StringLiteral(literal) if literal.text == name)
                .then(|| source.node_ref(node).unwrap())
        })
        .unwrap()
}

fn assert_graph_target(program: &Program, name: &str, expected: Option<&str>) {
    let graph = program.project_graph_snapshot();
    let matches = graph
        .resolutions
        .iter()
        .filter(|resolution| {
            resolution.request.containing_file == MAIN && resolution.request.specifier == name
        })
        .collect::<Vec<_>>();
    let [resolution] = matches.as_slice() else {
        panic!("expected one resolution for {name}: {matches:?}");
    };
    assert_eq!(
        resolution
            .result
            .resolved
            .as_ref()
            .map(|resolved| resolved.resolved_file_name.as_str()),
        expected
    );
    assert_eq!(
        resolution
            .target
            .as_ref()
            .map(|target| target.file_name.as_str()),
        expected
    );
    if let Some(expected) = expected {
        assert!(program.source_file(expected).is_some());
    }
}

fn assert_json_parse_boundary(program: &Program) {
    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected the JSON parse boundary: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(
        diagnostic.file_name.as_deref(),
        Some("/project/settings.json")
    );
    assert_eq!(diagnostic.code, Some(1005));
    assert_eq!(diagnostic.category, ts_diagnostics::Category::Error);
    let range = diagnostic.range.unwrap();
    assert_eq!((range.start.get(), range.end.get()), (10, 11));
    assert_eq!(diagnostic.message, "';' expected.");
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        program
            .source_file("/project/settings.json")
            .unwrap()
            .source_text,
        r#"{"enabled":true}"#
    );
}

fn check_exported_target(filesystem: &MemoryFileSystem, expected: &str) -> Program {
    let (program, checked) = Program::try_from_config_with_canonical_checker_and_queries(
        filesystem,
        CONFIG,
        |program, queries| {
            let specifier = import_specifier(program, "pkg");
            let before = queries.module_resolution(specifier);
            let CanonicalModuleResolutionLookup::Resolved(resolution) = before else {
                panic!("package export did not resolve: {before:?}");
            };
            assert_eq!(
                program
                    .source_file_by_id(resolution.target_file())
                    .unwrap()
                    .file_name,
                expected
            );
            assert!(queries.replay_sources().unwrap().is_empty());
            assert_eq!(queries.module_resolution(specifier), before);
        },
    )
    .unwrap();
    assert_eq!(checked, Some(()));
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(program.options().module, ModuleKind::None);
    assert!(!program.options().module_specified);
    assert_eq!(program.options().module_resolution_configured, None);
    assert_eq!(
        program.options().module_resolution,
        ModuleResolutionKind::Bundler
    );
    assert!(program.options().resolve_json_module);
    assert!(!program.options().resolve_json_module_specified);
    let graph = program.project_graph_snapshot();
    let resolution_options = graph.resolution_options.unwrap();
    assert_eq!(resolution_options.mode, ResolutionMode::Bundler);
    assert!(resolution_options.resolve_json);
    assert_graph_target(&program, "pkg", Some(expected));
    assert!(
        program
            .source_file("/project/node_modules/pkg/index.d.ts")
            .is_none()
    );
    program
}

#[test]
fn canonical_target_only_config_uses_bundler_package_exports() {
    let filesystem = package_filesystem();
    let config = r#"{
        "compilerOptions": {
            "target": "es2015", "lib": ["es2015"], "types": [],
            "strict": true, "skipLibCheck": true, "noEmit": true
        },
        "files": ["main.ts"]
    }"#;
    filesystem.write_file(CONFIG, config).unwrap();
    let program = check_exported_target(&filesystem, PUBLIC);
    assert_eq!(
        program
            .project_graph_snapshot()
            .config
            .unwrap()
            .source_text
            .as_deref(),
        Some(config)
    );
}

#[test]
fn canonical_inherited_resolution_defaults_use_custom_conditions() {
    let filesystem = package_filesystem();
    filesystem
        .write_file(
            "/project/base.json",
            r#"{
                "compilerOptions": {
                    "target": "es2015", "lib": ["es2015"], "types": [],
                    "strict": true, "skipLibCheck": true, "noEmit": true,
                    "customConditions": ["development"]
                }
            }"#,
        )
        .unwrap();
    filesystem
        .write_file(CONFIG, r#"{"extends":"./base.json","files":["main.ts"]}"#)
        .unwrap();
    let program = check_exported_target(&filesystem, DEVELOPMENT);
    assert_eq!(
        program.options().custom_conditions.as_deref(),
        Some(["development".to_owned()].as_slice())
    );
    let resolver = Resolver::new(&filesystem, program.options().module_resolution_options());
    let selected = resolver.resolve("pkg", MAIN);
    assert_eq!(selected.effective_mode, Some(ModuleFormat::Esm));
    assert_eq!(
        selected.resolved.as_ref().unwrap().resolved_file_name,
        DEVELOPMENT
    );
    assert_eq!(resolver.resolve("pkg", MAIN), selected);
}

#[test]
fn canonical_json_graph_defaults_select_files_and_preserve_explicit_false() {
    for configured in [None, Some(false), Some(true)] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(MAIN, "import './settings.json';\n")
            .unwrap();
        filesystem
            .write_file("/project/settings.json", r#"{"enabled":true}"#)
            .unwrap();
        let json_option = configured.map_or_else(String::new, |enabled| {
            format!(",\"resolveJsonModule\":{enabled}")
        });
        filesystem
            .write_file(
                CONFIG,
                &format!(
                    "{{\"compilerOptions\":{{\"target\":\"es2015\",\"noEmit\":true,\"noCheck\":true{json_option}}},\"files\":[\"main.ts\"]}}"
                ),
            )
            .unwrap();
        // This checks JSON resolution only. The canonical checker still rejects JSON sources.
        let mut called = false;
        let (program, checked) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            CONFIG,
            |_, _| called = true,
        )
        .unwrap();
        assert!(!called);
        assert_eq!(checked, None);
        let enabled = configured.unwrap_or(true);
        assert_eq!(program.options().resolve_json_module, enabled);
        assert_eq!(
            program.options().resolve_json_module_specified,
            configured.is_some()
        );
        assert_eq!(program.options().module, ModuleKind::None);
        assert!(!program.options().module_specified);
        let graph = program.project_graph_snapshot();
        let resolution_options = graph.resolution_options.unwrap();
        assert_eq!(resolution_options.mode, ResolutionMode::Bundler);
        assert_eq!(resolution_options.resolve_json, enabled);
        let expected = enabled.then_some("/project/settings.json");
        assert_graph_target(&program, "./settings.json", expected);
        assert_eq!(
            program.source_file("/project/settings.json").is_some(),
            enabled
        );
        assert!(!filesystem.file_exists("/project/settings.d.json.ts"));
        let resolver = Resolver::new(&filesystem, program.options().module_resolution_options());
        let selected = resolver.resolve("./settings.json", MAIN);
        assert_eq!(
            selected
                .resolved
                .as_ref()
                .map(|resolved| resolved.resolved_file_name.as_str()),
            expected
        );
        assert_eq!(resolver.resolve("./settings.json", MAIN), selected);
        if enabled {
            assert_json_parse_boundary(&program);
        } else {
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        }
    }
}

#[test]
fn canonical_removed_resolution_reports_5108_at_the_configured_value() {
    for (name, configured, label) in [
        ("classic", ModuleResolutionKind::Classic, "Classic"),
        ("node10", ModuleResolutionKind::Node10, "node10"),
        ("node", ModuleResolutionKind::Node10, "node10"),
    ] {
        let filesystem = package_filesystem();
        let config = format!(
            "{{\"compilerOptions\":{{\"target\":\"es2015\",\"moduleResolution\":\"{name}\",\"lib\":[\"es2015\"],\"types\":[],\"skipLibCheck\":true,\"noEmit\":true}},\"files\":[\"main.ts\"]}}"
        );
        filesystem.write_file(CONFIG, &config).unwrap();
        let (program, checked) = Program::try_from_config_with_canonical_checker_and_queries(
            &filesystem,
            CONFIG,
            |_, queries| assert!(queries.has_diagnostics()),
        )
        .unwrap();
        assert_eq!(checked, Some(()));
        let [diagnostic] = program.diagnostics() else {
            panic!(
                "expected the removed-option error: {:?}",
                program.diagnostics()
            );
        };
        assert_eq!(diagnostic.code, Some(5108));
        assert_eq!(diagnostic.file_name.as_deref(), Some(CONFIG));
        assert_eq!(
            diagnostic.message,
            format!(
                "Option 'moduleResolution={label}' has been removed. Please remove it from your configuration."
            )
        );
        let range = diagnostic.range.unwrap();
        assert_eq!(
            &config[range.start.get() as usize..range.end.get() as usize],
            format!("\"{name}\"")
        );
        assert_eq!(
            program.options().module_resolution_configured,
            Some(configured)
        );
        assert_eq!(
            program.options().module_resolution,
            ModuleResolutionKind::Bundler
        );
        assert_graph_target(&program, "pkg", Some(PUBLIC));
    }
}

#[test]
fn command_line_bundler_override_removes_only_the_stale_resolution_error() {
    for unknown in [false, true] {
        let filesystem = package_filesystem();
        let unknown_option = if unknown {
            ",\"unknownOption\":true"
        } else {
            ""
        };
        let config = format!(
            "{{\"compilerOptions\":{{\"target\":\"es2015\",\"moduleResolution\":\"node10\",\"noCheck\":true,\"noEmit\":true,\"resolveJsonModule\":false{unknown_option}}},\"files\":[\"main.ts\"]}}"
        );
        filesystem.write_file(CONFIG, &config).unwrap();
        let overrides = CompilerOptions {
            module_resolution: ModuleResolutionKind::Bundler,
            module_resolution_configured: Some(ModuleResolutionKind::Bundler),
            ..CompilerOptions::default()
        };
        // The CLI loader has no canonical query callback. noCheck limits this to config and graph work.
        let program = Program::from_config_with_command_line_options(
            &filesystem,
            CONFIG,
            ProgramOptionsOverride::default(),
            &overrides,
            &BTreeSet::from(["moduleresolution".to_owned()]),
        );
        assert!(program.options().no_check);
        assert_eq!(
            program.options().module_resolution,
            ModuleResolutionKind::Bundler
        );
        assert_eq!(
            program.options().module_resolution_configured,
            Some(ModuleResolutionKind::Bundler)
        );
        assert!(!program.options().resolve_json_module);
        assert!(program.options().resolve_json_module_specified);
        assert_eq!(program.diagnostics().len(), usize::from(unknown));
        if unknown {
            let diagnostic = &program.diagnostics()[0];
            assert_eq!(diagnostic.code, Some(5023));
            assert_eq!(
                diagnostic.message,
                "Unknown compiler option 'unknownOption'."
            );
        }
        assert_graph_target(&program, "pkg", Some(PUBLIC));
        assert_eq!(
            program
                .project_graph_snapshot()
                .config
                .unwrap()
                .source_text
                .as_deref(),
            Some(config.as_str())
        );
    }
}

#[test]
fn command_line_resolution_uses_the_inherited_module_json_default() {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/base.json",
            r#"{"compilerOptions":{"target":"es2015","module":"node20","noCheck":true,"noEmit":true}}"#,
        )
        .unwrap();
    filesystem
        .write_file(CONFIG, r#"{"extends":"./base.json","files":["main.ts"]}"#)
        .unwrap();
    filesystem
        .write_file(MAIN, "import './settings.json';\n")
        .unwrap();
    filesystem
        .write_file("/project/settings.json", r#"{"enabled":true}"#)
        .unwrap();
    let overrides = CompilerOptions {
        module_resolution: ModuleResolutionKind::Node16,
        module_resolution_configured: Some(ModuleResolutionKind::Node16),
        resolve_json_module: false,
        ..CompilerOptions::default()
    };
    let program = Program::from_config_with_command_line_options(
        &filesystem,
        CONFIG,
        ProgramOptionsOverride::default(),
        &overrides,
        &BTreeSet::from(["moduleresolution".to_owned()]),
    );
    assert!(program.options().no_check);
    assert_eq!(program.options().module, ModuleKind::Node20);
    assert!(program.options().module_specified);
    assert_eq!(
        program.options().module_resolution,
        ModuleResolutionKind::Node16
    );
    assert_eq!(
        program.options().module_resolution_configured,
        Some(ModuleResolutionKind::Node16)
    );
    assert!(program.options().resolve_json_module);
    assert!(!program.options().resolve_json_module_specified);
    assert_json_parse_boundary(&program);
    assert_graph_target(&program, "./settings.json", Some("/project/settings.json"));
}

#[test]
fn removed_command_line_resolution_uses_the_null_compiler_options_key() {
    let filesystem = MemoryFileSystem::new(true);
    let config = r#"{"files":["main.ts"],"compilerOptions":null}"#;
    let source = "const value = 1;\n";
    filesystem.write_file(CONFIG, config).unwrap();
    filesystem.write_file(MAIN, source).unwrap();
    let overrides = CompilerOptions {
        module_resolution: ModuleResolutionKind::Bundler,
        module_resolution_configured: Some(ModuleResolutionKind::Node10),
        ..CompilerOptions::default()
    };
    let program = Program::from_config_with_command_line_options(
        &filesystem,
        CONFIG,
        ProgramOptionsOverride::default(),
        &overrides,
        &BTreeSet::from(["moduleresolution".to_owned()]),
    );
    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected the removed-option error: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(diagnostic.code, Some(5108));
    assert_eq!(diagnostic.category, ts_diagnostics::Category::Error);
    assert_eq!(diagnostic.file_name.as_deref(), Some(CONFIG));
    let range = diagnostic.range.unwrap();
    assert_eq!((range.start.get(), range.end.get()), (21, 38));
    assert_eq!(
        &config[range.start.get() as usize..range.end.get() as usize],
        "\"compilerOptions\""
    );
    assert_eq!(
        diagnostic.message,
        "Option 'moduleResolution=node10' has been removed. Please remove it from your configuration."
    );
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        program.options().module_resolution_configured,
        Some(ModuleResolutionKind::Node10)
    );
    assert_eq!(
        program.options().module_resolution,
        ModuleResolutionKind::Bundler
    );
    assert_eq!(program.diagnostic_source_text(CONFIG), Some(config));
    assert_eq!(program.diagnostic_source_text(MAIN), Some(source));
}

#[test]
fn diagnostic_source_text_keeps_the_retained_source_and_exact_config_path() {
    let filesystem = MemoryFileSystem::new(true);
    let source = "export const value = 1;\n";
    let config =
        r#"{"compilerOptions":{"noCheck":true,"noLib":true,"noEmit":true},"files":["main.ts"]}"#;
    filesystem.write_file(MAIN, source).unwrap();
    filesystem.write_file(CONFIG, config).unwrap();
    let program = Program::from_config(&filesystem, CONFIG);
    assert!(
        program.diagnostics().is_empty(),
        "{:?}",
        program.diagnostics()
    );
    assert_eq!(program.source_files().len(), 1);
    assert!(program.source_file(CONFIG).is_none());
    let graph = program.project_graph_snapshot();

    filesystem.write_file(MAIN, "changed source").unwrap();
    filesystem.write_file(CONFIG, "changed config").unwrap();
    filesystem
        .write_file("/other/tsconfig.json", config)
        .unwrap();

    assert_eq!(program.diagnostic_source_text(MAIN), Some(source));
    assert_eq!(program.diagnostic_source_text(CONFIG), Some(config));
    assert_eq!(program.diagnostic_source_text("tsconfig.json"), None);
    assert_eq!(program.diagnostic_source_text("/other/tsconfig.json"), None);
    assert_eq!(program.diagnostic_source_text("/project/missing.ts"), None);
    assert_eq!(program.project_graph_snapshot(), graph);
    assert!(program.source_file(CONFIG).is_none());
}
