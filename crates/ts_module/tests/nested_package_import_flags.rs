use std::{
    io,
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

use serde_json::{Value, json};
use ts_module::{ModuleFormat, ResolutionMode, ResolutionOptions, Resolver};
use ts_vfs::{DirectoryEntries, FileSystem, MemoryFileSystem};

struct ObservedFileSystem {
    inner: MemoryFileSystem,
    calls: AtomicUsize,
    realpaths: Mutex<Vec<String>>,
}

impl ObservedFileSystem {
    fn new(physical_root: &str) -> Self {
        let inner = MemoryFileSystem::new(true);
        for (path, text) in [
            (
                "/app/package.json".to_owned(),
                r##"{"name":"app","type":"module","imports":{"#dep":"pkg","#chain":"#dep","#missing":"missing"}}"##,
            ),
            ("/app/main.ts".to_owned(), ""),
            (
                format!("{physical_root}/pkg/package.json"),
                r#"{"name":"pkg","version":"1.0.0","type":"module","exports":{".":{"import":"./esm.d.mts","require":"./commonjs.d.cts"}}}"#,
            ),
            (
                format!("{physical_root}/pkg/esm.d.mts"),
                "export declare const value: number;",
            ),
            (
                format!("{physical_root}/pkg/commonjs.d.cts"),
                "export declare const value: string;",
            ),
            (
                format!("{physical_root}/host/package.json"),
                r##"{"name":"host","type":"module","imports":{"#relative":"./local.d.ts","#fallback":["missing","./local.d.ts"],"#chainRelative":"#relative"}}"##,
            ),
            (format!("{physical_root}/host/main.ts"), ""),
            (
                format!("{physical_root}/host/local.d.ts"),
                "export declare const local: boolean;",
            ),
        ] {
            inner.write_file(&path, text).unwrap();
        }
        inner.add_directory_link(&format!("{physical_root}/pkg"), "/app/node_modules/pkg");
        inner.add_directory_link(&format!("{physical_root}/host"), "/app/node_modules/host");
        Self {
            inner,
            calls: AtomicUsize::new(0),
            realpaths: Mutex::new(Vec::new()),
        }
    }
}

impl FileSystem for ObservedFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.use_case_sensitive_file_names()
    }

    fn file_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.file_exists(path)
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.directory_exists(path)
    }

    fn realpath(&self, path: &str) -> String {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.realpaths.lock().unwrap().push(path.to_owned());
        self.inner.realpath(path)
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.modified_time(path)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.read_file(path)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        self.inner.write_file(path, contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        self.calls.fetch_add(1, Ordering::Relaxed);
        self.inner.read_directory(path)
    }
}

#[derive(Clone, Copy)]
enum Target {
    Package,
    Local,
    Missing,
}

struct Case {
    name: &'static str,
    specifier: &'static str,
    containing_file: &'static str,
    target: Target,
    nested: bool,
}

const CASES: [Case; 8] = [
    Case {
        name: "direct_pkg",
        specifier: "pkg",
        containing_file: "/app/main.ts",
        target: Target::Package,
        nested: false,
    },
    Case {
        name: "nested_pkg",
        specifier: "#dep",
        containing_file: "/app/main.ts",
        target: Target::Package,
        nested: true,
    },
    Case {
        name: "nested_chain",
        specifier: "#chain",
        containing_file: "/app/main.ts",
        target: Target::Package,
        nested: true,
    },
    Case {
        name: "missing_target",
        specifier: "#missing",
        containing_file: "/app/main.ts",
        target: Target::Missing,
        nested: false,
    },
    Case {
        name: "relative_import_map",
        specifier: "#relative",
        containing_file: "/app/node_modules/host/main.ts",
        target: Target::Local,
        nested: false,
    },
    Case {
        name: "fallback_after_missing",
        specifier: "#fallback",
        containing_file: "/app/node_modules/host/main.ts",
        target: Target::Local,
        nested: false,
    },
    Case {
        name: "nested_relative_map",
        specifier: "#chainRelative",
        containing_file: "/app/node_modules/host/main.ts",
        target: Target::Local,
        nested: true,
    },
    Case {
        name: "direct_relative",
        specifier: "./local.js",
        containing_file: "/app/node_modules/host/main.ts",
        target: Target::Local,
        nested: false,
    },
];

fn expected_result(
    case: &Case,
    physical_root: &str,
    usage: ModuleFormat,
    preserve_symlinks: bool,
) -> (Value, Vec<String>) {
    let (suffix, extension) = match case.target {
        Target::Package if usage == ModuleFormat::Esm => ("pkg/esm.d.mts", ".d.mts"),
        Target::Package => ("pkg/commonjs.d.cts", ".d.cts"),
        Target::Local => ("host/local.d.ts", ".d.ts"),
        Target::Missing => return (Value::Null, Vec::new()),
    };
    let lookup = format!("/app/node_modules/{suffix}");
    let follows = !preserve_symlinks && !case.specifier.starts_with('.');
    let selected = if follows {
        format!("{physical_root}/{suffix}")
    } else {
        lookup.clone()
    };
    let external = !case.nested || selected.contains("/node_modules/");
    let realpaths = if follows {
        vec![lookup.clone()]
    } else {
        Vec::new()
    };
    (
        json!({
            "fileName": selected,
            "lookupFileName": lookup,
            "externalLibraryImport": external,
            "extension": extension,
        }),
        realpaths,
    )
}

fn run_case(
    case: &Case,
    physical_root: &str,
    mode: ResolutionMode,
    usage: ModuleFormat,
    preserve_symlinks: bool,
) -> (Value, Option<String>) {
    let filesystem = ObservedFileSystem::new(physical_root);
    let resolver = Resolver::new(
        &filesystem,
        ResolutionOptions {
            mode,
            preserve_symlinks,
            ..ResolutionOptions::default()
        },
    );
    let result = resolver.resolve_with_mode(case.specifier, case.containing_file, usage);
    let actual = result.resolved.as_ref().map_or(Value::Null, |resolved| {
        json!({
            "fileName": resolved.resolved_file_name,
            "lookupFileName": resolved.original_file_name,
            "externalLibraryImport": resolved.is_external_library_import,
            "extension": resolved.extension.map(ts_path::FileExtension::as_str),
        })
    });
    let calls = filesystem.calls.load(Ordering::Relaxed);
    let realpaths = filesystem.realpaths.lock().unwrap().clone();
    let cached = resolver.resolve_with_mode(case.specifier, case.containing_file, usage);
    assert_eq!(cached, result);
    assert_eq!(filesystem.calls.load(Ordering::Relaxed), calls);
    assert_eq!(result.effective_mode, Some(usage));
    assert!(result.package_json_inputs.as_ref().unwrap().is_complete());
    let (expected, expected_realpaths) =
        expected_result(case, physical_root, usage, preserve_symlinks);
    let failure = if actual == expected && realpaths == expected_realpaths {
        None
    } else {
        Some(format!(
            "{} {mode:?} {usage:?} {physical_root} preserve={preserve_symlinks}: actual={actual}, expected={expected}, realpaths={realpaths:?}, expected_realpaths={expected_realpaths:?}",
            case.name,
        ))
    };
    (
        json!({
            "result": actual,
            "realpathCalls": realpaths,
            "fileSystemCalls": calls,
            "effectiveMode": match usage { ModuleFormat::Esm => "esm", ModuleFormat::CommonJs => "commonjs" },
            "packageInputsDebug": format!("{:?}", result.package_json_inputs),
            "failedLookupsDebug": format!("{:?}", result.failed_lookups),
        }),
        failure,
    )
}

#[test]
fn nested_package_import_flags_match_pinned_go_matrix() {
    let mut failures = Vec::new();
    for (layout, physical_root) in [("outside", "/store"), ("inside", "/store/node_modules")] {
        for (mode_name, mode) in [
            ("node16", ResolutionMode::Node16),
            ("nodenext", ResolutionMode::NodeNext),
            ("bundler", ResolutionMode::Bundler),
        ] {
            for (usage_name, usage) in [
                ("import", ModuleFormat::Esm),
                ("require", ModuleFormat::CommonJs),
            ] {
                for preserve_symlinks in [false, true] {
                    for case in &CASES {
                        let (mut row, failure) =
                            run_case(case, physical_root, mode, usage, preserve_symlinks);
                        row["probe"] = json!("wave134_nested_package_import_flags");
                        row["layout"] = json!(layout);
                        row["mode"] = json!(mode_name);
                        row["usage"] = json!(usage_name);
                        row["preserveSymlinks"] = json!(preserve_symlinks);
                        row["case"] = json!(case.name);
                        row["specifier"] = json!(case.specifier);
                        row["containingFile"] = json!(case.containing_file);
                        println!("{row}");
                        if let Some(failure) = failure {
                            failures.push(failure);
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
