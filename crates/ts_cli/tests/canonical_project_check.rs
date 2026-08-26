use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct ProjectDirectory(PathBuf);

impl ProjectDirectory {
    fn new(files: &[(&str, &str)]) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "tsgo-canonical-project-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        let directory = Self(path);
        for (name, source) in files {
            let path = directory.0.join(name);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, source).unwrap();
        }
        directory
    }

    fn run(&self, arguments: &[&str]) -> Output {
        let before = project_contents(&self.0);
        let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
            .args(arguments)
            .current_dir(&self.0)
            .output()
            .unwrap();
        assert_eq!(
            project_contents(&self.0),
            before,
            "command wrote project files"
        );
        output
    }
}

impl Drop for ProjectDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn project_contents(root: &Path) -> BTreeMap<PathBuf, Option<Vec<u8>>> {
    let mut contents = BTreeMap::new();
    let mut directories = vec![root.to_path_buf()];
    while let Some(directory) = directories.pop() {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            let content = if path.is_dir() {
                directories.push(path.clone());
                None
            } else {
                Some(fs::read(&path).unwrap())
            };
            contents.insert(path.strip_prefix(root).unwrap().to_path_buf(), content);
        }
    }
    contents
}

#[test]
fn canonical_check_accepts_config_files_and_directories_without_emitting() {
    let directory = ProjectDirectory::new(&[
        (
            "config/base.json",
            r#"{
                "compilerOptions": {
                    "module":"esnext","moduleResolution":"bundler","strict":true,
                    "lib":["es5"],"types":[],"skipLibCheck":true,
                    "declaration":true,"sourceMap":true,"incremental":true,
                    "rootDir":"../app/src","outDir":"../out"
                }
            }"#,
        ),
        (
            "app/tsconfig.json",
            r#"{"extends":"../config/base.json","files":["src/main.ts"]}"#,
        ),
        (
            "app/src/main.ts",
            "import { value } from './values';\nexport const copy: number = value;\n",
        ),
        (
            "app/src/values.d.ts",
            "export declare const value: number;\n",
        ),
    ]);

    for project in ["app/tsconfig.json", "app"] {
        let output = directory.run(&["--check-canonical", project]);
        assert_eq!(output.status.code(), Some(0));
        assert!(
            output.stdout.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn canonical_check_formats_source_diagnostics_and_skips_outputs() {
    let directory = ProjectDirectory::new(&[
        (
            "tsconfig.json",
            r#"{
                "files":["main.ts"],
                "compilerOptions":{
                    "lib":["es5"],"types":[],"strict":true,
                    "declaration":true,"rootDir":".","outDir":"out"
                }
            }"#,
        ),
        (
            "main.ts",
            "const source: number = 1;\nconst value: string = source;\n",
        ),
    ]);

    let output = directory.run(&["--check-canonical", "."]);

    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "main.ts(2,7): error TS2322: Type 'number' is not assignable to type 'string'.\n"
    );
    assert!(output.stderr.is_empty());
}

#[test]
fn canonical_check_reports_missing_project_paths_and_config_files() {
    let directory = ProjectDirectory::new(&[]);
    for (project, code) in [("missing.json", 5058), (".", 5081)] {
        let output = directory.run(&["--check-canonical", project]);

        assert_eq!(output.status.code(), Some(1));
        assert!(String::from_utf8_lossy(&output.stdout).starts_with(&format!("error TS{code}:")));
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn canonical_check_keeps_config_parse_errors() {
    let directory = ProjectDirectory::new(&[("tsconfig.json", "{")]);

    let output = directory.run(&["--check-canonical", "tsconfig.json"]);

    assert_eq!(output.status.code(), Some(1));
    let diagnostics = String::from_utf8(output.stdout).unwrap();
    assert!(diagnostics.contains("tsconfig.json"));
    assert!(diagnostics.contains("error TS1136:"));
    assert!(output.stderr.is_empty());
}

#[test]
fn canonical_check_reports_unsupported_boundaries_without_emitting() {
    for (config, code) in [
        (
            r#"{"files":[],"references":[{"path":"./missing"}]}"#,
            "M00.PROJECT_REFERENCES",
        ),
        (
            r#"{
                "files":["settings.json"],
                "compilerOptions":{
                    "module":"esnext","moduleResolution":"bundler",
                    "resolveJsonModule":true,"lib":["es5"],"types":[],"outDir":"out"
                }
            }"#,
            "C00.SOURCE_KIND",
        ),
    ] {
        let directory = ProjectDirectory::new(&[
            ("tsconfig.json", config),
            ("settings.json", r#"{"enabled":true}"#),
        ]);

        let output = directory.run(&["--check-canonical", "."]);

        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).starts_with(&format!("error {code}:")));
    }
}

#[test]
fn canonical_check_reports_no_check_as_unverified() {
    let directory = ProjectDirectory::new(&[
        (
            "base.json",
            r#"{
                "compilerOptions":{
                    "noCheck":true,"lib":["es5"],"types":[],"declaration":true,"outDir":"out"
                }
            }"#,
        ),
        (
            "tsconfig.json",
            r#"{"extends":"./base.json","files":["main.ts"]}"#,
        ),
        ("main.ts", "const value: string = 1;\n"),
    ]);

    let output = directory.run(&["--check-canonical", "."]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "error: canonical checking was skipped because noCheck is enabled.\n"
    );
}

#[test]
fn canonical_check_requires_exactly_one_project_path() {
    let directory = ProjectDirectory::new(&[]);
    for arguments in [
        &["--check-canonical"][..],
        &["--check-canonical", ".", "extra"][..],
    ] {
        let output = directory.run(arguments);

        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert_eq!(
            String::from_utf8(output.stderr).unwrap(),
            "error: --check-canonical requires exactly one project path\n"
        );
    }
}
