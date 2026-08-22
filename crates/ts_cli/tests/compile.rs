use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

const FALLBACK_ORACLE: &str = "/home/theo/.local/bin/tsgo-oracle";
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(name: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("tsgo-cli-{name}-{}-{sequence}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(program: &str, directory: &Path, arguments: &[&str]) -> Output {
    Command::new(program)
        .args(arguments)
        .current_dir(directory)
        .output()
        .unwrap()
}

fn assert_matches_oracle(directory: &Path, arguments: &[&str]) {
    let actual = run(env!("CARGO_BIN_EXE_tsgo"), directory, arguments);
    let Some(oracle) = std::env::var_os("TS_GO_ORACLE")
        .map(PathBuf::from)
        .filter(|path| path.is_file())
        .or_else(|| {
            Path::new(FALLBACK_ORACLE)
                .is_file()
                .then(|| FALLBACK_ORACLE.into())
        })
    else {
        return;
    };
    let expected = run(&oracle.to_string_lossy(), directory, arguments);
    assert_eq!(
        actual.status.code(),
        expected.status.code(),
        "arguments: {arguments:?}"
    );
    assert_eq!(actual.stdout, expected.stdout, "arguments: {arguments:?}");
    assert_eq!(actual.stderr, expected.stderr, "arguments: {arguments:?}");
}

fn oracle_path() -> Option<PathBuf> {
    std::env::var_os("TS_GO_ORACLE")
        .map(PathBuf::from)
        .filter(|path| path.is_file())
        .or_else(|| {
            Path::new(FALLBACK_ORACLE)
                .is_file()
                .then(|| FALLBACK_ORACLE.into())
        })
}

fn write_minimal_emit_corpus(directory: &Path) {
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(
        directory.join("src/dep.ts"),
        concat!(
            "export interface User { name: string }\n",
            "export const makeUser = (user: User): User => user;\n",
        ),
    )
    .unwrap();
    fs::write(
        directory.join("src/main.ts"),
        concat!(
            "import { type User, makeUser } from './dep.js';\n",
            "export interface Result<T> { value: T }\n",
            "export const result = makeUser({ name: 'Ada' } satisfies User);\n",
        ),
    )
    .unwrap();
    fs::write(
        directory.join("src/view.tsx"),
        concat!(
            "type Props = { label: string };\n",
            "export const View = ({ label }: Props) => <section>{label}</section>;\n",
        ),
    )
    .unwrap();
    fs::write(
        directory.join("src/legacy.js"),
        "export const doubled = [1, 2].map((value) => value * 2);\n",
    )
    .unwrap();
    fs::write(
        directory.join("src/widget.jsx"),
        "export const Widget = () => <div data-ok />;\n",
    )
    .unwrap();
}

#[test]
fn direct_file_no_emit_matches_oracle() {
    let directory = TestDirectory::new("direct");
    fs::write(directory.0.join("main.ts"), "const answer: number = 42;\n").unwrap();
    assert_matches_oracle(
        &directory.0,
        &["main.ts", "--ignoreConfig", "--noEmit", "--pretty", "false"],
    );
}

#[test]
fn no_emit_on_error_skips_output_and_uses_status_one() {
    let directory = TestDirectory::new("no-emit-on-error");
    fs::write(directory.0.join("main.ts"), "const answer: string = 42;\n").unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmitOnError",
            "--noLib",
            "--pretty",
            "false",
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(!directory.0.join("main.js").exists());
}

#[test]
fn project_no_emit_matches_oracle() {
    let directory = TestDirectory::new("project");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"compilerOptions":{"target":"esnext"},"files":["main.ts"]}"#,
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "--project",
            "tsconfig.json",
            "--noEmit",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn no_arguments_compile_the_implicit_project_like_the_oracle() {
    let directory = TestDirectory::new("implicit-project");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"compilerOptions":{"noEmit":true},"files":["main.ts"]}"#,
    )
    .unwrap();

    assert_matches_oracle(&directory.0, &[]);
}

#[test]
fn side_effect_import_diagnostics_match_oracle_defaults_and_overrides() {
    let directory = TestDirectory::new("side-effect-imports");
    fs::write(
        directory.0.join("main.ts"),
        "import './missing-style.css';\nimport './missing-module';\n",
    )
    .unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noEmit":true}}"#,
    )
    .unwrap();

    assert_matches_oracle(
        &directory.0,
        &["main.ts", "--ignoreConfig", "--noEmit", "--pretty", "false"],
    );
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--noUncheckedSideEffectImports",
            "false",
            "--pretty",
            "false",
        ],
    );
    assert_matches_oracle(
        &directory.0,
        &["--project", "tsconfig.json", "--pretty", "false"],
    );

    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"noEmit":true,"noUncheckedSideEffectImports":false}}"#,
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &["--project", "tsconfig.json", "--pretty", "false"],
    );
}

#[test]
fn response_files_match_oracle_quoting_quiet_and_read_diagnostics() {
    let directory = TestDirectory::new("response-files");
    fs::write(
        directory.0.join("with spaces.ts"),
        "const value: string = 1;\n",
    )
    .unwrap();
    fs::write(
        directory.0.join("quoted.rsp"),
        "--ignoreConfig --noEmit --pretty false \"with spaces.ts\"",
    )
    .unwrap();
    fs::write(
        directory.0.join("utf8-bom.rsp"),
        "\u{feff}--ignoreConfig --noEmit --pretty false \"with spaces.ts\"",
    )
    .unwrap();
    let mut utf16 = vec![0xff, 0xfe];
    for unit in "--ignoreConfig --noEmit --pretty false \"with spaces.ts\"".encode_utf16() {
        utf16.extend_from_slice(&unit.to_le_bytes());
    }
    fs::write(directory.0.join("utf16.rsp"), utf16).unwrap();
    fs::write(directory.0.join("quiet.rsp"), "--quiet --wat\n").unwrap();
    fs::write(
        directory.0.join("unterminated.rsp"),
        "--ignoreConfig \"with spaces.ts",
    )
    .unwrap();

    for arguments in [
        &["@quoted.rsp"][..],
        &["@utf8-bom.rsp"][..],
        &["@utf16.rsp"][..],
        &["@quiet.rsp"][..],
        &["@missing.rsp"][..],
        &["@unterminated.rsp"][..],
    ] {
        assert_matches_oracle(&directory.0, arguments);
    }
}

#[test]
fn common_compiler_options_match_oracle() {
    let directory = TestDirectory::new("common-options");
    fs::create_dir_all(directory.0.join("src")).unwrap();
    fs::write(
        directory.0.join("src/main.ts"),
        "export const answer: number = 42;\n",
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "src/main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--target",
            "es2022",
            "--module",
            "esnext",
            "--moduleResolution",
            "bundler",
            "--jsx",
            "react-jsx",
            "--outDir",
            "dist",
            "--rootDir",
            "src",
            "--declaration",
            "--sourceMap",
            "--allowJs",
            "--checkJs",
            "--strict",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn compiler_option_aliases_match_oracle() {
    let directory = TestDirectory::new("option-aliases");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "-t",
            "es2022",
            "-m",
            "esnext",
            "-d",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn extended_compiler_options_match_oracle() {
    let directory = TestDirectory::new("extended-options");
    fs::write(
        directory.0.join("main.ts"),
        "interface User { name?: string }\nconst user: User = {};\n",
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--exactOptionalPropertyTypes",
            "--allowArbitraryExtensions",
            "--allowImportingTsExtensions",
            "--removeComments",
            "--noImplicitThis",
            "false",
            "--noUncheckedIndexedAccess",
            "--noUncheckedSideEffectImports",
            "--useDefineForClassFields",
            "false",
            "--moduleResolution",
            "bundler",
            "--customConditions",
            "browser,development",
            "--moduleSuffixes",
            ".native,.ios",
            "--lib",
            "es2022,dom",
            "--typeRoots",
            "./types,./vendor/types",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn numeric_compiler_options_match_oracle() {
    let directory = TestDirectory::new("numeric-options");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    for value in ["0", "2", "+2"] {
        assert_matches_oracle(
            &directory.0,
            &[
                "main.ts",
                "--ignoreConfig",
                "--noCheck",
                "--noEmit",
                "--maxNodeModuleJsDepth",
                value,
                "--pretty",
                "false",
            ],
        );
    }
}

#[test]
fn invalid_numeric_compiler_options_match_oracle() {
    let directory = TestDirectory::new("invalid-numeric-options");
    for arguments in [
        &["--maxNodeModuleJsDepth"][..],
        &["--maxNodeModuleJsDepth", "nope"][..],
        &["--maxNodeModuleJsDepth", "2.5"][..],
        &["--maxNodeModuleJsDepth", "-1"][..],
    ] {
        assert_matches_oracle(&directory.0, arguments);
    }
}

#[test]
fn quiet_mode_matches_oracle_for_compiler_and_command_errors() {
    let directory = TestDirectory::new("quiet-mode");
    fs::write(directory.0.join("main.ts"), "const answer: string = 42;\n").unwrap();
    for arguments in [
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--quiet",
            "--pretty",
            "false",
        ][..],
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "-q",
            "--pretty",
            "false",
        ][..],
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--quiet",
            "false",
            "--pretty",
            "false",
        ][..],
        &["--quiet", "--wat"][..],
        &["--wat", "--quiet"][..],
        &["--quiet", "--project", "missing.json", "--pretty", "false"][..],
        &["--build", "--quiet", "missing.json", "--pretty", "false"][..],
    ] {
        assert_matches_oracle(&directory.0, arguments);
    }
}

#[test]
fn missing_explicit_project_diagnostics_match_oracle() {
    let directory = TestDirectory::new("missing-project");
    fs::create_dir_all(directory.0.join("without-config")).unwrap();
    for arguments in [
        &["--project", "missing.json", "--pretty", "false"][..],
        &["--project", "without-config", "--pretty", "false"][..],
        &[
            "--project",
            "./without-config/../missing.json",
            "--pretty",
            "false",
        ][..],
    ] {
        assert_matches_oracle(&directory.0, arguments);
    }
}

#[test]
fn list_files_only_matches_oracle_and_skips_checking_and_emit() {
    let directory = TestDirectory::new("list-files-only");
    fs::write(directory.0.join("main.ts"), "const answer: string = 42;\n").unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noLib",
            "--listFilesOnly",
            "--pretty",
            "false",
        ],
    );
    assert!(!directory.0.join("main.js").exists());
}

#[test]
fn list_emitted_files_matches_oracle() {
    let directory = TestDirectory::new("list-emitted-files");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noCheck",
            "--target",
            "esnext",
            "--module",
            "esnext",
            "--outDir",
            "dist",
            "--listEmittedFiles",
            "--pretty",
            "false",
        ],
    );
    assert!(directory.0.join("dist/main.js").is_file());
}

#[test]
fn command_line_option_diagnostics_match_oracle() {
    let directory = TestDirectory::new("option-diagnostics");
    for arguments in [
        &["--project"][..],
        &["-p"][..],
        &["--lib"][..],
        &["--help", "--wat"][..],
        &["--version", "--wat"][..],
        &["--force"][..],
        &["--dry"][..],
        &["--clean"][..],
        &["--pretty=false"][..],
        &["--build", "--wat"][..],
        &["--build", "--pretty=false"][..],
        &["--build", "--listFilesOnly"][..],
        &["--build", "--clean", "--watch"][..],
        &["--build", "--clean", "--force"][..],
        &["--build", "--watch", "--dry"][..],
    ] {
        assert_matches_oracle(&directory.0, arguments);
    }
}

#[test]
fn control_flow_options_match_oracle() {
    let directory = TestDirectory::new("control-flow-options");
    fs::write(
        directory.0.join("main.ts"),
        concat!(
            "function choose(value: boolean) { if (value) return 1; }\n",
            "function cases(value: number) { switch (value) { case 1: value++; case 2: break; } }\n",
            "function unreachable() { return; const after = 1; }\n",
            "try { throw 1; } catch (caught) { caught.toFixed(); }\n",
        ),
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noEmit",
            "--noImplicitReturns",
            "--noFallthroughCasesInSwitch",
            "--allowUnreachableCode",
            "false",
            "--useUnknownInCatchVariables",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn project_and_files_conflict_matches_oracle() {
    let directory = TestDirectory::new("project-conflict");
    fs::write(directory.0.join("main.ts"), "const value = 1;\n").unwrap();
    fs::write(directory.0.join("tsconfig.json"), "{}").unwrap();
    assert_matches_oracle(
        &directory.0,
        &["main.ts", "--project", "tsconfig.json", "--pretty", "false"],
    );
}

#[test]
fn explicit_file_with_config_matches_oracle() {
    let directory = TestDirectory::new("config-bypass");
    fs::write(directory.0.join("main.ts"), "const value = 1;\n").unwrap();
    fs::write(directory.0.join("tsconfig.json"), "{}").unwrap();
    assert_matches_oracle(&directory.0, &["main.ts", "--noEmit", "--pretty", "false"]);
}

#[test]
fn emits_direct_file() {
    let directory = TestDirectory::new("emit-direct");
    fs::write(directory.0.join("main.ts"), "const answer: number = 42;\n").unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["main.ts", "--ignoreConfig", "--pretty", "false"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("main.js")).unwrap();
    assert!(javascript.contains("answer"));
    assert!(!javascript.contains(": number"));
}

#[test]
fn direct_file_preserves_ecmascript_modules_by_default() {
    let directory = TestDirectory::new("emit-default-module");
    fs::write(
        directory.0.join("main.ts"),
        "export const answer: number = 42;\n",
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--target",
            "es2015",
            "--pretty",
            "false",
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("main.js")).unwrap();
    assert!(
        javascript.contains("export const answer = 42;"),
        "{javascript}"
    );
    assert!(!javascript.contains("exports.answer"), "{javascript}");
}

#[test]
fn direct_file_transforms_explicit_commonjs_modules() {
    let directory = TestDirectory::new("emit-commonjs-module");
    fs::write(
        directory.0.join("main.ts"),
        "export const answer: number = 42;\n",
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--target",
            "es2015",
            "--module",
            "commonjs",
            "--pretty",
            "false",
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("main.js")).unwrap();
    assert!(javascript.contains("exports.answer = 42;"), "{javascript}");
    assert!(!javascript.contains("export const answer"), "{javascript}");
}

#[test]
fn creates_project_output_directory() {
    let directory = TestDirectory::new("emit-project");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"compilerOptions":{"outDir":"dist"},"files":["main.ts"]}"#,
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["--project", "tsconfig.json", "--pretty", "false"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("dist/main.js")).unwrap();
    assert!(
        javascript.contains("export var answer = 42;"),
        "{javascript}"
    );
    assert!(!javascript.contains("exports.answer"), "{javascript}");
}

#[test]
fn command_line_options_override_project_options() {
    let directory = TestDirectory::new("project-overrides");
    fs::write(directory.0.join("main.ts"), "export const answer = 42;\n").unwrap();
    fs::write(
        directory.0.join("tsconfig.json"),
        r#"{"files":["main.ts"],"compilerOptions":{"target":"es5","outDir":"original"}}"#,
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &[
            "--project",
            "tsconfig.json",
            "--target",
            "es2022",
            "--module",
            "esnext",
            "--moduleResolution",
            "node10",
            "--outDir",
            "override",
            "--declaration",
            "--sourceMap",
            "--pretty",
            "false",
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let javascript = fs::read_to_string(directory.0.join("override/main.js")).unwrap();
    assert!(javascript.contains("const answer"));
    assert!(directory.0.join("override/main.js.map").is_file());
    assert!(directory.0.join("override/main.d.ts").is_file());
    assert!(!directory.0.join("original/main.js").exists());
}

#[test]
fn no_check_skips_semantic_diagnostics_and_emits() {
    let directory = TestDirectory::new("no-check");
    fs::write(
        directory.0.join("main.ts"),
        "import { missing } from './absent'; const value: string = 1;\n",
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "main.ts",
            "--ignoreConfig",
            "--noCheck",
            "--pretty",
            "false",
        ],
    );
    assert!(directory.0.join("main.js").is_file());
}

#[test]
fn minimal_no_check_emit_matches_oracle_bytes_for_all_four_source_kinds() {
    let Some(oracle) = oracle_path() else {
        return;
    };
    let actual_directory = TestDirectory::new("minimal-emit-actual");
    let oracle_directory = TestDirectory::new("minimal-emit-oracle");
    write_minimal_emit_corpus(&actual_directory.0);
    write_minimal_emit_corpus(&oracle_directory.0);
    let arguments = [
        "src/dep.ts",
        "src/main.ts",
        "src/view.tsx",
        "src/legacy.js",
        "src/widget.jsx",
        "--ignoreConfig",
        "--noCheck",
        "--target",
        "esnext",
        "--module",
        "esnext",
        "--jsx",
        "preserve",
        "--allowJs",
        "--outDir",
        "out",
        "--pretty",
        "false",
    ];
    let actual = run(env!("CARGO_BIN_EXE_tsgo"), &actual_directory.0, &arguments);
    let expected = run(&oracle.to_string_lossy(), &oracle_directory.0, &arguments);
    assert_eq!(actual.status.code(), expected.status.code());
    assert_eq!(actual.stdout, expected.stdout);
    assert_eq!(actual.stderr, expected.stderr);
    for relative in [
        "out/dep.js",
        "out/main.js",
        "out/view.jsx",
        "out/legacy.js",
        "out/widget.jsx",
    ] {
        assert_eq!(
            fs::read(actual_directory.0.join(relative)).unwrap(),
            fs::read(oracle_directory.0.join(relative)).unwrap(),
            "emit mismatch for {relative}",
        );
    }
}

#[test]
fn minimal_syntax_diagnostics_match_oracle_for_all_four_source_kinds() {
    let directory = TestDirectory::new("minimal-syntax");
    fs::write(directory.0.join("bad.ts"), "const value: number = ;\n").unwrap();
    fs::write(
        directory.0.join("bad.tsx"),
        "const view = <section></article>;\n",
    )
    .unwrap();
    fs::write(directory.0.join("bad.js"), "const value = ;\n").unwrap();
    fs::write(
        directory.0.join("bad.jsx"),
        "const view = <section></article>;\n",
    )
    .unwrap();
    assert_matches_oracle(
        &directory.0,
        &[
            "bad.ts",
            "bad.tsx",
            "bad.js",
            "bad.jsx",
            "--ignoreConfig",
            "--noCheck",
            "--noEmit",
            "--allowJs",
            "--jsx",
            "preserve",
            "--pretty",
            "false",
        ],
    );
}

#[test]
fn minimal_no_check_emit_runs_in_node() {
    let directory = TestDirectory::new("minimal-runtime");
    fs::write(
        directory.0.join("runtime.ts"),
        concat!(
            "const values: number[] = [1, 2, 3];\n",
            "console.log(values.map((value) => value * 2).join(','));\n",
        ),
    )
    .unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &[
            "runtime.ts",
            "--ignoreConfig",
            "--noCheck",
            "--target",
            "esnext",
            "--module",
            "esnext",
            "--pretty",
            "false",
        ],
    );
    assert!(output.status.success(), "{output:?}");
    let runtime = run("node", &directory.0, &["runtime.js"]);
    assert!(runtime.status.success(), "{runtime:?}");
    assert_eq!(runtime.stdout, b"2,4,6\n");
}

#[test]
fn pretty_formats_diagnostics() {
    let directory = TestDirectory::new("pretty");
    fs::write(directory.0.join("main.ts"), "const value: string = 1;\n").unwrap();
    let output = run(
        env!("CARGO_BIN_EXE_tsgo"),
        &directory.0,
        &["main.ts", "--ignoreConfig", "--noEmit", "--pretty", "true"],
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.windows(2).any(|bytes| bytes == b"\x1b["));
}

#[test]
fn semantic_parity_corpus_matches_oracle() {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/semantic-parity");
    let mut names = fs::read_dir(&corpus)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .filter(|name| {
            Path::new(name)
                .extension()
                .is_some_and(|extension| extension.eq_ignore_ascii_case("ts"))
        })
        .collect::<Vec<_>>();
    names.sort();
    assert!(!names.is_empty());
    let directory = TestDirectory::new("semantic-parity");
    for name in names {
        fs::copy(corpus.join(&name), directory.0.join(&name)).unwrap();
        assert_matches_oracle(
            &directory.0,
            &[
                &name,
                "--ignoreConfig",
                "--noEmit",
                "--strict",
                "--pretty",
                "false",
            ],
        );
    }
}
