//! PORT: not in Go. Issue #50: off Linux and Windows, Go's realpath is
//! `filepath.EvalSymlinks`, which keeps the caller's spelling of each part that
//! is not a link. The port used libc `realpath(3)`, which on macOS gives the
//! stored case. So with the project path typed in another case than on disk,
//! a file reached through a workspace link got a second spelling, and the port
//! reported TS1261 where Go reports nothing.
//!
//! The tests run the issue's npm workspace through `tsgo`. They need a
//! case-insensitive temp dir (macOS APFS by default) and return at once on a
//! case-sensitive one. On Linux Go's realpath reads /proc/self/fd, so the
//! file is empty there.
#![cfg(not(any(target_os = "linux", windows)))]

use std::path::{Path, PathBuf};
use std::process::Command;

/// The issue's workspace `<base>/Work/Mono` under a new temp dir `<base>`:
/// `packages/app` imports `@acme/lib`, and `node_modules/@acme/lib` is a link
/// with the text `lib_link`. None when the temp dir is case-sensitive.
fn workspace(name: &str, lib_link: &str) -> Option<PathBuf> {
    let base = std::fs::canonicalize(std::env::temp_dir())
        .unwrap()
        .join(format!("ts_goport_{name}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let r = base.join("Work/Mono");
    for dir in ["packages/app/src", "packages/lib/src", "node_modules/@acme"] {
        std::fs::create_dir_all(r.join(dir)).unwrap();
    }
    let files = [
        (
            "packages/lib/package.json",
            r#"{"name":"@acme/lib","version":"1.0.0","types":"src/index.ts"}"#,
        ),
        (
            "packages/lib/src/index.ts",
            "export const greet = (n: string) => `hi ${n}`;\n",
        ),
        (
            "packages/app/package.json",
            r#"{"name":"@acme/app","version":"1.0.0"}"#,
        ),
        (
            "packages/app/src/main.ts",
            "import { greet } from \"@acme/lib\";\nexport const s: string = greet(\"x\");\n",
        ),
        (
            "tsconfig.json",
            r#"{"compilerOptions":{"strict":true,"module":"nodenext","noEmit":true},"include":["packages/*/src"]}"#,
        ),
    ];
    for (file, text) in files {
        std::fs::write(r.join(file), text).unwrap();
    }
    std::os::unix::fs::symlink(lib_link, r.join("node_modules/@acme/lib")).unwrap();
    std::os::unix::fs::symlink("../../packages/app", r.join("node_modules/@acme/app")).unwrap();
    if !base.join("work/mono").exists() {
        let _ = std::fs::remove_dir_all(&base);
        return None;
    }
    Some(base)
}

/// Runs `tsgo` in `cwd` (also its `PWD`, as a shell sets it) and returns the
/// exit code and stdout.
fn tsgo(cwd: &Path, args: &[&str]) -> (Option<i32>, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(args)
        .current_dir(cwd)
        .env("PWD", cwd)
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    (output.status.code(), stdout)
}

// The issue's repro: `tsc -p mono` in `Work` when the folder is `Mono`.
#[test]
fn project_path_in_other_case_through_workspace_link() {
    let Some(base) = workspace("realpath_case", "../../packages/lib") else {
        return;
    };
    let work = base.join("Work");
    assert_eq!(tsgo(&work, &["-p", "mono"]), (Some(0), String::new()));

    // The resolver's real path keeps the typed "mono".
    let (code, trace) = tsgo(&work, &["-p", "mono", "--traceResolution"]);
    let mono = work.join("mono");
    let mono = mono.to_str().unwrap();
    let line = format!(
        "Resolving real path for '{mono}/node_modules/@acme/lib/src/index.ts', result '{mono}/packages/lib/src/index.ts'."
    );
    assert_eq!(code, Some(0));
    assert!(trace.lines().any(|l| l == line), "{trace}");
    let _ = std::fs::remove_dir_all(&base);
}

// The issue's reverse case: the link text is `../../packages/Lib` and the
// folder is `lib`. Go keeps the link's spelling, so the two names of the file
// differ in case and Go reports TS1261.
#[test]
fn link_text_in_other_case() {
    let Some(base) = workspace("realpath_link_case", "../../packages/Lib") else {
        return;
    };
    let (code, out) = tsgo(&base.join("Work"), &["-p", "Mono"]);
    assert_eq!(code, Some(2), "{out}");
    assert!(
        out.contains("error TS1261: Already included file name"),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&base);
}
