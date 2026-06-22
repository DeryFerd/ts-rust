use std::{fs, path::PathBuf};

#[test]
fn parses_all_bundled_declaration_libraries_without_diagnostics() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../ts_bundled/libs");
    let mut paths: Vec<_> = fs::read_dir(&root)
        .expect("read bundled library directory")
        .map(|entry| entry.expect("read bundled library entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "ts"))
        .collect();
    paths.sort();

    let mut failures = Vec::new();
    for path in &paths {
        let source = fs::read_to_string(path).expect("read bundled declaration library");
        let result = ts_parser::parse_source_file(&source);
        if !result.diagnostics.is_empty() {
            failures.push(format!(
                "{}: {} diagnostics",
                path.file_name().unwrap().to_string_lossy(),
                result.diagnostics.len()
            ));
        }
    }

    assert_eq!(
        paths.len(),
        108,
        "expected every bundled declaration library"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
