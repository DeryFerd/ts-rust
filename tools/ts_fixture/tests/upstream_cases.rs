use std::{env, fs, path::Path};

use ts_fixture::Case;

#[test]
fn parses_all_available_upstream_compiler_cases() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let roots = [
        Path::new(&repository).join("testdata/tests/cases/compiler"),
        Path::new(&repository).join("testdata/tests/cases/conformance"),
        Path::new(&repository).join("_submodules/TypeScript/tests/cases/compiler"),
        Path::new(&repository).join("_submodules/TypeScript/tests/cases/conformance"),
    ];
    let mut parsed = 0;
    let mut invalid_utf8 = 0;
    for root in roots {
        visit(&root, &mut |path| {
            let bytes = fs::read(path).unwrap_or_else(|error| {
                panic!("failed to read upstream case {}: {error}", path.display())
            });
            if std::str::from_utf8(&bytes).is_err() {
                invalid_utf8 += 1;
            }
            Case::parse(path, bytes).unwrap_or_else(|error| {
                panic!("failed to parse upstream case {}: {error}", path.display())
            });
            parsed += 1;
        });
    }
    assert!(
        parsed > 12_000,
        "expected the initialized TypeScript corpus"
    );
    assert!(
        invalid_utf8 > 0,
        "expected invalid-UTF-8 scanner fixtures to remain visible"
    );
}

fn visit(root: &Path, callback: &mut impl FnMut(&Path)) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    for entry in entries {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            visit(&path, callback);
        } else if matches!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("ts" | "tsx" | "js" | "jsx")
        ) {
            callback(&path);
        }
    }
}
