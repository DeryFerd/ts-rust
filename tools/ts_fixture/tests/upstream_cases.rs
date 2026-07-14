use std::{env, fs};

use ts_fixture::{Case, discover_upstream_manifest};

#[test]
fn parses_all_available_upstream_compiler_cases() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let manifest = discover_upstream_manifest(repository.as_ref())
        .unwrap_or_else(|error| panic!("failed to discover upstream compiler oracle: {error}"));
    let mut parsed = 0;
    let mut parsed_units = 0;
    let mut invalid_utf8 = 0;
    for suite in manifest.suites {
        for case_manifest in suite.cases {
            let path = &case_manifest.path;
            let bytes = fs::read(path).unwrap_or_else(|error| {
                panic!("failed to read upstream case {}: {error}", path.display())
            });
            if std::str::from_utf8(&bytes).is_err() {
                invalid_utf8 += 1;
            }
            let case = Case::parse(path, bytes).unwrap_or_else(|error| {
                panic!("failed to parse upstream case {}: {error}", path.display())
            });
            for unit in &case.units {
                let _ = ts_parser::parse_source_file(unit.source_text.as_scannable_str());
                parsed_units += 1;
            }
            parsed += 1;
        }
    }
    assert!(
        parsed > 12_000,
        "expected the initialized TypeScript corpus"
    );
    assert!(
        invalid_utf8 > 0,
        "expected invalid-UTF-8 scanner fixtures to remain visible"
    );
    assert!(
        parsed_units >= parsed,
        "expected at least one parsed source unit per fixture"
    );
}
