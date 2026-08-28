use std::{fs, path::PathBuf};

use ts_core::{TextPos, TextRange};

use crate::{
    Case, CompilationDiagnostic, CompilationDiagnosticCategory, CompilationDiagnosticOrdering,
    FixtureChecker, compile_case_variant, expand_option_matrix, render_error_baseline,
};

// Complete inputs from the pinned TypeScript fixture and accepted Go baseline.
const SOURCE: &str = concat!(
    "// @target: es2015\r\n",
    "// Should fail. Even though the array is contextually typed with { id: number }[], it still\r\n",
    "// has type { foo: string }[], which is not assignable to { id: number }[].\r\n",
    "<{ id: number; }[]>[{ foo: \"s\" }];\r\n",
    "\r\n",
    "// Should succeed, as the {} element causes the type of the array to be {}[]\r\n",
    "<{ id: number; }[]>[{ foo: \"s\" }, {}]; ",
);

const EXPECTED: &str = concat!(
    "arrayCast.ts(3,23): error TS2353: Object literal may only specify known properties, and 'foo' does not exist in type '{ id: number; }'.\r\n",
    "\r\n",
    "\r\n",
    "==== arrayCast.ts (1 errors) ====\r\n",
    "    // Should fail. Even though the array is contextually typed with { id: number }[], it still\r\n",
    "    // has type { foo: string }[], which is not assignable to { id: number }[].\r\n",
    "    <{ id: number; }[]>[{ foo: \"s\" }];\r\n",
    "                          ~~~\r\n",
    "!!! error TS2353: Object literal may only specify known properties, and 'foo' does not exist in type '{ id: number; }'.\r\n",
    "    \r\n",
    "    // Should succeed, as the {} element causes the type of the array to be {}[]\r\n",
    "    <{ id: number; }[]>[{ foo: \"s\" }, {}]; ",
);

#[test]
fn original_array_cast_retains_the_excess_property_diagnostic() {
    let case = Case::parse(
        "_submodules/TypeScript/tests/cases/compiler/arrayCast.ts",
        SOURCE,
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, false).unwrap();
    let actual = render_error_baseline(&case, &compilation.diagnostics);
    retain_artifacts(&case, &actual.text);
    assert!(actual.unsupported_details.is_empty());
    assert_eq!(actual.text, EXPECTED);
    assert_eq!(compilation.diagnostics.len(), 1);
    assert_eq!(compilation.diagnostics[0].code, Some(2353));
}

fn retain_artifacts(case: &Case, actual: &str) {
    let Some(directory) = std::env::var_os("TS_ARRAY_CAST_ARTIFACT_DIR") else {
        return;
    };
    let directory = PathBuf::from(directory);
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("arrayCast.ts"), SOURCE).unwrap();
    fs::write(directory.join("arrayCast.expected.errors.txt"), EXPECTED).unwrap();
    fs::write(directory.join("arrayCast.after.errors.txt"), actual).unwrap();

    let Some(scorecard) = std::env::var_os("TS_ARRAY_CAST_ROOT79_SCORECARD") else {
        return;
    };
    let scorecard: serde_json::Value =
        serde_json::from_slice(&fs::read(scorecard).unwrap()).unwrap();
    let variant = scorecard["variants"]
        .as_array()
        .unwrap()
        .iter()
        .find(|variant| variant["variantKey"] == "v1:2eff8b597fa14fed61672328a7fcffab")
        .unwrap();
    let records = variant["diagnostics"].as_array().unwrap();
    assert_eq!(records.len(), 1);
    let record = &records[0];
    assert_eq!(record["category"], "error");
    assert!(record["relatedInformation"].as_array().unwrap().is_empty());
    let start = u32::try_from(record["range"]["start"].as_u64().unwrap()).unwrap();
    let length = u32::try_from(record["range"]["length"].as_u64().unwrap()).unwrap();
    let diagnostic = CompilationDiagnostic {
        file_name: Some(record["fileName"].as_str().unwrap().to_owned()),
        source_text: Some(case.units[0].source_text.clone()),
        range: Some(TextRange::new(
            TextPos::new(start),
            TextPos::new(start.checked_add(length).unwrap()),
        )),
        code: Some(u32::try_from(record["code"].as_u64().unwrap()).unwrap()),
        category: Some(CompilationDiagnosticCategory::Error),
        message: record["message"].as_str().unwrap().to_owned(),
        related_information: Some(Vec::new()),
        ordering: CompilationDiagnosticOrdering::default(),
    };
    let before = render_error_baseline(case, &[diagnostic]);
    assert!(before.unsupported_details.is_empty());
    fs::write(directory.join("arrayCast.before.errors.txt"), before.text).unwrap();
}
