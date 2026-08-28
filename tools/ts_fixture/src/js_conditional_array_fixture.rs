use std::{fs, path::PathBuf};

use crate::{
    Case, FixtureChecker, compile_case_variant, expand_option_matrix, render_error_baseline,
};

const ORIGINAL: &str = concat!(
    "// @strict: true\n",
    "// @allowJs: true\n",
    "// @checkJs: true\n",
    "// @noEmit: true\n",
    "// @filename: t.js\n",
    "\n",
    "const is_morning = new Date().getHours() < 12;\n",
    "\n",
    "// prettier-ignore\n",
    "const greeting = ([\n",
    "  is_morning ? 'good morning' : 'good evening'\n",
    "]);\n",
);

#[test]
fn original_js_array_conditional_checks_date_and_both_branches() {
    let case = Case::parse(
        "testdata/tests/cases/compiler/jsSpeculativeParsingError.ts",
        ORIGINAL,
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, true).unwrap();
    let errors = render_error_baseline(&case, &compilation.diagnostics);
    if let Some(directory) = std::env::var_os("TS_JS_CONDITIONAL_ARRAY_ARTIFACT_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("original.ts"), ORIGINAL).unwrap();
        fs::write(directory.join("original.errors.txt"), &errors.text).unwrap();
        if let Some(artifacts) = &compilation.semantic_artifacts {
            match &artifacts.types {
                Ok(types) => fs::write(directory.join("original.types"), types).unwrap(),
                Err(error) => {
                    fs::write(directory.join("types-error.txt"), format!("{error:?}")).unwrap()
                }
            }
        }
    }
    assert!(errors.unsupported_details.is_empty());
    assert_eq!(errors.text, "");
    assert!(compilation.diagnostics.is_empty());
    let types = compilation
        .semantic_artifacts
        .as_ref()
        .unwrap()
        .types
        .as_ref()
        .unwrap();
    for expected in [
        ">Date : DateConstructor\r\n",
        ">new Date() : Date\r\n",
        ">new Date().getHours : () => number\r\n",
        ">new Date().getHours() : number\r\n",
        ">is_morning : boolean\r\n",
        ">greeting : string[]\r\n",
        ">is_morning ? 'good morning' : 'good evening' : \"good evening\" | \"good morning\"\r\n",
        ">'good morning' : \"good morning\"\r\n",
        ">'good evening' : \"good evening\"\r\n",
    ] {
        assert!(types.contains(expected), "missing {expected:?} in {types}");
    }
}

#[test]
fn js_array_conditional_checks_missing_names_in_both_branches() {
    let case = Case::parse(
        "jsArrayConditionalBranches.ts",
        concat!(
            "// @strict: true\n",
            "// @allowJs: true\n",
            "// @checkJs: true\n",
            "// @noEmit: true\n",
            "// @filename: branches.js\n",
            "const is_morning = new Date().getHours() < 12;\n",
            "const greeting = ([is_morning ? onlyTrueBranchMissing : onlyFalseBranchMissing]);\n",
        ),
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, false).unwrap();
    assert_eq!(
        compilation
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>(),
        [Some(2304), Some(2304)]
    );
    assert_eq!(
        compilation.diagnostics[0].message,
        "Cannot find name 'onlyTrueBranchMissing'."
    );
    assert_eq!(
        compilation.diagnostics[1].message,
        "Cannot find name 'onlyFalseBranchMissing'."
    );
}
