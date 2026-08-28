use std::{fs, path::PathBuf};

use crate::{
    Case, FixtureChecker, compile_case_variant, expand_option_matrix, render_error_baseline,
};

const SOURCE: &str = concat!(
    "// @target: es2015\r\n",
    "// @declaration: true\r\n",
    "\r\n",
    "var { } = { x: 5, y: \"hello\" };\r\n",
    "var { x4 } = { x4: 5, y4: \"hello\" };\r\n",
    "var { y5 } = { x5: 5, y5: \"hello\" };\r\n",
    "var { x6, y6 } = { x6: 5, y6: \"hello\" };\r\n",
    "var { x7: a1 } = { x7: 5, y7: \"hello\" };\r\n",
    "var { y8: b1 } = { x8: 5, y8: \"hello\" };\r\n",
    "var { x9: a2, y9: b2 } = { x9: 5, y9: \"hello\" };",
);

const EXPECTED: &str = concat!(
    "declarationEmitDestructuringObjectLiteralPattern1.ts(2,23): error TS2353: Object literal may only specify known properties, and 'y4' does not exist in type '{ x4: any; }'.\r\n",
    "declarationEmitDestructuringObjectLiteralPattern1.ts(3,16): error TS2353: Object literal may only specify known properties, and 'x5' does not exist in type '{ y5: any; }'.\r\n",
    "declarationEmitDestructuringObjectLiteralPattern1.ts(5,27): error TS2353: Object literal may only specify known properties, and 'y7' does not exist in type '{ x7: any; }'.\r\n",
    "declarationEmitDestructuringObjectLiteralPattern1.ts(6,20): error TS2353: Object literal may only specify known properties, and 'x8' does not exist in type '{ y8: any; }'.\r\n",
    "\r\n",
    "\r\n",
    "==== declarationEmitDestructuringObjectLiteralPattern1.ts (4 errors) ====\r\n",
    "    var { } = { x: 5, y: \"hello\" };\r\n",
    "    var { x4 } = { x4: 5, y4: \"hello\" };\r\n",
    "                          ~~\r\n",
    "!!! error TS2353: Object literal may only specify known properties, and 'y4' does not exist in type '{ x4: any; }'.\r\n",
    "    var { y5 } = { x5: 5, y5: \"hello\" };\r\n",
    "                   ~~\r\n",
    "!!! error TS2353: Object literal may only specify known properties, and 'x5' does not exist in type '{ y5: any; }'.\r\n",
    "    var { x6, y6 } = { x6: 5, y6: \"hello\" };\r\n",
    "    var { x7: a1 } = { x7: 5, y7: \"hello\" };\r\n",
    "                              ~~\r\n",
    "!!! error TS2353: Object literal may only specify known properties, and 'y7' does not exist in type '{ x7: any; }'.\r\n",
    "    var { y8: b1 } = { x8: 5, y8: \"hello\" };\r\n",
    "                       ~~\r\n",
    "!!! error TS2353: Object literal may only specify known properties, and 'x8' does not exist in type '{ y8: any; }'.\r\n",
    "    var { x9: a2, y9: b2 } = { x9: 5, y9: \"hello\" };",
);

#[test]
fn original_object_binding_pattern_keeps_all_four_excess_property_errors() {
    let case = Case::parse(
        "_submodules/TypeScript/tests/cases/compiler/declarationEmitDestructuringObjectLiteralPattern1.ts",
        SOURCE,
    )
    .unwrap();
    let mut variants = expand_option_matrix(&case);
    assert_eq!(variants.len(), 1);
    let compilation =
        compile_case_variant(&case, &mut variants[0], FixtureChecker::Canonical, false).unwrap();
    let actual = render_error_baseline(&case, &compilation.diagnostics);
    if let Some(directory) = std::env::var_os("TS_DESTRUCTURING_ARTIFACT_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("original.ts"), SOURCE).unwrap();
        fs::write(directory.join("expected.errors.txt"), EXPECTED).unwrap();
        fs::write(directory.join("after.errors.txt"), &actual.text).unwrap();
    }
    assert!(actual.unsupported_details.is_empty());
    assert_eq!(actual.text, EXPECTED);
    assert_eq!(compilation.diagnostics.len(), 4);
    assert!(
        compilation
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == Some(2353))
    );
}
