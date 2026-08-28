use std::{env, path::Path};

use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};

#[test]
fn accepted_strict_reserved_identifier_originals_match_full_error_artifacts() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    for case in [
        "compiler/downlevelLetConst11.ts",
        "compiler/downlevelLetConst6.ts",
        "compiler/letAsIdentifier2.ts",
        "compiler/strictModeReservedWordInModuleDeclaration.ts",
        "conformance/es6/functionDeclarations/FunctionDeclaration2_es6.ts",
        "conformance/es6/functionDeclarations/FunctionDeclaration4_es6.ts",
        "conformance/es6/variableDeclarations/VariableDeclaration11_es6.ts",
        "conformance/es6/variableDeclarations/VariableDeclaration6_es6.ts",
        "conformance/interfaces/interfaceDeclarations/asiPreventsParsingAsInterface01.ts",
        "conformance/interfaces/interfaceDeclarations/asiPreventsParsingAsInterface03.ts",
        "conformance/interfaces/interfaceDeclarations/asiPreventsParsingAsInterface05.ts",
        "conformance/parser/ecmascript5/StrictMode/parserStrictMode1.ts",
        "conformance/parser/ecmascript5/StrictMode/parserStrictMode2.ts",
    ] {
        let options = RunnerOptions {
            diagnostics: true,
            canonical_checker: true,
            filter: Some(format!("_submodules/TypeScript/tests/cases/{case}")),
            ..RunnerOptions::default()
        };
        let mut output = Vec::new();
        let summary =
            run_upstream_diagnostic_baselines(Path::new(&repository), &options, &mut output)
                .unwrap_or_else(|error| panic!("{case}: {error}"));
        assert_eq!(summary.selected_cases, 1, "{case}");
        assert!(summary.executed_variants > 0, "{case}");
        assert_eq!(
            summary.matched,
            summary.executed_variants,
            "{case}: {}",
            String::from_utf8_lossy(&output)
        );
        assert!(
            summary.is_success(),
            "{case}: {}",
            String::from_utf8_lossy(&output)
        );
    }
}
