//! Port-only test of the memo of spelling suggestions from the globals table
//! (`Checker::get_suggestion_for_symbol_name_lookup`, Go
//! `checker/checker.go:1816 getSuggestionForSymbolNameLookup`).
//!
//! PORT: no Go counterpart. Each unresolved name below is looked up twice or
//! more with the same meaning, so the second lookup reads the memo: a
//! primitive type alias suggestion (`string`, made new on each call), a
//! symbol of the globals table (`Symbol`), and no suggestion (`expect`).
//! `Symbl` in `f` finds `Symbl2` in a local scope before the globals.
//! `Arrray` as a type finds `Array`; as a value it finds nothing, because the
//! memo key holds the meaning. The expected output is Go N's (the same lib
//! text, `noLib` with the lib as a file).

use ts_goport::execute::tsc::ExitStatus;

use crate::support::child::run_command_in_child;
use crate::support::runner::TscInput;
use crate::support::test_sys::new_test_sys;

const PROJECT: &str = "/home/src/workspaces/project";

const TEXT: &str = r#"let a1: strin = "";
let a2: strin = "";
let b1 = Symbl;
let b2 = Symbl;
let c1 = expect;
let c2 = expect;
function f() {
    let a3: strin = "";
    let Symbl2 = 1;
    let b3 = Symbl;
    return [a3, b3, Symbl2];
}
let d1: Arrray<number> = [];
let d2 = Arrray;
"#;

const WANT: &str = "\
a.ts(1,9): error TS2552: Cannot find name 'strin'. Did you mean 'string'?
a.ts(2,9): error TS2552: Cannot find name 'strin'. Did you mean 'string'?
a.ts(3,10): error TS2552: Cannot find name 'Symbl'. Did you mean 'Symbol'?
a.ts(4,10): error TS2552: Cannot find name 'Symbl'. Did you mean 'Symbol'?
a.ts(5,10): error TS2304: Cannot find name 'expect'.
a.ts(6,10): error TS2304: Cannot find name 'expect'.
a.ts(8,13): error TS2552: Cannot find name 'strin'. Did you mean 'string'?
a.ts(10,14): error TS2552: Cannot find name 'Symbl'. Did you mean 'Symbl2'?
a.ts(13,9): error TS2552: Cannot find name 'Arrray'. Did you mean 'Array'?
a.ts(14,10): error TS2304: Cannot find name 'Arrray'.
";

#[test]
fn spelling_memo_of_globals_gives_the_same_suggestions() {
    let input = TscInput {
        files: [
            (format!("{PROJECT}/a.ts"), TEXT.into()),
            (
                format!("{PROJECT}/tsconfig.json"),
                r#"{"compilerOptions":{"noEmit":true},"files":["a.ts"]}"#.into(),
            ),
        ]
        .into_iter()
        .collect(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let args = ["-p", "tsconfig.json", "--pretty", "false"].map(String::from);
    let result = run_command_in_child(&sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
    assert!(result.unported.is_none(), "unported {:?}", result.unported);
    // The test system adds the list of files after the diagnostics.
    let output = sys.output_text();
    let diagnostics = output.split("!!! List files start").next();
    assert_eq!(diagnostics, Some(WANT));
    assert_eq!(
        result.status,
        ExitStatus::DiagnosticsPresentOutputsGenerated
    );
}
