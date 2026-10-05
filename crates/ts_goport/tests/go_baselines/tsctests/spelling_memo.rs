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
//! memo key holds the meaning.
//!
//! The two init-order tests ask for `Thingg` once during `initialize_checker`
//! and once after it. Between the two, the augmentation of `"foo"` (whose
//! `export =` is the merged global namespace `Thing`) adds value flags to
//! `Thing`, so only the second lookup finds `Thing`. A result kept during
//! `initialize_checker` would hide it. The first lookup is the failed
//! `export = Thingg` of `"bad"` (augmentation loop) or the import attribute
//! type of a pattern ambient module.
//!
//! The late-merge tests ask for one name before and after a late-bound
//! member is merged into a global in place. `globalThis` is also a class
//! whose static member has the computed name `"Foo"` (or another global's
//! name). When its exports are resolved (`globalThis.Foo`, or an alias
//! through `globalThis`), `combine_symbol_tables` merges that member into the
//! global. Two files declare the global, so it is transient and gets the
//! property flag, a value meaning, in place. A result kept from before the
//! merge would hide the new suggestion. These run single-threaded, so one
//! checker sees both lookups.
//!
//! Every expected output is Go N's (the same lib text, `noLib` with the lib
//! as a file). In the mid-scan test, Go's first line depends on its random
//! map order (see there).

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

/// Runs `tsgo -p tsconfig.json` on `files` (name, text) in the project dir
/// and gives the diagnostics text.
fn check(files: &[(&str, &str)], tsconfig: &str) -> String {
    let input = TscInput {
        files: files
            .iter()
            .map(|&(name, text)| (format!("{PROJECT}/{name}"), text.into()))
            .chain([(format!("{PROJECT}/tsconfig.json"), tsconfig.into())])
            .collect(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let args = ["-p", "tsconfig.json", "--pretty", "false"].map(String::from);
    let result = run_command_in_child(&sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
    assert!(result.unported.is_none(), "unported {:?}", result.unported);
    assert_eq!(
        result.status,
        ExitStatus::DiagnosticsPresentOutputsGenerated
    );
    // The test system adds the list of files after the diagnostics.
    let output = sys.output_text();
    output
        .split("!!! List files start")
        .next()
        .unwrap_or_default()
        .to_string()
}

#[test]
fn spelling_memo_of_globals_gives_the_same_suggestions() {
    let output = check(
        &[("a.ts", TEXT)],
        r#"{"compilerOptions":{"noEmit":true},"files":["a.ts"]}"#,
    );
    assert_eq!(output, WANT);
}

const THING: &str = "declare namespace Thing { interface J {} }\n";

const AUG_FOO: &str = r#"import "foo";
declare module "foo" { export const x: number; }
export {};
"#;

const USE: &str = "Thingg;\nexport {};\n";

#[test]
fn spelling_memo_waits_for_augmentations_after_failed_export_equals() {
    let globals = r#"declare namespace Thing { interface I {} }
declare module "bad" { export = Thingg; }
declare module "foo" { export = Thing; }
"#;
    let aug_bad = r#"import "bad";
declare module "bad" { export const y: number; }
export {};
"#;
    let output = check(
        &[
            ("globals1.d.ts", globals),
            ("globals2.d.ts", THING),
            ("aug1.ts", aug_bad),
            ("aug2.ts", AUG_FOO),
            ("use.ts", USE),
        ],
        r#"{"compilerOptions":{"noEmit":true,"strict":true,"module":"esnext","moduleResolution":"bundler"},"files":["globals1.d.ts","globals2.d.ts","aug1.ts","aug2.ts","use.ts"]}"#,
    );
    assert_eq!(
        output,
        "\
aug1.ts(2,16): error TS2671: Cannot augment module 'bad' because it resolves to a non-module entity.
globals1.d.ts(2,33): error TS2304: Cannot find name 'Thingg'.
use.ts(1,1): error TS2552: Cannot find name 'Thingg'. Did you mean 'Thing'?
"
    );
}

#[test]
fn spelling_memo_waits_for_augmentations_after_import_attributes() {
    let globals = r#"declare namespace Thing { interface I {} }
declare module "foo" { export = Thing; }
declare module "*.a" with { type: "a" } { const v: number; export default v; }
declare module "*.a" with { type: typeof Thingg } { const w: number; export default w; }
"#;
    let output = check(
        &[
            ("globals1.d.ts", globals),
            ("globals2.d.ts", THING),
            ("aug2.ts", AUG_FOO),
            ("use.ts", USE),
        ],
        r#"{"compilerOptions":{"noEmit":true,"strict":true,"module":"esnext","moduleResolution":"bundler"},"files":["globals1.d.ts","globals2.d.ts","aug2.ts","use.ts"]}"#,
    );
    assert_eq!(
        output,
        "\
error TS2318: Cannot find global type 'ImportAttributes'.
globals1.d.ts(4,35): error TS1555: An import attributes property must have a string literal type annotation.
globals1.d.ts(4,42): error TS2304: Cannot find name 'Thingg'.
use.ts(1,1): error TS2552: Cannot find name 'Thingg'. Did you mean 'Thing'?
"
    );
}

/// Runs `check` single-threaded with the options of the late-merge tests and
/// every file as a root, in order.
fn check_late(files: &[(&str, &str)]) -> String {
    let names: Vec<String> = files.iter().map(|(name, _)| format!("{name:?}")).collect();
    let tsconfig = format!(
        r#"{{"compilerOptions":{{"noEmit":true,"strict":true,"module":"esnext","moduleResolution":"bundler","singleThreaded":true}},"files":[{}]}}"#,
        names.join(",")
    );
    check(files, &tsconfig)
}

/// A module that makes `globalThis` also a class with the static member
/// `[k]`, where `k` has the literal type `name`.
fn global_this_class_aug(name: &str) -> String {
    format!(
        "declare const k: \"{name}\";\ndeclare global {{\n  class globalThis {{ static [k]: number; }}\n}}\nexport {{}};\n"
    )
}

const FOO_A: &str = "interface Foo { a: number }\n";
const FOO_B: &str = "interface Foo { b: number }\n";
const USE_FOO: &str = "Fooo;\ntype T = globalThis.Foo;\nFooo;\nexport {};\n";

#[test]
fn spelling_memo_sees_late_bound_merge_into_global() {
    let output = check_late(&[
        ("use.ts", USE_FOO),
        ("aug.ts", &global_this_class_aug("Foo")),
        ("globals1.d.ts", FOO_A),
        ("globals2.d.ts", FOO_B),
    ]);
    assert_eq!(
        output,
        "\
use.ts(1,1): error TS2304: Cannot find name 'Fooo'.
use.ts(3,1): error TS2552: Cannot find name 'Fooo'. Did you mean 'Foo'?
"
    );
}

#[test]
fn spelling_memo_sees_late_bound_merge_from_global_class() {
    let globals = "interface Foo { a: number }\ndeclare const k: \"Foo\";\ndeclare class globalThis { static [k]: number; }\n";
    let output = check_late(&[
        ("use.ts", USE_FOO),
        ("globals1.d.ts", globals),
        ("globals2.d.ts", FOO_B),
    ]);
    assert_eq!(
        output,
        "\
globals1.d.ts(3,15): error TS2397: Declaration name conflicts with built-in global identifier 'globalThis'.
use.ts(1,1): error TS2304: Cannot find name 'Fooo'.
use.ts(3,1): error TS2552: Cannot find name 'Fooo'. Did you mean 'Foo'?
"
    );
}

#[test]
fn spelling_memo_sees_late_bound_merge_into_alias_target() {
    let globals = "interface Foo { a: number }\ndeclare namespace Foo { interface X {} }\nimport Alias1 = Foo;\n";
    let output = check_late(&[
        (
            "use.ts",
            "Aliasx;\ntype T = globalThis.Foo;\nAliasx;\nexport {};\n",
        ),
        ("aug.ts", &global_this_class_aug("Foo")),
        ("globals1.d.ts", globals),
        ("globals2.d.ts", FOO_B),
    ]);
    assert_eq!(
        output,
        "\
use.ts(1,1): error TS2304: Cannot find name 'Aliasx'.
use.ts(3,1): error TS2552: Cannot find name 'Aliasx'. Did you mean 'Alias1'?
"
    );
}

#[test]
fn spelling_memo_sees_better_candidate_after_merge() {
    let output = check_late(&[
        (
            "use.ts",
            "Foooooo;\ntype T = globalThis.Foooooa;\nFoooooo;\nexport {};\n",
        ),
        ("aug.ts", &global_this_class_aug("Foooooa")),
        (
            "globals1.d.ts",
            "interface Foooooa { a: number }\ndeclare var Foxxooo: number;\n",
        ),
        ("globals2.d.ts", "interface Foooooa { b: number }\n"),
    ]);
    assert_eq!(
        output,
        "\
use.ts(1,1): error TS2304: Cannot find name 'Foooooo'.
use.ts(3,1): error TS2552: Cannot find name 'Foooooo'. Did you mean 'Foooooa'?
"
    );
}

#[test]
fn spelling_memo_sees_better_table_candidate_after_merge() {
    let output = check_late(&[
        (
            "use.ts",
            "Foooooo;\ntype T = globalThis.FoooooO;\nFoooooo;\nexport {};\n",
        ),
        ("aug.ts", &global_this_class_aug("FoooooO")),
        (
            "globals1.d.ts",
            "interface FoooooO { a: number }\ndeclare var Fooooo: number;\n",
        ),
        ("globals2.d.ts", "interface FoooooO { b: number }\n"),
    ]);
    assert_eq!(
        output,
        "\
use.ts(1,1): error TS2552: Cannot find name 'Foooooo'. Did you mean 'Fooooo'?
use.ts(3,1): error TS2552: Cannot find name 'Foooooo'. Did you mean 'FoooooO'?
"
    );
}

#[test]
fn spelling_memo_sees_merge_from_another_file() {
    let output = check_late(&[
        ("a1.ts", "Fooo;\nexport {};\n"),
        ("a2.ts", "export type T = globalThis.Foo;\n"),
        ("a3.ts", "Fooo;\nexport {};\n"),
        ("aug.ts", &global_this_class_aug("Foo")),
        ("globals1.d.ts", FOO_A),
        ("globals2.d.ts", FOO_B),
    ]);
    assert_eq!(
        output,
        "\
a1.ts(1,1): error TS2304: Cannot find name 'Fooo'.
a3.ts(1,1): error TS2552: Cannot find name 'Fooo'. Did you mean 'Foo'?
"
    );
}

/// The first scan for `Fooo` resolves the alias candidate `Qalias`, whose
/// target is found through `globalThis`, so the merge into `Foo` comes during
/// that scan. Go ranges over the globals map in random order: when it reads
/// `Foo` after `Qalias`, line 1 also suggests `Foo`. The port reads the table
/// in insertion order (`Foo` first), and the Go runs that read `Foo` first
/// give this output. Line 2 always suggests `Foo`.
#[test]
fn spelling_memo_sees_merge_during_its_scan() {
    let output = check_late(&[
        ("use.ts", "Fooo;\nFooo;\nexport {};\n"),
        ("aug.ts", &global_this_class_aug("Foo")),
        ("globals1.d.ts", FOO_A),
        (
            "globals2.d.ts",
            "interface Foo { b: number }\ndeclare namespace Bar { interface Y {} }\n",
        ),
        ("globals3.d.ts", "import Qalias = globalThis.Bar;\n"),
    ]);
    assert_eq!(
        output,
        "\
use.ts(1,1): error TS2304: Cannot find name 'Fooo'.
use.ts(2,1): error TS2552: Cannot find name 'Fooo'. Did you mean 'Foo'?
"
    );
}
