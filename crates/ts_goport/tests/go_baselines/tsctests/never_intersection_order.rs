//! Port-only test of the name order of `some_property_reduces_to_never`
//! (Go `checker/checker.go:22216 somePropertyReducesToNever`).
//!
//! PORT: no Go counterpart. Go ranges over a map, so it checks the shared
//! names of an intersection in a random order and stops at the first one
//! that reduces to never. Each name that it checks before that one makes a
//! synthetic property. The port checks the names that are not a method in
//! every constituent first. Here `A & B` reduces to never by `kind`, and the
//! 30 methods of `A` and `B` have different types, so each method checked
//! before `kind` makes one symbol and one intersection type. The counts must
//! not depend on where `kind` is declared. In first-seen order alone, `kind`
//! after the methods made 30 more symbols and 30 more types.

use crate::support::child::run_command_in_child;
use crate::support::runner::TscInput;
use crate::support::test_sys::new_test_sys;

const PROJECT: &str = "/home/src/workspaces/project";

/// The `Symbols` and `Types` lines of `tsc --extendedDiagnostics` on
/// `A & B`, with `kind` declared before or after the methods.
fn counts(kind_first: bool) -> (String, String) {
    let methods =
        |ret: &str| -> String { (0..30).map(|i| format!("    m{i}(): {ret};\n")).collect() };
    let interface = |name: &str, ret: &str, kind: &str| {
        let kind = format!("    kind: \"{kind}\";\n");
        if kind_first {
            format!("interface {name} {{\n{kind}{}}}\n", methods(ret))
        } else {
            format!("interface {name} {{\n{}{kind}}}\n", methods(ret))
        }
    };
    let text = format!(
        "{}{}declare const ab: A & B;\nexport const n: number = ab;\n",
        interface("A", "string", "a"),
        interface("B", "number", "b")
    );
    let input = TscInput {
        files: [
            (format!("{PROJECT}/a.ts"), text.into()),
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
    let args = ["-p", "tsconfig.json", "--extendedDiagnostics"].map(String::from);
    let result = run_command_in_child(&sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
    assert!(result.unported.is_none(), "unported {:?}", result.unported);
    let output = sys.output_text();
    let line = |name: &str| {
        output
            .lines()
            .find(|line| line.starts_with(name))
            .unwrap_or_else(|| panic!("no {name} line in:\n{output}"))
            .to_string()
    };
    (line("Symbols:"), line("Types:"))
}

#[test]
fn never_intersection_checks_properties_before_methods() {
    let first = counts(true);
    let last = counts(false);
    assert_eq!(first, last, "kind declared first, then last");
}
