//! Port of Go `internal/project/ata/validatepackagename_test.go`.

use ts_goport::project::ata::{self, NameValidationResult};

fn check(package_name: &str, status: NameValidationResult, name: &str, is_scope_name: bool) {
    let (got_status, got_name, got_is_scope_name) = ata::validate_package_name(package_name);
    assert_eq!(got_status, status, "status of {package_name:?}");
    assert_eq!(got_name, name, "name of {package_name:?}");
    assert_eq!(
        got_is_scope_name, is_scope_name,
        "isScopeName of {package_name:?}"
    );
}

fn check_status(package_name: &str, status: NameValidationResult) {
    let (got_status, _, _) = ata::validate_package_name(package_name);
    assert_eq!(got_status, status, "status of {package_name:?}");
}

// Go: validatepackagename_test.go:13 TestValidatePackageName/name cannot be too long
#[test]
fn name_cannot_be_too_long() {
    let mut package_name = String::from("a");
    for _ in 0..8 {
        package_name = package_name.repeat(2);
    }
    check_status(&package_name, ata::NAME_TOO_LONG);
}

// Go: validatepackagename_test.go:23 TestValidatePackageName/package name cannot start with dot
#[test]
fn package_name_cannot_start_with_dot() {
    check_status(".foo", ata::NAME_STARTS_WITH_DOT);
}

// Go: validatepackagename_test.go:28 TestValidatePackageName/package name cannot start with underscore
#[test]
fn package_name_cannot_start_with_underscore() {
    check_status("_foo", ata::NAME_STARTS_WITH_UNDERSCORE);
}

// Go: validatepackagename_test.go:33 TestValidatePackageName/package non URI safe characters are not supported
#[test]
fn package_non_uri_safe_characters_are_not_supported() {
    check_status("  scope  ", ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS);
    check_status(
        "; say \u{2018}Hello from TypeScript!\u{2019} #",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
    );
    check_status("a/b/c", ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS);
}

// Go: validatepackagename_test.go:42 TestValidatePackageName/scoped package name is supported
#[test]
fn scoped_package_name_is_supported() {
    check_status("@scope/bar", ata::NAME_OK);
}

// Go: validatepackagename_test.go:47 TestValidatePackageName/scoped name in scoped package name cannot start with dot
#[test]
fn scoped_name_in_scoped_package_name_cannot_start_with_dot() {
    check("@.scope/bar", ata::NAME_STARTS_WITH_DOT, ".scope", true);
    check("@.scope/.bar", ata::NAME_STARTS_WITH_DOT, ".scope", true);
}

// Go: validatepackagename_test.go:58 TestValidatePackageName/scoped name in scoped package name cannot start with dot#01
#[test]
fn scoped_name_in_scoped_package_name_cannot_start_with_dot_01() {
    check(
        "@_scope/bar",
        ata::NAME_STARTS_WITH_UNDERSCORE,
        "_scope",
        true,
    );
    check(
        "@_scope/_bar",
        ata::NAME_STARTS_WITH_UNDERSCORE,
        "_scope",
        true,
    );
}

// Go: validatepackagename_test.go:69 TestValidatePackageName/scope name in scoped package name with non URI safe characters are not supported
#[test]
fn scope_name_in_scoped_package_name_with_non_uri_safe_characters_are_not_supported() {
    check(
        "@  scope  /bar",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
        "  scope  ",
        true,
    );
    check(
        "@; say \u{2018}Hello from TypeScript!\u{2019} #/bar",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
        "; say \u{2018}Hello from TypeScript!\u{2019} #",
        true,
    );
    check(
        "@  scope  /  bar  ",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
        "  scope  ",
        true,
    );
}

// Go: validatepackagename_test.go:84 TestValidatePackageName/package name in scoped package name cannot start with dot
#[test]
fn package_name_in_scoped_package_name_cannot_start_with_dot() {
    check("@scope/.bar", ata::NAME_STARTS_WITH_DOT, ".bar", false);
}

// Go: validatepackagename_test.go:91 TestValidatePackageName/package name in scoped package name cannot start with underscore
#[test]
fn package_name_in_scoped_package_name_cannot_start_with_underscore() {
    check(
        "@scope/_bar",
        ata::NAME_STARTS_WITH_UNDERSCORE,
        "_bar",
        false,
    );
}

// Go: validatepackagename_test.go:98 TestValidatePackageName/package name in scoped package name with non URI safe characters are not supported
#[test]
fn package_name_in_scoped_package_name_with_non_uri_safe_characters_are_not_supported() {
    check(
        "@scope/  bar  ",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
        "  bar  ",
        false,
    );
    check(
        "@scope/; say \u{2018}Hello from TypeScript!\u{2019} #",
        ata::NAME_CONTAINS_NON_URI_SAFE_CHARACTERS,
        "; say \u{2018}Hello from TypeScript!\u{2019} #",
        false,
    );
}
