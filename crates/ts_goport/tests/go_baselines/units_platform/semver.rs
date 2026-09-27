//! Go: `internal/semver/{version,version_range}_test.go`.
//!
//! PORT: the Rust `Version` fields are private, so a Go `Version{...}`
//! literal is checked through the derived `Debug` text (the same fields),
//! and `TestVersionString` builds its versions by parsing the expected
//! text and checking the fields first.

use ts_goport::frontend::semver::{self, Version};

use super::Failures;

/// The derived `Debug` text of a Go `Version{major, minor, patch,
/// prerelease, build}` literal.
fn version_debug(
    major: u32,
    minor: u32,
    patch: u32,
    prerelease: &[&str],
    build: &[&str],
) -> String {
    format!(
        "Version {{ major: {major}, minor: {minor}, patch: {patch}, prerelease: {prerelease:?}, build: {build:?} }}"
    )
}

// Go: version_test.go:9 TestTryParseSemver
#[test]
fn test_try_parse_semver() {
    let tests: &[(&str, String)] = &[
        (
            "1.2.3-pre.4+build.5",
            version_debug(1, 2, 3, &["pre", "4"], &["build", "5"]),
        ),
        ("1.2.3-pre.4", version_debug(1, 2, 3, &["pre", "4"], &[])),
        (
            "1.2.3+build.4",
            version_debug(1, 2, 3, &[], &["build", "4"]),
        ),
        ("1.2.3", version_debug(1, 2, 3, &[], &[])),
    ];
    let mut failures = Failures::new("TestTryParseSemver");
    for (input, out) in tests {
        match semver::try_parse_version(input) {
            Ok(v) => failures.check_eq(input, format!("{v:?}"), out.clone()),
            Err(err) => failures.fail(input, format!("unexpected error {err}")),
        }
    }
    failures.finish();
}

// Go: version_test.go:31 TestVersionString
#[test]
fn test_version_string() {
    let tests: &[(String, &str)] = &[
        (
            version_debug(1, 2, 3, &["pre", "4"], &["build", "5"]),
            "1.2.3-pre.4+build.5",
        ),
        (
            version_debug(1, 2, 3, &["pre", "4"], &["build"]),
            "1.2.3-pre.4+build",
        ),
        (version_debug(1, 2, 3, &[], &["build"]), "1.2.3+build"),
        (version_debug(1, 2, 3, &["pre", "4"], &[]), "1.2.3-pre.4"),
        (
            version_debug(1, 2, 3, &[], &["build", "4"]),
            "1.2.3+build.4",
        ),
        (version_debug(1, 2, 3, &[], &[]), "1.2.3"),
    ];
    let mut failures = Failures::new("TestVersionString");
    for (fields, out) in tests {
        let v: Version = semver::must_parse_version(out);
        failures.check_eq(out, format!("{v:?}"), fields.clone());
        failures.check_eq(out, v.string(), out.to_string());
    }
    failures.finish();
}

const COMPARISON_LESS_THAN: i32 = -1;
const COMPARISON_EQUAL_TO: i32 = 0;
const COMPARISON_GREATER_THAN: i32 = 1;

// Go: version_test.go:53 TestVersionCompare
#[test]
fn test_version_compare() {
    use COMPARISON_EQUAL_TO as EQ;
    use COMPARISON_GREATER_THAN as GT;
    use COMPARISON_LESS_THAN as LT;
    let tests: &[(&str, &str, i32)] = &[
        ("1.0.0", "2.0.0", LT),
        ("1.0.0", "1.1.0", LT),
        ("1.0.0", "1.0.1", LT),
        ("2.0.0", "1.0.0", GT),
        ("1.1.0", "1.0.0", GT),
        ("1.0.1", "1.0.0", GT),
        ("1.0.0", "1.0.0", EQ),
        ("1.0.0", "1.0.0-pre", GT),
        ("1.0.1-pre", "1.0.0", GT),
        ("1.0.0-pre", "1.0.0", LT),
        ("1.0.0-0", "1.0.0-1", LT),
        ("1.0.0-1", "1.0.0-0", GT),
        ("1.0.0-2", "1.0.0-10", LT),
        ("1.0.0-10", "1.0.0-2", GT),
        ("1.0.0-0", "1.0.0-0", EQ),
        ("1.0.0-a", "1.0.0-b", LT),
        ("1.0.0-a-2", "1.0.0-a-10", GT),
        ("1.0.0-b", "1.0.0-a", GT),
        ("1.0.0-a", "1.0.0-a", EQ),
        ("1.0.0-A", "1.0.0-a", LT),
        ("1.0.0-0", "1.0.0-alpha", LT),
        ("1.0.0-alpha", "1.0.0-0", GT),
        ("1.0.0-0", "1.0.0-0", EQ),
        ("1.0.0-alpha", "1.0.0-alpha", EQ),
        ("1.0.0-alpha", "1.0.0-alpha.0", LT),
        ("1.0.0-alpha.0", "1.0.0-alpha", GT),
        ("1.0.0-a.0.b.1", "1.0.0-a.0.b.2", LT),
        ("1.0.0-a.0.b.1", "1.0.0-b.0.a.1", LT),
        ("1.0.0-a.0.b.2", "1.0.0-a.0.b.1", GT),
        ("1.0.0-b.0.a.1", "1.0.0-a.0.b.1", GT),
        ("1.0.0+build", "1.0.0", EQ),
        ("1.0.0+build.stuff", "1.0.0", EQ),
        ("1.0.0", "1.0.0+build", EQ),
        ("1.0.0+build", "1.0.0+stuff", EQ),
        ("1.0.0-alpha.99999", "1.0.0-alpha.100000", LT),
        ("1.0.0-alpha.beta", "1.0.0-alpha.alpha", GT),
    ];
    let mut failures = Failures::new("TestVersionCompare");
    for (v1, v2, want) in tests {
        let name = format!("{v1} <=> {v2}");
        match (semver::try_parse_version(v1), semver::try_parse_version(v2)) {
            (Ok(a), Ok(b)) => failures.check_eq(&name, a.compare(&b), *want),
            (a, b) => failures.fail(&name, format!("parse error {:?} {:?}", a.err(), b.err())),
        }
    }
    failures.finish();
}

// Go: version_range_test.go:11 TestWildcardsHaveSameString
#[test]
fn test_wildcards_have_same_string() {
    let mut failures = Failures::new("TestWildcardsHaveSameString");
    let groups: &[(&str, &[&str])] = &[
        (
            "majorWildcardStrings",
            &[
                "", "*", "*.*", "*.*.*", "x", "x.x", "x.x.x", "X", "X.X", "X.X.X",
            ],
        ),
        (
            "minorWildcardStrings",
            &["1", "1.*", "1.*.*", "1.x", "1.x.x", "1.X", "1.X.X"],
        ),
        ("patchWildcardStrings", &["1.2", "1.2.*", "1.2.x", "1.2.X"]),
        (
            "mixedCaseWildcardStrings",
            &["x", "X", "*", "x.X.x", "X.x.*"],
        ),
    ];
    // Go: version_range_test.go:57 assertAllVersionRangesHaveIdenticalStrings
    for (name, strs) in groups {
        for s1 in *strs {
            for s2 in *strs {
                let sub = format!("{name}/{s1} == {s2}");
                let (v1, ok1) = semver::try_parse_version_range(s1);
                let (v2, ok2) = semver::try_parse_version_range(s2);
                if !ok1 || !ok2 {
                    failures.fail(&sub, "range did not parse".into());
                    continue;
                }
                failures.check_eq(&sub, v1.string(), v2.string());
            }
        }
    }
    failures.finish();
}

// Go: version_range_test.go:930 assertRangesGoodBad
fn assert_ranges_good_bad(failures: &mut Failures, range: &str, good: &[&str], bad: &[&str]) {
    let (version_range, ok) = semver::try_parse_version_range(range);
    if !ok {
        failures.fail(range, "range did not parse".into());
        return;
    }
    for (list, want) in [(good, true), (bad, false)] {
        for text in list {
            match semver::try_parse_version(text) {
                Ok(v) => {
                    if version_range.test(&v) != want {
                        let not = if want { "" } else { "not " };
                        failures.fail(
                            range,
                            format!("{text} should {not}be matched by range {range}"),
                        );
                    }
                }
                Err(err) => failures.fail(range, format!("{text}: {err}")),
            }
        }
    }
}

// Go: version_range_test.go:79 TestVersionRanges
#[test]
fn test_version_ranges() {
    let mut f = Failures::new("TestVersionRanges");
    assert_ranges_good_bad(
        &mut f,
        "1",
        &["1.0.0", "1.9.9", "1.0.0-pre", "1.0.0+build"],
        &["0.0.0", "2.0.0", "0.0.0-pre", "0.0.0+build"],
    );
    assert_ranges_good_bad(
        &mut f,
        "1.2",
        &["1.2.0", "1.2.9", "1.2.0-pre", "1.2.0+build"],
        &["1.1.0", "1.3.0", "1.1.0-pre", "1.1.0+build"],
    );
    assert_ranges_good_bad(
        &mut f,
        "1.2.3",
        &["1.2.3", "1.2.3+build"],
        &["1.2.2", "1.2.4", "1.2.2-pre", "1.2.2+build", "1.2.3-pre"],
    );
    assert_ranges_good_bad(
        &mut f,
        "1.2.3-pre",
        &["1.2.3-pre", "1.2.3-pre+build.stuff"],
        &[
            "1.2.3",
            "1.2.3-pre.0",
            "1.2.3-pre.9",
            "1.2.3-pre.0+build",
            "1.2.3-pre.9+build",
            "1.2.3+build",
            "1.2.4",
        ],
    );
    assert_ranges_good_bad(&mut f, "<3.8.0", &["3.6", "3.7"], &["3.8", "3.9", "4.0"]);
    assert_ranges_good_bad(&mut f, "<=3.8.0", &["3.6", "3.7", "3.8"], &["3.9", "4.0"]);
    assert_ranges_good_bad(&mut f, ">3.8.0", &["3.9", "4.0"], &["3.6", "3.7", "3.8"]);
    assert_ranges_good_bad(&mut f, ">=3.8.0", &["3.8", "3.9", "4.0"], &["3.6", "3.7"]);
    assert_ranges_good_bad(&mut f, "<3.8.0-0", &["3.6", "3.7"], &["3.8", "3.9", "4.0"]);
    assert_ranges_good_bad(&mut f, "<=3.8.0-0", &["3.6", "3.7"], &["3.8", "3.9", "4.0"]);

    // Big numbers in prerelease strings.
    let lotsa_ones = "1".repeat(320);
    let range = format!(">=1.2.3-1{lotsa_ones}");
    let good = [
        format!("1.2.3-1{lotsa_ones}"),
        format!("1.2.3-11{lotsa_ones}.1"),
        format!("1.2.3-1{lotsa_ones}.1+build"),
    ];
    let bad = [format!("1.2.3-{lotsa_ones}.1+build")];
    let good: Vec<&str> = good.iter().map(String::as_str).collect();
    let bad: Vec<&str> = bad.iter().map(String::as_str).collect();
    assert_ranges_good_bad(&mut f, &range, &good, &bad);
    f.finish();
}

// Go: version_range_test.go:949 assertRangeTest
fn check_range_tests(test: &str, name: &str, tests: &[(&str, &str, bool)]) {
    let mut failures = Failures::new(test);
    for (range_text, version_text, in_range) in tests {
        let sub = format!("{name} (version {version_text} in range {range_text}) == {in_range}");
        let (version_range, ok) = semver::try_parse_version_range(range_text);
        if !ok {
            failures.fail(&sub, "range did not parse".into());
            continue;
        }
        match semver::try_parse_version(version_text) {
            Ok(v) => failures.check_eq(&sub, version_range.test(&v), *in_range),
            Err(err) => failures.fail(&sub, err),
        }
    }
    failures.finish();
}

// Go: version_range_test.go:136 TestComparatorsOfVersionRanges
#[test]
fn test_comparators_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        // empty (matches everything)
        ("", "2.0.0", true),
        ("", "2.0.0-0", true),
        ("", "1.1.0", true),
        ("", "1.1.0-0", true),
        ("", "1.0.1", true),
        ("", "1.0.1-0", true),
        ("", "1.0.0", true),
        ("", "1.0.0-0", true),
        ("", "0.0.0", true),
        ("", "0.0.0-0", true),
        // wildcard major (matches everything)
        ("*", "2.0.0", true),
        ("*", "2.0.0-0", true),
        ("*", "1.1.0", true),
        ("*", "1.1.0-0", true),
        ("*", "1.0.1", true),
        ("*", "1.0.1-0", true),
        ("*", "1.0.0", true),
        ("*", "1.0.0-0", true),
        ("*", "0.0.0", true),
        ("*", "0.0.0-0", true),
        // wildcard minor
        ("1", "2.0.0", false),
        ("1", "2.0.0-0", false),
        ("1", "1.1.0", true),
        ("1", "1.1.0-0", true),
        ("1", "1.0.1", true),
        ("1", "1.0.1-0", true),
        ("1", "1.0.0", true),
        ("1", "1.0.0-0", true),
        ("1", "0.0.0", false),
        ("1", "0.0.0-0", false),
        // wildcard patch
        ("1.1", "2.0.0", false),
        ("1.1", "2.0.0-0", false),
        ("1.1", "1.1.0", true),
        ("1.1", "1.1.0-0", true),
        ("1.1", "1.0.1", false),
        ("1.1", "1.0.1-0", false),
        ("1.1", "1.0.0", false),
        ("1.1", "1.0.0-0", false),
        ("1.1", "0.0.0", false),
        ("1.1", "0.0.0-0", false),
        ("1.0", "2.0.0", false),
        ("1.0", "2.0.0-0", false),
        ("1.0", "1.1.0", false),
        ("1.0", "1.1.0-0", false),
        ("1.0", "1.0.1", true),
        ("1.0", "1.0.1-0", true),
        ("1.0", "1.0.0", true),
        ("1.0", "1.0.0-0", true),
        ("1.0", "0.0.0", false),
        ("1.0", "0.0.0-0", false),
        // exact
        ("1.1.0", "2.0.0", false),
        ("1.1.0", "2.0.0-0", false),
        ("1.1.0", "1.1.0", true),
        ("1.1.0", "1.1.0-0", false),
        ("1.1.0", "1.0.1", false),
        ("1.1.0", "1.0.1-0", false),
        ("1.1.0", "1.0.0-0", false),
        ("1.1.0", "1.0.0", false),
        ("1.1.0", "0.0.0", false),
        ("1.1.0", "0.0.0-0", false),
        ("1.1.0-0", "2.0.0", false),
        ("1.1.0-0", "2.0.0-0", false),
        ("1.1.0-0", "1.1.0", false),
        ("1.1.0-0", "1.1.0-0", true),
        ("1.1.0-0", "1.0.1", false),
        ("1.1.0-0", "1.0.1-0", false),
        ("1.1.0-0", "1.0.0-0", false),
        ("1.1.0-0", "1.0.0", false),
        ("1.1.0-0", "0.0.0", false),
        ("1.1.0-0", "0.0.0-0", false),
        ("1.0.1", "2.0.0", false),
        ("1.0.1", "2.0.0-0", false),
        ("1.0.1", "1.1.0", false),
        ("1.0.1", "1.1.0-0", false),
        ("1.0.1", "1.0.1", true),
        ("1.0.1", "1.0.1-0", false),
        ("1.0.1", "1.0.0-0", false),
        ("1.0.1", "1.0.0", false),
        ("1.0.1", "0.0.0", false),
        ("1.0.1", "0.0.0-0", false),
        ("1.0.1-0", "2.0.0", false),
        ("1.0.1-0", "2.0.0-0", false),
        ("1.0.1-0", "1.1.0", false),
        ("1.0.1-0", "1.1.0-0", false),
        ("1.0.1-0", "1.0.1", false),
        ("1.0.1-0", "1.0.1-0", true),
        ("1.0.1-0", "1.0.0-0", false),
        ("1.0.1-0", "1.0.0", false),
        ("1.0.1-0", "0.0.0", false),
        ("1.0.1-0", "0.0.0-0", false),
        ("1.0.0", "2.0.0", false),
        ("1.0.0", "2.0.0-0", false),
        ("1.0.0", "1.1.0", false),
        ("1.0.0", "1.1.0-0", false),
        ("1.0.0", "1.0.1", false),
        ("1.0.0", "1.0.1-0", false),
        ("1.0.0", "1.0.0-0", false),
        ("1.0.0", "1.0.0", true),
        ("1.0.0", "0.0.0", false),
        ("1.0.0", "0.0.0-0", false),
        ("1.0.0-0", "2.0.0", false),
        ("1.0.0-0", "2.0.0-0", false),
        ("1.0.0-0", "1.1.0", false),
        ("1.0.0-0", "1.1.0-0", false),
        ("1.0.0-0", "1.0.1", false),
        ("1.0.0-0", "1.0.1-0", false),
        ("1.0.0-0", "1.0.0", false),
        ("1.0.0-0", "1.0.0-0", true),
        // = wildcard major (matches everything)
        ("=*", "2.0.0", true),
        ("=*", "2.0.0-0", true),
        ("=*", "1.1.0", true),
        ("=*", "1.1.0-0", true),
        ("=*", "1.0.1", true),
        ("=*", "1.0.1-0", true),
        ("=*", "1.0.0", true),
        ("=*", "1.0.0-0", true),
        ("=*", "0.0.0", true),
        ("=*", "0.0.0-0", true),
        // = wildcard minor
        ("=1", "2.0.0", false),
        ("=1", "2.0.0-0", false),
        ("=1", "1.1.0", true),
        ("=1", "1.1.0-0", true),
        ("=1", "1.0.1", true),
        ("=1", "1.0.1-0", true),
        ("=1", "1.0.0", true),
        ("=1", "1.0.0-0", true),
        ("=1", "0.0.0", false),
        ("=1", "0.0.0-0", false),
        // = wildcard patch
        ("=1.1", "2.0.0", false),
        ("=1.1", "2.0.0-0", false),
        ("=1.1", "1.1.0", true),
        ("=1.1", "1.1.0-0", true),
        ("=1.1", "1.0.1", false),
        ("=1.1", "1.0.1-0", false),
        ("=1.1", "1.0.0", false),
        ("=1.1", "1.0.0-0", false),
        ("=1.1", "0.0.0", false),
        ("=1.1", "0.0.0-0", false),
        ("=1.0", "2.0.0", false),
        ("=1.0", "2.0.0-0", false),
        ("=1.0", "1.1.0", false),
        ("=1.0", "1.1.0-0", false),
        ("=1.0", "1.0.1", true),
        ("=1.0", "1.0.1-0", true),
        ("=1.0", "1.0.0", true),
        ("=1.0", "1.0.0-0", true),
        ("=1.0", "0.0.0", false),
        ("=1.0", "0.0.0-0", false),
        // = exact
        ("=1.1.0", "2.0.0", false),
        ("=1.1.0", "2.0.0-0", false),
        ("=1.1.0", "1.1.0", true),
        ("=1.1.0", "1.1.0-0", false),
        ("=1.1.0", "1.0.1", false),
        ("=1.1.0", "1.0.1-0", false),
        ("=1.1.0", "1.0.0-0", false),
        ("=1.1.0", "1.0.0", false),
        ("=1.1.0", "0.0.0", false),
        ("=1.1.0", "0.0.0-0", false),
        ("=1.1.0-0", "2.0.0", false),
        ("=1.1.0-0", "2.0.0-0", false),
        ("=1.1.0-0", "1.1.0", false),
        ("=1.1.0-0", "1.1.0-0", true),
        ("=1.1.0-0", "1.0.1", false),
        ("=1.1.0-0", "1.0.1-0", false),
        ("=1.1.0-0", "1.0.0-0", false),
        ("=1.1.0-0", "1.0.0", false),
        ("=1.1.0-0", "0.0.0", false),
        ("=1.1.0-0", "0.0.0-0", false),
        ("=1.0.1", "2.0.0", false),
        ("=1.0.1", "2.0.0-0", false),
        ("=1.0.1", "1.1.0", false),
        ("=1.0.1", "1.1.0-0", false),
        ("=1.0.1", "1.0.1", true),
        ("=1.0.1", "1.0.1-0", false),
        ("=1.0.1", "1.0.0-0", false),
        ("=1.0.1", "1.0.0", false),
        ("=1.0.1", "0.0.0", false),
        ("=1.0.1", "0.0.0-0", false),
        ("=1.0.1-0", "2.0.0", false),
        ("=1.0.1-0", "2.0.0-0", false),
        ("=1.0.1-0", "1.1.0", false),
        ("=1.0.1-0", "1.1.0-0", false),
        ("=1.0.1-0", "1.0.1", false),
        ("=1.0.1-0", "1.0.1-0", true),
        ("=1.0.1-0", "1.0.0-0", false),
        ("=1.0.1-0", "1.0.0", false),
        ("=1.0.1-0", "0.0.0", false),
        ("=1.0.1-0", "0.0.0-0", false),
        ("=1.0.0", "2.0.0", false),
        ("=1.0.0", "2.0.0-0", false),
        ("=1.0.0", "1.1.0", false),
        ("=1.0.0", "1.1.0-0", false),
        ("=1.0.0", "1.0.1", false),
        ("=1.0.0", "1.0.1-0", false),
        ("=1.0.0", "1.0.0-0", false),
        ("=1.0.0", "1.0.0", true),
        ("=1.0.0", "0.0.0", false),
        ("=1.0.0", "0.0.0-0", false),
        ("=1.0.0-0", "2.0.0", false),
        ("=1.0.0-0", "2.0.0-0", false),
        ("=1.0.0-0", "1.1.0", false),
        ("=1.0.0-0", "1.1.0-0", false),
        ("=1.0.0-0", "1.0.1", false),
        ("=1.0.0-0", "1.0.1-0", false),
        ("=1.0.0-0", "1.0.0", false),
        ("=1.0.0-0", "1.0.0-0", true),
        // > wildcard major (matches nothing)
        (">*", "2.0.0", false),
        (">*", "2.0.0-0", false),
        (">*", "1.1.0", false),
        (">*", "1.1.0-0", false),
        (">*", "1.0.1", false),
        (">*", "1.0.1-0", false),
        (">*", "1.0.0", false),
        (">*", "1.0.0-0", false),
        (">*", "0.0.0", false),
        (">*", "0.0.0-0", false),
        // > wildcard minor
        (">1", "2.0.0", true),
        (">1", "2.0.0-0", true),
        (">1", "1.1.0", false),
        (">1", "1.1.0-0", false),
        (">1", "1.0.1", false),
        (">1", "1.0.1-0", false),
        (">1", "1.0.0", false),
        (">1", "1.0.0-0", false),
        (">1", "0.0.0", false),
        (">1", "0.0.0-0", false),
        // > wildcard patch
        (">1.1", "2.0.0", true),
        (">1.1", "2.0.0-0", true),
        (">1.1", "1.1.0", false),
        (">1.1", "1.1.0-0", false),
        (">1.1", "1.0.1", false),
        (">1.1", "1.0.1-0", false),
        (">1.1", "1.0.0", false),
        (">1.1", "1.0.0-0", false),
        (">1.1", "0.0.0", false),
        (">1.1", "0.0.0-0", false),
        (">1.0", "2.0.0", true),
        (">1.0", "2.0.0-0", true),
        (">1.0", "1.1.0", true),
        (">1.0", "1.1.0-0", true),
        (">1.0", "1.0.1", false),
        (">1.0", "1.0.1-0", false),
        (">1.0", "1.0.0", false),
        (">1.0", "1.0.0-0", false),
        (">1.0", "0.0.0", false),
        (">1.0", "0.0.0-0", false),
        // > exact
        (">1.1.0", "2.0.0", true),
        (">1.1.0", "2.0.0-0", true),
        (">1.1.0", "1.1.0", false),
        (">1.1.0", "1.1.0-0", false),
        (">1.1.0", "1.0.1", false),
        (">1.1.0", "1.0.1-0", false),
        (">1.1.0", "1.0.0", false),
        (">1.1.0", "1.0.0-0", false),
        (">1.1.0", "0.0.0", false),
        (">1.1.0", "0.0.0-0", false),
        (">1.1.0-0", "2.0.0", true),
        (">1.1.0-0", "2.0.0-0", true),
        (">1.1.0-0", "1.1.0", true),
        (">1.1.0-0", "1.1.0-0", false),
        (">1.1.0-0", "1.0.1", false),
        (">1.1.0-0", "1.0.1-0", false),
        (">1.1.0-0", "1.0.0", false),
        (">1.1.0-0", "1.0.0-0", false),
        (">1.1.0-0", "0.0.0", false),
        (">1.1.0-0", "0.0.0-0", false),
        (">1.0.1", "2.0.0", true),
        (">1.0.1", "2.0.0-0", true),
        (">1.0.1", "1.1.0", true),
        (">1.0.1", "1.1.0-0", true),
        (">1.0.1", "1.0.1", false),
        (">1.0.1", "1.0.1-0", false),
        (">1.0.1", "1.0.0", false),
        (">1.0.1", "1.0.0-0", false),
        (">1.0.1", "0.0.0", false),
        (">1.0.1", "0.0.0-0", false),
        (">1.0.1-0", "2.0.0", true),
        (">1.0.1-0", "2.0.0-0", true),
        (">1.0.1-0", "1.1.0", true),
        (">1.0.1-0", "1.1.0-0", true),
        (">1.0.1-0", "1.0.1", true),
        (">1.0.1-0", "1.0.1-0", false),
        (">1.0.1-0", "1.0.0", false),
        (">1.0.1-0", "1.0.0-0", false),
        (">1.0.1-0", "0.0.0", false),
        (">1.0.1-0", "0.0.0-0", false),
        (">1.0.0", "2.0.0", true),
        (">1.0.0", "2.0.0-0", true),
        (">1.0.0", "1.1.0", true),
        (">1.0.0", "1.1.0-0", true),
        (">1.0.0", "1.0.1", true),
        (">1.0.0", "1.0.1-0", true),
        (">1.0.0", "1.0.0", false),
        (">1.0.0", "1.0.0-0", false),
        (">1.0.0", "0.0.0", false),
        (">1.0.0", "0.0.0-0", false),
        (">1.0.0-0", "2.0.0", true),
        (">1.0.0-0", "2.0.0-0", true),
        (">1.0.0-0", "1.1.0", true),
        (">1.0.0-0", "1.1.0-0", true),
        (">1.0.0-0", "1.0.1", true),
        (">1.0.0-0", "1.0.1-0", true),
        (">1.0.0-0", "1.0.0", true),
        (">1.0.0-0", "1.0.0-0", false),
        (">1.0.0-0", "0.0.0", false),
        (">1.0.0-0", "0.0.0-0", false),
        // >= wildcard major (matches everything)
        (">=*", "2.0.0", true),
        (">=*", "2.0.0-0", true),
        (">=*", "1.1.0", true),
        (">=*", "1.1.0-0", true),
        (">=*", "1.0.1", true),
        (">=*", "1.0.1-0", true),
        (">=*", "1.0.0", true),
        (">=*", "1.0.0-0", true),
        (">=*", "0.0.0", true),
        (">=*", "0.0.0-0", true),
        // >= wildcard minor
        (">=1", "2.0.0", true),
        (">=1", "2.0.0-0", true),
        (">=1", "1.1.0", true),
        (">=1", "1.1.0-0", true),
        (">=1", "1.0.1", true),
        (">=1", "1.0.1-0", true),
        (">=1", "1.0.0", true),
        (">=1", "1.0.0-0", true),
        (">=1", "0.0.0", false),
        (">=1", "0.0.0-0", false),
        // >= wildcard patch
        (">=1.1", "2.0.0", true),
        (">=1.1", "2.0.0-0", true),
        (">=1.1", "1.1.0", true),
        (">=1.1", "1.1.0-0", true),
        (">=1.1", "1.0.1", false),
        (">=1.1", "1.0.1-0", false),
        (">=1.1", "1.0.0", false),
        (">=1.1", "1.0.0-0", false),
        (">=1.1", "0.0.0", false),
        (">=1.1", "0.0.0-0", false),
        (">=1.0", "2.0.0", true),
        (">=1.0", "2.0.0-0", true),
        (">=1.0", "1.1.0", true),
        (">=1.0", "1.1.0-0", true),
        (">=1.0", "1.0.1", true),
        (">=1.0", "1.0.1-0", true),
        (">=1.0", "1.0.0", true),
        (">=1.0", "1.0.0-0", true),
        (">=1.0", "0.0.0", false),
        (">=1.0", "0.0.0-0", false),
        // >= exact
        (">=1.1.0", "2.0.0", true),
        (">=1.1.0", "2.0.0-0", true),
        (">=1.1.0", "1.1.0", true),
        (">=1.1.0", "1.1.0-0", false),
        (">=1.1.0", "1.0.1", false),
        (">=1.1.0", "1.0.1-0", false),
        (">=1.1.0", "1.0.0", false),
        (">=1.1.0", "1.0.0-0", false),
        (">=1.1.0", "0.0.0", false),
        (">=1.1.0", "0.0.0-0", false),
        (">=1.1.0-0", "2.0.0", true),
        (">=1.1.0-0", "2.0.0-0", true),
        (">=1.1.0-0", "1.1.0", true),
        (">=1.1.0-0", "1.1.0-0", true),
        (">=1.1.0-0", "1.0.1", false),
        (">=1.1.0-0", "1.0.1-0", false),
        (">=1.1.0-0", "1.0.0", false),
        (">=1.1.0-0", "1.0.0-0", false),
        (">=1.1.0-0", "0.0.0", false),
        (">=1.1.0-0", "0.0.0-0", false),
        (">=1.0.1", "2.0.0", true),
        (">=1.0.1", "2.0.0-0", true),
        (">=1.0.1", "1.1.0", true),
        (">=1.0.1", "1.1.0-0", true),
        (">=1.0.1", "1.0.1", true),
        (">=1.0.1", "1.0.1-0", false),
        (">=1.0.1", "1.0.0", false),
        (">=1.0.1", "1.0.0-0", false),
        (">=1.0.1", "0.0.0", false),
        (">=1.0.1", "0.0.0-0", false),
        (">=1.0.1-0", "2.0.0", true),
        (">=1.0.1-0", "2.0.0-0", true),
        (">=1.0.1-0", "1.1.0", true),
        (">=1.0.1-0", "1.1.0-0", true),
        (">=1.0.1-0", "1.0.1", true),
        (">=1.0.1-0", "1.0.1-0", true),
        (">=1.0.1-0", "1.0.0", false),
        (">=1.0.1-0", "1.0.0-0", false),
        (">=1.0.1-0", "0.0.0", false),
        (">=1.0.1-0", "0.0.0-0", false),
        (">=1.0.0", "2.0.0", true),
        (">=1.0.0", "2.0.0-0", true),
        (">=1.0.0", "1.1.0", true),
        (">=1.0.0", "1.1.0-0", true),
        (">=1.0.0", "1.0.1", true),
        (">=1.0.0", "1.0.1-0", true),
        (">=1.0.0", "1.0.0", true),
        (">=1.0.0", "1.0.0-0", false),
        (">=1.0.0", "0.0.0", false),
        (">=1.0.0", "0.0.0-0", false),
        (">=1.0.0-0", "2.0.0", true),
        (">=1.0.0-0", "2.0.0-0", true),
        (">=1.0.0-0", "1.1.0", true),
        (">=1.0.0-0", "1.1.0-0", true),
        (">=1.0.0-0", "1.0.1", true),
        (">=1.0.0-0", "1.0.1-0", true),
        (">=1.0.0-0", "1.0.0", true),
        (">=1.0.0-0", "1.0.0-0", true),
        (">=1.0.0-0", "0.0.0", false),
        (">=1.0.0-0", "0.0.0-0", false),
        // < wildcard major (matches nothing)
        ("<*", "2.0.0", false),
        ("<*", "2.0.0-0", false),
        ("<*", "1.1.0", false),
        ("<*", "1.1.0-0", false),
        ("<*", "1.0.1", false),
        ("<*", "1.0.1-0", false),
        ("<*", "1.0.0", false),
        ("<*", "1.0.0-0", false),
        ("<*", "0.0.0", false),
        ("<*", "0.0.0-0", false),
        // < wildcard minor
        ("<1", "2.0.0", false),
        ("<1", "2.0.0-0", false),
        ("<1", "1.1.0", false),
        ("<1", "1.1.0-0", false),
        ("<1", "1.0.1", false),
        ("<1", "1.0.1-0", false),
        ("<1", "1.0.0", false),
        ("<1", "1.0.0-0", false),
        ("<1", "0.0.0", true),
        ("<1", "0.0.0-0", true),
        // < wildcard patch
        ("<1.1", "2.0.0", false),
        ("<1.1", "2.0.0-0", false),
        ("<1.1", "1.1.0", false),
        ("<1.1", "1.1.0-0", false),
        ("<1.1", "1.0.1", true),
        ("<1.1", "1.0.1-0", true),
        ("<1.1", "1.0.0", true),
        ("<1.1", "1.0.0-0", true),
        ("<1.1", "0.0.0", true),
        ("<1.1", "0.0.0-0", true),
        ("<1.0", "2.0.0", false),
        ("<1.0", "2.0.0-0", false),
        ("<1.0", "1.1.0", false),
        ("<1.0", "1.1.0-0", false),
        ("<1.0", "1.0.1", false),
        ("<1.0", "1.0.1-0", false),
        ("<1.0", "1.0.0", false),
        ("<1.0", "1.0.0-0", false),
        ("<1.0", "0.0.0", true),
        ("<1.0", "0.0.0-0", true),
        // < exact
        ("<1.1.0", "2.0.0", false),
        ("<1.1.0", "2.0.0-0", false),
        ("<1.1.0", "1.1.0", false),
        ("<1.1.0", "1.1.0-0", true),
        ("<1.1.0", "1.0.1", true),
        ("<1.1.0", "1.0.1-0", true),
        ("<1.1.0", "1.0.0", true),
        ("<1.1.0", "1.0.0-0", true),
        ("<1.1.0", "0.0.0", true),
        ("<1.1.0", "0.0.0-0", true),
        ("<1.1.0-0", "2.0.0", false),
        ("<1.1.0-0", "2.0.0-0", false),
        ("<1.1.0-0", "1.1.0", false),
        ("<1.1.0-0", "1.1.0-0", false),
        ("<1.1.0-0", "1.0.1", true),
        ("<1.1.0-0", "1.0.1-0", true),
        ("<1.1.0-0", "1.0.0", true),
        ("<1.1.0-0", "1.0.0-0", true),
        ("<1.1.0-0", "0.0.0", true),
        ("<1.1.0-0", "0.0.0-0", true),
        ("<1.0.1", "2.0.0", false),
        ("<1.0.1", "2.0.0-0", false),
        ("<1.0.1", "1.1.0", false),
        ("<1.0.1", "1.1.0-0", false),
        ("<1.0.1", "1.0.1", false),
        ("<1.0.1", "1.0.1-0", true),
        ("<1.0.1", "1.0.0", true),
        ("<1.0.1", "1.0.0-0", true),
        ("<1.0.1", "0.0.0", true),
        ("<1.0.1", "0.0.0-0", true),
        ("<1.0.1-0", "2.0.0", false),
        ("<1.0.1-0", "2.0.0-0", false),
        ("<1.0.1-0", "1.1.0", false),
        ("<1.0.1-0", "1.1.0-0", false),
        ("<1.0.1-0", "1.0.1", false),
        ("<1.0.1-0", "1.0.1-0", false),
        ("<1.0.1-0", "1.0.0", true),
        ("<1.0.1-0", "1.0.0-0", true),
        ("<1.0.1-0", "0.0.0", true),
        ("<1.0.1-0", "0.0.0-0", true),
        ("<1.0.0", "2.0.0", false),
        ("<1.0.0", "2.0.0-0", false),
        ("<1.0.0", "1.1.0", false),
        ("<1.0.0", "1.1.0-0", false),
        ("<1.0.0", "1.0.1", false),
        ("<1.0.0", "1.0.1-0", false),
        ("<1.0.0", "1.0.0", false),
        ("<1.0.0", "1.0.0-0", true),
        ("<1.0.0", "0.0.0", true),
        ("<1.0.0", "0.0.0-0", true),
        ("<1.0.0-0", "2.0.0", false),
        ("<1.0.0-0", "2.0.0-0", false),
        ("<1.0.0-0", "1.1.0", false),
        ("<1.0.0-0", "1.1.0-0", false),
        ("<1.0.0-0", "1.0.1", false),
        ("<1.0.0-0", "1.0.1-0", false),
        ("<1.0.0-0", "1.0.0", false),
        ("<1.0.0-0", "1.0.0-0", false),
        ("<1.0.0-0", "0.0.0", true),
        ("<1.0.0-0", "0.0.0-0", true),
        // <= wildcard major (matches everything)
        ("<=*", "2.0.0", true),
        ("<=*", "2.0.0-0", true),
        ("<=*", "1.1.0", true),
        ("<=*", "1.1.0-0", true),
        ("<=*", "1.0.1", true),
        ("<=*", "1.0.1-0", true),
        ("<=*", "1.0.0", true),
        ("<=*", "1.0.0-0", true),
        ("<=*", "0.0.0", true),
        ("<=*", "0.0.0-0", true),
        // <= wildcard minor
        ("<=1", "2.0.0", false),
        ("<=1", "2.0.0-0", false),
        ("<=1", "1.1.0", true),
        ("<=1", "1.1.0-0", true),
        ("<=1", "1.0.1", true),
        ("<=1", "1.0.1-0", true),
        ("<=1", "1.0.0", true),
        ("<=1", "1.0.0-0", true),
        ("<=1", "0.0.0", true),
        ("<=1", "0.0.0-0", true),
        // <= wildcard patch
        ("<=1.1", "2.0.0", false),
        ("<=1.1", "2.0.0-0", false),
        ("<=1.1", "1.1.0", true),
        ("<=1.1", "1.1.0-0", true),
        ("<=1.1", "1.0.1", true),
        ("<=1.1", "1.0.1-0", true),
        ("<=1.1", "1.0.0", true),
        ("<=1.1", "1.0.0-0", true),
        ("<=1.1", "0.0.0", true),
        ("<=1.1", "0.0.0-0", true),
        ("<=1.0", "2.0.0", false),
        ("<=1.0", "2.0.0-0", false),
        ("<=1.0", "1.1.0", false),
        ("<=1.0", "1.1.0-0", false),
        ("<=1.0", "1.0.1", true),
        ("<=1.0", "1.0.1-0", true),
        ("<=1.0", "1.0.0", true),
        ("<=1.0", "1.0.0-0", true),
        ("<=1.0", "0.0.0", true),
        ("<=1.0", "0.0.0-0", true),
        // <= exact
        ("<=1.1.0", "2.0.0", false),
        ("<=1.1.0", "2.0.0-0", false),
        ("<=1.1.0", "1.1.0", true),
        ("<=1.1.0", "1.1.0-0", true),
        ("<=1.1.0", "1.0.1", true),
        ("<=1.1.0", "1.0.1-0", true),
        ("<=1.1.0", "1.0.0", true),
        ("<=1.1.0", "1.0.0-0", true),
        ("<=1.1.0", "0.0.0", true),
        ("<=1.1.0", "0.0.0-0", true),
        ("<=1.1.0-0", "2.0.0", false),
        ("<=1.1.0-0", "2.0.0-0", false),
        ("<=1.1.0-0", "1.1.0", false),
        ("<=1.1.0-0", "1.1.0-0", true),
        ("<=1.1.0-0", "1.0.1", true),
        ("<=1.1.0-0", "1.0.1-0", true),
        ("<=1.1.0-0", "1.0.0", true),
        ("<=1.1.0-0", "1.0.0-0", true),
        ("<=1.1.0-0", "0.0.0", true),
        ("<=1.1.0-0", "0.0.0-0", true),
        ("<=1.0.1", "2.0.0", false),
        ("<=1.0.1", "2.0.0-0", false),
        ("<=1.0.1", "1.1.0", false),
        ("<=1.0.1", "1.1.0-0", false),
        ("<=1.0.1", "1.0.1", true),
        ("<=1.0.1", "1.0.1-0", true),
        ("<=1.0.1", "1.0.0", true),
        ("<=1.0.1", "1.0.0-0", true),
        ("<=1.0.1", "0.0.0", true),
        ("<=1.0.1", "0.0.0-0", true),
        ("<=1.0.1-0", "2.0.0", false),
        ("<=1.0.1-0", "2.0.0-0", false),
        ("<=1.0.1-0", "1.1.0", false),
        ("<=1.0.1-0", "1.1.0-0", false),
        ("<=1.0.1-0", "1.0.1", false),
        ("<=1.0.1-0", "1.0.1-0", true),
        ("<=1.0.1-0", "1.0.0", true),
        ("<=1.0.1-0", "1.0.0-0", true),
        ("<=1.0.1-0", "0.0.0", true),
        ("<=1.0.1-0", "0.0.0-0", true),
        ("<=1.0.0", "2.0.0", false),
        ("<=1.0.0", "2.0.0-0", false),
        ("<=1.0.0", "1.1.0", false),
        ("<=1.0.0", "1.1.0-0", false),
        ("<=1.0.0", "1.0.1", false),
        ("<=1.0.0", "1.0.1-0", false),
        ("<=1.0.0", "1.0.0", true),
        ("<=1.0.0", "1.0.0-0", true),
        ("<=1.0.0", "0.0.0", true),
        ("<=1.0.0", "0.0.0-0", true),
        ("<=1.0.0-0", "2.0.0", false),
        ("<=1.0.0-0", "2.0.0-0", false),
        ("<=1.0.0-0", "1.1.0", false),
        ("<=1.0.0-0", "1.1.0-0", false),
        ("<=1.0.0-0", "1.0.1", false),
        ("<=1.0.0-0", "1.0.1-0", false),
        ("<=1.0.0-0", "1.0.0", false),
        ("<=1.0.0-0", "1.0.0-0", true),
        ("<=1.0.0-0", "0.0.0", true),
        ("<=1.0.0-0", "0.0.0-0", true),
        // https://github.com/microsoft/TypeScript/issues/50909
        (">4.8", "4.9.0-beta", true),
        (">=4.9", "4.9.0-beta", true),
        ("<4.9", "4.9.0-beta", false),
        ("<=4.8", "4.9.0-beta", false),
    ];
    check_range_tests("TestComparatorsOfVersionRanges", "comparators", tests);
}

// Go: version_range_test.go:806 TestConjunctionsOfVersionRanges
#[test]
fn test_conjunctions_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        (">1.0.0 <2.0.0", "1.0.1", true),
        (">1.0.0 <2.0.0", "2.0.0", false),
        (">1.0.0 <2.0.0", "1.0.0", false),
        (">1 >2", "3.0.0", true),
    ];
    check_range_tests("TestConjunctionsOfVersionRanges", "conjunctions", tests);
}

// Go: version_range_test.go:819 TestDisjunctionsOfVersionRanges
#[test]
fn test_disjunctions_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        (">1.0.0 || <1.0.0", "1.0.1", true),
        (">1.0.0 || <1.0.0", "0.0.1", true),
        (">1.0.0 || <1.0.0", "1.0.0", false),
        (">1.0.0 || <1.0.0", "0.0.0", true),
        (">=1.0.0 <2.0.0 || >=3.0.0 <4.0.0", "1.0.0", true),
        (">=1.0.0 <2.0.0 || >=3.0.0 <4.0.0", "2.0.0", false),
        (">=1.0.0 <2.0.0 || >=3.0.0 <4.0.0", "3.0.0", true),
    ];
    check_range_tests("TestDisjunctionsOfVersionRanges", "disjunctions", tests);
}

// Go: version_range_test.go:835 TestHyphensOfVersionRanges
#[test]
fn test_hyphens_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        ("1.0.0 - 2.0.0", "1.0.0", true),
        ("1.0.0 - 2.0.0", "1.0.1", true),
        ("1.0.0 - 2.0.0", "2.0.0", true),
        ("1.0.0 - 2.0.0", "2.0.1", false),
        ("1.0.0 - 2.0.0", "0.9.9", false),
        ("1.0.0 - 2.0.0", "3.0.0", false),
    ];
    check_range_tests("TestHyphensOfVersionRanges", "hyphens", tests);
}

// Go: version_range_test.go:850 TestTildesOfVersionRanges
#[test]
fn test_tildes_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        ("~0", "0.0.0", true),
        ("~0", "0.1.0", true),
        ("~0", "0.1.2", true),
        ("~0", "0.1.9", true),
        ("~0", "1.0.0", false),
        ("~0.1", "0.1.0", true),
        ("~0.1", "0.1.2", true),
        ("~0.1", "0.1.9", true),
        ("~0.1", "0.2.0", false),
        ("~0.1.2", "0.1.2", true),
        ("~0.1.2", "0.1.9", true),
        ("~0.1.2", "0.2.0", false),
        ("~1.0.0", "1.0.0", true),
        ("~1.0.0", "1.0.1", true),
        ("~1", "1.0.0", true),
        ("~1", "1.2.0", true),
        ("~1", "1.2.3", true),
        ("~1", "0.0.0", false),
        ("~1", "2.0.0", false),
        ("~1.2", "1.2.0", true),
        ("~1.2", "1.2.3", true),
        ("~1.2", "1.1.0", false),
        ("~1.2", "1.3.0", false),
        ("~1.2.3", "1.2.3", true),
        ("~1.2.3", "1.2.9", true),
        ("~1.2.3", "1.1.0", false),
        ("~1.2.3", "1.3.0", false),
    ];
    check_range_tests("TestTildesOfVersionRanges", "tilde", tests);
}

// Go: version_range_test.go:886 TestCaretsOfVersionRanges
#[test]
fn test_carets_of_version_ranges() {
    let tests: &[(&str, &str, bool)] = &[
        ("^0", "0.0.0", true),
        ("^0", "0.1.0", true),
        ("^0", "0.9.0", true),
        ("^0", "0.1.2", true),
        ("^0", "0.1.9", true),
        ("^0", "1.0.0", false),
        ("^0.1", "0.1.0", true),
        ("^0.1", "0.1.2", true),
        ("^0.1", "0.1.9", true),
        ("^0.1.2", "0.1.2", true),
        ("^0.1.2", "0.1.9", true),
        ("^0.1.2", "0.0.0", false),
        ("^0.1.2", "0.2.0", false),
        ("^0.1.2", "1.0.0", false),
        ("^1", "1.0.0", true),
        ("^1", "1.2.0", true),
        ("^1", "1.2.3", true),
        ("^1", "1.9.0", true),
        ("^1", "0.0.0", false),
        ("^1", "2.0.0", false),
        ("^1.2", "1.2.0", true),
        ("^1.2", "1.2.3", true),
        ("^1.2", "1.9.0", true),
        ("^1.2", "1.1.0", false),
        ("^1.2", "2.0.0", false),
        ("^1.2.3", "1.2.3", true),
        ("^1.2.3", "1.9.0", true),
        ("^1.2.3", "1.2.2", false),
        ("^1.2.3", "2.0.0", false),
    ];
    check_range_tests("TestCaretsOfVersionRanges", "caret", tests);
}
