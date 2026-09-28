//! Ports of the two internal/ls/lsutil/userpreferences_test.go tests that Go
//! #4505 added: TestUserPreferencesParseServerFeaturePreferences and
//! TestUserPreferencesParseJSDocCompletionPreferences. The other tests of
//! that Go file are in `ls_tests.rs`.

use super::{Subtests, assert_equal};
use indexmap::IndexMap;
use ts_goport::frontend::json_ext::LspAny;
use ts_goport::ls::lsutil::parse_user_preferences;
use ts_goport::options::Tristate;

/// Go `map[string]any{...}` literal.
fn obj(entries: &[(&str, LspAny)]) -> LspAny {
    LspAny::Object(
        entries
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect(),
    )
}

/// The top-level Go `map[string]any{...}` given to `ParseUserPreferences`.
fn items(entries: &[(&str, LspAny)]) -> IndexMap<String, LspAny> {
    match obj(entries) {
        LspAny::Object(m) => m,
        _ => unreachable!(),
    }
}

fn enabled(value: bool) -> LspAny {
    obj(&[("enabled", LspAny::Bool(value))])
}

fn enable(value: bool) -> LspAny {
    obj(&[("enable", LspAny::Bool(value))])
}

// Go: ls/lsutil/userpreferences_test.go:459 TestUserPreferencesParseServerFeaturePreferences
#[test]
fn test_user_preferences_parse_server_feature_preferences() {
    let mut t = Subtests::new("TestUserPreferencesParseServerFeaturePreferences");

    let check = |prefs: ts_goport::ls::lsutil::UserPreferences, want: Tristate| {
        assert_equal(prefs.enable_validation, want, "EnableValidation")?;
        assert_equal(prefs.enable_formatting, want, "EnableFormatting")?;
        assert_equal(
            prefs.enable_auto_closing_tags,
            want,
            "EnableAutoClosingTags",
        )
    };

    t.run("preferred server feature settings", || {
        let prefs = parse_user_preferences(&items(&[(
            "js/ts",
            obj(&[
                ("validate", enabled(false)),
                ("format", enabled(false)),
                ("autoClosingTags", enabled(false)),
            ]),
        )]));
        check(prefs, Tristate::False)
    });

    t.run("legacy server feature fallbacks", || {
        let prefs = parse_user_preferences(&items(&[(
            "typescript",
            obj(&[
                ("validate", enable(false)),
                ("format", enable(false)),
                ("autoClosingTags", LspAny::Bool(false)),
            ]),
        )]));
        check(prefs, Tristate::False)
    });

    t.run("preferred settings take precedence over fallbacks", || {
        let prefs = parse_user_preferences(&items(&[
            (
                "typescript",
                obj(&[
                    ("validate", enable(false)),
                    ("format", enable(false)),
                    ("autoClosingTags", LspAny::Bool(false)),
                ]),
            ),
            (
                "js/ts",
                obj(&[
                    ("validate", enabled(true)),
                    ("format", enabled(true)),
                    ("autoClosingTags", enabled(true)),
                ]),
            ),
        ]));
        check(prefs, Tristate::True)
    });

    t.finish();
}

/// Go `map[string]any{section: {"suggest": suggest}}`.
fn suggest(section: &str, suggest: LspAny) -> (&str, LspAny) {
    (section, obj(&[("suggest", suggest)]))
}

// Go: ls/lsutil/userpreferences_test.go:514 TestUserPreferencesParseJSDocCompletionPreferences
#[test]
fn test_user_preferences_parse_js_doc_completion_preferences() {
    let mut t = Subtests::new("TestUserPreferencesParseJSDocCompletionPreferences");

    t.run("unified jsdoc enabled setting", || {
        let prefs = parse_user_preferences(&items(&[suggest(
            "js/ts",
            obj(&[("jsdoc", enabled(false))]),
        )]));
        assert_equal(
            prefs.enable_js_doc_completions,
            Tristate::False,
            "EnableJSDocCompletions",
        )
    });

    t.run("language fallback completeJSDocs setting", || {
        let prefs = parse_user_preferences(&items(&[suggest(
            "typescript",
            obj(&[("completeJSDocs", LspAny::Bool(false))]),
        )]));
        assert_equal(
            prefs.enable_js_doc_completions,
            Tristate::False,
            "EnableJSDocCompletions",
        )
    });

    t.run(
        "unified jsdoc enabled takes precedence over language fallback",
        || {
            let prefs = parse_user_preferences(&items(&[
                suggest(
                    "typescript",
                    obj(&[("completeJSDocs", LspAny::Bool(false))]),
                ),
                suggest("js/ts", obj(&[("jsdoc", enabled(true))])),
            ]));
            assert_equal(
                prefs.enable_js_doc_completions,
                Tristate::True,
                "EnableJSDocCompletions",
            )
        },
    );

    let generate_returns = obj(&[("jsdoc", obj(&[("generateReturns", LspAny::Bool(false))]))]);

    t.run("unified jsdoc generateReturns setting", || {
        let prefs = parse_user_preferences(&items(&[suggest("js/ts", generate_returns.clone())]));
        assert_equal(
            prefs.generate_return_in_doc_template,
            Tristate::False,
            "GenerateReturnInDocTemplate",
        )
    });

    t.run("language jsdoc generateReturns setting", || {
        let prefs =
            parse_user_preferences(&items(&[suggest("typescript", generate_returns.clone())]));
        assert_equal(
            prefs.generate_return_in_doc_template,
            Tristate::False,
            "GenerateReturnInDocTemplate",
        )
    });

    t.finish();
}
