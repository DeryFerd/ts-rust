//! Go: `internal/diagnostics/diagnostics_test.go`.
//!
//! PORT: Go `(*Message).Localize` and `diagnostics.Localize` are
//! `diagnostics_loc::{message_localize, localize}`; Go `language.English` is
//! `locale::language::english()`.

use ts_goport::diag;
use ts_goport::diagnostics_loc::{localize, message_localize};
use ts_goport::locale::{Locale, language};

use super::Failures;

fn tag(s: &str) -> Locale {
    Locale(language::must_parse(s))
}

// Go: diagnostics_test.go:11 TestLocalize
#[test]
fn test_localize() {
    let english = Locale(language::english());
    let und = Locale(language::Tag::UND);
    let tests: Vec<(
        &str,
        &'static ts_goport::diagnostics::Message,
        Locale,
        Vec<&str>,
        &str,
    )> = vec![
        (
            "english default",
            diag::Identifier_expected,
            english.clone(),
            vec![],
            "Identifier expected.",
        ),
        (
            "undefined locale uses english",
            diag::Identifier_expected,
            und,
            vec![],
            "Identifier expected.",
        ),
        (
            "with single argument",
            diag::X_0_expected,
            english.clone(),
            vec![")"],
            "')' expected.",
        ),
        (
            "with multiple arguments",
            diag::The_parser_expected_to_find_a_1_to_match_the_0_token_here,
            english,
            vec!["{", "}"],
            "The parser expected to find a '}' to match the '{' token here.",
        ),
        (
            "fallback to english for unknown locale",
            diag::Identifier_expected,
            tag("af-ZA"),
            vec![],
            "Identifier expected.",
        ),
        (
            "german",
            diag::Identifier_expected,
            tag("de-DE"),
            vec![],
            "Es wurde ein Bezeichner erwartet.",
        ),
        (
            "french",
            diag::Identifier_expected,
            tag("fr-FR"),
            vec![],
            "Identificateur attendu.",
        ),
        (
            "spanish",
            diag::Identifier_expected,
            tag("es-ES"),
            vec![],
            "Se esperaba un identificador.",
        ),
        (
            "japanese",
            diag::Identifier_expected,
            tag("ja-JP"),
            vec![],
            "識別子が必要です。",
        ),
        (
            "chinese simplified",
            diag::Identifier_expected,
            tag("zh-CN"),
            vec![],
            "应为标识符。",
        ),
        (
            "korean",
            diag::Identifier_expected,
            tag("ko-KR"),
            vec![],
            "식별자가 필요합니다.",
        ),
        (
            "russian",
            diag::Identifier_expected,
            tag("ru-RU"),
            vec![],
            "Ожидался идентификатор.",
        ),
        (
            "german with args",
            diag::X_0_expected,
            tag("de-DE"),
            vec![")"],
            "\")\" wurde erwartet.",
        ),
    ];
    let mut failures = Failures::new("TestLocalize");
    for (name, message, locale, args, expected) in tests {
        let args: Vec<String> = args.into_iter().map(String::from).collect();
        failures.check_eq(
            name,
            message_localize(message, &locale, &args),
            expected.to_string(),
        );
    }
    failures.finish();
}

// Go: diagnostics_test.go:113 TestLocalize_ByKey
#[test]
fn test_localize_by_key() {
    let english = Locale(language::english());
    let tests: Vec<(&str, &str, Vec<&str>, &str)> = vec![
        (
            "by key without args",
            "Identifier_expected_1003",
            vec![],
            "Identifier expected.",
        ),
        (
            "by key with args",
            "_0_expected_1005",
            vec![")"],
            "')' expected.",
        ),
    ];
    let mut failures = Failures::new("TestLocalize_ByKey");
    for (name, key, args, expected) in tests {
        let args: Vec<String> = args.into_iter().map(String::from).collect();
        failures.check_eq(
            name,
            localize(&english, None, key, &args),
            expected.to_string(),
        );
    }
    failures.finish();
}
