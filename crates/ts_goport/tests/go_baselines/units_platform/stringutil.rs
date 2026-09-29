//! Go: `internal/stringutil/{js_case,util}_test.go`.
//!
//! PORT: Go `stringutil.ToLowerJS`, `ToUpperJS` and `EncodeJSStringRune` are
//! in `scanner_util`; `EncodeURI` is `emitter::emitter::encode_uri`. A lone
//! surrogate is the port form of `encode_js_string_rune`, not WTF-8.

use ts_goport::emitter::emitter::encode_uri;
use ts_goport::scanner_util::{encode_js_string_rune, to_lower_js, to_upper_js};

use super::Failures;

// Go: js_case_test.go:5 TestJSCasing
#[test]
fn test_js_casing() {
    let tests: Vec<(&str, String, String)> = vec![
        ("ascii lowercase", to_lower_js("HELLO"), "hello".to_string()),
        ("ascii uppercase", to_upper_js("hello"), "HELLO".to_string()),
        (
            "lowercase dotted i",
            to_lower_js("İSPANYOL"),
            "i̇spanyol".to_string(),
        ),
        ("lowercase lone sigma", to_lower_js("Σ"), "σ".to_string()),
        ("lowercase final sigma", to_lower_js("ΟΣ"), "ος".to_string()),
        (
            "lowercase non-sigma greek",
            to_lower_js("Ω"),
            "ω".to_string(),
        ),
        (
            "uppercase sharp s",
            to_upper_js("ßfoo"),
            "SSFOO".to_string(),
        ),
        (
            "uppercase non-ascii simple mapping",
            to_upper_js("ω"),
            "Ω".to_string(),
        ),
        ("uppercase ligature", to_upper_js("ﬁoo"), "FIOO".to_string()),
        (
            "capitalize-style uppercase",
            format!("{}{}", to_upper_js("ß"), "foo".to_string()),
            "SSfoo".to_string(),
        ),
        (
            "uncapitalize-style lowercase",
            format!("{}{}", to_lower_js("İ"), "foo".to_string()),
            "i̇foo".to_string(),
        ),
        (
            "lowercase final sigma after lowercase letter without uppercase mapping",
            to_lower_js("ʕΣ"),
            "ʕς".to_string(),
        ),
        (
            "lowercase sigma after modifier letter",
            to_lower_js("ʰΣ"),
            "ʰσ".to_string(),
        ),
        (
            "lowercase sigma after case ignorable ypogegrammeni",
            to_lower_js("ͅΣ"),
            "ͅσ".to_string(),
        ),
        (
            "lowercase final sigma after feminine ordinal indicator",
            to_lower_js("ªΣ"),
            "ªς".to_string(),
        ),
        (
            "lowercase final sigma after masculine ordinal indicator",
            to_lower_js("ºΣ"),
            "ºς".to_string(),
        ),
        (
            "lowercase final sigma after roman numeral",
            to_lower_js("ⅠΣ"),
            "ⅰς".to_string(),
        ),
        (
            "lowercase sigma after uppercase property added after unicode 15",
            to_lower_js("\u{1C89}Σ"),
            "\u{1C89}σ".to_string(),
        ),
        (
            "lowercase sigma after uppercase property skewed from local v8 unicode data",
            to_lower_js("\u{A7CB}Σ"),
            "\u{A7CB}σ".to_string(),
        ),
        (
            "lowercase sigma before immediate latin letter",
            to_lower_js("ΣA"),
            "σa".to_string(),
        ),
        (
            "lowercase sigma before immediate roman numeral letter",
            to_lower_js("ΣⅠ"),
            "σⅰ".to_string(),
        ),
        (
            "lowercase sigma before case ignorable then latin letter",
            to_lower_js("ΣͅA"),
            "σͅa".to_string(),
        ),
        (
            "uppercase lone surrogate",
            to_upper_js(&encode_js_string_rune(0xD800)),
            encode_js_string_rune(0xD800),
        ),
        (
            "lowercase lone surrogate",
            to_lower_js(&format!("A{}B", encode_js_string_rune(0xD800))),
            format!("a{}b", encode_js_string_rune(0xD800)),
        ),
        (
            "uppercase lone low surrogate with text",
            to_upper_js(&format!("{}x", encode_js_string_rune(0xDC00))),
            format!("{}X", encode_js_string_rune(0xDC00)),
        ),
        (
            "lowercase lone surrogate before sigma",
            to_lower_js(&format!("{}Σ", encode_js_string_rune(0xD800))),
            format!("{}σ", encode_js_string_rune(0xD800)),
        ),
    ];
    let mut failures = Failures::new("TestJSCasing");
    for (name, got, want) in tests {
        failures.check_eq(name, got, want);
    }
    failures.finish();
}

// Go: util_test.go:5 TestEncodeURI
#[test]
fn test_encode_uri() {
    let tests = [
        ("encodes spaces as percent20", "a b", "a%20b"),
        (
            "preserves reserved uri characters",
            ";/?:@&=+$,#",
            ";/?:@&=+$,#",
        ),
        (
            "encodes brackets and unicode using utf8 bytes",
            "①Ⅻㄨㄩ U1[abc]",
            "%E2%91%A0%E2%85%AB%E3%84%A8%E3%84%A9%20U1%5Babc%5D",
        ),
    ];
    let mut failures = Failures::new("TestEncodeURI");
    for (name, input, expected) in tests {
        failures.check_eq(name, encode_uri(input), expected.to_string());
    }
    failures.finish();
}
