//! Go: diagnostics/loc_generated.go, and the localization part of
//! diagnostics/diagnostics.go (`(*Message).Localize`, `Localize`,
//! `getLocalizedMessages`, `Format`).
//!
//! PORT: the message catalogs are the Go files `diagnostics/loc/*.json.gz`,
//! copied unchanged to `crates/ts_goport/data/loc/` and embedded with
//! `include_bytes!` in place of Go `//go:embed`.
//! PORT: Go `sync.OnceValue` is a `OnceLock` per catalog, and the Go
//! `sync.Map` cache is a `Mutex` around a map.

use crate::prelude::*;

use crate::frontend::json::json_unmarshal;
use crate::locale::{Locale, language};
use std::io::Read;
use std::sync::{LazyLock, Mutex, OnceLock, PoisonError};
use ts_diagnostics::Message;

// Go: diagnostics/diagnostics.go:44 Key
// PORT: a key is a `&str` (`Message::key`); catalogs map `String` keys.

/// A localized message catalog: message key to localized text.
pub type LocaleMessages = FxHashMap<String, String>;

// Go: diagnostics/loc_generated.go:14 matcher
static MATCHER: LazyLock<language::Matcher> = LazyLock::new(|| {
    language::new_matcher(&[
        language::english(),
        language::must_parse("zh-CN"),
        language::must_parse("zh-TW"),
        language::must_parse("cs-CZ"),
        language::must_parse("de-DE"),
        language::must_parse("es-ES"),
        language::must_parse("fr-FR"),
        language::must_parse("it-IT"),
        language::must_parse("ja-JP"),
        language::must_parse("ko-KR"),
        language::must_parse("pl-PL"),
        language::must_parse("pt-BR"),
        language::must_parse("ru-RU"),
        language::must_parse("tr-TR"),
    ])
});

// Go: diagnostics/loc_generated.go:31 localeFuncs
static LOCALE_FUNCS: [Option<fn() -> &'static LocaleMessages>; 14] = [
    None, // English (default)
    Some(zh_cn),
    Some(zh_tw),
    Some(cs_cz),
    Some(de_de),
    Some(es_es),
    Some(fr_fr),
    Some(it_it),
    Some(ja_jp),
    Some(ko_kr),
    Some(pl_pl),
    Some(pt_br),
    Some(ru_ru),
    Some(tr_tr),
];

// Go: diagnostics/loc_generated.go:48 loadLocaleData
/// PORT: Go creates the gzip reader first and panics if the header is bad.
/// `flate2` reads the header lazily, so a bad header panics with the first
/// message. Go `gzip.Reader` reads concatenated members, like
/// `MultiGzDecoder`. The embedded data is valid, so neither panic happens.
fn load_locale_data(data: &[u8]) -> LocaleMessages {
    let mut gr = flate2::read::MultiGzDecoder::new(data);
    let mut decoded = Vec::new();
    if let Err(err) = gr.read_to_end(&mut decoded) {
        panic!("failed to create gzip reader: {err}");
    }
    let mut result = LocaleMessages::default();
    if let Err(err) = json_unmarshal(&decoded, &mut result, &[]) {
        panic!("failed to unmarshal locale data: {err}");
    }
    result
}

/// Go: one `//go:embed loc/<locale>.json.gz` variable and its
/// `sync.OnceValue` loader.
macro_rules! locale_data {
    ($data:ident, $func:ident, $file:literal) => {
        static $data: &[u8] = include_bytes!(concat!("../data/loc/", $file));

        fn $func() -> &'static LocaleMessages {
            static MESSAGES: OnceLock<LocaleMessages> = OnceLock::new();
            MESSAGES.get_or_init(|| load_locale_data($data))
        }
    };
}

// Go: diagnostics/loc_generated.go:62 zhCNData, zhCN
locale_data!(ZH_CN_DATA, zh_cn, "zh-CN.json.gz");
// Go: diagnostics/loc_generated.go:69 zhTWData, zhTW
locale_data!(ZH_TW_DATA, zh_tw, "zh-TW.json.gz");
// Go: diagnostics/loc_generated.go:76 csCZData, csCZ
locale_data!(CS_CZ_DATA, cs_cz, "cs-CZ.json.gz");
// Go: diagnostics/loc_generated.go:83 deDEData, deDE
locale_data!(DE_DE_DATA, de_de, "de-DE.json.gz");
// Go: diagnostics/loc_generated.go:90 esESData, esES
locale_data!(ES_ES_DATA, es_es, "es-ES.json.gz");
// Go: diagnostics/loc_generated.go:97 frFRData, frFR
locale_data!(FR_FR_DATA, fr_fr, "fr-FR.json.gz");
// Go: diagnostics/loc_generated.go:104 itITData, itIT
locale_data!(IT_IT_DATA, it_it, "it-IT.json.gz");
// Go: diagnostics/loc_generated.go:111 jaJPData, jaJP
locale_data!(JA_JP_DATA, ja_jp, "ja-JP.json.gz");
// Go: diagnostics/loc_generated.go:118 koKRData, koKR
locale_data!(KO_KR_DATA, ko_kr, "ko-KR.json.gz");
// Go: diagnostics/loc_generated.go:125 plPLData, plPL
locale_data!(PL_PL_DATA, pl_pl, "pl-PL.json.gz");
// Go: diagnostics/loc_generated.go:132 ptBRData, ptBR
locale_data!(PT_BR_DATA, pt_br, "pt-BR.json.gz");
// Go: diagnostics/loc_generated.go:139 ruRUData, ruRU
locale_data!(RU_RU_DATA, ru_ru, "ru-RU.json.gz");
// Go: diagnostics/loc_generated.go:146 trTRData, trTR
locale_data!(TR_TR_DATA, tr_tr, "tr-TR.json.gz");

// Go: diagnostics/diagnostics.go:67 (*Message).Localize
/// PORT: Go takes `...any` and stringifies them (`StringifyArgs`); Rust
/// callers pass the strings.
pub fn message_localize(m: &'static Message, locale: &Locale, args: &[String]) -> String {
    localize(locale, Some(m), "", args)
}

// Go: diagnostics/diagnostics.go:71 Localize
/// PORT: Go `message *Message` is an `Option`; `None` looks the message up
/// by `key`.
pub fn localize(
    locale: &Locale,
    message: Option<&'static Message>,
    key: &str,
    args: &[String],
) -> String {
    let mut message = message;
    if message.is_none() {
        message = ts_diagnostics::message_by_key(key);
    }
    let Some(message) = message else {
        panic!("Unknown diagnostic message: {key}");
    };

    let mut text = message.text();
    if let Some(localized) =
        get_localized_messages(&locale.0).and_then(|messages| messages.get(message.key()))
    {
        text = localized;
    }

    format(text, args)
}

// Go: diagnostics/diagnostics.go:89 localizedMessagesCache
static LOCALIZED_MESSAGES_CACHE: LazyLock<
    Mutex<FxHashMap<language::Tag, Option<&'static LocaleMessages>>>,
> = LazyLock::new(|| Mutex::new(FxHashMap::default()));

// Go: diagnostics/diagnostics.go:91 getLocalizedMessages
fn get_localized_messages(loc: &language::Tag) -> Option<&'static LocaleMessages> {
    if *loc == language::Tag::UND {
        return None;
    }

    // Check cache first
    if let Some(cached) = LOCALIZED_MESSAGES_CACHE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(loc)
    {
        return *cached;
    }

    let mut messages = None;

    let (index, confidence) = MATCHER.match_(std::slice::from_ref(loc));
    if confidence >= language::Confidence::Low && index < LOCALE_FUNCS.len() {
        if let Some(f) = LOCALE_FUNCS[index] {
            messages = Some(f());
        }
    }

    LOCALIZED_MESSAGES_CACHE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .insert(loc.clone(), messages);
    messages
}

// Go: diagnostics/diagnostics.go:114 placeholderRegexp
// Go: diagnostics/diagnostics.go:116 Format
/// PORT: Go replaces `{(\d+)}` with `regexp.ReplaceAllStringFunc`. The loop
/// below finds the same leftmost, non-overlapping matches (`\d` is ASCII in
/// Go regexp).
pub fn format(text: &str, args: &[String]) -> String {
    if args.is_empty() {
        return text.to_string();
    }

    // Replace invalid UTF-8 with Unicode replacement character
    // PORT: each arg is the port form of a Go string (see
    // `scanner_util::GO_STRING_MARKER`), so only an arg with a marker can
    // hold invalid bytes.
    let valid: Vec<String>;
    let args = if args.iter().any(|arg| contains_go_string_marker(arg)) {
        valid = args
            .iter()
            .map(|arg| go_to_valid_utf8(arg).into_owned())
            .collect();
        &valid[..]
    } else {
        args
    };

    let bytes = text.as_bytes();
    let mut result = String::with_capacity(text.len());
    let mut last = 0;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'{' {
            let digits = bytes[i + 1..]
                .iter()
                .take_while(|c| c.is_ascii_digit())
                .count();
            if digits > 0 && bytes.get(i + 1 + digits) == Some(&b'}') {
                let Ok(index) = text[i + 1..i + 1 + digits].parse::<i64>() else {
                    panic!("Invalid formatting placeholder");
                };
                let Some(arg) = usize::try_from(index)
                    .ok()
                    .and_then(|index| args.get(index))
                else {
                    panic!("Invalid formatting placeholder");
                };
                result.push_str(&text[last..i]);
                result.push_str(arg);
                i += digits + 2;
                last = i;
                continue;
            }
        }
        i += 1;
    }
    result.push_str(&text[last..]);
    result
}

// Go: diagnostics/diagnostics.go:137 StringifyArgs
// PORT: not ported; Rust callers pass `String` args (see `message_localize`).

#[cfg(test)]
mod tests {
    use super::*;

    fn locale(s: &str) -> Locale {
        let (l, ok) = crate::locale::parse(s);
        assert!(ok, "{s} should parse");
        l
    }

    #[test]
    fn parse_reports_invalid_tags() {
        assert!(!crate::locale::parse("").1);
        assert!(!crate::locale::parse("xx").1);
        assert!(!crate::locale::parse("de-AB").1);
        assert!(!crate::locale::parse("toolongtagname").1);
        assert!(crate::locale::parse("de").1);
        assert!(crate::locale::parse("ja-jp").1);
        assert!(crate::locale::parse("en_US").1);
    }

    #[test]
    fn locales_match_like_tsgo() {
        // (tag, index in LOCALE_FUNCS or None for English), checked against
        // x/text v0.38.0 and tsgo-oracle --locale.
        let cases: [(&str, Option<usize>); 16] = [
            ("en-US", None),
            ("de", Some(4)),
            ("de-AT", Some(4)),
            ("zh-cn", Some(1)),
            ("zh-HK", Some(2)),
            ("zh-Hant", Some(2)),
            ("pt-PT", Some(11)),
            ("es-419", Some(5)),
            ("gl", Some(5)),
            ("gsw", Some(4)),
            ("be", Some(12)),
            ("und-JP", Some(8)),
            ("uk", None),
            ("sr", None),
            ("yue", None),
            ("x-foo", None),
        ];
        for (tag, want) in cases {
            let messages = get_localized_messages(&locale(tag).0);
            let want = want
                .and_then(|i| LOCALE_FUNCS[i])
                .map(|f| f() as *const LocaleMessages);
            let got = messages.map(|m| m as *const LocaleMessages);
            assert_eq!(got, want, "{tag}");
        }
    }

    #[test]
    fn localizes_messages() {
        let m = diag::Type_0_is_not_assignable_to_type_1;
        let args = args!["string", "number"];
        assert_eq!(
            message_localize(m, &locale("de"), &args),
            "Der Typ \"string\" kann dem Typ \"number\" nicht zugewiesen werden."
        );
        assert_eq!(
            message_localize(m, &locale("zh-cn"), &args),
            "不能将类型“string”分配给类型“number”。"
        );
        assert_eq!(
            message_localize(m, &crate::locale::DEFAULT, &args),
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn every_catalog_loads() {
        for f in LOCALE_FUNCS.iter().flatten() {
            assert!(!f().is_empty());
        }
    }

    #[test]
    fn format_matches_go_regexp() {
        let args = args!["a", "b"];
        assert_eq!(format("{0}{1}", &args), "ab");
        assert_eq!(format("{{0}} {x} {} {1", &args), "{a} {x} {} {1");
        assert_eq!(format("{0}", &[]), "{0}");
        // Go `strings.ToValidUTF8`: a run of invalid bytes (port form units,
        // see `scanner_util::GO_STRING_MARKER`) becomes one U+FFFD, and a
        // real U+FDD0 stays.
        let args = args!["a\u{FDD0}\u{10F7FE}\u{FDD0}\u{10F7FF}b", "\u{FDD0}\u{FDD0}"];
        assert_eq!(format("{0} {1}", &args), "a\u{FFFD}b \u{FDD0}\u{FDD0}");
    }
}
