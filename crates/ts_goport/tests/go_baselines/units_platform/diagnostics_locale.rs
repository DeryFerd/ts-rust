//! Go: `internal/diagnostics/diagnostics_test.go` TestLocaleFiles and
//! TestLocaleFilesIgnoreStaleDiagnostics (ts#63987). The other tests of that
//! Go file are in diagnostics.rs.
//!
//! PORT: Go globs `loc/*.generated.json` next to the test. Here they are
//! `internal/diagnostics/loc/*.generated.json` in the Go checkout
//! (`TS_GO_REPO`). The typescript-go layout (pin B and older) has no
//! handback files and no TestLocaleFiles, so the test checks nothing there.
//! Go `getLocalizedMessages` is `diagnostics_loc::get_localized_messages`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use ts_goport::diag;
use ts_goport::diagnostics_loc::{LocaleMessages, get_localized_messages};
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::locale::language;

use super::Failures;
use crate::support::baseline::{go_repo, is_merged_layout};

// Go: diagnostics_test.go:151 TestLocaleFiles
#[test]
fn test_locale_files() {
    if !is_merged_layout() {
        eprintln!("TestLocaleFiles: skipped: the Go checkout has no loc/*.generated.json");
        return;
    }

    let loc_dir = go_repo().join("internal").join("diagnostics").join("loc");
    let entries = std::fs::read_dir(&loc_dir)
        .unwrap_or_else(|err| panic!("read {}: {err}", loc_dir.display()));
    // Go `filepath.Glob` returns the matches in lexical order.
    let mut files: Vec<PathBuf> = entries
        .map(|entry| entry.expect("read the loc directory").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".generated.json"))
        })
        .collect();
    files.sort();
    assert!(!files.is_empty());

    let mut failures = Failures::new("TestLocaleFiles");
    for path in &files {
        let file_name = path.file_name().and_then(|name| name.to_str()).unwrap();
        let locale_name = file_name.strip_suffix(".generated.json").unwrap();

        let data = match std::fs::read(path) {
            Ok(data) => data,
            Err(err) => {
                failures.fail(locale_name, format!("open {}: {err}", path.display()));
                continue;
            }
        };

        let mut handback = LocaleMessages::default();
        if let Err(err) = json_unmarshal(&data, &mut handback, &[]) {
            failures.fail(locale_name, format!("unmarshal: {err:?}"));
            continue;
        }
        validate_localized_messages(&mut failures, locale_name, &handback);

        let active_messages: BTreeMap<&str, &str> = handback
            .iter()
            .filter(|(key, _)| diag::key_to_message(key).is_some())
            .map(|(key, text)| (key.as_str(), text.as_str()))
            .collect();

        // Go `assert.DeepEqual(t, actual, activeMessages)`: a nil map (no
        // catalog for the locale) never equals the non-nil `activeMessages`.
        let Some(actual) = get_localized_messages(&language::must_parse(locale_name)) else {
            failures.fail(locale_name, "no localized messages".to_string());
            continue;
        };
        let actual: BTreeMap<&str, &str> = actual
            .iter()
            .map(|(key, text)| (key.as_str(), text.as_str()))
            .collect();
        if let Some(difference) = map_difference(&actual, &active_messages) {
            failures.fail(locale_name, difference);
        }
    }
    failures.finish();
}

// Go: diagnostics_test.go:184 TestLocaleFilesIgnoreStaleDiagnostics
#[test]
fn test_locale_files_ignore_stale_diagnostics() {
    let mut failures = Failures::new("TestLocaleFilesIgnoreStaleDiagnostics");
    let mut localized_messages = LocaleMessages::default();
    localized_messages.insert(
        "Removed_diagnostic_99999".to_string(),
        "Stale translation.".to_string(),
    );
    validate_localized_messages(
        &mut failures,
        "TestLocaleFilesIgnoreStaleDiagnostics",
        &localized_messages,
    );
    failures.finish();
}

// Go: diagnostics_test.go:191 validateLocalizedMessages
// PORT: Go ranges over the map in random order and stops the subtest at the
// first failed assert. The port checks the keys in sorted order and records
// every failure.
fn validate_localized_messages(
    failures: &mut Failures,
    name: &str,
    localized_messages: &LocaleMessages,
) {
    let sorted: BTreeMap<&String, &String> = localized_messages.iter().collect();
    for (key, localized_text) in sorted {
        let Some(message) = diag::key_to_message(key) else {
            continue;
        };
        let localized_placeholders = placeholder_set(localized_text);
        let english_placeholders = placeholder_set(message.text());
        if localized_placeholders.len() != english_placeholders.len() {
            failures.fail(
                name,
                format!(
                    "placeholder mismatch for {key:?}: {} (int) != {} (int)",
                    localized_placeholders.len(),
                    english_placeholders.len()
                ),
            );
        }
        for placeholder in &english_placeholders {
            if !localized_placeholders.contains(placeholder) {
                failures.fail(
                    name,
                    format!("localized diagnostic {key:?} is missing placeholder {placeholder}"),
                );
            }
        }
    }
}

// Go: diagnostics_test.go:207 placeholderSet
// PORT: Go collects the matches of `placeholderRegexp` (`{(\d+)}`,
// diagnostics.go:127). The loop finds the same leftmost, non-overlapping
// matches (`\d` is ASCII in Go regexp).
fn placeholder_set(text: &str) -> BTreeSet<&str> {
    let bytes = text.as_bytes();
    let mut result = BTreeSet::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'{' {
            let digits = bytes[i + 1..]
                .iter()
                .take_while(|c| c.is_ascii_digit())
                .count();
            if digits > 0 && bytes.get(i + 1 + digits) == Some(&b'}') {
                result.insert(&text[i..i + 2 + digits]);
                i += 2 + digits;
                continue;
            }
        }
        i += 1;
    }
    result
}

/// The difference of Go `assert.DeepEqual(actual, want)` for two message
/// maps: the counts of missing, extra and changed keys and the first few of
/// each, or `None` when the maps are equal.
// PORT: Go prints the whole go-cmp diff. The maps hold about 2,100 messages,
// so the port names the first keys only.
fn map_difference(actual: &BTreeMap<&str, &str>, want: &BTreeMap<&str, &str>) -> Option<String> {
    const SHOWN: usize = 5;
    let missing: Vec<&str> = want
        .keys()
        .filter(|key| !actual.contains_key(*key))
        .copied()
        .collect();
    let extra: Vec<&str> = actual
        .keys()
        .filter(|key| !want.contains_key(*key))
        .copied()
        .collect();
    let changed: Vec<&str> = want
        .iter()
        .filter(|(key, text)| actual.get(*key).is_some_and(|got| got != *text))
        .map(|(key, _)| *key)
        .collect();
    if missing.is_empty() && extra.is_empty() && changed.is_empty() {
        return None;
    }
    fn first<'a>(keys: &[&'a str]) -> Vec<&'a str> {
        keys.iter().take(SHOWN).copied().collect()
    }
    Some(format!(
        "localized messages differ from the active handback messages: {} missing {:?}, {} extra {:?}, {} changed {:?}",
        missing.len(),
        first(&missing),
        extra.len(),
        first(&extra),
        changed.len(),
        first(&changed)
    ))
}
