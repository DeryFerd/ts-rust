//! Pinned spelling-suggestion selection.
//!
//! This is the generic kernel from typescript-go's
//! `internal/core/core.go::GetSpellingSuggestion` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Candidate filtering remains a
//! caller concern: returning `None` from `get_name` is the typed equivalent of
//! the upstream empty-name sentinel used for symbols with the wrong meaning.
//!
//! Rust's standard library does not expose Go's simple case-mapping tables.
//! This port reconstructs the pinned Go Unicode 15 mappings from Rust's scalar
//! mappings, with explicit handling for dotted capital I and the theta-symbol
//! fold orbit. Mappings added by the Rust toolchain's newer Unicode tables are
//! suppressed below so the suggestion policy remains pinned to Unicode 15.

use std::cmp::Ordering;

/// Returns the closest eligible spelling candidate under TypeScript's pinned
/// weighted edit-distance policy.
///
/// Equal-distance candidates are ordered by `compare`. If the comparator also
/// reports equality, the first candidate in input order is retained.
#[allow(dead_code)] // Installed ahead of the property-diagnostic consumer.
pub(super) fn get_spelling_suggestion<'name, Candidate, Candidates, GetName, Compare>(
    name: &str,
    candidates: Candidates,
    get_name: GetName,
    compare: Compare,
) -> Option<Candidate>
where
    Candidates: IntoIterator<Item = Candidate>,
    GetName: Fn(&Candidate) -> Option<&'name str>,
    Compare: Fn(&Candidate, &Candidate) -> Ordering,
{
    let name_characters = name.chars().collect::<Vec<_>>();
    let maximum_length_difference = 2_usize.max((name_characters.len() as f64 * 0.34) as usize);
    let mut best_distance = (name_characters.len() as f64 * 0.4).floor() + 0.9;
    let mut buffers = LevenshteinBuffers::default();
    let mut best_candidate = None;

    for candidate in candidates {
        let Some(candidate_name) = get_name(&candidate).filter(|name| !name.is_empty()) else {
            continue;
        };

        // Preserve the pinned implementation's deliberately observable units:
        // the requested name is measured in Unicode scalar values, while the
        // candidate is measured in UTF-8 bytes here and in the short-name gate.
        let maximum_length = candidate_name.len().max(name_characters.len());
        let minimum_length = candidate_name.len().min(name_characters.len());
        if maximum_length - minimum_length > maximum_length_difference
            || candidate_name == name
            || candidate_name.len() < 3 && !unicode_equal_fold(candidate_name, name)
        {
            continue;
        }

        let candidate_characters = candidate_name.chars().collect::<Vec<_>>();
        let Some(distance) = levenshtein_with_max(
            &mut buffers,
            &name_characters,
            &candidate_characters,
            best_distance,
        ) else {
            continue;
        };
        debug_assert!(distance <= best_distance);

        let replace = distance < best_distance
            || best_candidate
                .as_ref()
                .is_none_or(|best| compare(&candidate, best).is_lt());
        if replace {
            best_distance = distance;
            best_candidate = Some(candidate);
        }
    }

    best_candidate
}

/// String-specialized form using TypeScript's lexical tie-break.
#[allow(dead_code)] // Installed ahead of the property-diagnostic consumer.
pub(super) fn get_spelling_suggestion_for_strings<'candidate>(
    name: &str,
    candidates: impl IntoIterator<Item = &'candidate str>,
) -> Option<&'candidate str> {
    get_spelling_suggestion(
        name,
        candidates,
        |candidate| Some(*candidate),
        |left, right| left.cmp(right),
    )
}

#[derive(Default)]
struct LevenshteinBuffers {
    previous: Vec<f64>,
    current: Vec<f64>,
}

/// Computes the pinned weighted Levenshtein distance, stopping once the active
/// band proves that the result cannot return below `maximum`.
fn levenshtein_with_max(
    buffers: &mut LevenshteinBuffers,
    left: &[char],
    right: &[char],
    maximum: f64,
) -> Option<f64> {
    let buffer_size = right.len() + 1;
    buffers.previous.resize(buffer_size, 0.0);
    buffers.current.resize(buffer_size, 0.0);

    let previous = &mut buffers.previous;
    let current = &mut buffers.current;
    let big = maximum + 0.01;
    for (index, value) in previous.iter_mut().enumerate() {
        *value = index as f64;
    }

    let mut previous = previous.as_mut_slice();
    let mut current = current.as_mut_slice();
    for row in 1..=left.len() {
        let left_character = left[row - 1];
        let minimum_column = ((row as f64 - maximum).ceil() as isize).max(1) as usize;
        let maximum_column = ((maximum + row as f64).floor() as usize).min(right.len());
        let mut column_minimum = row as f64;
        current[0] = column_minimum;

        for value in current.iter_mut().take(minimum_column).skip(1) {
            *value = big;
        }
        for column in minimum_column..=maximum_column {
            let substitution_distance =
                if simple_lowercase(left_character) == simple_lowercase(right[column - 1]) {
                    previous[column - 1] + 0.1
                } else {
                    previous[column - 1] + 2.0
                };
            let distance = if left_character == right[column - 1] {
                previous[column - 1]
            } else {
                (previous[column] + 1.0)
                    .min(current[column - 1] + 1.0)
                    .min(substitution_distance)
            };
            current[column] = distance;
            column_minimum = column_minimum.min(distance);
        }
        for value in current.iter_mut().skip(maximum_column + 1) {
            *value = big;
        }
        if column_minimum > maximum {
            return None;
        }
        std::mem::swap(&mut previous, &mut current);
    }

    let result = previous[right.len()];
    (result <= maximum).then_some(result)
}

/// Rust exposes full Unicode mappings as iterators. Go's `unicode.ToLower`
/// uses one-rune simple mappings, so expansions deliberately retain the input.
fn simple_lowercase(character: char) -> char {
    // Rust exposes the full `i` + combining-dot mapping, while Go's
    // `unicode.ToLower` returns the one-rune simple mapping.
    if character == '\u{0130}' {
        'i'
    } else if has_post_unicode_15_lowercase_mapping(character) {
        character
    } else {
        single_character_mapping(character, character.to_lowercase())
    }
}

fn simple_uppercase(character: char) -> char {
    if has_post_unicode_15_uppercase_mapping(character) {
        character
    } else {
        single_character_mapping(character, character.to_uppercase())
    }
}

/// Uppercase sides of case pairs known to Rust but absent from Go's pinned
/// Unicode 15 tables. Their newer lowercase mappings must remain invisible.
fn has_post_unicode_15_lowercase_mapping(character: char) -> bool {
    matches!(
        character,
        '\u{1C89}'
            | '\u{A7CB}'
            | '\u{A7CC}'
            | '\u{A7CE}'
            | '\u{A7D2}'
            | '\u{A7D4}'
            | '\u{A7DA}'
            | '\u{A7DC}'
            | '\u{10D50}'..='\u{10D65}'
            | '\u{16EA0}'..='\u{16EB8}'
    )
}

/// Lowercase sides of case pairs known to Rust but absent from Go's pinned
/// Unicode 15 tables. Their newer uppercase mappings must remain invisible.
fn has_post_unicode_15_uppercase_mapping(character: char) -> bool {
    matches!(
        character,
        '\u{019B}'
            | '\u{0264}'
            | '\u{1C8A}'
            | '\u{A7CD}'
            | '\u{A7CF}'
            | '\u{A7D3}'
            | '\u{A7D5}'
            | '\u{A7DB}'
            | '\u{10D70}'..='\u{10D85}'
            | '\u{16EBB}'..='\u{16ED3}'
    )
}

fn single_character_mapping(original: char, mut mapped: impl Iterator<Item = char>) -> char {
    let first = mapped.next().unwrap_or(original);
    if mapped.next().is_none() {
        first
    } else {
        original
    }
}

/// The short-name gate uses Go's `strings.EqualFold`, whose simple-fold
/// equivalence includes compatibility characters such as Kelvin sign and the
/// Greek final sigma but excludes locale-specific Turkic-I folding.
fn unicode_equal_fold(left: &str, right: &str) -> bool {
    let mut left = left.chars();
    let mut right = right.chars();
    loop {
        match (left.next(), right.next()) {
            (None, None) => return true,
            (Some(left), Some(right)) if simple_fold_equal(left, right) => {}
            _ => return false,
        }
    }
}

fn simple_fold_equal(left: char, right: char) -> bool {
    if left == right {
        return true;
    }
    // Unicode default simple folding intentionally has no Turkic-I mapping.
    if matches!(left, '\u{0130}' | '\u{0131}') || matches!(right, '\u{0130}' | '\u{0131}') {
        return false;
    }
    simple_lowercase(left) == simple_lowercase(right)
        || simple_uppercase(left) == simple_uppercase(right)
        // This is the sole pinned `caseOrbit` edge not reconstructed by the
        // common simple lower/upper mappings.
        || matches!((left, right), ('\u{03D1}', '\u{03F4}') | ('\u{03F4}', '\u{03D1}'))
}

#[cfg(test)]
mod tests {
    use super::{
        LevenshteinBuffers, get_spelling_suggestion, get_spelling_suggestion_for_strings,
        levenshtein_with_max, simple_lowercase, simple_uppercase, unicode_equal_fold,
    };
    use std::cmp::Ordering;

    fn distance(left: &str, right: &str, maximum: f64) -> Option<f64> {
        levenshtein_with_max(
            &mut LevenshteinBuffers::default(),
            &left.chars().collect::<Vec<_>>(),
            &right.chars().collect::<Vec<_>>(),
            maximum,
        )
    }

    #[test]
    fn weighted_distance_preserves_exact_case_insertion_and_substitution_costs() {
        assert_eq!(distance("same", "same", 0.0), Some(0.0));
        assert_eq!(distance("A", "a", 0.1), Some(0.1));
        assert_eq!(distance("ab", "a", 1.0), Some(1.0));
        assert_eq!(distance("a", "ab", 1.0), Some(1.0));
        assert_eq!(distance("a", "b", 2.0), Some(2.0));
        assert_eq!(distance("a", "b", 1.99), None);
        assert_eq!(distance("ab", "ba", 2.0), Some(2.0));
    }

    #[test]
    fn ascii_candidates_use_weighted_distance_and_lexical_ties() {
        assert_eq!(
            get_spelling_suggestion_for_strings("value", ["valeu", "values", "vault"]),
            Some("values")
        );
        assert_eq!(
            get_spelling_suggestion_for_strings("abcdef", ["abcxef", "abcdxf"]),
            Some("abcdxf")
        );
    }

    #[test]
    fn equal_comparator_retains_input_order_for_equal_distances() {
        let candidates = [(1_u8, "abcxef"), (2, "abcdxf")];
        let selected = get_spelling_suggestion(
            "abcdef",
            candidates,
            |candidate| Some(candidate.1),
            |_, _| Ordering::Equal,
        );
        assert_eq!(selected, Some((1, "abcxef")));
    }

    #[test]
    fn generic_candidates_can_borrow_names_from_an_external_store() {
        let names = ["values".to_owned(), "value".to_owned()];
        let selected = get_spelling_suggestion(
            "value",
            [0_usize, 1],
            |candidate| names.get(*candidate).map(String::as_str),
            usize::cmp,
        );
        assert_eq!(selected, Some(0));
    }

    #[test]
    fn exact_names_empty_names_and_ineligible_candidates_are_excluded() {
        let candidates = [
            (0_u8, Some("value")),
            (1, Some("")),
            (2, None),
            (3, Some("values")),
        ];
        assert_eq!(
            get_spelling_suggestion(
                "value",
                candidates,
                |candidate| candidate.1,
                |left, right| left.0.cmp(&right.0),
            ),
            Some((3, Some("values")))
        );
        assert_eq!(
            get_spelling_suggestion_for_strings("value", ["value"]),
            None
        );
        assert_eq!(
            get_spelling_suggestion_for_strings("", ["", "a", "AB"]),
            None
        );
    }

    #[test]
    fn names_shorter_than_three_bytes_require_unicode_case_equality() {
        assert_eq!(
            get_spelling_suggestion_for_strings("ab", ["ac", "AB"]),
            Some("AB")
        );
        assert_eq!(get_spelling_suggestion_for_strings("a", ["b"]), None);
        assert_eq!(get_spelling_suggestion_for_strings("É", ["é"]), Some("é"));

        // Audit the special multi-member classes in Go's `caseOrbit` table.
        assert!(unicode_equal_fold("K", "K"));
        assert!(unicode_equal_fold("S", "ſ"));
        assert!(unicode_equal_fold("Σ", "ς"));
        assert!(unicode_equal_fold("µ", "μ"));
        assert!(unicode_equal_fold("ϑ", "ϴ"));

        // Default Unicode folding deliberately excludes Turkic-I mappings.
        assert!(!unicode_equal_fold("I", "ı"));
        assert!(!unicode_equal_fold("İ", "i"));
    }

    #[test]
    fn newer_rust_case_pairs_remain_unmapped_under_pinned_unicode_15() {
        fn assert_unmapped_pair(uppercase: char, lowercase: char) {
            assert_eq!(simple_lowercase(uppercase), uppercase);
            assert_eq!(simple_uppercase(lowercase), lowercase);
            assert!(!unicode_equal_fold(
                &uppercase.to_string(),
                &lowercase.to_string()
            ));
        }

        let singleton_pairs = [
            ('\u{A7DC}', '\u{019B}'),
            ('\u{A7CB}', '\u{0264}'),
            ('\u{1C89}', '\u{1C8A}'),
            ('\u{A7CC}', '\u{A7CD}'),
            ('\u{A7CE}', '\u{A7CF}'),
            ('\u{A7D2}', '\u{A7D3}'),
            ('\u{A7D4}', '\u{A7D5}'),
            ('\u{A7DA}', '\u{A7DB}'),
        ];
        for (uppercase, lowercase) in singleton_pairs {
            assert_unmapped_pair(uppercase, lowercase);
        }

        let grouped_ranges = [
            (0x10D50_u32, 0x10D65_u32, 0x10D70_u32),
            (0x16EA0_u32, 0x16EB8_u32, 0x16EBB_u32),
        ];
        let mut range_pair_count = 0;
        for (uppercase_start, uppercase_end, lowercase_start) in grouped_ranges {
            for uppercase in uppercase_start..=uppercase_end {
                let lowercase = lowercase_start + uppercase - uppercase_start;
                assert_unmapped_pair(
                    char::from_u32(uppercase).expect("valid uppercase scalar"),
                    char::from_u32(lowercase).expect("valid lowercase scalar"),
                );
                range_pair_count += 1;
            }
        }
        assert_eq!(singleton_pairs.len() + range_pair_count, 55);

        assert!(!unicode_equal_fold("Ƛ", "ƛ"));
        assert_eq!(get_spelling_suggestion_for_strings("ƛ", ["Ƛ"]), None);
        assert_eq!(get_spelling_suggestion_for_strings("abcƛ", ["abcꟜ"]), None);
        assert_eq!(distance("abcƛ", "abcꟜ", 2.0), Some(2.0));
    }

    #[test]
    fn rust_unicode_version_matches_the_audited_case_mapping_surface() {
        assert_eq!(
            char::UNICODE_VERSION,
            (17, 0, 0),
            "re-audit post-Unicode-15 case-mapping exclusions for the new Rust Unicode tables"
        );
    }

    #[test]
    fn unicode_edit_distance_uses_scalar_values_after_the_byte_length_gate() {
        assert_eq!(distance("CAFÉ", "café", 0.4), Some(0.4));
        assert_eq!(distance("İabc", "iabc", 0.1), Some(0.1));
        assert_eq!(
            get_spelling_suggestion_for_strings("CAFÉ", ["café"]),
            Some("café")
        );
        assert_eq!(
            get_spelling_suggestion_for_strings("İabc", ["iabc"]),
            Some("iabc")
        );
        // Pinned Go compares the candidate's UTF-8 byte length with the
        // requested name's rune length before computing edit distance.
        assert_eq!(get_spelling_suggestion_for_strings("😀a", ["😀A"]), None);
    }

    #[test]
    fn length_and_distance_threshold_edges_are_inclusive() {
        // Five requested runes admit distance 2.9: one substitution costs 2.
        assert_eq!(
            get_spelling_suggestion_for_strings("abcde", ["abXde"]),
            Some("abXde")
        );
        // Two substitutions cost 4 and exceed the same threshold.
        assert_eq!(
            get_spelling_suggestion_for_strings("abcde", ["aXYde"]),
            None
        );
        // Three-rune names admit insertion/deletion cost 1 but not substitution 2.
        assert_eq!(
            get_spelling_suggestion_for_strings("abc", ["abbc"]),
            Some("abbc")
        );
        assert_eq!(get_spelling_suggestion_for_strings("abc", ["axc"]), None);

        // Eight requested runes permit two extra candidate bytes, while three
        // would be close enough by distance alone but fail the length gate.
        assert_eq!(
            get_spelling_suggestion_for_strings("abcdefgh", ["abcdefghXY"]),
            Some("abcdefghXY")
        );
        assert_eq!(
            get_spelling_suggestion_for_strings("abcdefgh", ["abcdefghXYZ"]),
            None
        );
        // At nine runes, the 34% length threshold grows from two to three.
        assert_eq!(
            get_spelling_suggestion_for_strings("abcdefghi", ["abcdefghiXYZ"]),
            Some("abcdefghiXYZ")
        );
    }

    #[test]
    fn long_distant_candidates_hit_the_banded_cutoff() {
        let requested = "a".repeat(256);
        let candidate = "z".repeat(256);
        assert_eq!(
            get_spelling_suggestion_for_strings(&requested, [candidate.as_str()]),
            None
        );
        assert_eq!(distance(&requested, &candidate, 3.9), None);
    }
}
