//! Port of `scanner/regexp.go`: the regular expression body checker that
//! `Scanner.ReScanSlashToken` runs when it reports errors.
//!
//! PORT: Go strings are byte strings. The values that this checker returns
//! (`scanClassAtom`, `scanClassSetOperand`, ...) can hold WTF-8 lone-surrogate
//! sentinels from `stringutil.EncodeJSStringRune`, which a Rust `String`
//! cannot hold. These values are only compared (empty check, length and
//! `DecodeJSStringRune`), so they are `Vec<u8>` here, and the private
//! `encode_js_string_rune_bytes`, `decode_js_string_rune_bytes` and
//! `decode_rune_in_bytes` helpers do the Go byte math on them.
//!
//! Go `rune` values from `Scanner.char()` and `Scanner.charAt()` are `i32`
//! (a raw byte, or -1 at the end). `match rune(ch)` stands in for a Go
//! `switch ch` over ASCII cases.

use crate::prelude::*;
use crate::flags_macros::{go_enum, go_flags};

use super::scanner_p1::{
    rune_to_string, utf8_decode_rune_in_string, EscapeSequenceScanningFlags, Scanner, RUNE_ERROR,
};
use super::unicode_properties::*;

go_flags!(RegularExpressionFlags, i32 {
    NONE = 0; // regularExpressionFlagsNone
    HAS_INDICES = 1 << 0; // d
    GLOBAL = 1 << 1; // g
    IGNORE_CASE = 1 << 2; // i
    MULTILINE = 1 << 3; // m
    DOT_ALL = 1 << 4; // s
    UNICODE = 1 << 5; // u
    UNICODE_SETS = 1 << 6; // v
    STICKY = 1 << 7; // y
    ANY_UNICODE_MODE = (1 << 5) | (1 << 6); // regularExpressionFlagsUnicode | regularExpressionFlagsUnicodeSets
    MODIFIERS = (1 << 2) | (1 << 3) | (1 << 4); // regularExpressionFlagsIgnoreCase | regularExpressionFlagsMultiline | regularExpressionFlagsDotAll
});

// Go: scanner/regexp.go:33 charCodeToRegExpFlag
// PORT: Go map lookup `charCodeToRegExpFlag[ch]` -> `(flag, ok)` as `Option`.
pub fn char_code_to_reg_exp_flag(ch: i32) -> Option<RegularExpressionFlags> {
    match rune(ch) {
        Some('d') => Some(RegularExpressionFlags::HAS_INDICES),
        Some('g') => Some(RegularExpressionFlags::GLOBAL),
        Some('i') => Some(RegularExpressionFlags::IGNORE_CASE),
        Some('m') => Some(RegularExpressionFlags::MULTILINE),
        Some('s') => Some(RegularExpressionFlags::DOT_ALL),
        Some('u') => Some(RegularExpressionFlags::UNICODE),
        Some('v') => Some(RegularExpressionFlags::UNICODE_SETS),
        Some('y') => Some(RegularExpressionFlags::STICKY),
        _ => None,
    }
}

// Go: scanner/regexp.go:44 regExpFlagToFirstAvailableLanguageVersion
// PORT: Go map lookup as `Option`.
pub fn reg_exp_flag_to_first_available_language_version(flag: RegularExpressionFlags) -> Option<ScriptTarget> {
    match flag {
        RegularExpressionFlags::HAS_INDICES => Some(ScriptTarget::ES2022),
        RegularExpressionFlags::DOT_ALL => Some(ScriptTarget::ES2018),
        RegularExpressionFlags::UNICODE_SETS => Some(ScriptTarget::ES2024),
        _ => None,
    }
}

impl Scanner {
    // Go: scanner/regexp.go:50 checkRegularExpressionFlagAvailability
    pub fn check_regular_expression_flag_availability(&mut self, flag: RegularExpressionFlags, pos: i32, size: i32) {
        if let Some(available_from) = reg_exp_flag_to_first_available_language_version(flag) {
            if self.language_version() < available_from {
                self.error_at(
                    diag::This_regular_expression_flag_is_only_available_when_targeting_0_or_later,
                    pos,
                    size,
                    args![available_from.string().to_lowercase()],
                );
            }
        }
    }
}

go_enum!(ClassSetExpressionType, i32 {
    UNKNOWN = 0; // classSetExpressionTypeUnknown
    CLASS_UNION = 1; // classSetExpressionTypeClassUnion
    CLASS_INTERSECTION = 2; // classSetExpressionTypeClassIntersection
    CLASS_SUBTRACTION = 3; // classSetExpressionTypeClassSubtraction
});

// Go: scanner/regexp.go:65 groupNameReference
#[derive(Clone, Debug, Default)]
pub struct GroupNameReference {
    pub pos: i32,
    pub end: i32,
    pub name: String,
}

// Go: scanner/regexp.go:71 decimalEscapeValue
#[derive(Clone, Copy, Debug, Default)]
pub struct DecimalEscapeValue {
    pub pos: i32,
    pub end: i32,
    pub value: i32,
}

// Go: scanner/regexp.go:77 regExpParser
pub struct RegExpParser<'a> {
    pub scanner: &'a mut Scanner,
    pub end: i32,
    pub reg_exp_flags: RegularExpressionFlags,
    pub any_unicode_mode: bool,
    pub unicode_sets_mode: bool,
    pub annex_b: bool,

    pub any_unicode_mode_or_non_annex_b: bool,
    pub named_capture_groups: bool,

    // See scanClassSetExpression.
    pub may_contain_strings: bool,
    // The number of all (named and unnamed) capturing groups defined in the regex.
    pub number_of_capturing_groups: i32,
    // All named capturing groups defined in the regex.
    pub group_specifiers: FxHashMap<String, bool>,
    // All references to named capturing groups in the regex.
    pub group_name_references: Vec<GroupNameReference>,
    // All numeric backreferences within the regex.
    pub decimal_escapes: Vec<DecimalEscapeValue>,
    // A stack of scopes for named capturing groups. See scanGroupName.
    pub named_capturing_groups: Vec<FxHashMap<String, bool>>,

    // pendingLowSurrogate holds the low surrogate to emit on the next
    // scanSourceCharacter call when Corsa has to split a non-BMP rune into
    // UTF-16 surrogate code units in non-unicode mode. Strada did not need
    // this bookkeeping because its source text was already indexed as UTF-16.
    pub pending_low_surrogate: i32,
}

// PORT: Go builds `regExpParser` with a struct literal in
// `Scanner.ReScanSlashToken` (scanner.go:1210). This constructor takes the
// same fields and gives the other fields their Go zero values.
pub fn new_reg_exp_parser(
    scanner: &mut Scanner,
    end: i32,
    reg_exp_flags: RegularExpressionFlags,
    any_unicode_mode: bool,
    unicode_sets_mode: bool,
    annex_b: bool,
    named_capture_groups: bool,
) -> RegExpParser<'_> {
    RegExpParser {
        scanner,
        end,
        reg_exp_flags,
        any_unicode_mode,
        unicode_sets_mode,
        annex_b,
        any_unicode_mode_or_non_annex_b: false,
        named_capture_groups,
        may_contain_strings: false,
        number_of_capturing_groups: 0,
        group_specifiers: FxHashMap::default(),
        group_name_references: Vec::new(),
        decimal_escapes: Vec::new(),
        named_capturing_groups: Vec::new(),
        pending_low_surrogate: 0,
    }
}

impl<'a> RegExpParser<'a> {
    // Go: scanner/regexp.go:108 pos
    fn pos(&self) -> i32 {
        self.scanner.scanner_state.pos
    }

    // Go: scanner/regexp.go:112 setPos
    // PORT: Go never calls this method either.
    #[allow(dead_code)]
    fn set_pos(&mut self, v: i32) {
        self.scanner.scanner_state.pos = v;
    }

    // Go: scanner/regexp.go:116 incPos
    fn inc_pos(&mut self, n: i32) {
        self.scanner.scanner_state.pos += n;
    }

    // Go: scanner/regexp.go:120 char
    fn char(&self) -> i32 {
        self.scanner.char()
    }

    // Go: scanner/regexp.go:124 charAt
    fn char_at(&self, pos: i32) -> i32 {
        self.scanner.char_at(pos - self.pos())
    }

    // Go: scanner/regexp.go:128 error
    fn error(&mut self, msg: &'static ts_diagnostics::Message, pos: i32, length: i32, args: Vec<String>) {
        self.scanner.error_at(msg, pos, length, args);
    }

    // Go: scanner/regexp.go:132 text
    fn text(&self) -> &str {
        self.scanner.text()
    }

    /// Go `p.text()[start:end]` as Go string bytes.
    // PORT: helper for Go string slicing into a byte string value.
    fn text_bytes(&self, start: i32, end: i32) -> Vec<u8> {
        self.text().as_bytes()[start as usize..end as usize].to_vec()
    }

    /// Go `utf8.DecodeRuneInString(p.text()[p.pos():])`.
    // PORT: helper for the repeated Go expression.
    fn decode_rune_at_pos(&self) -> (i32, i32) {
        utf8_decode_rune_in_string(self.text(), self.pos() as usize)
    }
}

// Go: scanner/regexp.go:136 compareDecimalStrings
pub fn compare_decimal_strings(a: &str, b: &str) -> i32 {
    let mut a = a.trim_start_matches('0');
    let mut b = b.trim_start_matches('0');
    if a.is_empty() {
        a = "0";
    }
    if b.is_empty() {
        b = "0";
    }
    if a.len() != b.len() {
        if a.len() < b.len() {
            return -1;
        }
        return 1;
    }
    match a.cmp(b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

impl<'a> RegExpParser<'a> {
    // Go: scanner/regexp.go:155 scanDisjunction
    // Disjunction ::= Alternative ('|' Alternative)*
    fn scan_disjunction(&mut self, is_in_group: bool) {
        loop {
            self.named_capturing_groups.push(FxHashMap::default());
            self.scan_alternative(is_in_group);
            self.named_capturing_groups.pop();
            if self.char() != '|' as i32 {
                return;
            }
            self.inc_pos(1);
        }
    }

    // Go: scanner/regexp.go:205 scanAlternative
    // Alternative ::= Term*
    // Term ::=
    //
    //	| Assertion
    //	| Atom Quantifier?
    //
    // Assertion ::=
    //
    //	| '^'
    //	| '$'
    //	| '\b'
    //	| '\B'
    //	| '(?=' Disjunction ')'
    //	| '(?!' Disjunction ')'
    //	| '(?<=' Disjunction ')'
    //	| '(?<!' Disjunction ')'
    //
    // Quantifier ::= QuantifierPrefix '?'?
    // QuantifierPrefix ::=
    //
    //	| '*'
    //	| '+'
    //	| '?'
    //	| '{' DecimalDigits (',' DecimalDigits?)? '}'
    //
    // Atom ::=
    //
    //	| PatternCharacter
    //	| '.'
    //	| '\' AtomEscape
    //	| CharacterClass
    //	| '(?<' RegExpIdentifierName '>' Disjunction ')'
    //	| '(?' RegularExpressionFlags ('-' RegularExpressionFlags)? ':' Disjunction ')'
    //
    // CharacterClass ::= unicodeMode
    //
    //	? '[' ClassRanges ']'
    //	: '[' ClassSetExpression ']'
    fn scan_alternative(&mut self, is_in_group: bool) {
        let mut is_previous_term_quantifiable = false;
        while self.pos() < self.end {
            let start = self.pos();
            let ch = self.char();
            match rune(ch) {
                Some('^' | '$') => {
                    self.inc_pos(1);
                    is_previous_term_quantifiable = false;
                }
                Some('\\') => {
                    self.inc_pos(1);
                    match rune(self.char()) {
                        Some('b' | 'B') => {
                            self.inc_pos(1);
                            is_previous_term_quantifiable = false;
                        }
                        _ => {
                            self.scan_atom_escape();
                            is_previous_term_quantifiable = true;
                        }
                    }
                }
                Some('(') => {
                    self.inc_pos(1);
                    if self.char() == '?' as i32 {
                        self.inc_pos(1);
                        match rune(self.char()) {
                            Some('=' | '!') => {
                                self.inc_pos(1);
                                // In Annex B, `(?=Disjunction)` and `(?!Disjunction)` are quantifiable
                                is_previous_term_quantifiable = !self.any_unicode_mode_or_non_annex_b;
                            }
                            Some('<') => {
                                let group_name_start = self.pos();
                                self.inc_pos(1);
                                match rune(self.char()) {
                                    Some('=' | '!') => {
                                        self.inc_pos(1);
                                        is_previous_term_quantifiable = false;
                                    }
                                    _ => {
                                        self.scan_group_name(false /*isReference*/);
                                        self.scan_expected_char('>' as i32);
                                        if self.scanner.language_version() < ScriptTarget::ES2018 {
                                            let len = self.pos() - group_name_start;
                                            self.error(
                                                diag::Named_capturing_groups_are_only_available_when_targeting_ES2018_or_later,
                                                group_name_start,
                                                len,
                                                vec![],
                                            );
                                        }
                                        self.number_of_capturing_groups += 1;
                                        is_previous_term_quantifiable = true;
                                    }
                                }
                            }
                            _ => {
                                let flags_start = self.pos();
                                let set_flags = self.scan_pattern_modifiers(RegularExpressionFlags::NONE);
                                if self.char() == '-' as i32 {
                                    self.inc_pos(1);
                                    self.scan_pattern_modifiers(set_flags);
                                    if self.pos() == flags_start + 1 {
                                        let len = self.pos() - flags_start;
                                        self.error(
                                            diag::Subpattern_flags_must_be_present_when_there_is_a_minus_sign,
                                            flags_start,
                                            len,
                                            vec![],
                                        );
                                    }
                                }
                                self.scan_expected_char(':' as i32);
                                is_previous_term_quantifiable = true;
                            }
                        }
                    } else {
                        self.number_of_capturing_groups += 1;
                        is_previous_term_quantifiable = true;
                    }
                    self.scan_disjunction(true /*isInGroup*/);
                    self.scan_expected_char(')' as i32);
                }
                Some('{' | '*' | '+' | '?') => {
                    // PORT: Go `case '{'` ends with `fallthrough` into
                    // `case '*', '+', '?'`. The `{` part runs first here, and
                    // each Go `continue` is a `continue` of the outer loop.
                    if ch == '{' as i32 {
                        self.inc_pos(1);
                        let digits_start = self.pos();
                        self.scan_digits();
                        let min_str = self.scanner.token_value().to_string();
                        if !self.any_unicode_mode_or_non_annex_b && min_str.is_empty() {
                            is_previous_term_quantifiable = true;
                            continue;
                        }
                        if self.char() == ',' as i32 {
                            self.inc_pos(1);
                            self.scan_digits();
                            let max_str = self.scanner.token_value().to_string();
                            if min_str.is_empty() {
                                if !max_str.is_empty() || self.char() == '}' as i32 {
                                    self.error(diag::Incomplete_quantifier_Digit_expected, digits_start, 0, vec![]);
                                } else {
                                    self.error(
                                        diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                                        start,
                                        1,
                                        args![rune_to_string(ch)],
                                    );
                                    is_previous_term_quantifiable = true;
                                    continue;
                                }
                            } else if !max_str.is_empty() {
                                if compare_decimal_strings(&min_str, &max_str) > 0
                                    && (self.any_unicode_mode_or_non_annex_b || self.char() == '}' as i32)
                                {
                                    let len = self.pos() - digits_start;
                                    self.error(diag::Numbers_out_of_order_in_quantifier, digits_start, len, vec![]);
                                }
                            }
                        } else if min_str.is_empty() {
                            if self.any_unicode_mode_or_non_annex_b {
                                self.error(
                                    diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                                    start,
                                    1,
                                    args![rune_to_string(ch)],
                                );
                            }
                            is_previous_term_quantifiable = true;
                            continue;
                        }
                        if self.char() != '}' as i32 {
                            if self.any_unicode_mode_or_non_annex_b {
                                let pos = self.pos();
                                self.error(diag::X_0_expected, pos, 0, args!["}"]);
                                self.inc_pos(-1);
                            } else {
                                is_previous_term_quantifiable = true;
                                continue;
                            }
                        }
                    }
                    self.inc_pos(1);
                    if self.char() == '?' as i32 {
                        // Non-greedy
                        self.inc_pos(1);
                    }
                    if !is_previous_term_quantifiable {
                        let len = self.pos() - start;
                        self.error(diag::There_is_nothing_available_for_repetition, start, len, vec![]);
                    }
                    is_previous_term_quantifiable = false;
                }
                Some('.') => {
                    self.inc_pos(1);
                    is_previous_term_quantifiable = true;
                }
                Some('[') => {
                    self.inc_pos(1);
                    if self.unicode_sets_mode {
                        self.scan_class_set_expression();
                    } else {
                        self.scan_class_ranges();
                        self.pending_low_surrogate = 0;
                    }
                    self.scan_expected_char(']' as i32);
                    is_previous_term_quantifiable = true;
                }
                Some(')' | ']' | '}') => {
                    // PORT: Go `case ')'` returns when in a group and
                    // otherwise falls through into `case ']', '}'`.
                    if ch == ')' as i32 && is_in_group {
                        return;
                    }
                    if self.any_unicode_mode_or_non_annex_b || ch == ')' as i32 {
                        let pos = self.pos();
                        self.error(
                            diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            pos,
                            1,
                            args![rune_to_string(ch)],
                        );
                    }
                    self.inc_pos(1);
                    is_previous_term_quantifiable = true;
                }
                Some('/' | '|') => {
                    return;
                }
                _ => {
                    self.scan_source_character();
                    is_previous_term_quantifiable = true;
                }
            }
        }
    }

    // Go: scanner/regexp.go:354 scanPatternModifiers
    fn scan_pattern_modifiers(&mut self, mut curr_flags: RegularExpressionFlags) -> RegularExpressionFlags {
        while self.pos() < self.end {
            let (ch, size) = self.decode_rune_at_pos();
            if ch == RUNE_ERROR || !rune(ch).is_some_and(is_identifier_part) {
                break;
            }
            let pos = self.pos();
            match char_code_to_reg_exp_flag(ch) {
                None => {
                    self.error(diag::Unknown_regular_expression_flag, pos, size, vec![]);
                }
                Some(flag) if curr_flags.intersects(flag) => {
                    self.error(diag::Duplicate_regular_expression_flag, pos, size, vec![]);
                }
                Some(flag) if !flag.intersects(RegularExpressionFlags::MODIFIERS) => {
                    self.error(
                        diag::This_regular_expression_flag_cannot_be_toggled_within_a_subpattern,
                        pos,
                        size,
                        vec![],
                    );
                }
                Some(flag) => {
                    curr_flags |= flag;
                    self.scanner.check_regular_expression_flag_availability(flag, pos, size);
                }
            }
            self.inc_pos(size);
        }
        curr_flags
    }

    // Go: scanner/regexp.go:382 scanAtomEscape
    // AtomEscape ::=
    //
    //	| DecimalEscape
    //	| CharacterClassEscape
    //	| CharacterEscape
    //	| 'k<' RegExpIdentifierName '>'
    fn scan_atom_escape(&mut self) {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'\\');
        let ch = self.char();
        if ch == 'k' as i32 {
            self.inc_pos(1);
            if self.char() == '<' as i32 {
                self.inc_pos(1);
                self.scan_group_name(true /*isReference*/);
                self.scan_expected_char('>' as i32);
            } else if self.any_unicode_mode_or_non_annex_b || self.named_capture_groups {
                let pos = self.pos() - 2;
                self.error(
                    diag::X_k_must_be_followed_by_a_capturing_group_name_enclosed_in_angle_brackets,
                    pos,
                    2,
                    vec![],
                );
            }
            return;
        }
        // PORT: Go `case 'q'` falls through into `default` when not in
        // Unicode Sets mode.
        if ch == 'q' as i32 && self.unicode_sets_mode {
            self.inc_pos(1);
            let pos = self.pos() - 2;
            self.error(diag::X_q_is_only_available_inside_character_class, pos, 2, vec![]);
            return;
        }
        if !self.scan_character_class_escape() && !self.scan_decimal_escape() {
            // Regex literals cannot contain line breaks here, so a character escape must consume something.
            // PORT: Go calls this inside `debug.Assert`, which always runs
            // the call. The call stays outside `debug_assert!`.
            let escape = self.scan_character_escape(true /*atomEscape*/);
            debug_assert!(!escape.is_empty());
        }
    }

    // Go: scanner/regexp.go:410 scanDecimalEscape
    // DecimalEscape ::= [1-9] [0-9]*
    fn scan_decimal_escape(&mut self) -> bool {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'\\');
        let ch = self.char();
        if ch >= '1' as i32 && ch <= '9' as i32 {
            let start = self.pos();
            self.scan_digits();
            // PORT: Go `strconv.Atoi` fails only on overflow here and then
            // uses `math.MaxInt`. Go `int` is `i32` in this crate, so the
            // overflow limit is `i32::MAX`. The only use is `value >
            // numberOfCapturingGroups`, which gives the same result.
            let val = self.scanner.token_value().parse::<i32>().unwrap_or(i32::MAX);
            let end = self.pos();
            self.decimal_escapes.push(DecimalEscapeValue { pos: start, end, value: val });
            return true;
        }
        false
    }

    // Go: scanner/regexp.go:436 scanCharacterEscape
    // CharacterEscape ::=
    //
    //	| `c` ControlLetter
    //	| IdentityEscape
    //	| (Other sequences handled by `scanEscapeSequence`)
    //
    // IdentityEscape ::=
    //
    //	| '^' | '$' | '/' | '\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|'
    //	| [~AnyUnicodeMode] (any other non-identifier characters)
    fn scan_character_escape(&mut self, atom_escape: bool) -> Vec<u8> {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'\\');
        let mut ch = self.char();
        if ch == -1 {
            let pos = self.pos() - 1;
            self.error(diag::Undetermined_character_escape, pos, 1, vec![]);
            return b"\\".to_vec();
        }
        match rune(ch) {
            Some('c') => {
                self.inc_pos(1);
                ch = self.char();
                if rune(ch).is_some_and(is_ascii_letter) {
                    self.inc_pos(1);
                    return rune_to_bytes(ch & 0x1f);
                }
                if self.any_unicode_mode_or_non_annex_b {
                    let pos = self.pos() - 2;
                    self.error(diag::X_c_must_be_followed_by_an_ASCII_letter, pos, 2, vec![]);
                } else if atom_escape {
                    self.inc_pos(-1);
                    return b"\\".to_vec();
                }
                rune_to_bytes(ch)
            }
            Some('^' | '$' | '/' | '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|') => {
                self.inc_pos(1);
                rune_to_bytes(ch)
            }
            _ => {
                self.inc_pos(-1); // back up to include the backslash for scanEscapeSequence
                let mut flags = EscapeSequenceScanningFlags::REGULAR_EXPRESSION;
                if self.annex_b {
                    flags |= EscapeSequenceScanningFlags::ANNEX_B;
                }
                if self.any_unicode_mode {
                    flags |= EscapeSequenceScanningFlags::ANY_UNICODE_MODE;
                }
                if atom_escape {
                    flags |= EscapeSequenceScanningFlags::ATOM_ESCAPE;
                }
                // PORT: the Go string result becomes bytes. See the file note.
                self.scanner.scan_escape_sequence(flags).into_bytes()
            }
        }
    }

    // Go: scanner/regexp.go:476 scanGroupName
    fn scan_group_name(&mut self, is_reference: bool) {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'<');
        self.scanner.scanner_state.token_start = self.pos();
        self.scanner.scan_identifier(0);
        let token_start = self.scanner.scanner_state.token_start;
        if self.pos() == token_start {
            let pos = self.pos();
            self.error(diag::Expected_a_capturing_group_name, pos, 0, vec![]);
        } else if is_reference {
            let end = self.pos();
            let name = self.scanner.token_value().to_string();
            self.group_name_references.push(GroupNameReference { pos: token_start, end, name });
        } else if self.named_capturing_groups_contains(self.scanner.token_value()) {
            let len = self.pos() - token_start;
            self.error(
                diag::Named_capturing_groups_with_the_same_name_must_be_mutually_exclusive_to_each_other,
                token_start,
                len,
                vec![],
            );
        } else {
            let name = self.scanner.token_value().to_string();
            if let Some(last) = self.named_capturing_groups.last_mut() {
                last.insert(name.clone(), true);
            }
            self.group_specifiers.insert(name, true);
        }
    }

    // Go: scanner/regexp.go:494 namedCapturingGroupsContains
    fn named_capturing_groups_contains(&self, name: &str) -> bool {
        for group in &self.named_capturing_groups {
            if group.get(name).copied().unwrap_or(false) {
                return true;
            }
        }
        false
    }

    // Go: scanner/regexp.go:503 isClassContentExit
    fn is_class_content_exit(&self, ch: i32) -> bool {
        ch == ']' as i32 || self.pos() >= self.end
    }

    // Go: scanner/regexp.go:508 scanClassRanges
    // ClassRanges ::= '^'? (ClassAtom ('-' ClassAtom)?)*
    fn scan_class_ranges(&mut self) {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'[');
        self.pending_low_surrogate = 0;
        if self.char() == '^' as i32 {
            self.inc_pos(1);
        }
        while self.pos() < self.end {
            let mut ch = self.char();
            if self.is_class_content_exit(ch) {
                return;
            }
            let min_start = self.pos();
            let min_character = self.scan_class_atom();
            if self.char() == '-' as i32 {
                self.inc_pos(1);
                ch = self.char();
                if self.is_class_content_exit(ch) {
                    return;
                }
                if min_character.is_empty() && self.any_unicode_mode_or_non_annex_b {
                    let len = self.pos() - 1 - min_start;
                    self.error(
                        diag::A_character_class_range_must_not_be_bounded_by_another_character_class,
                        min_start,
                        len,
                        vec![],
                    );
                }
                let max_start = self.pos();
                let max_character = self.scan_class_atom();
                if max_character.is_empty() && self.any_unicode_mode_or_non_annex_b {
                    let len = self.pos() - max_start;
                    self.error(
                        diag::A_character_class_range_must_not_be_bounded_by_another_character_class,
                        max_start,
                        len,
                        vec![],
                    );
                    continue;
                }
                if min_character.is_empty() {
                    continue;
                }
                let (min_character_value, min_size) = decode_js_string_rune_bytes(&min_character);
                let (max_character_value, max_size) = decode_js_string_rune_bytes(&max_character);
                if min_character.len() == min_size
                    && max_character.len() == max_size
                    && min_character_value > max_character_value
                {
                    let len = self.pos() - min_start;
                    self.error(diag::Range_out_of_order_in_character_class, min_start, len, vec![]);
                }
            }
        }
    }

    // Go: scanner/regexp.go:563 scanClassSetExpression
    // Static Semantics: MayContainStrings
    //     ClassUnion: ClassSetOperands.some(ClassSetOperand => ClassSetOperand.MayContainStrings)
    //     ClassIntersection: ClassSetOperands.every(ClassSetOperand => ClassSetOperand.MayContainStrings)
    //     ClassSubtraction: ClassSetOperands[0].MayContainStrings
    //     ClassSetOperand:
    //         || ClassStringDisjunctionContents.MayContainStrings
    //         || CharacterClassEscape.UnicodePropertyValueExpression.LoneUnicodePropertyNameOrValue.MayContainStrings
    //     ClassStringDisjunctionContents: ClassStrings.some(ClassString => ClassString.ClassSetCharacters.length !== 1)
    //     LoneUnicodePropertyNameOrValue: isBinaryUnicodePropertyOfStrings(LoneUnicodePropertyNameOrValue)
    //
    // ClassSetExpression ::= '^'? (ClassUnion | ClassIntersection | ClassSubtraction)
    // ClassUnion ::= (ClassSetRange | ClassSetOperand)*
    // ClassIntersection ::= ClassSetOperand ('&&' ClassSetOperand)+
    // ClassSubtraction ::= ClassSetOperand ('--' ClassSetOperand)+
    // ClassSetRange ::= ClassSetCharacter '-' ClassSetCharacter
    fn scan_class_set_expression(&mut self) {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'[');
        let mut is_character_complement = false;
        if self.char() == '^' as i32 {
            self.inc_pos(1);
            is_character_complement = true;
        }
        let mut expression_may_contain_strings = false;
        let mut ch = self.char();
        if self.is_class_content_exit(ch) {
            return;
        }
        let mut start = self.pos();
        let mut operand: Vec<u8> = Vec::new();
        let mut two_chars: Vec<u8> = Vec::new();
        if self.pos() + 1 < self.end {
            two_chars = self.text_bytes(self.pos(), self.pos() + 2);
        }
        match two_chars.as_slice() {
            b"--" | b"&&" => {
                let pos = self.pos();
                self.error(diag::Expected_a_class_set_operand, pos, 0, vec![]);
                self.may_contain_strings = false;
            }
            _ => {
                operand = self.scan_class_set_operand();
            }
        }
        match rune(self.char()) {
            Some('-') => {
                if self.pos() + 1 < self.end && self.char_at(self.pos() + 1) == '-' as i32 {
                    if is_character_complement && self.may_contain_strings {
                        let len = self.pos() - start;
                        self.error(
                            diag::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class,
                            start,
                            len,
                            vec![],
                        );
                    }
                    expression_may_contain_strings = self.may_contain_strings;
                    self.scan_class_set_sub_expression(ClassSetExpressionType::CLASS_SUBTRACTION);
                    self.may_contain_strings = !is_character_complement && expression_may_contain_strings;
                    return;
                }
            }
            Some('&') => {
                if self.pos() + 1 < self.end && self.char_at(self.pos() + 1) == '&' as i32 {
                    self.scan_class_set_sub_expression(ClassSetExpressionType::CLASS_INTERSECTION);
                    if is_character_complement && self.may_contain_strings {
                        let len = self.pos() - start;
                        self.error(
                            diag::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class,
                            start,
                            len,
                            vec![],
                        );
                    }
                    expression_may_contain_strings = self.may_contain_strings;
                    self.may_contain_strings = !is_character_complement && expression_may_contain_strings;
                    return;
                } else {
                    // PORT: Go reports `string(ch)`, where `ch` is the
                    // character read before the first operand.
                    let pos = self.pos();
                    self.error(
                        diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                        pos,
                        1,
                        args![rune_to_string(ch)],
                    );
                }
            }
            _ => {
                if is_character_complement && self.may_contain_strings {
                    let len = self.pos() - start;
                    self.error(
                        diag::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class,
                        start,
                        len,
                        vec![],
                    );
                }
                expression_may_contain_strings = self.may_contain_strings;
            }
        }
        while self.pos() < self.end {
            ch = self.char();
            match rune(ch) {
                Some('-') => {
                    self.inc_pos(1);
                    ch = self.char();
                    if self.is_class_content_exit(ch) {
                        self.may_contain_strings = !is_character_complement && expression_may_contain_strings;
                        return;
                    }
                    if ch == '-' as i32 {
                        self.inc_pos(1);
                        let pos = self.pos() - 2;
                        self.error(
                            diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                            pos,
                            2,
                            vec![],
                        );
                        start = self.pos() - 2;
                        operand = self.text_bytes(start, self.pos());
                        continue;
                    } else {
                        if operand.is_empty() {
                            let len = self.pos() - 1 - start;
                            self.error(
                                diag::A_character_class_range_must_not_be_bounded_by_another_character_class,
                                start,
                                len,
                                vec![],
                            );
                        }
                        let second_start = self.pos();
                        let second_operand = self.scan_class_set_operand();
                        if is_character_complement && self.may_contain_strings {
                            let len = self.pos() - second_start;
                            self.error(
                                diag::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class,
                                second_start,
                                len,
                                vec![],
                            );
                        }
                        expression_may_contain_strings = expression_may_contain_strings || self.may_contain_strings;
                        if second_operand.is_empty() {
                            let len = self.pos() - second_start;
                            self.error(
                                diag::A_character_class_range_must_not_be_bounded_by_another_character_class,
                                second_start,
                                len,
                                vec![],
                            );
                        } else if !operand.is_empty() {
                            let (min_character_value, min_size) = decode_js_string_rune_bytes(&operand);
                            let (max_character_value, max_size) = decode_js_string_rune_bytes(&second_operand);
                            if operand.len() == min_size
                                && second_operand.len() == max_size
                                && min_character_value > max_character_value
                            {
                                let len = self.pos() - start;
                                self.error(diag::Range_out_of_order_in_character_class, start, len, vec![]);
                            }
                        }
                    }
                }
                Some('&') => {
                    start = self.pos();
                    self.inc_pos(1);
                    if self.char() == '&' as i32 {
                        self.inc_pos(1);
                        let pos = self.pos() - 2;
                        self.error(
                            diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                            pos,
                            2,
                            vec![],
                        );
                        if self.char() == '&' as i32 {
                            let pos = self.pos();
                            self.error(
                                diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                                pos,
                                1,
                                args![rune_to_string(ch)],
                            );
                            self.inc_pos(1);
                        }
                    } else {
                        let pos = self.pos() - 1;
                        self.error(
                            diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            pos,
                            1,
                            args![rune_to_string(ch)],
                        );
                    }
                    operand = self.text_bytes(start, self.pos());
                    continue;
                }
                _ => {}
            }
            if self.is_class_content_exit(self.char()) {
                break;
            }
            start = self.pos();
            two_chars = Vec::new();
            if self.pos() + 1 < self.end {
                two_chars = self.text_bytes(self.pos(), self.pos() + 2);
            }
            match two_chars.as_slice() {
                b"--" | b"&&" => {
                    let pos = self.pos();
                    self.error(
                        diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                        pos,
                        2,
                        vec![],
                    );
                    self.inc_pos(2);
                    operand = self.text_bytes(start, self.pos());
                }
                _ => {
                    operand = self.scan_class_set_operand();
                }
            }
        }
        self.may_contain_strings = !is_character_complement && expression_may_contain_strings;
    }

    // Go: scanner/regexp.go:689 scanClassSetSubExpression
    fn scan_class_set_sub_expression(&mut self, expression_type: ClassSetExpressionType) {
        let mut expression_may_contain_strings = self.may_contain_strings;
        while self.pos() < self.end {
            let mut ch = self.char();
            if self.is_class_content_exit(ch) {
                break;
            }
            match rune(ch) {
                Some('-') => {
                    self.inc_pos(1);
                    if self.char() == '-' as i32 {
                        self.inc_pos(1);
                        if expression_type != ClassSetExpressionType::CLASS_SUBTRACTION {
                            let pos = self.pos() - 2;
                            self.error(
                                diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                                pos,
                                2,
                                vec![],
                            );
                        }
                    } else {
                        let pos = self.pos() - 1;
                        self.error(
                            diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                            pos,
                            1,
                            vec![],
                        );
                    }
                }
                Some('&') => {
                    self.inc_pos(1);
                    if self.char() == '&' as i32 {
                        self.inc_pos(1);
                        if expression_type != ClassSetExpressionType::CLASS_INTERSECTION {
                            let pos = self.pos() - 2;
                            self.error(
                                diag::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead,
                                pos,
                                2,
                                vec![],
                            );
                        }
                        if self.char() == '&' as i32 {
                            let pos = self.pos();
                            self.error(
                                diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                                pos,
                                1,
                                args![rune_to_string(ch)],
                            );
                            self.inc_pos(1);
                        }
                    } else {
                        let pos = self.pos() - 1;
                        self.error(
                            diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            pos,
                            1,
                            args![rune_to_string(ch)],
                        );
                    }
                }
                _ => match expression_type {
                    ClassSetExpressionType::CLASS_SUBTRACTION => {
                        let pos = self.pos();
                        self.error(diag::X_0_expected, pos, 0, args!["--"]);
                    }
                    ClassSetExpressionType::CLASS_INTERSECTION => {
                        let pos = self.pos();
                        self.error(diag::X_0_expected, pos, 0, args!["&&"]);
                    }
                    _ => {}
                },
            }
            ch = self.char();
            if self.is_class_content_exit(ch) {
                let pos = self.pos();
                self.error(diag::Expected_a_class_set_operand, pos, 0, vec![]);
                break;
            }
            self.scan_class_set_operand();
            if expression_type == ClassSetExpressionType::CLASS_INTERSECTION {
                expression_may_contain_strings = expression_may_contain_strings && self.may_contain_strings;
            }
        }
        self.may_contain_strings = expression_may_contain_strings;
    }

    // Go: scanner/regexp.go:748 scanClassSetOperand
    // ClassSetOperand ::=
    //
    //	| '[' ClassSetExpression ']'
    //	| '\' CharacterClassEscape
    //	| '\q{' ClassStringDisjunctionContents '}'
    //	| ClassSetCharacter
    fn scan_class_set_operand(&mut self) -> Vec<u8> {
        self.may_contain_strings = false;
        match rune(self.char()) {
            Some('[') => {
                self.inc_pos(1);
                self.scan_class_set_expression();
                self.scan_expected_char(']' as i32);
                Vec::new()
            }
            Some('\\') => {
                self.inc_pos(1);
                if self.scan_character_class_escape() {
                    return Vec::new();
                } else if self.char() == 'q' as i32 {
                    self.inc_pos(1);
                    if self.char() == '{' as i32 {
                        self.inc_pos(1);
                        self.scan_class_string_disjunction_contents();
                        self.scan_expected_char('}' as i32);
                        return Vec::new();
                    } else {
                        let pos = self.pos() - 2;
                        self.error(
                            diag::X_q_must_be_followed_by_string_alternatives_enclosed_in_braces,
                            pos,
                            2,
                            vec![],
                        );
                        return b"q".to_vec();
                    }
                }
                self.inc_pos(-1);
                // PORT: Go `fallthrough` into `default`.
                self.scan_class_set_character()
            }
            _ => self.scan_class_set_character(),
        }
    }

    // Go: scanner/regexp.go:780 scanClassStringDisjunctionContents
    // ClassStringDisjunctionContents ::= ClassSetCharacter* ('|' ClassSetCharacter*)*
    fn scan_class_string_disjunction_contents(&mut self) {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'{');
        let mut character_count = 0;
        while self.pos() < self.end {
            let ch = self.char();
            match rune(ch) {
                Some('}') => {
                    if character_count != 1 {
                        self.may_contain_strings = true;
                    }
                    return;
                }
                Some('|') => {
                    if character_count != 1 {
                        self.may_contain_strings = true;
                    }
                    self.inc_pos(1);
                    character_count = 0;
                }
                _ => {
                    self.scan_class_set_character();
                    character_count += 1;
                }
            }
        }
    }

    // Go: scanner/regexp.go:808 scanClassSetCharacter
    // ClassSetCharacter ::=
    //
    //	| SourceCharacter -- ClassSetSyntaxCharacter -- ClassSetReservedDoublePunctuator
    //	| '\' (CharacterEscape | ClassSetReservedPunctuator | 'b')
    fn scan_class_set_character(&mut self) -> Vec<u8> {
        let ch = self.char();
        if ch == '\\' as i32 {
            self.inc_pos(1);
            let inner_ch = self.char();
            match rune(inner_ch) {
                Some('b') => {
                    self.inc_pos(1);
                    return b"\x08".to_vec();
                }
                Some('&' | '-' | '!' | '#' | '%' | ',' | ':' | ';' | '<' | '=' | '>' | '@' | '`' | '~') => {
                    self.inc_pos(1);
                    return rune_to_bytes(inner_ch);
                }
                _ => {
                    return self.scan_character_escape(false /*atomEscape*/);
                }
            }
        } else if self.pos() + 1 < self.end && ch == self.char_at(self.pos() + 1) {
            match rune(ch) {
                Some(
                    '&' | '!' | '#' | '%' | '*' | '+' | ',' | '.' | ':' | ';' | '<' | '=' | '>' | '?' | '@' | '`'
                    | '~',
                ) => {
                    let pos = self.pos();
                    self.error(
                        diag::A_character_class_must_not_contain_a_reserved_double_punctuator_Did_you_mean_to_escape_it_with_backslash,
                        pos,
                        2,
                        vec![],
                    );
                    self.inc_pos(2);
                    return self.text_bytes(self.pos() - 2, self.pos());
                }
                _ => {}
            }
        }
        match rune(ch) {
            Some('/' | '(' | ')' | '[' | ']' | '{' | '}' | '-' | '|') => {
                let pos = self.pos();
                self.error(
                    diag::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                    pos,
                    1,
                    args![rune_to_string(ch)],
                );
                self.inc_pos(1);
                return rune_to_bytes(ch);
            }
            _ => {}
        }
        self.scan_source_character()
    }

    // Go: scanner/regexp.go:851 scanClassAtom
    // ClassAtom ::=
    //
    //	| SourceCharacter but not one of '\' or ']'
    //	| '\' ClassEscape
    //
    // ClassEscape ::=
    //
    //	| 'b'
    //	| '-'
    //	| CharacterClassEscape
    //	| CharacterEscape
    fn scan_class_atom(&mut self) -> Vec<u8> {
        if self.char() == '\\' as i32 {
            self.inc_pos(1);
            let ch = self.char();
            match rune(ch) {
                Some('b') => {
                    self.inc_pos(1);
                    b"\x08".to_vec()
                }
                Some('-') => {
                    self.inc_pos(1);
                    rune_to_bytes(ch)
                }
                _ => {
                    if self.scan_character_class_escape() {
                        return Vec::new();
                    }
                    self.scan_character_escape(false /*atomEscape*/)
                }
            }
        } else {
            self.scan_source_character()
        }
    }

    // Go: scanner/regexp.go:877 scanCharacterClassEscape
    // CharacterClassEscape ::=
    //
    //	| 'd' | 'D' | 's' | 'S' | 'w' | 'W'
    //	| [+AnyUnicodeMode] ('P' | 'p') '{' UnicodePropertyValueExpression '}'
    fn scan_character_class_escape(&mut self) -> bool {
        debug_assert!(self.pos() > 0 && self.text().as_bytes()[self.pos() as usize - 1] == b'\\');
        let mut is_character_complement = false;
        let start = self.pos() - 1;
        let ch = self.char();
        match rune(ch) {
            Some('d' | 'D' | 's' | 'S' | 'w' | 'W') => {
                self.inc_pos(1);
                true
            }
            Some('P' | 'p') => {
                // PORT: Go `case 'P'` sets the flag and falls through into `case 'p'`.
                if ch == 'P' as i32 {
                    is_character_complement = true;
                }
                self.inc_pos(1);
                if self.char() == '{' as i32 {
                    self.inc_pos(1);
                    let property_name_or_value_start = self.pos();
                    let property_name_or_value = self.scan_word_characters();
                    if self.char() == '=' as i32 {
                        let property_name = non_binary_unicode_property(&property_name_or_value);
                        if self.pos() == property_name_or_value_start {
                            let pos = self.pos();
                            self.error(diag::Expected_a_Unicode_property_name, pos, 0, vec![]);
                        } else if property_name.is_empty() {
                            let len = self.pos() - property_name_or_value_start;
                            self.error(diag::Unknown_Unicode_property_name, property_name_or_value_start, len, vec![]);
                            let suggestion = self.get_spelling_suggestion_for_unicode_property_name(&property_name_or_value);
                            if !suggestion.is_empty() {
                                self.error(diag::Did_you_mean_0, property_name_or_value_start, len, args![suggestion]);
                            }
                        }
                        self.inc_pos(1);
                        let property_value_start = self.pos();
                        let property_value = self.scan_word_characters();
                        if self.pos() == property_value_start {
                            let pos = self.pos();
                            self.error(diag::Expected_a_Unicode_property_value, pos, 0, vec![]);
                        } else if !property_name.is_empty() {
                            let values = values_of_non_binary_unicode_properties(property_name);
                            if let Some(values) = values {
                                if !values.contains(&property_value.as_str()) {
                                    let len = self.pos() - property_value_start;
                                    self.error(diag::Unknown_Unicode_property_value, property_value_start, len, vec![]);
                                    let suggestion =
                                        self.get_spelling_suggestion_for_unicode_property_value(property_name, &property_value);
                                    if !suggestion.is_empty() {
                                        self.error(diag::Did_you_mean_0, property_value_start, len, args![suggestion]);
                                    }
                                }
                            }
                        }
                    } else {
                        let len = self.pos() - property_name_or_value_start;
                        if self.pos() == property_name_or_value_start {
                            let pos = self.pos();
                            self.error(diag::Expected_a_Unicode_property_name_or_value, pos, 0, vec![]);
                        } else if BINARY_UNICODE_PROPERTIES_OF_STRINGS.contains(&property_name_or_value.as_str()) {
                            if !self.unicode_sets_mode {
                                self.error(
                                    diag::Any_Unicode_property_that_would_possibly_match_more_than_a_single_character_is_only_available_when_the_Unicode_Sets_v_flag_is_set,
                                    property_name_or_value_start,
                                    len,
                                    vec![],
                                );
                            } else if is_character_complement {
                                self.error(
                                    diag::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class,
                                    property_name_or_value_start,
                                    len,
                                    vec![],
                                );
                            } else {
                                self.may_contain_strings = true;
                            }
                        } else if !GENERAL_CATEGORY_VALUES.contains(&property_name_or_value.as_str())
                            && !BINARY_UNICODE_PROPERTIES.contains(&property_name_or_value.as_str())
                        {
                            self.error(
                                diag::Unknown_Unicode_property_name_or_value,
                                property_name_or_value_start,
                                len,
                                vec![],
                            );
                            let suggestion =
                                self.get_spelling_suggestion_for_unicode_property_name_or_value(&property_name_or_value);
                            if !suggestion.is_empty() {
                                self.error(diag::Did_you_mean_0, property_name_or_value_start, len, args![suggestion]);
                            }
                        }
                    }
                    self.scan_expected_char('}' as i32);
                    if !self.any_unicode_mode {
                        let len = self.pos() - start;
                        self.error(
                            diag::Unicode_property_value_expressions_are_only_available_when_the_Unicode_u_flag_or_the_Unicode_Sets_v_flag_is_set,
                            start,
                            len,
                            vec![],
                        );
                    }
                } else if self.any_unicode_mode_or_non_annex_b {
                    let pos = self.pos() - 2;
                    self.error(
                        diag::X_0_must_be_followed_by_a_Unicode_property_value_expression_enclosed_in_braces,
                        pos,
                        2,
                        args![rune_to_string(ch)],
                    );
                } else {
                    self.inc_pos(-1);
                    return false;
                }
                true
            }
            _ => false,
        }
    }

    // Go: scanner/regexp.go:955 getSpellingSuggestionForUnicodePropertyName
    fn get_spelling_suggestion_for_unicode_property_name(&self, name: &str) -> String {
        get_spelling_suggestion_for_strings(
            name,
            NON_BINARY_UNICODE_PROPERTIES.iter().map(|(alias, _)| alias.to_string()),
        )
    }

    // Go: scanner/regexp.go:959 getSpellingSuggestionForUnicodePropertyValue
    fn get_spelling_suggestion_for_unicode_property_value(&self, property_name: &str, value: &str) -> String {
        let Some(values) = values_of_non_binary_unicode_properties(property_name) else {
            return String::new();
        };
        get_spelling_suggestion_for_strings(value, values.iter().map(|v| v.to_string()))
    }

    // Go: scanner/regexp.go:967 getSpellingSuggestionForUnicodePropertyNameOrValue
    fn get_spelling_suggestion_for_unicode_property_name_or_value(&self, name: &str) -> String {
        get_spelling_suggestion_for_strings(
            name,
            GENERAL_CATEGORY_VALUES
                .iter()
                .chain(BINARY_UNICODE_PROPERTIES.iter())
                .chain(BINARY_UNICODE_PROPERTIES_OF_STRINGS.iter())
                .map(|v| v.to_string()),
        )
    }

    // Go: scanner/regexp.go:975 scanWordCharacters
    fn scan_word_characters(&mut self) -> String {
        let start = self.pos();
        while self.pos() < self.end {
            let ch = self.char();
            // Go: scanner/scanner.go:2250 isWordCharacter
            // PORT: inlined; the scanner_util.rs copy is private and takes `char`.
            if !rune(ch).is_some_and(|c| is_ascii_letter(c) || is_digit(c) || c == '_') {
                break;
            }
            self.inc_pos(1);
        }
        // Word characters are ASCII, so this slice is on char boundaries.
        self.text()[start as usize..self.pos() as usize].to_string()
    }

    // Go: scanner/regexp.go:987 scanSourceCharacter
    fn scan_source_character(&mut self) -> Vec<u8> {
        if self.pos() >= self.end {
            return Vec::new();
        }
        if !self.any_unicode_mode {
            if self.pending_low_surrogate != 0 {
                // Second of two surrogate code units for the same non-BMP character.
                // Now advance past the full UTF-8 sequence (the high surrogate call did not advance).
                let (_, size) = self.decode_rune_at_pos();
                self.inc_pos(size);
                let low = self.pending_low_surrogate;
                self.pending_low_surrogate = 0;
                return encode_js_string_rune_bytes(low);
            }
            let (ch, size) = self.decode_rune_at_pos();
            if ch == RUNE_ERROR || size == 0 {
                // Not a valid rune; consume one raw byte.
                self.inc_pos(1);
                let byte = self.text().as_bytes()[self.pos() as usize - 1];
                return rune_to_bytes(i32::from(byte));
            }
            // Go: utf16.RuneLen(ch) == 2
            if (0x10000..=0x10FFFF).contains(&ch) {
                // Non-BMP character: emit the high surrogate first WITHOUT advancing.
                // The low surrogate will be emitted on the next call, which also advances.
                let (high, low) = code_point_to_surrogate_pair_i32(ch);
                self.pending_low_surrogate = low;
                return encode_js_string_rune_bytes(high);
            }
            self.inc_pos(size);
            return rune_to_bytes(ch);
        }
        let (ch, size) = self.decode_rune_at_pos();
        if size == 0 {
            return Vec::new();
        }
        if ch == RUNE_ERROR {
            // Invalid UTF-8; consume the byte to avoid infinite loops.
            self.inc_pos(size);
            return Vec::new();
        }
        self.inc_pos(size);
        rune_to_bytes(ch)
    }

    // Go: scanner/regexp.go:1030 scanExpectedChar
    fn scan_expected_char(&mut self, ch: i32) {
        if self.char() == ch {
            self.inc_pos(1);
        } else {
            let pos = self.pos();
            self.error(diag::X_0_expected, pos, 0, args![rune_to_string(ch)]);
        }
    }

    // Go: scanner/regexp.go:1038 scanDigits
    fn scan_digits(&mut self) {
        let start = self.pos();
        while self.pos() < self.end && rune(self.char()).is_some_and(is_digit) {
            self.inc_pos(1);
        }
        let value = self.text()[start as usize..self.pos() as usize].to_string();
        self.scanner.set_token_value(&value);
    }

    // Go: scanner/regexp.go:1046 run
    pub fn run(&mut self) {
        // Regular expressions are checked more strictly when either in 'u' or 'v' mode, or
        // when not using the looser interpretation of the syntax from ECMA-262 Annex B.
        self.any_unicode_mode_or_non_annex_b = self.any_unicode_mode || !self.annex_b;

        self.scan_disjunction(false /*isInGroup*/);

        let references = self.group_name_references.clone();
        for reference in &references {
            if !self.group_specifiers.get(&reference.name).copied().unwrap_or(false) {
                self.error(
                    diag::There_is_no_capturing_group_named_0_in_this_regular_expression,
                    reference.pos,
                    reference.end - reference.pos,
                    args![reference.name],
                );
                if !self.group_specifiers.is_empty() {
                    // PORT: Go iterates the map keys in random order. The
                    // result does not depend on order: ties are broken by
                    // `strings.Compare`.
                    let suggestion =
                        get_spelling_suggestion_for_strings(&reference.name, self.group_specifiers.keys().cloned());
                    if !suggestion.is_empty() {
                        self.error(
                            diag::Did_you_mean_0,
                            reference.pos,
                            reference.end - reference.pos,
                            args![suggestion],
                        );
                    }
                }
            }
        }
        let escapes = self.decimal_escapes.clone();
        for escape in &escapes {
            // Although a DecimalEscape with a value greater than the number of capturing groups
            // is treated as either a LegacyOctalEscapeSequence or an IdentityEscape in Annex B,
            // an error is nevertheless reported since it's most likely a mistake.
            if escape.value > self.number_of_capturing_groups {
                if self.number_of_capturing_groups > 0 {
                    let n = self.number_of_capturing_groups;
                    self.error(
                        diag::This_backreference_refers_to_a_group_that_does_not_exist_There_are_only_0_capturing_groups_in_this_regular_expression,
                        escape.pos,
                        escape.end - escape.pos,
                        args![n],
                    );
                } else {
                    self.error(
                        diag::This_backreference_refers_to_a_group_that_does_not_exist_There_are_no_capturing_groups_in_this_regular_expression,
                        escape.pos,
                        escape.end - escape.pos,
                        vec![],
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Private Go runtime helpers (PORT: `unicode/utf8`, `unicode/utf16` and
// `stringutil` byte math on Go string bytes).
// ---------------------------------------------------------------------------

/// A Go `rune` as a Rust `char` for `match` and predicates. -1 (end of text)
/// and surrogates give `None`.
fn rune(ch: i32) -> Option<char> {
    u32::try_from(ch).ok().and_then(char::from_u32)
}

/// Go `string(rune)`: UTF-8 bytes. An invalid rune gives U+FFFD.
fn rune_to_bytes(ch: i32) -> Vec<u8> {
    rune_to_string(ch).into_bytes()
}

/// Go `utf8.DecodeRuneInString(s)`: `(RuneError, 0)` for empty input and
/// `(RuneError, 1)` for an invalid sequence.
fn decode_rune_in_bytes(s: &[u8]) -> (i32, i32) {
    if s.is_empty() {
        return (RUNE_ERROR, 0);
    }
    let head = &s[..s.len().min(4)];
    let valid = match std::str::from_utf8(head) {
        Ok(text) => text,
        // The prefix up to `valid_up_to` is valid UTF-8.
        Err(err) => std::str::from_utf8(&head[..err.valid_up_to()]).unwrap_or(""),
    };
    match valid.chars().next() {
        Some(ch) => (ch as i32, ch.len_utf8() as i32),
        None => (RUNE_ERROR, 1),
    }
}

/// Go `utf16.EncodeRune` through `stringutil.CodePointToSurrogatePair`.
fn code_point_to_surrogate_pair_i32(ch: i32) -> (i32, i32) {
    if !(0x10000..=0x10FFFF).contains(&ch) {
        return (RUNE_ERROR, RUNE_ERROR);
    }
    let r = ch - 0x10000;
    (0xD800 + ((r >> 10) & 0x3FF), 0xDC00 + (r & 0x3FF))
}

// Go: stringutil/util.go:323 EncodeJSStringRune
// PORT: byte-string copy of `scanner_util::encode_js_string_rune`, which
// cannot keep the lone-surrogate sentinel in a Rust `String`.
fn encode_js_string_rune_bytes(ch: i32) -> Vec<u8> {
    if (0xD800..0xE000).contains(&ch) {
        return vec![0xED, (0x80 | ((ch >> 6) & 0x3F)) as u8, (0x80 | (ch & 0x3F)) as u8];
    }
    rune_to_bytes(ch)
}

// Go: stringutil/util.go:334 DecodeJSStringRune
// PORT: byte-string copy of `scanner_util::decode_js_string_rune`, which
// cannot see the lone-surrogate sentinel in a Rust `&str`.
fn decode_js_string_rune_bytes(s: &[u8]) -> (i32, usize) {
    if s.len() >= 3 && s[0] == 0xED && (0xA0..=0xBF).contains(&s[1]) && (0x80..=0xBF).contains(&s[2]) {
        return (0xD000 | (i32::from(s[1] & 0x3F) << 6) | i32::from(s[2] & 0x3F), 3);
    }
    let (ch, size) = decode_rune_in_bytes(s);
    (ch, size as usize)
}
