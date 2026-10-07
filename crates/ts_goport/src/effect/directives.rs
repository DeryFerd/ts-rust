//! Port of Effect-TS/tsgo `internal/directives/parser.go`: the
//! `@effect-diagnostics` and `@effect-diagnostics-next-line` comments.

use crate::diagnostics::Category;
use crate::effect::etscore::Severity;
use rustc_hash::FxHashMap;

// Go: directives/parser.go ToCategory
#[must_use]
pub fn to_category(s: Severity) -> Category {
    match s {
        Severity::Error => Category::Error,
        Severity::Warning => Category::Warning,
        Severity::Suggestion => Category::Suggestion,
        Severity::Message => Category::Message,
        _ => Category::Warning,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleSeverity {
    pub rule: String,
    pub severity: Severity,
}

/// One directive comment. `line` is 0-based; `pos` and `end` are the byte
/// offsets of the matched text in the source.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Directive {
    pub line: i32,
    pub pos: i32,
    pub end: i32,
    pub is_next_line: bool,
    pub rules: Vec<RuleSeverity>,
}

impl Directive {
    #[must_use]
    pub fn affected_line(&self) -> i32 {
        if self.is_next_line {
            return self.line + 1;
        }
        self.line
    }
}

/// Go RE2 `\w`.
fn is_word(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Go RE2 `\s`: `[\t\n\f\r ]`.
fn is_space(b: u8) -> bool {
    matches!(b, b'\t' | b'\n' | b'\x0c' | b'\r' | b' ')
}

/// `[\w:\-*]`
fn is_rule_char(b: u8) -> bool {
    is_word(b) || matches!(b, b':' | b'-' | b'*')
}

fn span_while(s: &[u8], mut i: usize, f: impl Fn(u8) -> bool) -> usize {
    while i < s.len() && f(s[i]) {
        i += 1;
    }
    i
}

const DIRECTIVE: &[u8] = b"@effect-diagnostics";
const NEXT_LINE: &[u8] = b"-next-line";

/// Go `directivePattern.FindStringSubmatchIndex` for
/// `@effect-diagnostics(-next-line)?\s+([\w:\-*]+(?:\s+[\w:\-*]+)*)`:
/// (match start, match end, is next line, rules start, rules end).
fn find_directive(line: &[u8]) -> Option<(usize, usize, bool, usize, usize)> {
    let mut from = 0;
    while let Some(off) = line[from..]
        .windows(DIRECTIVE.len())
        .position(|w| w == DIRECTIVE)
    {
        let start = from + off;
        let after = start + DIRECTIVE.len();
        // Leftmost-first: the optional group is tried before its absence.
        let mut candidates = Vec::with_capacity(2);
        if line[after..].starts_with(NEXT_LINE) {
            candidates.push((after + NEXT_LINE.len(), true));
        }
        candidates.push((after, false));
        for (at, next_line) in candidates {
            let spaces_end = span_while(line, at, is_space);
            if spaces_end == at {
                continue;
            }
            let first_end = span_while(line, spaces_end, is_rule_char);
            if first_end == spaces_end {
                continue;
            }
            // `(?:\s+[\w:\-*]+)*`, greedy.
            let mut end = first_end;
            loop {
                let ws_end = span_while(line, end, is_space);
                if ws_end == end {
                    break;
                }
                let tok_end = span_while(line, ws_end, is_rule_char);
                if tok_end == ws_end {
                    break;
                }
                end = tok_end;
            }
            return Some((start, end, next_line, spaces_end, end));
        }
        from = start + 1;
    }
    None
}

/// Go `ruleSeverityPattern.FindAllStringSubmatch` for
/// `(\w+|\*):(\w+(?:-\w+)?)`.
fn find_rule_severities(s: &[u8]) -> Vec<(String, String)> {
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len() {
        let name_end = if is_word(s[i]) {
            span_while(s, i, is_word)
        } else if s[i] == b'*' {
            i + 1
        } else {
            i += 1;
            continue;
        };
        if name_end >= s.len() || s[name_end] != b':' {
            i += 1;
            continue;
        }
        let sev_start = name_end + 1;
        let mut sev_end = span_while(s, sev_start, is_word);
        if sev_end == sev_start {
            i += 1;
            continue;
        }
        if sev_end < s.len() && s[sev_end] == b'-' {
            let tail_end = span_while(s, sev_end + 1, is_word);
            if tail_end > sev_end + 1 {
                sev_end = tail_end;
            }
        }
        let text = |a: usize, b: usize| String::from_utf8_lossy(&s[a..b]).into_owned();
        result.push((text(i, name_end), text(sev_start, sev_end)));
        i = sev_end;
    }
    result
}

// Go: directives/parser.go CollectEffectDirectives
#[must_use]
pub fn collect_effect_directives(source_text: &str) -> Vec<Directive> {
    let mut directives = Vec::new();
    let mut line_start_pos: usize = 0;
    for (line_num, line) in source_text.split('\n').enumerate() {
        let bytes = line.as_bytes();
        if let Some((match_start, match_end, is_next_line, rules_start, rules_end)) =
            find_directive(bytes)
        {
            let rules: Vec<RuleSeverity> = find_rule_severities(&bytes[rules_start..rules_end])
                .into_iter()
                .map(|(rule, severity)| RuleSeverity {
                    rule,
                    severity: Severity::parse(&severity),
                })
                .collect();
            if !rules.is_empty() {
                directives.push(Directive {
                    line: i32::try_from(line_num).unwrap_or(i32::MAX),
                    pos: i32::try_from(line_start_pos + match_start).unwrap_or(i32::MAX),
                    end: i32::try_from(line_start_pos + match_end).unwrap_or(i32::MAX),
                    is_next_line,
                    rules,
                });
            }
        }
        line_start_pos += line.len() + 1; // +1 for newline
    }
    directives
}

/// Go `DirectiveSet`.
#[derive(Debug, Default)]
pub struct DirectiveSet {
    by_line: FxHashMap<i32, Vec<Directive>>,
    file_level: Vec<RuleSeverity>,
    section_directives: Vec<Directive>,
    used_directives: FxHashMap<i32, bool>,
}

fn rule_matches(rule: &str, rule_lower: &str) -> bool {
    let name = rule.to_lowercase();
    name == rule_lower || name == "*"
}

// Go: directives/parser.go BuildDirectiveSet
#[must_use]
pub fn build_directive_set(directives: &[Directive]) -> DirectiveSet {
    let mut ds = DirectiveSet::default();
    for d in directives {
        let mut has_skip_file = false;
        for rs in &d.rules {
            if rs.severity == Severity::SkipFile {
                ds.file_level.push(rs.clone());
                has_skip_file = true;
            }
        }
        if d.is_next_line {
            ds.by_line
                .entry(d.affected_line())
                .or_default()
                .push(d.clone());
        } else if !has_skip_file {
            let section_rules: Vec<RuleSeverity> = d
                .rules
                .iter()
                .filter(|rs| rs.severity != Severity::SkipFile)
                .cloned()
                .collect();
            if !section_rules.is_empty() {
                ds.section_directives.push(Directive {
                    line: d.line,
                    is_next_line: false,
                    rules: section_rules,
                    ..Default::default()
                });
            }
        }
    }
    ds
}

impl DirectiveSet {
    // Go: GetEffectiveSeverity
    #[must_use]
    pub fn get_effective_severity(
        &self,
        rule_name: &str,
        line: i32,
        default_severity: Severity,
    ) -> Severity {
        self.effective_severity(rule_name, line, default_severity).0
    }

    // Go: IsSuppressed
    #[must_use]
    pub fn is_suppressed(&self, rule_name: &str, line: i32) -> bool {
        let severity = self.get_effective_severity(rule_name, line, Severity::Error);
        severity == Severity::Off || severity == Severity::SkipFile
    }

    // Go: IsSkipFile
    #[must_use]
    pub fn is_skip_file(&self, rule_name: &str) -> bool {
        let rule_lower = rule_name.to_lowercase();
        self.file_level
            .iter()
            .any(|rs| rule_matches(&rs.rule, &rule_lower))
    }

    // Go: GetEffectiveSeverityAndMarkUsed
    pub fn get_effective_severity_and_mark_used(
        &mut self,
        rule_name: &str,
        line: i32,
        default_severity: Severity,
    ) -> Severity {
        let (severity, used_line) = self.effective_severity(rule_name, line, default_severity);
        if let Some(used_line) = used_line {
            self.used_directives.insert(used_line, true);
        }
        severity
    }

    fn effective_severity(
        &self,
        rule_name: &str,
        line: i32,
        default_severity: Severity,
    ) -> (Severity, Option<i32>) {
        let rule_lower = rule_name.to_lowercase();
        if self
            .file_level
            .iter()
            .any(|rs| rule_matches(&rs.rule, &rule_lower))
        {
            return (Severity::SkipFile, None);
        }
        if let Some(directives) = self.by_line.get(&line) {
            for d in directives {
                for rs in &d.rules {
                    if rule_matches(&rs.rule, &rule_lower) {
                        return (rs.severity, Some(d.line));
                    }
                }
            }
        }
        for sd in self.section_directives.iter().rev() {
            if sd.line > line {
                continue;
            }
            for rs in &sd.rules {
                if rule_matches(&rs.rule, &rule_lower) {
                    return (rs.severity, None);
                }
            }
        }
        (default_severity, None)
    }

    // Go: HasEnablingDirective
    #[must_use]
    pub fn has_enabling_directive(&self, rule_name: &str) -> bool {
        let rule_lower = rule_name.to_lowercase();
        let enables =
            |rs: &RuleSeverity| rule_matches(&rs.rule, &rule_lower) && !rs.severity.is_off();
        self.section_directives
            .iter()
            .any(|sd| sd.rules.iter().any(enables))
            || self
                .by_line
                .values()
                .flatten()
                .any(|d| d.rules.iter().any(enables))
    }

    // Go: HasAnyDirectiveForRule
    #[must_use]
    pub fn has_any_directive_for_rule(&self, rule_name: &str) -> bool {
        let rule_lower = rule_name.to_lowercase();
        let matches =
            |rules: &[RuleSeverity]| rules.iter().any(|rs| rule_matches(&rs.rule, &rule_lower));
        matches(&self.file_level)
            || self.section_directives.iter().any(|sd| matches(&sd.rules))
            || self.by_line.values().flatten().any(|d| matches(&d.rules))
    }

    // Go: GetUnusedNextLineDirectives
    #[must_use]
    pub fn get_unused_next_line_directives(&self, all: &[Directive]) -> Vec<Directive> {
        all.iter()
            .filter(|d| {
                d.is_next_line
                    && !self.used_directives.get(&d.line).copied().unwrap_or(false)
                    && !d.rules.iter().any(|rs| rs.rule == "*")
            })
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rules(d: &Directive) -> Vec<(&str, Severity)> {
        d.rules
            .iter()
            .map(|r| (r.rule.as_str(), r.severity))
            .collect()
    }

    #[test]
    fn collects_directives_like_go() {
        let ds = collect_effect_directives(
            "// @effect-diagnostics floatingEffect:off pocRule:warning\nconst x = 1;\n// @effect-diagnostics-next-line *:off because reasons\n// @effect-diagnostics *:skip-file",
        );
        assert_eq!(ds.len(), 3);
        assert_eq!(
            rules(&ds[0]),
            [
                ("floatingEffect", Severity::Off),
                ("pocRule", Severity::Warning)
            ]
        );
        assert!(!ds[0].is_next_line);
        assert_eq!((ds[0].pos, ds[0].end), (3, 57));
        assert_eq!(ds[1].line, 2);
        assert!(ds[1].is_next_line);
        assert_eq!(rules(&ds[1]), [("*", Severity::Off)]);
        assert_eq!(rules(&ds[2]), [("*", Severity::SkipFile)]);
    }

    #[test]
    fn reason_text_does_not_add_rules() {
        let ds = collect_effect_directives(
            "// @effect-diagnostics-next-line globalDate:off date is fine here",
        );
        assert_eq!(rules(&ds[0]), [("globalDate", Severity::Off)]);
    }

    #[test]
    fn next_line_and_section_severity() {
        let src = "// @effect-diagnostics-next-line floatingEffect:off\nx\n// @effect-diagnostics FloatingEffect:warning\ny";
        let mut set = build_directive_set(&collect_effect_directives(src));
        assert_eq!(
            set.get_effective_severity("floatingEffect", 1, Severity::Error),
            Severity::Off
        );
        assert_eq!(
            set.get_effective_severity("floatingEffect", 0, Severity::Error),
            Severity::Error
        );
        assert_eq!(
            set.get_effective_severity("floatingEffect", 3, Severity::Error),
            Severity::Warning
        );
        let all = collect_effect_directives(src);
        assert_eq!(set.get_unused_next_line_directives(&all).len(), 1);
        set.get_effective_severity_and_mark_used("floatingEffect", 1, Severity::Error);
        assert!(set.get_unused_next_line_directives(&all).is_empty());
    }
}
