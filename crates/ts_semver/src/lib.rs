//! TypeScript-compatible semantic versions and npm-style version ranges.

use std::{cmp::Ordering, error::Error, fmt, str::FromStr};

/// A semantic version. Missing minor and patch components parse as zero.
#[derive(Clone, Debug)]
pub struct Version {
    major: u32,
    minor: u32,
    patch: u32,
    prerelease: Vec<String>,
    build: Vec<String>,
}

impl Version {
    #[must_use]
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
            prerelease: Vec::new(),
            build: Vec::new(),
        }
    }

    /// Parses a semantic version.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed components, identifiers, or overflow.
    pub fn parse(text: &str) -> Result<Self, SemverParseError> {
        parse_version(text)
    }

    #[must_use]
    pub const fn major(&self) -> u32 {
        self.major
    }

    #[must_use]
    pub const fn minor(&self) -> u32 {
        self.minor
    }

    #[must_use]
    pub const fn patch(&self) -> u32 {
        self.patch
    }

    #[must_use]
    pub fn prerelease(&self) -> &[String] {
        &self.prerelease
    }

    #[must_use]
    pub fn build(&self) -> &[String] {
        &self.build
    }

    fn increment_major(&self) -> Self {
        Self::new(self.major.saturating_add(1), 0, 0)
    }

    fn increment_minor(&self) -> Self {
        Self::new(self.major, self.minor.saturating_add(1), 0)
    }

    fn increment_patch(&self) -> Self {
        Self::new(self.major, self.minor, self.patch.saturating_add(1))
    }

    fn with_zero_prerelease(mut self) -> Self {
        self.prerelease = vec!["0".to_owned()];
        self
    }
}

impl fmt::Display for Version {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if !self.prerelease.is_empty() {
            write!(formatter, "-{}", self.prerelease.join("."))?;
        }
        if !self.build.is_empty() {
            write!(formatter, "+{}", self.build.join("."))?;
        }
        Ok(())
    }
}

impl FromStr for Version {
    type Err = SemverParseError;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Self::parse(text)
    }
}

impl PartialEq for Version {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Version {}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> Ordering {
        self.major
            .cmp(&other.major)
            .then_with(|| self.minor.cmp(&other.minor))
            .then_with(|| self.patch.cmp(&other.patch))
            .then_with(|| compare_prerelease(&self.prerelease, &other.prerelease))
    }
}

/// A semantic version or range parsing failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemverParseError {
    input: String,
}

impl SemverParseError {
    fn new(input: &str) -> Self {
        Self {
            input: input.to_owned(),
        }
    }
}

impl fmt::Display for SemverParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "Could not parse version string from {:?}",
            self.input
        )
    }
}

impl Error for SemverParseError {}

/// Parses a version using the upstream TypeScript semver grammar.
///
/// # Errors
///
/// Returns an error when `text` is not a valid semantic version.
pub fn try_parse_version(text: &str) -> Result<Version, SemverParseError> {
    Version::parse(text)
}

/// Parses a version and panics if it is malformed.
///
/// # Panics
///
/// Panics when `text` is not a valid semantic version.
#[must_use]
pub fn must_parse(text: &str) -> Version {
    Version::parse(text).unwrap_or_else(|error| panic!("{error}"))
}

/// An npm-style disjunction of comparator sets.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VersionRange {
    alternatives: Vec<Vec<Comparator>>,
}

impl VersionRange {
    /// Parses a version range.
    ///
    /// # Errors
    ///
    /// Returns an error when any partial version or comparator is malformed.
    pub fn parse(text: &str) -> Result<Self, SemverParseError> {
        parse_range(text).ok_or_else(|| SemverParseError::new(text))
    }

    #[must_use]
    pub fn test(&self, version: &Version) -> bool {
        self.alternatives.is_empty()
            || self.alternatives.iter().any(|alternative| {
                alternative
                    .iter()
                    .all(|comparator| comparator.test(version))
            })
    }
}

impl fmt::Display for VersionRange {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.alternatives.is_empty() {
            return formatter.write_str("*");
        }
        for (alternative_index, alternative) in self.alternatives.iter().enumerate() {
            if alternative_index != 0 {
                formatter.write_str(" || ")?;
            }
            if alternative.is_empty() {
                formatter.write_str("*")?;
            } else {
                for (index, comparator) in alternative.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(" ")?;
                    }
                    write!(formatter, "{}{}", comparator.operator, comparator.operand)?;
                }
            }
        }
        Ok(())
    }
}

impl FromStr for VersionRange {
    type Err = SemverParseError;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Self::parse(text)
    }
}

/// Attempts to parse a TypeScript-compatible npm version range.
#[must_use]
pub fn try_parse_version_range(text: &str) -> Option<VersionRange> {
    parse_range(text)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Operator {
    Less,
    LessEqual,
    Equal,
    GreaterEqual,
    Greater,
}

impl fmt::Display for Operator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Equal => "=",
            Self::GreaterEqual => ">=",
            Self::Greater => ">",
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Comparator {
    operator: Operator,
    operand: Version,
}

impl Comparator {
    fn test(&self, version: &Version) -> bool {
        let comparison = version.cmp(&self.operand);
        match self.operator {
            Operator::Less => comparison == Ordering::Less,
            Operator::LessEqual => comparison != Ordering::Greater,
            Operator::Equal => comparison == Ordering::Equal,
            Operator::GreaterEqual => comparison != Ordering::Less,
            Operator::Greater => comparison == Ordering::Greater,
        }
    }
}

#[derive(Clone, Debug)]
struct PartialVersion {
    version: Version,
    major_wildcard: bool,
    minor_wildcard: bool,
    patch_wildcard: bool,
}

fn parse_version(text: &str) -> Result<Version, SemverParseError> {
    let (without_build, build) = split_once_optional(text, '+', false)?;
    let (core, prerelease) = split_once_optional(without_build, '-', true)?;
    let components = core.split('.').collect::<Vec<_>>();
    if components.is_empty() || components.len() > 3 {
        return Err(SemverParseError::new(text));
    }
    let major = parse_number(components[0]).ok_or_else(|| SemverParseError::new(text))?;
    let minor = components
        .get(1)
        .map_or(Some(0), |value| parse_number(value))
        .ok_or_else(|| SemverParseError::new(text))?;
    let patch = components
        .get(2)
        .map_or(Some(0), |value| parse_number(value))
        .ok_or_else(|| SemverParseError::new(text))?;
    let prerelease =
        parse_identifiers(prerelease, true).ok_or_else(|| SemverParseError::new(text))?;
    let build = parse_identifiers(build, false).ok_or_else(|| SemverParseError::new(text))?;
    Ok(Version {
        major,
        minor,
        patch,
        prerelease,
        build,
    })
}

fn split_once_optional(
    text: &str,
    delimiter: char,
    allow_in_value: bool,
) -> Result<(&str, Option<&str>), SemverParseError> {
    let (first, second) = text
        .split_once(delimiter)
        .map_or((text, None), |(first, second)| (first, Some(second)));
    if second == Some("")
        || !allow_in_value && second.is_some_and(|value| value.contains(delimiter))
    {
        Err(SemverParseError::new(text))
    } else {
        Ok((first, second))
    }
}

fn parse_number(text: &str) -> Option<u32> {
    if text.is_empty()
        || !text.bytes().all(|byte| byte.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return None;
    }
    text.parse().ok()
}

fn parse_identifiers(value: Option<&str>, prerelease: bool) -> Option<Vec<String>> {
    let Some(value) = value else {
        return Some(Vec::new());
    };
    value
        .split('.')
        .map(|part| {
            let valid = !part.is_empty()
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
                && (!prerelease
                    || !part.bytes().all(|byte| byte.is_ascii_digit())
                    || part == "0"
                    || !part.starts_with('0'));
            valid.then(|| part.to_owned())
        })
        .collect()
}

fn compare_prerelease(left: &[String], right: &[String]) -> Ordering {
    match (left.is_empty(), right.is_empty()) {
        (true, true) => return Ordering::Equal,
        (true, false) => return Ordering::Greater,
        (false, true) => return Ordering::Less,
        (false, false) => {}
    }
    for (left, right) in left.iter().zip(right) {
        let comparison = compare_identifier(left, right);
        if comparison != Ordering::Equal {
            return comparison;
        }
    }
    left.len().cmp(&right.len())
}

fn compare_identifier(left: &str, right: &str) -> Ordering {
    let left_numeric = left.bytes().all(|byte| byte.is_ascii_digit());
    let right_numeric = right.bytes().all(|byte| byte.is_ascii_digit());
    match (left_numeric, right_numeric) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        (true, true) => left.len().cmp(&right.len()).then_with(|| left.cmp(right)),
        (false, false) => left.cmp(right),
    }
}

fn parse_range(text: &str) -> Option<VersionRange> {
    let mut alternatives = Vec::new();
    for range in text
        .split("||")
        .map(str::trim)
        .filter(|range| !range.is_empty())
    {
        if let Some((left, right)) = split_hyphen(range) {
            alternatives.push(parse_hyphen(left, right)?);
        } else {
            let mut comparators = Vec::new();
            for simple in range.split_whitespace() {
                comparators.extend(parse_simple(simple)?);
            }
            alternatives.push(comparators);
        }
    }
    Some(VersionRange { alternatives })
}

fn split_hyphen(text: &str) -> Option<(&str, &str)> {
    let bytes = text.as_bytes();
    for index in 1..bytes.len().saturating_sub(1) {
        if bytes[index] == b'-'
            && bytes[index - 1].is_ascii_whitespace()
            && bytes[index + 1].is_ascii_whitespace()
        {
            return Some((text[..index].trim(), text[index + 1..].trim()));
        }
    }
    None
}

fn parse_hyphen(left: &str, right: &str) -> Option<Vec<Comparator>> {
    let left = parse_partial(left)?;
    let right = parse_partial(right)?;
    let mut result = Vec::new();
    if !left.major_wildcard {
        result.push(Comparator {
            operator: Operator::GreaterEqual,
            operand: left.version,
        });
    }
    if !right.major_wildcard {
        let (operator, operand) = if right.minor_wildcard {
            (Operator::Less, right.version.increment_major())
        } else if right.patch_wildcard {
            (Operator::Less, right.version.increment_minor())
        } else {
            (Operator::LessEqual, right.version)
        };
        result.push(Comparator { operator, operand });
    }
    Some(result)
}

fn parse_simple(text: &str) -> Option<Vec<Comparator>> {
    let (operator, partial) = if let Some(rest) = text.strip_prefix(">=") {
        (">=", rest)
    } else if let Some(rest) = text.strip_prefix("<=") {
        ("<=", rest)
    } else if let Some(rest) = text.strip_prefix(['~', '^', '<', '>', '=']) {
        (&text[..1], rest)
    } else {
        ("", text)
    };
    parse_comparator(operator, parse_partial(partial)?)
}

fn parse_partial(text: &str) -> Option<PartialVersion> {
    if text.is_empty() {
        return None;
    }
    let (without_build, build) = split_once_optional(text, '+', false).ok()?;
    let (core, prerelease) = split_once_optional(without_build, '-', true).ok()?;
    let components = core.split('.').collect::<Vec<_>>();
    if components.is_empty() || components.len() > 3 {
        return None;
    }
    let major_wildcard = is_wildcard(components[0]);
    let minor_wildcard = components.get(1).is_none_or(|value| is_wildcard(value));
    let patch_wildcard = components.get(2).is_none_or(|value| is_wildcard(value));
    if major_wildcard && components.iter().any(|component| !is_wildcard(component))
        || minor_wildcard && components.get(2).is_some_and(|value| !is_wildcard(value))
    {
        return None;
    }
    let major = if major_wildcard {
        0
    } else {
        parse_number(components[0])?
    };
    let minor = if minor_wildcard {
        0
    } else {
        parse_number(components[1])?
    };
    let patch = if patch_wildcard {
        0
    } else {
        parse_number(components[2])?
    };
    Some(PartialVersion {
        version: Version {
            major,
            minor,
            patch,
            prerelease: parse_identifiers(prerelease, true)?,
            build: parse_identifiers(build, false)?,
        },
        major_wildcard,
        minor_wildcard,
        patch_wildcard,
    })
}

fn parse_comparator(operator: &str, partial: PartialVersion) -> Option<Vec<Comparator>> {
    if partial.major_wildcard {
        return Some(if matches!(operator, "<" | ">") {
            vec![Comparator {
                operator: Operator::Less,
                operand: Version::new(0, 0, 0).with_zero_prerelease(),
            }]
        } else {
            Vec::new()
        });
    }
    let result = match operator {
        "~" => {
            let upper = if partial.minor_wildcard {
                partial.version.increment_major()
            } else {
                partial.version.increment_minor()
            };
            bounds(partial.version, upper)
        }
        "^" => {
            let upper = if partial.version.major > 0 || partial.minor_wildcard {
                partial.version.increment_major()
            } else if partial.version.minor > 0 || partial.patch_wildcard {
                partial.version.increment_minor()
            } else {
                partial.version.increment_patch()
            };
            bounds(partial.version, upper)
        }
        "<" | ">=" => {
            let mut version = partial.version;
            if partial.minor_wildcard || partial.patch_wildcard {
                version = version.with_zero_prerelease();
            }
            vec![Comparator {
                operator: if operator == "<" {
                    Operator::Less
                } else {
                    Operator::GreaterEqual
                },
                operand: version,
            }]
        }
        "<=" | ">" => {
            let mut normalized_operator = if operator == "<=" {
                Operator::LessEqual
            } else {
                Operator::Greater
            };
            let mut version = partial.version;
            if partial.minor_wildcard {
                normalized_operator = if operator == "<=" {
                    Operator::Less
                } else {
                    Operator::GreaterEqual
                };
                version = version.increment_major().with_zero_prerelease();
            } else if partial.patch_wildcard {
                normalized_operator = if operator == "<=" {
                    Operator::Less
                } else {
                    Operator::GreaterEqual
                };
                version = version.increment_minor().with_zero_prerelease();
            }
            vec![Comparator {
                operator: normalized_operator,
                operand: version,
            }]
        }
        "" | "=" => {
            if partial.minor_wildcard || partial.patch_wildcard {
                let lower = partial.version.clone().with_zero_prerelease();
                let upper = if partial.minor_wildcard {
                    partial.version.increment_major()
                } else {
                    partial.version.increment_minor()
                }
                .with_zero_prerelease();
                bounds(lower, upper)
            } else {
                vec![Comparator {
                    operator: Operator::Equal,
                    operand: partial.version,
                }]
            }
        }
        _ => return None,
    };
    Some(result)
}

fn bounds(lower: Version, upper: Version) -> Vec<Comparator> {
    vec![
        Comparator {
            operator: Operator::GreaterEqual,
            operand: lower,
        },
        Comparator {
            operator: Operator::Less,
            operand: upper,
        },
    ]
}

fn is_wildcard(text: &str) -> bool {
    matches!(text, "*" | "x" | "X")
}

#[cfg(test)]
mod tests {
    use super::{Version, VersionRange};

    fn assert_range(range: &str, good: &[&str], bad: &[&str]) {
        let range = VersionRange::parse(range).unwrap();
        for version in good {
            assert!(range.test(&Version::parse(version).unwrap()), "{version}");
        }
        for version in bad {
            assert!(!range.test(&Version::parse(version).unwrap()), "{version}");
        }
    }

    #[test]
    fn parses_formats_and_compares_versions() {
        let version = Version::parse("1.2.3-pre.4+build.5").unwrap();
        assert_eq!(version.to_string(), "1.2.3-pre.4+build.5");
        assert_eq!(Version::parse("1.2").unwrap().to_string(), "1.2.0");
        assert!(
            Version::parse("1.0.0-alpha.2").unwrap() < Version::parse("1.0.0-alpha.10").unwrap()
        );
        assert_eq!(
            Version::parse("1.0.0+a").unwrap(),
            Version::parse("1.0.0+b").unwrap()
        );
        assert_eq!(
            Version::parse("1.0.0-alpha-beta").unwrap().prerelease(),
            ["alpha-beta"]
        );
        assert!(Version::parse("01.0.0").is_err());
        assert!(Version::parse("1.0.0-01").is_err());
    }

    #[test]
    fn supports_wildcards_and_comparators() {
        assert_range("1", &["1.0.0-pre", "1.9.9"], &["0.9.9", "2.0.0"]);
        assert_range("1.2", &["1.2.0-pre", "1.2.9"], &["1.1.9", "1.3.0"]);
        assert_range(">=3.8.0 <4", &["3.8.0", "3.9.9"], &["3.7.9", "4.0.0"]);
        assert_range(">*", &[], &["0.0.0", "99.0.0"]);
    }

    #[test]
    fn supports_hyphen_tilde_caret_and_disjunction() {
        assert_range("1.0.0 - 2.0.0", &["1.0.0", "2.0.0"], &["0.9.9", "2.0.1"]);
        assert_range("~1.2", &["1.2.0", "1.2.9"], &["1.1.9", "1.3.0"]);
        assert_range("^0.1.2", &["0.1.2", "0.1.9"], &["0.1.1", "0.2.0"]);
        assert_range(">1.0.0 || <1.0.0", &["1.0.1", "0.9.9"], &["1.0.0"]);
    }

    #[test]
    fn canonicalizes_equivalent_wildcards() {
        let expected = VersionRange::parse("1").unwrap().to_string();
        for range in ["1.*", "1.x", "1.X.X"] {
            assert_eq!(VersionRange::parse(range).unwrap().to_string(), expected);
        }
        assert_eq!(VersionRange::parse("").unwrap().to_string(), "*");
    }
}
