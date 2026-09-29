//! JavaScript-compatible `Number` operations and pseudo-bigint handling. This
//! was the `ts_jsnum` crate.

use std::{fmt, ops};

use num_bigint::BigInt;
use num_traits::ToPrimitive;

pub const MAX_SAFE_INTEGER: Number = Number(9_007_199_254_740_991.0);
pub const MIN_SAFE_INTEGER: Number = Number(-9_007_199_254_740_991.0);

#[must_use]
pub fn nan() -> Number {
    Number::nan()
}

#[must_use]
pub fn infinity(sign: i32) -> Number {
    Number::infinity(sign)
}

/// ECMAScript `StringToNumber` conversion.
#[must_use]
pub fn from_string(text: &str) -> Number {
    Number::from_string(text)
}

/// A JavaScript IEEE-754 `Number` value.
#[derive(Clone, Copy, Debug, Default, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Number(pub f64);

impl Number {
    #[must_use]
    pub const fn new(value: f64) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn value(self) -> f64 {
        self.0
    }

    #[must_use]
    pub fn nan() -> Self {
        Self(f64::NAN)
    }

    #[must_use]
    pub fn infinity(sign: i32) -> Self {
        Self(if sign < 0 {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        })
    }

    #[must_use]
    pub fn is_nan(self) -> bool {
        self.0.is_nan()
    }

    #[must_use]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// ECMAScript `ToInt32`.
    #[must_use]
    pub fn to_int32(self) -> i32 {
        if !self.0.is_finite() || self.0 == 0.0 {
            return 0;
        }
        let integer = self.0.trunc() % 4_294_967_296.0;
        let unsigned = if integer < 0.0 {
            integer + 4_294_967_296.0
        } else {
            integer
        };
        unsigned.to_u32().unwrap_or(0).cast_signed()
    }

    /// ECMAScript `ToUint32`.
    #[must_use]
    pub fn to_uint32(self) -> u32 {
        self.to_int32().cast_unsigned()
    }

    #[must_use]
    pub fn signed_right_shift(self, other: Self) -> Self {
        Self(f64::from(self.to_int32() >> (other.to_uint32() & 31)))
    }

    #[must_use]
    pub fn unsigned_right_shift(self, other: Self) -> Self {
        Self(f64::from(self.to_uint32() >> (other.to_uint32() & 31)))
    }

    #[must_use]
    pub fn left_shift(self, other: Self) -> Self {
        Self(f64::from(
            self.to_int32().wrapping_shl(other.to_uint32() & 31),
        ))
    }

    #[must_use]
    pub fn bitwise_not(self) -> Self {
        Self(f64::from(!self.to_int32()))
    }

    #[must_use]
    pub fn bitwise_or(self, other: Self) -> Self {
        Self(f64::from(self.to_int32() | other.to_int32()))
    }

    #[must_use]
    pub fn bitwise_and(self, other: Self) -> Self {
        Self(f64::from(self.to_int32() & other.to_int32()))
    }

    #[must_use]
    pub fn bitwise_xor(self, other: Self) -> Self {
        Self(f64::from(self.to_int32() ^ other.to_int32()))
    }

    #[must_use]
    pub fn floor(self) -> Self {
        Self(self.0.floor())
    }

    #[must_use]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    /// ECMAScript Number remainder operation.
    #[must_use]
    pub fn remainder(self, divisor: Self) -> Self {
        match () {
            () if self.is_nan() || divisor.is_nan() || self.is_infinite() => Self::nan(),
            () if divisor.is_infinite() => self,
            () if divisor.0 == 0.0 => Self::nan(),
            () if self.0 == 0.0 => self,
            () => Self(self.0 % divisor.0),
        }
    }

    /// ECMAScript Number exponentiation operation.
    #[must_use]
    pub fn exponentiate(self, exponent: Self) -> Self {
        let is_one = self.0.to_bits() == 1.0_f64.to_bits();
        let is_negative_one = self.0.to_bits() == (-1.0_f64).to_bits();
        if (is_one || is_negative_one) && exponent.is_infinite() || is_one && exponent.is_nan() {
            return Self::nan();
        }

        let base = self.0;
        let exponent_value = exponent.0;
        if base.abs() > 1.0
            && base.to_bits() == base.trunc().to_bits()
            && exponent_value >= 0.0
            && exponent_value.to_bits() == exponent_value.trunc().to_bits()
            && exponent_value.is_finite()
            && let Some(base_integer) = base.to_i64()
            && let Some(power) = exponent_value.to_u32()
        {
            let magnitude = exponent_value * base.abs().log2();
            if magnitude > 53.0 && magnitude <= f64::MAX.log2() {
                let exact = BigInt::from(base_integer).pow(power);
                if let Some(result) = exact.to_f64() {
                    return Self(result);
                }
            }
        }
        Self(base.powf(exponent_value))
    }

    /// ECMAScript `StringToNumber` conversion.
    #[must_use]
    pub fn from_string(text: &str) -> Self {
        string_to_number(text)
    }
}

impl fmt::Display for Number {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer = ryu_js::Buffer::new();
        formatter.write_str(buffer.format(self.0))
    }
}

impl From<f64> for Number {
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl From<Number> for f64 {
    fn from(value: Number) -> Self {
        value.0
    }
}

macro_rules! arithmetic {
    ($trait:ident, $method:ident, $operator:tt) => {
        impl ops::$trait for Number {
            type Output = Self;

            fn $method(self, other: Self) -> Self {
                Self(self.0 $operator other.0)
            }
        }
    };
}

arithmetic!(Add, add, +);
arithmetic!(Sub, sub, -);
arithmetic!(Mul, mul, *);
arithmetic!(Div, div, /);

impl ops::Neg for Number {
    type Output = Self;

    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl ops::Rem for Number {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        self.remainder(other)
    }
}

fn string_to_number(text: &str) -> Number {
    let text = text.trim_matches(is_js_whitespace);
    match text {
        "" => return Number(0.0),
        "Infinity" | "+Infinity" => return Number::infinity(1),
        "-Infinity" => return Number::infinity(-1),
        _ => {}
    }
    if !text.chars().all(is_number_character) {
        return Number::nan();
    }
    if let Some(number) = parse_integer_literal(text) {
        return number;
    }

    let (unsigned, negative) = text
        .strip_prefix('-')
        .map_or((text, false), |value| (value, true));
    let unsigned = if negative {
        unsigned
    } else {
        unsigned.strip_prefix('+').unwrap_or(unsigned)
    };
    if !unsigned
        .chars()
        .next()
        .is_some_and(|character| character.is_ascii_digit() || character == '.')
    {
        return Number::nan();
    }
    let Some(value) = parse_decimal_float(unsigned) else {
        return Number::nan();
    };
    Number(if negative { -value } else { value })
}

fn parse_integer_literal(text: &str) -> Option<Number> {
    let prefix = text.get(0..2).unwrap_or_default();
    let (radix, digits, prefixed) = match prefix {
        "0b" | "0B" => (2, &text[2..], true),
        "0o" | "0O" => (8, &text[2..], true),
        "0x" | "0X" => (16, &text[2..], true),
        _ => (10, text, false),
    };
    if prefixed && (digits.is_empty() || !digits.chars().all(|character| character.is_digit(radix)))
    {
        return Some(Number::nan());
    }
    if !prefixed && !digits.chars().all(|character| character.is_ascii_digit()) {
        return None;
    }
    let digits = digits.trim_start_matches('0');
    let digits = if digits.is_empty() { "0" } else { digits };
    let integer = BigInt::parse_bytes(digits.as_bytes(), radix)?;
    Some(Number(integer.to_f64()?))
}

fn parse_decimal_float(text: &str) -> Option<f64> {
    let (mantissa, exponent) = text.find(['e', 'E']).map_or((text, None), |index| {
        (&text[..index], Some(&text[index + 1..]))
    });
    if mantissa.matches('.').count() > 1 {
        return None;
    }
    let (integer, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, None), |(integer, fraction)| {
            (integer, Some(fraction))
        });
    if integer.is_empty() && fraction.is_none_or(str::is_empty)
        || !integer.chars().all(|character| character.is_ascii_digit())
        || fraction.is_some_and(|value| !value.chars().all(|character| character.is_ascii_digit()))
    {
        return None;
    }
    if let Some(exponent) = exponent {
        let digits = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
        if digits.is_empty() || !digits.chars().all(|character| character.is_ascii_digit()) {
            return None;
        }
    }
    text.parse().ok()
}

fn is_number_character(character: char) -> bool {
    character.is_ascii_digit()
        || matches!(
            character,
            'a'..='f' | 'A'..='F' | '.' | '-' | '+' | 'x' | 'X' | 'o' | 'O'
        )
}

fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\n' | '\r'
            | '\t'
            | '\u{000b}'
            | '\u{000c}'
            | '\u{0020}'
            | '\u{00a0}'
            | '\u{1680}'
            | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

/// A decimal representation of a JavaScript bigint without requiring bigint
/// arithmetic at call sites.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PseudoBigInt {
    pub negative: bool,
    pub base10_value: String,
}

impl PseudoBigInt {
    #[must_use]
    pub fn new(value: &str, negative: bool) -> Self {
        let value = value.trim_start_matches('0').to_owned();
        Self {
            negative: negative && !value.is_empty(),
            base10_value: value,
        }
    }

    #[must_use]
    pub fn sign(&self) -> i8 {
        if self.base10_value.is_empty() {
            0
        } else if self.negative {
            -1
        } else {
            1
        }
    }

    /// Parses a scanner-validated signed bigint literal.
    #[must_use]
    pub fn parse_valid(text: &str) -> Self {
        let (text, negative) = text
            .strip_prefix('-')
            .map_or((text, false), |text| (text, true));
        Self::new(&parse_pseudo_big_int(text), negative)
    }
}

impl fmt::Display for PseudoBigInt {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.base10_value.is_empty() {
            formatter.write_str("0")
        } else if self.negative {
            write!(formatter, "-{}", self.base10_value)
        } else {
            formatter.write_str(&self.base10_value)
        }
    }
}

/// Converts a scanner-validated bigint literal to unsigned decimal text.
///
/// # Panics
///
/// Panics when a non-decimal literal is malformed.
#[must_use]
pub fn parse_pseudo_big_int(text: &str) -> String {
    let text = text.strip_suffix('n').unwrap_or(text);
    let prefix = text.get(0..2).unwrap_or_default();
    let radix = match prefix {
        "0b" | "0B" => Some(2),
        "0o" | "0O" => Some(8),
        "0x" | "0X" => Some(16),
        _ => None,
    };
    let Some(radix) = radix else {
        let value = text.trim_start_matches('0');
        return if value.is_empty() { "0" } else { value }.to_owned();
    };
    let digits = text[2..].replace('_', "");
    BigInt::parse_bytes(digits.as_bytes(), radix)
        .unwrap_or_else(|| panic!("Failed to parse big int: {text:?}"))
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER, Number, PseudoBigInt, parse_pseudo_big_int};

    fn assert_number(actual: Number, expected: Number) {
        if expected.is_nan() {
            assert!(actual.is_nan());
        } else {
            assert_eq!(actual.0.to_bits(), expected.0.to_bits());
        }
    }

    #[test]
    fn converts_to_int32_and_performs_bitwise_operations() {
        let cases = [
            (Number(0.0), 0),
            (Number::nan(), 0),
            (Number::infinity(1), 0),
            (Number(2_147_483_648.0), i32::MIN),
            (MAX_SAFE_INTEGER, -1),
            (MIN_SAFE_INTEGER, 1),
            (Number(-0.4), 0),
            (Number(f64::MAX), 0),
        ];
        for (input, expected) in cases {
            assert_eq!(input.to_int32(), expected);
        }
        assert_eq!(
            Number(f64::from(0xdead_beef_u32)).bitwise_not(),
            Number(559_038_736.0)
        );
        assert_eq!(
            Number(-1.0).unsigned_right_shift(Number(0.0)),
            Number(4_294_967_295.0)
        );
        assert_eq!(Number(1.0).left_shift(Number(33.0)), Number(2.0));
    }

    #[test]
    fn implements_remainder_and_exponentiation_special_cases() {
        assert!(Number(1.0).remainder(Number(0.0)).is_nan());
        assert!(Number::infinity(1).remainder(Number(2.0)).is_nan());
        assert_eq!(Number(2.0).remainder(Number::infinity(1)), Number(2.0));
        assert_eq!(
            Number(-0.0).remainder(Number(3.0)).0.to_bits(),
            (-0.0_f64).to_bits()
        );
        assert!(Number(-1.0).exponentiate(Number::infinity(1)).is_nan());
        assert!(Number(1.0).exponentiate(Number::nan()).is_nan());
        assert_eq!(
            Number(2.0).exponentiate(Number(60.0)),
            Number(1_152_921_504_606_846_976.0)
        );
    }

    #[test]
    fn formats_numbers_like_javascript() {
        let cases = [
            (Number::nan(), "NaN"),
            (Number::infinity(1), "Infinity"),
            (Number::infinity(-1), "-Infinity"),
            (Number(-0.0), "0"),
            (Number(std::f64::consts::PI), "3.141592653589793"),
            (Number(1e20), "100000000000000000000"),
            (Number(1e21), "1e+21"),
            (Number::from(f64::from_bits(1)), "5e-324"),
            (
                Number::from(f64::from_bits(0x000f_ffff_ffff_ffff)),
                "2.225073858507201e-308",
            ),
            (Number(-2.109_808_898_695_963e16), "-21098088986959630"),
            (Number(19_686_109_595_169_230_000.0), "19686109595169230000"),
        ];
        for (number, expected) in cases {
            assert_eq!(number.to_string(), expected);
        }
    }

    #[test]
    fn parses_javascript_number_strings() {
        let cases = [
            ("", Number(0.0)),
            ("1.", Number(1.0)),
            (".0000", Number(0.0)),
            ("  +Infinity\n", Number::infinity(1)),
            ("-.0", Number(-0.0)),
            ("0b1010", Number(10.0)),
            ("0o12", Number(10.0)),
            ("0x123456789abcdef0", Number(1_311_768_467_463_790_300.0)),
            ("1e1000", Number::infinity(1)),
            (
                "010000000000000000000",
                Number(10_000_000_000_000_000_000.0),
            ),
            ("\u{00a0}1234.56\u{feff}", Number(1234.56)),
        ];
        for (text, expected) in cases {
            assert_number(Number::from_string(text), expected);
        }
        for invalid in ["NaN", ".", "1e", "++0", "0_0", "0b2", "1.f", "\u{200b}"] {
            assert!(Number::from_string(invalid).is_nan(), "{invalid:?}");
        }
    }

    #[test]
    fn overflowing_radix_literals_convert_to_positive_infinity() {
        for (prefix, digit, count) in [("0b", '1', 1_100), ("0o", '7', 400), ("0x", 'f', 300)] {
            let literal = format!("{prefix}{}", digit.to_string().repeat(count));
            assert_eq!(Number::from_string(&literal), Number::infinity(1));
        }
    }

    #[test]
    fn handles_pseudo_bigints() {
        assert_eq!(parse_pseudo_big_int("00042n"), "42");
        assert_eq!(parse_pseudo_big_int("0b1010_0101n"), "165");
        assert_eq!(parse_pseudo_big_int("0o755n"), "493");
        assert_eq!(
            parse_pseudo_big_int("0x18ee90ff6c373e0ee4e3f0ad2n"),
            "123456789012345678901234567890"
        );
        let negative = PseudoBigInt::parse_valid("-00042n");
        assert_eq!(negative.to_string(), "-42");
        assert_eq!(negative.sign(), -1);
        assert_eq!(PseudoBigInt::new("000", true).sign(), 0);
    }
}
