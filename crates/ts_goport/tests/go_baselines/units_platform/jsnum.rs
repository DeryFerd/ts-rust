//! Go: `internal/jsnum/{jsnum,pseudobigint,string,ryu}_test.go`, run on the
//! `ts_jsnum` crate (the Number type of the goport).
//!
//! The `Node` subtests run the same inputs through Node.js, as Go does
//! (`jstest.EvalNodeScript`), and are skipped when Node.js is not found.

use std::path::Path;

use ts_jsnum::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER, Number, PseudoBigInt};

use super::Failures;
use crate::astnav_api::jstest;

// Go: jsnum_test.go:15 assertEqualNumber
fn equal_number(got: f64, want: f64) -> bool {
    if got.is_nan() || want.is_nan() {
        got.is_nan() == want.is_nan()
    } else {
        got == want
    }
}

fn check_number(failures: &mut Failures, name: &str, got: f64, want: f64) {
    if !equal_number(got, want) {
        failures.fail(name, format!("got {got:?}, want {want:?}"));
    }
}

// Go: jsnum_test.go:27 assertWithinOneULP
fn within_one_ulp(got: f64, want: f64) -> bool {
    if got.is_nan() || want.is_nan() {
        return got.is_nan() == want.is_nan();
    }
    got == want || got.to_bits().abs_diff(want.to_bits()) <= 1
}

// Go: jsnum_test.go:86 numToUint32s
fn num_to_uint32s(n: f64) -> [u32; 2] {
    let bits = n.to_bits();
    [bits as u32, (bits >> 32) as u32]
}

// Go: jsnum_test.go:91 uint32sToNum
fn uint32s_to_num(a: [u32; 2]) -> f64 {
    f64::from_bits(u64::from(a[0]) | (u64::from(a[1]) << 32))
}

const NODE_BITS: &str = r#"
		import fs from 'fs';

		function fromBits(bits) {
			const buffer = new ArrayBuffer(8);
			(new Uint32Array(buffer))[0] = bits[0];
			(new Uint32Array(buffer))[1] = bits[1];
			return new Float64Array(buffer)[0];
		}

		function toBits(number) {
			const buffer = new ArrayBuffer(8);
			(new Float64Array(buffer))[0] = number;
			return [(new Uint32Array(buffer))[0], (new Uint32Array(buffer))[1]];
		}
"#;

fn bits_json(bits: [u32; 2]) -> String {
    format!("[{},{}]", bits[0], bits[1])
}

/// Runs `script` in Node.js on the JSON `input` and returns its result.
fn eval_node<T: ts_goport::frontend::json::UnmarshalerFrom + Default>(
    script: &str,
    input: &str,
) -> T {
    let tmpdir = jstest::TempDir::new();
    let input_path = tmpdir.path().join("input.json");
    std::fs::write(&input_path, input).unwrap();
    let input_arg = input_path.to_str().unwrap();
    jstest::eval_node_script::<T>(script, Path::new(tmpdir.path()), &[input_arg]).unwrap()
}

// Go: jsnum_test.go:97 evalBinaryOp
// PORT: the Node script returns only the result bits; Go also echoes x and y.
fn eval_binary_op(op: &str, xs: &[f64], ys: &[f64]) -> Vec<f64> {
    let input: Vec<String> = xs
        .iter()
        .zip(ys)
        .map(|(x, y)| {
            format!(
                r#"{{"x":{},"y":{}}}"#,
                bits_json(num_to_uint32s(*x)),
                bits_json(num_to_uint32s(*y))
            )
        })
        .collect();
    let script = format!(
        r#"{NODE_BITS}
		export default function(inputFile) {{
			const input = JSON.parse(fs.readFileSync(inputFile, 'utf8'));
			return input.map(({{x, y}}) => {{
				const a = fromBits(x);
				const b = fromBits(y);
				return toBits({op});
			}});
		}};
	"#
    );
    let results: Vec<[u32; 2]> = eval_node(&script, &format!("[{}]", input.join(",")));
    assert_eq!(results.len(), xs.len());
    results.into_iter().map(uint32s_to_num).collect()
}

// Go: jsnum_test.go:150 evalUnaryOp
fn eval_unary_op(op: &str, xs: &[f64]) -> Vec<f64> {
    let input: Vec<String> = xs
        .iter()
        .map(|x| format!(r#"{{"x":{}}}"#, bits_json(num_to_uint32s(*x))))
        .collect();
    let script = format!(
        r#"{NODE_BITS}
		export default function(inputFile) {{
			const input = JSON.parse(fs.readFileSync(inputFile, 'utf8'));
			return input.map(({{x}}) => {{
				const a = fromBits(x);
				return toBits({op});
			}});
		}};
	"#
    );
    let results: Vec<[u32; 2]> = eval_node(&script, &format!("[{}]", input.join(",")));
    assert_eq!(results.len(), xs.len());
    results.into_iter().map(uint32s_to_num).collect()
}

// Go: jsnum_test.go:203 toInt32Tests
fn to_int32_tests() -> Vec<(&'static str, f64, i32)> {
    let max_safe = MAX_SAFE_INTEGER.0;
    let min_safe = MIN_SAFE_INTEGER.0;
    vec![
        ("0.0", 0.0, 0),
        ("-0.0", -0.0, 0),
        ("NaN", f64::NAN, 0),
        ("+Inf", f64::INFINITY, 0),
        ("-Inf", f64::NEG_INFINITY, 0),
        ("MaxInt32", f64::from(i32::MAX), i32::MAX),
        ("MaxInt32+1", (i64::from(i32::MAX) + 1) as f64, i32::MIN),
        ("MinInt32", f64::from(i32::MIN), i32::MIN),
        ("MinInt32-1", (i64::from(i32::MIN) - 1) as f64, i32::MAX),
        ("MIN_SAFE_INTEGER", min_safe, 1),
        ("MIN_SAFE_INTEGER-1", min_safe - 1.0, 0),
        ("MIN_SAFE_INTEGER+1", min_safe + 1.0, 2),
        ("MAX_SAFE_INTEGER", max_safe, -1),
        ("MAX_SAFE_INTEGER-1", max_safe - 1.0, -2),
        ("MAX_SAFE_INTEGER+1", max_safe + 1.0, 0),
        ("-8589934590", -8589934590.0, 2),
        ("0xDEADBEEF", 0xDEADBEEF_u32 as f64, -559038737),
        ("4294967808", 4294967808.0, 512),
        ("-0.4", -0.4, 0),
        ("SmallestNonzeroFloat64", f64::from_bits(1), 0),
        ("-SmallestNonzeroFloat64", -f64::from_bits(1), 0),
        ("MaxFloat64", f64::MAX, 0),
        ("-MaxFloat64", -f64::MAX, 0),
        (
            "Largest subnormal number",
            f64::from_bits(0x000FFFFFFFFFFFFF),
            0,
        ),
        (
            "Smallest positive normal number",
            f64::from_bits(0x0010000000000000),
            0,
        ),
        ("Largest normal number", f64::MAX, 0),
        ("-Largest normal number", -f64::MAX, 0),
        ("1.0", 1.0, 1),
        ("-1.0", -1.0, -1),
        ("1e308", 1e308, 0),
        ("-1e308", -1e308, 0),
        ("math.Pi", std::f64::consts::PI, 3),
        ("-math.Pi", -std::f64::consts::PI, -3),
        ("math.E", std::f64::consts::E, 2),
        ("-math.E", -std::f64::consts::E, -2),
        ("0.5", 0.5, 0),
        ("-0.5", -0.5, 0),
        ("0.49999999999999994", 0.49999999999999994, 0),
        ("-0.49999999999999994", -0.49999999999999994, 0),
        ("0.5000000000000001", 0.5000000000000001, 0),
        ("-0.5000000000000001", -0.5000000000000001, 0),
        ("2^31 + 0.5", 2147483648.5, -2147483648),
        ("-2^31 - 0.5", -2147483648.5, -2147483648),
        ("2^40", 1099511627776.0, 0),
        ("-2^40", -1099511627776.0, 0),
        ("TypeFlagsNarrowable", 536624127.0, 536624127),
    ]
}

// Go: jsnum_test.go:252 TestToInt32
#[test]
fn test_to_int32() {
    let tests = to_int32_tests();
    let mut failures = Failures::new("TestToInt32");
    for (name, input, want) in &tests {
        failures.check_eq(
            &format!("{name} ({input})"),
            Number(*input).to_int32(),
            *want,
        );
    }
    if !jstest::skip_if_no_node_js("TestToInt32/Node") {
        let inputs: Vec<f64> = tests.iter().map(|t| t.1).collect();
        let zeros = vec![0.0; tests.len()];
        let js_results = eval_binary_op("a | b", &inputs, &zeros);
        for (i, (name, input, _)) in tests.iter().enumerate() {
            let got = f64::from(Number(*input).to_int32());
            check_number(
                &mut failures,
                &format!("Node/{name} ({input})"),
                got,
                js_results[i],
            );
        }
    }
    failures.finish();
}

/// Go tests of a binary op: rows `(x, y, want)`; `op` names the Node
/// expression; `f` is the Rust op.
fn check_binary(
    test: &str,
    op: &str,
    tests: &[(f64, f64, f64)],
    f: impl Fn(Number, Number) -> Number,
    node_check: fn(f64, f64) -> bool,
) {
    let mut failures = Failures::new(test);
    for (x, y, want) in tests {
        let got = f(Number(*x), Number(*y)).0;
        check_number(&mut failures, &format!("{x} {op} {y}"), got, *want);
    }
    if !jstest::skip_if_no_node_js(&format!("{test}/Node")) {
        let xs: Vec<f64> = tests.iter().map(|t| t.0).collect();
        let ys: Vec<f64> = tests.iter().map(|t| t.1).collect();
        let js_results = eval_binary_op(&format!("a {op} b"), &xs, &ys);
        for (i, (x, y, _)) in tests.iter().enumerate() {
            let got = f(Number(*x), Number(*y)).0;
            if !node_check(got, js_results[i]) {
                failures.fail(
                    &format!("Node/{x} {op} {y}"),
                    format!("got {got:?}, node {:?}", js_results[i]),
                );
            }
        }
    }
    failures.finish();
}

// Go: jsnum_test.go:291 TestBitwiseNOT
#[test]
fn test_bitwise_not() {
    let tests: &[(f64, f64)] = &[
        (-2147483649.0, -2147483648.0),
        (2147483647.0, -2147483648.0),
        (-4294967296.0, -1.0),
        (0.0, -1.0),
        (2147483648.0, 2147483647.0),
        (-2147483648.0, 2147483647.0),
        (4294967296.0, -1.0),
    ];
    let mut failures = Failures::new("TestBitwiseNOT");
    for (x, want) in tests {
        check_number(
            &mut failures,
            &format!("~{x}"),
            Number(*x).bitwise_not().0,
            *want,
        );
    }
    if !jstest::skip_if_no_node_js("TestBitwiseNOT/Node") {
        let xs: Vec<f64> = tests.iter().map(|t| t.0).collect();
        let js_results = eval_unary_op("~a", &xs);
        for (i, (x, _)) in tests.iter().enumerate() {
            let got = Number(*x).bitwise_not().0;
            check_number(&mut failures, &format!("Node/~{x}"), got, js_results[i]);
        }
    }
    failures.finish();
}

// Go: jsnum_test.go:333 TestBitwiseAND
#[test]
fn test_bitwise_and() {
    let tests = &[
        (0.0, 0.0, 0.0),
        (0.0, 1.0, 0.0),
        (1.0, 0.0, 0.0),
        (1.0, 1.0, 1.0),
    ];
    check_binary(
        "TestBitwiseAND",
        "&",
        tests,
        Number::bitwise_and,
        equal_number,
    );
}

// Go: jsnum_test.go:374 TestBitwiseOR
#[test]
fn test_bitwise_or() {
    let tests = &[
        (0.0, 0.0, 0.0),
        (0.0, 1.0, 1.0),
        (1.0, 0.0, 1.0),
        (1.0, 1.0, 1.0),
    ];
    check_binary(
        "TestBitwiseOR",
        "|",
        tests,
        Number::bitwise_or,
        equal_number,
    );
}

// Go: jsnum_test.go:415 TestBitwiseXOR
#[test]
fn test_bitwise_xor() {
    let tests = &[
        (0.0, 0.0, 0.0),
        (0.0, 1.0, 1.0),
        (1.0, 0.0, 1.0),
        (1.0, 1.0, 0.0),
    ];
    check_binary(
        "TestBitwiseXOR",
        "^",
        tests,
        Number::bitwise_xor,
        equal_number,
    );
}

// Go: jsnum_test.go:456 TestSignedRightShift
#[test]
fn test_signed_right_shift() {
    let tests = &[
        (1.0, 0.0, 1.0),
        (1.0, 1.0, 0.0),
        (1.0, 2.0, 0.0),
        (1.0, 31.0, 0.0),
        (1.0, 32.0, 1.0),
        (-4.0, 0.0, -4.0),
        (-4.0, 1.0, -2.0),
        (-4.0, 2.0, -1.0),
        (-4.0, 3.0, -1.0),
        (-4.0, 4.0, -1.0),
        (-4.0, 31.0, -1.0),
        (-4.0, 32.0, -4.0),
        (-4.0, 33.0, -2.0),
    ];
    check_binary(
        "TestSignedRightShift",
        ">>",
        tests,
        Number::signed_right_shift,
        equal_number,
    );
}

// Go: jsnum_test.go:500 TestUnsignedRightShift
#[test]
fn test_unsigned_right_shift() {
    let tests = &[
        (1.0, 0.0, 1.0),
        (1.0, 1.0, 0.0),
        (1.0, 2.0, 0.0),
        (1.0, 31.0, 0.0),
        (1.0, 32.0, 1.0),
        (-4.0, 0.0, 4294967292.0),
        (-4.0, 1.0, 2147483646.0),
        (-4.0, 2.0, 1073741823.0),
        (-4.0, 3.0, 536870911.0),
        (-4.0, 4.0, 268435455.0),
        (-4.0, 31.0, 1.0),
        (-4.0, 32.0, 4294967292.0),
        (-4.0, 33.0, 2147483646.0),
    ];
    check_binary(
        "TestUnsignedRightShift",
        ">>>",
        tests,
        Number::unsigned_right_shift,
        equal_number,
    );
}

// Go: jsnum_test.go:544 TestLeftShift
#[test]
fn test_left_shift() {
    let tests = &[
        (1.0, 0.0, 1.0),
        (1.0, 1.0, 2.0),
        (1.0, 2.0, 4.0),
        (1.0, 31.0, -2147483648.0),
        (1.0, 32.0, 1.0),
        (-4.0, 0.0, -4.0),
        (-4.0, 1.0, -8.0),
        (-4.0, 2.0, -16.0),
        (-4.0, 3.0, -32.0),
        (-4.0, 31.0, 0.0),
        (-4.0, 32.0, -4.0),
    ];
    check_binary(
        "TestLeftShift",
        "<<",
        tests,
        Number::left_shift,
        equal_number,
    );
}

// Go: jsnum_test.go:586 TestRemainder
// PORT: Go `math.Mod` and Rust `%` on f64 are both the exact IEEE fmod.
#[test]
fn test_remainder() {
    let nan = f64::NAN;
    let inf = f64::INFINITY;
    let tests = &[
        (nan, 1.0, nan),
        (1.0, nan, nan),
        (inf, 1.0, nan),
        (-inf, 1.0, nan),
        (123.0, inf, 123.0),
        (123.0, -inf, 123.0),
        (123.0, 0.0, nan),
        (123.0, -0.0, nan),
        (0.0, 123.0, 0.0),
        (-0.0, 123.0, -0.0),
        (10.0, 3.0, 1.0),
        (-10.0, 3.0, -1.0),
        (10.0, -3.0, 1.0),
        (-10.0, -3.0, -1.0),
        (5.5, 2.0, 1.5),
        (-5.5, 2.0, -1.5),
        (1.0, 0.5, 0.0),
        (-1.0, 0.5, -0.0),
        (1.5, 1.0, 0.5),
        (-1.5, 1.0, -0.5),
        (7.0, 0.1, 7.0_f64 % 0.1),
        (7.0, 0.2, 7.0_f64 % 0.2),
        (7.0, 0.3, 7.0_f64 % 0.3),
        (100.0, 0.3, 100.0_f64 % 0.3),
    ];
    check_binary("TestRemainder", "%", tests, Number::remainder, equal_number);
}

// Go: jsnum_test.go:640 TestExponentiate
#[test]
fn test_exponentiate() {
    let nan = f64::NAN;
    let inf = f64::INFINITY;
    let tests = &[
        (2.0, 3.0, 8.0),
        (inf, 3.0, inf),
        (inf, -5.0, 0.0),
        (-inf, 3.0, -inf),
        (-inf, 4.0, inf),
        (-inf, -3.0, -0.0),
        (-inf, -4.0, 0.0),
        (0.0, 3.0, 0.0),
        (0.0, -10.0, inf),
        (-0.0, 3.0, -0.0),
        (-0.0, 4.0, 0.0),
        (-0.0, -3.0, -inf),
        (-0.0, -4.0, inf),
        (3.0, inf, inf),
        (-3.0, inf, inf),
        (3.0, -inf, 0.0),
        (-3.0, -inf, 0.0),
        (nan, 3.0, nan),
        (1.0, inf, nan),
        (1.0, -inf, nan),
        (-1.0, inf, nan),
        (-1.0, -inf, nan),
        (1.0, nan, nan),
        (10.0, 308.0, f64::from_bits(0x7fe1ccf385ebc8a0)),
        (5.0, 210.0, f64::from_bits(0x5e68557f31326bbb)),
        (10.0, 200.0, f64::from_bits(0x6974e718d7d7625a)),
    ];
    // The Node check allows 1 ULP, as Go does.
    check_binary(
        "TestExponentiate",
        "**",
        tests,
        Number::exponentiate,
        within_one_ulp,
    );
}

// Go: pseudobigint_test.go:10 TestParsePseudoBigInt
#[test]
fn test_parse_pseudo_big_int() {
    let mut test_numbers: Vec<Number> = (0..1000).map(|i| Number(f64::from(i))).collect();
    for bits in 0..53 {
        test_numbers.push(Number((1_i64 << bits) as f64));
        test_numbers.push(Number(((1_i64 << bits) - 1) as f64));
    }

    let mut failures = Failures::new("TestParsePseudoBigInt");
    // strip base-10 strings
    for test_number in &test_numbers {
        for leading_zeros in 0..10 {
            let lit = format!("{}{}n", "0".repeat(leading_zeros), test_number);
            failures.check_eq(
                "strip base-10 strings",
                ts_jsnum::parse_pseudo_big_int(&lit),
                test_number.to_string(),
            );
        }
    }

    // parse non-decimal bases (small numbers)
    let cases = [
        ("0b0n", "0"),
        ("0b1n", "1"),
        ("0b1010n", "10"),
        ("0b1010_0101n", "165"),
        ("0B1101n", "13"),
        ("0o0n", "0"),
        ("0o7n", "7"),
        ("0o755n", "493"),
        ("0o7_5_5n", "493"),
        ("0O12n", "10"),
        ("0x0n", "0"),
        ("0xFn", "15"),
        ("0xFFn", "255"),
        ("0xF_Fn", "255"),
        ("0X1Fn", "31"),
    ];
    for (lit, out) in cases {
        failures.check_eq(
            &format!("parse non-decimal bases {lit:?}"),
            ts_jsnum::parse_pseudo_big_int(lit),
            out.to_string(),
        );
    }

    // can parse large literals
    let want = "123456789012345678901234567890";
    for lit in [
        "123456789012345678901234567890n",
        "0b1100011101110100100001111111101101100001101110011111000001110111001001110001111110000101011010010n",
        "0o143564417755415637016711617605322n",
        "0x18ee90ff6c373e0ee4e3f0ad2n",
    ] {
        failures.check_eq(
            &format!("can parse large literals {lit}"),
            ts_jsnum::parse_pseudo_big_int(lit),
            want.to_string(),
        );
    }
    failures.finish();
    // Keep the PseudoBigInt type in use: Go ParsePseudoBigInt feeds it.
    let _ = PseudoBigInt::parse_valid("1n");
}

// Go: ryu_test.go:22 ieeeParts2Double
fn ieee_parts2double(sign: bool, ieee_exponent: u32, ieee_mantissa: u64) -> f64 {
    assert!(ieee_exponent <= 2047, "ieeeExponent > 2047");
    assert!(ieee_mantissa <= MAX_MANTISSA, "ieeeMantissa > maxMantissa");
    let sign_bit = u64::from(sign);
    f64::from_bits((sign_bit << 63) | (u64::from(ieee_exponent) << 52) | ieee_mantissa)
}

// Go: ryu_test.go:37 maxMantissa
const MAX_MANTISSA: u64 = (1 << 53) - 1;

// Go: string_test.go:22 stringTests
fn string_tests() -> Vec<(f64, &'static str)> {
    let mut tests = vec![
        (f64::NAN, "NaN"),
        (f64::INFINITY, "Infinity"),
        (f64::NEG_INFINITY, "-Infinity"),
        (0.0, "0"),
        (-0.0, "0"),
        (1.0, "1"),
        (-1.0, "-1"),
        (0.3, "0.3"),
        (-0.3, "-0.3"),
        (1.5, "1.5"),
        (-1.5, "-1.5"),
        (1e308, "1e+308"),
        (-1e308, "-1e+308"),
        (std::f64::consts::PI, "3.141592653589793"),
        (-std::f64::consts::PI, "-3.141592653589793"),
        (MAX_SAFE_INTEGER.0, "9007199254740991"),
        (MIN_SAFE_INTEGER.0, "-9007199254740991"),
        (f64::from_bits(0x000FFFFFFFFFFFFF), "2.225073858507201e-308"),
        (
            f64::from_bits(0x0010000000000000),
            "2.2250738585072014e-308",
        ),
        (1234567.8, "1234567.8"),
        (19686109595169230000.0, "19686109595169230000"),
        (123.456, "123.456"),
        (-123.456, "-123.456"),
        (444123.0, "444123"),
        (-444123.0, "-444123"),
        (444123.789123456789875436, "444123.7891234568"),
        (-444123.78963636363636363636, "-444123.7896363636"),
        (1e21, "1e+21"),
        (1e20, "100000000000000000000"),
    ];
    tests.extend(ryu_tests());
    tests
}

// Go: ryu_test.go:39 ryuTests
fn ryu_tests() -> Vec<(f64, &'static str)> {
    vec![
        (2.2250738585072014e-308, "2.2250738585072014e-308"),
        (
            f64::from_bits(0x7fefffffffffffff),
            "1.7976931348623157e+308",
        ),
        (f64::from_bits(1), "5e-324"),
        (2.98023223876953125e-8, "2.9802322387695312e-8"),
        (-2.109808898695963e16, "-21098088986959630"),
        (4.940656e-318, "4.940656e-318"),
        (1.18575755e-316, "1.18575755e-316"),
        (2.989102097996e-312, "2.989102097996e-312"),
        (9.0608011534336e15, "9060801153433600"),
        (4.708356024711512e18, "4708356024711512000"),
        (9.409340012568248e18, "9409340012568248000"),
        (1.2345678, "1.2345678"),
        (f64::from_bits(0x4830F0CF064DD592), "5.764607523034235e+39"),
        (f64::from_bits(0x4840F0CF064DD592), "1.152921504606847e+40"),
        (f64::from_bits(0x4850F0CF064DD592), "2.305843009213694e+40"),
        (1.2, "1.2"),
        (1.23, "1.23"),
        (1.234, "1.234"),
        (1.2345, "1.2345"),
        (1.23456, "1.23456"),
        (1.234567, "1.234567"),
        (1.2345678, "1.2345678"),
        (1.23456789, "1.23456789"),
        (1.234567895, "1.234567895"),
        (1.2345678901, "1.2345678901"),
        (1.23456789012, "1.23456789012"),
        (1.234567890123, "1.234567890123"),
        (1.2345678901234, "1.2345678901234"),
        (1.23456789012345, "1.23456789012345"),
        (1.234567890123456, "1.234567890123456"),
        (1.2345678901234567, "1.2345678901234567"),
        (4.294967294, "4.294967294"),
        (4.294967295, "4.294967295"),
        (4.294967296, "4.294967296"),
        (4.294967297, "4.294967297"),
        (4.294967298, "4.294967298"),
        (ieee_parts2double(false, 4, 0), "1.7800590868057611e-307"),
        (
            ieee_parts2double(false, 6, MAX_MANTISSA),
            "2.8480945388892175e-306",
        ),
        (ieee_parts2double(false, 41, 0), "2.446494580089078e-296"),
        (
            ieee_parts2double(false, 40, MAX_MANTISSA),
            "4.8929891601781557e-296",
        ),
        (ieee_parts2double(false, 1077, 0), "18014398509481984"),
        (
            ieee_parts2double(false, 1076, MAX_MANTISSA),
            "36028797018963964",
        ),
        (ieee_parts2double(false, 307, 0), "2.900835519859558e-216"),
        (
            ieee_parts2double(false, 306, MAX_MANTISSA),
            "5.801671039719115e-216",
        ),
        (
            ieee_parts2double(false, 934, 0x000FA7161A4D6E0C),
            "3.196104012172126e-27",
        ),
        (9007199254740991.0, "9007199254740991"),
        (9007199254740992.0, "9007199254740992"),
        (1.0e+0, "1"),
        (1.2e+1, "12"),
        (1.23e+2, "123"),
        (1.234e+3, "1234"),
        (1.2345e+4, "12345"),
        (1.23456e+5, "123456"),
        (1.234567e+6, "1234567"),
        (1.2345678e+7, "12345678"),
        (1.23456789e+8, "123456789"),
        (1.23456789e+9, "1234567890"),
        (1.234567895e+9, "1234567895"),
        (1.2345678901e+10, "12345678901"),
        (1.23456789012e+11, "123456789012"),
        (1.234567890123e+12, "1234567890123"),
        (1.2345678901234e+13, "12345678901234"),
        (1.23456789012345e+14, "123456789012345"),
        (1.234567890123456e+15, "1234567890123456"),
        (1.0e+0, "1"),
        (1.0e+1, "10"),
        (1.0e+2, "100"),
        (1.0e+3, "1000"),
        (1.0e+4, "10000"),
        (1.0e+5, "100000"),
        (1.0e+6, "1000000"),
        (1.0e+7, "10000000"),
        (1.0e+8, "100000000"),
        (1.0e+9, "1000000000"),
        (1.0e+10, "10000000000"),
        (1.0e+11, "100000000000"),
        (1.0e+12, "1000000000000"),
        (1.0e+13, "10000000000000"),
        (1.0e+14, "100000000000000"),
        (1.0e+15, "1000000000000000"),
        (1000000000000001.0, "1000000000000001"),
        (1000000000000010.0, "1000000000000010"),
        (1000000000000100.0, "1000000000000100"),
        (1000000000001000.0, "1000000000001000"),
        (1000000000010000.0, "1000000000010000"),
        (1000000000100000.0, "1000000000100000"),
        (1000000001000000.0, "1000000001000000"),
        (1000000010000000.0, "1000000010000000"),
        (1000000100000000.0, "1000000100000000"),
        (1000001000000000.0, "1000001000000000"),
        (1000010000000000.0, "1000010000000000"),
        (1000100000000000.0, "1000100000000000"),
        (1001000000000000.0, "1001000000000000"),
        (1010000000000000.0, "1010000000000000"),
        (1100000000000000.0, "1100000000000000"),
        (8.0, "8"),
        (64.0, "64"),
        (512.0, "512"),
        (8192.0, "8192"),
        (65536.0, "65536"),
        (524288.0, "524288"),
        (8388608.0, "8388608"),
        (67108864.0, "67108864"),
        (536870912.0, "536870912"),
        (8589934592.0, "8589934592"),
        (68719476736.0, "68719476736"),
        (549755813888.0, "549755813888"),
        (8796093022208.0, "8796093022208"),
        (70368744177664.0, "70368744177664"),
        (562949953421312.0, "562949953421312"),
        (9007199254740992.0, "9007199254740992"),
        (8.0e+3, "8000"),
        (64.0e+3, "64000"),
        (512.0e+3, "512000"),
        (8192.0e+3, "8192000"),
        (65536.0e+3, "65536000"),
        (524288.0e+3, "524288000"),
        (8388608.0e+3, "8388608000"),
        (67108864.0e+3, "67108864000"),
        (536870912.0e+3, "536870912000"),
        (8589934592.0e+3, "8589934592000"),
        (68719476736.0e+3, "68719476736000"),
        (549755813888.0e+3, "549755813888000"),
        (8796093022208.0e+3, "8796093022208000"),
    ]
}

// Go: string_test.go:66 fromStringTests
fn from_string_tests() -> Vec<(f64, &'static str)> {
    vec![
        (f64::NAN, "    NaN"),
        (f64::INFINITY, "Infinity    "),
        (f64::NEG_INFINITY, "    -Infinity"),
        (1.0, "1."),
        (1.0, "1.0   "),
        (1.0, "+1"),
        (1.0, "+1."),
        (1.0, "+1.0"),
        (f64::NAN, "whoops"),
        (0.0, ""),
        (0.0, "0"),
        (0.0, "0."),
        (0.0, "0.0"),
        (0.0, "0.0000"),
        (0.0, ".0000"),
        (-0.0, "-0"),
        (-0.0, "-0."),
        (-0.0, "-0.0"),
        (-0.0, "-.0"),
        (f64::NAN, "."),
        (f64::NAN, "e"),
        (f64::NAN, ".e"),
        (f64::NAN, "+"),
        (0.0, "0X0"),
        (f64::NAN, "e0"),
        (f64::NAN, "E0"),
        (f64::NAN, "1e"),
        (f64::NAN, "1e+"),
        (f64::NAN, "1e-"),
        (1.0, "1e+0"),
        (f64::NAN, "++0"),
        (f64::NAN, "0_0"),
        (f64::INFINITY, "1e1000"),
        (f64::NEG_INFINITY, "-1e1000"),
        (0.0, ".0e0"),
        (f64::NAN, "0e++0"),
        (10.0, "0XA"),
        ((0b1010_u128 as f64), "0b1010"),
        ((0b1010_u128 as f64), "0B1010"),
        ((0o12_u128 as f64), "0o12"),
        ((0o12_u128 as f64), "0O12"),
        ((0x123456789abcdef0_u128 as f64), "0x123456789abcdef0"),
        ((0x123456789abcdef0_u128 as f64), "0X123456789ABCDEF0"),
        (18446744073709552000.0, "0X10000000000000000"),
        (18446744073709597000.0, "0X1000000000000A801"),
        (f64::NAN, "0B0.0"),
        (
            1.231235345083403e+91,
            "12312353450834030486384068034683603046834603806830644850340602384608368034634603680348603864",
        ),
        (
            f64::NAN,
            "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX8OOOOOOOOOOOOOOOOOOO",
        ),
        (f64::INFINITY, "+Infinity"),
        (1234.56, "  \t1234.56  "),
        (f64::NAN, "\u{200b}"),
        (0.0, " "),
        (0.0, "\n"),
        (0.0, "\r"),
        (0.0, "\r\n"),
        (0.0, "\u{2028}"),
        (0.0, "\u{2029}"),
        (0.0, "\t"),
        (0.0, "\u{000b}"),
        (0.0, "\u{000c}"),
        (0.0, "\u{FEFF}"),
        (0.0, "\u{00A0}"),
        (10000000000000000000.0, "010000000000000000000"),
        (f64::NAN, "0x1.fffffffffffffp1023"),
        (f64::NAN, "0X_1FFFP-16"),
        (f64::NAN, "1_000"),
        (0.0, "0x0"),
        (0.0, "0X0"),
        (f64::NAN, "0xOOPS"),
        ((0xABCDEF_u128 as f64), "0xABCDEF"),
        ((0xABCDEF_u128 as f64), "0xABCDEF"),
        (0.0, "0o0"),
        (0.0, "0O0"),
        (f64::NAN, "0o8"),
        (f64::NAN, "0O8"),
        ((0o12345_u128 as f64), "0o12345"),
        ((0o12345_u128 as f64), "0O12345"),
        (0.0, "0b0"),
        (0.0, "0B0"),
        (f64::NAN, "0b2"),
        (f64::NAN, "0b2"),
        ((0b10101_u128 as f64), "0b10101"),
        ((0b10101_u128 as f64), "0B10101"),
        (f64::NAN, "1.f"),
        (f64::NAN, "1.e"),
        (f64::NAN, "1.0ef"),
        (f64::NAN, "1.0e"),
        (f64::NAN, ".f"),
        (f64::NAN, ".e"),
        (f64::NAN, ".0ef"),
        (f64::NAN, ".0e"),
        (f64::NAN, "a.f"),
        (f64::NAN, "a.e"),
        (f64::NAN, "a.0ef"),
        (f64::NAN, "a.0e"),
    ]
}

// Go: string_test.go:54 TestString
#[test]
fn test_string() {
    let mut failures = Failures::new("TestString");
    for (number, s) in string_tests() {
        failures.check_eq(
            &format!("{number:?}"),
            Number(number).to_string(),
            s.to_string(),
        );
    }
    failures.finish();
}

// Go: string_test.go:189 TestFromString
#[test]
fn test_from_string() {
    let mut failures = Failures::new("TestFromString");
    for (number, s) in string_tests() {
        let name = format!("stringTests/{s}");
        check_number(&mut failures, &name, ts_jsnum::from_string(s).0, number);
        check_number(
            &mut failures,
            &name,
            ts_jsnum::from_string(&format!("{s} ")).0,
            number,
        );
        check_number(
            &mut failures,
            &name,
            ts_jsnum::from_string(&format!(" {s}")).0,
            number,
        );
    }
    for (number, s) in from_string_tests() {
        let name = format!("fromStringTests/{s:?}");
        check_number(&mut failures, &name, ts_jsnum::from_string(s).0, number);
    }
    failures.finish();
}

// Go: string_test.go:214 TestStringRoundtrip
#[test]
fn test_string_roundtrip() {
    let mut failures = Failures::new("TestStringRoundtrip");
    for (_, s) in string_tests() {
        failures.check_eq(s, ts_jsnum::from_string(s).to_string(), s.to_string());
    }
    failures.finish();
}

// Go: string_test.go:302 getStringResultsFromJS
// PORT: the Node script returns `[str, lo, hi]` string triples.
fn get_string_results_from_js(tests: &[(f64, &str)]) -> Vec<(f64, String)> {
    let input: Vec<String> = tests
        .iter()
        .map(|(number, s)| {
            format!(
                r#"{{"bits":{},"str":{}}}"#,
                bits_json(num_to_uint32s(*number)),
                json_string(s)
            )
        })
        .collect();
    let script = format!(
        r#"{NODE_BITS}
		export default function(inputFile) {{
			const input = JSON.parse(fs.readFileSync(inputFile, 'utf8'));
			return input.map((input) => {{
				const bits = toBits(+input.str);
				return [""+fromBits(input.bits), String(bits[0]), String(bits[1])];
			}});
		}};
	"#
    );
    let results: Vec<Vec<String>> = eval_node(&script, &format!("[{}]", input.join(",")));
    assert_eq!(results.len(), tests.len());
    results
        .into_iter()
        .map(|r| {
            let bits = [r[1].parse().unwrap(), r[2].parse().unwrap()];
            (uint32s_to_num(bits), r[0].clone())
        })
        .collect()
}

fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 || c == '\u{2028}' || c == '\u{2029}' => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// Go: string_test.go:225 TestStringJS
#[test]
fn test_string_js() {
    if jstest::skip_if_no_node_js("TestStringJS") {
        return;
    }
    let mut failures = Failures::new("TestStringJS");
    let string_tests = string_tests();
    let results = get_string_results_from_js(&string_tests);
    for (i, (number, s)) in string_tests.iter().enumerate() {
        let name = format!("stringTests/{number:?}");
        check_number(&mut failures, &name, results[i].0, *number);
        failures.check_eq(&name, results[i].1.as_str(), *s);
    }
    let from_string_tests = from_string_tests();
    let results = get_string_results_from_js(&from_string_tests);
    for (i, (number, s)) in from_string_tests.iter().enumerate() {
        check_number(
            &mut failures,
            &format!("fromString {s:?}"),
            results[i].0,
            *number,
        );
    }
    failures.finish();
}
