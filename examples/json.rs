extern crate bad_parsers;

use std::collections::HashMap;
use std::str::FromStr;

use bad_parsers::{Tokens, Parser, ParseError, lazy, span_string_char, string, token, token_satisfies, first_of};

// JSON is being parsed according to the grammar at: https://www.json.org/json-en.html

#[allow(dead_code)]
#[derive(Debug, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Array(Vec<Json>),
    Object(HashMap<String, Json>),
}

macro_rules! impl_json_from {
    ($t:ty, $i:ident) => {
        impl From<$t> for Json {
            fn from(value: $t) -> Self {
                Json::$i(value)
            }
        }
    };
}

impl_json_from!(bool, Bool);
impl_json_from!(i64, Int);
impl_json_from!(f64, Float);
impl_json_from!(String, String);
impl_json_from!(Vec<Json>, Array);
impl_json_from!(HashMap<String, Json>, Object);

fn json_null<'a>() -> impl Parser<'a, &'a str, char, Json> {
    // map instead of replace saves implementing clone for Json
    string("null").map(|_| Json::Null)
}

fn json_bool<'a>() -> impl Parser<'a, &'a str, char, Json> {
    string("true")
        .replace(true)
        .or(string("false").replace(false))
        .convert()
}

fn digits<'a>() -> impl Parser<'a, &'a str, char, &'a str> {
    span_string_char(char::is_ascii_digit)
}

// int body must:
// only contain 0-9
// be non-empty
// be exactly "0" OR not start with '0'
// returns: (sign found, body)
fn integer<'a>() -> impl Parser<'a, &'a str, char, (bool, &'a str)> {
    token('-')
        .optional()
        .map(|opt| opt.is_some())
        .plus(digits().ensure(|s| !s.is_empty() && (*s == "0" || !s.starts_with('0'))))
}

fn fraction<'a>() -> impl Parser<'a, &'a str, char, Option<&'a str>> {
    token('.').right(digits()).optional()
}

fn exponent<'a>() -> impl Parser<'a, &'a str, char, (bool, &'a str)> {
    let sign = token('-').or(token('+')).optional().map(|s| Some('-') == s);
    token('e').or(token('E'))
        .right(sign)
        .plus(digits())
}

// returns Int and Float Json variants
fn json_number<'a>() -> impl Parser<'a, &'a str, char, Json> {
    let p = integer().plus(fraction()).plus(exponent().optional());
    move |input: &'a str| {
        let (inp, (((sign, i_body), frac), exp)) = p.parse(input)?;
        
        // Implementation choice: if the string contains a fraction component AND/OR
        // an exponent component, it is treated as a float
        if frac.is_some() || exp.is_some() {
            let exp_str = if let Some((exp_sign, exp_digits)) = exp {
                format!("e{}{}",
                    if exp_sign { "-" } else { "" },
                    exp_digits
                )
            } else {
                "".to_string()
            };
            let full_string = format!("{}{}.{}{}",
                if sign { "-" } else { "" },
                i_body,
                if let Some(frac_digits) = frac { frac_digits } else { "0" },
                exp_str,
            );
            // i promise this isn't cheating
            match f64::from_str(&full_string) {
                Ok(f) => Ok((inp, Json::Float(f))),
                Err(parse_float_error) => {
                    let mut e = ParseError::other(parse_float_error, inp);
                    e.set_details(&format!(
                        "successfully parsed the float ({}), but the type conversion failed",
                        full_string
                    ));
                    return Err(e);
                }
            }
        } else {
            let full_string = format!("{}{}",
                if sign { "-" } else { "" },
                i_body
            );
            // i still promise this isn't cheating
            match i64::from_str(&full_string) {
                Ok(i) => Ok((inp, Json::Int(i))),
                Err(parse_int_error) => {
                    let mut e = ParseError::other(parse_int_error, inp);
                    e.set_details(&format!(
                        "successfully parsed the int ({}), but the type conversion failed",
                        full_string
                    ));
                    return Err(e);
                }
            }
        }
    }
}

fn extract_codepoint(text: &str) -> Option<(&str, char)> {
    let (point_text, rest) = text.split_at_checked(4)?;
    // note: from_str_radix(_, 16) allows for mixed-case hex literals,
    // so no upper/lower case conversion is required
    let u = u32::from_str_radix(point_text, 16).ok()?;
    let c = char::try_from(u).ok()?;
    Some((rest, c))
}

fn string_char<'a>()  -> impl Parser<'a, &'a str, char, char> {
    |input: &'a str| {
        if let Some(input2) = input.strip_prefix('\\') {
            match input2.take_one() {
                None => Err(ParseError::no_parse(
                    "expected escape sequence to continue but found end-of-input",
                    input
                )),
                Some((input3, 'u')) => {
                    match extract_codepoint(input3) {
                        Some((input4, c)) => Ok((input4, c)),
                        None => Err(ParseError::no_parse(
                            "invalid codepoint literal",
                            input
                        )),
                    }
                }
                Some((input3, '\\')) => Ok((input3, '\\')),
                Some((input3, '"')) => Ok((input3, '"')),
                Some((input3, 'n')) => Ok((input3, '\n')),
                Some((input3, 'r')) => Ok((input3, '\r')),
                Some((input3, 't')) => Ok((input3, '\t')),
                Some((input3, 'f')) => Ok((input3, '\u{000c}')),
                Some((input3, 'b')) => Ok((input3, '\u{0008}')),
                // i'm not sure why this needs an escape sequence, but it's in the spec
                Some((input3, '/')) => Ok((input3, '/')),
                Some(_) => Err(ParseError::no_parse("invalid escape sequence", input)),
            }
        } else {
            match input.take_one() {
                None => Err(ParseError::empty_input()),
                Some((_inp2, '"')) => Err(ParseError::no_parse(
                    "unescaped double-quotes are not valid string body characters",
                    input
                )),
                // only need to check the lower limit, chars with scalar-values
                // higher than 0x10ffff don't show up in safe rust
                Some((_inp2, '\u{0000}' .. '\u{0020}')) => Err(ParseError::no_parse(
                    "found char with a non-allowed scalar value",
                    input
                )),
                Some((rest, c)) => Ok((rest, c)),
            }
        }
    }
}

fn string_literal<'a>() -> impl Parser<'a, &'a str, char, String> {
    string_char().mult().within(token('"')).map(|v| String::from_iter(v.into_iter()))
}

fn json_string<'a>() -> impl Parser<'a, &'a str, char, Json> {
    string_literal().convert()
}

// using the definition of whitespace found in the spec
fn is_whitespace(c: &char) -> bool {
    matches!(c, '\u{20}' | '\u{0D}' | '\u{0A}' | '\u{09}')
}

fn ws<'a>() -> impl Parser<'a, &'a str, char, ()> {
    token_satisfies(is_whitespace).mult().ignore()
}

// includes surrounding whitespace
fn comma<'a>() -> impl Parser<'a, &'a str, char, ()> {
    token(',').within(ws()).ignore()
}

// does not include trailing commas
// does not include whitespace before the first element OR after the last element
// DOES allow for empty lists
fn comma_delimited<'a, T, P>(p: P) -> impl Parser<'a, &'a str, char, Vec<T>>
where
    T: 'a,
    P: Parser<'a, &'a str, char, T> + 'a,
{
    p.sep_by(comma()).recover_default()
}

// spec does not support trailing commas for arrays
fn json_array<'a>() -> impl Parser<'a, &'a str, char, Json> {
    let arr_body = comma_delimited(lazy(json_value).boxed());
    let open = token('[').left(ws());
    let close = ws().right(token(']'));
    arr_body.between(open, close).convert()
}

// Implementation choice: duplicate object keys will be handled
// according to ECMA-262: "In the case where there are duplicate
// name Strings within an object, lexically preceding values
// for the same key shall be overwritten."
// This is also the current behavior for HashMap::from([(K, V); const N])
// as well as HashMap::from_iter(), so this behavior should be implemented for free.
fn json_object<'a>() -> impl Parser<'a, &'a str, char, Json> {
    let member = string_literal()
        .left(token(':').within(ws()))
        .plus(lazy(json_value).boxed());
    let obj_body = comma_delimited(member);
    let open = token('{').left(ws());
    let close = ws().right(token('}'));
    obj_body.between(open, close).map(|kvs| {
        HashMap::from_iter(kvs.into_iter()).into()
    })
}

fn json_value<'a>() -> impl Parser<'a, &'a str, char, Json> {
    first_of![
        json_null(),
        json_bool(),
        json_number(),
        json_string(),
        json_array(),
        json_object(),
    ]
}

fn main() {

    let final_boss = r#"{
        "nulls": null,
        "bools": [true, false],
        "ints": {
            "zero": 0,
            "positive": 56789,
            "negative": -1234
        },
        "floats": {
            "zeroes": [0.0, -0e1],
            "positive": 12340.56789,
            "negative": -98765.04321
        },
        "strings": "新しい日の誕生",
        "funkier strings": "weird begins > \"\\\/\r\n\u03a3\f _\b \t< weird ends",
        "nesting": [
            {"child1": 1},
            {"child2" :2},
            {"child3" : 3},
            {"children456":[4,5,6]}
        ],
        "matrix": [
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9]
        ]
    }"#;
    println!("{:?}", json_object().parse(final_boss));
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_err {
        ($e:expr) => {
            assert!($e.is_err());
        };
    }

    #[test]
    fn example_json_test_null() {
        let p = json_null();

        assert_eq!(("", Json::Null), p.parse("null").unwrap());
        assert_eq!(("_extra", Json::Null), p.parse("null_extra").unwrap());

        assert_err!(p.parse(""));
        assert_err!(p.parse("nUll"));
        assert_err!(p.parse("nil"));
        assert_err!(p.parse("Null"));
    }

    #[test]
    fn example_json_test_bool() {
        let p = json_bool();

        assert_eq!(("", Json::Bool(true)), p.parse("true").unwrap());
        assert_eq!(("", Json::Bool(false)), p.parse("false").unwrap());
        assert_eq!(("_extra", Json::Bool(true)), p.parse("true_extra").unwrap());
        assert_eq!(("_extra", Json::Bool(false)), p.parse("false_extra").unwrap());

        assert_err!(p.parse(""));
        assert_err!(p.parse("frue"));
        assert_err!(p.parse("tralse"));
        assert_err!(p.parse("False"));
        assert_err!(p.parse("True"));
    }

    #[test]
    fn example_json_test_number() {
        let p = json_number();

        assert_eq!(("", Json::Int(0)), p.parse("0").unwrap());
        assert_eq!(("", Json::Int(0)), p.parse("-0").unwrap());
        assert_eq!(("", Json::Int(123450)), p.parse("123450").unwrap());
        assert_eq!(("", Json::Int(-67890)), p.parse("-67890").unwrap());

        assert_eq!(("_450", Json::Int(123)), p.parse("123_450").unwrap());
        assert_eq!(("_450.678", Json::Int(123)), p.parse("123_450.678").unwrap());

        assert_eq!(("", Json::Float(0.0)), p.parse("0.0").unwrap());
        assert_eq!(("", Json::Float(-0.0)), p.parse("-0.0").unwrap());
        
        assert_eq!(("", Json::Float(12345.06789)), p.parse("12345.06789").unwrap());
        assert_eq!(("", Json::Float(-12345.06789)), p.parse("-12345.06789").unwrap());

        // exhaustive format checks, '2' added to end of all patterns
        // with decimal point
        assert_eq!(("", Json::Float(12.342)), p.parse("12.342").unwrap());
        assert_eq!(("", Json::Float(-12.342)), p.parse("-12.342").unwrap());
        assert_eq!(("", Json::Float(1234.0)), p.parse("12.34e2").unwrap());
        assert_eq!(("", Json::Float(-1234.0)), p.parse("-12.34e2").unwrap());
        assert_eq!(("", Json::Float(1234.0)), p.parse("12.34E2").unwrap());
        assert_eq!(("", Json::Float(-1234.0)), p.parse("-12.34E2").unwrap());
        assert_eq!(("+2", Json::Float(12.34)), p.parse("12.34+2").unwrap());
        assert_eq!(("+2", Json::Float(-12.34)), p.parse("-12.34+2").unwrap());
        assert_eq!(("", Json::Float(1234.0)), p.parse("12.34e+2").unwrap());
        assert_eq!(("", Json::Float(-1234.0)), p.parse("-12.34e+2").unwrap());
        assert_eq!(("", Json::Float(1234.0)), p.parse("12.34E+2").unwrap());
        assert_eq!(("", Json::Float(-1234.0)), p.parse("-12.34E+2").unwrap());
        assert_eq!(("-2", Json::Float(12.34)), p.parse("12.34-2").unwrap());
        assert_eq!(("-2", Json::Float(-12.34)), p.parse("-12.34-2").unwrap());
        assert_eq!(("", Json::Float(0.1234)), p.parse("12.34e-2").unwrap());
        assert_eq!(("", Json::Float(-0.1234)), p.parse("-12.34e-2").unwrap());
        assert_eq!(("", Json::Float(0.1234)), p.parse("12.34E-2").unwrap());
        assert_eq!(("", Json::Float(-0.1234)), p.parse("-12.34E-2").unwrap());
        //without decimal point
        assert_eq!(("", Json::Int(12342)), p.parse("12342").unwrap());
        assert_eq!(("", Json::Int(-12342)), p.parse("-12342").unwrap());
        assert_eq!(("", Json::Float(123400.0)), p.parse("1234e2").unwrap());
        assert_eq!(("", Json::Float(-123400.0)), p.parse("-1234e2").unwrap());
        assert_eq!(("", Json::Float(123400.0)), p.parse("1234E2").unwrap());
        assert_eq!(("", Json::Float(-123400.0)), p.parse("-1234E2").unwrap());
        assert_eq!(("+2", Json::Int(1234)), p.parse("1234+2").unwrap());
        assert_eq!(("+2", Json::Int(-1234)), p.parse("-1234+2").unwrap());
        assert_eq!(("", Json::Float(123400.0)), p.parse("1234e+2").unwrap());
        assert_eq!(("", Json::Float(-123400.0)), p.parse("-1234e+2").unwrap());
        assert_eq!(("", Json::Float(123400.0)), p.parse("1234E+2").unwrap());
        assert_eq!(("", Json::Float(-123400.0)), p.parse("-1234E+2").unwrap());
        assert_eq!(("-2", Json::Int(1234)), p.parse("1234-2").unwrap());
        assert_eq!(("-2", Json::Int(-1234)), p.parse("-1234-2").unwrap());
        assert_eq!(("", Json::Float(12.34)), p.parse("1234e-2").unwrap());
        assert_eq!(("", Json::Float(-12.34)), p.parse("-1234e-2").unwrap());
        assert_eq!(("", Json::Float(12.34)), p.parse("1234E-2").unwrap());
        assert_eq!(("", Json::Float(-12.34)), p.parse("-1234E-2").unwrap());

        // only 'zero' values can begin their whole component with zero:
        assert_err!(p.parse("01"));
        assert_err!(p.parse("01.0"));
        assert_err!(p.parse("-01"));
        assert_err!(p.parse("-01.0e4"));

        // correct handling of values out of range of i64
        let i64min_str = "-9223372036854775808";
        assert_eq!(("", Json::Int(-9_223_372_036_854_775_808i64)), p.parse(i64min_str).unwrap());
        let i64min_minus1_str = "-9223372036854775809";
        assert_err!(p.parse(i64min_minus1_str));
        assert_err!(p.parse("-9999999999999999999999999999999999999999999999999"));
        let i64max_str = "9223372036854775807";
        assert_eq!(("", Json::Int(9_223_372_036_854_775_807i64)), p.parse(i64max_str).unwrap());
        let i64max_plus1_str = "9223372036854775808";//-1.7976931348623157E+308f64
        assert_err!(p.parse(i64max_plus1_str));
        assert_err!(p.parse("9999999999999999999999999999999999999999999999999"));

        // TODO: test extreme values of f64
    }

    #[test]
    fn example_json_test_string() {
        let p = json_string();

        assert_eq!(("", Json::String("".into())), p.parse("\"\"").unwrap());
        assert_eq!(("", Json::String("foo".into())), p.parse("\"foo\"").unwrap());
        assert_eq!(("extra", Json::String("foo".into())), p.parse("\"foo\"extra").unwrap());

        assert_eq!(("", Json::String("text with \" some \\ escapes".into())), p.parse("\"text with \\\" some \\\\ escapes\"").unwrap());

        // every (supported) escape sequence
        assert_eq!(("", Json::String("\\".into())), p.parse(r#""\\""#).unwrap());
        assert_eq!(("", Json::String("/".into())), p.parse(r#""\/""#).unwrap());
        assert_eq!(("", Json::String("\"".into())), p.parse(r#""\"""#).unwrap());
        assert_eq!(("", Json::String("\u{0008}".into())), p.parse(r#""\b""#).unwrap());
        assert_eq!(("", Json::String("\u{000C}".into())), p.parse(r#""\f""#).unwrap());
        assert_eq!(("", Json::String("\n".into())), p.parse(r#""\n""#).unwrap());
        assert_eq!(("", Json::String("\r".into())), p.parse(r#""\r""#).unwrap());
        assert_eq!(("", Json::String("\t".into())), p.parse(r#""\t""#).unwrap());
        // unicode codepoints
        assert_eq!(("", Json::String("A".into())), p.parse(r#""\u0041""#).unwrap());
        assert_eq!(("", Json::String("Σ".into())), p.parse(r#""\u03a3""#).unwrap());
        assert_eq!(("", Json::String("Σ".into())), p.parse(r#""\u03A3""#).unwrap());

        // un-escaped control characters
        assert_err!(p.parse("\"\0\""));
        assert_err!(p.parse("\"\n\""));
        assert_err!(p.parse("\"\u{1B}\""));

        // invalid escape sequences
        assert_err!(p.parse(r#""\""#));
        assert_err!(p.parse(r#""\j""#));
        assert_err!(p.parse(r#""\0""#));
        assert_err!(p.parse(r#""\xab""#));

        // invalid unicode codepoints
        assert_err!(p.parse(r#""\uD800""#));
        assert_err!(p.parse(r#""\uDFFF""#));
        assert_err!(p.parse(r#""\uDE01""#));
    }

    /*
    #[test]
    fn example_json_test_array() {
        assert_eq!(("", Json::Cons(_)), p.parse("[]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[  ]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[ null]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[true, false ]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[1, 2, 3, -4.5, 1e2]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[ \"strings\", [\"in\"], [\"nested\",\"arrays\"] ]").unwrap());
    }

    #[test]
    fn example_json_test_object() {
        assert_eq!(("", Json::Cons(_)), p.parse("{}").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("{  }").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("{\"foo\" : null}").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("{ \"first\":{\"one\": 1}, \"second\": {\"two_i\":2, \"two_f\": 2.0} }").unwrap());
    }

    #[test]
    fn example_json_test_value() {
        assert_eq!(("", Json::Cons(_)), p.parse("null").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("true").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("109").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("-98765.4e-4").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("\"strings with \\\" escapes\"").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("[null, 1, true, -3.4]").unwrap());
        assert_eq!(("", Json::Cons(_)), p.parse("{ \"objects\": null, \"containing\": false, \"all\" :23.45, \"of\" : \"the\", \"different\": [\"data\", \"types\"], \"including\":{\"other\":\"objects\"} }").unwrap());
    }
    */
}
