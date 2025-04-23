#[allow(dead_code)]
extern crate bad_parsers;

use std::collections::HashMap;
use std::str::FromStr;

use bad_parsers::{
    eof, first_of, lazy, string, token, token_satisfies, ParseError, Parser, Tokens,
};

// JSON is being parsed according to the grammar at: https://www.json.org/json-en.html
// It's not exactly produciton-ready, but it works well enough
// Also, lexing JSON and then parsing the tokens is overkill for such a simple format,
// but I want to demonstrate the fact that you can do both
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

impl From<&str> for Json {
    fn from(value: &str) -> Self {
        Json::String(value.to_owned())
    }
}

// digit string is one or more ascii digits, does not check for leading zeroes
// string literal contains the chars between the quote marks, may be empty
#[derive(Debug, Clone, PartialEq, Eq)]
enum JToken {
    StringLiteral(String),
    DigitString(String),
    True,
    False,
    Null,
    OpenCurly,
    CloseCurly,
    Colon,
    Comma,
    OpenSquare,
    CloseSquare,
    Minus,
    Plus,
    E,
    Dot,
}

// using the definition of whitespace found in the spec
fn is_whitespace(c: &char) -> bool {
    matches!(c, '\u{20}' | '\u{0D}' | '\u{0A}' | '\u{09}')
}

fn ws<'a>() -> impl Parser<'a, &'a str, char, ()> {
    token_satisfies(is_whitespace).mult().ignore()
}

macro_rules! lex_simple {
    ($name:ident, $pat:literal, $tok:ident) => {
        fn $name<'a>() -> impl Parser<'a, &'a str, char, JToken> {
            string($pat).replace(JToken::$tok)
        }
    };
}
lex_simple!(lex_true, "true", True);
lex_simple!(lex_false, "false", False);
lex_simple!(lex_null, "null", Null);
lex_simple!(lex_open_curly, "{", OpenCurly);
lex_simple!(lex_close_curly, "}", CloseCurly);
lex_simple!(lex_colon, ":", Colon);
lex_simple!(lex_comma, ",", Comma);
lex_simple!(lex_open_square, "[", OpenSquare);
lex_simple!(lex_close_square, "]", CloseSquare);
lex_simple!(lex_minus, "-", Minus);
lex_simple!(lex_plus, "+", Plus);
lex_simple!(lex_dot, ".", Dot);

fn lex_e<'a>() -> impl Parser<'a, &'a str, char, JToken> {
    token('e').or(token('E')).replace(JToken::E)
}

fn lex_digit_string<'a>() -> impl Parser<'a, &'a str, char, JToken> {
    token_satisfies(char::is_ascii_digit)
        .mult1()
        .map(|cs| JToken::DigitString(String::from_iter(cs)))
}

fn extract_codepoint(text: &str) -> Option<(&str, char)> {
    let (point_text, rest) = text.split_at_checked(4)?;
    // note: from_str_radix(_, 16) allows for mixed-case hex literals,
    // so no upper/lower case conversion is required
    let u = u32::from_str_radix(point_text, 16).ok()?;
    let c = char::try_from(u).ok()?;
    Some((rest, c))
}

fn string_char<'a>() -> impl Parser<'a, &'a str, char, char> {
    |input: &'a str| {
        if let Some(input2) = input.strip_prefix('\\') {
            match input2.take_one() {
                None => Err(ParseError::no_parse(
                    "expected escape sequence to continue but found end-of-input",
                    input,
                )),
                Some((input3, 'u')) => match extract_codepoint(input3) {
                    Some((input4, c)) => Ok((input4, c)),
                    None => Err(ParseError::no_parse("invalid codepoint literal", input)),
                },
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
                None => Err(ParseError::empty_input(
                    "expected string literal to continue, but got end of input",
                )),
                Some((_inp2, '"')) => Err(ParseError::no_parse(
                    "unescaped double-quotes are not valid string body characters",
                    input,
                )),
                // only need to check the lower limit, chars with scalar-values
                // higher than 0x10ffff don't show up in safe rust
                Some((_inp2, '\u{0000}'..'\u{0020}')) => Err(ParseError::no_parse(
                    "found char with a non-allowed scalar value",
                    input,
                )),
                Some((rest, c)) => Ok((rest, c)),
            }
        }
    }
}

fn string_literal<'a>() -> impl Parser<'a, &'a str, char, String> {
    string_char()
        .mult()
        .within(token('"'))
        .map(String::from_iter)
}

fn lex_string_literal<'a>() -> impl Parser<'a, &'a str, char, JToken> {
    string_literal().map(JToken::StringLiteral)
}

fn lex_lexeme<'a>() -> impl Parser<'a, &'a str, char, JToken> {
    first_of![
        lex_true(),
        lex_false(),
        lex_null(),
        lex_open_curly(),
        lex_close_curly(),
        lex_colon(),
        lex_comma(),
        lex_open_square(),
        lex_close_square(),
        lex_minus(),
        lex_plus(),
        lex_dot(),
        lex_digit_string(),
        lex_string_literal(),
        lex_e(),
    ]
}

fn lex_json<'a>() -> impl Parser<'a, &'a str, char, Vec<JToken>> {
    lex_lexeme().sep_by(ws()).within(ws())
}

fn json_null<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    // map instead of replace saves implementing clone for Json
    token(JToken::Null).map(|_| Json::Null)
}

fn json_bool<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    token(JToken::True)
        .replace(true)
        .or(token(JToken::False).replace(false))
        .convert()
}

fn json_digit_string<'a>() -> impl Parser<'a, &'a [JToken], JToken, String> {
    |input: &'a [JToken]| match input.take_one() {
        Some((rest, JToken::DigitString(s))) => Ok((rest, s)),
        Some((_rest, t)) => {
            let msg = format!("expected digit string, but found: {:?}", t);
            Err(ParseError::no_parse(&msg, input))
        }
        None => Err(ParseError::empty_input(
            "expected digit string but found nothing",
        )),
    }
}

// parses ::Plus or ::Minus, returns (== ::Minus)
fn json_sign_is_negative<'a>() -> impl Parser<'a, &'a [JToken], JToken, bool> {
    token(JToken::Minus)
        .replace(true)
        .or(token(JToken::Plus).replace(false))
}

// returns Int and Float Json variants
fn json_number<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    let integer = token(JToken::Minus)
        .optional()
        .plus(json_digit_string().ensure(|s| s == "0" || !s.starts_with('0')));
    let fraction = token(JToken::Dot).right(json_digit_string());
    let exponent = token(JToken::E).right(
        json_sign_is_negative()
            .recover(false)
            .plus(json_digit_string()),
    );

    let p = integer.plus(fraction.optional()).plus(exponent.optional());

    move |input: &'a [JToken]| {
        let (inp, (((opt_neg_sign, i_body), frac), exp)) = p.parse(input)?;

        // Implementation choice: if the string contains a fraction component AND/OR
        // an exponent component, it is treated as a float
        if frac.is_some() || exp.is_some() {
            let exp_str = if let Some((exp_sign, exp_digits)) = exp {
                format!("e{}{}", if exp_sign { "-" } else { "" }, exp_digits)
            } else {
                "".to_string()
            };
            let full_string = format!(
                "{}{}.{}{}",
                if opt_neg_sign.is_some() { "-" } else { "" },
                i_body,
                frac.unwrap_or("0".to_string()),
                exp_str,
            );
            // i promise this isn't cheating
            match f64::from_str(&full_string) {
                Ok(f) => Ok((inp, Json::Float(f))),
                Err(parse_float_error) => {
                    let details = &format!(
                        "successfully parsed the float ({}), but the type conversion failed",
                        full_string
                    );
                    Err(ParseError::other(details, inp, parse_float_error))
                }
            }
        } else {
            let full_string = format!(
                "{}{}",
                if opt_neg_sign.is_some() { "-" } else { "" },
                i_body
            );
            // i still promise this isn't cheating
            match i64::from_str(&full_string) {
                Ok(i) => Ok((inp, Json::Int(i))),
                Err(parse_int_error) => {
                    let details = &format!(
                        "successfully parsed the int ({}), but the type conversion failed",
                        full_string
                    );
                    Err(ParseError::other(details, inp, parse_int_error))
                }
            }
        }
    }
}

// used for string values and object keys
fn json_string_literal<'a>() -> impl Parser<'a, &'a [JToken], JToken, String> {
    |input: &'a [JToken]| match input.take_one() {
        Some((rest, JToken::StringLiteral(s))) => Ok((rest, s)),
        Some((_rest, t)) => {
            let msg = format!("expected string literal, but found: {:?}", t);
            Err(ParseError::no_parse(&msg, input))
        }
        None => Err(ParseError::empty_input(
            "expected string literal but found nothing",
        )),
    }
}

fn json_string<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    json_string_literal().convert()
}

// spec does not support trailing commas for arrays
fn json_array<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    let arr_body = lazy(json_value)
        .sep_by(token(JToken::Comma))
        .recover_default()
        .boxed();
    arr_body
        .between(token(JToken::OpenSquare), token(JToken::CloseSquare))
        .convert()
}

// Implementation choice: duplicate object keys will be handled
// according to ECMA-262: "In the case where there are duplicate
// name Strings within an object, lexically preceding values
// for the same key shall be overwritten."
// This is also the current behavior for HashMap::from([(K, V); const N])
// as well as HashMap::from_iter(), so this behavior should be implemented for free.
fn json_object<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    let member = json_string_literal()
        .left(token(JToken::Colon))
        .plus(lazy(json_value))
        .boxed();
    member
        .sep_by(token(JToken::Comma))
        .recover_default()
        .between(token(JToken::OpenCurly), token(JToken::CloseCurly))
        .map(HashMap::<String, Json>::from_iter)
        .convert()
}

fn json_value<'a>() -> impl Parser<'a, &'a [JToken], JToken, Json> {
    first_of![
        json_null(),
        json_bool(),
        json_number(),
        json_string(),
        json_array(),
        json_object(),
    ]
}

// yes, this discards all of the error information, i don't care
fn parse_json(input_string: &str) -> Option<Json> {
    let lex = lex_json();
    //println!("About to lex");
    let tokens = lex.parse(input_string).ok()?.1;
    //println!("Got tokens: {:?}", tokens);

    //println!("About to parse");
    let p = json_value().left(eof());
    p.parse(tokens.as_slice()).ok().map(|tup| tup.1)
}

fn main() {
    let r = parse_json(r#"[null, true, 3, 4.5]"#);
    println!("parsed: {:?}", r);
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_none {
        ($e:expr) => {
            assert!($e.is_none());
        };
    }

    #[test]
    fn example_json_test_null() {
        assert_eq!(Json::Null, parse_json("null").unwrap());
        assert_eq!(Json::Null, parse_json("null_extra").unwrap());

        assert_none!(parse_json(""));
        assert_none!(parse_json("nUll"));
        assert_none!(parse_json("nil"));
        assert_none!(parse_json("Null"));
    }

    #[test]
    fn example_json_test_bool() {
        assert_eq!(Json::Bool(true), parse_json("true").unwrap());
        assert_eq!(Json::Bool(false), parse_json("false").unwrap());
        assert_eq!(Json::Bool(true), parse_json("true_extra").unwrap());
        assert_eq!(Json::Bool(false), parse_json("false_extra").unwrap());

        assert_none!(parse_json(""));
        assert_none!(parse_json("frue"));
        assert_none!(parse_json("tralse"));
        assert_none!(parse_json("False"));
        assert_none!(parse_json("True"));
    }

    #[test]
    fn example_json_test_number() {
        assert_eq!(Json::Int(0), parse_json("0").unwrap());
        assert_eq!(Json::Int(0), parse_json("-0").unwrap());
        assert_eq!(Json::Int(123450), parse_json("123450").unwrap());
        assert_eq!(Json::Int(-67890), parse_json("-67890").unwrap());

        assert_eq!(Json::Int(123), parse_json("123_450").unwrap());
        assert_eq!(Json::Int(123), parse_json("123_450.678").unwrap());

        assert_eq!(Json::Float(0.0), parse_json("0.0").unwrap());
        assert_eq!(Json::Float(-0.0), parse_json("-0.0").unwrap());

        assert_eq!(Json::Float(12345.06789), parse_json("12345.06789").unwrap());
        assert_eq!(
            Json::Float(-12345.06789),
            parse_json("-12345.06789").unwrap()
        );

        // exhaustive format checks, '2' added to end of all patterns
        // with decimal point
        assert_eq!(Json::Float(12.342), parse_json("12.342").unwrap());
        assert_eq!(Json::Float(-12.342), parse_json("-12.342").unwrap());
        assert_eq!(Json::Float(1234.0), parse_json("12.34e2").unwrap());
        assert_eq!(Json::Float(-1234.0), parse_json("-12.34e2").unwrap());
        assert_eq!(Json::Float(1234.0), parse_json("12.34E2").unwrap());
        assert_eq!(Json::Float(-1234.0), parse_json("-12.34E2").unwrap());
        assert_none!(parse_json("12.34+2"));
        assert_none!(parse_json("-12.34+2"));
        assert_eq!(Json::Float(1234.0), parse_json("12.34e+2").unwrap());
        assert_eq!(Json::Float(-1234.0), parse_json("-12.34e+2").unwrap());
        assert_eq!(Json::Float(1234.0), parse_json("12.34E+2").unwrap());
        assert_eq!(Json::Float(-1234.0), parse_json("-12.34E+2").unwrap());
        assert_none!(parse_json("12.34-2"));
        assert_none!(parse_json("-12.34-2"));
        assert_eq!(Json::Float(0.1234), parse_json("12.34e-2").unwrap());
        assert_eq!(Json::Float(-0.1234), parse_json("-12.34e-2").unwrap());
        assert_eq!(Json::Float(0.1234), parse_json("12.34E-2").unwrap());
        assert_eq!(Json::Float(-0.1234), parse_json("-12.34E-2").unwrap());
        //without decimal point
        assert_eq!(Json::Int(12342), parse_json("12342").unwrap());
        assert_eq!(Json::Int(-12342), parse_json("-12342").unwrap());
        assert_eq!(Json::Float(123400.0), parse_json("1234e2").unwrap());
        assert_eq!(Json::Float(-123400.0), parse_json("-1234e2").unwrap());
        assert_eq!(Json::Float(123400.0), parse_json("1234E2").unwrap());
        assert_eq!(Json::Float(-123400.0), parse_json("-1234E2").unwrap());
        assert_none!(parse_json("1234+2"));
        assert_none!(parse_json("-1234+2"));
        assert_eq!(Json::Float(123400.0), parse_json("1234e+2").unwrap());
        assert_eq!(Json::Float(-123400.0), parse_json("-1234e+2").unwrap());
        assert_eq!(Json::Float(123400.0), parse_json("1234E+2").unwrap());
        assert_eq!(Json::Float(-123400.0), parse_json("-1234E+2").unwrap());
        assert_none!(parse_json("1234-2"));
        assert_none!(parse_json("-1234-2"));
        assert_eq!(Json::Float(12.34), parse_json("1234e-2").unwrap());
        assert_eq!(Json::Float(-12.34), parse_json("-1234e-2").unwrap());
        assert_eq!(Json::Float(12.34), parse_json("1234E-2").unwrap());
        assert_eq!(Json::Float(-12.34), parse_json("-1234E-2").unwrap());

        // only 'zero' values can begin their whole component with zero:
        assert_none!(parse_json("01"));
        assert_none!(parse_json("01.0"));
        assert_none!(parse_json("-01"));
        assert_none!(parse_json("-01.0e4"));

        // correct handling of values out of range of i64
        let i64min_str = "-9223372036854775808";
        assert_eq!(
            Json::Int(-9_223_372_036_854_775_808i64),
            parse_json(i64min_str).unwrap()
        );
        let i64min_minus1_str = "-9223372036854775809";
        assert_none!(parse_json(i64min_minus1_str));
        assert_none!(parse_json(
            "-9999999999999999999999999999999999999999999999999"
        ));
        let i64max_str = "9223372036854775807";
        assert_eq!(
            Json::Int(9_223_372_036_854_775_807i64),
            parse_json(i64max_str).unwrap()
        );
        let i64max_plus1_str = "9223372036854775808"; //-1.7976931348623157E+308f64
        assert_none!(parse_json(i64max_plus1_str));
        assert_none!(parse_json(
            "9999999999999999999999999999999999999999999999999"
        ));

        // TODO: test extreme values of f64
    }

    #[test]
    fn example_json_test_string() {
        assert_eq!(Json::String("".into()), parse_json("\"\"").unwrap());
        assert_eq!(Json::String("foo".into()), parse_json("\"foo\"").unwrap());

        assert_eq!(
            Json::String("text with \" some \\ escapes".into()),
            parse_json("\"text with \\\" some \\\\ escapes\"").unwrap()
        );

        // every (supported) escape sequence
        assert_eq!(Json::String("\\".into()), parse_json(r#""\\""#).unwrap());
        assert_eq!(Json::String("/".into()), parse_json(r#""\/""#).unwrap());
        assert_eq!(Json::String("\"".into()), parse_json(r#""\"""#).unwrap());
        assert_eq!(
            Json::String("\u{0008}".into()),
            parse_json(r#""\b""#).unwrap()
        );
        assert_eq!(
            Json::String("\u{000C}".into()),
            parse_json(r#""\f""#).unwrap()
        );
        assert_eq!(Json::String("\n".into()), parse_json(r#""\n""#).unwrap());
        assert_eq!(Json::String("\r".into()), parse_json(r#""\r""#).unwrap());
        assert_eq!(Json::String("\t".into()), parse_json(r#""\t""#).unwrap());
        // unicode codepoints
        assert_eq!(Json::String("A".into()), parse_json(r#""\u0041""#).unwrap());
        assert_eq!(Json::String("Σ".into()), parse_json(r#""\u03a3""#).unwrap());
        assert_eq!(Json::String("Σ".into()), parse_json(r#""\u03A3""#).unwrap());

        // un-escaped control characters
        assert_none!(parse_json("\"\0\""));
        assert_none!(parse_json("\"\n\""));
        assert_none!(parse_json("\"\u{1B}\""));

        // invalid escape sequences
        assert_none!(parse_json(r#""\""#));
        assert_none!(parse_json(r#""\j""#));
        assert_none!(parse_json(r#""\0""#));
        assert_none!(parse_json(r#""\xab""#));

        // invalid unicode codepoints
        assert_none!(parse_json(r#""\uD800""#));
        assert_none!(parse_json(r#""\uDFFF""#));
        assert_none!(parse_json(r#""\uDE01""#));
    }

    #[test]
    fn example_json_test_array() {
        assert_eq!(Json::Array(vec![]), parse_json("[]").unwrap());
        assert_eq!(Json::Array(vec![]), parse_json("[  ]").unwrap());
        assert_none!(parse_json("[  ]extra"));
        assert_eq!(
            Json::Array(vec![Json::Null]),
            parse_json("[ null]").unwrap()
        );
        assert_eq!(
            Json::Array(vec![Json::Bool(true), Json::Bool(false)]),
            parse_json("[true, false ]").unwrap()
        );
        assert_eq!(
            Json::Array(vec![
                Json::from(1),
                Json::from(2),
                Json::from(3),
                Json::from(-4.5),
                Json::from(1.0e2),
            ]),
            parse_json("[1, 2, 3, -4.5, 1e2]").unwrap()
        );
        assert_eq!(
            Json::Array(vec!["strings".into(), "in".into(), "arrays".into(),]),
            parse_json(r#"[ "strings", "in", "arrays" ]"#).unwrap()
        );
        assert_eq!(
            Json::Array(vec![
                Json::from("we"),
                Json::from(vec![Json::from("even")]),
                Json::from(vec![Json::from(vec![
                    Json::from("have"),
                    Json::from(vec![Json::from("nested"), Json::from("arrays"),]),
                ]),]),
            ]),
            parse_json(r#"["we",["even"],[["have",["nested","arrays"]]]]"#).unwrap()
        );

        assert_eq!(
            Json::Array(vec![
                Json::from(HashMap::from([
                    ("objects".into(), "with".into()),
                    ("multiple".into(), "keys".into()),
                ])),
                Json::from(HashMap::from([])),
                Json::from(HashMap::from([("inside".into(), "arrays".into())])),
            ]),
            parse_json(
                r#"[
                {"objects": "with", "multiple": "keys"},
                {},
                {"inside": "arrays"}
            ]"#
            )
            .unwrap()
        );

        // internal whitespace is fine
        assert_eq!(Json::Array(vec![]), parse_json("[ \t\n\r  ]").unwrap());
        assert_eq!(Json::Array(vec![Json::Null]), parse_json("[null]").unwrap());
        assert_eq!(
            Json::Array(vec![Json::Null]),
            parse_json("[ null]").unwrap()
        );
        assert_eq!(
            Json::Array(vec![Json::Null]),
            parse_json("[null ]").unwrap()
        );
        assert_eq!(
            Json::Array(vec![Json::Null]),
            parse_json("[    null   ]").unwrap()
        );

        macro_rules! a {
            () => {
                Json::Array(vec![Json::Null, Json::Null])
            };
        }
        assert_eq!(a!(), parse_json("[null,null]").unwrap());
        assert_eq!(a!(), parse_json("[null,null ]").unwrap());
        assert_eq!(a!(), parse_json("[null, null]").unwrap());
        assert_eq!(a!(), parse_json("[null, null ]").unwrap());
        assert_eq!(a!(), parse_json("[null ,null]").unwrap());
        assert_eq!(a!(), parse_json("[null ,null ]").unwrap());
        assert_eq!(a!(), parse_json("[null , null]").unwrap());
        assert_eq!(a!(), parse_json("[null , null ]").unwrap());
        assert_eq!(a!(), parse_json("[ null,null]").unwrap());
        assert_eq!(a!(), parse_json("[ null,null ]").unwrap());
        assert_eq!(a!(), parse_json("[ null, null]").unwrap());
        assert_eq!(a!(), parse_json("[ null, null ]").unwrap());
        assert_eq!(a!(), parse_json("[ null ,null]").unwrap());
        assert_eq!(a!(), parse_json("[ null ,null ]").unwrap());
        assert_eq!(a!(), parse_json("[ null , null]").unwrap());
        assert_eq!(a!(), parse_json("[ null , null ]").unwrap());

        assert_none!(parse_json(r#""#));
        assert_none!(parse_json("[ bhsrlre ]"));
        assert_none!(parse_json(r#"[ "oops\", "forgot the closing bracket" "#));
        assert_none!(parse_json(r#" "forgot the opening bracket too" ]"#));
        assert_none!(parse_json(r#" "are brackets", " even real?" "#));

        // no trailing commas
        assert_none!(parse_json("[ , ]"));
        assert_none!(parse_json("[ 8, ]"));
        assert_none!(parse_json("[8, 9 10,]"));
        assert_none!(parse_json("[8, [9,], 10]"));
    }

    #[test]
    fn example_json_test_object() {
        assert_eq!(Json::from(HashMap::from([])), parse_json("{}").unwrap());
        assert_eq!(
            Json::Object(HashMap::from([("foo".into(), Json::Null)]).into()),
            parse_json(r#"{"foo":null}"#).unwrap()
        );
        assert_eq!(
            Json::Object(HashMap::from([
                ("attribute".into(), Json::Null),
                ("values".into(), false.into()),
                ("can".into(), 12.into()),
                ("be".into(), 21.0.into()),
                ("any".into(), "type".into()),
                ("including".into(), vec!["arrays".into()].into()),
                (
                    "and".into(),
                    HashMap::from([("other".into(), "objects".into())]).into()
                ),
            ])),
            parse_json(
                r#"{
                "attribute": null,
                "values": false,
                "can": 12,
                "be": 21.0,
                "any": "type",
                "including": ["arrays"],
                "and": {"other": "objects"}
            }"#
            )
            .unwrap()
        );
        assert_eq!(
            Json::Object(HashMap::from([
                (
                    "first".into(),
                    HashMap::from([("one".into(), 1.into())]).into()
                ),
                (
                    "second".into(),
                    HashMap::from([("two_i".into(), 2.into()), ("two_f".into(), 2.0.into()),])
                        .into()
                ),
                (
                    "three".into(),
                    HashMap::from([(
                        "four".into(),
                        HashMap::from([(
                            "five".into(),
                            HashMap::from([("six".into(), 7.into())]).into()
                        )])
                        .into()
                    )])
                    .into()
                ),
            ])),
            parse_json(
                r#"{
                "first": {"one":1},
                "second": {
                    "two_i": 2,
                    "two_f": 2.0
                },
                "three": {"four": {"five": {"six":7} }}
            }"#
            )
            .unwrap()
        );

        assert_none!(parse_json(r#""#));
        assert_none!(parse_json(r#" {"oh": "no" "#));
        assert_none!(parse_json(r#" "it's happening": "again" } "#));
        assert_none!(parse_json(r#" "why am i":"like this" "#));

        // internal whitespace is ok
        macro_rules! o {
            () => {
                Json::Object(HashMap::from([(String::from("one"), Json::Int(1))]))
            };
        }
        assert_eq!(o!(), parse_json(r#"{"one":1}"#).unwrap());
        assert_eq!(o!(), parse_json(r#"{ "one":1}"#).unwrap());
        assert_eq!(o!(), parse_json(r#"{ "one" :1}"#).unwrap());
        assert_eq!(o!(), parse_json(r#"{ "one" : 1}"#).unwrap());
        assert_eq!(o!(), parse_json(r#"{ "one" : 1 }"#).unwrap());

        // no trailing commas
        assert_none!(parse_json("{,}"));
        assert_none!(parse_json(r#"{ "one":1, }"#));
        assert_none!(parse_json(r#"{ "one":1, "two":2, "three":3 , }"#));
        assert_none!(parse_json(
            r#"{
            "one":1,
            "two": {
                "nested":"object",
                "with":"trailing comma",
            },
            "three":3
        }"#
        ));

        // later identical keys replace earlier ones
        assert_eq!(
            Json::Object(HashMap::from([
                ("one".into(), 100.into()),
                ("two".into(), 2.into()),
                ("three".into(), 3.into()),
            ])),
            parse_json(
                r#"{
                "one": 1,
                "two": 2,
                "one": 10,
                "three": 3,
                "one": 100
            }"#
            )
            .unwrap()
        );
    }

    #[test]
    fn example_json_test_final_boss() {
        let final_boss_input = r#"{
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
                "negative": -98765.04321,
                "exponents": [1e4, 1E+4, 1E-4]
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
            ],
            "strange object keys": {
                "": "empty key",
                "foo\u0000bar": "escaped null",
                "\u041f\u043e\u043b\u0442\u043e\u0440\u0430 \u0417\u0435\u043c\u043b\u0435\u043a\u043e\u043f\u0430": "text -Полтора Землекопа- in unicode escapes"
            }
        }"#;
        let final_boss_expected = Json::Object(HashMap::from([
            ("nulls".into(), Json::Null),
            ("bools".into(), Json::Array(vec![true.into(), false.into()])),
            (
                "ints".into(),
                Json::Object(HashMap::from([
                    ("zero".into(), 0.into()),
                    ("positive".into(), 56789.into()),
                    ("negative".into(), (-1234).into()),
                ])),
            ),
            (
                "floats".into(),
                Json::Object(HashMap::from([
                    (
                        "zeroes".into(),
                        Json::Array(vec![0.0.into(), (-0.0).into()]),
                    ),
                    ("positive".into(), 12340.56789.into()),
                    ("negative".into(), (-98765.04321).into()),
                    (
                        "exponents".into(),
                        Json::Array(vec![10000.0.into(), 10000.0.into(), 0.0001.into()]),
                    ),
                ])),
            ),
            ("strings".into(), "新しい日の誕生".into()),
            (
                "funkier strings".into(),
                "weird begins > \"\\/\r\nΣ\u{000C} _\u{0008} \t< weird ends".into(),
            ),
            (
                "nesting".into(),
                Json::Array(vec![
                    Json::Object(HashMap::from([("child1".into(), 1.into())])),
                    Json::Object(HashMap::from([("child2".into(), 2.into())])),
                    Json::Object(HashMap::from([("child3".into(), 3.into())])),
                    Json::Object(HashMap::from([(
                        "children456".into(),
                        vec![4.into(), 5.into(), 6.into()].into(),
                    )])),
                ]),
            ),
            (
                "matrix".into(),
                Json::Array(vec![
                    Json::Array(vec![1.into(), 2.into(), 3.into()]),
                    Json::Array(vec![4.into(), 5.into(), 6.into()]),
                    Json::Array(vec![7.into(), 8.into(), 9.into()]),
                ]),
            ),
            (
                "strange object keys".into(),
                Json::Object(HashMap::from([
                    ("".into(), "empty key".into()),
                    ("foo\0bar".into(), "escaped null".into()),
                    (
                        "Полтора Землекопа".into(),
                        "text -Полтора Землекопа- in unicode escapes".into(),
                    ),
                ])),
            ),
        ]));

        assert_eq!(final_boss_expected, parse_json(final_boss_input).unwrap());
    }
}
