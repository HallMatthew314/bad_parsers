extern crate bad_parsers;

use std::collections::HashMap;
use std::str::FromStr;

use bad_parsers::{Tokens, Parser, ParseError, span_string_char, string, token, token_satisfies, first_of};

// JSON is being parsed according to the grammar at: https://www.json.org/json-en.html

#[derive(Debug)]
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

fn string_char<'a>()  -> impl Parser<'a, &'a str, char, char> {
    |input: &'a str| {
        if let Some(input2) = input.strip_prefix('\\') {
            match input2.take_one() {
                None => Err(ParseError::no_parse(
                    "expected escape sequence to continue but found end-of-input",
                    input
                )),
                Some((input3, 'u')) => {
                    let Some((point_text, input4)) = input3.split_at_checked(4) else {
                        return Err(ParseError::no_parse(
                            "invalid codepoint literal",
                            input
                        ));
                    };
                    // note: from_str_radix(_, 16) allows for mixed-case hex literals,
                    // so no upper/lower case conversion is required
                    let Ok(u) = u32::from_str_radix(point_text, 16) else {
                        return Err(ParseError::no_parse(
                            "invalid codepoint literal",
                            input
                        ));
                    };
                    match char::try_from(u) {
                        Err(_) => Err(ParseError::no_parse(
                            "codepoint is valid, but the value is not allowed in Rust",
                            input
                        )),
                        Ok(c) => Ok((input4, c)),
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

fn json_value<'a>() -> impl Parser<'a, &'a str, char, Json> {
    first_of![
        json_null(),
        json_bool(),
        json_number(),
        json_string(),
    ]
}

fn main() {
    println!("{:?}", json_null().parse("null"));
    println!("{:?}", json_bool().parse("true"));
    println!("{:?}", json_bool().parse("false"));
    println!("{:?}", json_number().parse("0"));
    println!("{:?}", json_number().parse("-0"));
    println!("{:?}", json_number().parse("123450"));
    println!("{:?}", json_number().parse("-67890"));
    println!("{:?}", json_number().parse("0.0"));
    println!("{:?}", json_number().parse("-0.0"));
    println!("{:?}", json_number().parse("123.450"));
    println!("{:?}", json_number().parse("-67.890"));
    println!("{:?}", json_number().parse("1.0e5"));
    println!("{:?}", json_number().parse("1e+5"));
    println!("{:?}", json_number().parse("1.0e-5"));
    println!("{:?}", json_number().parse("1e-5"));
    println!("{:?}", json_string().parse("\"\"")); // empty string
    println!("{:?}", json_string().parse(r#""a string""#));
    // the codepoint literals should become "greek capital letter sigma" (Σ)
    let complicated_string = r#""a\r\n \u03a3tring\"\fwith \\ \/e\u03A3caped\tcharacters_\b""#;
    match json_string().parse(complicated_string) {
        Err(e) => println!("{:?}", e),
        ok => {
            println!("{:?}", ok);
            let Ok((_, Json::String(s))) = ok else { panic!("shut up rust"); };
            println!("as rendered by rust:\n{}", s);
        }
    }
    // Implementation choice: duplicate object keys will be handled
    // according to ECMA-262: "In the case where there are duplicate
    // name Strings within an object, lexically preceding values
    // for the same key shall be overwritten."
    // This is also the current behavior for HashMap::from([(K, V); const N])
    // as well as HashMap::from_iter(), so this should be implemented for free.
    let test_map = HashMap::<&str, i32>::from_iter(vec![
        ("alpha", 1),
        ("beta", 2),
        ("gamma", 3),
        ("alpha", 4),
        ("epsilon", 5),
        ("alpha", 6),
    ].into_iter());
    println!("{:?}", test_map);

    let test_hex1 = u32::from_str_radix("1AA5", 16).unwrap();
    let test_hex2 = u32::from_str_radix("1aA5", 16).unwrap();
    let test_hex3 = u32::from_str_radix("1Aa5", 16).unwrap();
    let test_hex4 = u32::from_str_radix("1aa5", 16).unwrap();
    println!("{}\n{}\n{}\n{}", test_hex1, test_hex2, test_hex3, test_hex4);
}

