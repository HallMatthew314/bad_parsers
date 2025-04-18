extern crate bad_parsers;

use std::collections::HashMap;
use std::str::FromStr;

use bad_parsers::{Parser, ParseError, span_string_char, string, token, token_satisfies};

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
}

