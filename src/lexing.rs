//! Tools for creating lexers
//!
//! This module is still a work-in-progress.
//!
//! For the purposes of this library, a 'lexer' is an object that implements
//! [`Parser<'a, &'a str, char, T>`], where `T` is some arbitrary token type
//! that will be parsed from later on.

/// Creates a function that provides a lexer capable of returning one result.
///
/// This macro requires the following for invocation:
/// * an identifier to name the resulting function
/// * one or more string literals for the lexer to look for
/// * the type of the token being returned
/// * the token value being returned
///
/// As such, lexers made with this function can only return one value on success:
/// ```
/// use bad_parsers::{Parser, simple_lexer};
///
/// #[derive(Debug, PartialEq)]
/// enum MyToken {
///     Colon,
///     SomethingElse,
/// }
///
/// simple_lexer!(lex_colon, ":", MyToken, MyToken::Colon);
///
/// let p = lex_colon();
///
/// assert_eq!(("", MyToken::Colon), p.parse(":").unwrap());
/// assert!(p.parse("something else").is_err());
/// ```
/// Note, however, that can can still match multiple patterns before returning that value:
/// ```
/// use bad_parsers::{Parser, simple_lexer};
///
/// #[derive(Debug, PartialEq)]
/// enum MyToken {
///     Sign,
///     SomethingElse,
/// }
///
/// simple_lexer!(lex_sign, "-", "+", MyToken, MyToken::Sign);
///
/// let p = lex_sign();
///
/// assert_eq!(("", MyToken::Sign), p.parse("+").unwrap());
/// assert_eq!(("", MyToken::Sign), p.parse("-").unwrap());
/// assert!(p.parse("something else").is_err());
/// ```
#[macro_export] // TODO: how to keep macros in a specific module, is it possible?
macro_rules! simple_lexer {
    ($name:ident, $pattern:literal, $rtype:ty, $val:expr) => {
        fn $name<'a>() -> impl $crate::Parser<'a, &'a str, char, $rtype> {
            $crate::string($pattern).map(|_| $val)
        }
    };
    ($name:ident, $( $pattern:literal ),+, $rtype:ty, $val:expr) => {
        fn $name<'a>() -> impl $crate::Parser<'a, &'a str, char, $rtype> {
            $crate::first_of![
                $( $crate::string($pattern) ),+
            ].map(|_| $val)
        }
    };
}
