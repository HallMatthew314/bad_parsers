//! # bad_parsers
//!
//! A parser combinator library written by myself for myself.
//!
//! Don't say I didn't warn you.
//!
//! `bad_parsers` is a parser combinator library written entirely from scratch in safe Rust
//! with no external dependencies.
//! The provided parsers are able to parse from string slices, arbitrary token type slices,
//! as well as other token collections you may wish to implement yourself.
//!
//! In addition to these qulities, using this library in your own project is guaranteed to
//! make it worse! For free!
//!
//! ## Main Features
//!
//! * A [Parser trait](Parser) that primarily interfaces with functions and closures that act
//!     like parsers, but could also be used to treat other types as parsers as well.
//! * A [Tokens trait](Tokens) that allows things to be parsed out of
//!     arbitrary data types.<sup>[citation needed]</sup>
//! * Slightly-above the bare minimum of error handling: [`ParseResult`]s can provide one (1)
//!     error message when parsing is unsuccessful.
//! * [Lazily evaluated parsers](lazy) that allow for recursive definitions.
//! * A collection of common parser combinator utility functions to build custom parsers with.
//!
//! ## Overview of how the parsers work
//!
//! The job of a parser is to extract meaningful data from a collection of tokens.
//! To this end, a parser can be thought of as a function from some input tokens to some kind
//! of data the parser is looking for.
//! To achieve this, a parser will:
//!
//! * Examine the stream of tokens
//! * Fail if it cannot find what it is looking for
//! * If it does find it, return the parsed data *and* the remaining tokens
//!
//! The importance of returning the remaining tokens cannot be overstated, as this is what
//! allows multiple simple parsers to be composed and chained together to create much more
//! sophisticated parsers.
//!
//! ## [`Tokens`] and parser inputs
//!
//! As was already stated, parsers in this library are able to parse from arbitrary data
//! types, as long as they implement the [`Tokens`] trait.
//!
//! Implementors of this trait are thought of as containers of individual tokens.
//! In general, a type may implement [`Tokens<T>`] if:
//!
//! * it has a notion of being 'empty'
//! * it has a notion of *immutably* taking a single token from the 'front'
//!
//! More precise implementation guidelines for this trait are available in its documentation.
//!
//! All parsers accept a token container as their input to parse from and parsers being combined
//! together must operate on *the same token container type*.
//!
//! Currently, [`Tokens`] is only implemented OOTB by [`&str`] and [`&[T]`](slice).
//! In practice, these should be the only input types you would need to deal with.
//!
//! These two types having the same interface allows parsers to parse directly from strings, as
//! well as collections of arbitrary token types.
//! This means that for applications such as parsing a programming language, the combinator
//! framework can be used for both lexing **and** parsing.
//!
//! ## Creating parsers
//!
//! All parsers implement the trait [`Parser<'a, Toks, T, A>`](Parser).
//! The type arguments are as follows:
//!
//! * `'a` - named lifetime, nothing special
//! * `Toks` - the type of token stream this parser operates on, must implement [`Tokens<T>`]
//! * `T` - the type of the individual tokens contained within `Toks`
//! * `A` - the type of the value this parser tries to parse
//!
//! The typical way to define a custom parser is to use a function which returns an opaque type
//! with the appropriate [`Parser`] implementation.
//! This is normally done by returning a [closure with the approriate
//! signature](Parser#impl-Parser<'a,+Toks,+T,+A>-for-F):
//! ```
//! use bad_parsers::{Parser, ParseError};
//!
//! // parses a single i32 token if it's even
//! fn custom_parser<'a>() -> impl Parser<'a, &'a [i32], i32, i32> {
//!     |input: &'a [i32]| match input.iter().next() {
//!         Some(x) if x % 2 == 0 => Ok((&input[1..], *x)),
//!         _ => Err(ParseError::no_parse("no even int", input)),
//!     }
//! }
//!
//! // quirk with lifetimes: define your inputs before creating the parser
//! let nums = [1, 2, 3, 4, 5, 6, 7, 8, 9];
//!
//! let starts_with1 = &nums[0..];
//! let starts_with2 = &nums[1..];
//! let starts_with3 = &nums[2..];
//!
//! let p = custom_parser();
//!
//! assert!(p.parse(starts_with1).is_err());
//! assert_eq!((starts_with3, 2), p.parse(starts_with2).unwrap());
//! ```
//! Note the above example alludes to a quirk to do with the lifetimes of inputs.
//! That is explained more in-depth in the documentation of the [`Parser`] trait.
//!
//! If differing opaque types become an issue for the compiler, you may wish to wrap the parser
//! in a [`BoxedParser`], which can easily be done with the [`boxed`](Parser::boxed) method.
//!
//! Most of the provided combinator functions in this library will accept generic parser types.
//! However, some will require a [`BoxedParser`].
//! The most notable examples are the operator overloads for [`BoxedParser`].
//!
//! ## Worked Example: Parsing an Integer
//!
//! Suppose we want to find an integer at the start of a string.
//! At a high level, this means we first need to see if there are digits at the start of the
//! string.
//! If not, the parsing has failed and the parser will return an error.
//! If it succeeds, we need to return the digits it found, as well as the rest of the string.
//!
//! To get started, let's just try to parse a single digit.
//! We can do this with the parser-building function [`token_satisfies`], which builds a simple
//! parser out of a predicate function:
//! ```
//! use bad_parsers::{Parser, token_satisfies};
//!
//! let front_number = token_satisfies(char::is_ascii_digit);
//!
//! assert_eq!(("23", '1'), front_number.parse("123").unwrap());
//! assert_eq!(("rest", '3'), front_number.parse("3rest").unwrap());
//! assert_eq!(("0rest", '3'), front_number.parse("30rest").unwrap());
//! assert!(front_number.parse("no front number").is_err());
//! assert!(front_number.parse("").is_err());
//! ```
//! As we can see, the parser was able to extract the first digit from the front of the first
//! three inputs, but it failed to parse anything when there is no digit at the start,
//! or when the input is empty.
//!
//! A good first step, but we need to parse multiple digits.
//! For a task like this, `bad_parsers` provides the [`mult1`] combinator.
//! This takes a parser, and runs it multiple times over the input and collects the results in
//! a [`Vec`].
//! This new parser will keep collecting parsed values until it is unable to parse any more.
//! This parser will also fail if it is unable to parse at least one item from the input,
//! hence the
//! name:
//! ```
//! use bad_parsers::{Parser, token_satisfies};
//!
//! let front_number = token_satisfies(char::is_ascii_digit).mult1();
//!
//! assert_eq!(("", vec!['1', '2', '3']), front_number.parse("123").unwrap());
//! assert_eq!(("rest", vec!['3']), front_number.parse("3rest").unwrap());
//! assert_eq!(("rest", vec!['3', '0']), front_number.parse("30rest").unwrap());
//! assert!(front_number.parse("no front number").is_err());
//! assert!(front_number.parse("").is_err());
//! ```
//!
//! Now we're getting somewhere!
//!
//! We are now able to get all the digits from the start of a string.
//! Unfortunately, a [`Vec<char>`] is not an integer that Rust can do arithmetic with.
//! There are a few ways we could turn it into an integer, so I'm going to choose one of the
//! more convoluted solutions to show off more of the library.
//! We'll be using the [`map`] combinator to turn the digit characters into integers.
//! Note that the [`map`] is added *before* the [`mult1`], as we only want to work with one
//! digitat a time for the moment:
//! ```
//! use bad_parsers::{Parser, token_satisfies};
//!
//! let front_number = token_satisfies(char::is_ascii_digit)
//!     .map(|c| c.to_digit(10).unwrap())
//!     .mult1();
//!
//! assert_eq!(("", vec![1, 2, 3]), front_number.parse("123").unwrap());
//! assert_eq!(("rest", vec![3]), front_number.parse("3rest").unwrap());
//! assert_eq!(("rest", vec![3, 0]), front_number.parse("30rest").unwrap());
//! assert!(front_number.parse("no front number").is_err());
//! assert!(front_number.parse("").is_err());
//! ```
//! It's safe to unwrap the result of [`to_digit`](char::to_digit) here because it should
//! only receive actual digit characters as inputs.
//!
//! With that, we're almost there!
//! Our digits are now actual numbers.
//! All we have to do now is put them together.
//!
//! We'll need a more involved [`map`] for this one:
//! ```
//! use bad_parsers::{Parser, token_satisfies};
//!
//! let front_number = token_satisfies(char::is_ascii_digit)
//!     .map(|c| c.to_digit(10).unwrap())
//!     .mult1()
//!     .map(|digs| {
//!         let mut n = 0;
//!         for d in digs {
//!             n *= 10;
//!             n += d;
//!         }
//!         n
//!     });
//!
//! assert_eq!(("", 123), front_number.parse("123").unwrap());
//! assert_eq!(("rest", 3), front_number.parse("3rest").unwrap());
//! assert_eq!(("rest", 30), front_number.parse("30rest").unwrap());
//! assert!(front_number.parse("no front number").is_err());
//! assert!(front_number.parse("").is_err());
//! ```
//! Success! We now have a parser that can extract an integer from the start of a string.
//! With that being said, we could make this more friendly for other programmers who want to use
//! this cutting-edge integer parsing technology.
//! A programmer who is just trying to parse an integer doesn't really need to worry about the
//! remaining input, but our parser still returns it.
//! Let's put this parser in an easier-to-use function:
//! ```
//! use bad_parsers::{Parser, token_satisfies};
//!
//! fn parse_int(input: &str) -> Option<u32> {
//!     let p = token_satisfies(char::is_ascii_digit)
//!         .map(|c| c.to_digit(10).unwrap())
//!         .mult1()
//!         .map(|digs| {
//!             let mut n = 0;
//!             for d in digs {
//!                 n *= 10;
//!                 n += d;
//!             }
//!             n
//!         });
//!     match p.parse(input) {
//!         Ok((_, n)) => Some(n),
//!         Err(_)     => None,
//!     }
//! }
//!
//! assert_eq!(Some(123), parse_int("123"));
//! assert_eq!(Some(3), parse_int("3rest"));
//! assert_eq!(Some(30), parse_int("30rest"));
//! assert!(parse_int("no front number").is_none());
//! assert!(parse_int("").is_none());
//! ```
//! This works well enough, but is it *really* correct?
//! If an input string starts with an integer, but contains some more text after it, should it
//! still be considered valid?
//!
//! Perhaps, perhaps not.
//! But just for fun, let's modify this function to *only* return an integer when the string
//! contains no extra text.
//! We can do this with two more combinators.
//! To check that there is no text left after the integer, we can use [`eof`].
//! This special parser will succeed with a [`()`](unit) only if the input is empty.
//! But to make it work together with our integer parser, we'll need to combine them together
//! with [`plus`]:
//! ```
//! use bad_parsers::{Parser, eof, token_satisfies};
//!
//! fn parse_int(input: &str) -> Option<u32> {
//!     let p = token_satisfies(char::is_ascii_digit)
//!         .map(|c| c.to_digit(10).unwrap())
//!         .mult1()
//!         .map(|digs| {
//!             let mut n = 0;
//!             for d in digs {
//!                 n *= 10;
//!                 n += d;
//!             }
//!             n
//!         })
//!         .plus(eof());
//!     match p.parse(input) {
//!         Ok((_, (n, ()))) => Some(n),
//!         Err(_)           => None,
//!     }
//! }
//!
//! assert_eq!(Some(123), parse_int("123"));
//! assert!(parse_int("3rest").is_none());
//! assert!(parse_int("30rest").is_none());
//! assert!(parse_int("no front number").is_none());
//! assert!(parse_int("").is_none());
//! ```
//! Now only the first input is parsed successfully, as the two after it have trailing text.
//!
//! Also note that the returned value has changed types f-rom [`u32`] to [`(u32, ())`](tuple).
//! This is due to the use of `plus`, which will run two parsers in sequence, and return the
//! values of both when they both succeed, and fail completely unless both parsers succeed.
//!
//! Of course, in this situation we only care about the first value being returned, so we can
//! replace [`plus`] with a variant called [`left`], which works the same as [`plus`] but only
//! returns the first value:
//! ```
//! use bad_parsers::{Parser, eof, token_satisfies};
//!
//! fn parse_int(input: &str) -> Option<u32> {
//!     let p = token_satisfies(char::is_ascii_digit)
//!         .map(|c| c.to_digit(10).unwrap())
//!         .mult1()
//!         .map(|digs| {
//!             let mut n = 0;
//!             for d in digs {
//!                 n *= 10;
//!                 n += d;
//!             }
//!             n
//!         })
//!         .left(eof());
//!     match p.parse(input) {
//!         Ok((_, n)) => Some(n),
//!         Err(_)     => None,
//!     }
//! }
//!
//! assert_eq!(Some(123), parse_int("123"));
//! assert!(parse_int("3rest").is_none());
//! assert!(parse_int("30rest").is_none());
//! assert!(parse_int("no front number").is_none());
//! assert!(parse_int("").is_none());
//! ```
//! Now the code is a little bit cleaner. Thanks [`left`]!
//!
//! As you can see, our humble parser combinators have been able to solve a long-standing
//! computer science problem, one that stumped Turing, Church, and even von Neumann!
//!
//! I really ought to submit this feature to the Rust development team.
//! The standard library could really make use of this-
//! ```
//! # use bad_parsers::{Parser, eof, token_satisfies};
//! # fn parse_int(input: &str) -> Option<u32> {
//! #     let p = token_satisfies(char::is_ascii_digit)
//! #         .map(|c| c.to_digit(10).unwrap())
//! #         .mult1()
//! #         .map(|digs| {
//! #             let mut n = 0;
//! #             for d in digs {
//! #                 n *= 10;
//! #                 n += d;
//! #             }
//! #             n
//! #         })
//! #         .left(eof());
//! #     match p.parse(input) {
//! #        Ok((_, n)) => Some(n),
//! #        Err(_)     => None,
//! #    }
//! # }
//! let x: u32 = parse_int("123").unwrap();
//!
//! let y: u32 = str::parse("123").unwrap();
//!
//! assert_eq!(x, y);
//! assert_ne!("time taken", "well-spent");
//! ```
//! Oh.
use std::fmt::{self, Debug};
use std::marker::PhantomData;
use std::ops::{Add, BitOr, Bound, Deref, Mul, RangeBounds, Shl, Shr};

#[derive(Debug)]
enum ErrorType<Toks> {
    NoParse {
        loc: Toks,
    },
    EmptyInput,
    UnexpectedInput {
        loc: Toks,
    },
    Flunk {
        loc: Toks,
    },
    NotEnough {
        loc: Toks,
        needed: usize,
        got: usize,
    },
    Other {
        cause: Box<dyn std::error::Error>,
        loc: Toks,
    },
}

/// The `Err` type of [`ParseResult`].
///
/// Instances of this struct are returned by parsers when they are unsuccessful.
///
/// This type provides various functions and methods for the creation and modification of
/// error values.
/// It is not advised to create values of [`ParseError`] without one of the provided constructor
/// functions, nor to pattern-match or destructure this type.
/// The reason as to why this is the case is ~~because Rust is a temperamental pile of
/// garbage~~ due to some quirks with Rust's type system.
///
/// Constructing different kinds of errors with this type will require providing differing
/// amounts of information depending on the specificity of the error type.
/// An error type like [`ParseError::not_enough`] requires providing extra information related
/// to the number of parsed elements, while [`ParseError::empty_input`] requires no extra
/// information at all.
/// The two most common values to give a constructor are:
/// * `details`: a `&str` providing extra human-readable information about this specific failure
/// * `loc` a `Toks` providing the input that the parser failed to parse from
///
/// When providing `details`, the information should be relevant to the specific parser in
/// your parser chain.
/// For example, if a parser looking for a single digit is just a wrapped around
/// [`token_satisfies`], and the error message is not modified, the parser will return a
/// generic error message that a predicate failed.
///
/// Example of providing a useful message via [`map_error`]:
/// ```
/// use bad_parsers::{Parser, ParseError, Tokens, token_satisfies};
///
/// let digit = token_satisfies(char::is_ascii_digit)
///     .map_error(|e: ParseError<&str, char>| {
///         if let Some(input) = e.get_loc_non_empty() {
///             let c = input.take_one().unwrap().1;
///             ParseError::no_parse(
///                 &format!("expected a digit, but found: {:?}", c),
///                 input,
///             )
///         } else {
///             ParseError::empty_input()
///         }
///     });
/// ```
#[derive(Debug)]
pub struct ParseError<Toks, T> {
    error_type: ErrorType<Toks>,
    details: Option<String>,
    _phantom: PhantomData<T>,
}

impl<Toks, T> ParseError<Toks, T> {
    /// Signals that a parser has failed to parse due to the input ending sooner than expected.
    pub fn empty_input() -> Self {
        Self {
            error_type: ErrorType::EmptyInput,
            details: None,
            _phantom: PhantomData,
        }
    }

    /// Signals that a parser has failed to parse because it expected the input to be empty,
    /// but it was not.
    ///
    /// See also: [`eof`].
    pub fn unexpected_input(loc: Toks) -> Self
    where
        Toks: Tokens<T>,
        T: Clone + Debug,
    {
        Self {
            error_type: ErrorType::UnexpectedInput { loc },
            details: None,
            _phantom: PhantomData,
        }
    }

    /// Signals that a parser has failed intentionally.
    ///
    /// See also: [`flunk`], [`flunk_with`].
    pub fn flunk(details: &str, loc: Toks) -> Self
    where
        Toks: Tokens<T>,
        T: Clone + Debug,
    {
        Self {
            error_type: ErrorType::Flunk { loc },
            details: Some(details.to_owned()),
            _phantom: PhantomData,
        }
    }

    /// Signals that a parser has failed to parse whatever it was trying to parse.
    ///
    /// This variant is intended to be the generic failure type.
    /// When you need your parser to fail and you are unsure of which error type to use, you
    /// should probably use this one.
    pub fn no_parse(details: &str, loc: Toks) -> Self
    where
        Toks: Tokens<T>,
        T: Clone + Debug,
    {
        Self {
            error_type: ErrorType::NoParse { loc },
            details: Some(details.to_owned()),
            _phantom: PhantomData,
        }
    }

    /// Signals that a parser has failed due to being unable to parse as many elements as it
    /// should have.
    ///
    /// This variant is intended to be used by parsers that repeatedly run *a single, specific
    /// parser* in order to collect multiple elements.
    ///
    /// See also: [`at_least`], [`in_range`], [`mult1`], [`sep_by`].
    pub fn not_enough(loc: Toks, needed: usize, got: usize) -> Self
    where
        Toks: Tokens<T>,
        T: Clone + Debug,
    {
        Self {
            error_type: ErrorType::NotEnough { loc, needed, got },
            details: None,
            _phantom: PhantomData,
        }
    }

    /// Signals that a parser has failed due to a non-specific reason.
    ///
    /// This variant is intended to be used when parsing was not successful due to factors
    /// outside of the parsing chain, such as [I/O errors](std::io::Error).
    /// A more robust system of forwarding arbitrary error types may be implemented in the
    /// future.
    ///
    /// If your parser simply fails to parse, but not for any of the reasons associated with
    /// the other variants, you should use [`ParseError::no_parse`], not this.
    pub fn other<E: std::error::Error + 'static>(cause: E, loc: Toks) -> Self {
        Self {
            error_type: ErrorType::Other { cause: Box::new(cause), loc },
            details: None,
            _phantom: PhantomData,
        }
    }

    /// Returns the specific details of this failure, if there are any.
    pub fn get_details(&self) -> Option<&str> {
        self.details.as_deref()
    }

    /// Overwrites the specific details of this failure.
    pub fn set_details(&mut self, msg: &str) {
        self.details = Some(msg.to_owned());
    }

    /// Returns the input that was unable to be parsed from.
    ///
    /// Not all error types are able to provide a meaningful input state to report, hence why
    /// this function returns an [`Option`].
    ///
    /// **Caution:** the above statement implies that if this error *does* contain an input
    /// state, then the input should also be non-empty.
    /// However, this should not be assumed to always be true, and this method makes no such
    /// guarantee.
    ///
    /// If your error reporting requires a non-empty input to refer to, consider using
    /// [`ParseError::get_loc_non_empty`] instead.
    pub fn get_loc(&self) -> Option<Toks>
    where
        Toks: Clone + Copy,
    {
        match self.error_type {
            ErrorType::EmptyInput => None,
            ErrorType::UnexpectedInput { loc }
            | ErrorType::Flunk { loc }
            | ErrorType::NoParse { loc }
            | ErrorType::NotEnough { loc, .. }
            | ErrorType::Other { loc, .. } => Some(loc),
        }
    }

    /// Returns the non-empty input that was unable to be parsed from.
    ///
    /// Not all error types are able to provide a meaningful input state to report, hence why
    /// this function returns an [`Option`].
    ///
    /// The input states returned by this method are guaranteed to be non-empty.
    ///
    /// If your error reporting does not require the input to be non-empty, you may wish to use
    /// [`ParseError::get_loc`] instead.
    pub fn get_loc_non_empty(&self) -> Option<Toks>
    where
        Toks: Tokens<T>,
        T: Clone + Debug,
    {
        match self.get_loc() {
            Some(loc) if !loc.no_tokens() => Some(loc),
            _ => None,
        }
    }

    /// Returns whether or not this error was caused by another (non-parsing related) error.
    ///
    /// If this returns `true`, a parser should not attempt to recover from this error.
    /// This is because the parsing will have failed not due to parser failure, but by being
    /// interrupted by another class of error that should be handled
    /// outside of the parser chain.
    ///
    /// See also: [`Parser::map_error`].
    pub fn caused_by_other(&self) -> bool {
        match self.error_type {
            ErrorType::Other { .. } => true,
            _ => false,
        }
    }
}

// Safety:
// Data types across all variants of ErrorType<Toks>
// * usize: Sync+Send
// * Box<dyn Error>: Sync+Send implemented by Box<T>
// * Toks: Sync+Send if enforced by trait bound
// ErrorType<Toks> can implement Sync+Send IF: Toks: Sync+Send
//
// Composition of ParseError<Toks, T>
// * error_type: ErrorType<Toks>: Send+Snc as established above
// * details: String: Sync+Send
// * _phantom: PhantomData<T>: Sync+Send IF T: Sync+Send
// ParseError<Toks, T> can implement Sync+Send IF Toks: Sync+Send AND T: Sync+Send
unsafe impl<Toks, T> Sync for ParseError<Toks, T>
where
    Toks: Sync,
    T: Send,
{}
unsafe impl<Toks, T> Send for ParseError<Toks, T>
where
    Toks: Send,
    T: Send,
{}

impl<Toks, T> fmt::Display for ParseError<Toks, T>
where
    Toks: Tokens<T>,
    T: Clone + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let details = match self.get_details() {
            Some(d) => d,
            None => "(no extra information available)",
        };
        match self.error_type {
            ErrorType::EmptyInput => {
                write!(f, "Parser was expecting more input, but there was none")
            }
            ErrorType::UnexpectedInput { loc } => {
                write!(
                    f,
                    "Parser expected no more input, but found: {}",
                    loc.preview()
                )
            }
            ErrorType::Other { loc, .. } => {
                write!(
                    f,
                    "An error occurred while parsing, Failed at: {}",
                    loc.preview()
                )
            }
            ErrorType::Flunk { loc } => {
                write!(
                    f,
                    "Parser flunked: {}, Flunked at: {}",
                    details,
                    loc.preview()
                )
            }
            ErrorType::NoParse { loc } => {
                write!(
                    f,
                    "Parser was unsuccessful: {}, Failed at: {}",
                    details,
                    loc.preview()
                )
            }
            ErrorType::NotEnough { loc, needed, got } => {
                write!(
                    f,
                    "Parser needed to parse {} elements, but only parsed {}: {}, Failed at: {}",
                    needed,
                    got,
                    details,
                    loc.preview()
                )
            }
        }
    }
}

impl<Toks, T> std::error::Error for ParseError<Toks, T>
where
    Toks: Tokens<T> + Debug,
    T: Clone + Debug,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let ErrorType::Other { cause, .. } = &self.error_type {
            cause.source()
        } else {
            None
        }
    }
}

/// The `Result` type returned by parsers.
///
/// A successful parser will return the remaining input as well as the value that was parsed.
/// A failed parser will return a [`ParseError`] detailing why the parser failed.
pub type ParseResult<'a, Toks, T, A> = Result<(Toks, A), ParseError<Toks, T>>;

/// Interface for collections of tokens.
///
/// Unless you need something more specific (e.g., methods that only [`&str`] implements), this
/// should be the only way you would need to work with inputs in custom parsers.
///
/// ## How to implement this trait
///
/// Don't. Just convert whatever input you need to parse into a slice and you're good to go.
///
/// ### But I wanna!
///
/// Fine.
///
/// A type may implement this trait if it has the following properties:
///
/// * it can be treated as a collection of other values (`T`) with a deterministic order
/// * it has a notion of being empty
/// * it has a notion of taking a single value from the 'front' of the collection, *immutably*
///
/// This trait is designed to be easy to implement for fat pointer types like [`&str`] and
/// [`&[T]`](slice).
/// This is because taking a token from the collection can be implemented as cloning the
/// first element, then returning it along with a re-sized pointer that omits that element.
///
/// For the above reason, implementing this trait for non-reference types is not encouraged,
/// hence the `Self: Deref` constraint.
/// The `Self: Copy + Clone` constraints are also added to allow for the copy semantics that
/// reference types have, as Rust cannot prove that a [`Deref`] can usually also be copied.
///
/// ## Why do we need `T: Clone`?
///
/// The `T: Clone` constraint is required to ensure that we can work with inputs immutably.
/// This is mandated by this library because parsers may be tasked with operating on the same
/// inputs, which could cause parsers to consume input that others may need access to.
///
/// For example, consider two parsers that operate on [`&str`].
/// The first parser is looking for the word `"food"`, and the other is looking for the
/// word `"fool"`.
/// Suppose that both parsers are implemented by checking each character in the input one at
/// a time:
/// ```txt
/// invoking food_p.parse("food"):
///
/// status   | remaining input
/// --------------------------
/// 'f' - ok | "food"
/// 'o' - ok | "ood"
/// 'o' - ok | "od"
/// 'd' - ok | "d"
///  success | ""
///
/// invoking food_p.parse("fool"):
///
/// status    | remaining input
/// ---------------------------
/// 'f' - ok  | "fool"
/// 'o' - ok  | "ool"
/// 'o' - ok  | "ol"
/// 'l' - err | "l"
///  failed   | "l"
///
/// results for these inputs with the fool_p parser are left as an exercise for the reader
/// ```
/// Now suppose we combine these two parsers into a parser that tries to parse `"food"`
/// *or* `"fool"`, in that order.
/// Remember that in these hypotheticals, the input data is being mutated:
/// ```txt
/// food_or_fool = food_p.or(fool_p)
///
/// invoking food_or_fool.parse("food"):
///
/// status          | remaining input
/// ---------------------------------
/// trying p_food   | "food"
/// 'f' - ok        | "food"
/// 'o' - ok        | "ood"
/// 'o' - ok        | "od"
/// 'd' - ok        | "d"
///  success (food) | ""
/// ```
/// The implementation seems to work fine, but watch what happens when it tries to parse
/// `"fool"`:
/// ```txt
/// invoking food_or_fool.parse("fool"):
///
/// status        | remaining input
/// -------------------------------
/// trying p_food | "fool"
/// 'f' - ok      | "fool"
/// 'o' - ok      | "ool"
/// 'o' - ok      | "ol"
/// 'l' - err     | "l"
/// trying p_fool | "l"
/// 'f' - err     | "l"
/// failed        | "l"
/// ```
/// Even though the input should have been parsed by the parser that was looking for `"fool"`,
/// the modification of the input took away the data that it was looking for.
///
/// This problem is resolved when the sub-parsers are given the same starting inputs:
/// ```txt
/// invoking food_or_fool.parse("fool"):
///
/// status         | remaining input
/// --------------------------------
/// trying p_food  | "fool"
/// 'f' - ok       | "fool"
/// 'o' - ok       | "ool"
/// 'o' - ok       | "ol"
/// 'l' - err      | "l"
/// trying p_fool  | "fool"
/// 'f' - ok       | "fool"
/// 'o' - ok       | "ool"
/// 'o' - ok       | "ol"
/// 'l' - ok       | "l"
/// success (fool) | ""
/// ```
/// Some other parser combinator libraries (such as Haskell's
/// [Parsec](https://hackage.haskell.org/package/parsec)) fix this issue by requiring the
/// programmer to explicitly mark where the input should be preserved in the event of
/// parser failure.
/// This library instead opts to *always* preserve the input for the convienience of the
/// programmer, at the cost of not being as performant.
/// If your project cannot afford to take this performance hit,
/// you should probably ~~just use C~~ look for a more suitable parsing solution.
pub trait Tokens<T>
where
    Self: Sized + Deref + Copy + Clone,
    T: Clone + Debug,
{
    /// Attempts to take a single token from the collection.
    ///
    /// When implementing this trait, this method *must not* mutate `self`, as other parsers
    /// rely on token data remaining unmodified between parsers.
    /// To get a better idea of what your implementation of this method should look like, you may
    /// refer to the [`&str`](#impl-Tokens<char>-for-%26str) and
    /// [`&[T]`](#impl-Tokens<T>-for-%26[T]) implementations.
    fn take_one(self) -> Option<(Self, T)>;

    /// Returns `true` if this token collection is empty.
    ///
    /// When implementing this trait, there is usually an `is_empty` method for your container
    /// that you can use here.
    fn no_tokens(&self) -> bool;

    /// Returns a preview of the front of the token stream.
    ///
    /// This method is used for error reporting.
    fn preview(&self) -> String;
}

impl<'a> Tokens<char> for &'a str {
    fn take_one(self) -> Option<(&'a str, char)> {
        self.chars().next().map(|c| (&self[c.len_utf8()..], c))
    }

    fn no_tokens(&self) -> bool {
        self.is_empty()
    }

    fn preview(&self) -> String {
        let mut preview_end: usize = 35;

        if self.len() <= preview_end {
            return format!("\"{}\"", &self);
        }

        // if the ending index if partway through a character,
        // move it backwards until it isn't
        while !self.is_char_boundary(preview_end) {
            preview_end -= 1;
        }

        format!("\"{} ...\"", &self[..preview_end])
    }
}

impl<'a, T> Tokens<T> for &'a [T]
where
    T: Clone + Debug,
{
    fn take_one(self) -> Option<(&'a [T], T)>
    where
        T: 'a,
    {
        self.iter().next().map(|t| (&self[1..], t.clone()))
    }

    fn no_tokens(&self) -> bool {
        self.is_empty()
    }

    fn preview(&self) -> String {
        let preview_end: usize = 8;
        format!("{:?}", &self[..preview_end])
    }
}

/// Interface for working with parser objects
///
/// A type can implement this trait and/or be treated as a parser if it contains a function/closure
/// with the signature of the [`parse`](Parser::parse) method of this trait:
/// `Fn(Toks) -> ParseResult<'a, Toks, A>`. The following constraints also apply to the type
/// arguments of *all* parsers:
/// * `'a` - lifetime of the parser, its input, and its output.
/// * `Toks: Tokens<T> + 'a` - the type of the input token container.
/// * `T: Clone` - the type of the individual tokens contained within `Toks`.
/// * `A: 'a` - the type of what this parser tries to parse.
///
/// Please note that the constraints listed here are only the most fundamental constraints.
/// Other functions in this library will usually require other constraints to be satisfied
/// in order for them to work properly.
/// Please see the documentation for the [`Tokens<T>`] trait for more information about the
/// constraints of parser inputs.
///
/// The majority of the trait functions of [`Parser`] do not actually provide any unique
/// functionality and are simply alternate ways of using some of the combinator functions
/// provided by this library.
/// These associated functions exist to allow for syntactically-different ways to define a given
/// parser, which allows programmers to choose the way that reads best to them.
/// ```
/// use bad_parsers::{Parser, token, plus};
///
/// // These behave identically
/// let p1 = plus(token('a'), token('b'));
/// let p2 = token('a').plus(token('b'));
///
/// let r1 = p1.parse("abcd");
/// let r2 = p2.parse("abcd");
/// assert_eq!(r1.unwrap(), r2.unwrap());
/// ```
/// An issue you may encounter when parsing from non-static inputs is that, depending on how your
/// code is organized, the compiler may determine your input will not live long enough for your
/// parser to parse from it:
/// ```compile_fail
/// /* This example does not compile. */
/// use bad_parsers::{Parser, any_token};
///
/// // Parser defined first
/// let two_tokens = any_token().plus(any_token());
///
/// // Input defined second, will not live long enough
/// let nums = [1, 2, 3, 4, 5, 6];
/// let nums_slice = nums.as_slice();
///
/// assert_eq!((&nums_slice[2..], (1, 2)), two_tokens.parse(nums_slice).unwrap());
/// ```
/// Trying to compile the above code will produce an error that looks somthing like this:
/// ```txt
/// error[E0597]: `nums` does not live long enough
///   --> src/lib.rs:581:18
///    |
/// 11 | let nums = [1, 2, 3, 4, 5, 6];
///    |     ---- binding `nums` declared here
/// 12 | let nums_slice = nums.as_slice();
///    |                  ^^^^ borrowed value does not live long enough
/// ...
/// 15 | } _doctest_main_src_lib_rs_572_0() }
///    | -
///    | |
///    | `nums` dropped here while still borrowed
///    | borrow might be used here, when `two_tokens` is dropped and runs the destructor for type `impl Parser<'_, &[i32], i32, (i32, i32)>`
///    |
///    = note: values in a scope are dropped in the opposite order they are defined
///
/// For more information about this error, try `rustc --explain E0597`.
/// ```
/// Thankfully, the solution to this issue is very simple: just define the parser *after* the
/// input:
/// ```
/// /* Fixed version of previous example. */
/// use bad_parsers::{Parser, any_token};
///
/// // Input defined second, will now live long enough
/// let nums = [1, 2, 3, 4, 5, 6];
/// let nums_slice = nums.as_slice();
///
/// // Parser defined second
/// let two_tokens = any_token().plus(any_token());
///
/// assert_eq!((&nums_slice[2..], (1, 2)), two_tokens.parse(nums_slice).unwrap());
/// ```
pub trait Parser<'a, Toks, T, A>
where
    Toks: Tokens<T>,
    T: Clone + Debug,
{
    /// Attempt to parse from the given input.
    fn parse(&self, input: Toks) -> ParseResult<'a, Toks, T, A>;

    /// Put `Self` into a [`BoxedParser`].
    fn boxed(self) -> BoxedParser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        T: 'a,
        A: 'a,
    {
        BoxedParser::new(self)
    }

    /// Method version of [`map_error`].
    fn map_error<F>(self, f: F) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        F: Fn(ParseError<Toks, T>) -> ParseError<Toks, T> + 'a,
    {
        map_error(self, f)
    }

    /// Method version of [`and_then`].
    fn and_then<F, Q, B>(self, f: F) -> impl Parser<'a, Toks, T, B>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        F: Fn(A) -> Q + 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        and_then(self, f)
    }

    /// Method version of [`map`]
    fn map<F, B>(self, f: F) -> impl Parser<'a, Toks, T, B>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        F: Fn(A) -> B + 'a,
        B: 'a,
    {
        map(self, f)
    }

    /// Method version of [`ignore`]
    fn ignore(self) -> impl Parser<'a, Toks, T, ()>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        ignore(self)
    }

    /// Method version of [`convert`]
    fn convert<B>(self) -> impl Parser<'a, Toks, T, B>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: Into<B> + 'a,
        B: 'a,
    {
        convert(self)
    }

    /// Method version of [`replace`]
    fn replace<B>(self, value: B) -> impl Parser<'a, Toks, T, B>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        B: Clone + 'a,
    {
        replace(self, value)
    }

    /// Method version of [`or`]
    fn or<Q>(self, other: Q) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        Q: Parser<'a, Toks, T, A> + 'a,
    {
        or(self, other)
    }

    /// Method version of [`recover`]
    fn recover(self, value: A) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        T: 'a, // TODO: lifetime oddity
        A: Clone + 'a,
    {
        recover(self, value)
    }

    /// Method version of [`recover_default`]
    fn recover_default(self) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        T: 'a, // TODO: lifetime oddity
        A: Default + 'a,
    {
        recover_default(self)
    }

    /// Method version of [`optional`]
    fn optional(self) -> impl Parser<'a, Toks, T, Option<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        optional(self)
    }

    /// Method version of [`ensure`]
    fn ensure<F>(self, f: F) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        F: Fn(&A) -> bool + 'a,
    {
        ensure(self, f)
    }

    /// Method version of [`reject`]
    fn reject<F>(self, f: F) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        F: Fn(&A) -> bool + 'a,
    {
        reject(self, f)
    }

    /// Method version of [`plus`]
    fn plus<Q, B>(self, other: Q) -> impl Parser<'a, Toks, T, (A, B)>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        plus(self, other)
    }

    /// Method version of [`left`]
    fn left<Q, B>(self, other: Q) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        T: 'a, // TODO: lifetime oddity
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        left(self, other)
    }

    /// Method version of [`right`]
    fn right<Q, B>(self, other: Q) -> impl Parser<'a, Toks, T, B>
    where
        Self: Sized + 'a,
        Toks: 'a,
        T: 'a, // TODO: lifetime oddity
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        right(self, other)
    }

    /// Method version of [`in_range`]
    fn in_range<R>(self, range: R) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        R: RangeBounds<usize> + 'a,
    {
        in_range(self, range)
    }

    /// Method version of [`mult`]
    fn mult(self) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        mult(self)
    }

    /// Method version of [`mult1`]
    fn mult1(self) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        mult1(self)
    }

    /// Method version of [`exactly`]
    fn exactly(self, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        exactly(self, n)
    }

    /// Method version of [`at_least`]
    fn at_least(self, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        at_least(self, n)
    }

    /// Method version of [`at_most`]
    fn at_most(self, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
    {
        at_most(self, n)
    }

    /// Method version of [`sep_by`]
    fn sep_by<Q, B>(self, other: Q) -> impl Parser<'a, Toks, T, Vec<A>>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        sep_by(self, other)
    }

    /// Method version of [`within`]
    fn within<Q, B>(self, other: Q) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
    {
        within(self, other)
    }

    /// Method version of [`between`]
    fn between<Q, B, R, C>(self, left: Q, right: R) -> impl Parser<'a, Toks, T, A>
    where
        Self: Sized + 'a,
        Toks: 'a,
        A: 'a,
        Q: Parser<'a, Toks, T, B> + 'a,
        B: 'a,
        R: Parser<'a, Toks, T, C> + 'a,
        C: 'a,
    {
        between(self, left, right)
    }
}

/// Allows functions/closures with the appropriate signature to act as parsers.
///
/// ## Examples
/// ```
/// use bad_parsers::{Tokens, Parser, ParseResult, ParseError};
///
/// // This function can be treated as a parser directly
/// fn take_one<'a, Toks, T>(input: Toks) -> ParseResult<'a, Toks, T, T>
/// where
///     Toks: Tokens<T> + 'a,
///     T: Clone + std::fmt::Debug,
/// {
///     match input.take_one() {
///         Some((rest, t)) => Ok((rest, t)),
///         None => Err(ParseError::empty_input()),
///     }
/// }
///
/// // This function builds a closure which can in turn be treated as a parser
/// fn token<'a, Toks, T>(find: T) -> impl Parser<'a, Toks, T, T>
/// where
///     Toks: Tokens<T> + 'a,
///     T: Clone + std::fmt::Debug + Eq + 'a,
/// {
///     move |input: Toks| match input.take_one() {
///         Some((rest, t)) => {
///             if t == find {
///                 Ok((rest, t))
///             } else {
///                 Err(ParseError::no_parse(
///                     &format!("could not find token '{:?}'", find),
///                     input
///                 ))
///             }
///         }
///         None => Err(ParseError::empty_input()),
///     }
/// }
///
/// assert_eq!(("bcd", 'a'), take_one.parse("abcd").unwrap());
/// assert_eq!(("bcd", 'a'), token('a').parse("abcd").unwrap());
/// ```
impl<'a, Toks, T, A, F> Parser<'a, Toks, T, A> for F
where
    F: Fn(Toks) -> ParseResult<'a, Toks, T, A> + 'a,
    Toks: Tokens<T>,
    T: Clone + Debug,
{
    fn parse(&self, input: Toks) -> ParseResult<'a, Toks, T, A> {
        self(input)
    }
}

/// Container for heap-allocated parsers.
///
/// The primary purpose of this struct is to wrap an opaque parser type when Rust complains about
/// opaque type mismatches.
///
/// Additionally, this struct also implements [`Parser`], so it can be cleanly given to functions
/// that expect a parser, rather than having to manually work around the type differences when
/// directly using a [`Box<dyn Parser<'a, Toks, T, A> + 'a>`](Box).
pub struct BoxedParser<'a, Toks, T, A> {
    parser: Box<dyn Parser<'a, Toks, T, A> + 'a>,
}

impl<'a, Toks, T, A> BoxedParser<'a, Toks, T, A> {
    /// Move the given [`Parser`] into a [`BoxedParser`].
    pub fn new<P>(p: P) -> Self
    where
        Self: Sized + 'a,
        Toks: Tokens<T> + 'a,
        T: Clone + Debug,
        A: 'a,
        P: Parser<'a, Toks, T, A> + 'a,
    {
        BoxedParser {
            parser: Box::new(p),
        }
    }
}

/// Allows for [`Parser`] functionality via the wrapped parser object.
impl<'a, Toks, T, A> Parser<'a, Toks, T, A> for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T>,
    T: Clone + Debug,
{
    fn parse(&self, input: Toks) -> ParseResult<'a, Toks, T, A> {
        self.parser.parse(input)
    }

    // this is already a BoxedParser,
    // no need to re-box it
    fn boxed(self) -> BoxedParser<'a, Toks, T, A> {
        self
    }
}

/// Allows use of the `+` operator in place of [`plus`].
impl<'a, Toks, T, A, B> Add<BoxedParser<'a, Toks, T, B>> for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    A: 'a,
    B: 'a,
{
    type Output = BoxedParser<'a, Toks, T, (A, B)>;

    fn add(self, rhs: BoxedParser<'a, Toks, T, B>) -> Self::Output {
        self.plus(rhs).boxed()
    }
}

/// Allows use of the `<<` operator in place of [`left`].
impl<'a, Toks, T, A, B> Shl<BoxedParser<'a, Toks, T, B>> for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    A: 'a,
    B: 'a,
{
    type Output = Self;

    fn shl(self, rhs: BoxedParser<'a, Toks, T, B>) -> Self::Output {
        self.left(rhs).boxed()
    }
}

/// Allows use of the `>>` operator in place of [`right`].
impl<'a, Toks, T, A, B> Shr<BoxedParser<'a, Toks, T, B>> for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    A: 'a,
    B: 'a,
{
    type Output = BoxedParser<'a, Toks, T, B>;

    fn shr(self, rhs: BoxedParser<'a, Toks, T, B>) -> Self::Output {
        self.right(rhs).boxed()
    }
}

/// Allows use of the `*` operator in place of [`exactly`].
impl<'a, Toks, T, A> Mul<usize> for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    A: 'a,
{
    type Output = BoxedParser<'a, Toks, T, Vec<A>>;

    fn mul(self, rhs: usize) -> Self::Output {
        self.exactly(rhs).boxed()
    }
}

/// Allows use of the `|` operator in place of [`or`].
impl<'a, Toks, T, A> BitOr for BoxedParser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    A: 'a,
{
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        self.or(other).boxed()
    }
}

/// Creates a [`Parser`] that tries to parse with all of the argument parsers.
///
/// This macro acts as a shorthand for chaining many individual parsers together with [`or`].
/// As such, the parser created from this macro will attempt to parse the input with each
/// [`Parser`] it was provided with, *in the order they were given*.
/// The first time a parser succeeds, this parser will return that result.
/// If none of the parsers succeed, then this parser will fail.
/// Currently this parser does not specifically provide an error implying it was created from
/// this macro, though this is subject to change.
///
/// **Note:** if any of the provided parsers produce an error value created with the
/// [`ParseError::other`] function before any of the parsers are successful, this parser will
/// *not* attempt to parse with the remaining parsers and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// This macro requires at least two parser arguments to be invoked. This restriction exists
/// partly for type-checking reasons, but primarily becuase trying to use this macro with
/// less than two parsers would be unusual, and it is unclear what kind of parser the macro
/// should even produce in such a situation.
///
/// It also gave me a name error while I was testing the single-parser case, which as far as
/// I'm concerned is a capital offense.
///
/// See also: [`or`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, first_of, string};
///
/// let p = first_of![string("abc"), string("ab"), string("a")];
///
/// assert_eq!(("", "abc"), p.parse("abc").unwrap());
/// assert_eq!(("x", "ab"), p.parse("abx").unwrap());
/// assert_eq!(("xy", "a"), p.parse("axy").unwrap());
/// assert!(p.parse("no matches here").is_err());
/// ```
#[macro_export]
macro_rules! first_of {
    ($h:expr, $($p:expr),+ $(,)?) => {
        $h
            $( .or($p) )+
    };
}

/// Creates a lazily-evaluated parser from another parser-building function.
///
/// This implementation works by moving the builder function `f` into a closure,
/// which is in turn treated as a parser.
/// Each time that parser is run, it builds a parser with `f` and passes it the input.
/// The result from that parser is then returned, success or failure.
///
/// Using parsers lazily can sometimes improve performance, but the primary reason this function
/// exists is to allow for parsers with recursive definitions.
/// Without lazy evaluation, attempting to recursively define a parser will cause an
/// infinite loop.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, BoxedParser, lazy, token};
///
/// // This example repeatedly parses 'a' until it encounters a 'b'.
/// // Incidentally, it also has to be boxed due to conflicting opaque types.
/// fn recursive_parser<'a>() -> BoxedParser<'a, &'a str, char, char> {
///     token('b')
///         .or(token('a').right(lazy(recursive_parser)))
///         .boxed()
/// }
///
/// // Without lazy evaluation, instantiating
/// // this parser would cause an infinite loop.
/// let p = recursive_parser();
///
/// assert!(p.parse("c").is_err());
/// assert_eq!(("", 'b'), p.parse("b").unwrap());
/// assert_eq!(("", 'b'), p.parse("ab").unwrap());
/// assert_eq!(("", 'b'), p.parse("aaab").unwrap());
/// ```
pub fn lazy<'a, Toks, T, A, F, P>(f: F) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    F: Fn() -> P + 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    move |input| f().parse(input)
}

/// Changes the given parser's error value with the provided function.
///
/// This function provides another option for modifying the error values of failed parsers, as
/// using a function like this may be more convinient than manually matching against
/// [`ParseResult`]s.
///
/// **Note:** this function explicitly prohibits the modification/replacement of error values
/// created with the [`ParseError::other`] function, as such errors were caused by factors
/// outside of the parser chain. However, this function does not prohibit the creation of
/// such error values.
///
/// See also: [`ParseError`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, ParseError, token};
///
/// let p1 = token('a');
/// let p2 = token('a').map_error(|mut e| {
///     e.set_details("custom message");
///     e
/// });
///
/// // Fails with default error message
/// let expected1 = "Parser was unsuccessful: predicate of ensure failed, Failed at: \"b\"";
/// let msg1 = p1.parse("b").unwrap_err().to_string();
/// // Fails with custom error message
/// let expected2 = "Parser was unsuccessful: custom message, Failed at: \"b\"";
/// let msg2 = p2.parse("b").unwrap_err().to_string();
///
/// assert_eq!(expected1, msg1);
/// assert_eq!(expected2, msg2);
/// ```
pub fn map_error<'a, Toks, T, A, P, F>(p: P, f: F) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    P: Parser<'a, Toks, T, A> + 'a,
    F: Fn(ParseError<Toks, T>) -> ParseError<Toks, T> + 'a,
{
    let map_f = move |e: ParseError<Toks, T>| {
        // If this error was caused by an external error,
        // do not allow the user-provided function to modify it.
        if e.caused_by_other() {
            e
        } else {
            f(e)
        }
    };
    move |input| p.parse(input).map_err(&map_f)
}

/// Creates a parser that always succeeds and performs no meaningful operations.
///
/// ## Examples
/// ```
/// use bad_parsers::{Parser, identity};
///
/// let p = identity();
///
/// assert_eq!(("what did you expect?", ()), p.parse("what did you expect?").unwrap());
/// ```
pub fn identity<'a, Toks, T>() -> impl Parser<'a, Toks, T, ()>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
{
    move |input| Ok((input, ()))
}

/// Creates a parser that succeeds only on empty inputs.
///
/// This parser relies on the [`Tokens::no_tokens`] function to determine if the input is empty.
/// If the input is empty, it is left alone and the parser returns a [`()`](unit).
/// If the input is not empty, the parser fails.
///
/// This parser is typically used to assert that the entire input has been parsed.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, eof, token};
///
/// let p = token('a').left(eof());
///
/// assert_eq!(("", 'a'), p.parse("a").unwrap());
/// assert!(p.parse("a and some other stuff").is_err());
/// ```
pub fn eof<'a, Toks, T>() -> impl Parser<'a, Toks, T, ()>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
{
    move |input: Toks| {
        if input.no_tokens() {
            Ok((input, ()))
        } else {
            Err(ParseError::unexpected_input(input))
        }
    }
}

/// Creates a parser that always fails.
///
/// This parser will always fail regardless of the input.
///
/// Since it never actually returns a value, the return type of this parser can be
/// coerced into whatever is needed to make it fit in your parser chain.
///
/// It's usually a good idea to manually change the error of this parser into something
/// meaningful.
///
/// See also: [`flunk`], [`map_error`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, ParseError, flunk};
///
/// let p = flunk::<&str, char, ()>();
///
/// let msg1 = format!("Parser flunked: flunked parser, Flunked at: \"\"");
/// let msg2 = format!("Parser flunked: flunked parser, Flunked at: \"foo\"");
/// assert_eq!(msg1, p.parse("").unwrap_err().to_string());
/// assert_eq!(msg2, p.parse("foo").unwrap_err().to_string());
/// ```
pub fn flunk<'a, Toks, T, A>() -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
{
    |input| Err(ParseError::flunk("flunked parser", input))
}

/// Creates a parser that always fails with a specified error.
///
/// This parser will always fail regardless of the input.
///
/// Since it never actually returns a value, the return type of this parser can be
/// coerced into whatever is needed to make it fit in your parser chain.
///
/// This function can be used as a more conveinient way to create a failing parser with a custom
/// message than calling [`flunk`] and then [`map_error`].
///
/// See also: [`flunk`], [`map_error`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, ParseError, flunk_with};
///
/// let p = flunk_with::<&str, char, ()>("custom message");
///
/// let msg1 = format!("Parser flunked: custom message, Flunked at: \"\"");
/// let msg2 = format!("Parser flunked: custom message, Flunked at: \"foo\"");
/// assert_eq!(msg1, p.parse("").unwrap_err().to_string());
/// assert_eq!(msg2, p.parse("foo").unwrap_err().to_string());
/// ```
pub fn flunk_with<'a, Toks, T, A>(message: &'a str) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
{
    move |input| Err(ParseError::flunk(message, input))
}

/// Creates a parser that always succeeds with the given value.
///
/// When run, this parser will leave the input alone and instantly return a copy of the
/// given value.
///
/// `A` is required to implement [`Clone`] because the parser can run multiple times and must
/// be able to produce the same value each time.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, succeed};
///
/// let p = succeed(42);
///
/// assert_eq!(("", 42), p.parse("").unwrap());
/// assert_eq!(("foo", 42), p.parse("foo").unwrap());
/// ```
pub fn succeed<'a, Toks, T, A>(value: A) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: Clone + 'a,
{
    move |input| Ok((input, value.clone()))
}

/// Creates a parser that always succeeds with a default value.
///
/// When run, this parser will leave the input alone and instantly return the result of
/// `A::default`.
///
/// Naturally, `A` must implement [`Default`] in order to use this function.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, succeed_default};
///
/// let p = succeed_default::<&str, char, u32>();
/// let expected = u32::default();
///
/// assert_eq!(("", expected), p.parse("").unwrap());
/// assert_eq!(("foo", expected), p.parse("foo").unwrap());
/// ```
pub fn succeed_default<'a, Toks, T, A>() -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: Default + 'a,
{
    move |input| Ok((input, A::default()))
}

/// Turns the success value of the given parser into a new parser, then runs it.
///
/// This function behaves in a similar way to the `and_then` functions of other types such as
/// [`Result`] or [`Option`].
///
/// Parsers built with this combinator will first try to parse a value with `p`.
/// If `p` fails, then the whole parser fails.
/// If `p` succeeds, the parser will pass the parsed value into `f` to generate a new parser.
/// Then the parser will run that new parser on the rest of the input, succeeding or failing
/// based on what the new parser does.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, any_token, token};
///
/// // Parses any token if it occurs twice in a row, only returns one copy
/// let p = any_token().and_then(|t| token(t));
///
/// assert_eq!(("", 'a'), p.parse("aa").unwrap());
/// assert_eq!(("a", 'b'), p.parse("bba").unwrap());
/// assert!(p.parse("").is_err());
/// assert!(p.parse("ab").is_err());
/// ```
pub fn and_then<'a, Toks, T, A, P, F, Q, B>(p: P, f: F) -> impl Parser<'a, Toks, T, B>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    F: Fn(A) -> Q + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
{
    move |input1| p.parse(input1).and_then(|(input2, x)| f(x).parse(input2))
}

/// Alters the returned value of a successful parse with the given function.
///
/// This parser will first try to parse a value with `p`.
/// If `p` fails then the parser fails as normal.
/// If `p` succeeds, the parser will pass the parsed value into `f` and then return that value.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').map(u32::from);
///
/// assert_eq!(("", 97), p.parse("a").unwrap());
/// assert!(p.parse("b").is_err());
/// ```
pub fn map<'a, Toks, T, A, P, F, B>(p: P, f: F) -> impl Parser<'a, Toks, T, B>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    F: Fn(A) -> B + 'a,
{
    move |input| p.parse(input).map(|(rest, x)| (rest, f(x)))
}

/// Discards the returned value of a successful parse.
///
/// When `p` successfully parses a value, it is discarded and replaced with a [`()`](unit).
///
/// This can be used to simplify return types when the actual parsed value is not relevant.
///
/// Additionally, since [`()`](unit) is a zero-sized type, using this combinator may also
/// provide performance improvements.
///
/// Maybe?
///
/// I don't know, I'm just some guy with a laptop.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').ignore();
///
/// assert_eq!(("", ()), p.parse("a").unwrap());
/// assert!(p.parse("b").is_err());
/// ```
pub fn ignore<'a, Toks, T, A, P>(p: P) -> impl Parser<'a, Toks, T, ()>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    P: Parser<'a, Toks, T, A> + 'a,
{
    move |input1| {
        let (input2, _) = p.parse(input1)?;
        Ok((input2, ()))
    }
}

/// Alters the returned value of a successful parse with `A::into`.
///
/// When `p` successfully parses a value, it is converted from an `A` into a `B`.
///
/// Naturally, there must be an implementation of [`From<A>`] or [`Into<B>`] to use this
/// combinator.
/// Examples:
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').convert();
///
/// assert_eq!(("", 97_u32), p.parse("a").unwrap());
/// assert!(p.parse("b").is_err());
/// ```
pub fn convert<'a, Toks, T, A, P, B>(p: P) -> impl Parser<'a, Toks, T, B>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: Into<B> + 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    B: 'a,
{
    map(p, A::into)
}

/// Replaces the returned value of a successful parse with the given value.
///
/// When `p` successfully parses a value, it is replaced with another arbitrary value.
///
/// `B` is required to implement [`Clone`] because the parser can run multiple times and must
/// be able to produce the same value each time.
/// ## Examples:
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').replace(42);
///
/// assert_eq!(("", 42), p.parse("a").unwrap());
/// assert!(p.parse("b").is_err());
/// ```
pub fn replace<'a, Toks, T, A, P, B>(p: P, value: B) -> impl Parser<'a, Toks, T, B>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    B: Clone + 'a,
{
    map(p, move |_| value.clone())
}

/// Tries to parse with two different parsers of the same type.
///
/// Strictly speaking, the two parsers are probably going to have different types.
/// The important part is that they accept the same input type and return the same output type.
///
/// This parser will first attempt to parse a value with `p`.
/// If `p` succeeds, that value is returned.
/// If `p` fails, the parser will attempt to parse the same input with `q` and return whatever
/// the result of that is, success or fail.
///
/// **Note:** if the error value produced by `p` was created with the [`ParseError::other`]
/// function, this parser will *not* attempt to parse with `q`.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// When called directly, `p` will be used first and `q` second.
/// When called as a [method of `Parser`](Parser::or), the receiving parser (the `self`) is
/// used first and the `other` parser is used second.
///
/// This combinator may also be expressed with the `|` operator if **both** `p` and `q` are
/// [`BoxedParser`]s.
///
/// See also: [`first_of`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, string, token};
///
/// // will try to parse "ab" before "a"
/// let p = string("ab").or(string("a"));
///
/// assert_eq!(("", "ab"), p.parse("ab").unwrap());
/// assert_eq!(("c", "a"), p.parse("ac").unwrap());
/// assert!(p.parse("neither").is_err());
/// ```
pub fn or<'a, Toks, T, A, P, Q>(p: P, q: Q) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, A> + 'a,
{
    move |input| match p.parse(input) {
        Err(e) if e.caused_by_other() => Err(e),
        Err(_) => q.parse(input),
        ok => ok,
    }
}

/// Returns the given value when the given parser fails.
///
/// When `p` succeeds, the parser behaves as normal.
/// When `p` fails, instead of failing the whole parsing chain, it leaves the input alone and
/// returns `value`.
///
/// **Note:** if the error value produced by `p` was created with the [`ParseError::other`]
/// function, this parser will *not* return the provided value and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// `A` is required to implement [`Clone`] because the parser can run multiple times and will
/// need to produce the same value on each failed parse.
///
/// See also: [`optional`], [`recover_default`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').recover('_');
///
/// assert_eq!(("", 'a'), p.parse("a").unwrap());
/// assert_eq!(("", '_'), p.parse("").unwrap());
/// assert_eq!(("b", '_'), p.parse("b").unwrap());
/// ```
pub fn recover<'a, Toks, T, A, P>(p: P, value: A) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a, // TODO: figure out why rust complains about the lifetime here
    A: Clone + 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    or(p, succeed(value))
}

/// Returns a default value when the given parser fails.
///
/// When `p` succeeds, the parser behaves as normal.
/// When `p` fails, instead of failing the whole parsing chain, it leaves the input alone and
/// returns the result of `A::default`.
///
/// **Note:** if the error value produced by `p` was created with the [`ParseError::other`]
/// function, this parser will *not* return a default value and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// Naturally, `A` must implement [`Default`] to generate a default value.
///
/// See also: [`optional`], [`recover`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').map(u32::from).recover_default();
///
/// assert_eq!(("", 97), p.parse("a").unwrap());
/// assert_eq!(("", 0), p.parse("").unwrap());
/// assert_eq!(("b", 0), p.parse("b").unwrap());
/// ```
pub fn recover_default<'a, Toks, T, A, P>(p: P) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a, // TODO: same lifetime oddity as recover
    A: Default + 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    or(p, succeed_default())
}

/// Wraps the return value in an `Option`, allows parsing to continue on failure.
///
/// If `p` succeeds, the parser returns the value it normally would within a `Some`.
/// If `p` fails, instead of failing the whole parsing chain, it leaves the input alone and
/// returns a `None`.
///
/// **Note:** if the error value produced by `p` was created with the [`ParseError::other`]
/// function, this parser will *not* return a `None` value and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// See also: [`recover`], [`recover_default`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').optional();
///
/// assert_eq!(("", Some('a')), p.parse("a").unwrap());
/// assert_eq!(("", None), p.parse("").unwrap());
/// assert_eq!(("b", None), p.parse("b").unwrap());
/// ```
pub fn optional<'a, Toks, T, A, P>(p: P) -> impl Parser<'a, Toks, T, Option<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    move |input| match p.parse(input) {
        Ok((rest, x)) => Ok((rest, Some(x))),
        Err(e) if e.caused_by_other() => Err(e),
        Err(_) => Ok((input, None)),
    }
}

/// Fails the given parser if its return value does NOT pass the given predicate.
///
/// If `p` fails to parse as normal, then the parser fails.
/// If `p` succeeds, the parsed value is given to the predicate.
/// The value is then returned as normal if it passes the predicate.
/// If it fails the predicate, then the parser fails.
///
/// This combinator serves as a way to assert a particular condition of the parsed value that
/// would be impossible/inconvenient to check directly at the parsing step.
///
/// See also: [`reject`], [`token_satisfies`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, any_token};
///
/// let arr1 = [1, 2, 3, 4, 5];
/// let arr2 = [1, 2, 9, 4, 5];
///
/// let nums1 = &arr1[..];
/// let nums2 = &arr2[..];
///
/// // Parse an aribtrary sequence of ints, as long as they are *all* in ascending order.
/// let p = any_token().mult().ensure(|ns| ns.is_sorted());
///
/// assert_eq!((&nums1[5..], vec![1, 2, 3, 4, 5]), p.parse(nums1).unwrap());
/// assert!(p.parse(nums2).is_err());
/// ```
pub fn ensure<'a, Toks, T, A, P, F>(p: P, f: F) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    F: Fn(&A) -> bool + 'a,
{
    move |input| match p.parse(input) {
        Ok((rest, x)) if f(&x) => Ok((rest, x)),
        Ok(_) => Err(ParseError::no_parse("predicate of ensure failed", input)),
        Err(e) => Err(e),
    }
}

/// Fails the given parser if its return value DOES pass the given predicate.
///
/// If `p` fails to parse as normal, then the parser fails.
/// If `p` succeeds, the parsed value is given to the predicate.
/// The value is then returned as normal if it *fails* the predicate.
/// If it passes the predicate, then the parser fails.
///
/// This combinator serves as a way to assert a particular condition of the parsed value that
/// would be impossible/inconvenient to check directly at the parsing step.
///
/// See also: [`ensure`], [`token_satisfies`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, any_token};
///
/// let arr1 = [1, 2, 3, 4, 5];
/// let arr2 = [1, 2, 9, 4, 5];
///
/// let nums1 = &arr1[..];
/// let nums2 = &arr2[..];
///
/// // Parse an aribtrary sequence of ints, as long as they are *all* in ascending order.
/// let p = any_token().mult().reject(|ns| ns.is_sorted());
///
/// assert_eq!((&nums2[5..], vec![1, 2, 9, 4, 5]), p.parse(nums2).unwrap());
/// assert!(p.parse(nums1).is_err());
/// ```
pub fn reject<'a, Toks, T, A, P, F>(p: P, f: F) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    F: Fn(&A) -> bool + 'a,
{
    ensure(p, move |x| !f(x))
}

/// Parses with two parsers in series, returns both values.
///
/// This parser will first try to parse a value with `p`.
/// If `p` succeeds, the parser will try to then parse a value with `q` (from the returned input
/// from `p`).
/// If `q` succeeds, then both values are returned.
/// If either `p` or `q` fail, then the parser fails.
///
/// Both parsers must succeed *in the order that they are provided*.
/// They must also operate on the same input type, though they are free to have different
/// return types.
///
/// When called directly, `p` will be used first and `q` second.
/// When called as a [method of `Parser`](Parser::plus), the receiving parser (the `self`) is
/// used first and the `other` parser is used second.
///
/// This combinator may also be expressed with the `+` operator if **both** `p` and `q` are
/// [`BoxedParser`]s.
///
/// See also: [`left`], [`right`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').plus(token('b').convert::<u32>());
///
/// assert_eq!(("", ('a', 98)), p.parse("ab").unwrap());
/// assert!(p.parse("a").is_err());
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ba").is_err());
/// assert!(p.parse("at").is_err());
/// ```
pub fn plus<'a, Toks, T, A, P, Q, B>(p: P, q: Q) -> impl Parser<'a, Toks, T, (A, B)>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
    B: 'a,
{
    move |input1| {
        let (input2, x) = p.parse(input1)?;
        let (input3, y) = q.parse(input2)?;
        Ok((input3, (x, y)))
    }
}

/// Parses with two parsers in series, returns the first value.
///
/// This parser will first try to parse a value with `p`.
/// If `p` succeeds, the parser will try to then parse a value with `q` (from the returned input
/// from `p`).
/// If `q` succeeds, then the value parsed by `q` is returned.
/// If either `p` or `q` fail, then the parser fails.
///
/// Both parsers must succeed *in the order that they are provided*.
/// They must also operate on the same input type, though they are free to have different
/// return types.
///
/// When called directly, `p` will be used first and `q` second.
/// When called as a [method of `Parser`](Parser::left), the receiving parser (the `self`) is
/// used first and the `other` parser is used second.
///
/// This combinator may also be expressed with the `<<` operator if **both** `p` and `q` are
/// [`BoxedParser`]s.
///
/// See also: [`plus`], [`right`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').left(token('b').convert::<u32>());
///
/// assert_eq!(("", 'a'), p.parse("ab").unwrap());
/// assert!(p.parse("a").is_err());
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ba").is_err());
/// assert!(p.parse("at").is_err());
/// ```
pub fn left<'a, Toks, T, A, P, Q, B>(p: P, q: Q) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a, // TODO also lifetime oddity, is it map()?
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
    B: 'a,
{
    map(plus(p, q), |tup| tup.0)
}

/// Parses with two parsers in series, returns second value
///
/// This parser will first try to parse a value with `p`.
/// If `p` succeeds, the parser will try to then parse a value with `q` (from the returned input
/// from `p`).
/// If `q` succeeds, then the value parsed by `q` is returned.
/// If either `p` or `q` fail, then the parser fails.
///
/// Both parsers must succeed *in the order that they are provided*.
/// They must also operate on the same input type, though they are free to have different
/// return types.
///
/// When called directly, `p` will be used first and `q` second.
/// When called as a [method of `Parser`](Parser::right), the receiving parser (the `self`) is
/// used first and the `other` parser is used second.
///
/// This combinator may also be expressed with the `>>` operator if **both** `p` and `q` are
/// [`BoxedParser`]s.
///
/// See also: [`left`], [`plus`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').right(token('b').convert::<u32>());
///
/// assert_eq!(("", 98), p.parse("ab").unwrap());
/// assert!(p.parse("a").is_err());
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ba").is_err());
/// assert!(p.parse("at").is_err());
/// ```
pub fn right<'a, Toks, T, A, P, Q, B>(p: P, q: Q) -> impl Parser<'a, Toks, T, B>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a, // TODO same as above
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
    B: 'a,
{
    map(plus(p, q), |tup| tup.1)
}

/// Parses with the given parser an amount of times based on the provided range.
///
/// This parser will attempt to use `p` to parse a number of elements that would fit into the
/// provided range.
/// If `p` parses less than the lower limit of the range, this parser will fail.
/// If `p` parses up to the upper limit of the range, this parser will stop parsing and return
/// all of the parsed items.
///
/// **Note:** if `p` has already parsed the minimum number of elements, but then produces an
/// error value created with the [`ParseError::other`] function, this parser will *not* return
/// the already-parsed elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// Ranges can be specified with range literals, as well as any other type that implements
/// [`RangeBounds<usize>`].
/// As such, it will also act appropriately with range bounds that cannot normally be expressed
/// with range literals, such as ranges that exclude the start value.
///
/// **WARNING:** if `p` is able to successfully parse things *without consuming any input*
/// and the upper limit of the range is unbonded, then running this parser may create an
/// infinite loop.
///
/// See also: [`at_least`], [`at_most`], [`exactly`], [`mult`], [`mult1`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').in_range(2..4);
///
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ab").is_err());
/// assert_eq!(("", vec!['a', 'a']), p.parse("aa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("a", vec!['a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn in_range<'a, Toks, T, A, P, R>(p: P, range: R) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    R: RangeBounds<usize> + 'a,
{
    move |mut input| {
        let max = match range.end_bound() {
            // edge-case, prevents an underflow and
            // saves a bit of time
            Bound::Included(0) | Bound::Excluded(0) | Bound::Excluded(1) => {
                return Ok((input, vec![]));
            }
            // includes edge-case, technically stops vec overflow,
            // which would probably OOM first but who cares
            Bound::Included(&usize::MAX) | Bound::Unbounded => usize::MAX,
            Bound::Included(n) => *n,
            Bound::Excluded(n) => n - 1,
        };
        let min = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(n) => *n,
            Bound::Excluded(n) => n + 1,
        };

        // not possible to parse a correct number of values
        if max < min {
            return Err(ParseError::no_parse(
                &format!("impossible parser range: {}..={}", min, max),
                input
            ));
        }

        let mut values = vec![];

        while values.len() < max {
            match p.parse(input) {
                Err(e) if e.caused_by_other() => {
                    return Err(e);
                }
                Err(_) => {
                    break;
                }
                Ok((next_input, x)) => {
                    values.push(x);
                    input = next_input;
                }
            }
        }

        if values.len() < min {
            Err(ParseError::not_enough(input, min, values.len()))
        } else {
            Ok((input, values))
        }
    }
}

/// Parses zero or more values with the given parser.
///
/// This combinator behaves identically to `in_range(p, ..)`.
///
/// This parser will continue parsing with `p` until `p` fails, potentially consuming all of the
/// input if `p` never fails.
/// If `p` is unable to parse any elements, this parser will return an empty [`Vec<A>`].
///
/// **Note:** if `p` produces an error value created with the [`ParseError::other`] function,
/// this parser will *not* return the already-parsed elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// **WARNING:** if `p` is able to successfully parse things *without consuming any input*,
/// then running this parser may create an infinite loop.
///
/// See also: [`at_least`], [`at_most`], [`exactly`], [`in_range`], [`mult1`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').mult();
///
/// assert_eq!(("b", vec![]), p.parse("b").unwrap());
/// assert_eq!(("b", vec!['a']), p.parse("ab").unwrap());
/// assert_eq!(("", vec!['a', 'a']), p.parse("aa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn mult<'a, Toks, T, A, P>(p: P) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    in_range(p, ..)
}

/// Parses one or more values with the given parser
///
/// This combinator behaves identically to `in_range(p, 1..)`.
///
/// This parser will continue parsing with `p` until `p` fails, potentially consuming all of the
/// input if `p` never fails.
/// If `p` is unable to parse any elements, this parser will fail.
///
/// **Note:** if `p` has already parsed an element, but then produces an error value created
/// with the [`ParseError::other`] function, this parser will *not* return the already-parsed
/// elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// **WARNING:** if `p` is able to successfully parse things *without consuming any input*,
/// then running this parser may create an infinite loop.
///
/// See also: [`at_least`], [`at_most`], [`exactly`], [`in_range`], [`mult`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').mult1();
///
/// assert!(p.parse("b").is_err());
/// assert_eq!(("b", vec!['a']), p.parse("ab").unwrap());
/// assert_eq!(("", vec!['a', 'a']), p.parse("aa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn mult1<'a, Toks, T, A, P>(p: P) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    in_range(p, 1..)
}

/// Parses the exact number of times specified with the given parser.
///
/// This combinator behaves identically to `in_range(p, n..=n)`.
///
/// This parser will repeatedly parse with `p` until it has parsed exactly `n` items.
/// If `p` is not able to parse enough items, this parser will fail.
///
/// This combinator may also be expressed with the `*` operator if `p` is a [`BoxedParser`].
///
/// See also: [`at_least`], [`at_most`], [`in_range`], [`mult`], [`mult1`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').exactly(3);
///
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ab").is_err());
/// assert!(p.parse("aa").is_err());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("a", vec!['a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn exactly<'a, Toks, T, A, P>(p: P, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    in_range(p, n..=n)
}

/// Parses at least the number of times specified with the given parser.
///
/// This combinator behaves identically to `in_range(p, n..)`.
///
/// This parser will continue parsing with `p` until it fails, potentially consuming all of the
/// input if `p` never fails.
/// If `p` is unable to parse a minimum of `n` elements, this parser will fail.
///
/// **Note:** if `p` has already parsed the minimum number of elements, but then produces an
/// error value created with the [`ParseError::other`] function, this parser will *not* return
/// the already-parsed elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// **WARNING:** if `p` is able to successfully parse things *without consuming any input*,
/// then running this parser may create an infinite loop.
///
/// See also: [`at_most`], [`exactly`], [`in_range`], [`mult`], [`mult1`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').at_least(3);
///
/// assert!(p.parse("b").is_err());
/// assert!(p.parse("ab").is_err());
/// assert!(p.parse("aa").is_err());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn at_least<'a, Toks, T, A, P>(p: P, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    in_range(p, n..)
}

/// Parses at most the number of times specified with the given parser.
///
/// This combinator behaves identically to `in_range(p, ..=n)`.
///
/// This parser will repeatedly parse with `p` until it has parsed exactly `n` items.
/// If `p` is not able to parse enough items, this parser will return the items that it was
/// able to parse.
///
/// **Note:** if `p` produces an error value created with the [`ParseError::other`] function,
/// this parser will *not* return the already-parsed elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// See also: [`at_least`], [`exactly`], [`in_range`], [`mult`], [`mult1`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').at_most(3);
///
/// assert_eq!(("b", vec![]), p.parse("b").unwrap());
/// assert_eq!(("b", vec!['a']), p.parse("ab").unwrap());
/// assert_eq!(("", vec!['a', 'a']), p.parse("aa").unwrap());
/// assert_eq!(("", vec!['a', 'a', 'a']), p.parse("aaa").unwrap());
/// assert_eq!(("a", vec!['a', 'a', 'a']), p.parse("aaaa").unwrap());
/// ```
pub fn at_most<'a, Toks, T, A, P>(p: P, n: usize) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
{
    in_range(p, ..=n)
}

/// Parses one or more times with the first parser, separated by parses of the second parser.
///
/// This is a very useful combinator, as the parser it produces is very awkward to express
/// manually.
/// If you were to do so, however, it would look something like this:
/// ```compile_fail
/// use bad_parsers::{BoxedParser, Parser, token};
///
/// let p = token('a');
/// let q = token(',');
///
/// // This garbage doesn't even compile
/// // because `p` is moved by the call to `plus`.
/// let sep_by_p_q: BoxedParser<&str, char, Vec<char>> = p.plus(q.right(p).mult())
///     .map(|(first, mut rest)| {
///         let mut items = vec![first];
///         items.append(&mut rest);
///         items
///     })
///     .boxed();
/// ```
/// This parser will first try to parse a single item with `p`.
/// If `p` fails here, then this parser will fail.
/// After the intial parse, this parser will repeatedly attempt to parse with `q` and then `p`
/// in a pair.
/// For each successful parse of `q` and `p`, this parser will keep the result of `p`.
/// This continues until either `q` or `p` fails.
/// If `p` fails, the input consumed by `q` is restored.
///
/// **Note:** if `p` or `q` produce an error value created with the [`ParseError::other`]
/// function, this parser will *not* return the already-parsed elements and will fail instead.
/// This is because such an error was caused by factors outside of the parser chain and
/// should not be recovered from.
/// See the documentation for [`ParseError`] more information.
///
/// When called directly, the parsed items from `p` will be kept and those of `q` are ignored.
/// When called as a [method of `Parser`](Parser::sep_by), the receiving parser (the `self`) is
/// used as `p` and the `other` parser is used as `q`.
///
/// **WARNING:** if `p` and `q` are able to successfully parse things *without consuming any
/// input*, then running this parser may create an infinite loop.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').sep_by(token(','));
///
/// assert_eq!(("", vec!['a']), p.parse("a").unwrap());
/// assert_eq!(("", vec!['a', 'a']), p.parse("a,a").unwrap());
/// assert_eq!((",", vec!['a', 'a']), p.parse("a,a,").unwrap());
/// assert_eq!((",b", vec!['a', 'a']), p.parse("a,a,b").unwrap());
/// assert!(p.parse("").is_err());
/// assert!(p.parse(",a").is_err());
/// ```
pub fn sep_by<'a, Toks, T, A, P, Q, B>(p: P, q: Q) -> impl Parser<'a, Toks, T, Vec<A>>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
    B: 'a,
{
    move |mut input| {
        let (next_input, x) = p.parse(input)?;
        let mut items = vec![x];
        input = next_input;

        loop {
            match q.parse(input) {
                Err(e) if e.caused_by_other() => {
                    return Err(e);
                }
                Err(_) => {
                    break;
                }
                Ok((tmp_input, _sep)) => match p.parse(tmp_input) {
                    Err(e) if e.caused_by_other() => {
                        return Err(e);
                    }
                    Err(_) => {
                        break;
                    }
                    Ok((next_input, x)) => {
                        items.push(x);
                        input = next_input;
                    }
                }
            }
        }
        Ok((input, items))
    }
}

/// Parses the value of the first parser in-between two parses of the second parser.
///
/// This parser will first try to parse an item with `q`, and discard the result.
/// Next, this parser will try to parse an item with `p`, and keep the result.
/// Then it will try to parse with `q` once more, discarding the result.
/// If all three of these parses are successful, this parser returns the item parsed with `p`.
/// If any of these steps fail, this parser will fail.
///
/// When called directly, the parsed item from `p` will be kept and those of `q` are ignored.
/// When called as a [method of `Parser`](Parser::within), the receiving parser (the `self`) is
/// used as `p` and the `other` parser is used as `q`.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token, token_satisfies};
///
/// let surround = token_satisfies(|c: &char| c.is_whitespace()).mult1();
/// let p = token('a').within(surround);
///
/// assert_eq!(("", 'a'), p.parse(" a ").unwrap());
/// assert_eq!(("", 'a'), p.parse(" \n  a  \r ").unwrap());
/// assert!(p.parse("a").is_err());
/// assert!(p.parse(" a").is_err());
/// assert!(p.parse("a ").is_err());
/// assert!(p.parse(" b ").is_err());
/// ```
pub fn within<'a, Toks, T, A, P, Q, B>(p: P, q: Q) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
{
    move |input1| {
        let (input2, _) = q.parse(input1)?;
        let (input3, x) = p.parse(input2)?;
        let (input4, _) = q.parse(input3)?;
        Ok((input4, x))
    }
}

/// Parses with the second, first, then third parser, returns the first parser's value.
///
/// This parser will first try to parse an item with `left`, and discard the result.
/// Next, this parser will try to parse an item with `p`, and keep the result.
/// Then it will try to parse with `right`, discarding the result.
/// If all three of these parses are successful, this parser returns the item parsed with `p`.
/// If any of these steps fail, this parser will fail.
///
/// When called directly, the parsed item from `p` will be kept and those of `left` and
/// `right` are ignored.
/// When called as a [method of `Parser`](Parser::between), the receiving parser (the `self`)
/// is used as `p` and the `left` and `right` parsers are used as you would expect.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a').between(token('<'), token('>'));
///
/// assert_eq!(("", 'a'), p.parse("<a>").unwrap());
/// assert_eq!(("extra", 'a'), p.parse("<a>extra").unwrap());
/// assert!(p.parse("a").is_err());
/// assert!(p.parse("<a").is_err());
/// assert!(p.parse("a>").is_err());
/// assert!(p.parse("<b>").is_err());
/// ```
pub fn between<'a, Toks, T, A, P, Q, B, R, C>(
    p: P,
    left: Q,
    right: R,
) -> impl Parser<'a, Toks, T, A>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
    A: 'a,
    P: Parser<'a, Toks, T, A> + 'a,
    Q: Parser<'a, Toks, T, B> + 'a,
    R: Parser<'a, Toks, T, C> + 'a,
{
    move |input1| {
        let (input2, _) = left.parse(input1)?;
        let (input3, x) = p.parse(input2)?;
        let (input4, _) = right.parse(input3)?;
        Ok((input4, x))
    }
}

/// Parses a single token from the input.
///
/// This parser will only fail when the input is empty.
/// ## Examples:
/// ```
/// use bad_parsers::{Parser, any_token};
///
/// let p = any_token();
///
/// assert_eq!(("", 'a'), p.parse("a").unwrap());
/// assert_eq!(("cde", 'b'), p.parse("bcde").unwrap());
/// assert_eq!(("しい日の誕生", '新'), p.parse("新しい日の誕生").unwrap());
/// assert!(p.parse("").is_err());
/// ```
pub fn any_token<'a, Toks, T>() -> impl Parser<'a, Toks, T, T>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug,
{
    move |input: Toks| match input.take_one() {
        None => Err(ParseError::empty_input()),
        Some((rest, t)) => Ok((rest, t)),
    }
}

/// Parses a single token that satisfies the given predicate.
///
/// This parser will fail if the token does not pass the predicate, or if the input is empty.
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token_satisfies};
///
/// fn is_vowel(c: &char) -> bool {
///     match c.to_ascii_lowercase() {
///         'a' | 'e' | 'i' | 'o' | 'u' => true,
///         _                           => false,
///     }
/// }
///
/// let p = token_satisfies(is_vowel);
///
/// assert_eq!(("bcd", 'a'), p.parse("abcd").unwrap());
/// assert_eq!(("bcd", 'e'), p.parse("ebcd").unwrap());
/// assert!(p.parse("fbcd").is_err());
/// assert!(p.parse("").is_err());
/// ```
pub fn token_satisfies<'a, Toks, T, F>(f: F) -> impl Parser<'a, Toks, T, T>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + 'a,
    F: Fn(&T) -> bool + 'a,
{
    ensure(any_token(), f)
}

/// Parses the specified token.
///
/// This parser fails if the input is empty or if the token found does not equal the specified
/// token (as far as [`PartialEq`] is concerned).
/// ## Examples
/// ```
/// use bad_parsers::{Parser, token};
///
/// let p = token('a');
///
/// assert_eq!(("", 'a'), p.parse("a").unwrap());
/// assert_eq!(("b", 'a'), p.parse("ab").unwrap());
/// assert!(p.parse("").is_err());
/// assert!(p.parse("ba").is_err());
/// ```
pub fn token<'a, Toks, T>(tok: T) -> impl Parser<'a, Toks, T, T>
where
    Toks: Tokens<T> + 'a,
    T: Clone + Debug + PartialEq + 'a,
{
    token_satisfies(move |t| *t == tok)
}

/// Parses a literal string slice.
///
/// This parser is essentially a wrapper for [`&str::strip_prefix`].
/// As such, this parser will succeed if the front of the input matches the provided string
/// slice.
///
/// Note that the output of this parser is a [`&str`], not an owned [`String`].
/// ## Examples
/// ```
/// use bad_parsers::{Parser, string};
///
/// let p = string("foo");
///
/// assert_eq!(("", "foo"), p.parse("foo").unwrap());
/// assert_eq!(("d", "foo"), p.parse("food").unwrap());
/// assert_eq!(("l", "foo"), p.parse("fool").unwrap());
/// assert!(p.parse("").is_err());
/// assert!(p.parse("f").is_err());
/// assert!(p.parse("fo").is_err());
/// assert!(p.parse("fou").is_err());
/// ```
pub fn string<'a>(target: &'a str) -> impl Parser<'a, &'a str, char, &'a str> {
    move |input: &'a str| match input.strip_prefix(target) {
        Some(rest) => Ok((rest, target)),
        None => Err(ParseError::no_parse(
            &format!("could not parse string literal:{:?}", target),
            input
        )),
    }
}

/// Parses from a string slice while the given predicate holds true, per character.
///
/// This parser iterates through each [`char`] in the input and checks if it passes the
/// predicate.
/// Once it has found a [`char`] that does not pass the predicate, or reaches the end of the
/// input, the parser splits the input at that point and returns the front.
///
/// Note that the output of this parser is a [`&str`], not an owned [`String`].
///
/// See also: [`span_string_slice`].
/// ## Examples:
/// ```
/// use bad_parsers::{Parser, span_string_char};
///
/// fn is_vowel(c: &char) -> bool {
///     match c.to_ascii_lowercase() {
///         'a' | 'e' | 'i' | 'o' | 'u' => true,
///         _                           => false,
///     }
/// }
///
/// let p = span_string_char(is_vowel);
///
/// assert_eq!(("bcd", "a"), p.parse("abcd").unwrap());
/// assert_eq!(("", "aeiou"), p.parse("aeiou").unwrap());
/// assert_eq!(("xaeiou", ""), p.parse("xaeiou").unwrap());
/// ```
pub fn span_string_char<'a, F>(f: F) -> impl Parser<'a, &'a str, char, &'a str>
where
    F: Fn(&char) -> bool + 'a,
{
    move |input: &'a str| {
        let mut i: usize = 0;

        for c in input.chars() {
            if f(&c) {
                i += c.len_utf8();
            } else {
                break;
            }
        }

        let (front, back) = input.split_at(i);
        Ok((back, front))
    }
}

/// Parses from a string slice while the given predicate holds true for the rest of the input.
///
/// This parser iterates through different states of the input, where each new state has the
/// frontmost [`char`] of the previous state removed.
/// This continues until an input state is reached that does not pass the predicate, or until the
/// parser reaches the end of the input.
/// Once this state has been found, the parser splits the input at that point and returns the
/// front.
///
/// Note that the output of this parser is a [`&str`], not an owned [`String`].
///
/// See also: [`span_string_char`].
/// ## Examples:
/// ```
/// use bad_parsers::{Parser, span_string_slice};
///
/// let p = span_string_slice(|s| s.len() > 2);
///
/// assert_eq!(("cd", "ab"), p.parse("abcd").unwrap());
/// assert_eq!(("a", ""), p.parse("a").unwrap());
/// assert_eq!(("", ""), p.parse("").unwrap());
/// assert_eq!(("21", "9876543"), p.parse("987654321").unwrap());
/// ```
pub fn span_string_slice<'a, F>(f: F) -> impl Parser<'a, &'a str, char, &'a str>
where
    F: Fn(&str) -> bool + 'a,
{
    move |input: &'a str| {
        let mut i: usize = 0;

        for c in input.chars() {
            if f(&input[i..]) {
                i += c.len_utf8();
            } else {
                break;
            }
        }

        let (front, back) = input.split_at(i);
        Ok((back, front))
    }
}

/// Parses from a slice while the given predicate holds true, per item in the slice.
///
/// This parser iterates through each `T` in the input and checks if it passes the predicate.
/// Once it has found a `T` that does not pass the predicate, or reaches the end of the input,
/// the parser splits the input at that point and returns the front.
/// ## Examples:
/// ```
/// use bad_parsers::{Parser, span_slice};
///
/// let arr: [i32; 4] = [1, 2, 3, 4];
/// let nums = arr.as_slice();
///
/// // Will parse first two tokens in `arr`.
/// let p1 = span_slice(|n: &i32| *n < 3);
/// // Will parse no tokens in `arr`.
/// let p2 = span_slice(|n: &i32| *n == 99);
/// // Will parse all tokens in `arr`.
/// let p3 = span_slice(|n: &i32| *n > 0);
///
/// assert_eq!((&nums[2..], &nums[0..2]), p1.parse(nums).unwrap());
/// assert_eq!((nums, &nums[0..0]), p2.parse(nums).unwrap());
/// assert_eq!((&nums[4..], nums), p3.parse(nums).unwrap());
/// ```
pub fn span_slice<'a, T, F>(f: F) -> impl Parser<'a, &'a [T], T, &'a [T]>
where
    T: Clone + Debug + 'a,
    F: Fn(&T) -> bool + 'a,
{
    move |input: &'a [T]| {
        let mut i = 0;

        for x in input.iter() {
            if f(x) {
                i += 1;
            } else {
                break;
            }
        }

        let (front, back) = input.split_at(i);
        Ok((back, front))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens_take_one_str() {
        assert_eq!(None, "".take_one());
        assert_eq!(Some(("", 'a')), "a".take_one());
        assert_eq!(Some(("b", 'a')), "ab".take_one());
        assert_eq!(Some(("京", '東')), "東京".take_one());
    }

    #[test]
    fn tokens_no_tokens_str() {
        assert!("".no_tokens());
        assert!(!"foo".no_tokens());
        assert!(!"  ".no_tokens());
    }

    #[test]
    fn tokens_take_one_slice_t() {
        let nums = [1, 2, 3, 4];
        assert_eq!(None, nums[0..0].take_one());

        // all because slice literals are trash
        for i in 1..nums.len() {
            if let Some((rest, x)) = nums[0..i].take_one() {
                assert_eq!(&nums[1..i], rest);
                assert_eq!(1, x);
            }
        }
    }

    #[test]
    fn tokens_no_tokens_slice_t() {
        let nums = [1, 2, 3, 4];

        assert!((&nums[..0]).no_tokens());

        for i in 0..nums.len() {
            assert!(!(&nums[..=i]).no_tokens());
        }
    }

    macro_rules! p_test {
        ($name:ident, $toks:ty, $a:ty, $p:expr, $good:expr, $bad:expr,) => {
            #[test]
            fn $name() {
                let p = $p;
                let good: Vec<($toks, ($toks, $a))> = $good;
                let bad: Vec<$toks> = $bad;
                for input in bad {
                    assert!(p.parse(input).is_err());
                }
                for (input, expected) in good {
                    assert_eq!(expected, p.parse(input).unwrap());
                }
            }
        };
    }

    p_test!(
        test_first_of_two,
        &str,
        &str,
        first_of![string("ab"), string("a")],
        vec![("ab", ("", "ab")), ("a", ("", "a")), ("aab", ("ab", "a")),],
        vec!["", "c", "cab", "cba"],
    );

    p_test!(
        test_first_of_many,
        &str,
        &str,
        first_of![
            string("a"),
            string("bc"),
            string("b"),
            string("d"),
            string("e"),
        ],
        vec![
            ("a", ("", "a")),
            ("aa", ("a", "a")),
            ("bc", ("", "bc")),
            ("ba", ("a", "b")),
            ("da", ("a", "d")),
            ("ea", ("a", "e")),
        ],
        vec!["", "f", "fabcde", "c"],
    );

    // return type is BoxedParser so it can work with lazy()
    fn panic_parser<'a>() -> BoxedParser<'a, &'a str, char, char> {
        panic!("panic parser evaluated, bug with lazy()");
    }

    // if this test panics, the lazy parser is being evaluated too soon
    p_test!(
        test_lazy_non_eval,
        &str,
        char,
        token('a').or(lazy(panic_parser)),
        vec![("a", ("", 'a'))],
        vec![],
    );

    // this test should panic because the first parser failing will
    // cause the second parser to be created
    #[test]
    #[should_panic]
    fn test_lazy_eval() {
        let p = token('a').or(lazy(panic_parser));
        let _r = p.parse("");
    }

    // recursively counts the number of 'a's at the start of the input
    fn recursive_parser<'a>() -> impl Parser<'a, &'a str, char, char> {
        token('b')
            .or(token('a').right(lazy(recursive_parser)))
            .boxed()
    }

    // if this test hangs, there's a bug with lazy
    p_test!(
        test_lazy_recursion,
        &str,
        char,
        recursive_parser(),
        vec![
            ("b", ("", 'b')),
            ("ab", ("", 'b')),
            ("aab", ("", 'b')),
            ("aaaaab", ("", 'b')),
        ],
        vec!["", "a", "aaaa", "aac", "c"],
    );

    #[test]
    fn test_map_error() {
        let p = token('a').map_error(|mut e| {
            e.set_details("couldn't find letter 'a'");
            e
        });

        let e = ParseError::no_parse("couldn't find letter 'a'", "b");
        let expected = e.to_string();

        assert_eq!(("", 'a'), p.parse("a").unwrap());
        assert_eq!(expected, p.parse("b").unwrap_err().to_string());
    }

    p_test!(
        test_identity,
        &str,
        (),
        identity(),
        vec![("", ("", ())), ("foo", ("foo", ())),],
        vec![],
    );

    p_test!(
        test_eof,
        &str,
        (),
        eof(),
        vec![("", ("", ()))],
        vec!["foo", "   "],
    );

    p_test!(
        test_succeed,
        &str,
        u8,
        succeed(42),
        vec![
            ("", ("", 42)),
            ("foo", ("foo", 42)),
            ("anything", ("anything", 42)),
        ],
        vec![],
    );

    p_test!(
        test_succeed_default,
        &str,
        u8,
        succeed_default(),
        vec![
            ("", ("", u8::default())),
            ("foo", ("foo", u8::default())),
            ("anything", ("anything", u8::default())),
        ],
        vec![],
    );

    p_test!(
        test_flunk,
        &str,
        (),
        flunk::<&str, char, ()>(),
        vec![],
        vec!["", "foo", "anything"],
    );

    #[test]
    fn test_flunk_with() {
        let p = flunk_with::<&str, char, ()>("message");

        let msg1 = format!("Parser flunked: {}, Flunked at: \"{}\"", "message", "");
        let msg2 = format!("Parser flunked: {}, Flunked at: \"{}\"", "message", "foo");
        let msg3 = format!("Parser flunked: {}, Flunked at: \"{}\"", "message", "anything");

        assert_eq!(msg1, p.parse("").unwrap_err().to_string());
        assert_eq!(msg2, p.parse("foo").unwrap_err().to_string());
        assert_eq!(msg3, p.parse("anything").unwrap_err().to_string());
    }

    p_test!(
        test_and_then,
        &str,
        char,
        any_token().and_then(token),
        vec![("aa", ("", 'a')), ("bb", ("", 'b')), ("aab", ("b", 'a')),],
        vec!["", "a", "b", "ab", "abb",],
    );

    p_test!(
        test_map,
        &str,
        u64,
        token('a').map(|c| c.into()),
        vec![
            ("a", ("", 97)),
            ("aa", ("a", 97)),
            ("ab", ("b", 97)),
            ("abc", ("bc", 97)),
        ],
        vec!["", "b", "ba"],
    );

    p_test!(
        test_ignore,
        &str,
        (),
        token('a').ignore(),
        vec![("a", ("", ())), ("aa", ("a", ())),],
        vec!["", "b", "ba"],
    );

    p_test!(
        test_convert,
        &str,
        u64,
        token('a').convert(),
        vec![
            ("a", ("", 97)),
            ("aa", ("a", 97)),
            ("ab", ("b", 97)),
            ("abc", ("bc", 97)),
        ],
        vec!["", "b", "ba"],
    );

    p_test!(
        test_replace,
        &str,
        bool,
        token('a').replace(true),
        vec![
            ("a", ("", true)),
            ("aa", ("a", true)),
            ("ab", ("b", true)),
            ("abc", ("bc", true)),
        ],
        vec!["", "b", "ba"],
    );

    p_test!(
        test_or,
        &str,
        char,
        token('a').or(token('b')),
        vec![
            ("a", ("", 'a')),
            ("b", ("", 'b')),
            ("ab", ("b", 'a')),
            ("ba", ("a", 'b')),
            ("bc", ("c", 'b')),
        ],
        vec!["", "c", "ca", "cb"],
    );

    p_test!(
        test_recover,
        &str,
        char,
        token('a').recover('x'),
        vec![
            ("", ("", 'x')),
            ("a", ("", 'a')),
            ("b", ("b", 'x')),
            ("ab", ("b", 'a')),
            ("ba", ("ba", 'x')),
            ("bc", ("bc", 'x')),
        ],
        vec![],
    );

    p_test!(
        test_recover_default,
        &str,
        char,
        token('a').recover_default(),
        vec![
            ("", ("", char::default())),
            ("a", ("", 'a')),
            ("b", ("b", char::default())),
            ("ab", ("b", 'a')),
            ("ba", ("ba", char::default())),
            ("bc", ("bc", char::default())),
        ],
        vec![],
    );

    p_test!(
        test_optional,
        &str,
        Option<char>,
        token('a').optional(),
        vec![
            ("a", ("", Some('a'))),
            ("ab", ("b", Some('a'))),
            ("abc", ("bc", Some('a'))),
            ("", ("", None)),
            ("b", ("b", None)),
            ("ba", ("ba", None)),
        ],
        vec![],
    );

    p_test!(
        test_ensure,
        &str,
        char,
        any_token().ensure(|c| *c == 'a'),
        vec![("a", ("", 'a')), ("ab", ("b", 'a')), ("abc", ("bc", 'a')),],
        vec!["", "b", "ba",],
    );

    p_test!(
        test_reject,
        &str,
        char,
        any_token().reject(|c| *c == 'a'),
        vec![("b", ("", 'b')), ("bc", ("c", 'b')), ("cb", ("b", 'c')),],
        vec!["", "a", "apple", "ab"],
    );

    p_test!(
        test_plus,
        &str,
        (char, char),
        token('a').plus(token('b')),
        vec![
            ("ab", ("", ('a', 'b'))),
            ("aba", ("a", ('a', 'b'))),
            ("abb", ("b", ('a', 'b'))),
            ("abc", ("c", ('a', 'b'))),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    p_test!(
        test_left,
        &str,
        char,
        token('a').left(token('b')),
        vec![
            ("ab", ("", 'a')),
            ("aba", ("a", 'a')),
            ("abb", ("b", 'a')),
            ("abc", ("c", 'a')),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    p_test!(
        test_right,
        &str,
        char,
        token('a').right(token('b')),
        vec![
            ("ab", ("", 'b')),
            ("aba", ("a", 'b')),
            ("abb", ("b", 'b')),
            ("abc", ("c", 'b')),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    type PR = (Bound<usize>, Bound<usize>);

    // in_range(p, ..) <=> mult(p)
    p_test!(
        test_in_range_uu,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Unbounded, Bound::Unbounded)),
        vec![
            (&[], (&[], vec![])),
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![],
    );

    // in_range(p, 1..) <=> mult1(p) <=> at_least(p, 1)
    p_test!(
        test_in_range_iu,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Included(1), Bound::Unbounded)),
        vec![
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![&[],],
    );

    p_test!(
        test_in_range_eu,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Excluded(1), Bound::Unbounded)),
        vec![
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![&[], &[1],],
    );

    // in_range(p, ..=n) <=> at_most(p, n)
    p_test!(
        test_in_range_ui,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Unbounded, Bound::Included(3))),
        vec![
            (&[], (&[], vec![])),
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[4], vec![1, 2, 3])),
        ],
        vec![],
    );

    p_test!(
        test_in_range_ii,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Included(1), Bound::Included(3))),
        vec![
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[4], vec![1, 2, 3])),
        ],
        vec![&[],],
    );

    p_test!(
        test_in_range_ei,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Excluded(1), Bound::Included(3))),
        vec![
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[4], vec![1, 2, 3])),
        ],
        vec![&[], &[1],],
    );

    p_test!(
        test_in_range_ue,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Unbounded, Bound::Excluded(3))),
        vec![
            (&[], (&[], vec![])),
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[3], vec![1, 2])),
            (&[1, 2, 3, 4], (&[3, 4], vec![1, 2])),
        ],
        vec![],
    );

    p_test!(
        test_in_range_ie,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Included(1), Bound::Excluded(3))),
        vec![
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[3], vec![1, 2])),
            (&[1, 2, 3, 4], (&[3, 4], vec![1, 2])),
        ],
        vec![&[],],
    );

    p_test!(
        test_in_range_ee,
        &[i32],
        Vec<i32>,
        any_token().in_range::<PR>((Bound::Excluded(1), Bound::Excluded(3))),
        vec![
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[3], vec![1, 2])),
            (&[1, 2, 3, 4], (&[3, 4], vec![1, 2])),
        ],
        vec![&[], &[1],],
    );

    // in_range(p, ..) <=> mult(p)
    p_test!(
        test_mult,
        &[i32],
        Vec<i32>,
        any_token().mult(),
        vec![
            (&[], (&[], vec![])),
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![],
    );

    // in_range(p, 1..) <=> mult1(p) <=> at_least(p, 1)
    p_test!(
        test_mult1,
        &[i32],
        Vec<i32>,
        any_token().mult1(),
        vec![
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![&[]],
    );

    // in_range(p, n..=n) <=> exactly(p, n)
    p_test!(
        test_exactly,
        &[i32],
        Vec<i32>,
        any_token().exactly(2),
        vec![
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[3], vec![1, 2])),
            (&[1, 2, 3, 4], (&[3, 4], vec![1, 2])),
        ],
        vec![&[], &[1]],
    );

    // in_range(p, 1..) <=> mult1(p) <=> at_least(p, 1)
    p_test!(
        test_at_least,
        &[i32],
        Vec<i32>,
        any_token().at_least(1),
        vec![
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[], vec![1, 2, 3, 4])),
        ],
        vec![&[],],
    );

    // in_range(p, ..=n) <=> at_most(p, n)
    p_test!(
        test_at_most,
        &[i32],
        Vec<i32>,
        any_token().at_most(3),
        vec![
            (&[], (&[], vec![])),
            (&[1], (&[], vec![1])),
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[], vec![1, 2, 3])),
            (&[1, 2, 3, 4], (&[4], vec![1, 2, 3])),
        ],
        vec![],
    );

    p_test!(
        test_sep_by,
        &str,
        Vec<char>,
        token('a').sep_by(token('b')),
        vec![
            ("a", ("", vec!['a'])),
            ("ab", ("b", vec!['a'])),
            ("aba", ("", vec!['a', 'a'])),
            ("abab", ("b", vec!['a', 'a'])),
            ("ababa", ("", vec!['a', 'a', 'a'])),
            ("ababaa", ("a", vec!['a', 'a', 'a'])),
            ("aababa", ("ababa", vec!['a'])),
        ],
        vec!["", "b", "ba", "bba", "xababa",],
    );

    p_test!(
        test_within,
        &str,
        char,
        token('a').within(token('-')),
        vec![("-a-", ("", 'a')), ("-a-b", ("b", 'a')),],
        vec!["", "a", "-a", "a-", "-b-"],
    );

    // alternate way to use or() combinator
    p_test!(
        test_op_bitor,
        &str,
        char,
        token('a').boxed() | token('b').boxed(),
        vec![
            ("a", ("", 'a')),
            ("b", ("", 'b')),
            ("ab", ("b", 'a')),
            ("ba", ("a", 'b')),
            ("bc", ("c", 'b')),
        ],
        vec!["", "c", "ca", "cb"],
    );

    // alternate way to use plus() combinator
    p_test!(
        test_op_add,
        &str,
        (char, char),
        token('a').boxed() + token('b').boxed(),
        vec![
            ("ab", ("", ('a', 'b'))),
            ("aba", ("a", ('a', 'b'))),
            ("abb", ("b", ('a', 'b'))),
            ("abc", ("c", ('a', 'b'))),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    // alternate way to use exactly() combinator
    p_test!(
        test_op_mul,
        &[i32],
        Vec<i32>,
        any_token().boxed() * 2,
        vec![
            (&[1, 2], (&[], vec![1, 2])),
            (&[1, 2, 3], (&[3], vec![1, 2])),
            (&[1, 2, 3, 4], (&[3, 4], vec![1, 2])),
        ],
        vec![&[], &[1]],
    );

    // alternate way to use left() combinator
    p_test!(
        test_op_shl,
        &str,
        char,
        token('a').boxed() << token('b').boxed(),
        vec![
            ("ab", ("", 'a')),
            ("aba", ("a", 'a')),
            ("abb", ("b", 'a')),
            ("abc", ("c", 'a')),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    // alternate way to use right() combinator
    p_test!(
        test_op_shr,
        &str,
        char,
        token('a').boxed() >> token('b').boxed(),
        vec![
            ("ab", ("", 'b')),
            ("aba", ("a", 'b')),
            ("abb", ("b", 'b')),
            ("abc", ("c", 'b')),
        ],
        vec!["", "a", "b", "ba", "acb",],
    );

    p_test!(
        test_any_token,
        &str,
        char,
        any_token(),
        vec![("a", ("", 'a')), ("ba", ("a", 'b')), ("abc", ("bc", 'a')),],
        vec![""],
    );

    p_test!(
        test_token_satisfies,
        &str,
        char,
        token_satisfies(|c: &char| c.is_ascii_digit()),
        vec![("1", ("", '1')), ("2a", ("a", '2')), ("22", ("2", '2')),],
        vec!["", "a", "a2"],
    );

    p_test!(
        test_token,
        &[u8],
        u8,
        token(42_u8),
        vec![
            (&[42], (&[], 42)),
            (&[42, 1], (&[1], 42)),
            (&[42, 42], (&[42], 42)),
        ],
        vec![&[], &[1], &[1, 42]],
    );

    p_test!(
        test_string,
        &str,
        &str,
        string("foo"),
        vec![
            ("foo", ("", "foo")),
            ("food", ("d", "foo")),
            ("fool", ("l", "foo")),
        ],
        vec!["", "f", "fo", "fox", "fro", "bar"],
    );

    p_test!(
        test_span_string_char,
        &str,
        &str,
        span_string_char(|c| c.is_alphanumeric()),
        vec![
            ("foo", ("", "foo")),
            ("1234", ("", "1234")),
            ("a1b2c3", ("", "a1b2c3")),
            ("a1b_2c3", ("_2c3", "a1b")),
            ("_2c3", ("_2c3", "")),
            ("a1藏b_2c3", ("_2c3", "a1藏b")),
        ],
        vec![],
    );

    p_test!(
        test_span_string_slice,
        &str,
        &str,
        span_string_slice(|s| !s.starts_with("stop")),
        vec![
            ("abcdef", ("", "abcdef")),
            ("abcstopdef", ("stopdef", "abc")),
            ("ab藏cstopd藏ef", ("stopd藏ef", "ab藏c")),
            ("", ("", "")),
            ("abstcopde", ("", "abstcopde")),
        ],
        vec![],
    );

    p_test!(
        test_span_slice,
        &[i32],
        &[i32],
        span_slice(|i| *i < 3),
        vec![
            (&[], (&[], &[])),
            (&[1], (&[], &[1])),
            (&[1, 2], (&[], &[1, 2])),
            (&[1, 2, 3], (&[3], &[1, 2])),
            (&[1, 4, 3], (&[4, 3], &[1])),
        ],
        vec![],
    );
}
