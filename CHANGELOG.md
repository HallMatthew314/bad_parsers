# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [unreleased]

### Added

- `within_and_sep_by` and `within_and_sep_by1`, similar combinators to `sep_by` but they work in the opposite way.
- `ParseError::other_parser`, allows forwarding error values between parsers with different input types

### Fixed

- fixed panic when calling `Tokens::preview` on slice types that have less than 8 elements

### Non-breaking changes

- various small changes to documentation

## [0.2.0-unstable]

### Added

- Changelog
- Example: JSON lexer + parser
- `ParseError::map_error_details`: a more convenient function for changing error details
- `trailing` + method version: a combinator similar to `left`, but allows the second parser to fail
- `was_parsed` + method version: a combinator similar to `optional` that returns a boolean
- `ParseError::append_error` and `ParseError::prepend_error` for more convenient error details modification

### Fixed

- The functions `left`, `recover`, `recover_default`, `right`, and `trailing` no longer have the `T: 'a` constraint.

### Breaking Changes
- A new convention for error constructor functions has been established:
    - First argument: `details: &str`, required on all constructors
    - Second argument (if applicable): `loc: Toks`, not required of constructors for situations where no meaningful value can be provided (e.g., `empty_input`).
    - All other arguments following these are specific to the type of error being constructed
- Due to the above: the following constructor function arguments have changed:
    - `empty_input()` is now `empty_input(details: &str)`
    - `unexpected_input(loc: Toks)` is now `unexpected_input(deatils: &str, loc: Toks)`
    - `not_enough(loc: Toks, needed: usize, got: usize)` is now `not_enough(details: &str, loc: Toks, needed: usize, got: usize)`
    - `other(cause: E, loc: Toks)` is now `other(details: &str, loc: Toks, cause: E)`
- Some other methods of `ParseError` were renamed to better suit Rust's conventions:
    - `ParseError::get_details` renamed to `ParseError::details`
    - `ParseError::set_details` renamed to `ParseError::overwrite_details`
    - `ParseError::get_loc` renamed to `ParseError::loc`
    - `ParseError::get_loc_non_empty` renamed to `ParseError::loc_non_empty`
- Newly-named `ParseError::details` function returns `&str` instead of `Option<&str>`
- Combinator `error_details` renamed to `map_error_details`

### Non-Breaking Changes
- Added documentation link to Cargo.toml
- Made the default error details for `token` more useful
- Changed some doctests to use the new `map_error_details` function
- Various superfluous changes to documentation
- Modified the template string in `ParseError`'s implementation of `Display`

## [0.1.0-unstable]

* original feature-set, see 71d37b8 is the lightweight-tagged 0.1.0 commit

