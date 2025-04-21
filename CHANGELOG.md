# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Security

nothing so far

### Added

- Changelog
- Example: JSON parser
- `ParseError.error_details`: a more convenient function for changing error details
- `was_parsed` + method version: a combinator similar to `optional` that returns a boolean

### Fixed

nothing so far

### Changed

- Added documentation link to Cargo.toml
- Made the default error message for `token` more useful
- Changed some more doctests to use the new `error_details` function
- Various superfluous changes to documentation

### Deprecated

nothing so far

### Removed

nothing so far

## [0.1.0-unstable]

* original feature-set, see 71d37b8 is the lightweight-tagged 0.1.0 commit

