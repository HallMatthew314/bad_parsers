# bad_parsers

## WARNING: CURRENTLY NOT STABLE

This library's API is far from finalized, and different components can change or vanish without warning.
It is not ~~currently~~ recommended to use this library for any vaguely-serious projects.

## What is this thing?

`bad_parsers` is the parsing library I end up re-implementing every few months, so I figured I might as well make it an actual crate.
This library uses [parser combinators](https://en.wikipedia.org/wiki/Parser_combinator) to create complex parsers that can parse from strings and slices of arbitrary token types.
This is the ~~only parsing method I know anything about~~ approach I use the most when trying to parse and/or lex things in various projects.

More information about this project can be found in [the documentation](https://docs.rs/bad_parsers).

### Is it Blazingly Fast 🚀?

Probably not. I haven't benchmarked it and I would have to be very bored to want to do that in the future.

### Is it Safe™?

As of writing, the only `unsafe` things in the library are the `Send` and `Sync` implementations for the `ParseError` type.
I have attempted to prove their thread-safety in some comments near the implementation and it seems fine to me.

### Are you ever going to take this project seriously?

Absolutely not!

And neither should you! :D

## Using this library

How to use this library in 5 easy steps:

1. Don't.
2. Run `cargo add bad_parsers` in your project directory, or manually add the following to your project's dependencies in `Cargo.toml`:
```
[dependencies]
bad_parsers = "<latest version here>"
```
3. Start using it:
```rust
use bad_parsers::{Parser, string};

fn main() {
    let p = string("hello");
    let r = p.parse("hello world");
    assert_eq!((" world", "hello"), r.unwrap());
}
```
4. Realize your mistake.
5. Switch to [nom](https://crates.io/crates/nom).

## Contributing

Please don't.

## Credit Where it's Due

This library owes its existence to:

 - [This video](https://www.youtube.com/watch?v=N9RUqGYuGfw) for explaining the concept of parser combinators.
 - [This article](https://bodil.lol/parser-combinators/) for providing the parser trait framework that this library uses.

