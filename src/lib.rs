// Copyright 2024 Cloudflare, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]
// Note: If you change this remember to update `README.md`. To do so run `cargo rdme`.
//! `wildcard` is a rust crate for wildcard matching.
//!
//! Here's how to use it:
//!
//! ```rust
//! # use wildcard::Wildcard;
//! #
//! let wildcard = Wildcard::new("*foo?*bar".as_bytes()).unwrap();
//!
//! assert!(wildcard.is_match("fooofooobar".as_bytes()));
//! ```
//!
//! Special characters can be escaped to represent their literal symbol:
//!
//! ```rust
//! # use wildcard::Wildcard;
//! #
//! let wildcard = Wildcard::new(r"\*\?".as_bytes()).unwrap();
//!
//! assert!(!wildcard.is_match("ab".as_bytes()));
//! assert!(wildcard.is_match("*?".as_bytes()));
//! ```
//!
//! You can also capture the substring that matched the metasymbols of the wildcard:
//!
//! ```rust
//! # use wildcard::Wildcard;
//! #
//! let wildcard = Wildcard::new("* is a * style?".as_bytes()).unwrap();
//!
//! let captures: Vec<&[u8]> = wildcard.captures("Lambic is a beer style!".as_bytes()).unwrap();
//!
//! assert_eq!(captures, ["Lambic".as_bytes(), "beer".as_bytes(), "!".as_bytes()]);
//! ```
//!
//! # Matching customization
//!
//! With `wildcard` you can configure these properties of a wildcard:
//!
//! 1. Configure the symbols for the metasymbols `*` and `?` as well as the escape symbol.
//! 2. Support for the metasymbol `?` can be disabled.
//! 3. Support for escaping can be disabled.
//! 4. Support for case-insensitive matching.

use std::borrow::Cow;
use std::fmt::Debug;
use std::ops::Range;
// TODO maybe not use thiserror so we can make the crate nostd?
use thiserror::Error;

/// Error representing an invalid [`Wildcard`] creation.
#[derive(Eq, PartialEq, Error, Debug)]
pub enum WildcardError {
    /// The wildcard contains a syntax error.
    #[error("wildcard syntax error at position {position}: {message}")]
    Syntax {
        /// First position of the error in the wildcard.
        position: usize,
        /// Description of the error.
        message: &'static str,
    },
    /// The wildcard matching not configured correctly, as it contains repeated special symbols
    /// (either the metasymbols or the escape symbol).
    #[error("invalid configuration of special symbols")]
    InvalidSpecialSymbolsConfiguration,
}

/// This trait defined the alphabet a wildcard can be used on.
pub trait WildcardSymbol: Eq + Copy {
    /// Default metasymbol that matches on sequences of arbitrary length.
    ///
    /// This is typically `*`.
    const DEFAULT_METASYMBOL_ANY: Self;
    /// Default metasymbol that matches on a single symbol.
    ///
    /// This is typically `?`.
    const DEFAULT_METASYMBOL_ONE: Self;
    /// Default metasymbol used for escaping.
    ///
    /// This is typically `\`.
    const DEFAULT_METASYMBOL_ESCAPE: Self;

    /// Checks equality in a case-insensitive way.
    fn eq_case_insensitive(a: Self, b: Self) -> bool;
}

impl WildcardSymbol for u8 {
    const DEFAULT_METASYMBOL_ANY: u8 = b'*';
    const DEFAULT_METASYMBOL_ONE: u8 = b'?';
    const DEFAULT_METASYMBOL_ESCAPE: u8 = b'\\';

    fn eq_case_insensitive(a: u8, b: u8) -> bool {
        a.eq_ignore_ascii_case(&b)
    }
}

impl WildcardSymbol for char {
    const DEFAULT_METASYMBOL_ANY: char = '*';
    const DEFAULT_METASYMBOL_ONE: char = '?';
    const DEFAULT_METASYMBOL_ESCAPE: char = '\\';

    fn eq_case_insensitive(a: char, b: char) -> bool {
        a.to_lowercase().eq(b.to_lowercase())
    }
}
#[derive(Clone)]
struct WildcardMatchingConfig<S> {
    metasymbol_any: S,
    metasymbol_one: Option<S>,
    symbol_escape: Option<S>,
    case_insensitive: bool,
}

impl<S> WildcardMatchingConfig<S>
where
    S: WildcardSymbol,
{
    fn validate(&self) -> Result<(), WildcardError> {
        // Special symbols cannot be the same.
        let has_special_symbol_repetitions = is_symbol(self.metasymbol_any, self.metasymbol_one)
            || is_symbol(self.metasymbol_any, self.symbol_escape)
            || (self.metasymbol_one.is_some() && self.metasymbol_one == self.symbol_escape);

        (!has_special_symbol_repetitions)
            .then_some(())
            .ok_or(WildcardError::InvalidSpecialSymbolsConfiguration)
    }
}

impl<S> Default for WildcardMatchingConfig<S>
where
    S: WildcardSymbol,
{
    fn default() -> Self {
        WildcardMatchingConfig {
            metasymbol_any: S::DEFAULT_METASYMBOL_ANY,
            metasymbol_one: Some(S::DEFAULT_METASYMBOL_ONE),
            symbol_escape: Some(S::DEFAULT_METASYMBOL_ESCAPE),
            case_insensitive: false,
        }
    }
}

/// A builder of a [`Wildcard`]. This allows you to configure specific behavior of the wildcard
/// matching.
pub struct WildcardBuilder<'a, S = u8>
where
    S: WildcardSymbol,
{
    pattern: Cow<'a, [S]>,
    config: WildcardMatchingConfig<S>,
}

impl<'a, S> WildcardBuilder<'a, S>
where
    S: WildcardSymbol,
{
    /// Creates a wildcard builder.
    #[must_use]
    pub fn new(pattern: &'a [S]) -> WildcardBuilder<'a, S> {
        WildcardBuilder::from_cow(Cow::Borrowed(pattern))
    }

    /// Creates a wildcard builder.
    #[must_use]
    pub fn from_owned(pattern: Vec<S>) -> WildcardBuilder<'static, S> {
        WildcardBuilder::from_cow(Cow::Owned(pattern))
    }

    /// Creates a wildcard builder.
    #[must_use]
    pub fn from_cow(pattern: Cow<'a, [S]>) -> WildcardBuilder<'a, S> {
        WildcardBuilder { pattern, config: WildcardMatchingConfig::default() }
    }

    /// Configures the metasymbol used to match on sequences of arbitrary length.
    ///
    /// This is typically `*`.
    #[must_use]
    pub fn with_any_metasymbol(mut self, s: S) -> WildcardBuilder<'a, S> {
        self.config.metasymbol_any = s;
        self
    }

    /// Configures the metasymbol used to match on a single symbol.
    ///
    /// This is typically `?`.
    #[must_use]
    pub fn with_one_metasymbol(mut self, s: S) -> WildcardBuilder<'a, S> {
        self.config.metasymbol_one = Some(s);
        self
    }

    /// Disable the metasymbol use to match on a single symbol.
    #[must_use]
    pub fn without_one_metasymbol(mut self) -> WildcardBuilder<'a, S> {
        self.config.metasymbol_one = None;
        self
    }

    /// Configures the symbol use to use for escaping.
    ///
    /// This is typically `\`.
    #[must_use]
    pub fn with_escape_symbol(mut self, s: S) -> WildcardBuilder<'a, S> {
        self.config.symbol_escape = Some(s);
        self
    }

    /// Disables escaping.
    #[must_use]
    pub fn without_escape(mut self) -> WildcardBuilder<'a, S> {
        self.config.symbol_escape = None;
        self
    }

    /// Configures case sensitivity used when matching.
    ///
    /// Note that special symbols are always matched verbatim.
    #[must_use]
    pub fn case_insensitive(mut self, on: bool) -> WildcardBuilder<'a, S> {
        self.config.case_insensitive = on;
        self
    }

    /// Builds the wildcard.
    pub fn build(self) -> Result<Wildcard<'a, S>, WildcardError> {
        Wildcard::new_with_config(self.pattern, self.config)
    }
}

/// A token of a wildcard.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum WildcardToken<S = u8> {
    /// Metasymbol that matches any sequence of symbols.
    MetasymbolAny,
    /// Metasymbol that matches a single symbol.
    MetasymbolOne,
    /// A literal symbol.
    Symbol(S),
}

impl<S> WildcardToken<S> {
    /// Whether the token represents a metasymbol.
    #[must_use]
    pub fn is_metasymbol(self) -> bool {
        match self {
            WildcardToken::MetasymbolAny | WildcardToken::MetasymbolOne => true,
            WildcardToken::Symbol(_) => false,
        }
    }
}

/// A wildcard. You can use this to check for match against input sequences:
///
/// ```rust
/// # use wildcard::Wildcard;
/// #
/// let wildcard = Wildcard::new("*foo?*bar".as_bytes()).expect("invalid wildcard");
///
/// assert!(wildcard.is_match("fooofooobar".as_bytes()));
/// ```
#[derive(Clone)]
pub struct Wildcard<'a, S = u8>
where
    S: WildcardSymbol,
{
    pattern: Cow<'a, [S]>,
    config: WildcardMatchingConfig<S>,
    metasymbol_count: usize,
}

impl<'a, S> Wildcard<'a, S>
where
    S: WildcardSymbol,
{
    /// Creates a wildcard.
    pub fn new(pattern: &'a [S]) -> Result<Wildcard<'a, S>, WildcardError> {
        Wildcard::new_with_config(Cow::Borrowed(pattern), WildcardMatchingConfig::default())
    }

    /// Creates a wildcard.
    pub fn from_owned(pattern: Vec<S>) -> Result<Wildcard<'static, S>, WildcardError> {
        Wildcard::new_with_config(Cow::Owned(pattern), WildcardMatchingConfig::default())
    }

    /// Creates a wildcard.
    pub fn from_cow(pattern: Cow<'a, [S]>) -> Result<Wildcard<'a, S>, WildcardError> {
        Wildcard::new_with_config(pattern, WildcardMatchingConfig::default())
    }

    fn new_with_config(
        pattern: Cow<'a, [S]>,
        config: WildcardMatchingConfig<S>,
    ) -> Result<Wildcard<'a, S>, WildcardError> {
        config.validate()?;

        let metasymbol_count = validate_syntax(&pattern, &config)?;
        let wildcard = Wildcard { pattern, config, metasymbol_count };

        Ok(wildcard)
    }

    /// Checks if `input` matches the wildcard.
    #[inline]
    #[must_use]
    pub fn is_match(&self, input: &[S]) -> bool {
        // Note that we want to have two different calls with different closures for each case so
        // each "version" of `matches()` can be properly optimized after monomorphization.
        match self.config.case_insensitive {
            true => matches(
                &self.config,
                &self.pattern,
                input,
                WildcardSymbol::eq_case_insensitive,
                |_| (),
            ),
            false => matches(&self.config, &self.pattern, input, |a, b| a == b, |_| ()),
        }
    }

    /// Captures all `input` substrings that matched the wildcard's metasymbols. This returns
    /// `None` if there's no match.
    ///
    /// ```rust
    /// # use wildcard::Wildcard;
    /// #
    /// let wildcard = Wildcard::new("* is part of *".as_bytes()).unwrap();
    ///
    /// let captures: Vec<&[u8]> = wildcard.captures("Lisboa is part of Portugal".as_bytes()).unwrap();
    ///
    /// assert_eq!(captures, ["Lisboa".as_bytes(), "Portugal".as_bytes()]);
    /// ```
    ///
    /// The captures are done in a lazy way: earlier captures will be as small as possible.
    #[inline]
    #[must_use]
    pub fn captures<'b>(&self, input: &'b [S]) -> Option<Vec<&'b [S]>> {
        let mut captures = Vec::with_capacity(self.metasymbol_count);

        let is_match = {
            let capture = |range| captures.push(&input[range]);

            // Note that we want to have two different calls with different closures for each case so
            // each "version" of `matches()` can be properly optimized after monomorphization.
            match self.config.case_insensitive {
                true => matches(
                    &self.config,
                    &self.pattern,
                    input,
                    WildcardSymbol::eq_case_insensitive,
                    capture,
                ),
                false => matches(&self.config, &self.pattern, input, |a, b| a == b, capture),
            }
        };

        match is_match {
            true => {
                // The captures for `?` cannot are not emitted by `matches()` (see function
                // documentation for why that is), so we have to backfill it.
                if let Some(metasymbol_one) = self.config.metasymbol_one {
                    fill_in_metasymbol_one_captures(
                        self.config.metasymbol_any,
                        metasymbol_one,
                        self.config.symbol_escape,
                        &self.pattern,
                        input,
                        &mut captures,
                    );
                }

                debug_assert_eq!(captures.len(), self.metasymbol_count);

                Some(captures)
            }
            false => None,
        }
    }

    /// The original pattern from which this wildcard was created.
    #[must_use]
    pub fn pattern(&self) -> &[S] {
        self.pattern.as_ref()
    }

    /// Number of metasymbols in the wildcard. The number of captures returned by
    /// [`Wildcard::captures()`], if there is match, will be the same as the number of metasymbols.
    #[must_use]
    pub fn metasymbol_count(&self) -> usize {
        self.metasymbol_count
    }

    /// Parse the wildcard into tokens.
    pub fn parsed(&self) -> impl Iterator<Item = WildcardToken<S>> + '_ {
        let mut i = 0;

        std::iter::from_fn(move || {
            if i >= self.pattern.len() {
                None
            } else {
                let symbol = self.pattern[i];

                if is_symbol(symbol, self.config.symbol_escape) {
                    // We can access index `i + 1` because we validated the pattern before.
                    let s = self.pattern[i + 1];
                    i += 2;
                    Some(WildcardToken::Symbol(s))
                } else if self.pattern[i] == self.config.metasymbol_any {
                    i += 1;
                    Some(WildcardToken::MetasymbolAny)
                } else if is_symbol(symbol, self.config.metasymbol_one) {
                    i += 1;
                    Some(WildcardToken::MetasymbolOne)
                } else {
                    i += 1;
                    Some(WildcardToken::Symbol(symbol))
                }
            }
        })
    }
}

/// Validates the syntax of the wildcard. Returns the number of metasymbols in the pattern.
fn validate_syntax<S>(
    pattern: &[S],
    config: &WildcardMatchingConfig<S>,
) -> Result<usize, WildcardError>
where
    S: Eq + Copy,
{
    // This function is somewhat performance-sensitive. Any changes to this function should be
    // validated by running the benchmarks against the baseline.

    let symbol_escape = config.symbol_escape;
    let metasymbol_any = config.metasymbol_any;
    let metasymbol_one = config.metasymbol_one;

    let pattern_len = pattern.len();

    let mut metasymbols = 0;
    let mut escape = false;
    let mut i = 0;

    // The performance is a bit better if we use a `while` instead of iterators.
    while i < pattern_len {
        let symbol = pattern[i];

        if escape {
            if symbol != metasymbol_any
                && !is_symbol(symbol, metasymbol_one)
                && !is_symbol(symbol, symbol_escape)
            {
                return Err(WildcardError::Syntax {
                    position: i - 1,
                    message: "invalid escape sequence",
                });
            }

            escape = false;
        } else if is_symbol(symbol, symbol_escape) {
            escape = true;
        } else if symbol == metasymbol_any || is_symbol(symbol, metasymbol_one) {
            metasymbols += 1;
        }

        i += 1;
    }

    if escape {
        return Err(WildcardError::Syntax {
            position: pattern_len - 1,
            message: "incomplete escape sequence at the end of the wildcard",
        });
    }

    Ok(metasymbols)
}

/// This function fills in the captures of `?` based on the captures of `*`. This needs to be done
/// because [`matches()`] does not emit captures of `?`. Read the documentation of [`matches()`] to
/// understand why.
fn fill_in_metasymbol_one_captures<'a, S>(
    metasymbol_any: S,
    metasymbol_one: S,
    symbol_escape: Option<S>,
    pattern: &[S],
    input: &'a [S],
    captures: &mut Vec<&'a [S]>,
) where
    S: Eq + Copy,
{
    // This function is somewhat performance-sensitive. Any changes to this function should be
    // validated by running the benchmarks against the baseline.

    let pattern_len = pattern.len();

    let mut input_index = 0;
    let mut captures_index = 0;
    let mut escape = false;
    let mut i = 0;

    // The performance is a bit better if we use a `while` instead of iterators.
    while i < pattern_len {
        let symbol = pattern[i];

        if escape {
            escape = false;
        } else if is_symbol(symbol, symbol_escape) {
            escape = true;
            input_index += 1;
        } else if symbol == metasymbol_any {
            input_index += captures[captures_index].len();
            captures_index += 1;
        } else if symbol == metasymbol_one {
            // TODO We can be more clever here to avoid quadratic complexity.
            captures.insert(captures_index, &input[input_index..=input_index]);
            captures_index += 1;
            input_index += 1;
        } else {
            input_index += 1;
        }

        i += 1;
    }
}

#[inline(always)]
fn is_symbol<S>(v: S, opt_symbol: Option<S>) -> bool
where
    S: Eq + Copy,
{
    match opt_symbol {
        None => false,
        Some(u) => u == v,
    }
}

/// The algorithm for matching. This is based on [Kurt's algorithm][kurt2016] with the following
/// optimizations taken from [Krauss algorithm][krauss2014]:
///
/// 1. Immediately skip consecutive stars.
/// 2. When matching a star, immediately fast-forward the input to a symbol that matches the first
///    symbol after the star. This applies both when star is found and when backtracking.
///
/// It also implements escaping of special symbols.
///
/// The closure `capture` will be called for all substrings matched by a star. It will *not* be
/// called for captures of `?`: because we do backtracking we would have to delay captures of ?
/// which would require us to use more memory.
///
/// [kurt2016]: http://dodobyte.com/wildcard.html
/// [krauss2014]: http://developforperformance.com/MatchingWildcards_AnImprovedAlgorithmForBigData.html
#[inline]
fn matches<S>(
    config: &WildcardMatchingConfig<S>,
    pattern: &[S],
    input: &[S],
    symbol_eq: impl Fn(S, S) -> bool,
    mut capture: impl FnMut(Range<usize>),
) -> bool
where
    S: Eq + Copy,
{
    // This function is very performance-sensitive. Any changes to this function should be validated
    // by running the benchmarks against the baseline.

    let symbol_escape = config.symbol_escape;
    let metasymbol_any = config.metasymbol_any;
    let metasymbol_one = config.metasymbol_one;

    let pattern_len = pattern.len();
    let input_len = input.len();
    let mut pattern_index = 0;
    let mut input_index = 0;

    // This will point to the first pattern symbol after the last star.
    let mut revert_pattern_index = 0;
    // After we see a star we will start to try to match the pattern after the star with this
    // position of the input. We will initially try to match the star with an empty substring.
    // If we fail to match we will increment this and try again, now trying to match the
    // star with a substring of length one, and so on.
    let mut revert_input_index = 0;
    // This will point to the first symbol of input that matches the star. The current assignment
    // for the star will be `input[last_star_input_index..revert_input_index]`.
    let mut last_star_input_index = 0;

    while input_index < input_len {
        let mut match_failed = false;

        if pattern_index >= pattern_len {
            match_failed = true;
        } else {
            let mut pattern_symbol = pattern[pattern_index];
            let mut escape = false;

            // Skip the escape symbol.
            if is_symbol(pattern_symbol, symbol_escape) {
                // If this is an escape it is safe to advance the one (i.e. we won't be out of
                // bounds) as this was validated beforehand.
                pattern_index += 1;
                pattern_symbol = pattern[pattern_index];
                escape = true;
            }

            if pattern_symbol == metasymbol_any && !escape {
                // If there was a previous star we can now establish its match.
                if revert_pattern_index > 0 {
                    capture(last_star_input_index..revert_input_index);
                }

                pattern_index += 1;

                // If there are multiple stars, skip them.
                while pattern_index < pattern_len && pattern[pattern_index] == metasymbol_any {
                    capture(input_index..input_index);
                    pattern_index += 1;
                }

                if pattern_index >= pattern_len {
                    // We reached the end of the pattern, and we just matched a `*`, so we can say for
                    // sure this is a match.
                    capture(input_index..input_len);
                    return true;
                }

                debug_assert!(pattern_index < pattern_len);

                let pattern_symbol = pattern[pattern_index];

                debug_assert!(pattern_symbol != metasymbol_any);

                last_star_input_index = input_index;

                // We had a `*` so we can advance to the next possible match (what we skip is what the
                // star consumed).
                if !is_symbol(pattern_symbol, metasymbol_one)
                    && !is_symbol(pattern_symbol, symbol_escape)
                {
                    while input_index < input_len && !symbol_eq(pattern_symbol, input[input_index])
                    {
                        input_index += 1;
                    }
                }

                // Update revert data. We will use this if we need to backtrack because of a mismatch.
                revert_pattern_index = pattern_index;
                revert_input_index = input_index;
            } else if !symbol_eq(pattern_symbol, input[input_index])
                && (!is_symbol(pattern_symbol, metasymbol_one) || escape)
            {
                match_failed = true;
            } else {
                pattern_index += 1;
                input_index += 1;
            }
        }

        if match_failed {
            // Here we either reached the end of the pattern or we had a symbol mismatch.
            // In either case we failed the match, so if we never saw a star before there's no
            // possible match. If we did find a star before that means we should backtrack and
            // consider the match where the star consumed one more symbol than the current try.

            // If we never saw a `*` before, there is no match.
            if revert_pattern_index == 0 {
                return false;
            }

            // We need to backtrack. Let's make the star consume one more symbol.
            revert_input_index += 1;

            debug_assert!(revert_pattern_index < pattern_len);

            let pattern_symbol = pattern[revert_pattern_index];

            debug_assert!(pattern_symbol != metasymbol_any);

            // Advance to the next possible match.
            if !is_symbol(pattern_symbol, metasymbol_one)
                && !is_symbol(pattern_symbol, symbol_escape)
            {
                while revert_input_index < input_len
                    && !symbol_eq(pattern_symbol, input[revert_input_index])
                {
                    revert_input_index += 1;
                }
            }

            pattern_index = revert_pattern_index;
            input_index = revert_input_index;
        }
    }

    // Emit the capture of the last star.
    if revert_pattern_index > 0 {
        capture(last_star_input_index..revert_input_index);
    }

    // If there are trailing stars simply skip them.
    while pattern_index < pattern_len && pattern[pattern_index] == metasymbol_any {
        capture(input_index..input_index);
        pattern_index += 1;
    }

    // If we consumed the entire pattern we have a match.
    pattern_index >= pattern_len
}

#[cfg(test)]
mod tests {
    use crate::{Wildcard, WildcardBuilder, WildcardError, WildcardToken};
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    fn vec_u8_to_vec_string(v: Vec<&[u8]>) -> Vec<String> {
        v.into_iter().map(|c| String::from_utf8_lossy(c).into_owned()).collect()
    }

    pub mod engine_regex_bytes {
        use crate::{Wildcard, WildcardToken};
        use regex::bytes::{Regex, RegexBuilder};

        fn make_regex(pattern: &str, case_insensitive: bool) -> Regex {
            let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");
            let mut regex_pattern = "^".to_owned();

            for token in wildcard.parsed() {
                match token {
                    WildcardToken::MetasymbolAny => {
                        regex_pattern.push_str("(.*?)");
                    }
                    WildcardToken::MetasymbolOne => {
                        regex_pattern.push_str("(.)");
                    }
                    WildcardToken::Symbol(s) => {
                        let slice = &[s];
                        let s = std::str::from_utf8(slice).expect("invalid utf-8 symbol");
                        regex_pattern.push_str(&regex::escape(s));
                    }
                }
            }

            regex_pattern.push('$');

            RegexBuilder::new(&regex_pattern)
                .dot_matches_new_line(true)
                .crlf(false)
                .unicode(false)
                .case_insensitive(case_insensitive)
                .build()
                .expect("invalid regex")
        }

        pub fn matches(pattern: &str, input: &[u8], case_insensitive: bool) -> bool {
            make_regex(pattern, case_insensitive).is_match(input)
        }

        pub fn captures<'a>(
            pattern: &str,
            input: &'a [u8],
            case_insensitive: bool,
        ) -> Option<Vec<&'a [u8]>> {
            make_regex(pattern, case_insensitive).captures(input).map(|c| {
                c.iter().flat_map(IntoIterator::into_iter).skip(1).map(|m| m.as_bytes()).collect()
            })
        }

        pub fn captures_as_string(
            pattern: &str,
            input: &[u8],
            case_insensitive: bool,
        ) -> Option<Vec<String>> {
            captures(pattern, input, case_insensitive)
                .map(|c| c.iter().map(|m| String::from_utf8_lossy(m).into_owned()).collect())
        }
    }

    #[derive(serde::Deserialize, Debug)]
    struct MatchTest {
        pattern: String,
        input: String,
        matches: bool,
        #[serde(default, rename = "case-insensitive")]
        case_insensitive: bool,
    }

    #[derive(serde::Deserialize)]
    struct MatchTests {
        #[serde(rename = "test")]
        tests: Vec<MatchTest>,
    }

    fn run_matching_tests(tests: MatchTests) -> Vec<String> {
        let mut errors = Vec::new();

        assert!(!tests.tests.is_empty());

        for test in tests.tests {
            let is_match = WildcardBuilder::new(test.pattern.as_bytes())
                .case_insensitive(test.case_insensitive)
                .build()
                .expect("invalid wildcard")
                .is_match(test.input.as_bytes());

            assert_eq!(
                engine_regex_bytes::matches(
                    &test.pattern,
                    test.input.as_bytes(),
                    test.case_insensitive
                ),
                test.matches,
                "it seems the test itself is wrong: {test:?}",
            );

            match (test.matches, is_match) {
                (true, false) => errors.push(format!(
                    r#"wildcard "{}" should have matched "{}""#,
                    test.pattern, test.input
                )),
                (false, true) => errors.push(format!(
                    r#"wildcard "{}" should not have matched "{}""#,
                    test.pattern, test.input
                )),
                (true, true) | (false, false) => (),
            }
        }

        errors
    }

    #[derive(serde::Deserialize, Debug)]
    struct CaptureTest {
        pattern: String,
        input: String,
        captures: Vec<String>,
        #[serde(default, rename = "case-insensitive")]
        case_insensitive: bool,
    }

    impl CaptureTest {
        fn from_matching_test(matching_test: MatchTest) -> Option<CaptureTest> {
            if !matching_test.matches {
                return None;
            }

            let captures = engine_regex_bytes::captures_as_string(
                &matching_test.pattern,
                matching_test.input.as_bytes(),
                matching_test.case_insensitive,
            )
            .unwrap_or_else(|| {
                panic!("the test should match but captures() returned None: {matching_test:?}")
            });

            Some(CaptureTest {
                pattern: matching_test.pattern,
                input: matching_test.input,
                captures,
                case_insensitive: matching_test.case_insensitive,
            })
        }
    }

    #[derive(serde::Deserialize)]
    struct CaptureTests {
        #[serde(rename = "test")]
        tests: Vec<CaptureTest>,
    }

    fn run_capture_tests(tests: CaptureTests) -> Vec<String> {
        let mut errors = Vec::new();

        assert!(!tests.tests.is_empty());

        for test in tests.tests {
            let wildcard = WildcardBuilder::new(test.pattern.as_bytes())
                .case_insensitive(test.case_insensitive)
                .build()
                .expect("invalid wildcard");

            assert_eq!(
                engine_regex_bytes::captures_as_string(
                    &test.pattern,
                    test.input.as_bytes(),
                    test.case_insensitive
                )
                .as_ref(),
                Some(&test.captures),
                "it seems the test itself is wrong: {test:?}",
            );

            let captures: Option<Vec<String>> =
                wildcard.captures(test.input.as_bytes()).map(vec_u8_to_vec_string);

            match captures {
                Some(captures) if captures != test.captures => errors.push(format!(
                    r#"captures for wildcard "{}" with input "{}" should have been {:?} instead of {:?}"#,
                    test.pattern, test.input, test.captures, captures,
                )),
                None => errors.push(format!(
                    "we did not get a match on the capture test {test:?}"
                )),
                Some(_) => (),
            }
        }

        errors
    }

    #[test]
    fn test_matching() {
        let tests = toml::from_str::<MatchTests>(include_str!("../testdata/matching.toml"))
            .expect("failed to parse test file");

        let errors = run_matching_tests(tests);

        assert!(errors.is_empty(), "{} tests failed:\n{}", errors.len(), errors.join("\n"));
    }

    #[test]
    fn test_capture() {
        let tests = toml::from_str::<CaptureTests>(include_str!("../testdata/capture.toml"))
            .expect("failed to parse test file");

        let errors = run_capture_tests(tests);

        assert!(errors.is_empty(), "{} tests failed:\n{}", errors.len(), errors.join("\n"));

        // We also create capture tests from the matching tests:
        let tests = {
            let t = toml::from_str::<MatchTests>(include_str!("../testdata/matching.toml"))
                .expect("failed to parse test file");

            CaptureTests {
                tests: t.tests.into_iter().filter_map(CaptureTest::from_matching_test).collect(),
            }
        };

        let errors = run_capture_tests(tests);

        assert!(errors.is_empty(), "{} tests failed:\n{}", errors.len(), errors.join("\n"));
    }

    #[test]
    fn test_syntax_validation() {
        let pattern = r"\foo";
        let expected = WildcardError::Syntax { position: 0, message: r"invalid escape sequence" };

        assert_eq!(Wildcard::new(pattern.as_bytes()).err(), Some(expected));

        let pattern = r"f\oo";
        let expected = WildcardError::Syntax { position: 1, message: r"invalid escape sequence" };

        assert_eq!(Wildcard::new(pattern.as_bytes()).err(), Some(expected));

        let pattern = r"foo\";
        let expected = WildcardError::Syntax {
            position: 3,
            message: "incomplete escape sequence at the end of the wildcard",
        };

        assert_eq!(Wildcard::new(pattern.as_bytes()).err(), Some(expected));

        let pattern = r"foo\\\";
        let expected = WildcardError::Syntax {
            position: 5,
            message: "incomplete escape sequence at the end of the wildcard",
        };

        assert_eq!(Wildcard::new(pattern.as_bytes()).err(), Some(expected));

        let pattern = r"f\?oo";
        let expected = WildcardError::Syntax { position: 1, message: r"invalid escape sequence" };
        let wildcard = WildcardBuilder::new(pattern.as_bytes()).without_one_metasymbol().build();

        assert_eq!(wildcard.err(), Some(expected));

        let pattern = r"f\?oo";
        let expected = WildcardError::Syntax { position: 1, message: r"invalid escape sequence" };
        let wildcard = WildcardBuilder::new(pattern.as_bytes()).with_one_metasymbol(b'!').build();

        assert_eq!(wildcard.err(), Some(expected));

        let pattern = r"f\*\\o\?o";

        assert!(Wildcard::new(pattern.as_bytes()).is_ok());

        let pattern = r"f?oo";
        let wildcard = WildcardBuilder::new(pattern.as_bytes()).without_one_metasymbol().build();

        assert!(wildcard.is_ok());

        let pattern = r"f\!o!o";
        let wildcard = WildcardBuilder::new(pattern.as_bytes()).with_one_metasymbol(b'!').build();

        assert!(wildcard.is_ok());

        let pattern = r"f\o\\o\";
        let wildcard = WildcardBuilder::new(pattern.as_bytes()).without_escape().build();

        assert!(wildcard.is_ok());
    }

    #[test]
    fn test_configuration_repeated_special_symbols() {
        let wildcard = WildcardBuilder::new(&[]).with_escape_symbol(b'*').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));

        let wildcard = WildcardBuilder::new(&[]).with_escape_symbol(b'?').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));

        let wildcard = WildcardBuilder::new(&[]).with_one_metasymbol(b'*').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));

        let wildcard = WildcardBuilder::new(&[]).with_one_metasymbol(b'\\').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));

        let wildcard = WildcardBuilder::new(&[]).with_any_metasymbol(b'?').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));

        let wildcard = WildcardBuilder::new(&[]).with_any_metasymbol(b'\\').build();

        assert_eq!(wildcard.err(), Some(WildcardError::InvalidSpecialSymbolsConfiguration));
    }

    #[test]
    fn test_wildcard_parsed() {
        let wildcard = Wildcard::new(r"a\\b?*c\?d\*".as_bytes()).unwrap();
        let expected = [
            WildcardToken::Symbol(b'a'),
            WildcardToken::Symbol(b'\\'),
            WildcardToken::Symbol(b'b'),
            WildcardToken::MetasymbolOne,
            WildcardToken::MetasymbolAny,
            WildcardToken::Symbol(b'c'),
            WildcardToken::Symbol(b'?'),
            WildcardToken::Symbol(b'd'),
            WildcardToken::Symbol(b'*'),
        ];

        assert_eq!(wildcard.parsed().collect::<Vec<_>>(), expected);

        let wildcard =
            WildcardBuilder::new(r"*?\\".as_bytes()).without_one_metasymbol().build().unwrap();
        let expected = [
            WildcardToken::MetasymbolAny,
            WildcardToken::Symbol(b'?'),
            WildcardToken::Symbol(b'\\'),
        ];

        assert_eq!(wildcard.parsed().collect::<Vec<_>>(), expected);

        let wildcard = WildcardBuilder::new(r"*?\".as_bytes()).without_escape().build().unwrap();
        let expected = [
            WildcardToken::MetasymbolAny,
            WildcardToken::MetasymbolOne,
            WildcardToken::Symbol(b'\\'),
        ];

        assert_eq!(wildcard.parsed().collect::<Vec<_>>(), expected);
    }

    #[test]
    fn test_matching_chars() {
        let pattern = "a*c".chars().collect::<Vec<char>>();
        let wildcard = Wildcard::new(&pattern).expect("invalid wildcard");

        assert!(wildcard.is_match(&['a', 'c']));
        assert!(!wildcard.is_match(&['a', 'b']));
        assert!(wildcard.is_match(&['a', 'b', 'c']));
        assert!(wildcard.is_match(&['a', 'b', 'b', 'c']));
    }

    #[test]
    fn test_matching_chars_case_insensitive() {
        let pattern = "ω*δ".chars().collect::<Vec<char>>();
        let wildcard = WildcardBuilder::new(&pattern)
            .case_insensitive(true)
            .build()
            .expect("invalid wildcard");

        assert!(wildcard.is_match(&['ω', 'Δ']));
        assert!(!wildcard.is_match(&['ω', 'x']));
        assert!(wildcard.is_match(&['Ω', 'x', 'δ']));
        assert!(wildcard.is_match(&['ω', 'x', 'x', 'Δ']));
    }

    #[test]
    fn test_capture_chars_case_insensitive() {
        let pattern = "ω*δ".chars().collect::<Vec<char>>();
        let wildcard = WildcardBuilder::new(&pattern)
            .case_insensitive(true)
            .build()
            .expect("invalid wildcard");

        assert_eq!(wildcard.captures(&['ω', 'Δ']), Some(vec![&[] as &[char]]));
        assert_eq!(wildcard.captures(&['ω', 'x']), None);
        assert_eq!(wildcard.captures(&['Ω', 'x', 'X', 'Δ']), Some(vec![&['x', 'X'] as &[char]]));
        assert_eq!(wildcard.captures(&['ω', 'ω', 'Ω', 'Δ']), Some(vec![&['ω', 'Ω'] as &[char]]));
    }

    #[derive(Clone, Debug)]
    struct WildcardAndInput {
        pattern: String,
        input: String,
    }

    struct NormalCharGen {
        chars_range: usize,
    }

    impl NormalCharGen {
        const ALPHA_CHARS: &'static str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

        fn new(gen: &mut Gen) -> NormalCharGen {
            // Bias towards a small set of characters.
            let chars_range = 1 + match u8::arbitrary(gen) % 100 {
                0..=10 => usize::arbitrary(gen) % (1 + usize::arbitrary(gen) % 2),
                11..=20 => usize::arbitrary(gen) % (1 + usize::arbitrary(gen) % 4),
                21..=30 => usize::arbitrary(gen) % (1 + usize::arbitrary(gen) % 6),
                31..=40 => usize::arbitrary(gen) % (1 + usize::arbitrary(gen) % 8),
                41..=50 => usize::arbitrary(gen) % (1 + usize::arbitrary(gen) % 10),
                _ => usize::arbitrary(gen) % NormalCharGen::ALPHA_CHARS.len(),
            };

            NormalCharGen { chars_range }
        }

        fn gen(&self, gen: &mut Gen) -> &'static str {
            let index = usize::arbitrary(gen) % self.chars_range;
            &NormalCharGen::ALPHA_CHARS[index..=index]
        }

        fn gen_maybe_special(&self, gen: &mut Gen) -> &'static str {
            match u8::arbitrary(gen) % 100 {
                0..=1 => "*",
                2..=3 => "?",
                4..=5 => r"\",
                _ => self.gen(gen),
            }
        }

        fn widen(&self, gen: &mut Gen) -> NormalCharGen {
            NormalCharGen {
                chars_range: 1
                    + (self.chars_range + (usize::arbitrary(gen) % 5))
                        % NormalCharGen::ALPHA_CHARS.len(),
            }
        }
    }

    fn arbitrary_length(gen: &mut Gen) -> usize {
        match u8::arbitrary(gen) % 100 {
            0..=15 => 0,
            16..=30 => 1 + usize::arbitrary(gen) % 5,
            31..=50 => 1 + usize::arbitrary(gen) % 10,
            _ => 1 + usize::arbitrary(gen) % gen.size(),
        }
    }

    fn wildcard_tokens_to_pattern(tokens: &[WildcardToken]) -> String {
        let mut pattern = String::with_capacity(2 * tokens.len());

        for token in tokens {
            match token {
                WildcardToken::MetasymbolAny => pattern.push('*'),
                WildcardToken::MetasymbolOne => pattern.push('?'),
                WildcardToken::Symbol(b) => match b {
                    b'*' => pattern.push_str(r"\*"),
                    b'?' => pattern.push_str(r"\?"),
                    b'\\' => pattern.push_str(r"\\"),
                    b => pattern.push(char::from(*b)),
                },
            }
        }

        pattern
    }

    fn create_input_matching_pattern(
        gen: &mut Gen,
        normal_chars_gen: &NormalCharGen,
        pattern: &[WildcardToken],
    ) -> String {
        // Let's have a wider charset than the pattern.
        let normal_chars_gen = normal_chars_gen.widen(gen);
        let mut input = String::with_capacity(pattern.len());

        for token in pattern {
            match token {
                WildcardToken::MetasymbolAny => {
                    let len = arbitrary_length(gen);

                    (0..len).for_each(|_| input.push_str(normal_chars_gen.gen_maybe_special(gen)));
                }
                WildcardToken::MetasymbolOne => {
                    input.push_str(normal_chars_gen.gen_maybe_special(gen));
                }
                WildcardToken::Symbol(b) => {
                    input.push(char::from(*b));
                }
            }
        }

        input
    }

    fn arbitrary_wildcard_token(gen: &mut Gen, normal_chars_gen: &NormalCharGen) -> WildcardToken {
        match u8::arbitrary(gen) % 100 {
            0..=20 => WildcardToken::MetasymbolAny,
            21..=30 => WildcardToken::MetasymbolOne,
            _ => {
                // We want to have a reasonable chance of hitting something that requires
                // escaping.
                match u8::arbitrary(gen) % 100 {
                    0..=5 => WildcardToken::Symbol(b'*'),
                    6..=10 => WildcardToken::Symbol(b'?'),
                    11..=15 => WildcardToken::Symbol(b'\\'),
                    _ => WildcardToken::Symbol(normal_chars_gen.gen(gen).as_bytes()[0]),
                }
            }
        }
    }

    fn arbitrary_wildcard_tokens(
        gen: &mut Gen,
        normal_chars_gen: &NormalCharGen,
    ) -> Vec<WildcardToken> {
        let len = arbitrary_length(gen);

        (0..len).map(|_| arbitrary_wildcard_token(gen, normal_chars_gen)).collect()
    }

    fn arbitrary_input(gen: &mut Gen, normal_chars_gen: &NormalCharGen) -> String {
        // Let's have a wider charset than the pattern.
        let normal_chars_gen = normal_chars_gen.widen(gen);
        let len = arbitrary_length(gen);

        (0..len).map(|_| normal_chars_gen.gen_maybe_special(gen)).collect()
    }

    impl Arbitrary for WildcardAndInput {
        fn arbitrary(gen: &mut Gen) -> WildcardAndInput {
            let will_match = bool::arbitrary(gen);

            match will_match {
                true => {
                    let WildcardAndMatchingInput { pattern, input } =
                        WildcardAndMatchingInput::arbitrary(gen);

                    WildcardAndInput { pattern, input }
                }
                false => {
                    let normal_chars_gen = NormalCharGen::new(gen);
                    let pattern_tokens = arbitrary_wildcard_tokens(gen, &normal_chars_gen);
                    let pattern = wildcard_tokens_to_pattern(&pattern_tokens);

                    let input = arbitrary_input(gen, &normal_chars_gen);

                    WildcardAndInput { pattern, input }
                }
            }
        }
    }

    /// Test case where the input matches the pattern.
    #[derive(Clone, Debug)]
    struct WildcardAndMatchingInput {
        pattern: String,
        input: String,
    }

    impl Arbitrary for WildcardAndMatchingInput {
        fn arbitrary(gen: &mut Gen) -> WildcardAndMatchingInput {
            let normal_chars_gen = NormalCharGen::new(gen);
            let pattern_tokens = arbitrary_wildcard_tokens(gen, &normal_chars_gen);
            let pattern = wildcard_tokens_to_pattern(&pattern_tokens);

            let input = {
                let input = create_input_matching_pattern(gen, &normal_chars_gen, &pattern_tokens);

                assert!(
                        engine_regex_bytes::matches(&pattern, input.as_bytes(), false),
                        "failed to create an input that matched the pattern\npattern: {pattern}\ninput  : {input}",
                    );

                input
            };

            WildcardAndMatchingInput { pattern, input }
        }
    }

    #[quickcheck]
    fn property_matching_equivalent_to_regex_engine(
        WildcardAndInput { pattern, input }: WildcardAndInput,
    ) -> bool {
        let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");

        wildcard.is_match(input.as_bytes())
            == engine_regex_bytes::matches(&pattern, input.as_bytes(), false)
    }

    #[quickcheck]
    fn property_capture_equivalent_to_regex_engine(
        WildcardAndInput { pattern, input }: WildcardAndInput,
    ) -> bool {
        let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");

        wildcard.captures(input.as_bytes())
            == engine_regex_bytes::captures(&pattern, input.as_bytes(), false)
    }

    #[quickcheck]
    fn property_capture_length_equals_number_of_metacharacters(
        WildcardAndMatchingInput { pattern, input }: WildcardAndMatchingInput,
    ) -> bool {
        let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");
        let metacharacter_count = wildcard.parsed().filter(|token| token.is_metasymbol()).count();

        let captures = wildcard
            .captures(input.as_bytes())
            .map(|c| c.len())
            .expect("this test should only get matching test cases");

        captures == metacharacter_count
    }

    #[quickcheck]
    fn property_captures_agree_with_is_match(
        WildcardAndInput { pattern, input }: WildcardAndInput,
    ) -> bool {
        let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");

        let captures = wildcard.captures(input.as_bytes()).map(|c| c.len());

        captures.is_some() == wildcard.is_match(input.as_bytes())
    }

    #[quickcheck]
    fn property_captures_filled_in_metasymbols_matches_input(
        WildcardAndMatchingInput { pattern, input }: WildcardAndMatchingInput,
    ) -> bool {
        let wildcard = Wildcard::new(pattern.as_bytes()).expect("invalid wildcard");

        let mut captures = wildcard
            .captures(input.as_bytes())
            .expect("this test should only get matching test cases")
            .into_iter();

        let mut pattern_filled_in = String::with_capacity(input.len());

        for token in wildcard.parsed() {
            match token {
                WildcardToken::MetasymbolAny | WildcardToken::MetasymbolOne => {
                    let fill = captures.next().expect("must be present");

                    pattern_filled_in.push_str(std::str::from_utf8(fill).expect("invalid utf-8"));
                }
                WildcardToken::Symbol(b) => pattern_filled_in.push(char::from(b)),
            }
        }

        pattern_filled_in == input
    }
}
