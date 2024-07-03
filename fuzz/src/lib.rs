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

pub mod engine_regex_bytes {
    use regex::bytes::{Regex, RegexBuilder};
    use wildcard::{Wildcard, WildcardToken};

    fn make_regex(pattern: &[u8], case_insensitive: bool) -> Result<Regex, &'static str> {
        let wildcard = Wildcard::new(pattern).map_err(|_| "invalid wildcard")?;
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
                    let s = std::str::from_utf8(slice)
                        .map_err(|_| "invalid utf-8 symbol in pattern")?;
                    regex_pattern.push_str(&regex::escape(s));
                }
            }
        }

        regex_pattern.push('$');

        let regex = RegexBuilder::new(&regex_pattern)
            .dot_matches_new_line(true)
            .crlf(false)
            .unicode(false)
            .case_insensitive(case_insensitive)
            .build()
            .expect("invalid regex");

        Ok(regex)
    }

    pub fn matches(
        pattern: &[u8],
        input: &[u8],
        case_insensitive: bool,
    ) -> Result<bool, &'static str> {
        Ok(make_regex(pattern, case_insensitive)?.is_match(input))
    }

    pub fn captures<'a>(
        pattern: &[u8],
        input: &'a [u8],
        case_insensitive: bool,
    ) -> Result<Option<Vec<&'a [u8]>>, &'static str> {
        let captures = make_regex(pattern, case_insensitive)?.captures(input).map(|c| {
            c.iter().flat_map(IntoIterator::into_iter).skip(1).map(|m| m.as_bytes()).collect()
        });

        Ok(captures)
    }
}
