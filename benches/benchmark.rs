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

#![allow(missing_docs)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::missing_panics_doc)]

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::time::Duration;

mod engine_wildmatch {
    use wildmatch::WildMatch;

    pub fn compile(pattern: &str) -> WildMatch {
        WildMatch::new(pattern)
    }

    pub fn matches(pattern: &str, input: &str) -> bool {
        compile(pattern).matches(input)
    }

    pub fn matches_compiled(compiled: &WildMatch, input: &str) -> bool {
        compiled.matches(input)
    }
}

mod engine_wildcard {
    use wildcard::Wildcard;

    pub fn compile(pattern: &[u8]) -> Wildcard<'_> {
        Wildcard::new(pattern).expect("invalid wildcard")
    }

    pub fn matches(pattern: &[u8], input: &[u8]) -> bool {
        compile(pattern).is_match(input)
    }

    pub fn matches_compiled(compiled: &Wildcard<'_>, input: &[u8]) -> bool {
        compiled.is_match(input)
    }

    pub fn captures<'a>(pattern: &[u8], input: &'a [u8]) -> Option<Vec<&'a [u8]>> {
        compile(pattern).captures(input)
    }

    pub fn captures_compiled<'a>(
        compiled: &Wildcard<'_>,
        input: &'a [u8],
    ) -> Option<Vec<&'a [u8]>> {
        compiled.captures(input)
    }
}

mod engine_regex_bytes {
    use regex::bytes::{Captures, Regex, RegexBuilder};
    use wildcard::{Wildcard, WildcardToken};

    pub fn compile(pattern: &str) -> Regex {
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
            .build()
            .expect("invalid regex")
    }

    pub fn matches(pattern: &str, input: &[u8]) -> bool {
        compile(pattern).is_match(input)
    }

    pub fn matches_compiled(compiled: &Regex, input: &[u8]) -> bool {
        compiled.is_match(input)
    }

    pub fn captures<'a>(pattern: &str, input: &'a [u8]) -> Option<Captures<'a>> {
        compile(pattern).captures(input)
    }

    pub fn captures_compiled<'a>(compiled: &Regex, input: &'a [u8]) -> Option<Captures<'a>> {
        compiled.captures(input)
    }
}

fn make_testcase_input(len: usize) -> String {
    let foo_count = len / 4 - 8;

    let input = format!(
        "fooo{}fooo{}fooo{}fooo{}foyofooofozobaar",
        "fofo".repeat(foo_count / 4),
        "oooo".repeat(foo_count / 4),
        "foof".repeat(foo_count / 4),
        "baar".repeat(foo_count / 4),
    );

    assert_eq!(input.len(), len);

    input
}

fn benchmark_comparison_matches_bytes_backtrack_heavy(c: &mut Criterion) {
    const PATTERN: &str = "fooo*fooo*fooo*fooo*fooo*baar";
    const SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128];

    for size_kib in SIZES {
        assert!(engine_regex_bytes::matches(
            PATTERN,
            make_testcase_input(size_kib * 1024).as_bytes()
        ));
    }

    let mut group = c.benchmark_group("comparison_matches_bytes_backtrack_heavy");

    group.sample_size(1000);

    for size_kib in SIZES {
        let input = make_testcase_input(size_kib * 1024);

        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input("regex", size_kib, |b, _| {
            b.iter(|| engine_regex_bytes::matches(PATTERN, input.as_bytes()));
        });

        let regex_compiled = engine_regex_bytes::compile(PATTERN);

        group.bench_with_input("regex (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_regex_bytes::matches_compiled(&regex_compiled, input.as_bytes()));
        });

        group.bench_with_input("wildmatch", size_kib, |b, _| {
            b.iter(|| engine_wildmatch::matches(PATTERN, &input));
        });

        let wildcard_compiled = engine_wildmatch::compile(PATTERN);

        group.bench_with_input("wildmatch (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_wildmatch::matches_compiled(&wildcard_compiled, &input));
        });

        group.bench_with_input("wildcard", size_kib, |b, _| {
            b.iter(|| engine_wildcard::matches(PATTERN.as_bytes(), input.as_bytes()));
        });

        let wildcard_compiled = engine_wildcard::compile(PATTERN.as_bytes());

        group.bench_with_input("wildcard (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_wildcard::matches_compiled(&wildcard_compiled, input.as_bytes()));
        });
    }

    group.finish();
}

fn benchmark_wildcard_matches_bytes_backtrack_heavy(c: &mut Criterion) {
    const PATTERN: &str = "fooo*fooo*fooo*fooo*fooo*baar";
    const SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128];

    for size_kib in SIZES {
        assert!(engine_regex_bytes::matches(
            PATTERN,
            make_testcase_input(size_kib * 1024).as_bytes()
        ));
    }

    let mut group = c.benchmark_group("wildcard_matches_bytes_backtrack_heavy");

    group.sample_size(1000);

    for size_kib in SIZES {
        let input = make_testcase_input(size_kib * 1024);

        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input("wildcard", size_kib, |b, _| {
            b.iter(|| engine_wildcard::matches(PATTERN.as_bytes(), input.as_bytes()));
        });

        let wildcard_compiled = engine_wildcard::compile(PATTERN.as_bytes());

        group.bench_with_input("wildcard (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_wildcard::matches_compiled(&wildcard_compiled, input.as_bytes()));
        });
    }

    group.finish();
}

fn benchmark_comparison_captures_bytes_backtrack_heavy(c: &mut Criterion) {
    const PATTERN: &str = "fooo*fooo*fooo*fooo*fooo*baar";
    const SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128];

    for size_kib in SIZES {
        assert!(engine_regex_bytes::matches(
            PATTERN,
            make_testcase_input(size_kib * 1024).as_bytes()
        ));
    }

    let mut group = c.benchmark_group("comparison_captures_bytes_backtrack_heavy");

    group.sample_size(1000);

    for size_kib in SIZES {
        let input = make_testcase_input(size_kib * 1024);

        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input("regex", size_kib, |b, _| {
            b.iter(|| engine_regex_bytes::captures(PATTERN, input.as_bytes()));
        });

        let regex_compiled = engine_regex_bytes::compile(PATTERN);

        group.bench_with_input("regex (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_regex_bytes::captures_compiled(&regex_compiled, input.as_bytes()));
        });

        group.bench_with_input("wildcard", size_kib, |b, _| {
            b.iter(|| engine_wildcard::captures(PATTERN.as_bytes(), input.as_bytes()));
        });

        let wildcard_compiled = engine_wildcard::compile(PATTERN.as_bytes());

        group.bench_with_input("wildcard (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_wildcard::captures_compiled(&wildcard_compiled, input.as_bytes()));
        });
    }

    group.finish();
}

fn benchmark_wildcard_captures_bytes_backtrack_heavy(c: &mut Criterion) {
    const PATTERN: &str = "fooo*fooo*fooo*fooo*fooo*baar";
    const SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128];

    for size_kib in SIZES {
        assert!(engine_regex_bytes::matches(
            PATTERN,
            make_testcase_input(size_kib * 1024).as_bytes()
        ));
    }

    let mut group = c.benchmark_group("wildcard_captures_bytes_backtrack_heavy");

    group.sample_size(1000);

    for size_kib in SIZES {
        let input = make_testcase_input(size_kib * 1024);

        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input("wildcard", size_kib, |b, _| {
            b.iter(|| engine_wildcard::captures(PATTERN.as_bytes(), input.as_bytes()));
        });

        let wildcard_compiled = engine_wildcard::compile(PATTERN.as_bytes());

        group.bench_with_input("wildcard (pre-compiled)", size_kib, |b, _| {
            b.iter(|| engine_wildcard::captures_compiled(&wildcard_compiled, input.as_bytes()));
        });
    }

    group.finish();
}

#[derive(serde::Deserialize)]
struct Inputs {
    #[serde(rename = "match")]
    match_: Vec<String>,
    no_match: Vec<String>,
}

#[derive(serde::Deserialize)]
struct Benchmark {
    pattern: String,
    inputs: Inputs,
}

#[derive(serde::Deserialize)]
struct Benchmarks {
    benchmarks: Vec<Benchmark>,
}

const BENCHDATA_SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128];

fn read_benchmark(size_kib: usize) -> Benchmarks {
    let benches =
        std::fs::read_to_string(format!("benches/benchdata/benchmarks_{}k.toml", size_kib))
            .expect("failed to read benchmark data");

    toml::from_str(&benches).expect("failed to parse benchmark file")
}

fn benchmark_benchdata_comparison_matches(c: &mut Criterion) {
    let mut group = c.benchmark_group("benchdata_comparison_matches");

    group.sample_size(100);
    group.measurement_time(Duration::from_secs(300));

    for &size_kib in BENCHDATA_SIZES {
        let benchmarks = read_benchmark(size_kib);

        let throughput = benchmarks
            .benchmarks
            .iter()
            .flat_map(|b| b.inputs.match_.iter().chain(&b.inputs.no_match))
            .map(|input| input.len() as u64)
            .sum();

        group.throughput(Throughput::Bytes(throughput));

        group.bench_with_input("regex", &size_kib, |b, _| {
            b.iter(|| {
                for benchmark in &benchmarks.benchmarks {
                    let pattern = &benchmark.pattern;

                    for input in benchmark.inputs.match_.iter().chain(&benchmark.inputs.no_match) {
                        criterion::black_box(engine_regex_bytes::matches(
                            &pattern,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        let regexes_compiled: Vec<_> =
            benchmarks.benchmarks.iter().map(|b| engine_regex_bytes::compile(&b.pattern)).collect();

        group.bench_with_input("regex (pre-compiled)", &size_kib, |b, _| {
            b.iter(|| {
                for (benchmark, regex_compiled) in
                    benchmarks.benchmarks.iter().zip(&regexes_compiled)
                {
                    for input in
                        benchmark.inputs.match_.iter().chain(benchmark.inputs.no_match.iter())
                    {
                        criterion::black_box(engine_regex_bytes::matches_compiled(
                            &regex_compiled,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        group.bench_with_input("wildmatch", &size_kib, |b, _| {
            b.iter(|| {
                for benchmark in &benchmarks.benchmarks {
                    let pattern = &benchmark.pattern;

                    for input in benchmark.inputs.match_.iter().chain(&benchmark.inputs.no_match) {
                        criterion::black_box(engine_wildmatch::matches(&pattern, input));
                    }
                }
            });
        });

        let wildmatchs_compiled: Vec<_> =
            benchmarks.benchmarks.iter().map(|b| engine_wildmatch::compile(&b.pattern)).collect();

        group.bench_with_input("wildmatch (pre-compiled)", &size_kib, |b, _| {
            b.iter(|| {
                for (benchmark, wildmatch_compiled) in
                    benchmarks.benchmarks.iter().zip(&wildmatchs_compiled)
                {
                    for input in
                        benchmark.inputs.match_.iter().chain(benchmark.inputs.no_match.iter())
                    {
                        criterion::black_box(engine_wildmatch::matches_compiled(
                            &wildmatch_compiled,
                            input,
                        ));
                    }
                }
            });
        });

        group.bench_with_input("wildcard", &size_kib, |b, _| {
            b.iter(|| {
                for benchmark in &benchmarks.benchmarks {
                    let pattern = &benchmark.pattern;

                    for input in benchmark.inputs.match_.iter().chain(&benchmark.inputs.no_match) {
                        criterion::black_box(engine_wildcard::matches(
                            pattern.as_bytes(),
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        let wildcards_compiled: Vec<_> = benchmarks
            .benchmarks
            .iter()
            .map(|b| engine_wildcard::compile(b.pattern.as_bytes()))
            .collect();

        group.bench_with_input("wildcard (pre-compiled)", &size_kib, |b, _| {
            b.iter(|| {
                for (benchmark, wildcard_compiled) in
                    benchmarks.benchmarks.iter().zip(&wildcards_compiled)
                {
                    for input in
                        benchmark.inputs.match_.iter().chain(benchmark.inputs.no_match.iter())
                    {
                        criterion::black_box(engine_wildcard::matches_compiled(
                            &wildcard_compiled,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });
    }

    group.finish();
}

fn benchmark_benchdata_comparison_captures(c: &mut Criterion) {
    let mut group = c.benchmark_group("benchdata_comparison_captures");

    group.sample_size(100);
    group.measurement_time(Duration::from_secs(300));

    for &size_kib in BENCHDATA_SIZES {
        let benchmarks = read_benchmark(size_kib);

        let throughput = benchmarks
            .benchmarks
            .iter()
            .flat_map(|b| b.inputs.match_.iter().chain(&b.inputs.no_match))
            .map(|input| input.len() as u64)
            .sum();

        group.throughput(Throughput::Bytes(throughput));

        group.bench_with_input("regex", &size_kib, |b, _| {
            b.iter(|| {
                for benchmark in &benchmarks.benchmarks {
                    let pattern = &benchmark.pattern;

                    for input in benchmark.inputs.match_.iter().chain(&benchmark.inputs.no_match) {
                        criterion::black_box(engine_regex_bytes::captures(
                            &pattern,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        let regexes_compiled: Vec<_> =
            benchmarks.benchmarks.iter().map(|b| engine_regex_bytes::compile(&b.pattern)).collect();

        group.bench_with_input("regex (pre-compiled)", &size_kib, |b, _| {
            b.iter(|| {
                for (benchmark, regex_compiled) in
                    benchmarks.benchmarks.iter().zip(&regexes_compiled)
                {
                    for input in
                        benchmark.inputs.match_.iter().chain(benchmark.inputs.no_match.iter())
                    {
                        criterion::black_box(engine_regex_bytes::captures_compiled(
                            &regex_compiled,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        group.bench_with_input("wildcard", &size_kib, |b, _| {
            b.iter(|| {
                for benchmark in &benchmarks.benchmarks {
                    let pattern = &benchmark.pattern;

                    for input in benchmark.inputs.match_.iter().chain(&benchmark.inputs.no_match) {
                        criterion::black_box(engine_wildcard::captures(
                            pattern.as_bytes(),
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });

        let wildcards_compiled: Vec<_> = benchmarks
            .benchmarks
            .iter()
            .map(|b| engine_wildcard::compile(b.pattern.as_bytes()))
            .collect();

        group.bench_with_input("wildcard (pre-compiled)", &size_kib, |b, _| {
            b.iter(|| {
                for (benchmark, wildcard_compiled) in
                    benchmarks.benchmarks.iter().zip(&wildcards_compiled)
                {
                    for input in
                        benchmark.inputs.match_.iter().chain(benchmark.inputs.no_match.iter())
                    {
                        criterion::black_box(engine_wildcard::captures_compiled(
                            &wildcard_compiled,
                            input.as_bytes(),
                        ));
                    }
                }
            });
        });
    }

    group.finish();
}

criterion_group!(
    benchmark,
    benchmark_comparison_matches_bytes_backtrack_heavy,
    benchmark_wildcard_matches_bytes_backtrack_heavy,
    benchmark_comparison_captures_bytes_backtrack_heavy,
    benchmark_wildcard_captures_bytes_backtrack_heavy,
    benchmark_benchdata_comparison_matches,
    benchmark_benchdata_comparison_captures,
);
criterion_main!(benchmark);
