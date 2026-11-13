//! 10,000 random requests from a fixed seed, each run through `execute` and
//! written with `serialize`: none panics, every outcome is a value, a state
//! or an error of a kind that a request without a deadline or a cancellation
//! may end with, and every error has its fallback line, with at most the
//! nested frames that the contract bounds.
//!
//! The requests fall into four categories with fixed counts: 4,000 general
//! requests, with random operations, variables, inputs and limits, some of
//! them with an entry of the operand table; 2,000
//! with exponents near $2^{32}$, near $2^{63}$ and near the `u64` bound;
//! 2,000 under limits with fields at their largest value, `u64::MAX`, all
//! of them or one at a time; and 2,000 with deeply nested inputs, up to
//! 20,000 levels, under the default `max_depth` and under raised ones.
//! Request `i` is generated from the seed `SEED + i` alone, so a failing
//! request is reproduced from the index and the seed that the failure
//! prints.
//!
//! `max_integer_bits` is the limit that bounds a power of numbers before it
//! is computed, and the work of a power is charged before it is computed,
//! by the machine words of the operands of its squarings and
//! multiplications. With `max_exponent` and `max_integer_bits` both at
//! `u64::MAX`, a power such as $3^{4294967023}$ therefore fails at once
//! under the default `max_work`; with `max_work` raised far enough as well,
//! it is computed in full, for minutes, before any limit can stop it: a
//! primitive operation is not interrupted, and real memory and CPU time are
//! bounded by the host, as the command contract states. So that the test
//! ends in bounded time, the exponent category still keeps
//! `max_integer_bits` at most $2^{20}$, and the inputs of the category of
//! largest limits, where `max_work` can be `u64::MAX`, keep their size and
//! the degrees of their powers small.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the test panics with the seed and the index of a failing request"
)]

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

use kalyx::command::serialize;
use kalyx::context::CancelFlag;
use kalyx::{
    Context, ErrorKind, FaultKind, LimitField, LimitId, Limits, Request, Settled, execute,
};

/// The seed of the requests.
const SEED: u64 = 0x5EED_0000_0000_0203;

/// The categories, in the order of the requests, with their counts.
const CATEGORIES: [(Category, u64); 4] = [
    (Category::General, 4_000),
    (Category::Exponents, 2_000),
    (Category::LargestLimits, 2_000),
    (Category::Deep, 2_000),
];

/// The deepest nesting of the deep category.
const DEEPEST: u64 = 20_000;

/// The most nested frames of an error, the bound $d$ of the contract of the
/// command entry.
const NESTED_FRAMES: usize = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Category {
    General,
    Exponents,
    LargestLimits,
    Deep,
}

/// SplitMix64, a fixed-seed generator written here; the tests use no
/// external generator.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

// ---------------------------------------------------------------------------
// The generators

/// An operation: mostly those of the dispatch table, sometimes another.
fn operation(random: &mut SplitMix64) -> &'static str {
    random.pick(&[
        "eval", "expand", "diff", "eval", "expand", "diff", "eval", "expand", "diff", "simplify",
        "", "EVAL",
    ])
}

/// One of the three operations of the dispatch table, for the categories
/// that test the boundaries of the operations.
fn table_operation(random: &mut SplitMix64) -> &'static str {
    random.pick(&["eval", "expand", "diff"])
}

/// A variable: mostly valid, sometimes empty, reserved or malformed.
fn variable(random: &mut SplitMix64) -> &'static str {
    random.pick(&[
        "x", "x", "x", "t", "y", "X", "x_1", "", "pi", "1x", "x y", "\u{e9}",
    ])
}

/// A leaf of an expression: symbols, small and large numbers, decimals and
/// now and then a stray character.
fn leaf(random: &mut SplitMix64) -> String {
    match random.below(12) {
        0 => random.next().to_string(),
        1 => format!("{}.{}", random.below(1000), random.below(1000)),
        2 => format!("{}/{}", random.below(100), random.below(100)),
        3 => random
            .pick(&[
                "#", "1.2.3", ")", "(", "^", "\t", "\u{3be}", "sin(x)", "x y", "",
            ])
            .to_owned(),
        _ => random
            .pick(&[
                "x", "t", "y", "X", "1", "2", "3", "1/2", "0.5", "12", "0", "x_1", "-1",
            ])
            .to_owned(),
    }
}

/// A random expression of the grammar, with every operator and
/// parentheses, and faults: divisions by zero, exponents that are not
/// integers and stray characters.
fn expression(random: &mut SplitMix64, depth: u32) -> String {
    if depth == 0 || random.below(4) == 0 {
        return leaf(random);
    }
    let left = expression(random, depth - 1);
    match random.below(10) {
        0 => format!("-{left}"),
        1 => format!("({left})"),
        2 => format!(
            "{left}^{}",
            random.pick(&["2", "3", "0", "(-1)", "5", "17"])
        ),
        3 => format!(
            "{left}^{}",
            random.pick(&["x", "(1/2)", "300", "0.5", "(2^3)"])
        ),
        4 => format!("{left}/{}", random.pick(&["0", "2", "(x-x)", "x", "(1-1)"])),
        5 => format!("({left})*({})", expression(random, depth - 1)),
        6 => format!(" {left} "),
        _ => {
            let operator = random.pick(&[" + ", "-", "*", " - ", "+", "/"]);
            format!("{left}{operator}{}", expression(random, depth - 1))
        }
    }
}

/// Limits of a general request: the defaults, or the defaults with one
/// field set to a small value, to 0 or to any value.
fn general_limits(random: &mut SplitMix64) -> Limits {
    let value = match random.below(3) {
        0 => random.below(64),
        1 => random.below(100_000),
        _ => random.next(),
    };
    with_field(Limits::new(), random.below(12), value)
}

/// `limits` with field `field`, from 0 to 8 in the order of `Limits`, set
/// to `value`; any other number leaves them as they are.
fn with_field(limits: Limits, field: u64, value: u64) -> Limits {
    match field {
        0 => limits.with_max_work(value),
        1 => limits.with_max_input_bytes(value),
        2 => limits.with_max_output_bytes(value),
        3 => limits.with_max_depth(value),
        4 => limits.with_max_nodes(value),
        5 => limits.with_max_storage_bytes(value),
        6 => limits.with_max_integer_bits(value),
        7 => limits.with_max_exponent(value),
        8 => limits.with_max_frames(value),
        _ => limits,
    }
}

/// A general request.
fn general(random: &mut SplitMix64) -> (Request, Limits) {
    let input = match random.below(25) {
        0 => String::new(),
        1 => "   ".to_owned(),
        _ => expression(random, 5),
    };
    let request = Request::new(operation(random), variable(random), &input)
        .with_input_version(random.next())
        .with_context_version(random.below(10))
        .with_settings_version(random.next());
    let limits = general_limits(random);
    // Drawn after the rest, so the other fields stay those of a request
    // without a table.
    let request = match random.below(10) {
        0 => {
            let role = random.pick(&["scope", "order", "input", "", "x"]);
            request.with_operand(role, &expression(random, 2))
        }
        _ => request,
    };
    (request, limits)
}

/// An exponent near $2^{32}$, $2^{63}$ or the `u64` bound, written as a
/// literal or as an expression; some of them are beyond `u64`.
fn large_exponent(random: &mut SplitMix64) -> String {
    let near = |random: &mut SplitMix64, at: u128| {
        let offset = u128::from(random.below(2_001));
        (at + offset).saturating_sub(1_000).to_string()
    };
    match random.below(8) {
        0 | 1 => near(random, 1 << 32),
        2 => near(random, 1 << 63),
        3 => near(random, u128::from(u64::MAX)),
        4 => random
            .pick(&[
                "4294967295",
                "4294967296",
                "4294967297",
                "18446744073709551615",
                "18446744073709551616",
                "9223372036854775807",
                "9223372036854775808",
            ])
            .to_owned(),
        5 => random
            .pick(&[
                "(2^32)", "(2^32-1)", "(2^64-1)", "(2^64)", "(2^63)", "(4^16)",
            ])
            .to_owned(),
        _ => (u64::MAX - random.below(4)).to_string(),
    }
}

/// The largest `max_integer_bits` of the exponent category: $2^{20}$.
const WIDEST: u64 = 1 << 20;

/// A request with exponents near the bounds, on bases of every kind, under
/// the default limits, with `max_exponent` at `u64::MAX`, or with random
/// limits, `max_integer_bits` at most `WIDEST` in each case.
fn exponents(random: &mut SplitMix64) -> (Request, Limits) {
    let base = random.pick(&[
        "x", "2", "(-1)", "1", "0", "(1/2)", "(x+1)", "(-2)", "(3/7)", "x^2", "(1-x)", "t", "y",
    ]);
    let e = large_exponent(random);
    let f = large_exponent(random);
    let input = match random.below(9) {
        0 => format!("{base}^{e}"),
        1 => format!("{base}^(-{e})"),
        2 => format!("({base}^{e})^{f}"),
        3 => format!("{base}^{e}*{base}^(-{e})"),
        4 => format!("{base}^{e} - {base}^{e}"),
        5 => format!("{base}^{e}*{base}^{f}"),
        6 => format!("({base})^{e}/({base})^{e}"),
        7 => format!("{base}^{e} + {}", expression(random, 2)),
        _ => format!("x^{e}*x^{f}*x^{e}"),
    };
    let limits = match random.below(5) {
        0 => Limits::new(),
        1 => Limits::new().with_max_exponent(u64::MAX),
        2 => Limits::new().with_max_integer_bits(WIDEST),
        3 => Limits::new()
            .with_max_exponent(u64::MAX)
            .with_max_integer_bits(WIDEST),
        _ => {
            let limits = general_limits(random);
            limits.with_max_integer_bits(limits.max_integer_bits.min(WIDEST))
        }
    };
    (Request::new(table_operation(random), "x", &input), limits)
}

/// A leaf whose powers stay small: a symbol or a small number.
fn small_leaf(random: &mut SplitMix64) -> &'static str {
    random.pick(&[
        "x", "x", "t", "1", "2", "3", "1/2", "0.25", "0", "-1", "7/3", "(x+1)", "(1-x)",
    ])
}

/// An expression of bounded size and degree: sums and products of at most
/// four factors each, whose factors are leaves raised at most to the power
/// 12, now and then with a division or a fault.
fn bounded_expression(random: &mut SplitMix64) -> String {
    let terms = 1 + random.below(4);
    let mut text = String::new();
    for index in 0..terms {
        if index > 0 {
            text.push_str(random.pick(&[" + ", " - ", "+", "-"]));
        }
        let factors = 1 + random.below(4);
        for factor in 0..factors {
            if factor > 0 {
                text.push_str(random.pick(&["*", "*", "/"]));
            }
            text.push_str(small_leaf(random));
            match random.below(4) {
                0 => text.push_str(&format!("^{}", random.below(13))),
                1 => text.push_str(&format!("^(-{})", random.below(4))),
                2 if random.below(8) == 0 => text.push_str(random.pick(&["^(1/2)", "^x", "/0"])),
                _ => {}
            }
        }
    }
    text
}

/// A request under limits with fields at `u64::MAX`: every field, or one
/// field at a time, in turn.
fn largest_limits(random: &mut SplitMix64, index: u64) -> (Request, Limits) {
    let limits = if index.is_multiple_of(2) {
        (0..9).fold(Limits::new(), |limits, field| {
            with_field(limits, field, u64::MAX)
        })
    } else {
        with_field(Limits::new(), (index / 2) % 9, u64::MAX)
    };
    let input = bounded_expression(random);
    let variable = random.pick(&["x", "x", "x", "t"]);
    (
        Request::new(table_operation(random), variable, &input),
        limits,
    )
}

/// A deeply nested input of up to `DEEPEST` levels, in one of seven
/// shapes, under the default limits, a `max_depth` just above or below its
/// depth, or `max_depth` at `u64::MAX`.
fn deep(random: &mut SplitMix64) -> (Request, Limits) {
    let levels = match random.below(3) {
        0 => 100 + random.below(1_000),
        1 => 1_000 + random.below(5_000),
        _ => 1 + random.below(DEEPEST),
    };
    let n = levels as usize;
    let leaf = random.pick(&["1", "x", "1/2", "t"]);
    let input = match random.below(7) {
        0 => format!("{}{leaf}{}", "(".repeat(n), ")".repeat(n)),
        1 => format!("{}{leaf}{}", "1+(".repeat(n), ")".repeat(n)),
        2 => format!("{}{leaf}{}", "(".repeat(n), "+1)".repeat(n)),
        3 => format!("{}{leaf}", "-".repeat(n)),
        4 => format!("{leaf}{}", "^1".repeat(n)),
        5 => format!("{}{leaf}{}", "x*(".repeat(n), ")".repeat(n)),
        _ => format!("{}{leaf}{}", "-(".repeat(n), ")".repeat(n)),
    };
    let limits = match random.below(4) {
        0 => Limits::new(),
        1 => Limits::new().with_max_depth(2 * levels + 2),
        2 => Limits::new().with_max_depth(levels / 2),
        _ => Limits::new().with_max_depth(u64::MAX),
    }
    .with_max_input_bytes(1 << 20);
    (Request::new(table_operation(random), "x", &input), limits)
}

/// Request `index` of `category`, generated from its own seed.
fn request(category: Category, index: u64) -> (Request, Limits) {
    let random = &mut SplitMix64(SEED.wrapping_add(index));
    match category {
        Category::General => general(random),
        Category::Exponents => exponents(random),
        Category::LargestLimits => largest_limits(random, index),
        Category::Deep => deep(random),
    }
}

/// Every request of the test, as its category and its index, in order:
/// the counts of `CATEGORIES`, with indices from 0 to 9,999.
fn schedule() -> Vec<(Category, u64)> {
    let mut all = Vec::new();
    let mut index = 0;
    for (category, count) in CATEGORIES {
        for _ in 0..count {
            all.push((category, index));
            index += 1;
        }
    }
    all
}

/// The levels of nesting of an input of the deep category: the most
/// parentheses, minus signs or powers `^1` that it holds.
fn levels(input: &str) -> u64 {
    let parentheses = input.matches('(').count();
    let minus = input.matches('-').count();
    let powers = input.matches("^1").count();
    parentheses.max(minus).max(powers) as u64
}

/// The decimal literals of `input`.
fn literals(input: &str) -> Vec<u128> {
    input
        .split(|character: char| !character.is_ascii_digit())
        .filter_map(|digits| digits.parse().ok())
        .collect()
}

/// Whether `input` holds an exponent near $2^{32}$: a literal within 1,000
/// of it, or `(2^32)` or `(2^32-1)`.
fn near_two_to_the_32(input: &str) -> bool {
    literals(input)
        .iter()
        .any(|value| value.abs_diff(1 << 32) <= 1_000)
        || input.contains("(2^32)")
        || input.contains("(2^32-1)")
}

/// Whether `input` holds an exponent near the `u64` bound: a literal within
/// 1,000 of `u64::MAX`, or `(2^64-1)` or `(2^64)`.
fn near_the_u64_bound(input: &str) -> bool {
    literals(input)
        .iter()
        .any(|value| value.abs_diff(u128::from(u64::MAX)) <= 1_000)
        || input.contains("(2^64-1)")
        || input.contains("(2^64)")
}

// ---------------------------------------------------------------------------
// The property

/// Whether `kind` may end a request that has no deadline and no
/// cancellation: a `ResourceLimit` or a fault of the input. `Internal`, a
/// defect of the library, may not, and neither may `OutsideDomain` or
/// `VariableMismatch`, faults of the input that no operation of the command
/// entry reaches.
fn is_listed(kind: ErrorKind) -> bool {
    matches!(
        kind,
        ErrorKind::ResourceLimit
            | ErrorKind::Fault(
                FaultKind::Syntax
                    | FaultKind::UnknownSymbol
                    | FaultKind::DivisionByZero
                    | FaultKind::NonIntegerExponent
                    | FaultKind::NotPolynomial
                    | FaultKind::Unsupported
            )
    )
}

/// Runs one request and its line, and returns the name of its result:
/// `value`, `state` or the kind of its error, with the limit for a
/// `ResourceLimit`. Fails when the outcome or the error of `serialize` is
/// not listed, a line is not one whole line, or an error has more nested
/// frames than the bound or no fallback line under
/// `Context::new(Limits::new(), CancelFlag::new())`.
fn check(request: &Request, limits: Limits) -> Result<String, String> {
    let mut own = Context::new(limits, CancelFlag::new());
    let outcome = execute(request, &mut own);
    let name = match outcome.result() {
        Ok(Settled::Value(_)) => "value".to_owned(),
        Ok(Settled::State(state)) => format!("state {state:?}"),
        Ok(other) => return Err(format!("an unknown result: {other:?}")),
        Err(error) if !is_listed(error.kind()) => {
            return Err(format!("an error of a kind not listed: {error:?}"));
        }
        Err(error) => match error.exceeded().map(|exceeded| exceeded.id()) {
            Some(LimitId::Field(field)) => format!("ResourceLimit {}", field.name()),
            Some(other) => format!("ResourceLimit {other:?}"),
            None => format!("{:?}", error.kind()),
        },
    };
    if let Err(error) = outcome.result() {
        if error.frames().len().saturating_sub(1) > NESTED_FRAMES {
            return Err(format!("more nested frames than the bound: {error:?}"));
        }
        let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
        match serialize(&outcome, fresh) {
            Ok(line) if line.last() == Some(&b'\n') => {}
            Ok(line) => return Err(format!("not one whole fallback line: {line:?}")),
            Err(error) => return Err(format!("the fallback line failed: {error:?}")),
        }
    }
    let line = match serialize(&outcome, &mut own) {
        Ok(line) => Some(line),
        Err(error) if error.kind() != ErrorKind::ResourceLimit => {
            return Err(format!("serialize failed with {error:?}"));
        }
        Err(_) if outcome.result().is_err() => {
            let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
            match serialize(&outcome, fresh) {
                Ok(line) => Some(line),
                Err(error) => return Err(format!("the fallback line failed: {error:?}")),
            }
        }
        Err(_) => None,
    };
    if let Some(line) = line {
        let newlines = line.iter().filter(|byte| **byte == b'\n').count();
        if newlines != 1 || line.last() != Some(&b'\n') {
            return Err(format!("not one whole line: {line:?}"));
        }
    }
    Ok(name)
}

// 10,000 requests from the fixed seed `SEED`, in four categories of exactly
// 4,000, 2,000, 2,000 and 2,000 requests, counted as they run, never panic,
// and every outcome and every line is listed; every error is written under a
// fresh context with the default limits and has at most $d = 1$ nested
// frame, and some general requests have an operand table. A failing or
// panicking
// request is reported with its category, its index and the seed, from
// which `request` generates it again. Each category reaches values and the
// errors of its boundaries: exponents and depths beyond their limits fail
// with `ResourceLimit` naming `max_exponent`, `max_integer_bits` or
// `max_depth`, and the same inputs under raised limits give values; at
// least 100 deep inputs nested beyond the default `max_depth` give values.
#[test]
fn ten_thousand_random_requests_never_panic() {
    assert_eq!(
        CATEGORIES,
        [
            (Category::General, 4_000),
            (Category::Exponents, 2_000),
            (Category::LargestLimits, 2_000),
            (Category::Deep, 2_000),
        ]
    );
    let mut seen: BTreeMap<Category, BTreeMap<String, u64>> = BTreeMap::new();
    let mut ran = 0;
    let mut deep_values_beyond_default = 0;
    let mut tables = 0;
    for (category, index) in schedule() {
        assert_eq!(index, ran, "the requests run in the order of their indices");
        let (request, limits) = request(category, index);
        let found = catch_unwind(AssertUnwindSafe(|| check(&request, limits)));
        let reproduce = || {
            format!(
                "request {index} of {category:?}, seed {SEED:#x} + {index}: {request:?} under {limits:?}"
            )
        };
        let name = match found {
            Ok(Ok(name)) => name,
            Ok(Err(message)) => panic!("{}: {message}", reproduce()),
            Err(_) => panic!("{}: panicked", reproduce()),
        };
        if !request.operands.is_empty() {
            tables += 1;
        }
        if category == Category::Deep
            && name == "value"
            && levels(&request.input) > Limits::new().max_depth
        {
            deep_values_beyond_default += 1;
        }
        *seen.entry(category).or_default().entry(name).or_default() += 1;
        ran += 1;
    }
    for (category, names) in &seen {
        println!("{category:?}: {names:?}");
    }
    assert_eq!(ran, 10_000);
    for (category, count) in CATEGORIES {
        assert_eq!(seen[&category].values().sum::<u64>(), count, "{category:?}");
    }
    println!("Deep: {deep_values_beyond_default} values beyond the default max_depth");
    assert!(deep_values_beyond_default >= 100);
    println!("General: {tables} requests with an operand table");
    assert!(tables >= 200, "{tables}");
    let has = |category: Category, name: &str| seen[&category].get(name).copied().unwrap_or(0) > 0;
    for category in [
        Category::General,
        Category::Exponents,
        Category::LargestLimits,
    ] {
        assert!(
            has(category, "value"),
            "{category:?}: {:?}",
            seen[&category]
        );
    }
    for name in [
        "Fault(Syntax)",
        "Fault(Unsupported)",
        "Fault(DivisionByZero)",
        "Fault(NonIntegerExponent)",
        "Fault(UnknownSymbol)",
        "Fault(NotPolynomial)",
        "ResourceLimit max_work",
    ] {
        assert!(
            has(Category::General, name),
            "{name}: {:?}",
            seen[&Category::General]
        );
    }
    for name in [
        "ResourceLimit max_exponent",
        "ResourceLimit max_integer_bits",
    ] {
        assert!(
            has(Category::Exponents, name),
            "{name}: {:?}",
            seen[&Category::Exponents]
        );
    }
    for name in ["value", "ResourceLimit max_depth"] {
        assert!(
            has(Category::Deep, name),
            "{name}: {:?}",
            seen[&Category::Deep]
        );
    }
}

// Each category generates its boundaries, checked on the requests alone,
// without running them: every request of the category of largest limits
// has a field at `u64::MAX`, the 1,000 of even index all nine and the
// others each field in turn; hundreds of exponent requests hold an exponent
// near $2^{32}$ and hundreds one near the `u64` bound, all under
// `max_integer_bits` of at most $2^{20}$; and every deep input is nested,
// most of them 100 levels or more, the deepest beyond 10,000 levels, with
// hundreds beyond the default `max_depth` under a `max_depth` that accepts
// them.
#[test]
fn the_categories_generate_their_boundaries() {
    let all = schedule();
    assert_eq!(all.len(), 10_000);
    let mut every_field = 0;
    let mut alone = [0_u64; 9];
    let mut near_32 = 0;
    let mut near_64 = 0;
    let mut hundred_levels = 0;
    let mut deepest = 0;
    let mut accepted_beyond_default = 0;
    let mut counts: BTreeMap<Category, u64> = BTreeMap::new();
    for (category, index) in all {
        *counts.entry(category).or_default() += 1;
        let (request, limits) = request(category, index);
        let at_max: Vec<usize> = LimitField::ALL
            .iter()
            .enumerate()
            .filter(|(_, field)| limits.get(**field) == u64::MAX)
            .map(|(position, _)| position)
            .collect();
        match category {
            Category::General => {}
            Category::Exponents => {
                assert!(limits.max_integer_bits <= WIDEST, "{index}: {limits:?}");
                near_32 += u64::from(near_two_to_the_32(&request.input));
                near_64 += u64::from(near_the_u64_bound(&request.input));
            }
            Category::LargestLimits => {
                match at_max.as_slice() {
                    [field] => alone[*field] += 1,
                    fields if fields.len() == 9 => every_field += 1,
                    fields => panic!("{index}: fields {fields:?} at u64::MAX in {limits:?}"),
                }
                assert_eq!(index % 2 == 0, at_max.len() == 9, "{index}");
            }
            Category::Deep => {
                let found = levels(&request.input);
                assert!(found >= 1, "{index}: {}", request.input);
                hundred_levels += u64::from(found >= 100);
                deepest = deepest.max(found);
                if found > Limits::new().max_depth && limits.max_depth >= 2 * found + 2 {
                    accepted_beyond_default += 1;
                }
            }
        }
    }
    println!(
        "every field {every_field}, one field {alone:?}, near 2^32 {near_32}, near the u64 bound {near_64}, 100 levels {hundred_levels}, deepest {deepest}, beyond the default and accepted {accepted_beyond_default}"
    );
    assert_eq!(counts.into_iter().collect::<Vec<_>>(), CATEGORIES.to_vec());
    assert_eq!(every_field, 1_000);
    assert_eq!(alone.iter().sum::<u64>(), 1_000);
    assert!(alone.iter().all(|count| *count >= 100), "{alone:?}");
    assert!(near_32 >= 600, "{near_32}");
    assert!(near_64 >= 800, "{near_64}");
    assert!(hundred_levels >= 1_500, "{hundred_levels}");
    assert!(deepest > 10_000, "{deepest}");
    assert!(accepted_beyond_default >= 600, "{accepted_beyond_default}");
}

// The requests are a function of their index and the seed alone: generated
// twice, request 7,321 is the same request under the same limits.
#[test]
fn a_request_is_generated_again_from_its_index() {
    assert_eq!(
        request(Category::LargestLimits, 7_321),
        request(Category::LargestLimits, 7_321)
    );
    assert_ne!(request(Category::General, 1), request(Category::General, 2));
}
