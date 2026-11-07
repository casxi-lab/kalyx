//! Property tests of the parser from fixed seeds, as testing obligation 8 of
//! `docs/components/syntax/contract.md` asks, and a differential check of
//! numeric input against an evaluator written here. The rules are those of
//! `docs/semantics.md` and of that contract; the tests use only the public
//! interface of the library and were written by an author other than the
//! author of the parser.
//!
//! - `restricted_inputs_give_a_term_a_syntax_error_or_a_resource_limit`
//!   parses 10,000 inputs over digits, `.`, `+`, `-`, `*`, parentheses,
//!   whitespace and characters that start no token, ASCII and not, without
//!   `/`, `^` and letters: soups of these characters of 0 to 400 bytes,
//!   expressions of the grammar with and without random edits, deep nesting
//!   of parentheses and unary minus signs of up to 3,000 levels, and chains
//!   of up to 6,000 operands. Every result is a term, a `Syntax` error or a
//!   `ResourceLimit`, and none is a panic.
//! - `full_inputs_give_only_the_listed_errors_with_spans_in_the_input`
//!   parses 10,000 inputs over the full alphabet of the grammar and the same
//!   extra characters: letters, the reserved names, call shapes and command
//!   words, `/` and `^` too, with every kind of whitespace. None panics, and
//!   every error is of a kind that the contract lists, with a span on
//!   character boundaries inside the input or empty at its end.
//! - `display_text_reads_back_as_the_same_term` builds 1,000 random terms
//!   through the constructors of the term core, with negative and fractional
//!   numbers and numbers beyond 64 bits, sums, products, integer powers with
//!   negative exponents, the witness shapes and scaled sums, displays each
//!   and parses the text back: the term read `Term::equals` the term, and its
//!   display is the same text.
//! - `numeric_input_has_the_value_of_an_independent_evaluator` writes 3,000
//!   random expressions of the grammar over numbers, with `/`, `^`, decimal
//!   literals, unary minus signs, parentheses and every kind of whitespace,
//!   and checks each against the evaluator of the model below: the term is
//!   the number that the evaluator computes, or both fail with the same fault
//!   and the same span.
//!
//! Each input of the first two properties is parsed three times, each time
//! in a fresh context: under limits far above it, under the default limits,
//! and under limits of which one, chosen at random, is small. Every run
//! checks what the contract states for every result:
//!
//! - an error carries a span on character boundaries of the input, which
//!   begins and ends at the boundaries of tokens, except where the table of
//!   spans allows one character of a literal, an empty span or the whole
//!   input; the span of `Unsupported` is a reserved name or a name and its
//!   `(`, that of `NonIntegerExponent` an exponent after `^`;
//! - a `ResourceLimit` names a field of `Limits` that the parser or the term
//!   core checks, with the value in force and the scope `Value` exactly for
//!   `max_nodes` and `max_storage_bytes`;
//! - an input longer than `max_input_bytes` fails with that limit and the
//!   span of the whole input, and no other input does;
//! - a run under smaller limits gives the result of the run under the larger
//!   limits and charges the same work, or it fails with a `ResourceLimit`.
//!
//! The runs under limits far above the input are compared with the model,
//! which decides whether the input is in the grammar, which fault comes first
//! when it is not, and, for numeric input, its value, its fault and the span
//! of the fault. Where two rules apply to the same text, the order of
//! failures of the contract decides: a reserved name or a call in the place
//! of an operator fails with `Syntax`, and a reserved name before a malformed
//! literal or a stray character with `Unsupported`. For numeric input in the
//! grammar, a small `max_depth` and a small `max_nodes` fail exactly when the
//! syntax depth and the syntax nodes of the model exceed them, a small
//! `max_depth` at the token that opens the first level beyond it. Every term
//! that a run gives reads back from its display text as the same term.
//!
//! **The model.** The input is read by a model of the grammar written here
//! from `docs/semantics.md`: its own lexer, an operator-precedence reader
//! with explicit stacks that keeps the span of every node and of the
//! parentheses around it, the levels of the depth measure of the contract,
//! and an evaluator over exact rationals of `i128` whose every operation is
//! checked for overflow. An input whose value overflows the model is not
//! compared with a value. `the_model_reads_the_examples_of_the_documents`
//! checks the model itself against the examples of the two documents and the
//! depth cases of `vectors/r02.tsv`.
//!
//! Each case draws from its own seed, the next output of a SplitMix64
//! started at the fixed seed of its property. A failing case prints its
//! index, its seed, its input and the small limit of its third run, and
//! `check(&mut Case::new(property, cases, index, seed), &mut Tally::default())`,
//! with the case function of the property as `check`, runs it alone.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "a failed check panics, and the guard of its case prints the seed and the input"
)]

use kalyx::context::CancelFlag;
use kalyx::number::{Integer, Rational};
use kalyx::syntax::parse;
use kalyx::term::{Term, TermKind};
use kalyx::{
    Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope, Limits,
    Span,
};

const VECTORS: &str = include_str!("../vectors/r02.tsv");

/// The inputs of each of the two properties over random text.
const INPUTS: u64 = 10_000;

/// The round trips of display text.
const ROUND_TRIPS: u64 = 1_000;

/// The numeric expressions checked against the evaluator.
const EXPRESSIONS: u64 = 3_000;

/// The draws of one case whose input can be rejected: a term whose
/// construction fails, or an expression whose value overflows the model, is
/// drawn again.
const ATTEMPTS: usize = 100;

const RESTRICTED_SEED: u64 = 0x5EED_0000_0000_0101;
const FULL_SEED: u64 = 0x5EED_0000_0000_0102;
const ROUND_TRIP_SEED: u64 = 0x5EED_0000_0000_0103;
const NUMERIC_SEED: u64 = 0x5EED_0000_0000_0104;

/// The names reserved for constants, which are not symbols.
const RESERVED: [&str; 3] = ["pi", "i", "undefined"];

/// The limits that the third run of a restricted input makes small.
const RESTRICTED_SMALL: [LimitField; 6] = [
    LimitField::InputBytes,
    LimitField::Depth,
    LimitField::Nodes,
    LimitField::Work,
    LimitField::IntegerBits,
    LimitField::StorageBytes,
];

/// The limits that the third run of a full input makes small.
const FULL_SMALL: [LimitField; 7] = [
    LimitField::InputBytes,
    LimitField::Depth,
    LimitField::Nodes,
    LimitField::Work,
    LimitField::IntegerBits,
    LimitField::StorageBytes,
    LimitField::Exponent,
];

// ---------------------------------------------------------------------------
// The random source and the cases

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

    /// A value in `0..bound`.
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    /// An index into a list of `len` items; the lists are short, so the
    /// conversions lose nothing.
    fn index(&mut self, len: usize) -> usize {
        self.below(len as u64) as usize
    }

    /// True with the probability `numerator / denominator`.
    fn chance(&mut self, numerator: u64, denominator: u64) -> bool {
        self.below(denominator) < numerator
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.index(items.len())]
    }
}

/// One case of a property: its seed, its random source and the input it
/// drew. A case that panics prints them when it is dropped.
struct Case {
    property: &'static str,
    cases: u64,
    index: u64,
    seed: u64,
    random: SplitMix64,
    input: String,
    notes: Vec<String>,
}

impl Case {
    fn new(property: &'static str, cases: u64, index: u64, seed: u64) -> Self {
        Self {
            property,
            cases,
            index,
            seed,
            random: SplitMix64(seed),
            input: String::new(),
            notes: Vec::new(),
        }
    }

    /// Records the input under test for the report of a failure.
    fn input(&mut self, text: &str) {
        text.clone_into(&mut self.input);
    }

    /// Records a detail of the case for the report of a failure.
    fn note(&mut self, note: String) {
        self.notes.push(note);
    }
}

impl Drop for Case {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "{}: case {} of {} failed; its seed is {:#018x}",
                self.property, self.index, self.cases, self.seed
            );
            eprintln!("  input ({} bytes): {:?}", self.input.len(), self.input);
            for note in &self.notes {
                eprintln!("  {note}");
            }
        }
    }
}

/// Counts of what the cases of a property exercised, printed after the run.
#[derive(Default)]
struct Tally(Vec<(String, u64)>);

impl Tally {
    fn add(&mut self, name: impl Into<String>, amount: u64) {
        let name = name.into();
        match self.0.iter_mut().find(|entry| entry.0 == name) {
            Some(entry) => entry.1 += amount,
            None => self.0.push((name, amount)),
        }
    }

    fn get(&self, name: &str) -> u64 {
        self.0
            .iter()
            .find(|entry| entry.0 == name)
            .map_or(0, |entry| entry.1)
    }

    /// Asserts that the cases exercised each of `names`.
    fn require(&self, property: &str, names: &[&str]) {
        for name in names {
            assert!(self.get(name) > 0, "{property}: no case exercised {name}");
        }
    }

    fn summary(&self) -> String {
        let parts: Vec<String> = self
            .0
            .iter()
            .map(|(name, count)| format!("{name}: {count}"))
            .collect();
        parts.join("; ")
    }
}

/// Runs `cases` cases of a property, each from its own seed: the next output
/// of a SplitMix64 started at `seed`.
fn run(property: &'static str, seed: u64, cases: u64, check: fn(&mut Case, &mut Tally)) -> Tally {
    let mut seeds = SplitMix64(seed);
    let mut tally = Tally::default();
    for index in 0..cases {
        let mut case = Case::new(property, cases, index, seeds.next());
        check(&mut case, &mut tally);
        tally.add("cases", 1);
    }
    assert_eq!(tally.get("cases"), cases);
    println!("{property}: {}", tally.summary());
    tally
}

// ---------------------------------------------------------------------------
// Limits and the checks of every result

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

/// Limits far above every input of the properties. `max_exponent` keeps its
/// default, 4096, and `max_integer_bits` is $2^{16}$, so that no case
/// computes a number of more bits; a numeric input whose value needs more
/// bits fails with a `ResourceLimit` even here.
fn generous() -> Limits {
    Limits::new()
        .with_max_work(u64::MAX)
        .with_max_input_bytes(1 << 20)
        .with_max_output_bytes(u64::MAX)
        .with_max_depth(1 << 16)
        .with_max_nodes(1 << 24)
        .with_max_storage_bytes(1 << 40)
        .with_max_integer_bits(1 << 16)
}

/// The limits under which display text is read back: those of [`generous`]
/// with room for the literals of display text, whose bound is 4 bits per
/// decimal digit, so about 1.2 times the bits of their numbers.
fn reading() -> Limits {
    generous().with_max_integer_bits(1 << 20)
}

/// [`generous`] with one limit, `field`, made small for an input of `length`
/// bytes: around the length for the input bytes, so that both sides of the
/// limit occur, and small for the others.
fn small_limits(
    random: &mut SplitMix64,
    length: usize,
    fields: &[LimitField],
) -> (LimitField, Limits) {
    let field = random.pick(fields);
    let length = length as u64;
    let limits = generous();
    let limits = match field {
        LimitField::InputBytes => {
            let bytes = if random.chance(1, 2) {
                random.below(length + 2)
            } else {
                length.saturating_sub(1) + random.below(3)
            };
            limits.with_max_input_bytes(bytes)
        }
        LimitField::Depth => {
            let bound = if random.chance(3, 4) { 40 } else { 300 };
            limits.with_max_depth(random.below(bound))
        }
        LimitField::Nodes => limits.with_max_nodes(random.below(length + 2)),
        LimitField::Work => limits.with_max_work(random.below(8 * length + 64)),
        LimitField::IntegerBits => limits.with_max_integer_bits(random.below(80)),
        LimitField::StorageBytes => limits.with_max_storage_bytes(random.below(300)),
        _ => limits.with_max_exponent(random.below(17)),
    };
    (field, limits)
}

/// Whether `error` is a `ResourceLimit` that names `field`.
fn is_limit(error: &Error, field: LimitField) -> bool {
    error.kind() == ErrorKind::ResourceLimit
        && error
            .exceeded()
            .is_some_and(|exceeded| *exceeded.id() == LimitId::Field(field))
}

/// Whether `result` is a `ResourceLimit` that names `field`.
fn fails_with_limit(result: &Result<Term, Error>, field: LimitField) -> bool {
    result.as_ref().is_err_and(|error| is_limit(error, field))
}

/// Whether `result` is the fault `fault`.
fn fails_with(result: &Result<Term, Error>, fault: FaultKind) -> bool {
    result
        .as_ref()
        .is_err_and(|error| error.kind() == ErrorKind::Fault(fault))
}

/// A short name of a result, for the tallies and the reports.
fn outcome(result: &Result<Term, Error>) -> String {
    match result {
        Ok(_) => String::from("a term"),
        Err(error) => match (error.kind(), error.exceeded()) {
            (ErrorKind::ResourceLimit, Some(exceeded)) => {
                format!("ResourceLimit {}", exceeded.id().name())
            }
            (ErrorKind::Fault(fault), _) => format!("{fault:?}"),
            (kind, _) => format!("{kind:?}"),
        },
    }
}

/// A report of a result for a failed assertion: the outcome, the span and
/// the message.
fn report(result: &Result<Term, Error>) -> String {
    match result {
        Ok(term) => format!("a term of the kind {:?}", term.kind()),
        Err(error) => format!("{} ({error})", outcome(result)),
    }
}

/// One run of `parse`: its result and the work that it charged.
struct Run {
    result: Result<Term, Error>,
    work: u64,
}

/// Parses `source` under `limits` in a fresh context, and asserts the rules
/// of every result: the rules of [`check_error`], and the limit of the input
/// bytes, which the parser checks before it reads any byte, so an input
/// longer than `max_input_bytes` fails with it and the span of the whole
/// input, and no other input does.
fn parse_checked(source: &str, limits: &Limits) -> Run {
    let c = &mut context(*limits);
    let result = parse(source, c);
    let length = source.len() as u64;
    match &result {
        Err(error) => {
            check_error(source, limits, error);
            if length > limits.max_input_bytes {
                assert!(
                    is_limit(error, LimitField::InputBytes),
                    "an input longer than max_input_bytes fails with that limit first, not with {}",
                    report(&result)
                );
                assert_eq!(error.span(), Span::new(0, source.len()), "{error}");
                assert_eq!(
                    error.exceeded().unwrap().amount(),
                    LimitAmount::Required(length),
                    "{error}"
                );
            } else {
                assert!(
                    !is_limit(error, LimitField::InputBytes),
                    "an input within max_input_bytes fails with that limit: {error}"
                );
            }
        }
        Ok(_) => assert!(
            length <= limits.max_input_bytes,
            "an input longer than max_input_bytes gives a term"
        ),
    }
    Run {
        result,
        work: c.work_used(),
    }
}

/// Asserts the rules that every error of `parse` follows: it carries a span,
/// a half-open range of byte offsets on character boundaries of the source;
/// its kind is one that the contract lists; and a `ResourceLimit` names a
/// field of `Limits` that the parser or the term core checks, with the value
/// in force, and the scope `Value` exactly for the retained totals. The
/// contexts of the tests are never cancelled and have no deadline, so
/// `Cancelled` and `DeadlineExceeded` cannot occur; `Internal` is a broken
/// invariant, and `UnknownSymbol` and `NotPolynomial` belong to later stages.
fn check_error(source: &str, limits: &Limits, error: &Error) {
    let span = error
        .span()
        .unwrap_or_else(|| panic!("an error without a span: {error}"));
    assert!(
        span.end() <= source.len()
            && source.is_char_boundary(span.start())
            && source.is_char_boundary(span.end()),
        "the span {}..{} is not on character boundaries inside the input of {} bytes: {error}",
        span.start(),
        span.end(),
        source.len()
    );
    match error.kind() {
        ErrorKind::ResourceLimit => {
            let exceeded = error
                .exceeded()
                .unwrap_or_else(|| panic!("a ResourceLimit names no limit: {error}"));
            let LimitId::Field(field) = exceeded.id() else {
                panic!("a ResourceLimit of parse names a parameter: {error}");
            };
            assert!(
                matches!(
                    field,
                    LimitField::InputBytes
                        | LimitField::Depth
                        | LimitField::Nodes
                        | LimitField::StorageBytes
                        | LimitField::IntegerBits
                        | LimitField::Exponent
                        | LimitField::Work
                ),
                "parse exceeds a limit that it does not check: {error}"
            );
            let retained = matches!(field, LimitField::Nodes | LimitField::StorageBytes);
            assert_eq!(
                exceeded.scope(),
                retained.then_some(LimitScope::Value),
                "{error}"
            );
            let allowed = if *field == LimitField::Exponent {
                limits.max_exponent.min(i64::MAX.unsigned_abs())
            } else {
                limits.get(*field)
            };
            assert_eq!(exceeded.allowed(), allowed, "{error}");
        }
        ErrorKind::Fault(
            FaultKind::Syntax
            | FaultKind::Unsupported
            | FaultKind::NonIntegerExponent
            | FaultKind::DivisionByZero,
        ) => {}
        kind => panic!(
            "parse returns an error of a kind that the contract does not list: {kind:?} ({error})"
        ),
    }
    check_alignment(source, error);
}

/// Asserts that the span of an error is one that the table of spans of the
/// contract allows: a token or a node, which begin and end at the
/// boundaries of tokens; one character, of a malformed literal, for
/// `Syntax`; an empty span at the end of the input, or after the point of a
/// literal that misses a digit for `Syntax`; and the whole input for the
/// input bytes and the level 1.
fn check_alignment(source: &str, error: &Error) {
    let span = error.span().unwrap();
    let (start, end) = (span.start(), span.end());
    let whole = (start, end) == (0, source.len());
    if whole
        && (is_limit(error, LimitField::InputBytes)
            || (is_limit(error, LimitField::Depth)
                && error.exceeded().unwrap().amount() == LimitAmount::Required(1)))
    {
        return;
    }
    let syntax = error.kind() == ErrorKind::Fault(FaultKind::Syntax);
    if start == end {
        let after_point = source.as_bytes()[..start].last() == Some(&b'.');
        assert!(
            start == source.len() || (syntax && after_point),
            "an empty span at {start} inside the input: {error}"
        );
        return;
    }
    if syntax && source[start..end].chars().count() == 1 {
        return;
    }
    let tokens = lex(source);
    assert!(
        tokens.iter().any(|token| token.start == start)
            && tokens.iter().any(|token| token.end == end),
        "the span {start}..{end}, {:?}, does not begin and end at the boundaries of tokens: {error}",
        &source[start..end]
    );
}

/// Asserts what the text under the span of a fault shows, where the
/// contract says what it is: a reserved name, or a name, whitespace and `(`
/// of function-call syntax, each starting at a token boundary, for
/// `Unsupported`; an exponent, right after `^` and whitespace, for
/// `NonIntegerExponent`; and only input with `/` or `^`, the operators that
/// introduce a negative power, has a `DivisionByZero`.
fn check_fault_text(source: &str, result: &Result<Term, Error>) {
    let Err(error) = result else { return };
    let Some(span) = error.span() else { return };
    let text = &source[span.start()..span.end()];
    let before = source.as_bytes()[..span.start()].last().copied();
    match error.kind() {
        ErrorKind::Fault(FaultKind::Unsupported) => {
            let reserved = RESERVED.contains(&text);
            assert!(
                reserved || is_call_text(text),
                "the span of Unsupported is neither a reserved name nor a call: {text:?}"
            );
            assert!(
                !before.is_some_and(is_literal_byte),
                "the name of Unsupported does not start a token: {text:?}"
            );
            if reserved {
                let after = source.as_bytes().get(span.end()).copied();
                assert!(
                    !after.is_some_and(is_name_byte),
                    "the reserved name of Unsupported does not end a token: {text:?}"
                );
            }
        }
        ErrorKind::Fault(FaultKind::NonIntegerExponent) => {
            let before = source[..span.start()].trim_end_matches(is_space_char);
            assert!(
                before.ends_with('^') && !text.is_empty() && !text.starts_with(is_space_char),
                "the span of NonIntegerExponent is not an exponent: {text:?}"
            );
        }
        ErrorKind::Fault(FaultKind::DivisionByZero) => assert!(
            source.contains('/') || source.contains('^'),
            "DivisionByZero in input without `/` and `^`"
        ),
        _ => {}
    }
}

/// Whether `text` is a name, optional whitespace and `(`.
fn is_call_text(text: &str) -> bool {
    let Some(name) = text.strip_suffix('(') else {
        return false;
    };
    let name = name.trim_end_matches(is_space_char).as_bytes();
    !name.is_empty() && is_name_start(name[0]) && name.iter().all(|byte| is_name_byte(*byte))
}

/// Asserts that `run`, under limits no larger than those of `reference`, has
/// the same result or a `ResourceLimit`, and that a run with the same result
/// charged the same work: the limits add failures and change nothing else,
/// since the steps of the parser and their charges depend only on the input.
fn assert_consistent(run: &Run, reference: &Run) {
    let (result, larger) = (&run.result, &reference.result);
    match (result, larger) {
        (Err(error), _) if error.kind() == ErrorKind::ResourceLimit => return,
        (Ok(term), Ok(expected)) => assert!(
            term.equals(expected, &mut context(reading())).unwrap(),
            "smaller limits give another term"
        ),
        (Err(error), Err(expected)) => assert!(
            error.kind() == expected.kind() && error.span() == expected.span(),
            "smaller limits give {} where larger limits give {}",
            report(result),
            report(larger)
        ),
        _ => panic!(
            "smaller limits give {} where larger limits give {}",
            report(result),
            report(larger)
        ),
    }
    assert_eq!(
        run.work,
        reference.work,
        "the same result under other limits charges other work: {}",
        report(result)
    );
}

/// Displays `term`, parses the text back and asserts that the term read is
/// `term`, with the same display; returns the text.
fn assert_reads_back(term: &Term) -> String {
    let c = &mut context(reading());
    let text = term.display(c).unwrap();
    let read = parse(&text, c).unwrap_or_else(|error| {
        panic!(
            "the display text {text:?} does not read back: {} ({error})",
            outcome(&Err(error.clone()))
        )
    });
    assert!(
        read.equals(term, c).unwrap(),
        "the display text {text:?} reads back as another term, displayed {:?}",
        read.display(c).unwrap()
    );
    assert_eq!(read.display(c).unwrap(), text);
    text
}

/// Asserts the result that the model expects of a numeric input in the
/// grammar: the number, or the fault or the exponent limit with its span.
/// When the integers of the model overflowed first, the result is a number
/// or an error of evaluation, never `Syntax` or `Unsupported`.
fn assert_expected(expected: &Expected, result: &Result<Term, Error>) {
    match (expected, result) {
        (Expected::Number(value), Ok(term)) => {
            let number = term.as_number().unwrap_or_else(|| {
                panic!("numeric input gives a term of the kind {:?}", term.kind())
            });
            assert_eq!(
                (
                    number.numerator().to_string(),
                    number.denominator().to_string()
                ),
                (value.numerator.to_string(), value.denominator.to_string()),
                "the parser and the model give different values"
            );
        }
        (Expected::Fault(fault, (start, end)), Err(error)) => assert!(
            error.kind() == ErrorKind::Fault(*fault) && error.span() == Span::new(*start, *end),
            "the model expects {fault:?} at {start}..{end}, the parser gives {}",
            report(result)
        ),
        (Expected::ExponentLimit((start, end)), Err(error)) => assert!(
            is_limit(error, LimitField::Exponent) && error.span() == Span::new(*start, *end),
            "the model expects the limit max_exponent at {start}..{end}, the parser gives {}",
            report(result)
        ),
        (Expected::Unknown, Ok(term)) => assert_eq!(term.kind(), TermKind::Number),
        (Expected::Unknown, Err(_)) => assert!(
            !fails_with(result, FaultKind::Syntax) && !fails_with(result, FaultKind::Unsupported),
            "input in the grammar gives {}",
            report(result)
        ),
        _ => panic!(
            "the model expects {expected:?}, the parser gives {}",
            report(result)
        ),
    }
}

/// Asserts the limits whose failure the model predicts exactly for a numeric
/// input in the grammar, when `field` is the one small limit: `max_depth`
/// fails exactly when the syntax depth exceeds it, at the token that opens
/// the first level beyond it and with that level as the amount, and
/// `max_nodes` exactly when the count of syntax nodes exceeds it. The term of
/// a numeric input is a number, of depth 1 and one node, so the term core
/// adds no such failure.
fn assert_exact_limits(
    source: &str,
    tree: &ModelTree,
    field: LimitField,
    limits: &Limits,
    result: &Result<Term, Error>,
) {
    match field {
        LimitField::Depth => match tree.depth_failure(source.len(), limits.max_depth) {
            Some(((start, end), level)) => {
                let error = result.as_ref().err().unwrap_or_else(|| {
                    panic!(
                        "an input of the depth {} gives a term under max_depth {}",
                        tree.levels().0,
                        limits.max_depth
                    )
                });
                assert!(
                    is_limit(error, LimitField::Depth)
                        && error.span() == Span::new(start, end)
                        && error.exceeded().unwrap().amount() == LimitAmount::Required(level),
                    "the model expects the limit max_depth at {start}..{end} for the level {level}, the parser gives {}",
                    report(result)
                );
            }
            None => assert!(
                !fails_with_limit(result, LimitField::Depth),
                "an input of the depth {} fails under max_depth {}",
                tree.levels().0,
                limits.max_depth
            ),
        },
        LimitField::Nodes => {
            let nodes = tree.nodes.len() as u64;
            assert_eq!(
                fails_with_limit(result, LimitField::Nodes),
                nodes > limits.max_nodes,
                "an input of {nodes} syntax nodes under max_nodes {} gives {}",
                limits.max_nodes,
                report(result)
            );
        }
        _ => {}
    }
}

/// Asserts that every input fails under `max_depth` 0: the level 1 of the
/// whole input is checked before its first token, with the span of the
/// whole input.
fn assert_level_one(source: &str, limits: &Limits, result: &Result<Term, Error>) {
    if limits.max_depth != 0 || source.len() as u64 > limits.max_input_bytes {
        return;
    }
    let error = result
        .as_ref()
        .err()
        .unwrap_or_else(|| panic!("an input gives a term under max_depth 0"));
    assert!(
        is_limit(error, LimitField::Depth)
            && error.span() == Span::new(0, source.len())
            && error.exceeded().unwrap().amount() == LimitAmount::Required(1),
        "under max_depth 0 the parser gives {}",
        report(result)
    );
}

// ---------------------------------------------------------------------------
// The model of the grammar

/// The lexemes of the model's own lexer, after the lexical rules of
/// `docs/semantics.md`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lexeme {
    /// A number literal of the form `1` or `1.5`.
    Number,
    /// Any other run of letters, digits, `_` and points that starts with a
    /// digit or a point.
    Malformed,
    /// An identifier.
    Name,
    /// `+`, `-`, `*`, `/` or `^`.
    Operator(u8),
    Open,
    Close,
    /// A character that starts no token.
    Stray,
}

#[derive(Clone, Copy, Debug)]
struct Token {
    lexeme: Lexeme,
    start: usize,
    end: usize,
}

/// The whitespace of the grammar: space, tab, line feed, form feed and
/// carriage return.
fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\x0c' | b'\r')
}

fn is_space_char(character: char) -> bool {
    matches!(character, ' ' | '\t' | '\n' | '\x0c' | '\r')
}

fn is_name_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn is_name_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// The bytes over which a number literal runs.
fn is_literal_byte(byte: u8) -> bool {
    is_name_byte(byte) || byte == b'.'
}

/// Whether a run of a number literal has the form `digit+ ('.' digit+)?`.
fn is_decimal(run: &[u8]) -> bool {
    let digits = leading_digits(run);
    if digits == 0 {
        return false;
    }
    match run.get(digits) {
        None => true,
        Some(b'.') => {
            let fraction = &run[digits + 1..];
            !fraction.is_empty() && leading_digits(fraction) == fraction.len()
        }
        Some(_) => false,
    }
}

fn leading_digits(bytes: &[u8]) -> usize {
    bytes
        .iter()
        .take_while(|byte| byte.is_ascii_digit())
        .count()
}

/// The tokens of `source`. A number literal starts with a digit or a point
/// and runs over every letter, digit, `_` and point that follows; an
/// identifier starts with a letter or `_`; whitespace separates tokens; and
/// any other character is a stray token of its whole length.
fn lex(source: &str) -> Vec<Token> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let byte = bytes[at];
        let start = at;
        at += 1;
        if is_space(byte) {
            continue;
        }
        let lexeme = if byte.is_ascii_digit() || byte == b'.' {
            while at < bytes.len() && is_literal_byte(bytes[at]) {
                at += 1;
            }
            if is_decimal(&bytes[start..at]) {
                Lexeme::Number
            } else {
                Lexeme::Malformed
            }
        } else if is_name_start(byte) {
            while at < bytes.len() && is_name_byte(bytes[at]) {
                at += 1;
            }
            Lexeme::Name
        } else {
            match byte {
                b'+' | b'-' | b'*' | b'/' | b'^' => Lexeme::Operator(byte),
                b'(' => Lexeme::Open,
                b')' => Lexeme::Close,
                _ => {
                    while !source.is_char_boundary(at) {
                        at += 1;
                    }
                    Lexeme::Stray
                }
            }
        };
        tokens.push(Token {
            lexeme,
            start,
            end: at,
        });
    }
    tokens
}

/// The shape of a node of the model's syntax tree.
#[derive(Clone, Copy, Debug)]
enum Shape {
    Literal,
    Name,
    /// A unary minus and the index of its operand.
    Negate(usize),
    /// A binary operator, the start of its token and the indices of its
    /// operands. A chain is a left-nested sequence of these.
    Binary {
        operator: u8,
        at: usize,
        left: usize,
        right: usize,
    },
}

/// A node of the model's syntax tree.
#[derive(Clone, Debug)]
struct ModelNode {
    shape: Shape,
    /// The span of the node: its token, or from its sign or the start of
    /// its first operand to the end of its last, without the parentheses
    /// around it.
    span: (usize, usize),
    /// The span with the parentheses around the node.
    outer: (usize, usize),
    /// The starts of the `(` around the node, the innermost first.
    opens: Vec<usize>,
}

/// The syntax tree of an input in the grammar: its nodes in postorder, the
/// operands of each node before it, from left to right, and the root last.
struct ModelTree {
    nodes: Vec<ModelNode>,
}

/// What the model reads in an input.
enum Reading {
    /// The input is in the grammar, with no reserved name and no
    /// function-call syntax.
    Tree(ModelTree),
    /// The first fault in reading order is `Syntax`.
    Syntax,
    /// The first fault in reading order is a reserved name or function-call
    /// syntax: `Unsupported`.
    Unsupported,
    /// Two rules apply to the same text, and the order of failures of the
    /// contract decides the first fault, for the reason given: an identifier
    /// where an operator is expected is a second operand, `Syntax`, also when
    /// it is a reserved name or a call; and a reserved name fails before the
    /// token after it is read, `Unsupported`, also when that token is a
    /// malformed literal or a stray character.
    Ordered(FaultKind, &'static str),
}

/// An operation waiting on the stack of the reader.
#[derive(Clone, Copy)]
enum Pending {
    /// A `(` and its start.
    Open(usize),
    /// A unary minus and its start.
    Negate(usize),
    /// A binary operator and its start.
    Binary(u8, usize),
}

/// How tightly a binary operator binds; a unary minus binds with 3, between
/// `*` and `/` and `^`.
fn binding(operator: u8) -> u8 {
    match operator {
        b'+' | b'-' => 1,
        b'*' | b'/' => 2,
        _ => 4,
    }
}

/// Reads `source` in the grammar with the precedence and associativity of
/// `docs/semantics.md`: `^` binds tightest and is right-associative, a unary
/// minus binds less tightly than `^` and more tightly than `*` and `/`, and
/// `*`, `/`, `+` and `-` are left-associative. A unary minus may start every
/// operand, there is no unary plus, and an identifier followed by `(` is
/// function-call syntax.
fn read_model(source: &str) -> Reading {
    let tokens = lex(source);
    let mut nodes: Vec<ModelNode> = Vec::new();
    let mut operands: Vec<usize> = Vec::new();
    let mut pending: Vec<Pending> = Vec::new();
    let mut expect_operand = true;
    for (index, token) in tokens.iter().enumerate() {
        let next = tokens.get(index + 1).map(|token| token.lexeme);
        let text = &source[token.start..token.end];
        if expect_operand {
            match token.lexeme {
                Lexeme::Number => {
                    leaf(&mut nodes, &mut operands, Shape::Literal, token);
                    expect_operand = false;
                }
                Lexeme::Name => {
                    if next == Some(Lexeme::Open) {
                        return Reading::Unsupported;
                    }
                    if RESERVED.contains(&text) {
                        return match next {
                            None
                            | Some(
                                Lexeme::Operator(_) | Lexeme::Close | Lexeme::Number | Lexeme::Name,
                            ) => Reading::Unsupported,
                            Some(_) => Reading::Ordered(
                                FaultKind::Unsupported,
                                "a reserved name before a malformed literal or a stray character",
                            ),
                        };
                    }
                    leaf(&mut nodes, &mut operands, Shape::Name, token);
                    expect_operand = false;
                }
                Lexeme::Operator(b'-') => pending.push(Pending::Negate(token.start)),
                Lexeme::Open => pending.push(Pending::Open(token.start)),
                _ => return Reading::Syntax,
            }
        } else {
            match token.lexeme {
                Lexeme::Operator(operator) => {
                    while let Some(&top) = pending.last() {
                        let applies = match top {
                            Pending::Open(_) => false,
                            Pending::Negate(_) => binding(operator) <= 3,
                            Pending::Binary(previous, _) => {
                                binding(previous) > binding(operator)
                                    || (binding(previous) == binding(operator) && operator != b'^')
                            }
                        };
                        if !applies {
                            break;
                        }
                        pending.pop();
                        apply(top, &mut nodes, &mut operands);
                    }
                    pending.push(Pending::Binary(operator, token.start));
                    expect_operand = true;
                }
                Lexeme::Close => loop {
                    match pending.pop() {
                        None => return Reading::Syntax,
                        Some(Pending::Open(start)) => {
                            let node = &mut nodes[*operands.last().unwrap()];
                            node.outer = (start, token.end);
                            node.opens.push(start);
                            break;
                        }
                        Some(operation) => apply(operation, &mut nodes, &mut operands),
                    }
                },
                Lexeme::Name if RESERVED.contains(&text) || next == Some(Lexeme::Open) => {
                    return Reading::Ordered(
                        FaultKind::Syntax,
                        "a reserved name or a call where an operator is expected",
                    );
                }
                _ => return Reading::Syntax,
            }
        }
    }
    if expect_operand {
        return Reading::Syntax;
    }
    while let Some(operation) = pending.pop() {
        if let Pending::Open(_) = operation {
            return Reading::Syntax;
        }
        apply(operation, &mut nodes, &mut operands);
    }
    assert_eq!(operands, [nodes.len() - 1], "the root is the last node");
    Reading::Tree(ModelTree { nodes })
}

fn leaf(nodes: &mut Vec<ModelNode>, operands: &mut Vec<usize>, shape: Shape, token: &Token) {
    let span = (token.start, token.end);
    operands.push(nodes.len());
    nodes.push(ModelNode {
        shape,
        span,
        outer: span,
        opens: Vec::new(),
    });
}

/// Builds the node of a unary minus or a binary operator from its operands
/// on the stack.
fn apply(operation: Pending, nodes: &mut Vec<ModelNode>, operands: &mut Vec<usize>) {
    let (shape, span) = match operation {
        Pending::Negate(at) => {
            let operand = operands.pop().unwrap();
            (Shape::Negate(operand), (at, nodes[operand].outer.1))
        }
        Pending::Binary(operator, at) => {
            let right = operands.pop().unwrap();
            let left = operands.pop().unwrap();
            let shape = Shape::Binary {
                operator,
                at,
                left,
                right,
            };
            (shape, (nodes[left].outer.0, nodes[right].outer.1))
        }
        Pending::Open(_) => panic!("a parenthesis is not an operation"),
    };
    operands.push(nodes.len());
    nodes.push(ModelNode {
        shape,
        span,
        outer: span,
        opens: Vec::new(),
    });
}

impl ModelTree {
    fn has_names(&self) -> bool {
        self.nodes
            .iter()
            .any(|node| matches!(node.shape, Shape::Name))
    }

    /// The depth of the input in the measure of the contract, and the start
    /// of every token that opens a level, with that level. The whole input is
    /// at level 1, and one level deeper than the construct that holds them
    /// are the contents of a pair of parentheses, the operand of a unary
    /// minus, the exponent of a power and every operand of a chain after its
    /// first: the right operand of a binary node, opened by its operator.
    fn levels(&self) -> (u64, Vec<(usize, u64)>) {
        let mut openings = Vec::new();
        let mut depth = 0;
        let mut stack = vec![(self.nodes.len() - 1, 1_u64)];
        while let Some((index, place)) = stack.pop() {
            let node = &self.nodes[index];
            let parentheses = node.opens.len() as u64;
            for (inner, start) in node.opens.iter().enumerate() {
                openings.push((*start, place + parentheses - inner as u64));
            }
            let level = place + parentheses;
            depth = depth.max(level);
            match node.shape {
                Shape::Negate(operand) => {
                    openings.push((node.span.0, level + 1));
                    stack.push((operand, level + 1));
                }
                Shape::Binary {
                    at, left, right, ..
                } => {
                    stack.push((left, level));
                    openings.push((at, level + 1));
                    stack.push((right, level + 1));
                }
                Shape::Literal | Shape::Name => {}
            }
        }
        (depth, openings)
    }

    /// The span and the level of the failure of `max_depth` for an input of
    /// `length` bytes, or `None` when the input is not deeper: the whole
    /// input for the level 1, and otherwise the first token in reading order
    /// that opens a level beyond the limit.
    fn depth_failure(&self, length: usize, max_depth: u64) -> Option<((usize, usize), u64)> {
        let (depth, openings) = self.levels();
        if depth <= max_depth {
            return None;
        }
        if max_depth == 0 {
            return Some(((0, length), 1));
        }
        let (start, level) = openings
            .into_iter()
            .filter(|opening| opening.1 > max_depth)
            .min_by_key(|opening| opening.0)?;
        Some(((start, start + 1), level))
    }
}

/// An exact rational of the model: a numerator and a positive denominator
/// in lowest terms, in `i128`. Every operation returns `None` when a part
/// does not fit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Fraction {
    numerator: i128,
    denominator: i128,
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a
}

impl Fraction {
    const ONE: Self = Self {
        numerator: 1,
        denominator: 1,
    };

    /// `numerator / denominator` in lowest terms; `None` for the denominator
    /// 0, which no caller passes, and when a part does not fit.
    fn new(numerator: i128, denominator: i128) -> Option<Self> {
        if denominator == 0 {
            return None;
        }
        let divisor =
            i128::try_from(gcd(numerator.unsigned_abs(), denominator.unsigned_abs())).ok()?;
        let (numerator, denominator) = (numerator / divisor, denominator / divisor);
        if denominator < 0 {
            Self::new(numerator.checked_neg()?, denominator.checked_neg()?)
        } else {
            Some(Self {
                numerator,
                denominator,
            })
        }
    }

    /// The value of a decimal literal: its digits as an integer over $10^k$
    /// for $k$ digits after the point.
    fn literal(text: &str) -> Option<Self> {
        let mut numerator: i128 = 0;
        let mut denominator: i128 = 1;
        let mut fraction = false;
        for byte in text.bytes() {
            if byte == b'.' {
                fraction = true;
                continue;
            }
            numerator = numerator
                .checked_mul(10)?
                .checked_add(i128::from(byte - b'0'))?;
            if fraction {
                denominator = denominator.checked_mul(10)?;
            }
        }
        Self::new(numerator, denominator)
    }

    fn is_zero(self) -> bool {
        self.numerator == 0
    }

    fn plus(self, other: Self) -> Option<Self> {
        let numerator = self
            .numerator
            .checked_mul(other.denominator)?
            .checked_add(other.numerator.checked_mul(self.denominator)?)?;
        Self::new(numerator, self.denominator.checked_mul(other.denominator)?)
    }

    fn times(self, other: Self) -> Option<Self> {
        let first = i128::try_from(gcd(
            self.numerator.unsigned_abs(),
            other.denominator.unsigned_abs(),
        ))
        .ok()?;
        let second = i128::try_from(gcd(
            other.numerator.unsigned_abs(),
            self.denominator.unsigned_abs(),
        ))
        .ok()?;
        let numerator = (self.numerator / first).checked_mul(other.numerator / second)?;
        let denominator = (self.denominator / second).checked_mul(other.denominator / first)?;
        Self::new(numerator, denominator)
    }

    fn negated(self) -> Option<Self> {
        Some(Self {
            numerator: self.numerator.checked_neg()?,
            denominator: self.denominator,
        })
    }

    /// The reciprocal of a number other than 0.
    fn reciprocal(self) -> Option<Self> {
        Self::new(self.denominator, self.numerator)
    }

    /// The power $k$; a zero base with $k < 0$ is excluded by the caller.
    fn power(self, exponent: i128) -> Option<Self> {
        let base = if exponent < 0 {
            self.reciprocal()?
        } else {
            self
        };
        if exponent == 0 {
            return Some(Self::ONE);
        }
        if base.denominator == 1 && matches!(base.numerator, 0 | 1) {
            return Some(base);
        }
        if base.denominator == 1 && base.numerator == -1 {
            return Some(if exponent % 2 == 0 { Self::ONE } else { base });
        }
        // Any other base overflows within 127 factors.
        let mut result = Self::ONE;
        for _ in 0..exponent.unsigned_abs() {
            result = result.times(base)?;
        }
        Some(result)
    }
}

/// What the model expects of a numeric input in the grammar.
#[derive(Debug)]
enum Expected {
    /// The value.
    Number(Fraction),
    /// A fault with its span.
    Fault(FaultKind, (usize, usize)),
    /// An exponent beyond `max_exponent`, with its span.
    ExponentLimit((usize, usize)),
    /// The integers of the model overflowed before the outcome was known.
    Unknown,
}

/// Evaluates the tree of a numeric input as `docs/semantics.md` maps syntax
/// to terms: the operands of a node before it, from left to right, and the
/// first failure ends the evaluation. The divisor of a `/` is inverted, and
/// the operand of a `-` negated, right after it, which is the order of the
/// left-associative reading of a chain; a division by zero has the span from
/// the start of the chain to the end of the divisor. The exponent of a power
/// must be an integer, else `NonIntegerExponent` with the span of the
/// exponent and its parentheses; then its magnitude is checked against
/// `max_exponent` with the same span; then a negative power of 0 fails with
/// `DivisionByZero` and the span of the power.
fn evaluate(tree: &ModelTree, source: &str, max_exponent: u64) -> Expected {
    let bound = u128::from(max_exponent.min(i64::MAX.unsigned_abs()));
    let mut values: Vec<Fraction> = Vec::with_capacity(tree.nodes.len());
    for node in &tree.nodes {
        let value = match node.shape {
            Shape::Literal => Fraction::literal(&source[node.span.0..node.span.1]),
            Shape::Name => return Expected::Unknown,
            Shape::Negate(operand) => values[operand].negated(),
            Shape::Binary {
                operator,
                left,
                right,
                ..
            } => {
                let (a, b) = (values[left], values[right]);
                match operator {
                    b'+' => a.plus(b),
                    b'-' => b.negated().and_then(|b| a.plus(b)),
                    b'*' => a.times(b),
                    b'/' if b.is_zero() => {
                        return Expected::Fault(FaultKind::DivisionByZero, node.span);
                    }
                    b'/' => b.reciprocal().and_then(|b| a.times(b)),
                    _ => {
                        let exponent = tree.nodes[right].outer;
                        if b.denominator != 1 {
                            return Expected::Fault(FaultKind::NonIntegerExponent, exponent);
                        }
                        if b.numerator.unsigned_abs() > bound {
                            return Expected::ExponentLimit(exponent);
                        }
                        if a.is_zero() && b.numerator < 0 {
                            return Expected::Fault(FaultKind::DivisionByZero, node.span);
                        }
                        a.power(b.numerator)
                    }
                }
            }
        };
        match value {
            Some(value) => values.push(value),
            None => return Expected::Unknown,
        }
    }
    values
        .last()
        .map_or(Expected::Unknown, |value| Expected::Number(*value))
}

// ---------------------------------------------------------------------------
// Pieces of input

const DIGITS: [&str; 10] = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];

/// The whitespace of the grammar.
const SPACES: [&str; 5] = [" ", "\t", "\n", "\r", "\x0c"];

/// ASCII characters that start no token: the vertical tab, NUL, delete,
/// escape and punctuation outside the grammar.
const STRAY_ASCII: [&str; 27] = [
    "\x0b", "\0", "\x7f", "\x1b", "=", ",", ";", "!", "#", "$", "%", "&", "[", "]", "{", "}", "<",
    ">", "?", "@", "~", "`", "|", "\\", "\"", "'", ":",
];

/// Characters outside ASCII, of two, three and four bytes: spaces, signs and
/// digits of other scripts, letters, a combining mark and the last code
/// point. Each starts no token.
const NON_ASCII: [&str; 20] = [
    "\u{a0}",
    "\u{85}",
    "\u{2003}",
    "\u{2028}",
    "\u{feff}",
    "\u{d7}",
    "\u{f7}",
    "\u{2212}",
    "\u{2013}",
    "\u{b2}",
    "\u{661}",
    "\u{2460}",
    "\u{3bb}",
    "\u{3c0}",
    "\u{e9}",
    "\u{131}",
    "\u{212a}",
    "\u{301}",
    "\u{1f600}",
    "\u{10ffff}",
];

/// Identifiers: symbols, names that resemble the reserved ones and command
/// words.
const NAMES: [&str; 20] = [
    "x",
    "y",
    "z",
    "x_1",
    "_",
    "_t",
    "Pi",
    "ii",
    "pi2",
    "I",
    "undefined_",
    "e",
    "diff",
    "expand",
    "eval",
    "sin",
    "f",
    "X9",
    "pii",
    "undefine",
];

/// Function-call syntax.
const CALLS: [&str; 9] = [
    "f(",
    "sin (",
    "max(x, y)",
    "pi(",
    "i(2)",
    "diff(x)",
    "g\t(",
    "undefined(",
    "h(x",
];

/// Number literals, valid and malformed.
const NUMBER_PIECES: [&str; 24] = [
    "0",
    "1",
    "2",
    "3",
    "10",
    "1.5",
    "0.25",
    "007",
    "4096",
    "4097",
    "5000",
    "123456789012345678901234567890",
    ".5",
    "1.",
    "1e-3",
    "1e3",
    "2x",
    "1_000",
    "1.2.3",
    "0x10",
    ".",
    "1..2",
    "2.x",
    "0.0",
];

/// Operators and parentheses, alone and in pairs.
const OPERATOR_PIECES: [&str; 14] = [
    "+", "-", "*", "/", "^", "(", ")", "**", "--", "^-", "/-", "-(", ")^", "^(",
];

/// Number literals of the generated expressions.
const LITERALS: [&str; 24] = [
    "0", "1", "2", "3", "4", "5", "7", "9", "10", "12", "100", "007", "0.5", "1.5", "2.25", "0.1",
    "0.125", "3.0", "10.01", "0.0", "00", "1234", "65536", "1.000",
];

/// Divisors whose value is 0.
const ZEROS: [&str; 8] = [
    "0",
    "0.0",
    "00",
    "(1-1)",
    "(2*0)",
    "-0",
    "(3 - 3)",
    "(0.5 - 1/2)",
];

/// Powers of 0, 1 and $-1$ at the bounds of `max_exponent`, and of 0 with
/// negative exponents, within that bound and beyond it, where the exponent
/// is checked first.
const EDGE_POWERS: [&str; 13] = [
    "0^-1",
    "0^(-2)",
    "(1-1)^-3",
    "0^(1-2)",
    "1^4096",
    "(-1)^4097",
    "0^4097",
    "1^-4096",
    "(-1)^(2^12)",
    "0^0",
    "0^-4097",
    "0^(-5000)",
    "(0*7)^-(2^13)",
];

/// Exponents that are small integer literals.
const SMALL_EXPONENTS: [&str; 10] = ["0", "1", "2", "2", "3", "3", "4", "5", "-1", "-2"];

/// Exponents whose value is an integer.
const INTEGER_EXPONENTS: [&str; 10] = [
    "(1+1)",
    "(4/2)",
    "(2*-1)",
    "(-3)",
    "(3-5)",
    "(0)",
    "(2^2)",
    "-(1)",
    "--2",
    "(6/3 - 1)",
];

/// Exponents whose value is not an integer.
const FRACTIONAL_EXPONENTS: [&str; 7] =
    ["(1/2)", "0.5", "(2/3)", "1.5", "(-1/3)", "-(1/2)", "(7/2)"];

/// Exponents beyond the default `max_exponent`, and some at its bound.
const LARGE_EXPONENTS: [&str; 9] = [
    "4096",
    "4097",
    "5000",
    "(2^12)",
    "(2^13)",
    "99999999999999999999",
    "(-4097)",
    "(2^70)",
    "-5000",
];

/// Inputs at the edges of the term core and the limits, with names.
const EDGE_INPUTS: [&str; 22] = [
    "1/(x-x)",
    "(x+y)^4096*(y+x)^4096",
    "9^9^9",
    "x^(1/2)",
    "0^-1",
    "(1/0)^0",
    "0*(1/0)",
    "x^4097",
    "x^(2^70)",
    "2^4096",
    "2^4095*2",
    "pi",
    "i",
    "undefined",
    "f(x)",
    "x/(0*x^(-1))",
    "1/0 + x^y",
    "x^y + 1/0",
    "x^-1 - x^-1",
    "(x^-1)^0 * y",
    "-3/4 + x - 1/2*y",
    "5 + 0*x^(-1)",
];

/// Which productions the expression writer uses.
#[derive(Clone, Copy)]
struct Grammar {
    /// `/` and `^` besides `+`, `-` and `*`.
    divisions_and_powers: bool,
    /// Identifiers among the operands, and now and then a reserved name or a
    /// call.
    names: bool,
}

const RESTRICTED_GRAMMAR: Grammar = Grammar {
    divisions_and_powers: false,
    names: false,
};

const NUMERIC_GRAMMAR: Grammar = Grammar {
    divisions_and_powers: true,
    names: false,
};

const FULL_GRAMMAR: Grammar = Grammar {
    divisions_and_powers: true,
    names: true,
};

/// Writes whitespace between two tokens: often none, often a space, and
/// sometimes any of the five kinds.
fn write_space(random: &mut SplitMix64, text: &mut String) {
    match random.below(8) {
        0..=3 => {}
        4 | 5 => text.push(' '),
        _ => {
            for _ in 0..=random.below(2) {
                text.push_str(random.pick(&SPACES));
            }
        }
    }
}

fn write_digits(random: &mut SplitMix64, count: u64, text: &mut String) {
    for _ in 0..count {
        text.push_str(random.pick(&DIGITS));
    }
}

/// Writes a valid number literal.
fn write_literal(random: &mut SplitMix64, text: &mut String) {
    match random.below(4) {
        0 => text.push_str(random.pick(&LITERALS)),
        1 => {
            let count = 1 + random.below(8);
            write_digits(random, count, text);
        }
        2 => {
            let count = 1 + random.below(4);
            write_digits(random, count, text);
            text.push('.');
            let count = 1 + random.below(4);
            write_digits(random, count, text);
        }
        _ => text.push_str(&random.below(13).to_string()),
    }
}

/// Writes an expression of the grammar: a chain of terms joined by `+` and
/// `-`, with at most `depth` more levels of parentheses.
fn write_expression(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    let terms = 1 + random.below(3);
    for index in 0..terms {
        if index > 0 {
            write_space(random, text);
            text.push_str(random.pick(&["+", "-"]));
            write_space(random, text);
        }
        write_term(random, grammar, depth, text);
    }
}

/// Writes a chain of unary operands joined by `*` and, when the grammar has
/// them, `/`, whose divisor is now and then 0.
fn write_term(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    let factors = 1 + random.below(3);
    for index in 0..factors {
        if index > 0 {
            write_space(random, text);
            let division = grammar.divisions_and_powers && random.chance(1, 3);
            text.push(if division { '/' } else { '*' });
            write_space(random, text);
            if division && random.chance(1, 8) {
                text.push_str(random.pick(&ZEROS));
                continue;
            }
        }
        write_unary(random, grammar, depth, text);
    }
}

/// Writes a unary operand: a unary minus before a unary operand, or a power.
fn write_unary(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    let mut signs = 0;
    while signs < 4 && random.chance(1, 6) {
        text.push('-');
        write_space(random, text);
        signs += 1;
    }
    write_power(random, grammar, depth, text);
}

/// Writes a primary operand, with an exponent when the grammar has powers.
fn write_power(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    if grammar.divisions_and_powers && random.chance(1, 50) {
        text.push_str(random.pick(&EDGE_POWERS));
        return;
    }
    write_primary(random, grammar, depth, text);
    if grammar.divisions_and_powers && random.chance(1, 5) {
        write_space(random, text);
        text.push('^');
        write_space(random, text);
        write_exponent(random, grammar, depth, text);
    }
}

/// Writes the exponent of a power: mostly a small integer, sometimes an
/// expression whose value is an integer, a fraction or beyond
/// `max_exponent`, and sometimes any unary operand.
fn write_exponent(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    match random.below(20) {
        0..=10 => text.push_str(random.pick(&SMALL_EXPONENTS)),
        11..=13 => text.push_str(random.pick(&INTEGER_EXPONENTS)),
        14 | 15 => text.push_str(random.pick(&FRACTIONAL_EXPONENTS)),
        16 => text.push_str(random.pick(&LARGE_EXPONENTS)),
        _ if depth == 0 => text.push_str(random.pick(&SMALL_EXPONENTS)),
        _ => write_unary(random, grammar, depth - 1, text),
    }
}

/// Writes a number, an identifier, or an expression in parentheses.
fn write_primary(random: &mut SplitMix64, grammar: Grammar, depth: u32, text: &mut String) {
    if depth > 0 && random.chance(1, 4) {
        text.push('(');
        write_space(random, text);
        write_expression(random, grammar, depth - 1, text);
        write_space(random, text);
        text.push(')');
    } else if grammar.names && random.chance(1, 3) {
        match random.below(25) {
            0 => text.push_str(random.pick(&RESERVED)),
            1 => text.push_str(random.pick(&CALLS)),
            _ => text.push_str(random.pick(&NAMES)),
        }
    } else {
        write_literal(random, text);
    }
}

/// A random byte offset of `text` on a character boundary, up to its length.
fn boundary(random: &mut SplitMix64, text: &str) -> usize {
    let mut at = random.index(text.len() + 1);
    while !text.is_char_boundary(at) {
        at -= 1;
    }
    at
}

/// Applies one to three random edits to `text`: inserting, deleting or
/// replacing a character, or repeating a piece of the text; `write` writes
/// the inserted characters.
fn mutate(random: &mut SplitMix64, text: &mut String, write: fn(&mut SplitMix64, &mut String)) {
    let edits = 1 + random.below(3);
    for _ in 0..edits {
        let at = boundary(random, text);
        match random.below(4) {
            0 => {
                let mut piece = String::new();
                write(random, &mut piece);
                text.insert_str(at, &piece);
            }
            1 if at < text.len() => {
                text.remove(at);
            }
            2 if at < text.len() => {
                text.remove(at);
                let mut piece = String::new();
                write(random, &mut piece);
                text.insert_str(at, &piece);
            }
            _ => {
                let end = boundary(random, text);
                let (start, end) = (at.min(end), at.max(end));
                let piece = text[start..end].to_owned();
                text.insert_str(end, &piece);
            }
        }
    }
}

/// Writes a character of the restricted alphabet: digits, `.`, `+`, `-`,
/// `*`, parentheses, whitespace and characters that start no token.
fn write_restricted_character(random: &mut SplitMix64, text: &mut String) {
    match random.below(20) {
        0..=6 => text.push_str(random.pick(&DIGITS)),
        7..=12 => text.push_str(random.pick(&["+", "-", "*", "(", ")", "."])),
        13 | 14 => text.push(' '),
        15 => text.push_str(random.pick(&SPACES)),
        16 | 17 => text.push_str(random.pick(&STRAY_ASCII)),
        _ => text.push_str(random.pick(&NON_ASCII)),
    }
}

/// Writes a character or a word of the full alphabet: the restricted
/// alphabet with letters, `_`, `/` and `^`, and now and then a whole name,
/// reserved name or call.
fn write_full_character(random: &mut SplitMix64, text: &mut String) {
    const LETTERS: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_";
    match random.below(24) {
        0..=4 => text.push_str(random.pick(&DIGITS)),
        5..=9 => text.push(char::from(random.pick(LETTERS))),
        10..=14 => text.push_str(random.pick(&["+", "-", "*", "/", "^", "(", ")", "."])),
        15 | 16 => text.push(' '),
        17 => text.push_str(random.pick(&SPACES)),
        18 | 19 => text.push_str(random.pick(&STRAY_ASCII)),
        20 | 21 => text.push_str(random.pick(&NON_ASCII)),
        _ => match random.below(3) {
            0 => text.push_str(random.pick(&RESERVED)),
            1 => text.push_str(random.pick(&CALLS)),
            _ => text.push_str(random.pick(&NAMES)),
        },
    }
}

/// A length of a soup: 0 to 9, 10 to 99 or 100 to 400 bytes, or any length
/// up to 400.
fn soup_length(random: &mut SplitMix64) -> u64 {
    match random.below(4) {
        0 => random.below(10),
        1 => 10 + random.below(90),
        2 => 100 + random.below(301),
        _ => random.below(401),
    }
}

/// A number of levels of nesting: around the default `max_depth` of 128,
/// and up to 3,000.
fn levels(random: &mut SplitMix64) -> usize {
    let levels = match random.below(4) {
        0 => 1 + random.below(130),
        1 => 124 + random.below(10),
        2 => 1 + random.below(600),
        _ => 1 + random.below(3_000),
    };
    levels as usize
}

/// Writes deep nesting or a long chain over the restricted alphabet.
fn write_deep_restricted(random: &mut SplitMix64, text: &mut String) {
    let levels = levels(random);
    let mut core = String::new();
    write_expression(random, RESTRICTED_GRAMMAR, 1, &mut core);
    match random.below(8) {
        0 => {
            text.push_str(&"(".repeat(levels));
            text.push_str(&core);
            text.push_str(&")".repeat(levels));
        }
        1 => {
            text.push_str(&"-".repeat(levels));
            text.push_str(&core);
        }
        2 => {
            text.push_str(&"1+(".repeat(levels));
            text.push('1');
            text.push_str(&")".repeat(levels));
        }
        3 => {
            text.push_str(&"(-".repeat(levels));
            text.push_str(&core);
            text.push_str(&")".repeat(levels));
        }
        4 => {
            let closing = (levels + random.index(5)).saturating_sub(2);
            text.push_str(&"(".repeat(levels));
            text.push_str(&core);
            text.push_str(&")".repeat(closing));
        }
        5 => {
            // A long flat chain: past the default `max_nodes` of 8192 from
            // 4097 operands on.
            let operands = 1 + random.below(6_000);
            for index in 0..operands {
                if index > 0 {
                    text.push_str(random.pick(&["+", "-", "+", "*"]));
                }
                text.push_str(random.pick(&DIGITS));
            }
        }
        6 => {
            text.push_str(&"1*(".repeat(levels));
            text.push('2');
            text.push_str(&")".repeat(levels));
        }
        _ => {
            text.push_str(&"( ".repeat(levels));
            text.push_str(&core);
            text.push_str(&" )".repeat(levels));
        }
    }
}

/// Writes deep nesting, towers and long chains over the full alphabet, and
/// the inputs at the edges of the term core and the limits.
fn write_deep_full(random: &mut SplitMix64, text: &mut String) {
    let levels = levels(random);
    match random.below(10) {
        0 => {
            text.push_str(&"x^".repeat(levels));
            text.push('x');
        }
        1 => {
            text.push_str(&"2^".repeat(1 + random.index(8)));
            text.push('1');
        }
        2 => {
            text.push_str(&"(x+".repeat(levels));
            text.push('y');
            text.push_str(&")".repeat(levels));
        }
        3 => text.push_str(&"f(".repeat(levels)),
        4 => {
            text.push_str(&"-x^-".repeat(levels));
            text.push('y');
        }
        5 => {
            text.push_str(&"x/".repeat(levels));
            text.push('x');
        }
        6 => text.push_str(random.pick(&EDGE_INPUTS)),
        7 => {
            text.push_str(&"x + ".repeat(levels));
            text.push('x');
        }
        8 => {
            text.push_str(&"(".repeat(levels));
            text.push_str(random.pick(&["pi", "x", "2", "x^(1/2)", "1/0"]));
            text.push_str(&")".repeat(levels));
        }
        _ => {
            let mut core = String::new();
            write_expression(random, FULL_GRAMMAR, 3, &mut core);
            text.push_str(&"(".repeat(levels));
            text.push_str(&core);
            text.push_str(&")".repeat(levels));
        }
    }
}

/// Writes a restricted input of one of four kinds, counted in `tally`.
fn write_restricted_input(random: &mut SplitMix64, text: &mut String, tally: &mut Tally) {
    match random.below(20) {
        0..=5 => {
            tally.add("soups", 1);
            for _ in 0..soup_length(random) {
                write_restricted_character(random, text);
            }
        }
        6..=10 => {
            tally.add("expressions", 1);
            let depth = random.below(5) as u32;
            write_expression(random, RESTRICTED_GRAMMAR, depth, text);
        }
        11..=15 => {
            tally.add("edited expressions", 1);
            let depth = random.below(5) as u32;
            write_expression(random, RESTRICTED_GRAMMAR, depth, text);
            mutate(random, text, write_restricted_character);
        }
        _ => {
            tally.add("deep nesting and long chains", 1);
            write_deep_restricted(random, text);
            if random.chance(1, 4) {
                mutate(random, text, write_restricted_character);
            }
        }
    }
}

/// Writes a full input of one of four kinds, counted in `tally`.
fn write_full_input(random: &mut SplitMix64, text: &mut String, tally: &mut Tally) {
    match random.below(20) {
        0..=4 => {
            tally.add("soups", 1);
            for _ in 0..soup_length(random) {
                write_full_character(random, text);
            }
        }
        5..=9 => {
            tally.add("token soups", 1);
            for _ in 0..random.below(60) {
                match random.below(10) {
                    0..=2 => text.push_str(random.pick(&NAMES)),
                    3 => text.push_str(random.pick(&RESERVED)),
                    4 => text.push_str(random.pick(&CALLS)),
                    5 | 6 => text.push_str(random.pick(&NUMBER_PIECES)),
                    _ => text.push_str(random.pick(&OPERATOR_PIECES)),
                }
                if random.chance(2, 3) {
                    write_space(random, text);
                }
            }
        }
        10..=14 => {
            tally.add("expressions", 1);
            let depth = random.below(5) as u32;
            write_expression(random, FULL_GRAMMAR, depth, text);
            if random.chance(1, 2) {
                mutate(random, text, write_full_character);
            }
        }
        _ => {
            tally.add("deep nesting, towers and edges", 1);
            write_deep_full(random, text);
            if random.chance(1, 4) {
                mutate(random, text, write_full_character);
            }
        }
    }
}

/// Counts the length and the characters of an input.
fn note_input(source: &str, tally: &mut Tally) {
    let length = match source.len() {
        0 => "inputs of 0 bytes",
        1..=9 => "inputs of 1 to 9 bytes",
        10..=99 => "inputs of 10 to 99 bytes",
        100..=400 => "inputs of 100 to 400 bytes",
        _ => "inputs of more than 400 bytes",
    };
    tally.add(length, 1);
    if !source.is_ascii() {
        tally.add("inputs with characters outside ASCII", 1);
    }
}

// ---------------------------------------------------------------------------
// Random input over the restricted alphabet

#[test]
fn restricted_inputs_give_a_term_a_syntax_error_or_a_resource_limit() {
    let property = "restricted_inputs_give_a_term_a_syntax_error_or_a_resource_limit";
    let tally = run(property, RESTRICTED_SEED, INPUTS, check_restricted);
    tally.require(
        property,
        &[
            "inputs of 0 bytes",
            "inputs of 1 to 9 bytes",
            "inputs of 10 to 99 bytes",
            "inputs of 100 to 400 bytes",
            "inputs of more than 400 bytes",
            "inputs with characters outside ASCII",
            "inputs deeper than the default max_depth",
            "values compared with the model",
            "generous limits: a term",
            "generous limits: Syntax",
            "default limits: a term",
            "default limits: Syntax",
            "default limits: ResourceLimit max_depth",
            "default limits: ResourceLimit max_nodes",
            "a small limit: ResourceLimit max_input_bytes",
            "a small limit: ResourceLimit max_depth",
            "a small limit: ResourceLimit max_nodes",
            "a small limit: ResourceLimit max_work",
            "a small limit: ResourceLimit max_integer_bits",
            "a small limit: ResourceLimit max_storage_bytes",
            "depth failures predicted by the model",
            "node failures predicted by the model",
        ],
    );
}

/// Asserts that a result of a restricted input is a term, a `Syntax` error
/// or a `ResourceLimit`.
fn assert_restricted_kind(result: &Result<Term, Error>) {
    assert!(
        result
            .as_ref()
            .is_ok_and(|term| term.kind() == TermKind::Number)
            || fails_with(result, FaultKind::Syntax)
            || result
                .as_ref()
                .is_err_and(|error| error.kind() == ErrorKind::ResourceLimit),
        "an input without `/`, `^` and letters gives {}",
        report(result)
    );
}

fn check_restricted(case: &mut Case, tally: &mut Tally) {
    let mut source = String::new();
    write_restricted_input(&mut case.random, &mut source, tally);
    case.input(&source);
    note_input(&source, tally);
    assert!(
        !source
            .bytes()
            .any(|byte| byte == b'/' || byte == b'^' || is_name_start(byte)),
        "the restricted alphabet has no `/`, `^`, letters or `_`"
    );
    let tree = match read_model(&source) {
        Reading::Tree(tree) => Some(tree),
        Reading::Syntax => None,
        _ => panic!("the model reads a name in input without letters"),
    };

    // Under limits far above the input, the model decides the result: a
    // term whose number is the value of the model, or `Syntax`.
    let wide = generous();
    let reference = parse_checked(&source, &wide);
    tally.add(
        format!("generous limits: {}", outcome(&reference.result)),
        1,
    );
    assert_restricted_kind(&reference.result);
    match &tree {
        None => assert!(
            fails_with(&reference.result, FaultKind::Syntax),
            "the model reads no expression of the grammar, the parser gives {}",
            report(&reference.result)
        ),
        Some(tree) => {
            if tree.levels().0 > Limits::new().max_depth {
                tally.add("inputs deeper than the default max_depth", 1);
            }
            let expected = evaluate(tree, &source, wide.max_exponent);
            if let Expected::Number(_) = expected {
                tally.add("values compared with the model", 1);
            }
            assert!(
                reference.result.is_ok(),
                "an expression of the grammar gives {} under limits far above it",
                report(&reference.result)
            );
            assert_expected(&expected, &reference.result);
        }
    }
    if let Ok(term) = &reference.result {
        assert_reads_back(term);
    }

    // The default limits.
    let default = parse_checked(&source, &Limits::new());
    tally.add(format!("default limits: {}", outcome(&default.result)), 1);
    assert_restricted_kind(&default.result);
    assert_consistent(&default, &reference);

    // One small limit.
    let (field, limits) = small_limits(&mut case.random, source.len(), &RESTRICTED_SMALL);
    case.note(format!(
        "the third run makes {} small: {}",
        field.name(),
        limits.get(field)
    ));
    let small = parse_checked(&source, &limits);
    tally.add(format!("a small limit: {}", outcome(&small.result)), 1);
    assert_restricted_kind(&small.result);
    assert_consistent(&small, &reference);
    assert_level_one(&source, &limits, &small.result);
    if let Some(tree) = &tree {
        assert_exact_limits(&source, tree, field, &limits, &small.result);
        note_prediction(field, &small.result, tally);
    }
}

/// Counts the failures of the small limit that the model predicted.
fn note_prediction(field: LimitField, result: &Result<Term, Error>, tally: &mut Tally) {
    if field == LimitField::Depth && fails_with_limit(result, LimitField::Depth) {
        tally.add("depth failures predicted by the model", 1);
    }
    if field == LimitField::Nodes && fails_with_limit(result, LimitField::Nodes) {
        tally.add("node failures predicted by the model", 1);
    }
}

// ---------------------------------------------------------------------------
// Random input over the full alphabet

#[test]
fn full_inputs_give_only_the_listed_errors_with_spans_in_the_input() {
    let property = "full_inputs_give_only_the_listed_errors_with_spans_in_the_input";
    let tally = run(property, FULL_SEED, INPUTS, check_full);
    tally.require(
        property,
        &[
            "inputs of 0 bytes",
            "inputs of 100 to 400 bytes",
            "inputs of more than 400 bytes",
            "inputs with characters outside ASCII",
            "read as a tree",
            "read as Syntax",
            "read as Unsupported",
            "read in the order of failures: a reserved name or a call where an operator is expected",
            "read in the order of failures: a reserved name before a malformed literal or a stray character",
            "values compared with the model",
            "terms read back from their display",
            "generous limits: a term",
            "generous limits: Syntax",
            "generous limits: Unsupported",
            "generous limits: NonIntegerExponent",
            "generous limits: DivisionByZero",
            "generous limits: ResourceLimit max_exponent",
            "default limits: a term",
            "default limits: ResourceLimit max_depth",
            "default limits: ResourceLimit max_integer_bits",
            "a small limit: ResourceLimit max_input_bytes",
            "a small limit: ResourceLimit max_depth",
            "a small limit: ResourceLimit max_nodes",
            "a small limit: ResourceLimit max_work",
            "a small limit: ResourceLimit max_integer_bits",
            "a small limit: ResourceLimit max_storage_bytes",
            "a small limit: ResourceLimit max_exponent",
            "depth failures predicted by the model",
            "node failures predicted by the model",
        ],
    );
}

fn check_full(case: &mut Case, tally: &mut Tally) {
    let mut source = String::new();
    write_full_input(&mut case.random, &mut source, tally);
    case.input(&source);
    note_input(&source, tally);
    let reading = read_model(&source);

    // Under limits far above the input, the model decides whether the input
    // is in the grammar, and the result of numeric input.
    let wide = generous();
    let reference = parse_checked(&source, &wide);
    let result = &reference.result;
    check_fault_text(&source, result);
    tally.add(format!("generous limits: {}", outcome(result)), 1);
    match &reading {
        Reading::Tree(tree) => {
            tally.add("read as a tree", 1);
            assert!(
                !fails_with(result, FaultKind::Syntax)
                    && !fails_with(result, FaultKind::Unsupported),
                "an expression of the grammar gives {}",
                report(result)
            );
            if !tree.has_names() {
                let expected = evaluate(tree, &source, wide.max_exponent);
                if !matches!(expected, Expected::Unknown) {
                    tally.add("values compared with the model", 1);
                }
                assert_expected(&expected, result);
            }
        }
        Reading::Syntax => {
            tally.add("read as Syntax", 1);
            assert!(
                fails_with(result, FaultKind::Syntax),
                "the model reads a syntax error first, the parser gives {}",
                report(result)
            );
        }
        Reading::Unsupported => {
            tally.add("read as Unsupported", 1);
            assert!(
                fails_with(result, FaultKind::Unsupported),
                "the model reads a reserved name or a call first, the parser gives {}",
                report(result)
            );
        }
        Reading::Ordered(fault, reason) => {
            tally.add(format!("read in the order of failures: {reason}"), 1);
            assert!(
                fails_with(result, *fault),
                "the order of failures gives {fault:?} first ({reason}), the parser gives {}",
                report(result)
            );
        }
    }
    if let Ok(term) = result {
        if !source.bytes().any(is_name_start) {
            assert_eq!(term.kind(), TermKind::Number, "input without names");
        }
        assert_reads_back(term);
        tally.add("terms read back from their display", 1);
    }

    // The default limits.
    let default = parse_checked(&source, &Limits::new());
    check_fault_text(&source, &default.result);
    tally.add(format!("default limits: {}", outcome(&default.result)), 1);
    assert_consistent(&default, &reference);

    // One small limit.
    let (field, limits) = small_limits(&mut case.random, source.len(), &FULL_SMALL);
    case.note(format!(
        "the third run makes {} small: {}",
        field.name(),
        limits.get(field)
    ));
    let small = parse_checked(&source, &limits);
    check_fault_text(&source, &small.result);
    tally.add(format!("a small limit: {}", outcome(&small.result)), 1);
    assert_consistent(&small, &reference);
    assert_level_one(&source, &limits, &small.result);
    if let Reading::Tree(tree) = &reading
        && !tree.has_names()
    {
        assert_exact_limits(&source, tree, field, &limits, &small.result);
        note_prediction(field, &small.result, tally);
    }
}

// ---------------------------------------------------------------------------
// Round trips of display text

/// The symbols of the generated terms, with names that resemble the
/// reserved ones and a command word.
const SYMBOLS: [&str; 14] = [
    "x",
    "y",
    "z",
    "x_1",
    "Pi",
    "ii",
    "pi2",
    "_",
    "_t",
    "I",
    "undefined_",
    "diff",
    "a1b2",
    "a_long_symbol_name",
];

/// The names among [`SYMBOLS`] that resemble a reserved name.
const RESEMBLING: [&str; 5] = ["Pi", "ii", "pi2", "I", "undefined_"];

/// Small numbers of the generated terms, as a numerator and a positive
/// denominator.
const FRACTIONS: [(i64, i64); 16] = [
    (0, 1),
    (1, 1),
    (-1, 1),
    (2, 1),
    (-2, 1),
    (3, 1),
    (1, 2),
    (-1, 2),
    (3, 4),
    (-3, 4),
    (5, 3),
    (-7, 2),
    (10, 1),
    (100, 1),
    (-12, 5),
    (2, 3),
];

/// The exponents of the generated powers.
const TERM_EXPONENTS: [i64; 11] = [-3, -2, -1, -1, 0, 0, 1, 2, 2, 3, 4];

/// Exponents of several digits, up to the default `max_exponent`, for powers
/// of bases that are not numbers.
const LARGE_TERM_EXPONENTS: [i64; 6] = [-4096, -100, -17, 12, 99, 4096];

/// The forms of display text that the round trips must exercise.
const FORMS: [&str; 21] = [
    "a negative fraction",
    "a number beyond 64 bits",
    "a name that resembles a reserved one",
    "a negative exponent",
    "a one (b^(-1))^0",
    "a power of a sum",
    "a power of a power",
    "an exponent of several digits",
    "a product with the coefficient 0",
    "a product with the coefficient -1",
    "a product with a fractional coefficient",
    "a product with a sum among its factors",
    "a product of several factors",
    "a sum with a constant",
    "a sum with a negative fractional constant",
    "a sum with a witness monomial",
    "a sum with a negative coefficient",
    "a sum with a coefficient other than 1 and -1",
    "a sum with a product as a core",
    "a sum whose text starts with a minus",
    "a sum of several monomials",
];

#[test]
fn display_text_reads_back_as_the_same_term() {
    let property = "display_text_reads_back_as_the_same_term";
    let tally = run(property, ROUND_TRIP_SEED, ROUND_TRIPS, check_round_trip);
    tally.require(property, &FORMS);
}

fn check_round_trip(case: &mut Case, tally: &mut Tally) {
    let c = &mut context(generous());
    for _ in 0..ATTEMPTS {
        match random_term(&mut case.random, 4, c) {
            Ok(term) => {
                let text = term.display(c).unwrap();
                case.input(&text);
                if text.len() > 4_000 {
                    tally.add("terms drawn again for a text beyond 4000 bytes", 1);
                    continue;
                }
                assert_reads_back(&term);
                note_forms(&term, tally);
                return;
            }
            Err(error) => tally.add(
                format!("terms drawn again after {}", outcome(&Err(error))),
                1,
            ),
        }
    }
    panic!("no term in {ATTEMPTS} attempts");
}

fn number(value: i64, c: &mut Context) -> Result<Term, Error> {
    Term::number(Rational::from(value), c)
}

fn random_symbol(random: &mut SplitMix64, c: &mut Context) -> Result<Term, Error> {
    Term::symbol(random.pick(&SYMBOLS), c)
}

/// A value in `-magnitude..=magnitude`.
fn signed(random: &mut SplitMix64, magnitude: u64) -> i64 {
    random.below(2 * magnitude + 1) as i64 - magnitude as i64
}

/// A random rational: small fractions, random fractions and decimals, and
/// numbers beyond 64 bits.
fn random_rational(random: &mut SplitMix64, c: &mut Context) -> Result<Rational, Error> {
    match random.below(8) {
        0..=3 => {
            let (numerator, denominator) = random.pick(&FRACTIONS);
            Rational::new(Integer::from(numerator), Integer::from(denominator), c)
        }
        4 => {
            let numerator = signed(random, 1_000_000_000);
            let denominator = 1 + random.below(1_000_000);
            Rational::new(Integer::from(numerator), Integer::from(denominator), c)
        }
        5 => {
            let numerator = signed(random, 10_000_000);
            let denominator = Rational::from(10).power(random.below(7) as i64, c)?;
            Rational::from(numerator).divide(&denominator, c)
        }
        6 => {
            let power = Rational::from(2).power(64 + random.below(137) as i64, c)?;
            let numerator = power.add(&Rational::from(signed(random, 1000)), c)?;
            let denominator = Rational::from(3).power(random.below(41) as i64, c)?;
            numerator.divide(&denominator, c)
        }
        _ => {
            let power = Rational::from(10).power(19 + random.below(42) as i64, c)?;
            let nines = power.subtract(&Rational::from(1), c)?;
            if random.chance(1, 2) {
                nines.negate(c)
            } else {
                Ok(nines)
            }
        }
    }
}

fn random_number(random: &mut SplitMix64, c: &mut Context) -> Result<Term, Error> {
    let value = random_rational(random, c)?;
    Term::number(value, c)
}

/// A random term built through the constructors of the term core, with at
/// most `depth` levels of operations: sums, products, powers, negations,
/// differences and quotients of random terms, the witness shapes, sums
/// scaled by numbers, sums whose content is not 1 as factors and bases, like
/// terms, powers of powers, and scaled copies of one sum among the operands
/// of a sum.
fn random_term(random: &mut SplitMix64, depth: u32, c: &mut Context) -> Result<Term, Error> {
    if depth == 0 || random.chance(1, 4) {
        return if random.chance(11, 20) {
            random_symbol(random, c)
        } else {
            random_number(random, c)
        };
    }
    let below = depth - 1;
    match random.below(15) {
        0 | 1 => {
            let count = 2 + random.below(3);
            let parts = random_terms(random, count, below, c)?;
            Term::sum(&parts, c)
        }
        2 | 3 => {
            let count = 2 + random.below(2);
            let parts = random_terms(random, count, below, c)?;
            Term::product(&parts, c)
        }
        4 => {
            if random.chance(1, 6) {
                let base = if random.chance(1, 2) {
                    random_symbol(random, c)?
                } else {
                    content_sum(random, below, c)?
                };
                base.power(random.pick(&LARGE_TERM_EXPONENTS), c)
            } else {
                random_term(random, below, c)?.power(random.pick(&TERM_EXPONENTS), c)
            }
        }
        5 => random_term(random, below, c)?.negate(c),
        6 => {
            let minuend = random_term(random, below, c)?;
            let subtrahend = random_term(random, below, c)?;
            minuend.subtract(&subtrahend, c)
        }
        7 => {
            let dividend = random_term(random, below, c)?;
            let divisor = random_term(random, below, c)?;
            dividend.divide(&divisor, c)
        }
        8 => witness(random, below, c),
        9 => {
            let count = 2 + random.below(2);
            let parts = random_terms(random, count, below, c)?;
            let sum = Term::sum(&parts, c)?;
            let scale = random_number(random, c)?;
            Term::product(&[scale, sum], c)
        }
        10 => content_sum(random, below, c),
        11 => {
            let term = random_term(random, below, c)?;
            let scale = random_number(random, c)?;
            let scaled = Term::product(&[scale, term.clone()], c)?;
            let negated = term.negate(c)?;
            Term::sum(&[term, scaled, negated], c)
        }
        12 => {
            let term = random_term(random, below, c)?;
            let inner = term.power(random.pick(&TERM_EXPONENTS), c)?;
            inner.power(random.pick(&TERM_EXPONENTS), c)
        }
        13 => {
            let parts = random_terms(random, 2, below, c)?;
            let sum = Term::sum(&parts, c)?;
            let two = number(2, c)?;
            let double = Term::product(&[two, sum.clone()], c)?;
            let negated = sum.negate(c)?;
            let other = random_term(random, below, c)?;
            match random.below(3) {
                0 => Term::sum(&[double, negated.clone(), negated, other], c),
                1 => Term::sum(&[double.clone(), negated.clone(), double, negated], c),
                _ => Term::sum(&[other, double, negated], c),
            }
        }
        _ => {
            let scale = random_number(random, c)?;
            let term = random_term(random, below, c)?;
            Term::product(&[scale, term], c)
        }
    }
}

fn random_terms(
    random: &mut SplitMix64,
    count: u64,
    depth: u32,
    c: &mut Context,
) -> Result<Vec<Term>, Error> {
    let mut terms = Vec::new();
    for _ in 0..count {
        terms.push(random_term(random, depth, c)?);
    }
    Ok(terms)
}

/// The witness shapes of the term core: $b^2 \cdot b^{-1}$, $b \cdot b^{-1}$,
/// $0 \cdot b^{-1}$, $(b^{-1})^0$, a sum whose monomials $b^{-1}$ cancel,
/// beside another term or a constant, a product with a one, and a product of
/// ones.
fn witness(random: &mut SplitMix64, depth: u32, c: &mut Context) -> Result<Term, Error> {
    let base = if random.chance(1, 2) {
        random_symbol(random, c)?
    } else {
        random_term(random, depth, c)?
    };
    let inverse = base.power(-1, c)?;
    match random.below(8) {
        0 => {
            let square = base.power(2, c)?;
            Term::product(&[square, inverse], c)
        }
        1 => Term::product(&[base, inverse], c),
        2 => {
            let zero = number(0, c)?;
            Term::product(&[zero, inverse], c)
        }
        3 => inverse.power(0, c),
        4 => {
            let other = random_term(random, depth, c)?;
            let negated = inverse.negate(c)?;
            Term::sum(&[other, inverse, negated], c)
        }
        5 => {
            let five = number(5, c)?;
            let negated = inverse.negate(c)?;
            Term::sum(&[five, inverse, negated], c)
        }
        6 => {
            let other = random_symbol(random, c)?;
            let one = inverse.power(0, c)?;
            Term::product(&[other, one], c)
        }
        _ => {
            let other = random_symbol(random, c)?;
            let product = Term::product(&[base, other], c)?;
            product.power(-1, c)?.power(0, c)
        }
    }
}

/// A sum whose content is not 1, $c a + c b$, as a factor of a product or the
/// base of a power, or a power of $1 - s$ for a symbol $s$.
fn content_sum(random: &mut SplitMix64, depth: u32, c: &mut Context) -> Result<Term, Error> {
    let scale = random_number(random, c)?;
    let first = random_symbol(random, c)?;
    let second = random_term(random, depth, c)?;
    let scaled_first = Term::product(&[scale.clone(), first], c)?;
    let scaled_second = Term::product(&[scale, second], c)?;
    let sum = Term::sum(&[scaled_first, scaled_second], c)?;
    match random.below(3) {
        0 => {
            let other = random_term(random, depth, c)?;
            Term::product(&[sum, other], c)
        }
        1 => sum.power(random.pick(&TERM_EXPONENTS), c),
        _ => {
            let one = number(1, c)?;
            let symbol = random_symbol(random, c)?;
            one.subtract(&symbol, c)?
                .power(random.pick(&[-2, -1, 2, 3]), c)
        }
    }
}

/// Whether `value` is 1 or $-1$.
fn is_unit(value: &Rational) -> bool {
    *value == Rational::from(1) || *value == Rational::from(-1)
}

fn is_wide(value: &Rational) -> bool {
    value.numerator().bits() > 64 || value.denominator().bits() > 64
}

/// Counts the forms of display text that `term` holds, walking it through
/// the accessors.
fn note_forms(term: &Term, tally: &mut Tally) {
    let mut stack = vec![term.clone()];
    while let Some(node) = stack.pop() {
        match node.kind() {
            TermKind::Number => {
                let value = node.as_number().unwrap();
                if value.is_negative() && !value.is_integer() {
                    tally.add("a negative fraction", 1);
                }
                if is_wide(value) {
                    tally.add("a number beyond 64 bits", 1);
                }
            }
            TermKind::Symbol => {
                if RESEMBLING.contains(&node.as_symbol().unwrap()) {
                    tally.add("a name that resembles a reserved one", 1);
                }
            }
            TermKind::Power => {
                let (base, exponent) = node.as_power().unwrap();
                if exponent < 0 {
                    tally.add("a negative exponent", 1);
                }
                if exponent == 0 {
                    tally.add("a one (b^(-1))^0", 1);
                }
                if exponent.unsigned_abs() >= 10 {
                    tally.add("an exponent of several digits", 1);
                }
                match base.kind() {
                    TermKind::Sum => tally.add("a power of a sum", 1),
                    TermKind::Power => tally.add("a power of a power", 1),
                    _ => {}
                }
            }
            TermKind::Product => {
                let (coefficient, factors) = node.as_product().unwrap();
                if coefficient.is_zero() {
                    tally.add("a product with the coefficient 0", 1);
                }
                if *coefficient == Rational::from(-1) {
                    tally.add("a product with the coefficient -1", 1);
                }
                if !coefficient.is_integer() {
                    tally.add("a product with a fractional coefficient", 1);
                }
                if is_wide(coefficient) {
                    tally.add("a number beyond 64 bits", 1);
                }
                if factors.iter().any(|factor| factor.kind() == TermKind::Sum) {
                    tally.add("a product with a sum among its factors", 1);
                }
                if factors.len() > 1 {
                    tally.add("a product of several factors", 1);
                }
            }
            TermKind::Sum => {
                let (constant, coefficients, cores) = node.as_sum().unwrap();
                if !constant.is_zero() {
                    tally.add("a sum with a constant", 1);
                }
                if constant.is_negative() && !constant.is_integer() {
                    tally.add("a sum with a negative fractional constant", 1);
                }
                if is_wide(constant) || coefficients.iter().any(is_wide) {
                    tally.add("a number beyond 64 bits", 1);
                }
                if coefficients.iter().any(Rational::is_zero) {
                    tally.add("a sum with a witness monomial", 1);
                }
                if coefficients.iter().any(Rational::is_negative) {
                    tally.add("a sum with a negative coefficient", 1);
                }
                if coefficients
                    .iter()
                    .any(|value| !value.is_zero() && !is_unit(value))
                {
                    tally.add("a sum with a coefficient other than 1 and -1", 1);
                }
                if cores.iter().any(|core| core.kind() == TermKind::Product) {
                    tally.add("a sum with a product as a core", 1);
                }
                if constant.is_zero() && coefficients.first().is_some_and(Rational::is_negative) {
                    tally.add("a sum whose text starts with a minus", 1);
                }
                if cores.len() > 1 {
                    tally.add("a sum of several monomials", 1);
                }
            }
            _ => {}
        }
        stack.extend(node.children().iter().cloned());
    }
}

// ---------------------------------------------------------------------------
// Numeric input against the evaluator

#[test]
fn numeric_input_has_the_value_of_an_independent_evaluator() {
    let property = "numeric_input_has_the_value_of_an_independent_evaluator";
    let tally = run(property, NUMERIC_SEED, EXPRESSIONS, check_numeric);
    assert!(
        tally.get("cases compared") >= 2_000,
        "{property}: fewer than 2,000 expressions compared"
    );
    tally.require(
        property,
        &[
            "numbers",
            "fractions",
            "DivisionByZero",
            "NonIntegerExponent",
            "ResourceLimit max_exponent",
        ],
    );
}

fn check_numeric(case: &mut Case, tally: &mut Tally) {
    let limits = generous();
    for _ in 0..ATTEMPTS {
        let mut source = String::new();
        write_expression(&mut case.random, NUMERIC_GRAMMAR, 3, &mut source);
        case.input(&source);
        let Reading::Tree(tree) = read_model(&source) else {
            panic!("the writer of expressions wrote input outside the grammar");
        };
        let expected = evaluate(&tree, &source, limits.max_exponent);
        match &expected {
            Expected::Unknown => {
                tally.add("expressions drawn again after an overflow of the model", 1);
                continue;
            }
            Expected::Number(value) => {
                tally.add("numbers", 1);
                if value.denominator != 1 {
                    tally.add("fractions", 1);
                }
            }
            Expected::Fault(fault, _) => tally.add(format!("{fault:?}"), 1),
            Expected::ExponentLimit(_) => tally.add("ResourceLimit max_exponent", 1),
        }
        let run = parse_checked(&source, &limits);
        assert_expected(&expected, &run.result);
        tally.add("cases compared", 1);
        return;
    }
    panic!("no expression in {ATTEMPTS} attempts");
}

// ---------------------------------------------------------------------------
// The model against the documents

/// The input of the case `id` of `vectors/r02.tsv`.
fn vector(id: &str) -> &'static str {
    VECTORS
        .lines()
        .find_map(|line| {
            let mut columns = line.split('\t');
            (columns.next() == Some(id)).then(|| columns.nth(2).unwrap())
        })
        .unwrap_or_else(|| panic!("no vector {id}"))
}

fn model_tree(source: &str) -> ModelTree {
    match read_model(source) {
        Reading::Tree(tree) => tree,
        _ => panic!("the model reads no expression in {source:?}"),
    }
}

// The model agrees with every example of `docs/semantics.md` and of the
// contract that it can decide without the term core, and with the depth
// cases of `vectors/r02.tsv`.
#[test]
fn the_model_reads_the_examples_of_the_documents() {
    for (source, numerator, denominator) in [
        ("(1+2)*3", 9, 1),
        ("2^3^2", 512, 1),
        ("(2^3)^2", 64, 1),
        ("-2^2", -4, 1),
        ("(-2)^2", 4, 1),
        ("-3^2*2", -18, 1),
        ("8/4/2", 1, 1),
        ("2/3*3", 2, 1),
        ("5-2-1", 2, 1),
        ("-2^2 + 2^3^2", 508, 1),
        ("2*-3+4", -2, 1),
        ("1--1", 2, 1),
        ("--2", 2, 1),
        ("2^-2", 1, 4),
        ("-2^-2", -1, 4),
        ("2^-1^2", 1, 2),
        ("1.5", 3, 2),
        ("0.1 + 0.2", 3, 10),
        ("001.2500", 5, 4),
        ("0^0", 1, 1),
        ("x^(1+1)", 0, 0),
        ("\t1 +\r\n2\x0c", 3, 1),
    ] {
        let tree = model_tree(source);
        match evaluate(&tree, source, 4096) {
            Expected::Number(value) => {
                assert_eq!(
                    (value.numerator, value.denominator),
                    (numerator, denominator),
                    "{source}"
                );
            }
            Expected::Unknown => assert!(tree.has_names(), "{source}"),
            other => panic!("{source}: {other:?}"),
        }
    }
    for source in [
        "",
        "   ",
        "+1",
        "1++2",
        ".5",
        "1.",
        "1e-3",
        "1e3",
        "2x",
        "2.5x",
        "0x10",
        "1_000",
        "1.2.3",
        ".",
        "()",
        "1+",
        "(1+2",
        "1+2)",
        "1 2",
        "x y",
        "x.5",
        "(1)(2)",
        "2(x + 1)",
        "1+\u{3bb}",
        "\u{3bb}",
        "x=1",
        "1/**2",
        "2^",
        "2^*3",
        "x,y",
        "1\u{d7}2",
        "1\u{b}+2",
        "2 x",
        "expand x",
        "1 2x",
    ] {
        assert!(matches!(read_model(source), Reading::Syntax), "{source:?}");
    }
    for source in [
        "pi",
        "i",
        "undefined",
        "2*pi",
        "x + i*y",
        "pi(2)",
        "pi(x)",
        "pi (x)",
        "f(x)",
        "f (x)",
        "sin(1)",
        "max(x, y)",
        "2*g(x)",
        "diff(x^2)",
        "f(",
    ] {
        assert!(
            matches!(read_model(source), Reading::Unsupported),
            "{source:?}"
        );
    }
    for (source, fault) in [
        ("1 pi", FaultKind::Syntax),
        ("1 f(x)", FaultKind::Syntax),
        ("x f(1)", FaultKind::Syntax),
        ("pi$", FaultKind::Unsupported),
        ("pi 1.", FaultKind::Unsupported),
    ] {
        assert!(
            matches!(read_model(source), Reading::Ordered(found, _) if found == fault),
            "{source:?}"
        );
    }
    for source in [
        "Pi",
        "ii",
        "pi2",
        "_pi",
        "I",
        "undefined_",
        "diff",
        "expand + diff*eval",
    ] {
        assert!(matches!(read_model(source), Reading::Tree(_)), "{source:?}");
    }
    for (source, fault, start, end) in [
        ("0*(1/0)", FaultKind::DivisionByZero, 3, 6),
        ("(1)/0", FaultKind::DivisionByZero, 0, 5),
        ("(1/0)^0", FaultKind::DivisionByZero, 1, 4),
        ("(1/0)^(1/0)", FaultKind::DivisionByZero, 1, 4),
        ("0^(-1)", FaultKind::DivisionByZero, 0, 6),
        ("0^-1", FaultKind::DivisionByZero, 0, 4),
        ("2*3/(1-1)*4", FaultKind::DivisionByZero, 0, 9),
        ("1/0 + 2^(1/2)", FaultKind::DivisionByZero, 0, 3),
        ("2 - 1/0*3", FaultKind::DivisionByZero, 4, 7),
        ("2^(1/2)", FaultKind::NonIntegerExponent, 2, 7),
        ("2^(1/2) + 1/0", FaultKind::NonIntegerExponent, 2, 7),
        ("2^0.5", FaultKind::NonIntegerExponent, 2, 5),
        ("2^(1/2)^1", FaultKind::NonIntegerExponent, 2, 9),
        ("2^(2/2)^(1/2)", FaultKind::NonIntegerExponent, 8, 13),
        ("2^-(1/2)", FaultKind::NonIntegerExponent, 2, 8),
    ] {
        let tree = model_tree(source);
        match evaluate(&tree, source, 4096) {
            Expected::Fault(found, span) => {
                assert_eq!((found, span), (fault, (start, end)), "{source}")
            }
            other => panic!("{source}: {other:?}"),
        }
    }
    let tree = model_tree("x^5000");
    assert!(matches!(
        evaluate(&model_tree("2^5000"), "2^5000", 4096),
        Expected::ExponentLimit((2, 6))
    ));
    assert!(matches!(evaluate(&tree, "x^5000", 4096), Expected::Unknown));
    for (source, depth, nodes) in [
        ("1", 1, 1),
        ("(1)", 2, 1),
        ("((x))", 3, 1),
        ("-1", 2, 2),
        ("-x", 2, 2),
        ("1+2+3", 2, 5),
        ("1+2+3+4", 2, 7),
        ("1+1+1+1", 2, 7),
        ("1*2+3", 2, 5),
        ("1+2*3", 3, 5),
        ("2^3^2", 3, 5),
        ("2^3^4", 3, 5),
        ("-2^2", 3, 4),
        ("2^-1", 3, 4),
        ("2^-3", 3, 4),
        ("((((1))))", 5, 1),
        ("2*(3+4)", 4, 5),
        ("1+(1+(1))", 5, 5),
        ("(1 + 2) * x", 3, 5),
        ("0*(1/0)", 4, 5),
        ("x/y + 1", 2, 5),
    ] {
        let tree = model_tree(source);
        assert_eq!(
            (tree.levels().0, tree.nodes.len()),
            (depth, nodes),
            "{source}"
        );
    }
    let nested = |levels: usize| format!("{}1{}", "(".repeat(levels), ")".repeat(levels));
    assert_eq!(model_tree(&nested(127)).levels().0, 128);
    assert_eq!(model_tree(&nested(127)).depth_failure(255, 128), None);
    let source = nested(128);
    assert_eq!(
        model_tree(&source).depth_failure(source.len(), 128),
        Some(((127, 128), 129))
    );
    assert_eq!(model_tree("1+-2").depth_failure(4, 2), Some(((2, 3), 3)));
    assert_eq!(model_tree("x^y^z").depth_failure(5, 2), Some(((3, 4), 3)));
    assert_eq!(model_tree("x").depth_failure(1, 0), Some(((0, 1), 1)));
    // The depth cases of the answer vectors: 63 right-nested sums reach the
    // depth 127, 64 fail at `max_depth` 32 at their 16th `(`, and 192 nested
    // parentheses fail at `max_depth` 128 at their 128th `(`.
    assert_eq!(model_tree(vector("right_nested_63")).levels().0, 127);
    let source = vector("right_depth_limit_1");
    assert_eq!(
        model_tree(source).depth_failure(source.len(), 32),
        Some(((47, 48), 33))
    );
    let source = vector("depth_limit_1");
    assert_eq!(
        model_tree(source).depth_failure(source.len(), 128),
        Some(((127, 128), 129))
    );
}
