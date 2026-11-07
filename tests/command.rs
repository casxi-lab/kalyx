//! The command entry, as code outside the library sees it: the three
//! operations, the rejected requests and their order, the versions that an
//! outcome echoes, the line bytes of outcomes and their bounded output, the
//! deadline and cancellation, a property test of the determinism of lines,
//! and the replay of every case of `vectors/r02.tsv`. The rules are those of
//! `docs/components/command/contract.md` and of the output lines of
//! `docs/semantics.md`. Errors are compared by kind, span and exceeded
//! limit, never by message.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a malformed case, as the tests do"
)]

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use kalyx::coefficient::Rationals;
use kalyx::command::{Settings, serialize};
use kalyx::context::{CancelFlag, CancelProbe, Clock};
use kalyx::polynomial::PolynomialRing;
use kalyx::syntax::parse;
use kalyx::term::Term;
use kalyx::{
    Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope, Limits,
    Outcome, Request, Settled, Span, execute,
};

const VECTORS: &str = include_str!("../vectors/r02.tsv");

/// The operations of the dispatch table.
const OPERATIONS: [&str; 3] = ["eval", "expand", "diff"];

// ---------------------------------------------------------------------------
// Fakes and helpers

/// A clock whose reading the test sets, counting its readings.
#[derive(Clone, Default)]
struct FakeClock {
    now: Arc<AtomicU64>,
    reads: Arc<AtomicU64>,
}

impl FakeClock {
    fn at(now: u64) -> Self {
        let clock = Self::default();
        clock.set(now);
        clock
    }

    fn set(&self, now: u64) {
        self.now.store(now, Ordering::SeqCst);
    }

    fn reads(&self) -> u64 {
        self.reads.load(Ordering::SeqCst)
    }
}

impl Clock for FakeClock {
    fn now(&mut self) -> u64 {
        self.reads.fetch_add(1, Ordering::SeqCst);
        self.now.load(Ordering::SeqCst)
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(self.clone())
    }
}

/// A clock that advances by one nanosecond at every reading, from 1.
#[derive(Clone, Default)]
struct TickingClock {
    reads: Arc<AtomicU64>,
}

impl Clock for TickingClock {
    fn now(&mut self) -> u64 {
        self.reads.fetch_add(1, Ordering::SeqCst) + 1
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(self.clone())
    }
}

/// A probe that counts its polls and reports cancellation from the poll
/// after the first `cancel_after` polls on, as a flag set between two polls
/// does.
#[derive(Clone)]
struct CountingProbe {
    polls: Arc<AtomicU64>,
    cancel_after: u64,
}

impl CountingProbe {
    fn after(cancel_after: u64) -> Self {
        Self {
            polls: Arc::new(AtomicU64::new(0)),
            cancel_after,
        }
    }

    fn never() -> Self {
        Self::after(u64::MAX)
    }

    fn polls(&self) -> u64 {
        self.polls.load(Ordering::SeqCst)
    }
}

impl CancelProbe for CountingProbe {
    fn is_cancelled(&mut self) -> bool {
        let poll = self.polls.fetch_add(1, Ordering::SeqCst) + 1;
        poll > self.cancel_after
    }

    fn fork(&self) -> Box<dyn CancelProbe> {
        Box::new(self.clone())
    }
}

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

fn observed(limits: Limits, clock: impl Clock + 'static, probe: &CountingProbe) -> Context {
    Context::with_observers(limits, Box::new(clock), Box::new(probe.clone()))
}

/// Limits raised far beyond every request of these tests, for reading
/// answers and for writing the lines of large results.
fn wide() -> Limits {
    Limits::new()
        .with_max_work(u64::MAX)
        .with_max_depth(1 << 20)
        .with_max_nodes(1 << 40)
        .with_max_storage_bytes(1 << 40)
        .with_max_output_bytes(u64::MAX)
        .with_max_exponent(1 << 20)
        .with_max_integer_bits(1 << 20)
}

/// The outcome of `request` under `limits`, with the context it charged.
fn run(request: &Request, limits: Limits) -> (Outcome, Context) {
    let mut c = context(limits);
    let outcome = execute(request, &mut c);
    (outcome, c)
}

/// The term of the outcome, which must be a value.
fn value(outcome: &Outcome) -> &Term {
    match outcome.result() {
        Ok(Settled::Value(term)) => term,
        other => panic!("not a value: {other:?}"),
    }
}

/// The error of the outcome, which must be an error.
fn error(outcome: &Outcome) -> &Error {
    match outcome.result() {
        Err(error) => error,
        Ok(settled) => panic!("not an error: {settled:?}"),
    }
}

/// Whether `term` is the term of `source`, read under wide limits.
fn is(term: &Term, source: &str) -> bool {
    let c = &mut context(wide());
    let expected = parse(source, c).expect(source);
    term.equals(&expected, c).unwrap()
}

/// The line of `outcome`, written under wide limits, as text.
fn line(outcome: &Outcome) -> String {
    let c = &mut context(wide());
    let bytes = serialize(outcome, c).unwrap();
    assert_eq!(
        c.output_used(),
        bytes.len() as u64,
        "every byte is charged once"
    );
    String::from_utf8(bytes).expect("a line is UTF-8")
}

/// The fields of a line, without its line feed.
fn fields(line: &str) -> Vec<&str> {
    line.strip_suffix('\n')
        .expect("a line ends with a line feed")
        .split('\t')
        .collect()
}

fn assert_fault(error: &Error, fault: FaultKind, span: Option<Span>) {
    assert_eq!(error.kind(), ErrorKind::Fault(fault), "{error}");
    assert_eq!(error.span(), span, "{error}");
}

fn assert_limit(error: &Error, field: LimitField) {
    assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{error}");
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(field),
        "{error}"
    );
}

// ---------------------------------------------------------------------------
// The three operations

// `eval` gives the exact number of its input, as a term.
#[test]
fn eval_gives_the_exact_number_of_the_input() {
    for (input, answer) in [
        ("1/3 + 1/6", "1/2"),
        ("0.1 + 0.2", "3/10"),
        ("-2^2 + 2^3^2", "508"),
        ("(2/3)^(-5)", "243/32"),
        (
            "18446744073709551616^2",
            "340282366920938463463374607431768211456",
        ),
    ] {
        let (outcome, _) = run(&Request::new("eval", "x", input), Limits::new());
        assert!(is(value(&outcome), answer), "{input}");
        assert_eq!(line(&outcome), format!("value\t0\t0\t0\t{answer}\n"));
    }
}

// `expand` gives the polynomial of its input in the variable, converted back
// to a term.
#[test]
fn expand_gives_the_polynomial_of_the_input_as_a_term() {
    let request = Request::new("expand", "x", "(x+1)^5");
    let (outcome, _) = run(&request, Limits::new());
    assert!(is(
        value(&outcome),
        "x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1"
    ));
    assert_eq!(
        line(&outcome),
        "value\t0\t0\t0\t1 + 5*x + 10*x^2 + 10*x^3 + 5*x^4 + x^5\n"
    );
    let request = Request::new("expand", "t", "(t-1)*(t+1) - t^2");
    let (outcome, _) = run(&request, Limits::new());
    assert!(is(value(&outcome), "-1"));
}

// `diff` gives the derivative by the variable of the polynomial of its
// input.
#[test]
fn diff_gives_the_derivative_by_the_variable() {
    let request = Request::new("diff", "t", "(t^3-2*t)/3");
    let (outcome, _) = run(&request, Limits::new());
    assert!(is(value(&outcome), "t^2 - 2/3"));
    assert_eq!(line(&outcome), "value\t0\t0\t0\t-2/3 + t^2\n");
    let request = Request::new("diff", "x", "7");
    let (outcome, _) = run(&request, Limits::new());
    assert!(is(value(&outcome), "0"));
}

// ---------------------------------------------------------------------------
// Rejected requests

// An operation that the dispatch table does not hold fails with
// `Unsupported`, without a span, before any work: names are compared byte
// for byte.
#[test]
fn an_unknown_operation_is_unsupported_before_any_work() {
    for name in [
        "simplify",
        "",
        "EVAL",
        "Expand",
        "eval ",
        " diff",
        "diff\n",
        "integrate",
        "évaluer",
    ] {
        let request = Request::new(name, "x", "x + 1");
        let (outcome, c) = run(&request, Limits::new());
        assert_fault(error(&outcome), FaultKind::Unsupported, None);
        assert_eq!(c.work_used(), 0, "{name:?}");
        let text = line(&outcome);
        assert_eq!(
            fields(&text)[..10].join(" "),
            "error 0 0 0 Unsupported - - - - -"
        );
    }
}

// A missing operand, an input that is empty or holds only whitespace, fails
// with `Syntax` and the empty span at the end of the input, for every
// operation.
#[test]
fn a_missing_operand_is_a_syntax_error_at_the_end_of_the_input() {
    for operation in OPERATIONS {
        for input in ["", " ", "\t", "\n\r\u{c} \t"] {
            let (outcome, _) = run(&Request::new(operation, "x", input), Limits::new());
            let end = input.len();
            assert_fault(error(&outcome), FaultKind::Syntax, Span::new(end, end));
            let text = line(&outcome);
            let span = format!("{end}..{end}");
            assert_eq!(fields(&text)[4..6], ["Syntax", span.as_str()]);
        }
    }
}

// The earlier implementation read a request line whose command word had no
// operand, such as `eval`, as an expression: the command fell back to
// simplification of the word itself, which succeeded with the symbol `eval`.
// Here the operation and its operand are separate fields of the request, an
// operation without an operand fails with `Syntax` and never gives a value,
// and an unknown operation never falls back to another operation.
#[test]
fn an_operation_without_an_operand_never_falls_back_to_a_result() {
    for operation in OPERATIONS {
        let (outcome, _) = run(&Request::new(operation, "x", ""), Limits::new());
        assert_fault(error(&outcome), FaultKind::Syntax, Span::new(0, 0));
        // Every field but the message: a syntax error at the start of the
        // empty input, so the operation did not become an operand.
        let text = line(&outcome);
        assert_eq!(
            fields(&text)[..10].join("\t"),
            "error\t0\t0\t0\tSyntax\t0..0\t-\t-\t-\t-"
        );
    }
    for (operation, input) in [("simplify", "eval"), ("", "expand"), ("eval x", "")] {
        let (outcome, _) = run(&Request::new(operation, "x", input), Limits::new());
        assert_fault(error(&outcome), FaultKind::Unsupported, None);
    }
}

// Settings other than the default fail with `Unsupported`. The settings of
// this release have no field, so code outside the library can build only the
// default, as the `compile_fail` documentation test of `Settings` shows, and
// the default is accepted for every operation, with any settings version;
// the rejection itself is tested in `src/command/tests.rs` with a settings
// record that has a field.
#[test]
fn the_default_settings_are_the_only_settings_and_are_accepted() {
    assert_eq!(Settings::new(), Settings::default());
    assert_eq!(Request::new("eval", "x", "1").settings, Settings::new());
    for operation in OPERATIONS {
        for settings in [Settings::new(), Settings::default()] {
            let request = Request::new(operation, "x", "x^2")
                .with_settings(settings)
                .with_settings_version(u64::MAX);
            let (outcome, _) = run(&request, Limits::new());
            assert_eq!(outcome.settings_version(), u64::MAX);
            if operation == "eval" {
                assert_fault(error(&outcome), FaultKind::UnknownSymbol, None);
            } else {
                value(&outcome);
            }
        }
    }
}

// The variable of `expand` and `diff` follows the rule of symbol names: a
// malformed name fails with `Syntax` and a reserved name with `Unsupported`,
// without a span, since a span points into the input, and before the input
// is read or anything is charged. `eval` does not read the variable.
#[test]
fn the_variable_of_expand_and_diff_follows_the_rule_of_symbol_names() {
    for operation in ["expand", "diff"] {
        for (variable, fault) in [
            ("", FaultKind::Syntax),
            ("1x", FaultKind::Syntax),
            ("x y", FaultKind::Syntax),
            ("x-1", FaultKind::Syntax),
            ("é", FaultKind::Syntax),
            ("pi", FaultKind::Unsupported),
            ("i", FaultKind::Unsupported),
            ("undefined", FaultKind::Unsupported),
        ] {
            // The input is missing as well; the variable comes first.
            let (outcome, c) = run(&Request::new(operation, variable, ""), Limits::new());
            assert_fault(error(&outcome), fault, None);
            assert_eq!(c.work_used(), 0, "{variable:?}");
        }
    }
    for variable in ["", "1x", "pi"] {
        let (outcome, _) = run(&Request::new("eval", variable, "2"), Limits::new());
        assert!(is(value(&outcome), "2"));
    }
}

// The charge of the variable, one unit and one per byte of the name, is a
// request failure when it does not fit the work, and stays one: a
// `ResourceLimit` naming `max_work`, without a span, with nothing charged.
#[test]
fn the_charge_of_the_variable_fails_as_a_resource_limit() {
    for operation in ["expand", "diff"] {
        let (outcome, c) = run(
            &Request::new(operation, "x", "1"),
            Limits::new().with_max_work(1),
        );
        let e = error(&outcome);
        assert_limit(e, LimitField::Work);
        assert_eq!(e.exceeded().unwrap().amount(), LimitAmount::Required(2));
        assert_eq!(e.span(), None);
        assert_eq!(c.work_used(), 0);
    }
}

// `eval` reads the canonical term of its input: a number is its value, and a
// term that is not a number holds a symbol, which has no value, so it fails
// with `UnknownSymbol`, without a span. `x - x` and `0*x` are the number 0,
// while `x/x` keeps its witness of $x^{-1}$ and a power of a sum is not
// expanded.
#[test]
fn eval_of_a_term_with_a_symbol_is_an_unknown_symbol() {
    for input in [
        "x",
        "x + 1",
        "x/x",
        "0*x^(-1)",
        "2*y",
        "(x+1)^2 - x^2 - 2*x - 1",
    ] {
        let (outcome, _) = run(&Request::new("eval", "x", input), Limits::new());
        assert_fault(error(&outcome), FaultKind::UnknownSymbol, None);
    }
    for input in ["x - x", "0*x", "(x - x)^0"] {
        let (outcome, _) = run(&Request::new("eval", "x", input), Limits::new());
        assert!(
            is(
                value(&outcome),
                if input == "(x - x)^0" { "1" } else { "0" }
            ),
            "{input}"
        );
    }
}

// Names are case-sensitive: `X` is not the variable `x`.
#[test]
fn names_are_case_sensitive() {
    let (outcome, _) = run(&Request::new("expand", "x", "X + 1"), Limits::new());
    assert_fault(error(&outcome), FaultKind::UnknownSymbol, None);
    let (outcome, _) = run(&Request::new("expand", "X", "x"), Limits::new());
    assert_fault(error(&outcome), FaultKind::UnknownSymbol, None);
    let (outcome, _) = run(&Request::new("diff", "X", "X^2"), Limits::new());
    assert!(is(value(&outcome), "2*X"));
}

// One context accumulates the work of every step of a request: the work of
// `expand` is the sum of the work of the ring, the parser, the expansion and
// the conversion back to a term, each run on a context of its own, and
// writing the line on the same context adds the work of the line.
#[test]
fn one_context_accumulates_the_work_of_every_step() {
    let request = Request::new("expand", "x", "(x/2 + 1)^3 - x");
    let (outcome, mut c) = run(&request, Limits::new());
    let mut steps = Vec::new();
    let step = &mut context(Limits::new());
    let ring = PolynomialRing::new(Rationals, "x", step).unwrap();
    steps.push(step.work_used());
    let step = &mut context(Limits::new());
    let term = parse(&request.input, step).unwrap();
    steps.push(step.work_used());
    let step = &mut context(Limits::new());
    let polynomial = ring.expand(&term, step).unwrap();
    steps.push(step.work_used());
    let step = &mut context(Limits::new());
    let back = ring.to_term(&polynomial, step).unwrap();
    steps.push(step.work_used());
    assert!(back.equals(value(&outcome), step).unwrap());
    assert!(steps.iter().all(|work| *work > 0), "{steps:?}");
    assert_eq!(c.work_used(), steps.iter().sum::<u64>());
    let alone = &mut context(Limits::new());
    serialize(&outcome, alone).unwrap();
    let before = c.work_used();
    serialize(&outcome, &mut c).unwrap();
    assert_eq!(c.work_used(), before + alone.work_used());
}

// A sum of 2,000 quotients $x/3$ expands to one monomial.
#[test]
fn a_sum_of_two_thousand_quotients_expands_to_one_monomial() {
    let input = vec!["x/3"; 2_000].join("+");
    let (outcome, _) = run(&Request::new("expand", "x", &input), wide());
    assert!(is(value(&outcome), "2000/3*x"));
    assert_eq!(line(&outcome), "value\t0\t0\t0\t2000/3*x\n");
}

// ---------------------------------------------------------------------------
// Versions

// The outcome echoes the three versions of its request, for a value, a
// fault, a rejected request and a request failure, and its line writes them
// after its first field.
#[test]
fn the_outcome_echoes_the_versions_of_its_request() {
    for (input_version, context_version, settings_version) in
        [(7, 11, 13), (u64::MAX, 0, u64::MAX), (0, u64::MAX, 1)]
    {
        let flag = CancelFlag::new();
        flag.cancel();
        let requests = [
            (
                Request::new("eval", "x", "1/3 + 1/6"),
                Context::new(Limits::new(), CancelFlag::new()),
            ),
            (
                Request::new("eval", "x", "1/0"),
                Context::new(Limits::new(), CancelFlag::new()),
            ),
            (
                Request::new("simplify", "x", "1"),
                Context::new(Limits::new(), CancelFlag::new()),
            ),
            (
                Request::new("diff", "x", "x^2"),
                Context::new(Limits::new(), flag),
            ),
        ];
        for (index, (request, mut c)) in requests.into_iter().enumerate() {
            let request = request
                .with_input_version(input_version)
                .with_context_version(context_version)
                .with_settings_version(settings_version);
            let outcome = execute(&request, &mut c);
            assert_eq!(
                (
                    outcome.input_version(),
                    outcome.context_version(),
                    outcome.settings_version()
                ),
                (input_version, context_version, settings_version)
            );
            let text = line(&outcome);
            let versions = [
                input_version.to_string(),
                context_version.to_string(),
                settings_version.to_string(),
            ];
            assert_eq!(fields(&text)[1..4], versions, "{text:?}");
            let kind = match outcome.into_result() {
                Ok(Settled::Value(_)) => "value",
                Err(error) => match error.kind() {
                    ErrorKind::Cancelled => "Cancelled",
                    ErrorKind::Fault(FaultKind::DivisionByZero) => "DivisionByZero",
                    ErrorKind::Fault(FaultKind::Unsupported) => "Unsupported",
                    other => panic!("unexpected kind {other:?}"),
                },
                Ok(other) => panic!("unexpected {other:?}"),
            };
            assert_eq!(
                kind,
                ["value", "DivisionByZero", "Unsupported", "Cancelled"][index]
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The lines

// Error lines carry the kind, the span into the input, the limit with its
// scope, the allowed value and the amount.
#[test]
fn error_lines_carry_the_kind_the_span_and_the_limit() {
    let exponent = Limits::new().with_max_exponent(256);
    let bits = Limits::new().with_max_integer_bits(4096);
    let nodes = Limits::new().with_max_nodes(12);
    for (request, limits, expected) in [
        (
            Request::new("eval", "x", "0*(1/0)"),
            Limits::new(),
            ["DivisionByZero", "3..6", "-", "-", "-", "-"],
        ),
        (
            Request::new("eval", "x", "2^(1/2)"),
            Limits::new(),
            ["NonIntegerExponent", "2..7", "-", "-", "-", "-"],
        ),
        (
            Request::new("eval", "x", "1.2.3"),
            Limits::new(),
            ["Syntax", "3..4", "-", "-", "-", "-"],
        ),
        (
            Request::new("eval", "x", "sin(x)"),
            Limits::new(),
            ["Unsupported", "0..4", "-", "-", "-", "-"],
        ),
        (
            Request::new("expand", "x", "x^257"),
            exponent,
            [
                "ResourceLimit",
                "2..5",
                "Field(max_exponent)",
                "-",
                "256",
                "Required(257)",
            ],
        ),
        (
            Request::new("eval", "x", "2^4096"),
            bits,
            [
                "ResourceLimit",
                "0..6",
                "Field(max_integer_bits)",
                "-",
                "4096",
                "Required(4097)",
            ],
        ),
        (
            Request::new("expand", "x", "(x+1)^5"),
            nodes,
            [
                "ResourceLimit",
                "-",
                "Field(max_nodes)",
                "Value",
                "12",
                "Required(17)",
            ],
        ),
        (
            Request::new("expand", "x", "x + y"),
            Limits::new(),
            ["UnknownSymbol", "-", "-", "-", "-", "-"],
        ),
        (
            Request::new("expand", "x", "(x^2-1)/(x-1)"),
            Limits::new(),
            ["NotPolynomial", "-", "-", "-", "-", "-"],
        ),
    ] {
        let (outcome, _) = run(&request, limits);
        let text = line(&outcome);
        let found = fields(&text);
        assert_eq!(found.len(), 11, "{text:?}");
        assert_eq!(found[4..10], expected, "{}: {text:?}", request.input);
        let error = error(&outcome);
        assert_eq!(found[10], escaped(error.message()));
    }
}

/// The escaping of the format: a backslash, a tab, a line feed and a
/// carriage return by their letters, every other control character as
/// `\xhh`.
fn escaped(text: &str) -> String {
    let mut escaped = String::new();
    for character in text.chars() {
        match character {
            '\\' => escaped.push_str("\\\\"),
            '\t' => escaped.push_str("\\t"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\u{0}'..='\u{1f}' | '\u{7f}' => {
                escaped.push_str(&format!("\\x{:02x}", u32::from(character)));
            }
            other => escaped.push(other),
        }
    }
    escaped
}

// A line that does not fit `max_output_bytes` fails with `ResourceLimit`
// naming that field and returns no bytes; the same line fits exactly its own
// length. The output charged never exceeds the limit.
#[test]
fn a_line_over_max_output_bytes_fails_with_a_resource_limit_and_no_output() {
    for request in [
        Request::new("expand", "x", "(x+1)^5"),
        Request::new("eval", "x", "1/0"),
    ] {
        let (outcome, _) = run(&request, Limits::new());
        let full = line(&outcome);
        let length = full.len() as u64;
        let c = &mut context(Limits::new().with_max_output_bytes(length));
        assert_eq!(serialize(&outcome, c).unwrap(), full.as_bytes());
        assert_eq!(c.output_used(), length);
        for allowed in [length - 1, length / 2, 0] {
            let c = &mut context(Limits::new().with_max_output_bytes(allowed));
            let error = serialize(&outcome, c).unwrap_err();
            assert_limit(&error, LimitField::OutputBytes);
            let exceeded = error.exceeded().unwrap();
            assert_eq!(exceeded.scope(), None);
            assert_eq!(exceeded.allowed(), allowed);
            assert!(c.output_used() <= allowed);
            let LimitAmount::Required(needed) = exceeded.amount() else {
                panic!("the output needed is exact: {exceeded:?}");
            };
            assert!(needed > allowed && needed <= length);
        }
        // A line also fails under too little work, and leaves no output.
        let c = &mut context(Limits::new().with_max_work(length / 2));
        assert_limit(&serialize(&outcome, c).unwrap_err(), LimitField::Work);
    }
}

/// Asserts that `text`, the line of `outcome`, has the documented shape: a
/// value has 5 fields and an error 11, the line ends with its only line
/// feed and holds no other control character than the tabs between its
/// fields, its versions are decimal numbers, the text of a value reads back
/// as its term, and the fields of an error are those of the error.
fn assert_shape(text: &str, outcome: &Outcome) {
    let found = fields(text);
    let control = text
        .bytes()
        .filter(|byte| (*byte < 0x20 && *byte != b'\t') || *byte == 0x7f)
        .count();
    assert_eq!(control, 1, "only the line feed: {text:?}");
    for version in &found[1..4] {
        assert!(
            version == &"0" || (!version.starts_with('0') && version.parse::<u64>().is_ok()),
            "{text:?}"
        );
    }
    match outcome.result() {
        Ok(Settled::Value(term)) => {
            assert_eq!((found[0], found.len()), ("value", 5), "{text:?}");
            let c = &mut context(wide());
            let read = parse(found[4], c).expect(found[4]);
            assert!(read.equals(term, c).unwrap(), "{text:?}");
        }
        Ok(other) => panic!("no operation of this release ends in a state: {other:?}"),
        Err(error) => {
            assert_eq!((found[0], found.len()), ("error", 11), "{text:?}");
            let span = match error.span() {
                Some(span) => format!("{}..{}", span.start(), span.end()),
                None => "-".to_owned(),
            };
            assert_eq!(found[5], span);
            match error.exceeded() {
                Some(exceeded) => {
                    let id = match exceeded.id() {
                        LimitId::Field(field) => format!("Field({})", field.name()),
                        other => panic!("no request parameter in this release: {other:?}"),
                    };
                    let scope = match exceeded.scope() {
                        Some(LimitScope::Value) => "Value",
                        Some(LimitScope::Frame) => "Frame",
                        Some(LimitScope::Temporary) => "Temporary",
                        None => "-",
                        Some(other) => panic!("unexpected scope {other:?}"),
                    };
                    let amount = match exceeded.amount() {
                        LimitAmount::Used(n) => format!("Used({n})"),
                        LimitAmount::Required(n) => format!("Required({n})"),
                        LimitAmount::Bound(n) => format!("Bound({n})"),
                        other => panic!("unexpected amount {other:?}"),
                    };
                    let allowed = exceeded.allowed().to_string();
                    assert_eq!(found[4], "ResourceLimit");
                    assert_eq!(
                        found[6..10],
                        [id.as_str(), scope, allowed.as_str(), amount.as_str()]
                    );
                }
                None => assert_eq!(found[6..10], ["-", "-", "-", "-"], "{text:?}"),
            }
            assert_eq!(found[10], escaped(error.message()));
        }
    }
}

// ---------------------------------------------------------------------------
// Determinism of lines: a property test

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

/// The cases of the property.
const CASES: u64 = 1_000;

const DETERMINISM_SEED: u64 = 0x5EED_0000_0000_0201;

/// A random expression of the grammar, with symbols, numbers, every
/// operator and parentheses, and now and then a fault: a division by zero,
/// an exponent that is not an integer or a stray character.
fn expression(random: &mut SplitMix64, depth: u32) -> String {
    if depth == 0 || random.below(4) == 0 {
        return random
            .pick(&[
                "x", "t", "y", "X", "1", "2", "3", "1/2", "0.5", "12", "0", "x_1",
            ])
            .to_owned();
    }
    let left = expression(random, depth - 1);
    match random.below(9) {
        0 => format!("-{left}"),
        1 => format!("({left})"),
        2 => format!("{left}^{}", random.pick(&["2", "3", "0", "(-1)", "5"])),
        3 => format!("{left}^{}", random.pick(&["x", "(1/2)", "300"])),
        4 => format!("{left}/{}", random.pick(&["0", "2", "(x-x)", "x"])),
        5 => format!("{left} {}", random.pick(&["2", "$", "y"])),
        _ => {
            let operator = random.pick(&[" + ", "-", "*", " - ", "+"]);
            format!("{left}{operator}{}", expression(random, depth - 1))
        }
    }
}

/// A request of the property: an operation, mostly of the table, a variable,
/// mostly valid, an input and random versions.
fn random_request(random: &mut SplitMix64) -> Request {
    let operation = random.pick(&[
        "eval", "expand", "diff", "eval", "expand", "diff", "simplify",
    ]);
    let variable = random.pick(&["x", "x", "t", "X", "", "pi"]);
    let input = match random.below(20) {
        0 => String::new(),
        1 => "  ".to_owned(),
        _ => expression(random, 4),
    };
    let version = |random: &mut SplitMix64| match random.below(3) {
        0 => 0,
        1 => random.below(1_000),
        _ => random.next(),
    };
    Request::new(operation, variable, &input)
        .with_input_version(version(random))
        .with_context_version(version(random))
        .with_settings_version(version(random))
}

/// The limits of a case: the defaults, or the defaults with one small field.
fn random_limits(random: &mut SplitMix64) -> Limits {
    match random.below(8) {
        0 => Limits::new().with_max_work(random.below(400)),
        1 => Limits::new().with_max_nodes(random.below(30)),
        2 => Limits::new().with_max_storage_bytes(random.below(200)),
        3 => Limits::new().with_max_exponent(random.below(6)),
        4 => Limits::new().with_max_integer_bits(random.below(12)),
        5 => Limits::new().with_max_depth(random.below(6)),
        _ => Limits::new(),
    }
}

// The same outcome is written as the same bytes: written twice, written
// from a clone, which shares its nodes, and written from the outcome of the
// same request run again in a fresh context, which builds its own nodes;
// under contexts with and without a deadline, on clocks at different
// readings. Each writing charges exactly its bytes as output and the same
// work, and every line has the documented shape. 1,000 cases from a fixed
// seed; every kind of line and the main kinds of error occur.
#[test]
fn the_same_outcome_is_written_as_the_same_bytes() {
    let mut random = SplitMix64(DETERMINISM_SEED);
    let mut kinds = std::collections::BTreeSet::new();
    for index in 0..CASES {
        let request = random_request(&mut random);
        let limits = random_limits(&mut random);
        let (first, first_context) = run(&request, limits);
        let (again, again_context) = run(&request, limits);
        assert_eq!(
            first_context.work_used(),
            again_context.work_used(),
            "case {index}: {request:?}"
        );
        let clone = first.clone();
        let mut lines = Vec::new();
        let mut works = Vec::new();
        for (outcome, clock) in [
            (&first, None),
            (&first, Some(0)),
            (&clone, Some(1_000_000_000)),
            (&again, None),
        ] {
            let probe = CountingProbe::never();
            let c = &mut match clock {
                None => observed(wide(), FakeClock::at(0), &probe),
                Some(now) => observed(wide(), FakeClock::at(now), &probe).with_deadline(u64::MAX),
            };
            let bytes = serialize(outcome, c).unwrap();
            assert_eq!(c.output_used(), bytes.len() as u64);
            works.push(c.work_used());
            lines.push(bytes);
        }
        assert!(
            lines.windows(2).all(|pair| pair[0] == pair[1]),
            "case {index}: {request:?}"
        );
        assert!(works.windows(2).all(|pair| pair[0] == pair[1]));
        let text = String::from_utf8(lines.swap_remove(0)).unwrap();
        assert_shape(&text, &first);
        let found = fields(&text);
        kinds.insert(if found[0] == "error" {
            found[4].to_owned()
        } else {
            found[0].to_owned()
        });
    }
    for kind in [
        "value",
        "Syntax",
        "Unsupported",
        "UnknownSymbol",
        "NotPolynomial",
        "DivisionByZero",
        "NonIntegerExponent",
        "ResourceLimit",
    ] {
        assert!(kinds.contains(kind), "no {kind} among {kinds:?}");
    }
}

// ---------------------------------------------------------------------------
// The deadline and cancellation

// Cancellation is observed at the next charge point: when the probe reports
// cancellation from its poll k + 1 on, the request ends with `Cancelled` at
// that very poll, for every k before the end of the request, and the outcome
// still echoes the versions; writing a line ends in the same way and returns
// no bytes.
#[test]
fn cancellation_is_observed_at_the_next_charge_point() {
    let request = Request::new("diff", "x", "(x+1)^3 - x").with_input_version(9);
    let probe = CountingProbe::never();
    let c = &mut observed(Limits::new(), FakeClock::at(0), &probe);
    let outcome = execute(&request, c);
    value(&outcome);
    let polls = probe.polls();
    assert!(polls > 10, "{polls}");
    for k in 0..polls {
        let probe = CountingProbe::after(k);
        let c = &mut observed(Limits::new(), FakeClock::at(0), &probe);
        let cancelled = execute(&request, c);
        assert_eq!(error(&cancelled).kind(), ErrorKind::Cancelled, "poll {k}");
        assert_eq!(probe.polls(), k + 1, "observed at the next charge point");
        assert_eq!(cancelled.input_version(), 9);
    }
    let probe = CountingProbe::never();
    let c = &mut observed(Limits::new(), FakeClock::at(0), &probe);
    let bytes = serialize(&outcome, c).unwrap();
    let polls = probe.polls();
    assert!(polls >= 6, "a poll at every field: {polls}");
    // An error line has eleven fields and a line feed, each its own charge
    // point.
    let (failed, _) = run(&Request::new("eval", "x", "1/0"), Limits::new());
    let counted = CountingProbe::never();
    serialize(
        &failed,
        &mut observed(Limits::new(), FakeClock::at(0), &counted),
    )
    .unwrap();
    assert_eq!(
        counted.polls(),
        12,
        "a poll at every field and the line feed"
    );
    for k in 0..polls {
        let probe = CountingProbe::after(k);
        let c = &mut observed(Limits::new(), FakeClock::at(0), &probe);
        let error = serialize(&outcome, c).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Cancelled, "poll {k}");
        assert_eq!(probe.polls(), k + 1);
        assert!(c.output_used() < bytes.len() as u64);
    }
}

/// The line that a host publishes for `outcome` by the fallback step of the
/// contract, and the errors of its request. The line is written under `own`,
/// the context of the request; when that fails and the outcome is an error,
/// of any kind, it is written again under a fresh context, with a fresh flag
/// and no deadline. A value or a state is never written again. The errors are
/// the error of the outcome and the error of `serialize` under `own`.
fn publish(outcome: &Outcome, own: &mut Context) -> (Option<Vec<u8>>, Vec<ErrorKind>) {
    let mut errors = Vec::new();
    if let Err(e) = outcome.result() {
        errors.push(e.kind());
    }
    let line = match serialize(outcome, own) {
        Ok(bytes) => Some(bytes),
        Err(e) => {
            errors.push(e.kind());
            match outcome.result() {
                Err(_) => {
                    let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
                    Some(serialize(outcome, fresh).expect("an error line fits a fresh context"))
                }
                Ok(_) => None,
            }
        }
    };
    (line, errors)
}

/// Asserts that `outcome` has no line under `own`, the context of its
/// request, failing there with `kind`, and that the host publishes its line
/// under a fresh context: the bytes of its line under wide limits.
fn assert_fallback_line(outcome: &Outcome, own: &mut Context, kind: ErrorKind) -> String {
    let full = line(outcome);
    let output = own.output_used();
    let (published, errors) = publish(outcome, own);
    assert!(own.output_used() < output + full.len() as u64);
    assert_eq!(errors, [error(outcome).kind(), kind], "{full:?}");
    assert_eq!(published.unwrap(), full.as_bytes());
    full
}

// The outcome of a request that ended with `Cancelled` or `DeadlineExceeded`
// never has a line under the request's own context: `serialize` polls the
// same probe, which keeps reporting the cancellation, and observes the same
// expiry, which is final, so it fails with the same error. The host publishes
// the line that it writes under a fresh context, with a fresh flag and no
// deadline.
#[test]
fn cancelled_and_expired_outcomes_have_no_line_under_their_own_context() {
    let flag = CancelFlag::new();
    flag.cancel();
    let c = &mut Context::new(Limits::new(), flag);
    let outcome = execute(&Request::new("eval", "x", "1"), c);
    assert_eq!(error(&outcome).kind(), ErrorKind::Cancelled);
    let text = assert_fallback_line(&outcome, c, ErrorKind::Cancelled);
    assert_eq!(fields(&text)[4], "Cancelled");
    assert_eq!(c.output_used(), 0);

    let probe = CountingProbe::never();
    let clock = FakeClock::at(0);
    let c = &mut observed(Limits::new(), clock.clone(), &probe).with_deadline(10);
    clock.set(10);
    let outcome = execute(
        &Request::new("expand", "x", "(x+1)^5").with_input_version(4),
        c,
    );
    assert_eq!(error(&outcome).kind(), ErrorKind::DeadlineExceeded);
    let text = assert_fallback_line(&outcome, c, ErrorKind::DeadlineExceeded);
    assert_eq!(
        fields(&text)[..5],
        ["error", "4", "0", "0", "DeadlineExceeded"]
    );
    assert_eq!(c.output_used(), 0);
}

// Any other outcome has no line under the request's own context when the
// work or the output that the request has left is less than its line needs.
// The outcomes of `expand` of `(x+1)^5` that exhaust `max_work` below 400
// have too little work left; so has the fault of `eval` of `0*(1/0)` under
// `max_work = 24`, which charged all 24 units before its division by zero.
// The host publishes the line of each under a fresh context.
#[test]
fn an_outcome_has_no_line_under_its_own_context_when_too_little_is_left() {
    let mut exhausted = 0;
    for max_work in 1..400 {
        let (outcome, mut c) = run(
            &Request::new("expand", "x", "(x+1)^5"),
            Limits::new().with_max_work(max_work),
        );
        let Err(e) = outcome.result() else {
            continue;
        };
        assert_limit(e, LimitField::Work);
        assert_limit(&serialize(&outcome, &mut c).unwrap_err(), LimitField::Work);
        let (outcome, mut c) = run(
            &Request::new("expand", "x", "(x+1)^5"),
            Limits::new().with_max_work(max_work),
        );
        let text = assert_fallback_line(&outcome, &mut c, ErrorKind::ResourceLimit);
        assert_eq!(fields(&text)[6], "Field(max_work)");
        exhausted += 1;
    }
    assert!(exhausted > 100, "{exhausted}");

    let (outcome, mut c) = run(
        &Request::new("eval", "x", "0*(1/0)"),
        Limits::new().with_max_work(24),
    );
    assert_fault(error(&outcome), FaultKind::DivisionByZero, Span::new(3, 6));
    assert_eq!(c.work_used(), 24);
    let (outcome_again, mut again) = run(
        &Request::new("eval", "x", "0*(1/0)"),
        Limits::new().with_max_work(24),
    );
    assert_limit(
        &serialize(&outcome_again, &mut again).unwrap_err(),
        LimitField::Work,
    );
    let text = assert_fallback_line(&outcome, &mut c, ErrorKind::ResourceLimit);
    assert_eq!(fields(&text)[4..6], ["DivisionByZero", "3..6"]);

    // A line over the output left fails as well, and falls back.
    let (outcome, _) = run(&Request::new("eval", "x", "1/0"), Limits::new());
    let c = &mut context(Limits::new().with_max_output_bytes(10));
    assert_fallback_line(&outcome, c, ErrorKind::ResourceLimit);
}

// A failed charge does not change the work charged so far, so an outcome of
// `ResourceLimit` on `max_work` has its line under its own context when the
// work left is enough: `diff` in a variable of 300 letters `a` needs 301
// units for the variable, fails under `max_work = 200` with nothing charged,
// and its line of 98 bytes is written under the context of the request.
#[test]
fn an_exhausted_max_work_has_its_line_when_the_work_left_is_enough() {
    let variable = "a".repeat(300);
    let (outcome, mut c) = run(
        &Request::new("diff", &variable, "x"),
        Limits::new().with_max_work(200),
    );
    let e = error(&outcome);
    assert_limit(e, LimitField::Work);
    let exceeded = e.exceeded().unwrap();
    assert_eq!(
        (exceeded.allowed(), exceeded.amount()),
        (200, LimitAmount::Required(301))
    );
    assert_eq!(c.work_used(), 0);
    let full = line(&outcome);
    assert_eq!(full.len(), 98);
    assert_eq!(
        fields(&full)[..10].join("\t"),
        "error\t0\t0\t0\tResourceLimit\t-\tField(max_work)\t-\t200\tRequired(301)"
    );
    let (published, errors) = publish(&outcome, &mut c);
    assert_eq!(published.unwrap(), full.as_bytes());
    assert_eq!(errors, [ErrorKind::ResourceLimit]);
    assert_eq!((c.work_used(), c.output_used()), (98, 98));
}

// The fallback step rewrites only errors: a value whose line does not fit
// the output or the integer bits of its request has no line, since its line
// under another context would escape those limits, and the failure of its
// line is an error of the request.
#[test]
fn a_value_is_never_written_again_under_another_context() {
    let (outcome, _) = run(&Request::new("eval", "x", "2^100"), Limits::new());
    for limits in [
        Limits::new().with_max_output_bytes(12),
        Limits::new().with_max_integer_bits(64),
    ] {
        let c = &mut context(limits);
        let (published, errors) = publish(&outcome, c);
        assert_eq!(published, None);
        assert_eq!(errors, [ErrorKind::ResourceLimit]);
    }
}

/// The terminal states of a job of krepi.
#[derive(Debug, PartialEq, Eq)]
enum JobState {
    Completed,
    Failed,
    Cancelled,
    ResourceExhausted,
}

/// A host that runs `requests` as one job, by the rule of the contract for a
/// job of several requests: one `clock` shared by the contexts of all its
/// requests with the deadline `deadline` of the job, cancellation and the
/// deadline checked between two requests, the line of every request that ran
/// published with the fallback step, and one terminal state. `flag` is the
/// cancel request of the job; when `poll` is false the contexts of the
/// requests poll a probe that never reports it, as a worker that does not
/// poll the job service during a request.
fn host_job<C: Clock + Clone + 'static>(
    requests: &[(Request, Limits)],
    clock: &C,
    deadline: u64,
    flag: &CancelFlag,
    poll: bool,
) -> (Vec<Vec<u8>>, JobState) {
    let mut lines = Vec::new();
    let mut failed = false;
    for (request, limits) in requests {
        if flag.is_cancelled() {
            return (lines, JobState::Cancelled);
        }
        if clock.clone().now() >= deadline {
            return (lines, JobState::ResourceExhausted);
        }
        let probe: Box<dyn CancelProbe> = if poll {
            Box::new(flag.clone())
        } else {
            Box::new(CountingProbe::never())
        };
        let mut c = Context::with_observers(*limits, Box::new(clock.clone()), probe)
            .with_deadline(deadline);
        let outcome = execute(request, &mut c);
        let (line, errors) = publish(&outcome, &mut c);
        lines.extend(line);
        let cancelled = errors.contains(&ErrorKind::Cancelled);
        if cancelled || errors.contains(&ErrorKind::DeadlineExceeded) {
            let state = if cancelled || flag.is_cancelled() {
                JobState::Cancelled
            } else {
                JobState::ResourceExhausted
            };
            return (lines, state);
        }
        failed |= !errors.is_empty();
    }
    let state = if failed {
        JobState::Failed
    } else {
        JobState::Completed
    };
    (lines, state)
}

/// A ticking clock that cancels `flag` from its reading `at` on, as a cancel
/// request that arrives during a request.
#[derive(Clone)]
struct CancellingClock {
    ticking: TickingClock,
    flag: CancelFlag,
    at: u64,
}

impl Clock for CancellingClock {
    fn now(&mut self) -> u64 {
        let now = self.ticking.now();
        if now >= self.at {
            self.flag.cancel();
        }
        now
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(self.clone())
    }
}

/// The kinds of the lines `lines`: the first field of a value line, the kind
/// of an error line.
fn kinds(lines: &[Vec<u8>]) -> Vec<String> {
    lines
        .iter()
        .map(|bytes| {
            let text = std::str::from_utf8(bytes).unwrap();
            let found = fields(text);
            if found[0] == "error" {
                found[4]
            } else {
                found[0]
            }
            .to_owned()
        })
        .collect()
}

// A job of several requests publishes the line of every request that ran,
// fallback lines included, and ends in one terminal state. A fault and a
// `ResourceLimit` fail the job without stopping it; cancellation and a passed
// deadline stop it, seen between two requests or reported by a request, and
// the stop decides the terminal state over every earlier fault; a job whose
// cancellation was requested ends cancelled even when a request reported
// `DeadlineExceeded`.
#[test]
fn a_job_of_several_requests_ends_by_the_stop_rule() {
    let eval = |input: &str| (Request::new("eval", "x", input), Limits::new());
    let far = u64::MAX;

    // Values only: completed.
    let flag = CancelFlag::new();
    let (lines, state) = host_job(&[eval("1"), eval("2")], &FakeClock::at(0), far, &flag, true);
    assert_eq!(
        (kinds(&lines), state),
        (vec!["value".into(), "value".into()], JobState::Completed)
    );

    // Faults and request limits, the counterexamples of the fallback step
    // among them, fail the job, and every request runs and has its line.
    let requests = [
        eval("1/0"),
        (
            Request::new("diff", &"a".repeat(300), "x"),
            Limits::new().with_max_work(200),
        ),
        (
            Request::new("eval", "x", "0*(1/0)"),
            Limits::new().with_max_work(24),
        ),
        (
            Request::new("expand", "x", "(x+1)^5"),
            Limits::new().with_max_work(100),
        ),
        eval("1/2"),
    ];
    let (lines, state) = host_job(&requests, &FakeClock::at(0), far, &flag, true);
    assert_eq!(state, JobState::Failed);
    assert_eq!(
        kinds(&lines),
        [
            "DivisionByZero",
            "ResourceLimit",
            "DivisionByZero",
            "ResourceLimit",
            "value"
        ]
    );

    // Cancelled before the job starts: no request runs.
    let cancelled = CancelFlag::new();
    cancelled.cancel();
    let (lines, state) = host_job(&requests, &FakeClock::at(0), far, &cancelled, true);
    assert_eq!((lines.len(), state), (0, JobState::Cancelled));

    // The deadline of the job passes between the first request and the
    // second: the clock reads the deadline at the check before the second.
    let one = TickingClock::default();
    host_job(&[eval("1/3")], &one, far, &flag, true);
    let deadline = one.reads.load(Ordering::SeqCst) + 1;
    let (lines, state) = host_job(
        &[eval("1/3"), eval("1/0")],
        &TickingClock::default(),
        deadline,
        &flag,
        true,
    );
    assert_eq!(
        (kinds(&lines), state),
        (vec!["value".into()], JobState::ResourceExhausted)
    );

    // The deadline passes in the middle of the second request: the job stops
    // there, after the fault of the first, with the fallback line of the
    // second, and the third does not run.
    let one = TickingClock::default();
    host_job(&[eval("1/0")], &one, far, &flag, true);
    let deadline = one.reads.load(Ordering::SeqCst) + 21;
    let requests = [
        eval("1/0"),
        (Request::new("expand", "x", "(x+1)^60"), Limits::new()),
        eval("1"),
    ];
    let (lines, state) = host_job(&requests, &TickingClock::default(), deadline, &flag, true);
    assert_eq!(state, JobState::ResourceExhausted);
    assert_eq!(kinds(&lines), ["DivisionByZero", "DeadlineExceeded"]);

    // The same, with a cancel request that arrives during the second request
    // and that its context does not poll: the job ends cancelled.
    let late = CancelFlag::new();
    let clock = CancellingClock {
        ticking: TickingClock::default(),
        flag: late.clone(),
        at: deadline - 10,
    };
    let (lines, state) = host_job(&requests, &clock, deadline, &late, false);
    assert_eq!(state, JobState::Cancelled);
    assert_eq!(kinds(&lines), ["DivisionByZero", "DeadlineExceeded"]);

    // A cancellation that the context of the second request polls ends it
    // with `Cancelled`, and the job is cancelled.
    let late = CancelFlag::new();
    let clock = CancellingClock {
        ticking: TickingClock::default(),
        flag: late.clone(),
        at: deadline - 10,
    };
    let (lines, state) = host_job(&requests, &clock, far, &late, true);
    assert_eq!(state, JobState::Cancelled);
    assert_eq!(kinds(&lines), ["DivisionByZero", "Cancelled"]);

    // A cancel request that arrives during the first request, which its
    // context does not poll, is seen between the first request and the
    // second: the job stops cancelled, over the fault of the first, with the
    // line of the first only.
    let between = CancelFlag::new();
    let clock = CancellingClock {
        ticking: TickingClock::default(),
        flag: between.clone(),
        at: 2,
    };
    let (lines, state) = host_job(
        &[eval("1/0"), eval("1"), eval("2")],
        &clock,
        far,
        &between,
        false,
    );
    assert_eq!(
        (kinds(&lines), state),
        (vec!["DivisionByZero".into()], JobState::Cancelled)
    );
}

// A request that fails before its first charge point reports that error and
// not the cancellation of its context: an unknown operation, a malformed
// variable and an input over `max_input_bytes`. So a host checks
// cancellation between two requests itself.
#[test]
fn a_request_that_fails_before_its_first_charge_reports_its_own_error() {
    let flag = CancelFlag::new();
    flag.cancel();
    for (request, limits, kind) in [
        (
            Request::new("simplify", "x", "1"),
            Limits::new(),
            ErrorKind::Fault(FaultKind::Unsupported),
        ),
        (
            Request::new("diff", "1x", "x"),
            Limits::new(),
            ErrorKind::Fault(FaultKind::Syntax),
        ),
        (
            Request::new("eval", "x", "12345"),
            Limits::new().with_max_input_bytes(4),
            ErrorKind::ResourceLimit,
        ),
    ] {
        let c = &mut Context::new(limits, flag.clone());
        let outcome = execute(&request, c);
        assert_eq!(error(&outcome).kind(), kind, "{request:?}");
        assert_eq!(c.work_used(), 0);
    }
    let c = &mut Context::new(Limits::new().with_max_input_bytes(4), flag);
    let outcome = execute(&Request::new("eval", "x", "12345"), c);
    assert_limit(error(&outcome), LimitField::InputBytes);
}

// The display of a value is charged to the context of the line: its steps as
// work, beyond the output of its bytes, and its numbers against that
// context's `max_integer_bits`.
#[test]
fn the_display_of_a_value_is_charged_to_the_context_of_the_line() {
    let (outcome, _) = run(&Request::new("eval", "x", "2^100"), Limits::new());
    assert!(is(value(&outcome), "1267650600228229401496703205376"));
    let c = &mut context(Limits::new().with_max_integer_bits(64));
    assert_limit(
        &serialize(&outcome, c).unwrap_err(),
        LimitField::IntegerBits,
    );
    let c = &mut context(Limits::new());
    let bytes = serialize(&outcome, c).unwrap();
    assert_eq!(c.output_used(), bytes.len() as u64);
    assert!(c.work_used() > c.output_used(), "{}", c.work_used());
}

// A caller that cancels between two requests stops the second at its first
// charge point, with nothing charged, as a host that checks cancellation
// between two evaluations does.
#[test]
fn a_flag_cancelled_between_two_requests_stops_the_second() {
    let flag = CancelFlag::new();
    let request = Request::new("expand", "x", "(x+1)^4");
    let mut first = Context::new(Limits::new(), flag.clone());
    value(&execute(&request, &mut first));
    flag.cancel();
    let mut second = Context::new(Limits::new(), flag.clone());
    let outcome = execute(&request, &mut second);
    assert_eq!(error(&outcome).kind(), ErrorKind::Cancelled);
    assert_eq!(second.work_used(), 0);
    assert_eq!(fields(&line(&outcome))[4], "Cancelled");
}

// The deadline comes with the context on an injected clock: a request whose
// deadline has passed ends with `DeadlineExceeded` at its first charge, a
// deadline that passes in the middle of a request ends it there, and a line
// is not written once the deadline has passed. A deadline far away on the
// monotonic clock changes nothing.
#[test]
fn a_deadline_on_an_injected_clock_ends_the_request() {
    let request = Request::new("expand", "x", "(x+1)^60").with_context_version(5);
    let probe = CountingProbe::never();
    let clock = FakeClock::at(0);
    let c = &mut observed(Limits::new(), clock.clone(), &probe).with_deadline(100);
    clock.set(100);
    let outcome = execute(&request, c);
    assert_eq!(error(&outcome).kind(), ErrorKind::DeadlineExceeded);
    assert_eq!(
        (c.work_used(), clock.reads(), outcome.context_version()),
        (0, 1, 5)
    );
    assert_eq!(fields(&line(&outcome))[4], "DeadlineExceeded");

    // The clock passes the deadline after its 50th reading.
    let (full, full_context) = run(&request, Limits::new());
    value(&full);
    let ticking = TickingClock::default();
    let c = &mut observed(Limits::new(), ticking.clone(), &probe).with_deadline(50);
    let outcome = execute(&request, c);
    assert_eq!(error(&outcome).kind(), ErrorKind::DeadlineExceeded);
    assert_eq!(ticking.reads.load(Ordering::SeqCst), 50);
    assert!(c.work_used() < full_context.work_used());

    let clock = FakeClock::at(0);
    let c = &mut observed(Limits::new(), clock.clone(), &probe).with_deadline(10);
    clock.set(10);
    let error = serialize(&full, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::DeadlineExceeded);
    assert_eq!(c.output_used(), 0);

    let c = &mut Context::new(Limits::new(), CancelFlag::new()).with_timeout(3_600_000_000_000);
    let outcome = execute(&request, c);
    assert_eq!(line(&outcome), line(&full));
}

// ---------------------------------------------------------------------------
// The answer vectors

/// One case of the vector file: its seven columns.
struct Case<'a> {
    id: &'a str,
    operation: &'a str,
    variable: &'a str,
    input: &'a str,
    result: &'a str,
    answer: &'a str,
    limits: &'a str,
}

/// The cases of `vectors/r02.tsv`, in their order, after the header row.
fn cases() -> Vec<Case<'static>> {
    VECTORS
        .lines()
        .skip(1)
        .map(|line| {
            let columns: [&str; 7] = line.split('\t').collect::<Vec<_>>().try_into().expect(line);
            let [id, operation, variable, input, result, answer, limits] = columns;
            Case {
                id,
                operation,
                variable,
                input,
                result,
                answer,
                limits,
            }
        })
        .collect()
}

/// The field of `Limits` named `name`.
fn limit_field(name: &str) -> LimitField {
    match name {
        "max_work" => LimitField::Work,
        "max_input_bytes" => LimitField::InputBytes,
        "max_output_bytes" => LimitField::OutputBytes,
        "max_depth" => LimitField::Depth,
        "max_nodes" => LimitField::Nodes,
        "max_storage_bytes" => LimitField::StorageBytes,
        "max_integer_bits" => LimitField::IntegerBits,
        "max_exponent" => LimitField::Exponent,
        "max_frames" => LimitField::Frames,
        other => panic!("not a field of Limits: {other}"),
    }
}

/// The limits of a case, the defaults with the settings of its `limits`
/// column, and the fields that it sets.
fn case_limits(case: &Case<'_>) -> (Limits, Vec<LimitField>) {
    let mut limits = Limits::new();
    let mut fields = Vec::new();
    if case.limits == "-" {
        return (limits, fields);
    }
    for setting in case.limits.split(';') {
        let (name, value) = setting.split_once('=').unwrap();
        let value: u64 = value.parse().unwrap();
        let field = limit_field(name);
        limits = match field {
            LimitField::Work => limits.with_max_work(value),
            LimitField::InputBytes => limits.with_max_input_bytes(value),
            LimitField::OutputBytes => limits.with_max_output_bytes(value),
            LimitField::Depth => limits.with_max_depth(value),
            LimitField::Nodes => limits.with_max_nodes(value),
            LimitField::StorageBytes => limits.with_max_storage_bytes(value),
            LimitField::IntegerBits => limits.with_max_integer_bits(value),
            LimitField::Exponent => limits.with_max_exponent(value),
            _ => limits.with_max_frames(value),
        };
        fields.push(field);
    }
    (limits, fields)
}

// Every case of `vectors/r02.tsv` runs as one request through the command
// entry under its limits. The result of a case with an answer is compared
// with the answer by canonical form, and its line writes the display text of
// the result; an error is compared by its kind, which its line writes, and a
// `ResourceLimit` by the field that the limits column sets. The line of every
// case fits the limits of the case: written under the context of its request,
// as a host writes it, it has the same bytes as under wide limits.
#[test]
fn every_vector_of_r02_replays_through_the_command_entry() {
    let cases = cases();
    assert_eq!(cases.len(), 58);
    let mut answered = 0;
    for case in &cases {
        let (limits, set) = case_limits(case);
        let request = Request::new(case.operation, case.variable, case.input);
        let (outcome, mut c) = run(&request, limits);
        let text = line(&outcome);
        let own = serialize(&outcome, &mut c).expect(case.id);
        assert_eq!(own, text.as_bytes(), "{}", case.id);
        assert_shape(&text, &outcome);
        if case.result == "ok" {
            assert!(is(value(&outcome), case.answer), "{}", case.id);
            answered += 1;
        } else {
            let error = error(&outcome);
            assert_eq!(fields(&text)[4], case.result, "{}", case.id);
            if case.result == "ResourceLimit" {
                assert_eq!(set.len(), 1, "{}", case.id);
                assert_limit(error, set[0]);
            }
        }
    }
    assert_eq!(answered, 49);
}

// The examples of the output lines in `docs/semantics.md`, with the requests
// that they name: every field but the message, whose wording is not part of
// the interface. The state line of the examples is written by the unit
// tests in `src/command/tests.rs`, since no operation of this release ends in
// a state.
#[test]
fn the_examples_of_the_output_lines_hold() {
    let versions = Request::new("expand", "x", "x^257")
        .with_input_version(3)
        .with_context_version(2)
        .with_settings_version(1);
    let cases = [
        (
            Request::new("eval", "x", "1/3 + 1/6"),
            Limits::new(),
            "value\t0\t0\t0\t1/2",
        ),
        (
            Request::new("expand", "x", "(x+1)^5").with_input_version(7),
            Limits::new(),
            "value\t7\t0\t0\t1 + 5*x + 10*x^2 + 10*x^3 + 5*x^4 + x^5",
        ),
        (
            Request::new("eval", "x", ""),
            Limits::new(),
            "error\t0\t0\t0\tSyntax\t0..0\t-\t-\t-\t-",
        ),
        (
            Request::new("eval", "x", "0*(1/0)"),
            Limits::new(),
            "error\t0\t0\t0\tDivisionByZero\t3..6\t-\t-\t-\t-",
        ),
        (
            versions,
            Limits::new().with_max_exponent(256),
            "error\t3\t2\t1\tResourceLimit\t2..5\tField(max_exponent)\t-\t256\tRequired(257)",
        ),
        (
            Request::new("expand", "x", "(x+1)^5"),
            Limits::new().with_max_nodes(12),
            "error\t0\t0\t0\tResourceLimit\t-\tField(max_nodes)\tValue\t12\tRequired(17)",
        ),
        (
            Request::new("eval", "x", "x"),
            Limits::new(),
            "error\t0\t0\t0\tUnknownSymbol\t-\t-\t-\t-\t-",
        ),
        (
            Request::new("simplify", "x", "x"),
            Limits::new(),
            "error\t0\t0\t0\tUnsupported\t-\t-\t-\t-\t-",
        ),
    ];
    for (request, limits, expected) in cases {
        let (outcome, _) = run(&request, limits);
        let text = line(&outcome);
        let found = fields(&text);
        let length = if found[0] == "error" { 10 } else { found.len() };
        assert_eq!(found[..length].join("\t"), expected, "{request:?}");
    }
}
