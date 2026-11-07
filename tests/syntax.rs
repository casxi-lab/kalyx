//! The parser: the single grammar with its precedence and associativity, the
//! decimal literals, the three limits of the parser with their spans, deep
//! input on a small stack, function-call syntax, the reserved names and the
//! command words, the vectors of `vectors/r02.tsv` that the parser decides,
//! strict evaluation through the term core, the spans of errors and the order
//! of failures, the display text read back and the charges. The rules are
//! those of `docs/semantics.md` and `docs/components/syntax/contract.md`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use kalyx::context::{CancelFlag, Storage};
use kalyx::number::{Integer, Rational};
use kalyx::syntax::parse;
use kalyx::term::{Term, TermKind};
use kalyx::{
    Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope, Limits,
    Span,
};

const VECTORS: &str = include_str!("../vectors/r02.tsv");

// ---------------------------------------------------------------------------
// Helpers

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

fn default_context() -> Context {
    context(Limits::new())
}

/// The display text of the term of `source` under the default limits.
fn shown(source: &str) -> String {
    let c = &mut default_context();
    let term = parse(source, c).expect(source);
    term.display(c).unwrap()
}

/// The error of `source` under `limits`.
fn failure(source: &str, limits: Limits) -> Error {
    parse(source, &mut context(limits)).expect_err(source)
}

/// The error of `source` under the default limits.
fn default_failure(source: &str) -> Error {
    failure(source, Limits::new())
}

fn span(start: usize, end: usize) -> Option<Span> {
    Some(Span::new(start, end).unwrap())
}

fn assert_fault(error: &Error, fault: FaultKind, start: usize, end: usize) {
    assert_eq!(error.kind(), ErrorKind::Fault(fault), "{error}");
    assert_eq!(error.span(), span(start, end), "{error}");
}

fn assert_limit(error: &Error, field: LimitField, start: usize, end: usize) {
    assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{error}");
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(field),
        "{error}"
    );
    assert_eq!(error.span(), span(start, end), "{error}");
}

/// Runs `test` on a thread with a stack of 2 MiB.
fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap();
}

/// `levels` pairs of parentheses around the literal `1`.
fn nested(levels: usize) -> String {
    format!("{}1{}", "(".repeat(levels), ")".repeat(levels))
}

/// One case of the vector file: its seven columns.
struct Case<'a> {
    id: &'a str,
    operation: &'a str,
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
            let columns: Vec<&str> = line.split('\t').collect();
            let columns: [&str; 7] = columns.try_into().expect(line);
            let [id, operation, _variable, input, result, answer, limits] = columns;
            Case {
                id,
                operation,
                input,
                result,
                answer,
                limits,
            }
        })
        .collect()
}

/// The case `id` of the vector file.
fn case(id: &str) -> Case<'static> {
    cases().into_iter().find(|case| case.id == id).expect(id)
}

/// The limits of a case: the defaults, with the `field=value` settings of its
/// `limits` column.
fn case_limits(case: &Case<'_>) -> Limits {
    let mut limits = Limits::new();
    if case.limits == "-" {
        return limits;
    }
    for setting in case.limits.split(';') {
        let (field, value) = setting.split_once('=').unwrap();
        let value: u64 = value.parse().unwrap();
        limits = match field {
            "max_depth" => limits.with_max_depth(value),
            "max_exponent" => limits.with_max_exponent(value),
            _ => {
                assert_eq!(field, "max_integer_bits", "a limit these tests set");
                limits.with_max_integer_bits(value)
            }
        };
    }
    limits
}

/// The work that `step` charges to a fresh context under the default limits.
fn work_of(step: impl FnOnce(&mut Context)) -> u64 {
    let c = &mut default_context();
    step(c);
    c.work_used()
}

/// The work that parsing `source` charges under the default limits.
fn parse_work(source: &str) -> u64 {
    work_of(|c| drop(parse(source, c).unwrap()))
}

fn number(value: i64, c: &mut Context) -> Term {
    Term::number(Rational::from(value), c).unwrap()
}

fn symbol(name: &str, c: &mut Context) -> Term {
    Term::symbol(name, c).unwrap()
}

// ---------------------------------------------------------------------------
// The grammar

// The first five cases of `vectors/r02.tsv` are the five evaluations of the
// workloads fixture; each parses, under its limits, into the number of its
// answer column, and the answer itself parses into the same term.
#[test]
fn the_first_five_eval_vectors_parse_to_their_answers() {
    let all = cases();
    let ids: Vec<&str> = all[..5].iter().map(|case| case.id).collect();
    assert_eq!(
        ids,
        [
            "rational_sum",
            "exact_decimal",
            "wide_integer",
            "negative_power",
            "precedence"
        ]
    );
    for case in &all[..5] {
        assert_eq!((case.operation, case.result), ("eval", "ok"), "{}", case.id);
        let c = &mut context(case_limits(case));
        let term = parse(case.input, c).unwrap();
        assert_eq!(term.kind(), TermKind::Number, "{}", case.id);
        assert_eq!(term.display(c).unwrap(), case.answer, "{}", case.id);
        let answer = parse(case.answer, c).unwrap();
        assert!(term.equals(&answer, c).unwrap(), "{}", case.id);
    }
    assert_eq!(shown("-2^2 + 2^3^2"), "508");
}

// `^` binds tightest and is right-associative; a unary minus binds less
// tightly than `^` and more tightly than `*` and `/`; `*`, `/`, `+` and `-`
// are left-associative.
#[test]
fn precedence_and_associativity_follow_the_grammar() {
    for (source, expected) in [
        ("(1+2)*3", "9"),
        ("2^3^2", "512"),
        ("(2^3)^2", "64"),
        ("-2^2", "-4"),
        ("(-2)^2", "4"),
        ("8/4/2", "1"),
        ("8/(4/2)", "4"),
        ("5-2-1", "2"),
        ("5-(2-1)", "4"),
        ("2+3*4", "14"),
        ("(2+3)*4", "20"),
        ("2*3^2", "18"),
        ("-3^2*2", "-18"),
        ("2/3*3", "2"),
        ("1/2/2", "1/4"),
        ("10-(2-(7-3))", "12"),
        ("(1/2)/(3/4)", "2/3"),
        ("-(2+3)*(-7+1)", "30"),
    ] {
        assert_eq!(shown(source), expected, "{source}");
    }
}

// A unary minus may start every operand: after a binary operator, after `(`,
// after another unary minus and after `^`, whose exponent is a unary
// expression, so `2^-2` is $2^{-2}$ and `2^-1^2` is $2^{-(1^2)}$.
#[test]
fn a_unary_minus_may_start_every_operand() {
    for (source, expected) in [
        ("2*-3+4", "-2"),
        ("1--1", "2"),
        ("--2", "2"),
        ("2^-2", "1/4"),
        ("-2^-2", "-1/4"),
        ("2^-1^2", "1/2"),
        ("2^--1", "2"),
        ("-x*y", "-x*y"),
        ("x*-y", "-x*y"),
        ("x/-y", "-x*y^(-1)"),
        ("x^-1", "x^(-1)"),
        ("-(x + y)", "-x - y"),
        (" 001.2500 / -0.50 ", "-5/2"),
    ] {
        assert_eq!(shown(source), expected, "{source}");
    }
}

// Whitespace is space, tab, line feed, form feed and carriage return; it
// separates tokens and means nothing else.
#[test]
fn whitespace_separates_tokens() {
    assert_eq!(shown("\t1 +\r\n2\x0c"), "3");
    assert_eq!(shown(" x_1  *  y "), "x_1*y");
    assert_fault(&default_failure("1\x0b+2"), FaultKind::Syntax, 1, 2);
}

// ---------------------------------------------------------------------------
// Number literals

// `1.5` is read exactly by the decimal literal function of the exact
// numbers: the same value as `Rational::parse_decimal`, the same bound of 4
// bits per digit against `max_integer_bits`, with the span of the literal.
#[test]
fn decimal_literals_are_read_by_the_literal_function() {
    let c = &mut default_context();
    let term = parse("1.5", c).unwrap();
    assert_eq!(term.display(c).unwrap(), "3/2");
    assert_eq!(
        term.as_number(),
        Some(&Rational::parse_decimal("1.5", c).unwrap())
    );
    let term = parse("001.2500", c).unwrap();
    assert_eq!(term.as_number().unwrap().to_string(), "5/4");
    assert_eq!(shown("0.1 + 0.2"), "3/10");
    // Two digits need 8 bits, one more than 7.
    let narrow = Limits::new().with_max_integer_bits(7);
    let error = failure("x + 1.5", narrow);
    assert_limit(&error, LimitField::IntegerBits, 4, 7);
    assert_eq!(error.exceeded().unwrap().amount(), LimitAmount::Required(8));
    let literal = Rational::parse_decimal("1.5", &mut context(narrow)).unwrap_err();
    assert_eq!(literal.exceeded(), error.exceeded());
}

// `.5`, `1.` and `1e-3` are syntax errors with the span of the offending
// character, or an empty span at the end of the literal; a number literal is
// the whole run of letters, digits, `_` and points that follows a digit, so
// `2x` and `1e3` are one invalid literal, never two operands.
#[test]
fn incomplete_and_scientific_literals_are_syntax_errors() {
    assert_fault(&default_failure(".5"), FaultKind::Syntax, 0, 1);
    assert_fault(&default_failure("1."), FaultKind::Syntax, 2, 2);
    assert_fault(&default_failure("1e-3"), FaultKind::Syntax, 1, 2);
    for (source, start, end) in [
        ("x + .5", 4, 5),
        ("1. + x", 2, 2),
        ("1e3", 1, 2),
        ("2x", 1, 2),
        ("2.5x", 3, 4),
        ("0x10", 1, 2),
        ("1_000", 1, 2),
        ("1.2.3", 3, 4),
        (".", 0, 1),
    ] {
        assert_fault(&default_failure(source), FaultKind::Syntax, start, end);
    }
}

// ---------------------------------------------------------------------------
// The limits of the parser

// The length of the source is checked against `max_input_bytes` before any
// byte is read: the error has the span of the whole source, and nothing is
// charged.
#[test]
fn input_bytes_are_checked_before_any_byte_is_read() {
    let limits = Limits::new().with_max_input_bytes(3);
    assert_eq!(
        parse("123", &mut context(limits))
            .unwrap()
            .display(&mut default_context())
            .unwrap(),
        "123"
    );
    let c = &mut context(limits);
    let error = parse("1234", c).unwrap_err();
    assert_limit(&error, LimitField::InputBytes, 0, 4);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), 3);
    assert_eq!(exceeded.amount(), LimitAmount::Required(4));
    assert_eq!(exceeded.scope(), None);
    assert_eq!(c.work_used(), 0);
    // The limit comes before every syntax error.
    assert_limit(&failure("1+$$", limits), LimitField::InputBytes, 0, 4);
}

// Each syntax node, a number, an identifier, a unary minus, a power and each
// binary operator, is checked with `check_storage` at scope `Value` as the
// count of nodes so far; parentheses add none, and the open frames and the
// reserved temporaries count as well.
#[test]
fn syntax_nodes_are_checked_against_max_nodes() {
    let fits = Limits::new().with_max_nodes(3);
    assert_eq!(shown_under("1+2", fits), "3");
    let error = failure("1+2", Limits::new().with_max_nodes(2));
    assert_limit(&error, LimitField::Nodes, 0, 3);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.allowed(), 2);
    assert_eq!(exceeded.amount(), LimitAmount::Required(3));
    // The rejected node is not charged: the four tokens 4, the two digits 2
    // and the two nodes that fit 2.
    let c = &mut context(Limits::new().with_max_nodes(2));
    assert!(parse("1+2", c).is_err());
    assert_eq!(c.work_used(), 4 + 2 + 2);
    // A syntax node costs no logical bytes: eleven syntax nodes fit under the
    // least `max_storage_bytes` that admits the number 1.
    let least = (0..)
        .find(|&k| parse("1", &mut context(Limits::new().with_max_storage_bytes(k))).is_ok())
        .unwrap();
    let limits = Limits::new().with_max_storage_bytes(least);
    assert!(parse("1*1*1*1*1*1", &mut context(limits)).is_ok());
    // A temporary of one node leaves room for two syntax nodes.
    let c = &mut context(fits);
    let reserved = c.reserve(Storage::new(1, 0)).unwrap();
    assert_limit(&parse("1+2", c).unwrap_err(), LimitField::Nodes, 0, 3);
    c.release(reserved);
    assert!(parse("1+2", c).is_ok());
    // The term of `1+1+1+1` has one node and its syntax tree seven, so the
    // parser rejects it; parentheses and spaces add no node.
    let error = failure("1+1+1+1", Limits::new().with_max_nodes(6));
    assert_limit(&error, LimitField::Nodes, 0, 7);
    for (source, nodes) in [
        ("((x))", 1),
        ("-x", 2),
        ("(1 + 2) * x", 5),
        ("0*(1/0)", 5),
        ("2^-3", 4),
        ("1+1+1+1", 7),
    ] {
        let limits = Limits::new().with_max_nodes(nodes);
        let tight = Limits::new().with_max_nodes(nodes - 1);
        assert!(
            !matches!(parse(source, &mut context(limits)), Err(ref e) if e.kind() == ErrorKind::ResourceLimit),
            "{source}"
        );
        assert_eq!(
            failure(source, tight).exceeded().unwrap().id(),
            &LimitId::Field(LimitField::Nodes),
            "{source}"
        );
    }
}

/// The display text of the term of `source` under `limits`.
fn shown_under(source: &str, limits: Limits) -> String {
    let c = &mut context(limits);
    let term = parse(source, c).unwrap();
    term.display(&mut default_context()).unwrap()
}

// The level of every operand is compared with `max_depth` before it is read:
// the whole input is at level 1, and the contents of parentheses, the
// operand of a unary minus, the exponent of a power and every operand of a
// chain after its first are one level deeper. The error has the span of the
// token that opens the level beyond the limit. The terms of these inputs are
// numbers, so only the parser limits their depth.
#[test]
fn the_syntax_depth_is_checked_against_max_depth() {
    for (source, depth) in [
        ("1", 1),
        ("(1)", 2),
        ("-1", 2),
        ("1+2+3+4", 2),
        ("1*2+3", 2),
        ("1+2*3", 3),
        ("2^3^2", 3),
        ("-2^2", 3),
        ("2^-1", 3),
        ("((((1))))", 5),
        ("2*(3+4)", 4),
        ("1+(1+(1))", 5),
    ] {
        let limits = Limits::new().with_max_depth(depth);
        assert!(parse(source, &mut context(limits)).is_ok(), "{source}");
        let error = failure(source, Limits::new().with_max_depth(depth - 1));
        assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{source}: {error}");
        let exceeded = error.exceeded().unwrap();
        assert_eq!(
            exceeded.id(),
            &LimitId::Field(LimitField::Depth),
            "{source}"
        );
        assert_eq!(exceeded.allowed(), depth - 1, "{source}");
        assert_eq!(exceeded.amount(), LimitAmount::Required(depth), "{source}");
    }
    // 127 pairs of parentheses fit the default limit of 128; the 128th `(`
    // opens level 129.
    assert!(parse(&nested(127), &mut default_context()).is_ok());
    let error = default_failure(&nested(128));
    assert_limit(&error, LimitField::Depth, 127, 128);
    assert_limit(
        &failure("x", Limits::new().with_max_depth(0)),
        LimitField::Depth,
        0,
        1,
    );
    assert_limit(
        &failure("1+-2", Limits::new().with_max_depth(2)),
        LimitField::Depth,
        2,
        3,
    );
    assert_limit(
        &failure("x^y^z", Limits::new().with_max_depth(2)),
        LimitField::Depth,
        3,
        4,
    );
}

// 20,000 nested parentheses parse on a thread with a stack of 2 MiB: with
// `max_depth` raised above their depth they give the number 1, and under the
// default limits they fail with `ResourceLimit` at the 128th `(`. The parser
// and the builder keep their state on the heap, so the builder also hands a
// deep term to the term core on that stack.
#[test]
fn twenty_thousand_nested_parentheses_on_a_2_mib_stack() {
    on_small_stack(|| {
        let source = nested(20_000);
        let c = &mut context(Limits::new().with_max_depth(20_001));
        let term = parse(&source, c).unwrap();
        assert_eq!(term.display(c).unwrap(), "1");
        let error = default_failure(&source);
        assert_limit(&error, LimitField::Depth, 127, 128);
        // Unary minus signs nest as deeply, with one node each.
        let minus = format!("{}1", "-".repeat(20_000));
        let wide = Limits::new()
            .with_max_depth(20_001)
            .with_max_nodes(20_001)
            .with_max_work(u64::MAX);
        let c = &mut context(wide);
        assert_eq!(parse(&minus, c).unwrap().display(c).unwrap(), "1");
        // `x*(y+x*(y+...x...))` with 10,000 products nested in sums has the
        // syntax depth 30,001 and builds a term of depth 20,001.
        let deep = format!("{}x{}", "x*(y+".repeat(10_000), ")".repeat(10_000));
        let limits = Limits::new()
            .with_max_depth(30_001)
            .with_max_nodes(1 << 20)
            .with_max_storage_bytes(1 << 30)
            .with_max_work(u64::MAX);
        let c = &mut context(limits);
        let term = parse(&deep, c).unwrap();
        assert_eq!((term.depth(), term.size()), (20_001, 40_001));
        let error = failure(&deep, limits.with_max_depth(30_000));
        assert_limit(&error, LimitField::Depth, 49_999, 50_000);
    });
}

// ---------------------------------------------------------------------------
// Function-call syntax, reserved names and command words

// An identifier followed by `(`, with or without whitespace between them, is
// function-call syntax, which fails with `Unsupported` and the span from the
// start of the name to the end of the `(`, whatever follows.
#[test]
fn function_call_syntax_is_unsupported() {
    for (source, start, end) in [
        ("f(x)", 0, 2),
        ("f (x)", 0, 3),
        ("sin(1)", 0, 4),
        ("max(x, y)", 0, 4),
        ("2*g(x)", 2, 4),
        ("diff(x^2)", 0, 5),
        ("f(", 0, 2),
    ] {
        assert_fault(&default_failure(source), FaultKind::Unsupported, start, end);
    }
    // A number or a parenthesis before `(` is juxtaposition, not a call.
    assert_fault(&default_failure("2(x)"), FaultKind::Syntax, 1, 2);
    assert_fault(&default_failure("(f)(x)"), FaultKind::Syntax, 3, 4);
}

// `pi`, `i` and `undefined` are reserved for the constants of a later
// release and fail with `Unsupported` and the span of the name, also before
// `(`; names that only resemble them are symbols.
#[test]
fn reserved_names_are_unsupported() {
    for (source, start, end) in [
        ("pi", 0, 2),
        ("i", 0, 1),
        ("undefined", 0, 9),
        ("2*pi", 2, 4),
        ("x + i*y", 4, 5),
        ("pi(2)", 0, 2),
    ] {
        assert_fault(&default_failure(source), FaultKind::Unsupported, start, end);
    }
    for name in ["Pi", "ii", "pi2", "_pi", "I", "undefined_"] {
        assert_eq!(shown(name), name);
    }
}

// The grammar has no command words: a word such as `eval`, `expand` or
// `diff` inside an expression is an identifier like any other.
#[test]
fn command_words_are_ordinary_names() {
    for word in ["eval", "expand", "diff", "simplify", "solve"] {
        let c = &mut default_context();
        let term = parse(word, c).unwrap();
        assert_eq!(term.as_symbol(), Some(word));
    }
    assert_eq!(shown("expand + diff*eval"), "expand + diff*eval");
    assert_fault(&default_failure("expand x"), FaultKind::Syntax, 7, 8);
}

// The three depth cases of `vectors/r02.tsv`, under their limits: 63
// right-nested sums parse under the default limits, 64 fail at
// `max_depth=32`, and 192 nested parentheses fail at `max_depth=128`.
#[test]
fn the_depth_vectors_of_r02() {
    let fits = case("right_nested_63");
    assert_eq!(fits.result, "ok");
    let c = &mut context(case_limits(&fits));
    let term = parse(fits.input, c).unwrap();
    assert_eq!(term.display(c).unwrap(), fits.answer);
    for id in ["right_depth_limit_1", "depth_limit_1"] {
        let deep = case(id);
        assert_eq!(deep.result, "ResourceLimit", "{id}");
        let error = failure(deep.input, case_limits(&deep));
        assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{id}");
        assert_eq!(
            error.exceeded().unwrap().id(),
            &LimitId::Field(LimitField::Depth),
            "{id}"
        );
        assert!(error.span().is_some(), "{id}");
    }
    // The first `(` whose contents exceed the limit: the 16th of the right
    // nesting, at byte 47, where the levels grow by two per `(`, and the
    // 128th of the parentheses alone.
    let error = failure(
        case("right_depth_limit_1").input,
        Limits::new().with_max_depth(32),
    );
    assert_limit(&error, LimitField::Depth, 47, 48);
    let error = failure(
        case("depth_limit_1").input,
        Limits::new().with_max_depth(128),
    );
    assert_limit(&error, LimitField::Depth, 127, 128);
}

// The error cases of `vectors/r02.tsv` that the parser decides, besides the
// depth cases, with the span of the offending text: a malformed literal, the
// division of `0*(1/0)`, the exponent of `2^(1/2)`, the 4097 bits of
// $2^{4096}$, and the exponent 257 of the expansion `degree_limit_1`, which
// fails as its input is read.
#[test]
fn the_error_vectors_of_r02() {
    for (id, fault, start, end) in [
        ("invalid_syntax_1", FaultKind::Syntax, 3, 4),
        ("zero_division_1", FaultKind::DivisionByZero, 3, 6),
        ("fractional_power_1", FaultKind::NonIntegerExponent, 2, 7),
    ] {
        let case = case(id);
        assert_eq!(
            case.result,
            format!("{fault:?}"),
            "{id}: the result kind of the vector"
        );
        assert_fault(&failure(case.input, case_limits(&case)), fault, start, end);
    }
    for (id, field, start, end) in [
        ("bit_limit_1", LimitField::IntegerBits, 0, 6),
        ("degree_limit_1", LimitField::Exponent, 2, 5),
    ] {
        let case = case(id);
        assert_eq!(case.result, "ResourceLimit", "{id}");
        assert_limit(&failure(case.input, case_limits(&case)), field, start, end);
    }
}

// Every evaluation of `vectors/r02.tsv` is decided by the parser alone:
// under its limits, an `ok` case parses into the number of its answer, and
// every other case fails with the kind of its result column.
#[test]
fn every_evaluation_of_r02_is_decided_by_the_parser() {
    let evaluations: Vec<Case<'static>> = cases()
        .into_iter()
        .filter(|case| case.operation == "eval")
        .collect();
    assert_eq!(evaluations.len(), 31);
    for case in &evaluations {
        let c = &mut context(case_limits(case));
        match parse(case.input, c) {
            Ok(term) => {
                assert_eq!(case.result, "ok", "{}", case.id);
                assert_eq!(term.kind(), TermKind::Number, "{}", case.id);
                assert_eq!(term.display(c).unwrap(), case.answer, "{}", case.id);
            }
            Err(error) => {
                let kind = match error.kind() {
                    ErrorKind::Fault(fault) => format!("{fault:?}"),
                    other => format!("{other:?}"),
                };
                assert_eq!(kind, case.result, "{}: {error}", case.id);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Spans

// Syntax errors carry the span of the offending token, and an empty span at
// the end when the input ends too early; a character outside the syntax is
// spanned whole.
#[test]
fn syntax_errors_carry_the_span_of_their_text() {
    for (source, start, end) in [
        ("", 0, 0),
        ("   ", 3, 3),
        ("()", 1, 2),
        ("1+", 2, 2),
        ("(1+2", 4, 4),
        ("1+2)", 3, 4),
        ("1 2", 2, 3),
        ("2 x", 2, 3),
        ("x y", 2, 3),
        ("x.5", 1, 3),
        ("(1)(2)", 3, 4),
        ("1+λ", 2, 4),
        ("λ", 0, 2),
        ("x=1", 1, 2),
        ("1/**2", 2, 3),
        ("+1", 0, 1),
        ("1++2", 2, 3),
        ("2^", 2, 2),
        ("2^*3", 2, 3),
        ("x,y", 1, 2),
        ("1×2", 1, 3),
    ] {
        let error = default_failure(source);
        assert_fault(&error, FaultKind::Syntax, start, end);
        assert!(source.is_char_boundary(start) && source.is_char_boundary(end));
    }
}

// An input that breaks two rules fails with the first failure in reading
// order: a reserved name fails before the token after it is read; any other
// identifier reads the token after it, to detect function-call syntax,
// before its node is checked; and a token that starts an operand right after
// a complete operand fails at once with `Syntax`.
#[test]
fn failures_come_in_reading_order() {
    for (source, start, end) in [
        ("pi(x)", 0, 2),
        ("pi (x)", 0, 2),
        ("pi$", 0, 2),
        ("pi 1.", 0, 2),
        ("f(", 0, 2),
    ] {
        assert_fault(&default_failure(source), FaultKind::Unsupported, start, end);
    }
    for (source, start, end) in [
        ("1 pi", 2, 4),
        ("1 f(x)", 2, 3),
        ("x f(1)", 2, 3),
        ("1 2x", 2, 4),
    ] {
        assert_fault(&default_failure(source), FaultKind::Syntax, start, end);
    }
    let none = Limits::new().with_max_nodes(0);
    assert_fault(&failure("x$", none), FaultKind::Syntax, 1, 2);
    assert_fault(&failure("x(", none), FaultKind::Unsupported, 0, 2);
    assert_limit(&failure("1$", none), LimitField::Nodes, 0, 1);
}

// An error of the term core gets the span of the syntax node whose term
// failed; an error of an exponent the span of the exponent with its
// parentheses.
#[test]
fn errors_of_the_term_core_carry_the_span_of_their_node() {
    // The exponent beyond `max_exponent`, and beyond the width of a `u64`.
    let error = default_failure("x^5000");
    assert_limit(&error, LimitField::Exponent, 2, 6);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(5000)
    );
    let error = default_failure("x^(2^70)");
    assert_limit(&error, LimitField::Exponent, 2, 8);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Bound(u64::MAX)
    );
    // The product of two exponents, and the bits of a power of a number.
    assert_limit(&default_failure("(x^2)^3000"), LimitField::Exponent, 0, 10);
    assert_limit(
        &default_failure("1 + 2^4096"),
        LimitField::IntegerBits,
        4,
        10,
    );
    // A product that the term core builds larger and deeper than its syntax:
    // $x y^{-1}$ has four nodes and the depth 3, and its chain the span of
    // `x/y`, not that of the whole sum.
    let limits = Limits::new().with_max_nodes(3);
    assert_limit(&failure("x/y", limits), LimitField::Nodes, 0, 3);
    let limits = Limits::new().with_max_depth(2);
    assert_limit(&failure("x/y + 1", limits), LimitField::Depth, 0, 3);
    assert_limit(&failure("x*y + z", limits), LimitField::Depth, 0, 7);
    // An exhausted budget, at the charge where it runs out.
    let error = failure("x + y", Limits::new().with_max_work(10));
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(LimitField::Work)
    );
    assert!(error.span().is_some());
}

// The exponent of a power is built after its base and must be a number that
// is an integer; it is then an `i64` under the exponent rules of the term
// core.
#[test]
fn exponents_are_integer_constants() {
    for (source, expected) in [
        ("x^(1+1)", "x^2"),
        ("x^-2", "x^(-2)"),
        ("x^(2*3-6)", "1"),
        ("x^(x-x)", "1"),
        ("2^(3^2)", "512"),
        ("(x+y)^2", "(x + y)^2"),
    ] {
        assert_eq!(shown(source), expected, "{source}");
    }
    for (source, start, end) in [
        ("x^y", 2, 3),
        ("x^(1/2)", 2, 7),
        ("x^0.5", 2, 5),
        ("x^(x/x)", 2, 7),
        ("2^(y)^2", 2, 7),
    ] {
        assert_fault(
            &default_failure(source),
            FaultKind::NonIntegerExponent,
            start,
            end,
        );
    }
    // The base is built first, so its division by zero comes before that of
    // the exponent.
    assert_fault(
        &default_failure("(1/0)^(1/0)"),
        FaultKind::DivisionByZero,
        1,
        4,
    );
}

// Numbers are evaluated strictly when their term is built, so an invalid
// numeric subterm fails at once, with the span of its operation.
#[test]
fn numbers_are_evaluated_strictly() {
    for (source, start, end) in [
        ("0*(1/0)", 3, 6),
        ("(1/0)^0", 1, 4),
        ("0^(-1)", 0, 6),
        ("0^-1", 0, 4),
        ("x/0", 0, 3),
        ("x/(x-x)", 0, 7),
        ("x/(0*x^(-1))", 0, 12),
        ("2*x/(1-1)*y", 0, 9),
    ] {
        assert_fault(
            &default_failure(source),
            FaultKind::DivisionByZero,
            start,
            end,
        );
    }
    assert_eq!(shown("0^0"), "1");
    assert_eq!(shown("0^3"), "0");
    assert_eq!(shown("x/x"), "x*x^(-1)");
    assert_eq!(shown("x - x"), "0");
    assert_eq!(shown("0*x^(-1)"), "0*x^(-1)");
    // The operands are built from left to right, each before its operation,
    // and a divisor is inverted before the next operand is built, as in a
    // left-associative reading of the chain.
    for (source, fault, start, end) in [
        ("1/0 + x^y", FaultKind::DivisionByZero, 0, 3),
        ("x^y + 1/0", FaultKind::NonIntegerExponent, 2, 3),
        ("1/0*x^y", FaultKind::DivisionByZero, 0, 3),
        ("x^y*1/0", FaultKind::NonIntegerExponent, 2, 3),
        ("2 - 1/0*x^y", FaultKind::DivisionByZero, 4, 7),
        ("x/(1-1) - y^(1/2)", FaultKind::DivisionByZero, 0, 7),
    ] {
        assert_fault(&default_failure(source), fault, start, end);
    }
    // Every syntax error comes before any term is built.
    assert_fault(&default_failure("1/0 + 1.2.3"), FaultKind::Syntax, 9, 10);
}

// ---------------------------------------------------------------------------
// The display text read back

// Every form of the display grammar of the term core reads back as the same
// term: canonical display text parses into a term whose display is that
// text, byte for byte.
#[test]
fn the_display_of_a_term_reads_back() {
    for text in [
        "-3/4",
        "5",
        "0",
        "x",
        "x^2",
        "x^(-1)",
        "(x + y)^(-2)",
        "(x^(-1))^0",
        "(x^(-1))^(-1)",
        "(-1 + x)^(-1)",
        "x*y",
        "-x*y",
        "-2*x",
        "1/2*x^(-1)*y^(-1)",
        "-z*(x + y)",
        "2*z*(x + y)",
        "3*z*(x + 2/3*y)",
        "4*(x + y)^2",
        "0*x^(-1)",
        "0*x^(-1)*y^(-1)",
        "-(-1 + x)^(-1)",
        "-3/4*x",
        "2 + x + y",
        "1 - x",
        "-x + y",
        "-2*x - y",
        "2*x + 2*y",
        "x - z*(x + y)",
        "5 + 0*x^(-1)",
        "-3/4 + x - 1/2*y",
        "y + 0*x^(-1)",
        "x*x^(-1)",
        "y*(x^(-1))^0",
    ] {
        assert_eq!(shown(text), text, "{text}");
    }
    // Terms built through the constructors read back as equal terms.
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let two = number(2, c);
    let sum = Term::sum(&[x.clone(), y.clone(), two.clone()], c).unwrap();
    let inverse = sum.power(-3, c).unwrap();
    let half = Term::number(
        Rational::new(Integer::from(1_i64), Integer::from(2_i64), c).unwrap(),
        c,
    )
    .unwrap();
    let product = Term::product(
        &[half, x.clone(), inverse.clone(), y.power(5, c).unwrap()],
        c,
    )
    .unwrap();
    let witness = inverse.power(0, c).unwrap();
    let difference = Term::sum(&[product.clone(), witness, x.negate(c).unwrap()], c).unwrap();
    for term in [sum, inverse, product, difference] {
        let text = term.display(c).unwrap();
        let read = parse(&text, c).unwrap();
        assert!(read.equals(&term, c).unwrap(), "{text}");
    }
}

// ---------------------------------------------------------------------------
// Charges

// The parser charges each token its bytes and the end of the input one unit
// more, each decimal literal its digits, and each syntax node one unit when
// it is read and one more when its term is built, besides the charges of the
// term core.
#[test]
fn charges_follow_the_charge_table() {
    // `x`: the token 1 and the end 1; one node 1; its term 1 and the symbol 2.
    assert_eq!(parse_work("x"), 6);
    // `12`: the token 2 and the end 1; the digits 2; one node 1; its term 1
    // and the number 1.
    assert_eq!(parse_work("12"), 8);
    // `1.5`: the token 3 and the end 1; the digits 2; one node 1; its term 1
    // and the number 1.
    assert_eq!(parse_work("1.5"), 9);
    // ` x + y `: the bytes 7 and the end 1; three nodes 3; three terms 3; the
    // two symbols 4 and the sum of the term core.
    let sum = work_of(|c| {
        let x = symbol("x", c);
        let y = symbol("y", c);
        let before = c.work_used();
        drop(Term::sum(&[x, y], c).unwrap());
        assert_eq!(c.work_used() - before, 17);
    });
    assert_eq!(sum, 4 + 17);
    assert_eq!(parse_work(" x + y "), 8 + 3 + 3 + 4 + 17);
    // `x/2`: the bytes 3 and the end 1; the digit 1; three nodes 3; three
    // terms 3; the symbol 2, the number 1, the power $2^{-1}$ and the product.
    let quotient = work_of(|c| {
        let x = symbol("x", c);
        let two = number(2, c);
        let inverse = two.power(-1, c).unwrap();
        drop(Term::product(&[x, inverse], c).unwrap());
    });
    assert_eq!(parse_work("x/2"), 4 + 1 + 3 + 3 + quotient);
    // `-x`: the bytes 2 and the end 1; two nodes 2; two terms 2; the symbol 2
    // and its negation.
    let negation = work_of(|c| drop(symbol("x", c).negate(c).unwrap()));
    assert_eq!(parse_work("-x"), 3 + 2 + 2 + negation);
    // `x^2`: the bytes 3 and the end 1; the digit 1; three nodes 3; three
    // terms 3; the symbol 2, the number 1 and the power.
    let square = work_of(|c| {
        let x = symbol("x", c);
        drop(number(2, c));
        drop(x.power(2, c).unwrap());
    });
    assert_eq!(parse_work("x^2"), 4 + 1 + 3 + 3 + square);
    // `2*x`: the bytes 3 and the end 1; the digit 1; three nodes 3; three
    // terms 3; the number 1, the symbol 2 and the product.
    let double = work_of(|c| {
        let two = number(2, c);
        let x = symbol("x", c);
        drop(Term::product(&[two, x], c).unwrap());
    });
    assert_eq!(parse_work("2*x"), 4 + 1 + 3 + 3 + double);
    // A rejected name charges only its token.
    let c = &mut default_context();
    assert!(parse("pi", c).is_err());
    assert_eq!(c.work_used(), 2);
    // A token is charged when it is read, also the `(` that opens a level
    // beyond `max_depth` and a literal beyond `max_integer_bits`, whose
    // digits are not charged: `x + 1.5` under 7 bits charges `x` 1, ` +` 2,
    // the node of `x` 1 and ` 1.5` 4. A node that its check rejects is not
    // charged, and neither is a character that starts no token, nor the
    // whitespace before it.
    for (source, limits, work) in [
        ("(1)", Limits::new().with_max_depth(1), 1),
        ("x + 1.5", Limits::new().with_max_integer_bits(7), 8),
        ("x", Limits::new().with_max_nodes(0), 2),
        ("  $", Limits::new(), 0),
    ] {
        let c = &mut context(limits);
        assert!(parse(source, c).is_err(), "{source}");
        assert_eq!(c.work_used(), work, "{source}");
    }
    // The charges do not depend on the limits.
    let wide = Limits::new()
        .with_max_work(u64::MAX)
        .with_max_depth(1 << 20);
    for source in ["-2^2 + 2^3^2", "(x + y)^2 / 2", "0.1 + 0.2"] {
        let c = &mut context(wide);
        parse(source, c).unwrap();
        assert_eq!(c.work_used(), parse_work(source), "{source}");
    }
}

// A request failure of a charge carries the span of the step that charged:
// a cancelled request fails at its first token.
#[test]
fn request_failures_carry_the_span_of_their_step() {
    let flag = CancelFlag::new();
    let c = &mut Context::new(Limits::new(), flag.clone());
    flag.cancel();
    let error = parse("  12 + 3", c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Cancelled);
    assert_eq!(error.span(), span(2, 4));
    // The work runs out at the token `+`: `12` charges 2, its digits 2 and
    // its node 1; the ` +` needs 2 more.
    let error = failure("12 + 3", Limits::new().with_max_work(6));
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(error.span(), span(3, 4));
}

// `parse` is also reachable at the crate root.
#[test]
fn parse_is_re_exported_at_the_root() {
    let c = &mut default_context();
    let term = kalyx::parse("2*x", c).unwrap();
    assert_eq!(term.display(c).unwrap(), "2*x");
}
