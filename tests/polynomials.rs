//! The univariate polynomials: the ring and its variable, the charges of
//! every operation, the limits of the degree and of the number of terms,
//! the storage formula, the expansion of terms with its failures and their
//! order, the conversion back to terms, the expansions and derivatives of
//! `vectors/r02.tsv`, deep terms on a small stack, and the shared
//! algorithms instantiated through a generic helper. The rules are those of
//! `docs/components/polynomials/contract.md`. The property tests of the
//! arithmetic against an independent reference are a separate file.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results and panic on a column that is not a limit, as the tests do"
)]

use std::convert::Infallible;

use kalyx::coefficient::{CoefficientRing, Rationals};
use kalyx::context::{CancelFlag, Storage};
use kalyx::number::{Integer, Rational};
use kalyx::polynomial::{Polynomial, PolynomialRing};
use kalyx::syntax::parse;
use kalyx::term::Term;
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

/// Limits raised far beyond every polynomial and term of these tests, for
/// building deep terms and for comparing results with answers.
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

/// The ring $\mathbb{Q}[x]$ for the variable `name`.
fn polynomial_ring(name: &str, c: &mut Context) -> PolynomialRing {
    PolynomialRing::new(Rationals, name, c).unwrap()
}

/// The term of `source`.
fn term(source: &str, c: &mut Context) -> Term {
    parse(source, c).expect(source)
}

/// The polynomial of `source` in `ring`.
fn polynomial(ring: &PolynomialRing, source: &str, c: &mut Context) -> Polynomial {
    let term = term(source, c);
    ring.expand(&term, c).expect(source)
}

/// The rational $n / d$.
fn rational(numerator: i64, denominator: i64) -> Rational {
    let c = &mut default_context();
    Rational::new(Integer::from(numerator), Integer::from(denominator), c).unwrap()
}

/// The terms of `polynomial` as pairs of a degree and the display text of
/// its coefficient, in increasing degree.
fn pairs(polynomial: &Polynomial) -> Vec<(u64, String)> {
    polynomial
        .degrees()
        .iter()
        .zip(polynomial.coefficients())
        .map(|(degree, coefficient)| (*degree, coefficient.to_string()))
        .collect()
}

/// `pairs` for coefficients written as integers or fractions.
fn expected(terms: &[(u64, &str)]) -> Vec<(u64, String)> {
    terms
        .iter()
        .map(|(degree, coefficient)| (*degree, (*coefficient).to_owned()))
        .collect()
}

/// The display text of `term`.
fn show(term: &Term, c: &mut Context) -> String {
    term.display(c).unwrap()
}

/// The work that `step` charges to `c`.
fn work<T>(c: &mut Context, step: impl FnOnce(&mut Context) -> T) -> u64 {
    let before = c.work_used();
    let _ = step(c);
    c.work_used() - before
}

fn assert_limit(error: &Error, field: LimitField) {
    assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{error}");
    assert_eq!(
        error.exceeded().unwrap().id(),
        &LimitId::Field(field),
        "{error}"
    );
}

fn assert_fault(error: &Error, fault: FaultKind) {
    assert_eq!(error.kind(), ErrorKind::Fault(fault), "{error}");
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
            let columns: Vec<&str> = line.split('\t').collect();
            let columns: [&str; 7] = columns.try_into().expect(line);
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

/// The case `id` of the vector file.
fn case(id: &str) -> Case<'static> {
    cases().into_iter().find(|case| case.id == id).expect(id)
}

/// The fields that the `limits` column of a case sets, by their names in
/// `Limits`.
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

/// The name of the kind of `error` in the `result` column.
fn result_name(error: &Error) -> String {
    match error.kind() {
        ErrorKind::Fault(fault) => format!("{fault:?}"),
        other => format!("{other:?}"),
    }
}

/// Runs an `expand` or `diff` case as one request under its limits: the
/// input is parsed, the ring of its variable is built, and the input is
/// expanded and converted back to a term, or differentiated.
fn run_case(case: &Case<'_>, limits: Limits) -> Result<Term, Error> {
    let c = &mut context(limits);
    let input = parse(case.input, c)?;
    let ring = PolynomialRing::new(Rationals, case.variable, c)?;
    if case.operation == "diff" {
        ring.differentiate(&input, c)
    } else {
        let polynomial = ring.expand(&input, c)?;
        ring.to_term(&polynomial, c)
    }
}

// ---------------------------------------------------------------------------
// The ring

// The variable follows the rule of symbol names of the term core, and the
// reserved names fail as `Term::symbol` fails; a ring charges one unit and
// one per byte of its name, after the check.
#[test]
fn the_variable_follows_the_rule_of_symbol_names() {
    let c = &mut default_context();
    for name in ["x", "t", "x_1", "_", "Var9"] {
        let before = c.work_used();
        let ring = polynomial_ring(name, c);
        assert_eq!(ring.variable(), name);
        assert_eq!(c.work_used() - before, 1 + name.len() as u64);
        assert_eq!(*ring.coefficient_ring(), Rationals);
    }
    for (name, start, end) in [("", 0, 0), ("1x", 0, 1), ("x-1", 1, 2), ("x y", 1, 2)] {
        let before = c.work_used();
        let error = PolynomialRing::new(Rationals, name, c).unwrap_err();
        assert_fault(&error, FaultKind::Syntax);
        assert_eq!(error.span(), Span::new(start, end), "{name:?}");
        assert_eq!(c.work_used(), before, "a rejected name charges nothing");
        let symbol = Term::symbol(name, c).unwrap_err();
        assert_eq!(symbol.kind(), error.kind());
        assert_eq!(symbol.span(), error.span());
    }
    for name in ["pi", "i", "undefined"] {
        let error = PolynomialRing::new(Rationals, name, c).unwrap_err();
        assert_fault(&error, FaultKind::Unsupported);
        assert_eq!(error.span(), Span::new(0, name.len()));
    }
}

// The polynomials of a ring are `Polynomial<Rationals>`, which is
// `Polynomial`, and their `Debug` view is shallow.
#[test]
fn polynomials_are_opaque_and_their_debug_view_is_shallow() {
    let c = &mut default_context();
    let ring: PolynomialRing<Rationals> = polynomial_ring("x", c);
    let x: Polynomial<Rationals> = ring.generator(c).unwrap();
    let same: Polynomial = x.clone();
    assert_eq!(
        format!("{same:?}"),
        "Polynomial { degree: Some(1), terms: 1, .. }"
    );
    let zero = ring.zero(c).unwrap();
    assert!(zero.is_zero());
    assert_eq!(zero.degree(), None);
    assert!(zero.degrees().is_empty() && zero.coefficients().is_empty());
    assert_eq!(
        format!("{zero:?}"),
        "Polynomial { degree: None, terms: 0, .. }"
    );
    let big = polynomial(&ring, "(x + 1)^40", c);
    assert_eq!(
        format!("{big:?}"),
        "Polynomial { degree: Some(40), terms: 41, .. }"
    );
}

// ---------------------------------------------------------------------------
// Charges

// Every operation charges fixed amounts: one unit per loop step, the
// coefficient operations of the rationals one unit each on the one-word
// coefficients here, and one unit for each result after its checks.
#[test]
fn operations_charge_the_amounts_of_the_charge_table() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    // The zero: its result. The one and $x$: the one of $\mathbb{Q}$ and
    // the result. A constant: the result; the zero test is free.
    assert_eq!(work(c, |c| ring.zero(c).unwrap()), 1);
    assert_eq!(work(c, |c| ring.one(c).unwrap()), 1 + 1);
    assert_eq!(work(c, |c| ring.generator(c).unwrap()), 1 + 1);
    let five = Rational::from(5_i64);
    assert_eq!(work(c, |c| ring.constant(&five, c).unwrap()), 1);
    let zero = Rational::from(0_i64);
    assert_eq!(work(c, |c| ring.constant(&zero, c).unwrap()), 1);
    let x = ring.generator(c).unwrap();
    let one = ring.one(c).unwrap();
    // $x + 1$: two merge steps and the result.
    let sum = ring.add(&x, &one, c).unwrap();
    assert_eq!(work(c, |c| ring.add(&x, &one, c).unwrap()), 2 + 1);
    // $(x + 1) + (x + 1)$: two steps, two additions of coefficients and the
    // result; $(x + 1) - (x + 1)$ the same with subtractions.
    assert_eq!(work(c, |c| ring.add(&sum, &sum, c).unwrap()), 2 + 2 + 1);
    assert_eq!(
        work(c, |c| ring.subtract(&sum, &sum, c).unwrap()),
        2 + 2 + 1
    );
    // $1 - x$: two steps, the negation of the term of $x$ and the result.
    assert_eq!(work(c, |c| ring.subtract(&one, &x, c).unwrap()), 2 + 1 + 1);
    // $-(x + 1)$: one step and one negation per term, and the result.
    assert_eq!(work(c, |c| ring.negate(&sum, c).unwrap()), 2 * 2 + 1);
    // $(x + 1)(x + 1)$: two rows, four product steps with four products;
    // the second row is merged into the first, three steps and one
    // addition; and the result.
    let square = ring.multiply(&sum, &sum, c).unwrap();
    assert_eq!(
        work(c, |c| ring.multiply(&sum, &sum, c).unwrap()),
        2 + 4 * 2 + 3 + 1 + 1
    );
    // $(x + 1)^2$: a copy, one unit per term and the result; one bit below
    // the highest, one unit and a squaring. $(x + 1)^0$: the one.
    assert_eq!(
        work(c, |c| ring.power(&sum, 2, c).unwrap()),
        (2 + 1) + 1 + 15
    );
    assert_eq!(work(c, |c| ring.power(&sum, 0, c).unwrap()), 1 + 1);
    // $(x + 1)^5$, with $5 = 101_2$: the copy; the bit of value 2, unset,
    // one unit and a squaring of $x + 1$; the bit of value 1, set, one unit,
    // a squaring of $(x + 1)^2$ and a product by $x + 1$.
    let fourth = ring.power(&square, 2, c).unwrap();
    let squaring = work(c, |c| ring.multiply(&square, &square, c).unwrap());
    let times = work(c, |c| ring.multiply(&fourth, &sum, c).unwrap());
    assert_eq!(
        work(c, |c| ring.power(&sum, 5, c).unwrap()),
        3 + (1 + 15) + (1 + squaring + times)
    );
    // The derivative of $x^2 + 2x + 1$: one step per term, and for each term
    // of positive degree the integer $d \cdot 1$ and a product; the result.
    assert_eq!(
        work(c, |c| ring.derivative(&square, c).unwrap()),
        3 + 2 * 2 + 1
    );
}

// The expansion charges one unit per node it visits and one per byte of the
// shorter of a symbol name and the variable name, besides the operations of
// the ring.
#[test]
fn the_expansion_charges_its_nodes_and_the_operations_of_the_ring() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    // A number: the node and its constant.
    let two = term("2", c);
    assert_eq!(work(c, |c| ring.expand(&two, c).unwrap()), 1 + 1);
    // The variable: the node, its byte and $x$.
    let x = term("x", c);
    assert_eq!(work(c, |c| ring.expand(&x, c).unwrap()), 1 + 1 + 2);
    // $x + 1$: the sum and its constant 1; the core $x$, 4; the constant of
    // its coefficient 1, the product of the constant and $x$, a row of one
    // step and one product and the result; the sum of the total 1 and $x$,
    // whose term comes after the constant: one appended term and the result.
    let sum = term("x + 1", c);
    assert_eq!(
        work(c, |c| ring.expand(&sum, c).unwrap()),
        (1 + 1) + 4 + (1 + (1 + 2 + 1) + (1 + 1))
    );
    // A power: its node, its base and the power of the ring.
    let square = term("x^2", c);
    let (base, exponent) = square.as_power().unwrap();
    let base_work = work(c, |c| ring.expand(base, c).unwrap());
    let base_polynomial = ring.expand(base, c).unwrap();
    let exponent = u64::try_from(exponent).unwrap();
    let power_work = work(c, |c| ring.power(&base_polynomial, exponent, c).unwrap());
    assert_eq!(
        work(c, |c| ring.expand(&square, c).unwrap()),
        1 + base_work + power_work
    );
    // A product: its node and the constant of its coefficient, then for each
    // stored factor in turn its expansion and the product with the total.
    let product = term("(x - 1)*(x + 2)", c);
    let (coefficient, factors) = product.as_product().unwrap();
    let mut product_work = 1 + work(c, |c| ring.constant(coefficient, c).unwrap());
    let mut total = ring.constant(coefficient, c).unwrap();
    for factor in factors {
        product_work += work(c, |c| ring.expand(factor, c).unwrap());
        let polynomial = ring.expand(factor, c).unwrap();
        product_work += work(c, |c| ring.multiply(&total, &polynomial, c).unwrap());
        total = ring.multiply(&total, &polynomial, c).unwrap();
    }
    assert_eq!(work(c, |c| ring.expand(&product, c).unwrap()), product_work);
    // A longer variable name charges the bytes of the shorter name.
    let long = PolynomialRing::new(Rationals, "abc", c).unwrap();
    let symbol = term("abc", c);
    assert_eq!(work(c, |c| long.expand(&symbol, c).unwrap()), 1 + 3 + 2);
    let short = term("ab", c);
    let error = long.expand(&short, c).unwrap_err();
    assert_fault(&error, FaultKind::UnknownSymbol);
    assert_eq!(work(c, |c| long.expand(&short, c).unwrap_err()), 1 + 2);
    // The conversion back: one unit per term and the constructors of the
    // term core, which it calls in this order.
    // A term of degree 1 is the product of its coefficient and the symbol
    // itself, with no power.
    let linear = polynomial(&ring, "2*x + 1", c);
    let converted = work(c, |c| ring.to_term(&linear, c).unwrap());
    let replayed = work(c, |c| {
        let x = Term::symbol("x", c).unwrap();
        let constant = Term::number(Rational::from(1_i64), c).unwrap();
        let two = Term::number(Rational::from(2_i64), c).unwrap();
        let monomial = Term::product(&[two, x], c).unwrap();
        Term::sum(&[constant, monomial], c).unwrap()
    });
    assert_eq!(converted, 2 + replayed);
    let polynomial = polynomial(&ring, "3*x^2 - 1", c);
    let converted = work(c, |c| ring.to_term(&polynomial, c).unwrap());
    let replayed = work(c, |c| {
        let x = Term::symbol("x", c).unwrap();
        let constant = Term::number(Rational::from(-1_i64), c).unwrap();
        let three = Term::number(Rational::from(3_i64), c).unwrap();
        let square = x.power(2, c).unwrap();
        let monomial = Term::product(&[three, square], c).unwrap();
        Term::sum(&[constant, monomial], c).unwrap()
    });
    assert_eq!(converted, 2 + replayed);
    // A constant builds no symbol: one unit for its term, the number and
    // the sum.
    let constant = ring.constant(&rational(7, 3), c).unwrap();
    let converted = work(c, |c| ring.to_term(&constant, c).unwrap());
    let replayed = work(c, |c| {
        let number = Term::number(rational(7, 3), c).unwrap();
        Term::sum(&[number], c).unwrap()
    });
    assert_eq!(converted, 1 + replayed);
    // The zero polynomial is the number 0, its empty sum.
    let zero = ring.zero(c).unwrap();
    let converted = work(c, |c| ring.to_term(&zero, c).unwrap());
    assert_eq!(converted, work(c, |c| Term::sum(&[], c).unwrap()));
}

// The charges are incremental: every operation, under every budget below
// its work, fails with `max_work` and returns nothing, and succeeds with
// its work; the work does not depend on the other limits.
#[test]
fn every_operation_is_charged_step_by_step() {
    type Operation = fn(&PolynomialRing, &Polynomial, &Polynomial, &Term, &mut Context) -> bool;
    let operations: [(&str, Operation); 6] = [
        ("add", |ring, a, b, _, c| ring.add(a, b, c).is_ok()),
        ("subtract", |ring, a, b, _, c| {
            ring.subtract(a, b, c).is_ok()
        }),
        ("multiply", |ring, a, b, _, c| {
            ring.multiply(a, b, c).is_ok()
        }),
        ("power", |ring, a, _, _, c| ring.power(a, 7, c).is_ok()),
        ("derivative", |ring, a, _, _, c| {
            ring.derivative(a, c).is_ok()
        }),
        ("expand", |ring, _, _, t, c| ring.expand(t, c).is_ok()),
    ];
    let setup = &mut default_context();
    let ring = polynomial_ring("x", setup);
    let a = polynomial(&ring, "x^3 - 2*x + 1/2", setup);
    let b = polynomial(&ring, "x^2 + 2*x - 5", setup);
    let input = term("(x - 1)*(x + 1)^3 - x^4", setup);
    for (name, operation) in operations {
        let mut charges = Vec::new();
        for limits in [Limits::new(), wide()] {
            let c = &mut context(limits);
            assert!(operation(&ring, &a, &b, &input, c), "{name}");
            charges.push(c.work_used());
        }
        assert_eq!(
            charges[0], charges[1],
            "{name}: the same work under every limits"
        );
        let full = charges[0];
        for budget in 0..full {
            let c = &mut context(Limits::new().with_max_work(budget));
            assert!(!operation(&ring, &a, &b, &input, c), "{name} with {budget}");
            assert!(c.work_used() <= budget, "{name} with {budget}");
        }
        let c = &mut context(Limits::new().with_max_work(full));
        assert!(operation(&ring, &a, &b, &input, c), "{name} with {full}");
        let c = &mut context(Limits::new().with_max_work(full - 1));
        let error = match name {
            "expand" => ring.expand(&input, c).unwrap_err(),
            "derivative" => ring.derivative(&a, c).unwrap_err(),
            "power" => ring.power(&a, 7, c).unwrap_err(),
            "multiply" => ring.multiply(&a, &b, c).unwrap_err(),
            "subtract" => ring.subtract(&a, &b, c).unwrap_err(),
            _ => ring.add(&a, &b, c).unwrap_err(),
        };
        assert_limit(&error, LimitField::Work);
    }
}

// A request failure of a charge ends an operation: a cancelled request
// fails at the first charge, with nothing built.
#[test]
fn a_cancelled_request_ends_an_operation_at_its_first_charge() {
    let flag = CancelFlag::new();
    let c = &mut Context::new(Limits::new(), flag.clone());
    let ring = polynomial_ring("x", c);
    let sum = polynomial(&ring, "x + 1", c);
    let input = term("(x + 1)^9", c);
    flag.cancel();
    let before = c.work_used();
    assert_eq!(
        ring.multiply(&sum, &sum, c).unwrap_err().kind(),
        ErrorKind::Cancelled
    );
    assert_eq!(
        ring.expand(&input, c).unwrap_err().kind(),
        ErrorKind::Cancelled
    );
    assert_eq!(ring.zero(c).unwrap_err().kind(), ErrorKind::Cancelled);
    assert_eq!(c.work_used(), before);
}

// ---------------------------------------------------------------------------
// The limits of the degree and of the number of terms

// The degree of a product, a power and the variable is checked against
// `max_exponent` before any charge of the operation, in checked arithmetic.
#[test]
fn the_degree_is_checked_against_max_exponent_before_the_work() {
    let limits = Limits::new().with_max_exponent(150);
    let c = &mut context(limits);
    let ring = polynomial_ring("x", c);
    let input = term("(x^100 + 1)*(x^100 - 1)", c);
    let before = c.work_used();
    let error = ring.expand(&input, c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), 150);
    assert_eq!(exceeded.amount(), LimitAmount::Required(200));
    assert_eq!(exceeded.scope(), None);
    assert!(c.work_used() > before, "the factors were expanded first");
    // The product itself charges nothing before it fails.
    let high = polynomial(&ring, "x^100 + 1", c);
    let rejected = work(c, |c| {
        let error = ring.multiply(&high, &high, c).unwrap_err();
        assert_limit(&error, LimitField::Exponent);
    });
    assert_eq!(rejected, 0);
    // A power checks its exponent, then its degree, before any charge: the
    // exponent also for a base of degree 0 and for the zero polynomial,
    // whose powers have no degree beyond the limit, and before a degree
    // beyond it.
    let x = ring.generator(c).unwrap();
    let square = ring.power(&x, 2, c).unwrap();
    let one = ring.one(c).unwrap();
    let zero = ring.zero(c).unwrap();
    for (base, exponent, amount) in [
        (&x, 151, 151),
        (&square, 76, 152),
        (&one, 151, 151),
        (&zero, 151, 151),
        (&square, 151, 151),
    ] {
        let rejected = work(c, |c| {
            let error = ring.power(base, exponent, c).unwrap_err();
            assert_limit(&error, LimitField::Exponent);
            assert_eq!(
                error.exceeded().unwrap().amount(),
                LimitAmount::Required(amount)
            );
        });
        assert_eq!(rejected, 0);
    }
    // A constant has the degree 0 under every exponent within the limit.
    assert_eq!(
        pairs(&ring.power(&one, 150, c).unwrap()),
        expected(&[(0, "1")])
    );
    // The degrees one above the limit fail, before any charge, and a degree
    // at the limit passes.
    let tall = polynomial(&ring, "x^100 + 1", c);
    let short = polynomial(&ring, "x^50 - 1", c);
    let below = &mut context(Limits::new().with_max_exponent(149));
    for rejected in [
        work(below, |below| {
            let error = ring.multiply(&tall, &short, below).unwrap_err();
            assert_limit(&error, LimitField::Exponent);
            assert_eq!(
                error.exceeded().unwrap().amount(),
                LimitAmount::Required(150)
            );
        }),
        work(below, |below| {
            let error = ring.power(&square, 75, below).unwrap_err();
            assert_limit(&error, LimitField::Exponent);
            assert_eq!(
                error.exceeded().unwrap().amount(),
                LimitAmount::Required(150)
            );
        }),
    ] {
        assert_eq!(rejected, 0);
    }
    let product = ring.multiply(&tall, &short, c).unwrap();
    assert_eq!(product.degree(), Some(150));
    assert_eq!(ring.power(&square, 75, c).unwrap().degree(), Some(150));
    // The variable itself has the degree 1.
    let c = &mut context(Limits::new().with_max_exponent(0));
    let ring = polynomial_ring("x", c);
    assert_limit(&ring.generator(c).unwrap_err(), LimitField::Exponent);
    assert_eq!(c.work_used(), 2, "only the ring was charged");
    // A degree beyond `u64::MAX` exceeds every limit.
    let c = &mut context(wide().with_max_exponent(u64::MAX));
    let ring = polynomial_ring("x", c);
    let x = ring.generator(c).unwrap();
    let high = ring.power(&x, i64::MAX as u64, c).unwrap();
    assert_eq!(high.degree(), Some(i64::MAX as u64));
    let error = ring.multiply(&high, &x, c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), i64::MAX as u64);
    let error = ring.multiply(&high, &high, c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(u64::MAX - 1)
    );
    let error = ring.power(&high, 3, c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Bound(u64::MAX)
    );
}

// The number of terms is bounded through the storage cost of a polynomial,
// checked with `check_storage` at scope `Value`: a polynomial of ten terms
// costs 53 nodes, so under `max_nodes = 40` the expansion of
// $1 + x + \dots + x^9$, whose term costs 18 nodes, fails when its total
// reaches eight terms.
#[test]
fn the_number_of_terms_is_bounded_through_the_storage_cost() {
    let source = "1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9";
    let wide_context = &mut context(wide());
    let ring = polynomial_ring("x", wide_context);
    let input = term(source, wide_context);
    assert_eq!(input.size(), 18);
    let all = ring.expand(&input, wide_context).unwrap();
    assert_eq!(all.degrees().len(), 10);
    assert_eq!(ring.storage(&all).nodes, 1 + 3 + 8 * 5 + 9);
    let c = &mut context(Limits::new().with_max_nodes(40));
    let error = ring.expand(&input, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.allowed(), 40);
    assert_eq!(exceeded.amount(), LimitAmount::Required(1 + 3 + 6 * 5 + 7));
    // The bytes are checked after the nodes: $1 + x + x^2 + x^3$ costs
    // $5 + 10 + 20 + 20 + 3 \cdot 4 = 67$ bytes.
    let c = &mut context(Limits::new().with_max_storage_bytes(64));
    let error = ring.expand(&input, c).unwrap_err();
    assert_limit(&error, LimitField::StorageBytes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.amount(), LimitAmount::Required(67));
    // The open frames and the reserved temporaries count as well.
    let c = &mut default_context();
    let x = ring.generator(c).unwrap();
    let reserved = c.reserve(Storage::new(8_190, 0)).unwrap();
    let error = ring.add(&x, &x, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    c.release(reserved);
    assert_eq!(pairs(&ring.add(&x, &x, c).unwrap()), expected(&[(1, "2")]));
    // A product checks each partial sum of its rows: the first row of
    // $(x - 1)(x^3 + x^2 + x + 1)$ costs 17 nodes, although the product
    // $x^4 - 1$ costs 7.
    let a = polynomial(&ring, "x^3 + x^2 + x + 1", wide_context);
    let b = polynomial(&ring, "x - 1", wide_context);
    let product = ring.multiply(&b, &a, wide_context).unwrap();
    assert_eq!(pairs(&product), expected(&[(0, "-1"), (4, "1")]));
    assert_eq!(ring.storage(&product).nodes, 7);
    assert_eq!(ring.storage(&a).nodes, 17);
    let c = &mut context(Limits::new().with_max_nodes(16));
    let error = ring.multiply(&b, &a, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(17)
    );
}

// A partial sum of the rows of a product can cost more than every row and
// than the product: the rows of $(1 + x + x^2)(1 - x^2 + x^4)$ cost at most
// 17 nodes and the product $1 + x - x^3 + x^5 + x^6$ costs 23, but the sum of
// the first two rows, $1 + x - x^2 - x^3 + x^4 + x^5$, costs 29.
#[test]
fn a_product_fails_at_a_partial_sum_above_every_row_and_the_product() {
    let wide_context = &mut context(wide());
    let ring = polynomial_ring("x", wide_context);
    let a = polynomial(&ring, "1 + x + x^2", wide_context);
    let b = polynomial(&ring, "1 - x^2 + x^4", wide_context);
    let product = ring.multiply(&a, &b, wide_context).unwrap();
    assert_eq!(ring.storage(&product).nodes, 23);
    let c = &mut context(Limits::new().with_max_nodes(28));
    let error = ring.multiply(&a, &b, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(29)
    );
}

// A product with the zero polynomial runs no row, and its result is checked
// as every result is: under `max_nodes = 0` the zero polynomial itself does
// not fit.
#[test]
fn a_product_with_zero_is_checked_as_every_result() {
    let wide_context = &mut context(wide());
    let ring = polynomial_ring("x", wide_context);
    let zero = ring.zero(wide_context).unwrap();
    let x = ring.generator(wide_context).unwrap();
    let c = &mut context(Limits::new().with_max_nodes(0));
    assert_limit(&ring.zero(c).unwrap_err(), LimitField::Nodes);
    assert_limit(&ring.multiply(&zero, &x, c).unwrap_err(), LimitField::Nodes);
    assert_limit(&ring.multiply(&x, &zero, c).unwrap_err(), LimitField::Nodes);
}

// The storage formula of a polynomial: the zero polynomial $(1, 4)$; a
// constant $c$ its rational and the variable name once; a term of degree 1
// $(3, \mathrm{rb}(c) + \ell + 4)$, of degree $k \ge 2$
// $(5, \mathrm{rb}(c) + \ell + \lvert k \rvert + 12)$, and $(1, 4)$ per
// addition.
#[test]
fn the_storage_formula_of_polynomials() {
    let c = &mut context(wide());
    for (name, length) in [("x", 1_u64), ("abc", 3)] {
        let ring = polynomial_ring(name, c);
        let cost = |source: &str, c: &mut Context| {
            let input = parse(&source.replace('x', name), c).unwrap();
            let polynomial = ring.expand(&input, c).unwrap();
            ring.storage(&polynomial)
        };
        let zero = ring.zero(c).unwrap();
        assert_eq!(ring.storage(&zero), Storage::new(1, 4));
        // rb(5) = 3 + 1 + 3, rb(1/2) = 1 + 2 + 3.
        assert_eq!(cost("5", c), Storage::new(1, 7 + length));
        assert_eq!(cost("x", c), Storage::new(3, 5 + length + 4));
        assert_eq!(cost("2*x", c), Storage::new(3, 6 + length + 4));
        assert_eq!(cost("x^2", c), Storage::new(5, 5 + length + 2 + 12));
        assert_eq!(cost("x^5/2", c), Storage::new(5, 6 + length + 3 + 12));
        assert_eq!(
            cost("x^5/2 + 2*x - 5", c),
            Storage::new(5 + 3 + 1 + 2, (6 + length + 15) + (6 + length + 4) + 7 + 8)
        );
        // The coefficient $2^{100}$ costs its 101 bits.
        assert_eq!(
            cost("2^100*x^4096", c),
            Storage::new(5, 101 + 1 + 3 + length + 13 + 12)
        );
        // The cost of a polynomial is its terms' and the variable's, with
        // the cost of each coefficient from `measure` of the coefficient
        // ring.
        let polynomial = {
            let input = parse(&"3*x^7 + x".replace('x', name), c).unwrap();
            ring.expand(&input, c).unwrap()
        };
        let mut nodes = 0;
        let mut bytes = 0;
        for (degree, coefficient) in polynomial.degrees().iter().zip(polynomial.coefficients()) {
            let own = ring.coefficient_ring().measure(coefficient);
            nodes += own.nodes + if *degree == 1 { 2 } else { 4 };
            bytes += own.bytes + length + if *degree == 1 { 4 } else { 3 + 12 };
        }
        assert_eq!(
            ring.storage(&polynomial),
            Storage::new(nodes + 1, bytes + 4)
        );
    }
}

// ---------------------------------------------------------------------------
// The expansion

// Numbers, the variable, sums, products and powers expand into their
// polynomials, and coefficients that cancel leave no term.
#[test]
fn terms_expand_into_their_polynomials() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    let cases: [(&str, &[(u64, &str)]); 9] = [
        ("0", &[]),
        ("-3/4", &[(0, "-3/4")]),
        ("x", &[(1, "1")]),
        ("2*x^3 - x + 1/2", &[(0, "1/2"), (1, "-1"), (3, "2")]),
        ("(x - 1)*(x + 1)", &[(0, "-1"), (2, "1")]),
        ("(x + 1)^3", &[(0, "1"), (1, "3"), (2, "3"), (3, "1")]),
        ("x*(x + 2)^2 - x^3", &[(1, "4"), (2, "4")]),
        ("(x/2 + 1/3)^2", &[(0, "1/9"), (1, "1/3"), (2, "1/4")]),
        ("(x + 1)^2 - x^2 - 2*x - 1", &[]),
    ];
    for (source, terms) in cases {
        let polynomial = polynomial(&ring, source, c);
        assert_eq!(pairs(&polynomial), expected(terms), "{source}");
    }
    // A sum of powers of a sum cancels in the polynomial, not in the term.
    let input = term("(x + 1)^2 - (x - 1)^2 - 4*x", c);
    assert_eq!(show(&input, c), "-4*x - (-1 + x)^2 + (1 + x)^2");
    assert!(ring.expand(&input, c).unwrap().is_zero());
    let partial = polynomial(&ring, "(x + 1)^2 - (x - 1)^2 + x^5", c);
    assert_eq!(pairs(&partial), expected(&[(1, "4"), (5, "1")]));
}

// Coefficients that cancel leave no term, in every operation: the zero
// polynomial has no term, and no polynomial keeps a coefficient 0.
#[test]
fn coefficients_that_cancel_leave_no_term() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    let a = polynomial(&ring, "x^3 + 2*x - 1", c);
    let b = polynomial(&ring, "x^2 - 2*x + 1", c);
    let sum = ring.add(&a, &b, c).unwrap();
    assert_eq!(pairs(&sum), expected(&[(2, "1"), (3, "1")]));
    let difference = ring.subtract(&a, &a, c).unwrap();
    assert!(difference.is_zero());
    assert!(difference.degrees().is_empty() && difference.coefficients().is_empty());
    assert_eq!(ring.storage(&difference), Storage::new(1, 4));
    let negated = ring.negate(&a, c).unwrap();
    assert!(ring.add(&a, &negated, c).unwrap().is_zero());
    // The rows of $(x - 1)(x + 1)$ cancel in the degree 1.
    let product = polynomial(&ring, "(x - 1)*(x + 1)", c);
    assert_eq!(product.degrees(), &[0, 2]);
    // A constant of zero and the derivative of a constant are zero.
    assert!(ring.constant(&Rational::from(0_i64), c).unwrap().is_zero());
    let seven = polynomial(&ring, "7", c);
    assert!(ring.derivative(&seven, c).unwrap().is_zero());
    // The expansion of a sum whose monomials cancel is zero, and so is its
    // term.
    for source in [
        "(x + 1)^2 - x^2 - 2*x - 1",
        "(x + 1)^8 - (x + 1)^8",
        "x*(x + 1) - x^2 - x",
    ] {
        let zero = polynomial(&ring, source, c);
        assert!(zero.is_zero(), "{source}");
        assert_eq!(show(&ring.to_term(&zero, c).unwrap(), c), "0");
    }
    // A monomial whose core expands to zero leaves a total that is not zero
    // as it is.
    let cases: [(&str, &[(u64, &str)]); 3] = [
        ("1 + ((x + 1)^2 - x^2 - 2*x - 1)^2", &[(0, "1")]),
        ("x + ((x + 1)^2 - x^2 - 2*x - 1)^2", &[(1, "1")]),
        ("3*x^2 + 5*((x + 1)^2 - x^2 - 2*x - 1)^3", &[(2, "3")]),
    ];
    for (source, terms) in cases {
        let kept = polynomial(&ring, source, c);
        assert_eq!(pairs(&kept), expected(terms), "{source}");
    }
    for polynomial in [&sum, &product, &a, &negated] {
        let zero = Rational::from(0_i64);
        assert!(polynomial.coefficients().iter().all(|value| *value != zero));
        assert!(
            polynomial
                .degrees()
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        );
    }
}

// A power with a negative exponent fails with `NotPolynomial` once its base
// is expanded, the witnesses of the term core among them: a base that holds
// the variable and no other symbol, even one whose polynomial is a
// constant.
#[test]
fn negative_powers_whose_base_holds_the_variable_are_not_polynomials() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    for source in [
        "1/x",
        "x^(-2)",
        "(x^2 - 1)/(x - 1)",
        "x*x^(-1)",
        "x^2*x^(-1)",
        "0*x^(-1)",
        "(x^(-1))^0",
        "x^(-1) - x^(-1) + x",
        "((x + 1)^2 - x^2 - 2*x)^(-1)",
        "3 + 2*(1 + x)^(-3)",
    ] {
        let input = term(source, c);
        let error = ring.expand(&input, c).unwrap_err();
        assert_fault(&error, FaultKind::NotPolynomial);
        assert_eq!(error.span(), None, "{source}");
    }
    // The witnesses are kept by the term core.
    assert_eq!(show(&term("0*x^(-1)", c), c), "0*x^(-1)");
    assert_eq!(show(&term("x^(-1) - x^(-1) + x", c), c), "x + 0*x^(-1)");
    // The same terms in another variable fail at their first other symbol.
    let other = PolynomialRing::new(Rationals, "y", c).unwrap();
    let input = term("x*x^(-1)", c);
    assert_fault(
        &other.expand(&input, c).unwrap_err(),
        FaultKind::UnknownSymbol,
    );
}

// The first failure of the walk ends the expansion: the depth before any
// charge, then each node when it is entered, with its charge and the
// constant of a product or a sum, before its children, which follow in
// their stored order; the polynomial of a node is formed after theirs.
#[test]
fn failures_come_in_the_order_of_the_visit() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    // A power is charged when it is entered, before its base: $y^{-1}$ and
    // $y^2$ charge their power, then $y$ and its byte, and only then fail
    // with `UnknownSymbol`, while $y$ alone fails with it within two units.
    for source in ["y^(-1)", "y^2"] {
        let input = term(source, c);
        for budget in 0..3 {
            let budgeted = &mut context(Limits::new().with_max_work(budget));
            let error = ring.expand(&input, budgeted).unwrap_err();
            assert_limit(&error, LimitField::Work);
        }
        let budgeted = &mut context(Limits::new().with_max_work(3));
        let error = ring.expand(&input, budgeted).unwrap_err();
        assert_fault(&error, FaultKind::UnknownSymbol);
        assert_eq!(budgeted.work_used(), 3, "{source}");
    }
    let input = term("y", c);
    let budgeted = &mut context(Limits::new().with_max_work(2));
    assert_fault(
        &ring.expand(&input, budgeted).unwrap_err(),
        FaultKind::UnknownSymbol,
    );
    // A product or a sum builds the constant of its coefficient or of its
    // constant when it is entered, before its first factor or core.
    for source in ["2*y", "y + 1"] {
        let input = term(source, c);
        let narrow = &mut context(Limits::new().with_max_nodes(0));
        let error = ring.expand(&input, narrow).unwrap_err();
        assert_limit(&error, LimitField::Nodes);
    }
    // A symbol is the variable only with the same bytes: another case of a
    // letter, or a later byte that differs, is another symbol.
    for (variable, symbol) in [("x", "X"), ("X", "x"), ("ab", "ac"), ("abc", "abd")] {
        let other = PolynomialRing::new(Rationals, variable, c).unwrap();
        let input = term(symbol, c);
        let error = other.expand(&input, c).unwrap_err();
        assert_fault(&error, FaultKind::UnknownSymbol);
    }
    for (source, fault) in [
        // A base that holds another symbol fails at that symbol, before its
        // negative exponent.
        ("(x + y)^(-1)", FaultKind::UnknownSymbol),
        ("y^(-1)", FaultKind::UnknownSymbol),
        // The factors of $x^{-1} y$ are sorted by their bases, $x$ first.
        ("y/x", FaultKind::NotPolynomial),
        ("x/y", FaultKind::UnknownSymbol),
        // The monomials of a sum are sorted by their cores: the symbol $y$
        // comes before the power $x^{-1}$.
        ("x^(-1) + y", FaultKind::UnknownSymbol),
        ("y^2 + x^(-1)", FaultKind::NotPolynomial),
    ] {
        let input = term(source, c);
        let error = ring.expand(&input, c).unwrap_err();
        assert_fault(&error, fault);
    }
    // A limit of an operation comes in the same order: the factor $x^{100}$
    // has the key $x$, before $z$, while the monomial $z$, a symbol, comes
    // before the power $x^{100}$. The terms are built under wider limits.
    let wide_context = &mut context(wide());
    let c = &mut context(Limits::new().with_max_exponent(50));
    for (source, exponent) in [("x^100*z", true), ("z*x^100", true), ("z + x^100", false)] {
        let input = term(source, wide_context);
        let error = ring.expand(&input, c).unwrap_err();
        if exponent {
            assert_limit(&error, LimitField::Exponent);
        } else {
            assert_fault(&error, FaultKind::UnknownSymbol);
        }
    }
    // The depth comes first of all, before any charge.
    let c = &mut context(Limits::new().with_max_depth(2));
    let input = term("(x + 1)^2*y", wide_context);
    assert_limit(&ring.expand(&input, c).unwrap_err(), LimitField::Depth);
    assert_eq!(c.work_used(), 0);
}

// The polynomials of a term are checked against the limits of the context
// that expands it, and a polynomial built under one context is checked
// against the limits of the context that uses it.
#[test]
fn polynomials_are_checked_against_the_receiving_limits() {
    let wide_context = &mut context(wide());
    let ring = polynomial_ring("x", wide_context);
    let input = term("2^5000*x^5000 + 1", wide_context);
    let high = ring.expand(&input, wide_context).unwrap();
    // The power $x^{5000}$ of the core comes before its coefficient.
    let c = &mut default_context();
    assert_limit(&ring.expand(&input, c).unwrap_err(), LimitField::Exponent);
    let c = &mut context(Limits::new().with_max_exponent(5000));
    assert_limit(
        &ring.expand(&input, c).unwrap_err(),
        LimitField::IntegerBits,
    );
    let c = &mut default_context();
    let one = ring.one(c).unwrap();
    let error = ring.add(&high, &one, c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let error = ring.to_term(&high, c).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let c = &mut context(Limits::new().with_max_integer_bits(8192));
    let error = ring.to_term(&high, c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let c = &mut context(
        Limits::new()
            .with_max_integer_bits(8192)
            .with_max_exponent(5000),
    );
    let converted = ring.to_term(&high, c).unwrap();
    let back = ring.expand(&converted, c).unwrap();
    assert_eq!(pairs(&back), pairs(&high));
    // Every operation checks its result against the receiving limits, also
    // the copy with which a power of exponent 1 starts; the coefficients are
    // small, so that no coefficient operation fails first.
    let tall = polynomial(&ring, "x^5000 + 1", wide_context);
    let many = polynomial(
        &ring,
        "1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9",
        wide_context,
    );
    let narrow = &mut context(Limits::new().with_max_nodes(40));
    let error = ring.power(&many, 1, narrow).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(53)
    );
    let c = &mut default_context();
    let one = ring.one(c).unwrap();
    for (error, degree) in [
        (ring.negate(&tall, c).unwrap_err(), 5000),
        (ring.derivative(&tall, c).unwrap_err(), 4999),
        (ring.subtract(&tall, &one, c).unwrap_err(), 5000),
    ] {
        assert_limit(&error, LimitField::Exponent);
        assert_eq!(
            error.exceeded().unwrap().amount(),
            LimitAmount::Required(degree)
        );
    }
    // The degree of a result is checked before its storage cost: a sum
    // beyond both reports the degree.
    let narrow = &mut context(Limits::new().with_max_nodes(3));
    let error = ring.add(&tall, &one, narrow).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(5000)
    );
}

// The conversion back gives the canonical term of the polynomial, through
// the constructors of the term core, which reads back to the polynomial.
#[test]
fn polynomials_convert_back_to_canonical_terms() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    for (source, text) in [
        ("0", "0"),
        ("7/3", "7/3"),
        ("x", "x"),
        ("-x", "-x"),
        ("(x - 1)*(x + 1)", "-1 + x^2"),
        ("(x + 1)^3", "1 + 3*x + 3*x^2 + x^3"),
        ("(x/2 - 1/3)^2", "1/9 - 1/3*x + 1/4*x^2"),
    ] {
        let polynomial = polynomial(&ring, source, c);
        let converted = ring.to_term(&polynomial, c).unwrap();
        assert_eq!(show(&converted, c), text, "{source}");
        let rebuilt = parse(text, c).unwrap();
        assert!(converted.equals(&rebuilt, c).unwrap(), "{source}");
        let back = ring.expand(&converted, c).unwrap();
        assert_eq!(pairs(&back), pairs(&polynomial), "{source}");
    }
    let t = PolynomialRing::new(Rationals, "t", c).unwrap();
    let polynomial = polynomial(&t, "(t - 2)^2", c);
    let converted = t.to_term(&polynomial, c).unwrap();
    assert_eq!(show(&converted, c), "4 - 4*t + t^2");
}

// The derivative by the variable: $(c x^d)' = (d \cdot 1) c x^{d - 1}$, with
// constants giving zero; `differentiate` is the expansion, the derivative
// and the conversion back.
#[test]
fn the_derivative_is_taken_by_the_variable() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    for (source, terms) in [
        ("5", &[][..]),
        ("x", &[(0, "1")][..]),
        ("x^3/3 - 2*x + 7", &[(0, "-2"), (2, "1")][..]),
        ("(x + 1)^4", &[(0, "4"), (1, "12"), (2, "12"), (3, "4")][..]),
    ] {
        let polynomial = polynomial(&ring, source, c);
        let derivative = ring.derivative(&polynomial, c).unwrap();
        assert_eq!(pairs(&derivative), expected(terms), "{source}");
    }
    let input = term("(x + 1)^3", c);
    let derivative = ring.differentiate(&input, c).unwrap();
    assert_eq!(show(&derivative, c), "3 + 6*x + 3*x^2");
    let t = PolynomialRing::new(Rationals, "t", c).unwrap();
    let error = t.differentiate(&input, c).unwrap_err();
    assert_fault(&error, FaultKind::UnknownSymbol);
}

// Powers by repeated squaring agree with repeated products, $a^0 = 1$ also
// for $a = 0$, and powers of zero are zero.
#[test]
fn powers_agree_with_repeated_products() {
    let c = &mut context(wide());
    let ring = polynomial_ring("x", c);
    let base = polynomial(&ring, "x^2 - 3*x/2 + 1", c);
    let mut product = ring.one(c).unwrap();
    for exponent in 0..=17 {
        let power = ring.power(&base, exponent, c).unwrap();
        assert_eq!(pairs(&power), pairs(&product), "{exponent}");
        product = ring.multiply(&product, &base, c).unwrap();
    }
    let zero = ring.zero(c).unwrap();
    assert_eq!(
        pairs(&ring.power(&zero, 0, c).unwrap()),
        expected(&[(0, "1")])
    );
    assert!(ring.power(&zero, 5, c).unwrap().is_zero());
    let half = ring.constant(&rational(1, 2), c).unwrap();
    let power = ring.power(&half, 10, c).unwrap();
    assert_eq!(pairs(&power), expected(&[(0, "1/1024")]));
}

// Products take the operand with fewer terms as their rows, so a product of
// operands with different numbers of terms charges the same in both orders;
// with as many terms, the left operand gives the rows, and the two orders
// can charge differently.
#[test]
fn products_take_their_rows_from_the_operand_with_fewer_terms() {
    let c = &mut default_context();
    let ring = polynomial_ring("x", c);
    let small = polynomial(&ring, "x - 2", c);
    let large = polynomial(&ring, "x^9 + x^7 - x^4 + 3*x^2 + 1", c);
    let forward = work(c, |c| ring.multiply(&small, &large, c).unwrap());
    let backward = work(c, |c| ring.multiply(&large, &small, c).unwrap());
    assert_eq!(forward, backward);
    // Two rows of five products, the first row the total; the second row's
    // terms each lie between those of the total, so ten merge steps and no
    // addition.
    assert_eq!(forward, 2 + 2 * 5 * 2 + 10 + 1);
    // Two terms each: two rows of two products, the second row added to the
    // first, and the result. The rows of $x^2 + 1$ or $x^{10} + 1$ are
    // $x + 1$ and a row above it, appended in two steps, while the rows of
    // $x + 1$ interleave and are merged in four.
    let appended = 2 + 2 * 2 * 2 + 2 + 1;
    let merged = 2 + 2 * 2 * 2 + 4 + 1;
    assert_eq!((appended, merged), (13, 15));
    for source in ["x^2 + 1", "x^10 + 1"] {
        let wide_apart = polynomial(&ring, source, c);
        let linear = polynomial(&ring, "x + 1", c);
        let forward = work(c, |c| ring.multiply(&wide_apart, &linear, c).unwrap());
        let backward = work(c, |c| ring.multiply(&linear, &wide_apart, c).unwrap());
        assert_eq!((forward, backward), (appended, merged), "{source}");
        assert_eq!(
            pairs(&ring.multiply(&wide_apart, &linear, c).unwrap()),
            pairs(&ring.multiply(&linear, &wide_apart, c).unwrap())
        );
    }
}

// ---------------------------------------------------------------------------
// The answer vectors

// The non-polynomial input and the unknown symbol of the answer vectors,
// taken over from the profiles fixture: under their limits, their
// expansions fail with `NotPolynomial` and `UnknownSymbol`.
#[test]
fn rational_function_1_and_unknown_symbol_1_fail_with_their_faults() {
    for (id, fault) in [
        ("rational_function_1", FaultKind::NotPolynomial),
        ("unknown_symbol_1", FaultKind::UnknownSymbol),
    ] {
        let case = case(id);
        assert_eq!(case.operation, "expand");
        assert_eq!(case.result, format!("{fault:?}"));
        let (limits, _) = case_limits(&case);
        let error = run_case(&case, limits).unwrap_err();
        assert_fault(&error, fault);
    }
}

// The 27 expansions and derivatives of `vectors/r02.tsv` as host tests: each
// runs under its limits as one request, its result compared with the
// parsed answer through `Term::equals`, and each error by its kind and, for
// a resource limit, the field that its limits column sets.
#[test]
fn the_expand_and_diff_vectors_of_r02() {
    let selected: Vec<Case<'static>> = cases()
        .into_iter()
        .filter(|case| case.operation == "expand" || case.operation == "diff")
        .collect();
    let count = |operation: &str, result: Option<&str>| {
        selected
            .iter()
            .filter(|case| case.operation == operation)
            .filter(|case| result.is_none_or(|result| case.result == result))
            .count()
    };
    assert_eq!(selected.len(), 27);
    assert_eq!(count("expand", None), 21);
    assert_eq!(count("expand", Some("ok")), 18);
    assert_eq!(count("expand", Some("NotPolynomial")), 1);
    assert_eq!(count("expand", Some("UnknownSymbol")), 1);
    assert_eq!(count("expand", Some("ResourceLimit")), 1);
    assert_eq!(count("diff", None), 6);
    assert_eq!(count("diff", Some("ok")), 6);
    for case in &selected {
        let (limits, fields) = case_limits(case);
        match run_case(case, limits) {
            Ok(result) => {
                assert_eq!(case.result, "ok", "{}", case.id);
                let c = &mut context(wide());
                let answer = parse(case.answer, c).expect(case.id);
                assert!(
                    result.equals(&answer, c).unwrap(),
                    "{}: {} is not {}",
                    case.id,
                    show(&result, c),
                    case.answer
                );
            }
            Err(error) => {
                assert_eq!(result_name(&error), case.result, "{}: {error}", case.id);
                if error.kind() == ErrorKind::ResourceLimit {
                    let id = error.exceeded().unwrap().id().clone();
                    assert!(
                        fields.iter().any(|field| id == LimitId::Field(*field)),
                        "{}: {error}",
                        case.id
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Depth

/// $t_0 = x + 1$ and $t_{i+1} = x t_i + 1$, of depth $2i + 2$: its polynomial
/// $1 + x + \dots + x^{i+1}$ grows with the depth.
fn growing_chain(steps: usize, c: &mut Context) -> Term {
    let x = Term::symbol("x", c).unwrap();
    let one = Term::number(Rational::from(1_i64), c).unwrap();
    let mut chain = Term::sum(&[x.clone(), one.clone()], c).unwrap();
    for _ in 0..steps {
        let scaled = Term::product(&[x.clone(), chain], c).unwrap();
        chain = Term::sum(&[scaled, one.clone()], c).unwrap();
    }
    chain
}

/// $t_0 = x + 1$ and $t_{i+1} = f t_i + 1$ with
/// $f = 1 + x + x^2 - x (x + 1)$, of depth $2i + 4$: $f$ expands to 1, so
/// the polynomial of $t_i$ is $x + 1 + i$, while the term keeps every level.
fn flat_chain(steps: usize, c: &mut Context) -> Term {
    let f = parse("1 + x + x^2 - x*(x + 1)", c).unwrap();
    let one = Term::number(Rational::from(1_i64), c).unwrap();
    let mut chain = parse("x + 1", c).unwrap();
    for _ in 0..steps {
        let scaled = Term::product(&[f.clone(), chain], c).unwrap();
        chain = Term::sum(&[scaled, one.clone()], c).unwrap();
    }
    chain
}

// Terms of depth beyond 100,000 are expanded and differentiated on a thread
// with a stack of 2 MiB, with `max_depth` above their depth: a chain whose
// polynomial stays small gives its result, and a chain whose polynomial
// grows with the depth runs out of work in the middle of the visit; neither
// overflows the stack.
#[test]
fn depth_100000_chains_expand_and_differentiate_on_a_2_mib_stack() {
    on_small_stack(|| {
        let c = &mut context(wide());
        let ring = polynomial_ring("x", c);
        let flat = flat_chain(50_000, c);
        assert_eq!(flat.depth(), 100_004);
        let polynomial = ring.expand(&flat, c).unwrap();
        assert_eq!(pairs(&polynomial), expected(&[(0, "50001"), (1, "1")]));
        let derivative = ring.differentiate(&flat, c).unwrap();
        assert_eq!(show(&derivative, c), "1");
        drop(flat);

        let growing = growing_chain(50_000, c);
        assert_eq!(growing.depth(), 100_002);
        let limits = Limits::new()
            .with_max_depth(1 << 20)
            .with_max_work(1_000_000);
        let c = &mut context(limits);
        let error = ring.expand(&growing, c).unwrap_err();
        assert_limit(&error, LimitField::Work);
        // The descent through the 50,000 levels was charged before the
        // budget ran out, while the visit returned through the levels.
        assert!(c.work_used() > 500_000, "{}", c.work_used());
        let c = &mut context(limits);
        assert_limit(
            &ring.differentiate(&growing, c).unwrap_err(),
            LimitField::Work,
        );
        drop(growing);
    });
}

// The entry compares the depth of the term with `max_depth` before any
// charge: a chain of depth 100,002 under the default limits fails at once.
#[test]
fn the_entry_rejects_a_term_deeper_than_max_depth() {
    on_small_stack(|| {
        let wide_context = &mut context(wide());
        let ring = polynomial_ring("x", wide_context);
        let deep = growing_chain(50_000, wide_context);
        let c = &mut default_context();
        let error = ring.expand(&deep, c).unwrap_err();
        assert_limit(&error, LimitField::Depth);
        let exceeded = error.exceeded().unwrap();
        assert_eq!(exceeded.allowed(), 128);
        assert_eq!(exceeded.amount(), LimitAmount::Required(100_002));
        assert_eq!(exceeded.scope(), None);
        assert_limit(
            &ring.differentiate(&deep, c).unwrap_err(),
            LimitField::Depth,
        );
        assert_eq!(c.work_used(), 0);
        // A term of depth `max_depth` passes the entry, and fails it under
        // a `max_depth` one below, before any charge.
        let shallow = growing_chain(63, wide_context);
        assert_eq!(shallow.depth(), 128);
        let polynomial = ring.expand(&shallow, c).unwrap();
        assert_eq!(polynomial.degree(), Some(64));
        let c = &mut context(Limits::new().with_max_depth(127));
        let error = ring.expand(&shallow, c).unwrap_err();
        assert_limit(&error, LimitField::Depth);
        assert_eq!(
            error.exceeded().unwrap().amount(),
            LimitAmount::Required(128)
        );
        assert_eq!(c.work_used(), 0);
    });
}

// ---------------------------------------------------------------------------
// One shared implementation

/// The product rule $(a b)' = a' b + a b'$ and the commutativity of the
/// product, written once for every coefficient ring whose zero test always
/// decides, through the methods of the ring alone.
fn product_rule_holds<K>(
    ring: &PolynomialRing<K>,
    a: &Polynomial<K>,
    b: &Polynomial<K>,
    c: &mut Context,
) -> bool
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let product = ring.multiply(a, b, c).unwrap();
    let swapped = ring.multiply(b, a, c).unwrap();
    let left = ring.derivative(&product, c).unwrap();
    let first = ring
        .multiply(&ring.derivative(a, c).unwrap(), b, c)
        .unwrap();
    let second = ring
        .multiply(a, &ring.derivative(b, c).unwrap(), c)
        .unwrap();
    let right = ring.add(&first, &second, c).unwrap();
    let difference = ring.subtract(&left, &right, c).unwrap();
    let commutator = ring.subtract(&product, &swapped, c).unwrap();
    product.degrees() == swapped.degrees() && commutator.is_zero() && difference.is_zero()
}

/// $x^n$ through the methods of the ring alone: the generator and a power.
fn monomial<K>(ring: &PolynomialRing<K>, degree: u64, c: &mut Context) -> Polynomial<K>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let x = ring.generator(c).unwrap();
    ring.power(&x, degree, c).unwrap()
}

// The shared algorithms are generic over the coefficient-field trait: the
// helpers above are written for every such ring and instantiated here with
// $\mathbb{Q}$, and the polynomials of $\mathbb{Q}[x]$ have the one public
// type `Polynomial<K>`.
#[test]
fn the_shared_algorithms_are_generic_over_the_coefficient_trait() {
    let c = &mut default_context();
    let ring: PolynomialRing<Rationals> = polynomial_ring("x", c);
    let a = polynomial(&ring, "x^3 - 2*x + 1/2", c);
    let b = polynomial(&ring, "(x - 1/3)^4", c);
    assert!(product_rule_holds(&ring, &a, &b, c));
    let cube: Polynomial<Rationals> = monomial(&ring, 3, c);
    assert_eq!(pairs(&cube), expected(&[(3, "1")]));
    let three = ring
        .coefficient_ring()
        .from_integer(&Integer::from(3_i64), c)
        .unwrap();
    let scaled = ring.constant(&three, c).unwrap();
    let derivative = ring.derivative(&cube, c).unwrap();
    let square = monomial(&ring, 2, c);
    let expected_derivative = ring.multiply(&scaled, &square, c).unwrap();
    assert_eq!(pairs(&derivative), pairs(&expected_derivative));
}
