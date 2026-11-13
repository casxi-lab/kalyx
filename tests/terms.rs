//! The term core: strict numeric evaluation, the canonical-form invariants
//! with one negative example each, sums scaled by numbers and taken by their
//! primitive parts, the witnesses of negative exponents, charging and the
//! limits of construction, deep terms on a small stack, byte-stable display
//! and two defects of the earlier implementation that the term core does not
//! have. The rules are those of `docs/components/terms/contract.md`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use std::cmp::Ordering;

use kalyx::context::{CancelFlag, Storage, StorageCost};
use kalyx::number::{Integer, Rational};
use kalyx::syntax::parse;
use kalyx::term::{Term, TermKind};
use kalyx::{
    Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope, Limits,
    Span,
};

// ---------------------------------------------------------------------------
// Helpers

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

fn default_context() -> Context {
    context(Limits::new())
}

/// Limits raised far beyond every term of these tests, for the deep terms
/// and the long texts.
fn wide() -> Limits {
    Limits::new()
        .with_max_work(u64::MAX)
        .with_max_depth(1 << 20)
        .with_max_nodes(1 << 40)
        .with_max_storage_bytes(1 << 40)
        .with_max_output_bytes(u64::MAX)
}

fn symbol(name: &str, c: &mut Context) -> Term {
    Term::symbol(name, c).unwrap()
}

fn integer(value: i64, c: &mut Context) -> Term {
    Term::number(Rational::from(value), c).unwrap()
}

fn rational(numerator: i64, denominator: i64, c: &mut Context) -> Term {
    let value = Rational::new(Integer::from(numerator), Integer::from(denominator), c).unwrap();
    Term::number(value, c).unwrap()
}

fn sum(terms: &[Term], c: &mut Context) -> Term {
    Term::sum(terms, c).unwrap()
}

fn product(terms: &[Term], c: &mut Context) -> Term {
    Term::product(terms, c).unwrap()
}

fn power(base: &Term, exponent: i64, c: &mut Context) -> Term {
    base.power(exponent, c).unwrap()
}

fn show(term: &Term, c: &mut Context) -> String {
    term.display(c).unwrap()
}

fn equal(left: &Term, right: &Term, c: &mut Context) -> bool {
    left.equals(right, c).unwrap()
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

/// Rebuilds `term` bottom-up through the public constructors, from what its
/// accessors expose.
fn rebuild(term: &Term, c: &mut Context) -> Term {
    if let Some(value) = term.as_number() {
        return Term::number(value.clone(), c).unwrap();
    }
    if let Some(name) = term.as_symbol() {
        return symbol(name, c);
    }
    if let Some((base, exponent)) = term.as_power() {
        let base = rebuild(base, c);
        return power(&base, exponent, c);
    }
    if let Some((coefficient, factors)) = term.as_product() {
        let mut operands = vec![Term::number(coefficient.clone(), c).unwrap()];
        for factor in factors {
            operands.push(rebuild(factor, c));
        }
        return product(&operands, c);
    }
    let (constant, coefficients, cores) = term.as_sum().unwrap();
    let mut operands = vec![Term::number(constant.clone(), c).unwrap()];
    for (coefficient, core) in coefficients.iter().zip(cores) {
        let coefficient = Term::number(coefficient.clone(), c).unwrap();
        let core = rebuild(core, c);
        operands.push(product(&[coefficient, core], c));
    }
    sum(&operands, c)
}

/// Whether every base of `inputs` that occurs with a negative exponent
/// occurs with one in `output`.
fn keeps_negative_bases(output: &Term, inputs: &[Term], c: &mut Context) -> bool {
    let after = output.negative_bases(c).unwrap();
    for input in inputs {
        for base in input.negative_bases(c).unwrap() {
            let mut found = false;
            for kept in &after {
                found |= equal(kept, &base, c);
            }
            if !found {
                return false;
            }
        }
    }
    true
}

/// The display texts of `terms`.
fn texts(terms: &[Term], c: &mut Context) -> Vec<String> {
    terms.iter().map(|term| show(term, c)).collect()
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
// Strict numeric evaluation

// $1/0$ fails when it is built, so $0 \cdot (1/0)$ fails with it and the
// zero cannot absorb it.
#[test]
fn zero_times_one_over_zero_is_division_by_zero() {
    let c = &mut default_context();
    let zero = integer(0, c);
    let one = integer(1, c);
    let result = one
        .divide(&zero, c)
        .and_then(|quotient| Term::product(&[zero.clone(), quotient], c));
    assert_fault(&result.unwrap_err(), FaultKind::DivisionByZero);
    let literal = Rational::new(Integer::from(1_i64), Integer::from(0_i64), c);
    assert_fault(&literal.unwrap_err(), FaultKind::DivisionByZero);
}

// $(1/0)^0$ is not 1: the base fails before the exponent rule applies. A
// product with the coefficient 0 raised to a negative power fails as well.
#[test]
fn one_over_zero_to_the_zero_is_division_by_zero() {
    let c = &mut default_context();
    let zero = integer(0, c);
    let one = integer(1, c);
    let result = one
        .divide(&zero, c)
        .and_then(|quotient| quotient.power(0, c));
    assert_fault(&result.unwrap_err(), FaultKind::DivisionByZero);
    let x = symbol("x", c);
    let inverse = power(&x, -1, c);
    let zero_product = product(&[zero, inverse], c);
    assert_eq!(show(&zero_product, c), "0*x^(-1)");
    let error = zero_product.power(-1, c).unwrap_err();
    assert_fault(&error, FaultKind::DivisionByZero);
    let error = x.divide(&zero_product, c).unwrap_err();
    assert_fault(&error, FaultKind::DivisionByZero);
}

// Every negative power of zero fails.
#[test]
fn zero_to_the_minus_one_is_division_by_zero() {
    let c = &mut default_context();
    let zero = integer(0, c);
    for exponent in [-1, -2, -4096] {
        let error = zero.power(exponent, c).unwrap_err();
        assert_fault(&error, FaultKind::DivisionByZero);
    }
    let x = symbol("x", c);
    assert_fault(&x.divide(&zero, c).unwrap_err(), FaultKind::DivisionByZero);
}

// $0^0 = 1$.
#[test]
fn zero_to_the_zero_is_one() {
    let c = &mut default_context();
    let zero = integer(0, c);
    let one = power(&zero, 0, c);
    assert_eq!(one.as_number(), Some(&Rational::from(1_i64)));
    assert_eq!(show(&one, c), "1");
}

// $x / x^{2^{32}}$ fails with ResourceLimit on `max_exponent` under the
// default limits, before any charge and without a panic.
#[test]
fn x_over_x_to_the_two_to_the_32_exceeds_max_exponent() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let before = c.work_used();
    let result = x.power(1 << 32, c).and_then(|large| x.divide(&large, c));
    let error = result.unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), 4096);
    assert_eq!(exceeded.amount(), LimitAmount::Required(1 << 32));
    assert_eq!(exceeded.scope(), None);
    assert_eq!(c.work_used(), before);
    let error = x.power(-(1 << 32), c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    // A merged exponent is checked as well: $x^{4096} x$ needs 4097.
    let largest = power(&x, 4096, c);
    let error = Term::product(&[largest, x.clone()], c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(4097)
    );
}

// ---------------------------------------------------------------------------
// The canonical-form invariants, one negative example each

// Uniqueness: one canonical form for every grouping of scaled copies of one
// sum. With $s = x + y$, $a = 2s$ and $b = -s$, the sums $a + b + b$ and
// $(a + b) + b$ are both 0, and $(a + b) + (a + b)$ and $a + b + a + b$ are
// both $2x + 2y$. An implementation that kept $2s$ as one monomial with the
// core $s$, and flattened a sum core whose coefficient became 1, would give
// $x + y - (x + y)$ for $(a + b) + b$ and $2(x + y)$ for $a + b + a + b$.
#[test]
fn uniqueness_scaled_copies_of_one_sum_give_one_form_in_every_grouping() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let s = sum(&[x.clone(), y.clone()], c);
    let a = product(&[integer(2, c), s.clone()], c);
    let b = s.negate(c).unwrap();
    assert_eq!(texts(&[a.clone(), b.clone()], c), ["2*x + 2*y", "-x - y"]);
    let zero = Rational::from(0_i64);
    let flat = sum(&[a.clone(), b.clone(), b.clone()], c);
    let left = sum(&[sum(&[a.clone(), b.clone()], c), b.clone()], c);
    let right = sum(&[a.clone(), sum(&[b.clone(), b.clone()], c)], c);
    for term in [&flat, &left, &right] {
        assert_eq!(term.as_number(), Some(&zero), "{}", show(term, c));
    }
    let pair = sum(&[a.clone(), b.clone()], c);
    assert_eq!(show(&pair, c), "x + y");
    assert!(equal(&pair, &s, c));
    let flat = sum(&[a.clone(), b.clone(), a.clone(), b.clone()], c);
    let pairs = sum(&[pair.clone(), pair], c);
    let likes = sum(
        &[sum(&[a.clone(), a.clone()], c), sum(&[b.clone(), b], c)],
        c,
    );
    assert_eq!(show(&flat, c), "2*x + 2*y");
    for term in [&pairs, &likes] {
        assert_eq!(show(term, c).as_bytes(), show(&flat, c).as_bytes());
        assert!(equal(term, &flat, c));
    }
    assert!(equal(&flat, &a, c));
}

// $s - s$ is 0 for a sum $s$, however it was scaled and grouped, and its
// power $-1$ fails with DivisionByZero, as does a quotient by it. An
// implementation that kept a scaled sum as one monomial would give
// $x + y - (x + y)$ for $(2s - s) - s$, which is not 0 and has a reciprocal.
#[test]
fn a_sum_minus_itself_is_zero_and_has_no_reciprocal() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let s = sum(&[x.clone(), y], c);
    let a = product(&[integer(2, c), s.clone()], c);
    let b = s.negate(c).unwrap();
    let pair = sum(&[a.clone(), b.clone()], c);
    let again = product(&[s.clone(), integer(2, c)], c);
    let differences = [
        s.subtract(&s, c).unwrap(),
        a.subtract(&again, c).unwrap(),
        b.subtract(&b, c).unwrap(),
        pair.subtract(&s, c).unwrap(),
        sum(&[a, b.clone(), b], c),
    ];
    let zero = Rational::from(0_i64);
    for difference in &differences {
        assert_eq!(
            difference.as_number(),
            Some(&zero),
            "{}",
            show(difference, c)
        );
        let error = difference.power(-1, c).unwrap_err();
        assert_fault(&error, FaultKind::DivisionByZero);
        let error = x.divide(difference, c).unwrap_err();
        assert_fault(&error, FaultKind::DivisionByZero);
    }
}

// Uniqueness with factors of opposite sign, which never merge: an
// implementation that merged them while the exponent stays negative would
// give $x^2 x^{-1}$ on the left and $x^3 x^{-2}$ on the right.
#[test]
fn uniqueness_every_grouping_of_opposite_signs_gives_one_form() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let square = power(&x, 2, c);
    let inverse_square = power(&x, -2, c);
    let inner_left = product(&[x.clone(), inverse_square.clone()], c);
    let left = product(&[inner_left, square.clone()], c);
    let inner_right = product(&[inverse_square, square], c);
    let right = product(&[x, inner_right], c);
    assert_eq!(show(&left, c), "x^3*x^(-2)");
    assert_eq!(show(&right, c), "x^3*x^(-2)");
    assert!(equal(&left, &right, c));
}

// Idempotence: rebuilding a canonical term from its parts gives the same
// term. Scaled copies of nested sums distribute into one flat sum,
// $2 S_1 - S_1 - S_2 = a + b + c$ with $S_1 = a + 2 S_2$ and $S_2 = b + c$.
// Where the content of a sum that is a factor or a base cancels against the
// coefficient, the result is the sum or the power alone:
// $\frac{1}{2}(2b + 2c) = b + c$ and $(1 - a)^2 = (-1 + a)^2$, whose content
// $-1$ gives $(-1)^2 = 1$. An implementation that kept such a coefficient 1 as
// a product node would give terms that rebuilding changes; the product
// $1 \cdot (-1 + a)^2$ would even display the same text as the power.
#[test]
fn idempotence_a_content_that_cancels_leaves_no_product() {
    let ctx = &mut default_context();
    let (a, b, c) = (symbol("a", ctx), symbol("b", ctx), symbol("c", ctx));
    let two = integer(2, ctx);
    let inner = sum(&[b.clone(), c.clone()], ctx);
    let doubled = product(&[two.clone(), inner.clone()], ctx);
    let outer = sum(&[a.clone(), doubled.clone()], ctx);
    assert_eq!(show(&outer, ctx), "a + 2*b + 2*c");
    let twice = product(&[two, outer.clone()], ctx);
    let less_outer = outer.negate(ctx).unwrap();
    let less_inner = inner.negate(ctx).unwrap();
    let flat = sum(&[twice, less_outer, less_inner], ctx);
    assert_eq!(show(&flat, ctx), "a + b + c");
    assert!(equal(&flat, &sum(&[c, b, a.clone()], ctx), ctx));
    let halved = product(&[rational(1, 2, ctx), doubled], ctx);
    assert_eq!(halved.kind(), TermKind::Sum);
    assert!(equal(&halved, &inner, ctx));
    let difference = sum(&[integer(1, ctx), a.negate(ctx).unwrap()], ctx);
    let square = power(&difference, 2, ctx);
    assert_eq!(square.kind(), TermKind::Power);
    assert_eq!(show(&square, ctx), "(-1 + a)^2");
    let cube = power(&difference, 3, ctx);
    assert_eq!(show(&cube, ctx), "-(-1 + a)^3");
    for term in [&outer, &flat, &halved, &square, &cube] {
        let again = rebuild(term, ctx);
        assert!(equal(term, &again, ctx), "{}", show(term, ctx));
        assert_eq!(show(&again, ctx), show(term, ctx));
        assert_eq!(again.kind(), term.kind());
    }
}

// The order of terms in sums and products: monomials and factors are sorted
// in the total order, whatever the order of the operands; numbers before
// symbols, symbols before powers, powers before products and products before
// sums. An implementation that kept the order of the operands would write
// `y + x`.
#[test]
fn order_sums_and_products_sort_their_terms() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    assert_eq!(show(&sum(&[y.clone(), x.clone()], c), c), "x + y");
    assert_eq!(show(&product(&[y.clone(), x.clone()], c), c), "x*y");
    let base = sum(&[x.clone(), y.clone()], c);
    let operands = [
        power(&base, 2, c),
        product(&[x.clone(), y.clone()], c),
        power(&x, 2, c),
        y.clone(),
        x.clone(),
        integer(3, c),
    ];
    assert_eq!(
        show(&sum(&operands, c), c),
        "3 + x + y + x^2 + (x + y)^2 + x*y"
    );
    let factors = [base.clone(), power(&y, 2, c), x.clone(), power(&x, -1, c)];
    assert_eq!(show(&product(&factors, c), c), "x*x^(-1)*y^2*(x + y)");
    assert_eq!(x.compare(&y, c).unwrap(), Ordering::Less);
    let third = rational(1, 3, c);
    let half = rational(1, 2, c);
    assert_eq!(third.compare(&half, c).unwrap(), Ordering::Less);
    assert_eq!(half.compare(&x, c).unwrap(), Ordering::Less);
    assert_eq!(base.compare(&x, c).unwrap(), Ordering::Greater);
    // Symbols order by the bytes of their names, a proper prefix first.
    let names = ["b", "x_1", "ab", "x", "a", "X"].map(|name| symbol(name, c));
    assert_eq!(show(&sum(&names, c), c), "X + a + ab + b + x + x_1");
}

// Merging of like terms and coefficients: equal cores add their
// coefficients and equal bases with one sign of exponent add their
// exponents, however and wherever the operands were built. An implementation
// that compared cores by identity, or kept the order of the summands of a
// sum inside a core, would leave $2 z (x + y) + 3 z (y + x)$ as two
// monomials, and one that compared the factors of a product before taking
// the primitive parts of its sums would leave $(2x + 2y)(y + x)$ as two
// factors.
#[test]
fn merging_like_terms_and_coefficients() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let forward = sum(&[x.clone(), y.clone()], c);
    let backward = sum(&[y.clone(), x.clone()], c);
    let two = integer(2, c);
    let three = integer(3, c);
    let left = product(&[two.clone(), z.clone(), forward.clone()], c);
    let right = product(&[backward.clone(), three.clone(), z], c);
    assert_eq!(show(&sum(&[left, right], c), c), "5*z*(x + y)");
    let doubled = product(&[two.clone(), forward], c);
    let tripled = product(&[three.clone(), backward.clone()], c);
    assert_eq!(show(&sum(&[doubled.clone(), tripled], c), c), "5*x + 5*y");
    let square = product(&[doubled, backward], c);
    assert_eq!(show(&square, c), "2*(x + y)^2");
    let other_x = symbol("x", c);
    assert_eq!(show(&sum(&[x.clone(), other_x.clone()], c), c), "2*x");
    assert_eq!(show(&product(&[x.clone(), other_x], c), c), "x^2");
    let six_x = product(&[two.clone(), product(&[three.clone(), x.clone()], c)], c);
    assert_eq!(show(&six_x, c), "6*x");
    let fifth = product(&[power(&x, 2, c), power(&x, 3, c)], c);
    assert_eq!(show(&fifth, c), "x^5");
    let fractions = sum(&[rational(1, 2, c), rational(1, 3, c)], c);
    assert_eq!(show(&fractions, c), "5/6");
    let spread = product(&[two, x.clone(), three, y], c);
    assert_eq!(show(&spread, c), "6*x*y");
}

// The elimination of 0 and 1: a zero summand, a factor 1, the exponent 1 and
// a sum or product left with one part disappear, and so do $0 \cdot x$ and
// $x - x$ without negative powers. An implementation that kept them would
// not write `y`.
#[test]
fn elimination_of_zero_and_one() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let zero = integer(0, c);
    let one = integer(1, c);
    let operands = [
        product(&[zero.clone(), x.clone()], c),
        product(&[one.clone(), y.clone(), one.clone()], c),
        power(&x, 0, c),
        integer(-1, c),
    ];
    let result = sum(&operands, c);
    assert_eq!(show(&result, c), "y");
    assert!(equal(&result, &y, c));
    assert!(equal(&power(&x, 1, c), &x, c));
    assert!(equal(&product(&[one, x.clone()], c), &x, c));
    assert!(equal(&sum(&[x.clone(), zero], c), &x, c));
    assert_eq!(show(&x.subtract(&x, c).unwrap(), c), "0");
    assert_eq!(show(&sum(&[], c), c), "0");
    assert_eq!(show(&product(&[], c), c), "1");
}

// Integer powers and the negative-exponent invariant: a base that occurs
// with a negative exponent is never lost. An implementation that cancelled
// would write `x`, `1`, `x`, `0` and `1` for the first five.
#[test]
fn integer_powers_keep_every_negative_base() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let zero = integer(0, c);
    let inverse = power(&x, -1, c);
    let square = power(&x, 2, c);
    let cases = [
        (product(&[square.clone(), inverse.clone()], c), "x^2*x^(-1)"),
        (product(&[x.clone(), inverse.clone()], c), "x*x^(-1)"),
        (power(&inverse, -1, c), "(x^(-1))^(-1)"),
        (product(&[zero.clone(), inverse.clone()], c), "0*x^(-1)"),
        (power(&inverse, 0, c), "(x^(-1))^0"),
        (product(&[inverse.clone(), power(&x, -2, c)], c), "x^(-3)"),
        (power(&power(&inverse, 0, c), -1, c), "(x^(-1))^0"),
        (power(&power(&inverse, 0, c), 5, c), "(x^(-1))^0"),
        (power(&inverse, 2, c), "x^(-2)"),
        (power(&square, -1, c), "x^(-2)"),
        (inverse.subtract(&inverse, c).unwrap(), "0*x^(-1)"),
    ];
    for (term, text) in &cases {
        assert_eq!(show(term, c), *text);
        assert!(term.has_negative_power(), "{text}");
        assert!(
            keeps_negative_bases(term, std::slice::from_ref(&inverse), c),
            "{text}"
        );
    }
    // Powers of one sign merge, and powers distribute over products.
    assert_eq!(show(&power(&square, 3, c), c), "x^6");
    let two_x_y = product(&[integer(2, c), x.clone(), y.clone()], c);
    assert_eq!(show(&power(&two_x_y, -1, c), c), "1/2*x^(-1)*y^(-1)");
    let five = integer(5, c);
    let negated = inverse.negate(c).unwrap();
    let kept = sum(&[inverse.clone(), five, negated], c);
    assert_eq!(show(&kept, c), "5 + 0*x^(-1)");
    // A witness that the other factors cover disappears.
    let one = power(&inverse, 0, c);
    assert_eq!(
        show(&product(&[one.clone(), inverse.clone()], c), c),
        "x^(-1)"
    );
    assert_eq!(show(&product(&[one, y], c), c), "y*(x^(-1))^0");
}

// ---------------------------------------------------------------------------
// Witnesses of negative exponents

// A witness keeps only the maximal bases: a base that occurs with a negative
// exponent inside another base is kept through it. In
// $0 \cdot (y + x^{-1})^{-1} x^{-1}$ the base $x$ occurs inside
// $y + x^{-1}$, so the zero product needs only the factor of the larger
// base, and both bases are still there.
#[test]
fn witnesses_keep_only_the_maximal_bases() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let zero = integer(0, c);
    let inverse = power(&x, -1, c);
    let shifted = sum(&[inverse.clone(), y.clone()], c);
    let outer = power(&shifted, -1, c);
    let operands = [zero, outer.clone(), inverse.clone()];
    let zero_product = product(&operands, c);
    let one = power(&outer, 0, c);
    let cancelled = outer.subtract(&outer, c).unwrap();
    let kept = sum(&[cancelled.clone(), x.clone()], c);
    assert_eq!(
        texts(&[zero_product.clone(), one.clone(), cancelled.clone()], c),
        [
            "0*(y + x^(-1))^(-1)",
            "((y + x^(-1))^(-1))^0",
            "0*(y + x^(-1))^(-1)"
        ]
    );
    assert_eq!(show(&kept, c), "x + 0*(y + x^(-1))^(-1)");
    for term in [&zero_product, &one, &cancelled, &kept] {
        let bases = term.negative_bases(c).unwrap();
        assert_eq!(texts(&bases, c), ["x", "y + x^(-1)"]);
        assert!(keeps_negative_bases(term, &operands, c));
    }
    // A witness factor that another factor covers is dropped, and one that
    // no factor covers is kept with its base.
    let covered = product(&[one.clone(), outer.clone()], c);
    assert_eq!(show(&covered, c), "(y + x^(-1))^(-1)");
    let uncovered = product(&[one, inverse], c);
    assert_eq!(show(&uncovered, c), "x^(-1)*((y + x^(-1))^(-1))^0");
}

// A witness keeps a base that is a sum by its primitive part:
// $(2x + 2y)^{-1} = \frac{1}{2} (x + y)^{-1}$, so
// $0 \cdot (2x + 2y)^{-1} = 0 \cdot (x + y)^{-1}$, and
// $(2x + 2y)^{-1} (x + y)$ keeps both factors of the base $x + y$. The sum
// and its primitive part are 0 at the same points, so $N$ of each result is
// $\{x + y\}$.
#[test]
fn witnesses_keep_a_sum_base_by_its_primitive_part() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let pair = sum(&[x.clone(), y.clone()], c);
    let doubled = product(&[integer(2, c), pair.clone()], c);
    let inverse = power(&doubled, -1, c);
    assert_eq!(show(&inverse, c), "1/2*(x + y)^(-1)");
    let cancelled = inverse.subtract(&inverse, c).unwrap();
    let cases = [
        (
            product(&[integer(0, c), inverse.clone()], c),
            "0*(x + y)^(-1)",
        ),
        (
            product(&[inverse.clone(), pair.clone()], c),
            "1/2*(x + y)*(x + y)^(-1)",
        ),
        (cancelled.clone(), "0*(x + y)^(-1)"),
        (power(&inverse, 0, c), "((x + y)^(-1))^0"),
        (sum(&[cancelled, integer(5, c)], c), "5 + 0*(x + y)^(-1)"),
        (x.divide(&doubled, c).unwrap(), "1/2*x*(x + y)^(-1)"),
    ];
    for (term, text) in &cases {
        assert_eq!(show(term, c), *text);
        assert_eq!(texts(&term.negative_bases(c).unwrap(), c), ["x + y"]);
        assert!(keeps_negative_bases(
            term,
            std::slice::from_ref(&inverse),
            c
        ));
    }
    let zero_product = &cases[0].0;
    let (coefficient, factors) = zero_product.as_product().unwrap();
    assert!(coefficient.is_zero());
    let (base, exponent) = factors[0].as_power().unwrap();
    assert!(equal(base, &pair, c));
    assert_eq!(exponent, -1);
}

// A sum that is a factor or a base is primitive: its content, the
// coefficient of its first monomial whose coefficient is not 0, joins the
// coefficient of the product, or comes out of the power as $c^k$:
// $(2x + 2y) z = 2 (x + y) z$, $(2x + 2y)^2 = 4 (x + y)^2$,
// $(1 - x)^{-1} = -(x - 1)^{-1}$ and $(3x + 2y) z = 3 (x + \frac{2}{3} y) z$.
// A sum whose only monomial is a witness has its constant as its content.
#[test]
fn sums_as_factors_and_bases_are_primitive() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let pair = sum(&[x.clone(), y.clone()], c);
    let two_x = product(&[integer(2, c), x.clone()], c);
    let two_y = product(&[integer(2, c), y.clone()], c);
    let doubled = sum(&[two_x, two_y.clone()], c);
    assert_eq!(show(&doubled, c), "2*x + 2*y");
    let one_minus_x = sum(&[integer(1, c), x.negate(c).unwrap()], c);
    let three_x = product(&[integer(3, c), x.clone()], c);
    let unbalanced = sum(&[two_y, three_x], c);
    let factor = product(&[doubled.clone(), z.clone()], c);
    let square = power(&doubled, 2, c);
    let reciprocal = power(&one_minus_x, -1, c);
    let fraction = product(&[unbalanced, z.clone()], c);
    assert_eq!(
        texts(
            &[factor.clone(), square.clone(), reciprocal.clone(), fraction],
            c
        ),
        [
            "2*z*(x + y)",
            "4*(x + y)^2",
            "-(-1 + x)^(-1)",
            "3*z*(x + 2/3*y)"
        ]
    );
    let expected = product(&[integer(2, c), z.clone(), pair.clone()], c);
    assert!(equal(&factor, &expected, c));
    let expected = product(&[integer(4, c), power(&pair, 2, c)], c);
    assert!(equal(&square, &expected, c));
    let (coefficient, factors) = reciprocal.as_product().unwrap();
    assert_eq!(coefficient, &Rational::from(-1_i64));
    let (base, exponent) = factors[0].as_power().unwrap();
    assert_eq!((show(base, c), exponent), (String::from("-1 + x"), -1));
    // A coefficient that meets a lone sum distributes over it again.
    assert!(equal(
        &product(&[rational(1, 2, c), doubled.clone()], c),
        &pair,
        c
    ));
    assert!(equal(
        &product(std::slice::from_ref(&doubled), c),
        &doubled,
        c
    ));
    assert!(equal(&power(&doubled, 1, c), &doubled, c));
    // $5 + 0 \cdot x^{-1}$ has the content 5.
    let inverse = power(&x, -1, c);
    let cancelled = inverse.subtract(&inverse, c).unwrap();
    let constant = sum(&[integer(5, c), cancelled], c);
    assert_eq!(show(&constant, c), "5 + 0*x^(-1)");
    assert_eq!(
        texts(
            &[product(&[constant.clone(), z], c), power(&constant, -1, c),],
            c
        ),
        ["5*z*(1 + 0*x^(-1))", "1/5*(1 + 0*x^(-1))^(-1)"]
    );
}

// ---------------------------------------------------------------------------
// Charging and the limits of construction

// Every construction charges the context, and an exhausted work budget ends
// the construction with ResourceLimit naming `max_work`.
#[test]
fn an_exhausted_work_budget_is_a_resource_limit() {
    let c = &mut context(Limits::new().with_max_work(60));
    let x = symbol("x", c);
    let mut term = x.clone();
    let mut last = c.work_used();
    let error = loop {
        let one = match Term::number(Rational::from(1_i64), c) {
            Ok(one) => one,
            Err(error) => break error,
        };
        assert!(c.work_used() > last);
        last = c.work_used();
        match Term::sum(&[term.clone(), one], c) {
            Ok(next) => term = next,
            Err(error) => break error,
        }
        assert!(c.work_used() > last);
        last = c.work_used();
    };
    assert_limit(&error, LimitField::Work);
    assert_eq!(error.exceeded().unwrap().allowed(), 60);
    assert!(c.work_used() <= 60);
}

/// $t_{i+1} = x t_i + 1$, two levels per step from $t_0 = x + 1$.
fn chain(steps: usize, c: &mut Context) -> Term {
    let x = symbol("x", c);
    let one = integer(1, c);
    let mut term = sum(&[x.clone(), one.clone()], c);
    for _ in 0..steps {
        let scaled = product(&[x.clone(), term], c);
        term = sum(&[scaled, one.clone()], c);
    }
    term
}

/// $x^{-1}$ raised to $-1$ again and again: one level per step.
fn nested_inverses(steps: usize, c: &mut Context) -> Term {
    let mut term = symbol("x", c);
    for _ in 0..steps {
        term = power(&term, -1, c);
    }
    term
}

// Terms of depth 100,000 are built, compared, displayed and dropped on a
// thread with a stack of 2 MiB: every traversal runs over a stack on the
// heap, and `Debug` shows one node. As convention 15 asks, `max_depth` is set
// above the tested depth.
#[test]
fn depth_100000_terms_build_compare_display_and_drop_on_a_2_mib_stack() {
    on_small_stack(|| {
        let c = &mut context(wide());
        let first = chain(50_000, c);
        let second = chain(50_000, c);
        assert_eq!(first.depth(), 100_002);
        assert_eq!(first.compare(&second, c).unwrap(), Ordering::Equal);
        let shorter = chain(49_999, c);
        assert_eq!(shorter.compare(&first, c).unwrap(), Ordering::Less);
        let text = show(&first, c);
        assert!(text.starts_with("1 + x*(1 + x*(1 + x*("), "{}", &text[..40]);
        assert_eq!(text.len(), 5 + 8 * 50_000);
        let shallow = format!("{first:?}");
        assert_eq!(
            shallow,
            "Term { kind: Sum, children: 1, size: 150002, depth: 100002, .. }"
        );
        drop(first);
        drop(second);
        drop(shorter);

        let deep = nested_inverses(100_000, c);
        let other = nested_inverses(100_000, c);
        assert_eq!(deep.depth(), 100_001);
        assert!(deep.has_negative_power());
        assert_eq!(deep.compare(&other, c).unwrap(), Ordering::Equal);
        let text = show(&deep, c);
        assert!(text.ends_with(")^(-1))^(-1)"));
        assert_eq!(text.len(), 6 + 7 * 99_999);
        drop(deep);
        drop(other);
    });
}

// The limits of construction: the tree size and the logical bytes of every
// new node are checked with `check_storage` at scope `Value`, together with
// the open frames and the reserved temporaries, and its depth against
// `max_depth`; a node that a check rejects charges nothing.
#[test]
fn nodes_storage_bytes_and_depth_are_checked_before_a_node_is_built() {
    let wide_open = &mut default_context();
    let names = ["x", "y", "z", "w"].map(|name| symbol(name, wide_open));

    let c = &mut context(Limits::new().with_max_nodes(4));
    let error = Term::sum(&names, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.allowed(), 4);
    assert_eq!(exceeded.amount(), LimitAmount::Required(5));
    let c = &mut context(Limits::new().with_max_nodes(5));
    assert_eq!(Term::sum(&names, c).unwrap().size(), 5);

    let c = &mut context(Limits::new().with_max_storage_bytes(3));
    let before = c.work_used();
    let error = Term::symbol("abcd", c).unwrap_err();
    assert_limit(&error, LimitField::StorageBytes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.amount(), LimitAmount::Required(4));
    assert_eq!(c.work_used(), before);
    assert!(Term::symbol("abc", c).is_ok());

    // Both exceeded: the nodes are reported.
    let c = &mut context(Limits::new().with_max_nodes(1).with_max_storage_bytes(1));
    let error = Term::sum(&names, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);

    // The open frames and the reserved temporaries count: three nodes of a
    // frame and a sum of three nodes exceed five, until the frame is left.
    let c = &mut context(Limits::new().with_max_nodes(5));
    let frame = c.enter_frame().unwrap();
    c.set_frame_cost(&frame, Storage::new(3, 0)).unwrap();
    let pair = [names[0].clone(), names[1].clone()];
    let error = Term::sum(&pair, c).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(error.exceeded().unwrap().scope(), Some(LimitScope::Value));
    c.leave_frame(frame);
    assert!(Term::sum(&pair, c).is_ok());
    // The sum $x + y$ is 6 bytes: with 5 reserved, it does not fit in 10.
    let c = &mut context(Limits::new().with_max_storage_bytes(10));
    let reserved = c.reserve(Storage::new(0, 5)).unwrap();
    let error = Term::sum(&pair, c).unwrap_err();
    assert_limit(&error, LimitField::StorageBytes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.amount(), LimitAmount::Required(11));
    c.release(reserved);
    assert_eq!(Term::sum(&pair, c).unwrap().storage(), Storage::new(3, 6));

    let c = &mut context(Limits::new().with_max_depth(3));
    let x = symbol("x", c);
    let twice = power(&power(&x, -1, c), -1, c);
    assert_eq!(twice.depth(), 3);
    let before = c.work_used();
    let error = twice.power(-1, c).unwrap_err();
    assert_limit(&error, LimitField::Depth);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), None);
    assert_eq!(exceeded.allowed(), 3);
    assert_eq!(exceeded.amount(), LimitAmount::Required(4));
    // The exponent check and the step of the power are charged, the
    // rejected node is not.
    assert_eq!(c.work_used() - before, 1);
    // The depth is checked before the storage: with both exceeded, the
    // depth is reported.
    let c = &mut context(Limits::new().with_max_depth(1).with_max_nodes(1));
    let error = Term::sum(&pair, c).unwrap_err();
    assert_limit(&error, LimitField::Depth);
}

/// The work that `step` charges to `c`.
fn work(c: &mut Context, step: impl FnOnce(&mut Context)) -> u64 {
    let before = c.work_used();
    step(c);
    c.work_used() - before
}

// The rows of the charge table on small constructions, worked out from the
// table: the operands of the work lists, the sort and the merge, the removal
// of zero monomials, the collection of the remaining cores and the split of
// a sum, the factors of a product and their keys when ones join them, a node
// and its children, the merges of a power of a power, the factors of a power
// of a product, the exponent 1, and the collection of negative bases with
// its inner bases and the set differences.
#[test]
fn construction_steps_charge_the_amounts_of_the_charge_table() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let inverse = power(&x, -1, c);
    let one = power(&inverse, 0, c);
    let minus_x = x.negate(c).unwrap();
    let minus_inverse = inverse.negate(c).unwrap();
    let pair = [x.clone(), y.clone()];
    let xy = product(&pair, c);
    // 2 operands, a sort of 2 items (2 placed and 1 comparison of 2 units),
    // a merge (2 items and 1 comparison), the removal of zero monomials 2,
    // the split 2, and a node with 2 children 3.
    assert_eq!(work(c, |c| drop(sum(&pair, c))), 17);
    // 2 operands, the sort 4, the merge 4, the factors of the merged items
    // 2, and a node with 2 children 3.
    assert_eq!(work(c, |c| drop(product(&pair, c))), 15);
    // 1, one merge of a power of a power, and a node with 1 child 2.
    assert_eq!(work(c, |c| drop(power(&inverse, 2, c))), 4);
    // The exponent 1 gives the base: 1.
    assert_eq!(work(c, |c| drop(power(&xy, 1, c))), 1);
    // 1, the power $1^2$ of the coefficient 4, 1 and a node with 1 child per
    // factor 6, and the product of the two powers 19.
    assert_eq!(work(c, |c| drop(power(&xy, 2, c))), 30);
    // 2 nodes visited and 1 base merged.
    assert_eq!(work(c, |c| drop(inverse.negative_bases(c).unwrap())), 3);
    // 1; $N$ with its inner bases 3 (2 nodes visited, 1 base merged and no
    // inner base); $\max N$, the set difference of 1 element, 1; the
    // reciprocal 2 and the one 2.
    assert_eq!(work(c, |c| drop(power(&inverse, 0, c))), 9);
    // $((x^{-1})^{-1})^0$: 1; $N$ with its inner bases 10 (3 nodes visited,
    // the sort and merge of the 2 bases 6 and of the 1 inner base 1);
    // $\max N$, the set difference of 2 elements with comparisons of 2 units
    // and 1 unit, 5; the reciprocal 2 and the one 2.
    let nested = power(&inverse, -1, c);
    assert_eq!(work(c, |c| drop(power(&nested, 0, c))), 20);
    // $x + y - x$: 3 operands; a sort of 3 items 12 (6 placed and 3
    // comparisons of 2 units); the merge 8 (3 items, 2 comparisons of 2 units
    // and the sum of two coefficients); the removal of zero monomials 2; and
    // $N$ of the cancelled core, 1 node visited. It has no negative base, so
    // the remaining cores are not collected, and $y$ alone is the sum.
    let operands = [x.clone(), y.clone(), minus_x];
    assert_eq!(work(c, |c| drop(sum(&operands, c))), 26);
    // $x^{-1} + y - x^{-1}$: 3 operands; the sort 14 (6 placed and
    // comparisons of 1, 1 and 6 units, the last of two equal powers: the
    // powers 1, the cursor of their bases 1, the bases 2, the cursor past
    // them 1 and the exponents 1); the merge 11 (3 items, comparisons of 1
    // and 6 units and the sum of two coefficients); the removal of zero
    // monomials 2; $N$ of the cancelled core with its inner bases 3, the
    // collection of the remaining core 1, its $N$ 1 and two set differences
    // of 1 element 2; the witness core, a reciprocal, 2 and its place, found
    // by 1 comparison of 1 step; the split 2 and a node with 2 children 3.
    let operands = [inverse.clone(), y.clone(), minus_inverse];
    assert_eq!(work(c, |c| drop(sum(&operands, c))), 45);
    // $(x^{-1})^0 y$: 2 operands; the merge of 1 item 1; the factors of the
    // merged items 1; $N$ of the one with its inner bases 4 (3 nodes visited
    // and 1 base merged); $N$ of the factors 1; two set differences of 1
    // element 2; the one, a reciprocal and its power, 4; the keys of the 2
    // factors 2 and their sort 3 (2 placed and 1 comparison of 1 step); and a
    // node with 2 children 3.
    assert_eq!(work(c, |c| drop(product(&[one.clone(), y.clone()], c))), 23);
}

// The rows of the charge table for sums as factors and bases, worked out
// from the table: the content of a sum, the inverse of a content other than
// 1, the scaling of a sum by a number, the product of a content and a
// coefficient, also the coefficient 0, the power of a content, the power of
// a product with a sum among its factors, and the assembly of a product with
// one factor, which scales a sum for a coefficient other than 0 and 1 only.
#[test]
fn scaling_and_primitive_parts_charge_the_amounts_of_the_charge_table() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let two = integer(2, c);
    let pair = sum(&[x.clone(), y.clone()], c);
    let doubled = product(&[two.clone(), pair.clone()], c);
    // $2 (x + y)$: 2 operands; the coefficient 2, as a product with 1, 1;
    // the content 1 of the sum 1 and its product with the coefficient 1; the
    // merge of 1 item 1; the factors of the merged items 1; the scaling of
    // the sum by 2: the constant 1, and 1 and the product 1 for each of its
    // 2 monomials 4; and a node with 2 children 3.
    assert_eq!(
        work(c, |c| drop(product(&[two.clone(), pair.clone()], c))),
        15
    );
    // $-(x + y)$: 1 operand; the content 1 of the sum 1 and its product with
    // the coefficient $-1$ 1; the merge 1; the factors 1; the scaling by $-1$:
    // the constant 1 and 2 for each of 2 monomials 4; and a node 3.
    assert_eq!(work(c, |c| drop(pair.negate(c).unwrap())), 13);
    // $(2x + 2y) z$: 2 operands; the content 2 of the sum 1, its inverse 1,
    // the scaling of the sum by $1/2$ 8 (the constant 1, 2 for each of 2
    // monomials, and a node with 2 children 3), and the product of the
    // content and the coefficient 1; a sort of 2 items 3 (2 placed and 1
    // comparison of 1 step) and their merge 3 (2 items and 1 comparison); the
    // factors 2; and a node with 2 children 3.
    let operands = [doubled.clone(), z.clone()];
    assert_eq!(work(c, |c| drop(product(&operands, c))), 24);
    // $(2x + 2y)^2$: 1; the content 2, its inverse and the scaling by $1/2$
    // 10; $2^2$ as `Rational::power` 4; the power node 2; and the product
    // node 2.
    assert_eq!(work(c, |c| drop(power(&doubled, 2, c))), 19);
    // $(x + y)^2$: 1; the content 1 of the sum 1; and the power node 2.
    assert_eq!(work(c, |c| drop(power(&pair, 2, c))), 4);
    // $(x + y) / 2$: the power $2^{-1}$ 5 (1, `Rational::power` 3 and the
    // number node 1); 2 operands; the content 1 of the sum 1 and its product
    // with the coefficient 1; the product of the coefficient and $1/2$ 1; the
    // merge 1; the factors 1; the scaling of the sum by $1/2$: the constant 1
    // and 2 for each of 2 monomials 4; and a node with 2 children 3.
    assert_eq!(work(c, |c| drop(pair.divide(&two, c).unwrap())), 20);
    // $\frac{1}{2} (2x + 2y)$: 2 operands; the coefficient $1/2$, as a
    // product with 1, 1; the content 2 of the sum 1, its inverse 1, the
    // scaling of the sum by $1/2$ 8 and the product of the content and $1/2$
    // 1; the merge 1; the factors 1; and the coefficient 1 with the single
    // sum gives that sum, with no scaling and no node.
    let half = rational(1, 2, c);
    let operands = [half, doubled.clone()];
    assert_eq!(work(c, |c| drop(product(&operands, c))), 16);
    // $x + y$ alone: 1 operand; the content 1 of the sum 1 and its product
    // with the coefficient 1; the merge 1; the factors 1; and the sum itself.
    assert_eq!(
        work(c, |c| drop(product(std::slice::from_ref(&pair), c))),
        5
    );
    // $(z (x + y))^2$: 1; the power $1^2$ of the coefficient 4; 1 and a node
    // with 1 child per factor 6, with no content for the factor $x + y$,
    // which is primitive; and the product of the two powers 17 (2 operands,
    // a sort of 2 items 3 and their merge 3, each with 1 comparison of 1
    // step, the factors 6 and a node with 2 children 3).
    let z_pair = product(&[z.clone(), pair.clone()], c);
    assert_eq!(work(c, |c| drop(power(&z_pair, 2, c))), 28);
    // $0 (2x + 2y)$: 2 operands; the coefficient 0, as a product with 1, 1;
    // the content 2 of the sum 1, its inverse 1, the scaling of the sum by
    // $1/2$ 8 and the product of the content and 0 1, as for any other
    // coefficient; the merge 1; the factors 1; $N$ of the factor, 1 node
    // visited; and the number 0 1.
    let zero = integer(0, c);
    let operands = [zero, doubled.clone()];
    assert_eq!(work(c, |c| drop(product(&operands, c))), 18);
}

// Sharing does not bypass `max_nodes`: a term whose tree doubles at every
// step while its nodes are shared is checked by its tree size, and is
// rejected once that exceeds the limit.
#[test]
fn shared_subterms_count_once_per_occurrence_against_max_nodes() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let mut term = product(&[x.clone(), y.clone()], c);
    let mut steps = 0;
    let error = loop {
        let left = sum(&[term.clone(), x.clone()], c);
        let right = sum(&[term.clone(), y.clone()], c);
        match Term::product(&[left, right], c) {
            Ok(next) => term = next,
            Err(error) => break error,
        }
        steps += 1;
    };
    assert_eq!(steps, 10);
    assert_eq!(term.size(), 8187);
    assert_limit(&error, LimitField::Nodes);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.scope(), Some(LimitScope::Value));
    assert_eq!(exceeded.amount(), LimitAmount::Required(2 * 8187 + 5));
}

// The term formula: the tree size in nodes, and the bytes of the canonical
// binary rendering, where a number counts as a rational, a symbol its bytes
// and each binary sum, product or power 4.
#[test]
fn the_storage_formula_of_terms() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    assert_eq!(rational(3, 4, c).storage(), Storage::new(1, 2 + 3 + 3));
    assert_eq!(integer(0, c).storage(), Storage::new(1, 4));
    assert_eq!(symbol("xy", c).storage(), Storage::new(1, 2));
    let square = power(&x, 2, c);
    assert_eq!(square.storage(), Storage::new(2, 1 + 6 + 4));
    // c x^k with c != 1 and k >= 2 costs rb(c) + l + |k| + 12.
    let three = integer(3, c);
    let scaled = product(&[three.clone(), square], c);
    assert_eq!(scaled.storage(), Storage::new(3, 6 + 1 + 2 + 12));
    // xy costs l_x + l_y + 4.
    assert_eq!(
        product(&[x.clone(), y.clone()], c).storage(),
        Storage::new(3, 6)
    );
    let one = integer(1, c);
    assert_eq!(
        sum(&[one, x.clone()], c).storage(),
        Storage::new(2, 5 + 1 + 4)
    );
    let two = integer(2, c);
    let left = product(&[two, x.clone()], c);
    let right = product(&[three, y], c);
    let linear = sum(&[left, right], c);
    assert_eq!(linear.storage(), Storage::new(3, (1 + 6 + 4) * 2 + 4));
    let inverse = power(&x, -1, c);
    assert_eq!(inverse.storage(), Storage::new(2, 1 + 5 + 4));
    assert_eq!(power(&inverse, 0, c).storage(), Storage::new(3, 10 + 4 + 4));
    let zero = integer(0, c);
    let zero_product = product(&[zero, inverse], c);
    assert_eq!(zero_product.storage(), Storage::new(3, 4 + 10 + 4));
    // A shared subterm counts once per occurrence.
    let base = sum(&[x.clone(), symbol("y", c)], c);
    let shared = product(&[power(&base, 2, c), power(&base, -1, c)], c);
    assert_eq!(shared.size(), 1 + 4 + 4);
}

// An exponent is an `i64`: under a `max_exponent` beyond its width, an
// exponent whose magnitude exceeds $2^{63} - 1$ names `max_exponent` with
// the effective value $2^{63} - 1$.
#[test]
fn exponents_beyond_the_width_of_i64_are_resource_limits() {
    let c = &mut context(Limits::new().with_max_exponent(u64::MAX));
    let width = i64::MAX as u64;
    let x = symbol("x", c);
    assert!(x.power(i64::MAX, c).is_ok());
    assert!(x.power(-i64::MAX, c).is_ok());
    let half = power(&x, 1 << 62, c);
    let error = Term::product(&[half.clone(), half], c).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), width);
    assert_eq!(exceeded.amount(), LimitAmount::Required(1 << 63));
    let error = x.power(i64::MIN, c).unwrap_err();
    assert_eq!(error.exceeded().unwrap().allowed(), width);
    let large = power(&x, 1 << 32, c);
    let error = large.power(1 << 31, c).unwrap_err();
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(1 << 63)
    );
}

// A term built under one context is checked against the limits of the
// context that receives it: its numbers against `max_integer_bits`, and its
// tree size and depth as a part of every node built on it.
#[test]
fn terms_are_checked_against_the_receiving_limits() {
    let c = &mut default_context();
    let large = Rational::from(2_i64).power(99, c).unwrap();
    let term = Term::number(large.clone(), c).unwrap();
    let narrow = &mut context(Limits::new().with_max_integer_bits(64));
    assert_limit(
        &Term::number(large, narrow).unwrap_err(),
        LimitField::IntegerBits,
    );
    assert_limit(&term.display(narrow).unwrap_err(), LimitField::IntegerBits);
    let x = symbol("x", c);
    // A number taken over unchanged, as $1 \cdot c$ or $0 + c$, is checked
    // as well.
    assert_limit(
        &Term::product(&[term.clone(), x.clone()], narrow).unwrap_err(),
        LimitField::IntegerBits,
    );
    assert_limit(
        &Term::sum(&[term.clone(), x.clone()], narrow).unwrap_err(),
        LimitField::IntegerBits,
    );
    let scaled = product(&[term, x.clone()], c);
    assert_limit(
        &Term::sum(&[scaled, x.clone()], narrow).unwrap_err(),
        LimitField::IntegerBits,
    );

    let pair = sum(&[x.clone(), symbol("y", c)], c);
    let z = symbol("z", c);
    let small = &mut context(Limits::new().with_max_nodes(4));
    let error = Term::product(&[pair.clone(), z], small).unwrap_err();
    assert_limit(&error, LimitField::Nodes);
    assert_eq!(error.exceeded().unwrap().amount(), LimitAmount::Required(5));
    let shallow = &mut context(Limits::new().with_max_depth(2));
    let error = pair.power(2, shallow).unwrap_err();
    assert_limit(&error, LimitField::Depth);
}

// Equal numbers never make the order of terms exceed `max_integer_bits`:
// $E = (N + 1)/(N - 1)$ with $N = 2^{2048}$, whose difference with itself
// needs 4098 bits, and $E x$, each read twice from their text under the
// default limits, are equal and compare `Equal`.
#[test]
fn terms_with_equal_numbers_beyond_half_the_bit_limit_are_equal() {
    let c = &mut default_context();
    let n = Rational::from(2_i64).power(2048, c).unwrap();
    let above = n.add(&Rational::from(1_i64), c).unwrap();
    let below = n.subtract(&Rational::from(1_i64), c).unwrap();
    let e = format!("{above}/{below}");
    for source in [e.clone(), format!("{e}*x")] {
        let first = parse(&source, c).unwrap();
        let second = parse(&source, c).unwrap();
        assert!(first.equals(&second, c).unwrap(), "{source}");
        assert_eq!(first.compare(&second, c).unwrap(), Ordering::Equal);
    }
}

// A scaled sum and the primitive part of a sum are checked as every term is:
// each scaled coefficient and the inverse of a content against
// `max_integer_bits` when it is computed, and the new sum node against
// `max_nodes` at scope `Value` and against `max_depth` before it is
// allocated.
#[test]
fn scaled_sums_and_primitive_parts_are_checked_before_they_are_built() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let pair = sum(&[x.clone(), y.clone()], c);
    let doubled = product(&[integer(2, c), pair.clone()], c);
    let two = integer(2, c);
    let large = Term::number(Rational::from(2_i64).power(40, c).unwrap(), c).unwrap();
    let scaled_y = product(&[large.clone(), y.clone()], c);
    let mixed = sum(&[x.clone(), scaled_y], c);
    let huge = Term::number(Rational::from(2_i64).power(99, c).unwrap(), c).unwrap();
    let steep = sum(&[product(&[huge, x.clone()], c), y.clone()], c);

    // $2^{40} (x + 2^{40} y)$ needs a coefficient of 81 bits.
    let narrow = &mut context(Limits::new().with_max_integer_bits(64));
    let error = Term::product(&[large, mixed], narrow).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    // The content $2^{99}$ of $2^{99} x + y$ is inverted under the receiving
    // limit.
    let error = Term::product(&[steep, z.clone()], narrow).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);

    // The scaled sum $2x + 2y$ and the primitive part $x + y$ of $2x + 2y$
    // are nodes of 3, beyond `max_nodes` 2.
    let small = &mut context(Limits::new().with_max_nodes(2));
    for result in [
        Term::product(&[two.clone(), pair.clone()], small),
        Term::product(&[doubled.clone(), z.clone()], small),
        doubled.power(2, small),
    ] {
        let error = result.unwrap_err();
        assert_limit(&error, LimitField::Nodes);
        let exceeded = error.exceeded().unwrap();
        assert_eq!(exceeded.scope(), Some(LimitScope::Value));
        assert_eq!(exceeded.amount(), LimitAmount::Required(3));
    }
    // Their depth 2 is beyond `max_depth` 1.
    let shallow = &mut context(Limits::new().with_max_depth(1));
    let error = Term::product(&[two, pair], shallow).unwrap_err();
    assert_limit(&error, LimitField::Depth);
    let error = doubled.negate(shallow).unwrap_err();
    assert_limit(&error, LimitField::Depth);
}

// The start 1 of a product and 0 of a sum, and the -1 of a negation, add no
// bits: a number of exactly `max_integer_bits` bits passes through them.
#[test]
fn numbers_of_max_integer_bits_pass_through_sums_and_products() {
    let c = &mut context(Limits::new().with_max_integer_bits(64));
    let largest = Rational::from(2_i64).power(63, c).unwrap();
    let big = Term::number(largest, c).unwrap();
    let x = symbol("x", c);
    assert_eq!(
        show(&sum(std::slice::from_ref(&big), c), c),
        "9223372036854775808"
    );
    assert_eq!(
        show(&product(&[big.clone(), x.clone()], c), c),
        "9223372036854775808*x"
    );
    assert_eq!(show(&big.negate(c).unwrap(), c), "-9223372036854775808");
    let difference = x.subtract(&big, c).unwrap();
    assert_eq!(show(&difference, c), "-9223372036854775808 + x");
    // A sum that needs more bits than the limit fails with the bound of the
    // addition of rationals.
    let one = integer(1, c);
    let error = Term::sum(&[big, one], c).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
}

// The fixed charges: a number one unit, a symbol one unit and one per byte
// of its name; a comparison one unit per step, one per byte of the shorter of
// two names and one per comparison of two numbers, where the cursor over the
// children or the monomials of two nodes takes one step per position and
// one past the last; a display one unit per step and one per byte of output.
#[test]
fn constructions_comparisons_and_displays_charge_fixed_amounts() {
    let c = &mut default_context();
    let before = c.work_used();
    let x = symbol("abc", c);
    assert_eq!(c.work_used() - before, 4);
    let before = c.work_used();
    let one = integer(1, c);
    assert_eq!(c.work_used() - before, 1);
    let y = symbol("abd", c);
    let before = c.work_used();
    assert_eq!(x.compare(&y, c).unwrap(), Ordering::Less);
    assert_eq!(c.work_used() - before, 1 + 3);
    let two = integer(2, c);
    let before = c.work_used();
    assert_eq!(one.compare(&two, c).unwrap(), Ordering::Less);
    assert_eq!(c.work_used() - before, 1 + 1);
    // Two equal products $pq$: the products 1; the cursor of their factors
    // 3, at the 2 positions and past them; the 2 pairs of symbols 2 each; the
    // numbers of factors 1; and the coefficients 1 and the comparison of
    // two numbers 1.
    let (p, q) = (symbol("p", c), symbol("q", c));
    let left = product(&[p.clone(), q.clone()], c);
    let right = product(&[q.clone(), p.clone()], c);
    assert_eq!(work(c, |c| assert!(left.equals(&right, c).unwrap())), 11);
    // Two equal sums $p + q$: the sums 1; the cursor of their monomials 3;
    // the 2 pairs of cores 2 each and of coefficients 2 each; the numbers of
    // monomials 1; and the constants 2.
    let left = sum(&[p.clone(), q.clone()], c);
    let right = sum(&[q.clone(), p.clone()], c);
    assert_eq!(work(c, |c| assert!(left.equals(&right, c).unwrap())), 15);
    // A comparison that the first pair of factors decides charges the same
    // whatever the number of factors: the products 1, the cursor at the
    // first position 1 and the pair of symbols 2.
    let mut lefts = vec![symbol("a", c)];
    let mut rights = vec![symbol("b", c)];
    for index in 0..64 {
        let factor = symbol(&format!("y{index}"), c);
        lefts.push(factor.clone());
        rights.push(factor);
    }
    let left = product(&lefts, c);
    let right = product(&rights, c);
    assert_eq!(left.children().len(), 65);
    assert_eq!(
        work(c, |c| assert!(left.compare(&right, c).unwrap().is_lt())),
        4
    );
    let before = (c.work_used(), c.output_used());
    assert_eq!(show(&x, c), "abc");
    assert_eq!(
        (c.work_used() - before.0, c.output_used() - before.1),
        (1 + 3, 3)
    );
    // The same construction charges the same work, whatever the limits.
    let mut charges = Vec::new();
    for limits in [Limits::new(), wide()] {
        let c = &mut context(limits);
        let x = symbol("x", c);
        let y = symbol("y", c);
        let pair = sum(&[y, x.clone()], c);
        let before = c.work_used();
        let squared = power(&pair, 2, c);
        let scaled = product(&[squared, x], c);
        charges.push(c.work_used() - before);
        drop(scaled);
    }
    assert_eq!(charges[0], charges[1]);
}

// A display charges its output before it writes it, and a display that fails
// returns no text. For a term of each shape, a number, a symbol, a power, a
// product and a sum, the display passes when `max_output_bytes` is exactly
// its bytes and charges that output, and one byte less fails with
// `ResourceLimit` naming `max_output_bytes` and returns no text.
#[test]
fn a_display_beyond_max_output_bytes_returns_no_text() {
    let c = &mut context(Limits::new().with_max_output_bytes(4));
    let x = symbol("x", c);
    let y = symbol("y", c);
    let pair = sum(&[x, y], c);
    let error = pair.display(c).unwrap_err();
    assert_limit(&error, LimitField::OutputBytes);
    assert!(c.output_used() <= 4);

    let c = &mut context(Limits::new());
    let x = symbol("x", c);
    let y = symbol("y", c);
    let shapes = [
        (TermKind::Number, rational(-3, 4, c), "-3/4"),
        (TermKind::Symbol, symbol("abc", c), "abc"),
        (TermKind::Power, power(&x, -2, c), "x^(-2)"),
        (
            TermKind::Product,
            product(&[integer(2, c), x.clone(), y.clone()], c),
            "2*x*y",
        ),
        (TermKind::Sum, sum(&[integer(1, c), x, y], c), "1 + x + y"),
    ];
    for (kind, term, text) in shapes {
        assert_eq!(term.kind(), kind, "{text}");
        let bytes = text.len() as u64;
        let exact = &mut context(Limits::new().with_max_output_bytes(bytes));
        assert_eq!(show(&term, exact), text);
        assert_eq!(exact.output_used(), bytes, "{text}");
        let short = &mut context(Limits::new().with_max_output_bytes(bytes - 1));
        let error = term.display(short).unwrap_err();
        assert_limit(&error, LimitField::OutputBytes);
        assert!(short.output_used() < bytes, "{text}");
    }
}

// ---------------------------------------------------------------------------
// Symbols and reserved names

// `pi`, `i` and `undefined` are reserved for constants and are not symbols;
// names that only resemble them are.
#[test]
fn reserved_names_are_unsupported() {
    let c = &mut default_context();
    for name in ["pi", "i", "undefined"] {
        let before = c.work_used();
        let error = Term::symbol(name, c).unwrap_err();
        assert_fault(&error, FaultKind::Unsupported);
        assert_eq!(error.span(), Span::new(0, name.len()));
        assert_eq!(c.work_used(), before);
    }
    for name in ["p", "ii", "pi2", "_i", "undefined_", "Pi", "I"] {
        assert_eq!(Term::symbol(name, c).unwrap().as_symbol(), Some(name));
    }
}

// A symbol name is an ASCII letter or `_` followed by ASCII letters, digits
// and `_`; another name fails with Syntax and the span of its first
// character that the form does not allow.
#[test]
fn symbol_names_are_identifiers() {
    let c = &mut default_context();
    let cases = [
        ("", (0, 0)),
        ("1x", (0, 1)),
        ("x-y", (1, 2)),
        ("x y", (1, 2)),
        ("\u{e9}", (0, 2)),
        ("x\u{3b8}", (1, 3)),
        ("x\u{1d465}", (1, 5)),
    ];
    for (name, (start, end)) in cases {
        let error = Term::symbol(name, c).unwrap_err();
        assert_fault(&error, FaultKind::Syntax);
        assert_eq!(error.span(), Span::new(start, end), "{name}");
    }
    for name in ["x", "_", "X1_y", "x_1", "Zz9"] {
        assert!(Term::symbol(name, c).is_ok(), "{name}");
    }
}

// ---------------------------------------------------------------------------
// Display and its stability

// The display grammar: minimal parentheses, a constant first, a negative
// coefficient as a minus, negative exponents in parentheses, and a sum among
// the factors of a product or as the base of a power in parentheses.
#[test]
fn the_display_follows_its_grammar() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let minus_one = integer(-1, c);
    let minus_two = integer(-2, c);
    let half = rational(1, 2, c);
    let pair = sum(&[x.clone(), y.clone()], c);
    let neg_x = product(&[minus_one.clone(), x.clone()], c);
    let z_pair = product(&[z.clone(), pair.clone()], c);
    let cases = [
        (rational(-3, 4, c), "-3/4"),
        (power(&x, -2, c), "x^(-2)"),
        (neg_x.clone(), "-x"),
        (product(&[minus_two.clone(), x.clone()], c), "-2*x"),
        (product(&[half.clone(), x.clone()], c), "1/2*x"),
        (
            product(&[minus_one.clone(), x.clone(), y.clone()], c),
            "-x*y",
        ),
        (product(&[integer(2, c), pair.clone()], c), "2*x + 2*y"),
        (pair.negate(c).unwrap(), "-x - y"),
        (product(&[integer(2, c), z_pair.clone()], c), "2*z*(x + y)"),
        (z_pair.negate(c).unwrap(), "-z*(x + y)"),
        (sum(&[integer(1, c), neg_x.clone()], c), "1 - x"),
        (sum(&[minus_one.clone(), x.clone()], c), "-1 + x"),
        (sum(&[neg_x.clone(), y.clone()], c), "-x + y"),
        (
            sum(
                &[product(&[minus_two, x.clone()], c), y.negate(c).unwrap()],
                c,
            ),
            "-2*x - y",
        ),
        (product(&[x.clone(), pair.clone()], c), "x*(x + y)"),
        (power(&pair, -2, c), "(x + y)^(-2)"),
        (power(&power(&pair, -2, c), -1, c), "((x + y)^(-2))^(-1)"),
        (sum(&[half.clone(), x.clone()], c), "1/2 + x"),
        (
            x.subtract(&product(&[half, y.clone()], c), c).unwrap(),
            "x - 1/2*y",
        ),
        (x.subtract(&pair, c).unwrap(), "-y"),
        (x.subtract(&z_pair, c).unwrap(), "x - z*(x + y)"),
        (power(&neg_x, 3, c), "-x^3"),
        (
            power(&sum(&[integer(1, c), neg_x.clone()], c), -1, c),
            "-(-1 + x)^(-1)",
        ),
    ];
    for (term, text) in &cases {
        assert_eq!(show(term, c), *text);
    }
}

/// A term with numbers, fractions, powers, a scaled sum, a sum as a factor
/// and as a base, a cancelled monomial and a witness, built in a fixed
/// order.
fn composite(c: &mut Context) -> Term {
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let half = rational(1, 2, c);
    let shifted = sum(&[x.clone(), half], c);
    let inverse_y = power(&y, -1, c);
    let first = product(
        &[integer(3, c), power(&shifted, 2, c), inverse_y.clone()],
        c,
    );
    let second = product(&[rational(-2, 3, c), sum(&[y.clone(), x.clone()], c)], c);
    let two_y = product(&[integer(2, c), y.clone()], c);
    let three_x = product(&[integer(3, c), x.clone()], c);
    let third = product(&[z.clone(), sum(&[two_y, three_x], c)], c);
    let inverse_z = power(&z, -1, c);
    let cancelled = inverse_z.subtract(&inverse_z, c).unwrap();
    let one = power(&power(&x, -1, c), 0, c);
    sum(&[first, second, third, cancelled, one, integer(7, c)], c)
}

// The same term, built in two runs with fresh contexts, has the same display
// bytes, which are pinned here, and charges the same work.
#[test]
fn display_bytes_are_the_same_in_two_runs() {
    let first = &mut default_context();
    let one = composite(first);
    let one_text = show(&one, first);
    let second = &mut default_context();
    let two = composite(second);
    let two_text = show(&two, second);
    assert_eq!(one_text.as_bytes(), two_text.as_bytes());
    assert_eq!(first.work_used(), second.work_used());
    assert_eq!(first.output_used(), second.output_used());
    assert_eq!(
        one_text,
        "7 - 2/3*x - 2/3*y + 0*z^(-1) + (x^(-1))^0 + 3*z*(x + 2/3*y) + 3*y^(-1)*(1/2 + x)^2"
    );
}

// Under associativity and commutativity, every order and grouping of the
// operands gives the same display bytes.
#[test]
fn construction_order_does_not_change_the_display_bytes() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let inverse = power(&x, -1, c);
    let pair = sum(&[y.clone(), x.clone()], c);
    let operands = [
        product(&[integer(2, c), inverse.clone()], c),
        power(&pair, 2, c),
        rational(5, 7, c),
        product(&[y.clone(), x.clone()], c),
        inverse.negate(c).unwrap(),
    ];
    let [a, b, d, e, f] = operands.clone();
    for combine in [Term::sum, Term::product] {
        let flat = combine(&operands, c).unwrap();
        let text = show(&flat, c);
        let reversed = [f.clone(), e.clone(), d.clone(), b.clone(), a.clone()];
        let left = combine(
            &[combine(&[a.clone(), b.clone()], c).unwrap(), d.clone()],
            c,
        )
        .unwrap();
        let left = combine(&[left, combine(&[e.clone(), f.clone()], c).unwrap()], c).unwrap();
        let right = combine(
            &[
                f.clone(),
                combine(&[d.clone(), b.clone(), e.clone()], c).unwrap(),
            ],
            c,
        )
        .unwrap();
        let right = combine(&[a.clone(), right], c).unwrap();
        for other in [combine(&reversed, c).unwrap(), left, right] {
            assert_eq!(show(&other, c).as_bytes(), text.as_bytes());
            assert!(equal(&other, &flat, c));
        }
    }
    let total = Term::sum(&operands, c).unwrap();
    assert_eq!(show(&total, c), "5/7 + x^(-1) + (x + y)^2 + x*y");
    let all = Term::product(&operands, c).unwrap();
    assert_eq!(show(&all, c), "-10/7*x*x^(-2)*y*(x + y)^2");
}

// ---------------------------------------------------------------------------
// Defects of the earlier implementation

// The products of the earlier implementation raised a collected base to its
// exponent and kept the power that this gave, so a product could hold a
// nested product or two factors with the same base
// (cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:docs/domains/cross-cutting/rewriting/contract.md:958).
// Here $x (xy)^2$ is $x^3 y^2$: no nested product and no two factors with
// the same key.
#[test]
fn a_power_of_a_product_leaves_no_nested_product_and_no_repeated_key() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let xy = product(&[x.clone(), y.clone()], c);
    let squared = power(&xy, 2, c);
    for result in [
        product(&[x.clone(), squared.clone()], c),
        product(&[squared, x.clone()], c),
    ] {
        assert_eq!(show(&result, c), "x^3*y^2");
        let (coefficient, factors) = result.as_product().unwrap();
        assert_eq!(coefficient, &Rational::from(1_i64));
        assert_eq!(factors.len(), 2);
        for factor in factors {
            assert_eq!(factor.kind(), TermKind::Power);
        }
        let (first, _) = factors[0].as_power().unwrap();
        let (second, _) = factors[1].as_power().unwrap();
        assert!(equal(first, &x, c));
        assert!(equal(second, &y, c));
    }
}

// The expansion of the earlier implementation did not order the operands of
// a sum used as a base or a core, so equal products did not cancel
// (cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic/functions/expansion.rs:199).
// Here sums built in different orders compare equal and merge as bases and
// as cores: $(x + y)^2 (y + x)^3 = (x + y)^5$ and $(x + y) z - z (y + x) = 0$.
#[test]
fn sums_built_in_different_orders_merge_as_bases_and_cores() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let z = symbol("z", c);
    let forward = sum(&[x.clone(), y.clone()], c);
    let backward = sum(&[y, x], c);
    let merged = product(&[power(&forward, 2, c), power(&backward, 3, c)], c);
    assert_eq!(show(&merged, c), "(x + y)^5");
    assert!(equal(&merged, &power(&forward, 5, c), c));
    let left = product(&[forward, z.clone()], c);
    let right = product(&[z, backward], c);
    let difference = left.subtract(&right, c).unwrap();
    assert_eq!(difference.as_number(), Some(&Rational::from(0_i64)));
}

// ---------------------------------------------------------------------------
// The interface

// The accessors expose the canonical structure that the parser, the
// polynomials and the command entry read.
#[test]
fn the_accessors_expose_the_canonical_structure() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let half = rational(1, 2, c);
    let three = integer(3, c);
    let scaled = product(&[three, x.clone(), power(&y, -2, c)], c);
    let total = sum(&[half, scaled.clone(), y.clone()], c);

    let (constant, coefficients, cores) = total.as_sum().unwrap();
    assert_eq!(constant.to_string(), "1/2");
    assert_eq!(coefficients.len(), 2);
    assert_eq!(coefficients[0], Rational::from(1_i64));
    assert_eq!(coefficients[1], Rational::from(3_i64));
    assert!(equal(&cores[0], &y, c));
    assert_eq!(cores[1].kind(), TermKind::Product);
    assert_eq!(cores[1].as_product().unwrap().0, &Rational::from(1_i64));
    assert_eq!(total.children().len(), 2);
    assert_eq!(total.kind(), TermKind::Sum);

    let (coefficient, factors) = scaled.as_product().unwrap();
    assert_eq!(coefficient, &Rational::from(3_i64));
    assert_eq!(factors.len(), 2);
    let (base, exponent) = factors[1].as_power().unwrap();
    assert_eq!((base.as_symbol(), exponent), (Some("y"), -2));
    assert!(scaled.has_negative_power());
    assert!(!x.has_negative_power());
    assert_eq!(x.as_number(), None);
    assert!(x.as_power().is_none());
    assert!(x.as_product().is_none());
    assert!(x.as_sum().is_none());
    assert!(x.children().is_empty());
    assert_eq!((x.size(), x.depth()), (1, 1));
    assert_eq!((total.size(), total.depth()), (6, 4));

    let ranks = [
        TermKind::Number,
        TermKind::Symbol,
        TermKind::Call,
        TermKind::Power,
        TermKind::Product,
        TermKind::Sum,
    ]
    .map(TermKind::rank);
    assert_eq!(ranks, [0, 2, 3, 4, 5, 6]);
    assert_eq!(
        format!("{total:?}"),
        "Term { kind: Sum, children: 2, size: 6, depth: 4, .. }"
    );
    assert_eq!(
        format!("{:?}", power(&y, -2, c)),
        "Term { kind: Power, exponent: -2, children: 1, size: 2, depth: 2, .. }"
    );
    assert_eq!(
        format!("{x:?}"),
        "Term { kind: Symbol, name: \"x\", children: 0, size: 1, depth: 1, .. }"
    );
    assert_eq!(
        format!("{:?}", rational(-1, 2, c)),
        "Term { kind: Number, value: -1/2, children: 0, size: 1, depth: 1, .. }"
    );
}

// Negation, difference and quotient are the canonical sums and products
// they stand for; a number distributes over a sum.
#[test]
fn negation_difference_and_quotient_are_canonical() {
    let c = &mut default_context();
    let x = symbol("x", c);
    let y = symbol("y", c);
    let six = integer(6, c);
    let two_x = product(&[integer(2, c), x.clone()], c);
    assert_eq!(show(&six.divide(&two_x, c).unwrap(), c), "3*x^(-1)");
    assert_eq!(show(&x.divide(&x, c).unwrap(), c), "x*x^(-1)");
    let ratio = x.divide(&y, c).unwrap();
    assert_eq!(show(&product(&[ratio, y.clone()], c), c), "x*y*y^(-1)");
    let pair = sum(&[x.clone(), y.clone()], c);
    let doubled = product(&[integer(2, c), pair.clone()], c);
    assert_eq!(show(&doubled.negate(c).unwrap(), c), "-2*x - 2*y");
    let back = doubled.negate(c).unwrap().negate(c).unwrap();
    assert!(equal(&back, &doubled, c));
    assert_eq!(show(&doubled.subtract(&pair, c).unwrap(), c), "x + y");
    let halves = pair.divide(&integer(2, c), c).unwrap();
    assert_eq!(show(&halves, c), "1/2*x + 1/2*y");
    assert!(equal(&doubled.divide(&integer(2, c), c).unwrap(), &pair, c));
    let third = rational(1, 3, c);
    assert_eq!(show(&third.divide(&six, c).unwrap(), c), "1/18");
    assert_eq!(show(&x.subtract(&third, c).unwrap(), c), "-1/3 + x");
}
