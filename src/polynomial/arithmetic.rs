//! The shared algorithms of the polynomial ring $K\[x\]$: admission, negation,
//! sums and differences, products, powers by repeated squaring and the
//! derivative, once for every coefficient ring $K$.
//!
//! The algorithms reach the coefficients only through the methods of the
//! coefficient-field trait: the element operations, the zero test, and
//! `measure`, from which every term takes the cost of its coefficient, a
//! part of the cost of the polynomial. They place no bound on the elements
//! beyond those of the trait. They need the zero test to decide, so they
//! are bounded by `CoefficientRing<Undecided = Infallible>`, and every term
//! whose coefficient becomes zero is dropped. Integers enter only as
//! $n \cdot 1$, through `from_integer`, and no algorithm divides, so they
//! hold in every characteristic.
//!
//! The algorithms charge only for their own steps: one unit for each step of
//! a loop and one for the step that builds a result, after its checks. Each
//! coefficient operation charges what the coefficient ring charges for it,
//! and every amount depends only on the operands. Every polynomial that an
//! algorithm forms, its result and each partial sum of a product, is checked
//! against `max_exponent` and with `check_storage` before it is used.

use std::convert::Infallible;

use crate::coefficient::{CoefficientRing, ZeroTest};
use crate::number::Integer;
use crate::{Context, Result};

use super::terms::{self, PolynomialTerms, internal};
use super::{Polynomial, PolynomialRing};

/// The work units charged for each polynomial that an operation returns,
/// after its checks.
const RESULT_CHARGE: u64 = 1;

/// The work units charged for each step of a loop: a term taken, written or
/// passed, a row of a product or a bit of an exponent.
const STEP_CHARGE: u64 = 1;

/// Whether a merge adds or subtracts its second operand.
#[derive(Clone, Copy)]
enum PolynomialSign {
    /// The sum of the two operands.
    Plus,
    /// The first operand minus the second.
    Minus,
}

/// The positions of a merge in its two operands.
struct PolynomialCursor {
    left: usize,
    right: usize,
}

/// Whether `value` is zero, by the zero test of `coefficients`, which always
/// decides: the reason of an undecided answer is uninhabited, and the empty
/// `match` unwraps it.
pub(super) fn is_zero<K>(
    coefficients: &K,
    value: &K::Element,
    context: &mut Context,
) -> Result<bool>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    match coefficients.zero_test(value, context)? {
        ZeroTest::Zero => Ok(true),
        ZeroTest::Nonzero => Ok(false),
        ZeroTest::Undecided(reason) => match reason {},
    }
}

/// The polynomial of `terms`, after the checks of [`terms::check`] and the
/// charge of one unit.
pub(super) fn admit<K>(
    ring: &PolynomialRing<K>,
    terms: PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing,
{
    terms::check(&terms, &ring.variable, context)?;
    context.charge(RESULT_CHARGE)?;
    Ok(Polynomial { terms })
}

/// The monomial `coefficient` $x^{\mathrm{degree}}$: the zero polynomial when
/// the zero test finds `coefficient` zero, then admitted.
pub(super) fn monomial<K>(
    ring: &PolynomialRing<K>,
    coefficient: K::Element,
    degree: u64,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut terms = PolynomialTerms::new();
    if !is_zero(&ring.coefficients, &coefficient, context)? {
        terms.push(&ring.coefficients, degree, coefficient)?;
    }
    admit(ring, terms, context)
}

/// A copy of `polynomial`: one unit per term for the copy, then admitted
/// under the limits of this context.
pub(super) fn copy<K>(
    ring: &PolynomialRing<K>,
    polynomial: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing,
{
    context.charge(polynomial.terms.len() as u64)?;
    admit(ring, polynomial.terms.clone(), context)
}

// ---------------------------------------------------------------------------
// Negation, sums and differences

/// $-a$: one unit and the negation of the coefficient for each term. The
/// negation of a coefficient that is not zero is not zero in any ring, so
/// no zero test is needed.
pub(super) fn negate<K>(
    ring: &PolynomialRing<K>,
    polynomial: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let negated = negated_terms(ring, &polynomial.terms, context)?;
    admit(ring, negated, context)
}

/// The terms of `terms` with their coefficients negated.
fn negated_terms<K>(
    ring: &PolynomialRing<K>,
    terms: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut negated = PolynomialTerms::with_capacity(terms.len());
    let mut index = 0;
    while index < terms.len() {
        context.charge(STEP_CHARGE)?;
        push_negated(ring, terms, index, &mut negated, context)?;
        index += 1;
    }
    Ok(negated)
}

/// Appends the negation of the term at `index` of `terms` to `negated`.
fn push_negated<K>(
    ring: &PolynomialRing<K>,
    terms: &PolynomialTerms<K::Element>,
    index: usize,
    negated: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let (degree, coefficient) = match terms.term(index) {
        Some(term) => term,
        None => return Err(internal("a negated term past the last term")),
    };
    let value = ring.coefficients.negate(coefficient, context)?;
    negated.push(&ring.coefficients, degree, value)
}

/// $a + b$.
pub(super) fn add<K>(
    ring: &PolynomialRing<K>,
    left: &Polynomial<K>,
    right: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let merged = merge(
        ring,
        &left.terms,
        &right.terms,
        PolynomialSign::Plus,
        context,
    )?;
    admit(ring, merged, context)
}

/// $a - b$.
pub(super) fn subtract<K>(
    ring: &PolynomialRing<K>,
    left: &Polynomial<K>,
    right: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let merged = merge(
        ring,
        &left.terms,
        &right.terms,
        PolynomialSign::Minus,
        context,
    )?;
    admit(ring, merged, context)
}

/// The sum `total + addend` of two owned polynomials, as the expansion of a
/// sum adds its monomials: when one of them is zero, the other; when every
/// degree of `addend` is above the degree of `total`, `total` with the terms
/// of `addend` appended, one unit per term; otherwise their merge, as
/// [`add`]. The result is admitted.
pub(super) fn accumulate<K>(
    ring: &PolynomialRing<K>,
    total: Polynomial<K>,
    addend: Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let sum = sum_terms(ring, total.terms, addend.terms, context)?;
    admit(ring, sum, context)
}

/// The terms of `total + addend`: `addend` when `total` has no terms, `total`
/// when `addend` has none, the terms of `addend` appended to `total` when
/// they all come after them, and the merge otherwise.
fn sum_terms<K>(
    ring: &PolynomialRing<K>,
    total: PolynomialTerms<K::Element>,
    addend: PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    match (total.last_degree(), addend.first_degree()) {
        (None, _) => Ok(addend),
        (_, None) => Ok(total),
        (Some(top), Some(bottom)) => {
            if top < bottom {
                append(&ring.coefficients, total, &addend, context)
            } else {
                merge(ring, &total, &addend, PolynomialSign::Plus, context)
            }
        }
    }
}

/// `total` with the terms of `addend`, whose degrees all lie above those of
/// `total`, appended in order: one unit per term. The coefficients are
/// those of `coefficients`.
fn append<K>(
    coefficients: &K,
    total: PolynomialTerms<K::Element>,
    addend: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing,
{
    let mut joined = total;
    let mut index = 0;
    while index < addend.len() {
        context.charge(STEP_CHARGE)?;
        push_copy(coefficients, addend, index, &mut joined)?;
        index += 1;
    }
    Ok(joined)
}

/// Appends a copy of the term at `index` of `terms` to `target`.
fn push_copy<K>(
    coefficients: &K,
    terms: &PolynomialTerms<K::Element>,
    index: usize,
    target: &mut PolynomialTerms<K::Element>,
) -> Result<()>
where
    K: CoefficientRing,
{
    match terms.term(index) {
        Some((degree, coefficient)) => target.push(coefficients, degree, coefficient.clone()),
        None => Err(internal("a copied term past the last term")),
    }
}

/// The terms of `left` plus or minus `right`, merged in increasing degree.
/// Each step charges one unit and takes the next term of one operand, or the
/// next terms of both when their degrees are equal; then their coefficients
/// are added or subtracted, and the term is dropped when the zero test finds
/// the result zero.
fn merge<K>(
    ring: &PolynomialRing<K>,
    left: &PolynomialTerms<K::Element>,
    right: &PolynomialTerms<K::Element>,
    sign: PolynomialSign,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut merged = PolynomialTerms::with_capacity(left.len().saturating_add(right.len()));
    let mut cursor = PolynomialCursor { left: 0, right: 0 };
    while cursor.left < left.len() || cursor.right < right.len() {
        context.charge(STEP_CHARGE)?;
        merge_step(ring, (left, right), sign, &mut cursor, &mut merged, context)?;
    }
    Ok(merged)
}

/// One step of [`merge`]: the term of lower degree, or the combination of
/// the two terms of equal degree, at the cursor.
fn merge_step<K>(
    ring: &PolynomialRing<K>,
    operands: (&PolynomialTerms<K::Element>, &PolynomialTerms<K::Element>),
    sign: PolynomialSign,
    cursor: &mut PolynomialCursor,
    merged: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let (left, right) = operands;
    match (left.term(cursor.left), right.term(cursor.right)) {
        (Some((low, value)), None) => {
            merged.push(&ring.coefficients, low, value.clone())?;
            cursor.left += 1;
            Ok(())
        }
        (None, Some((high, value))) => {
            push_signed(ring, high, value, sign, merged, context)?;
            cursor.right += 1;
            Ok(())
        }
        (Some((low, first)), Some((high, second))) => {
            if low < high {
                merged.push(&ring.coefficients, low, first.clone())?;
                cursor.left += 1;
            } else if high < low {
                push_signed(ring, high, second, sign, merged, context)?;
                cursor.right += 1;
            } else {
                push_combined(ring, low, (first, second), sign, merged, context)?;
                cursor.left += 1;
                cursor.right += 1;
            }
            Ok(())
        }
        (None, None) => Err(internal("a merge step past both operands")),
    }
}

/// Appends the term of the second operand alone: its coefficient for a sum,
/// and its negation for a difference.
fn push_signed<K>(
    ring: &PolynomialRing<K>,
    degree: u64,
    value: &K::Element,
    sign: PolynomialSign,
    merged: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let signed = match sign {
        PolynomialSign::Plus => value.clone(),
        PolynomialSign::Minus => ring.coefficients.negate(value, context)?,
    };
    merged.push(&ring.coefficients, degree, signed)
}

/// Appends the sum or the difference of two coefficients of the same
/// degree, unless the zero test finds it zero.
fn push_combined<K>(
    ring: &PolynomialRing<K>,
    degree: u64,
    values: (&K::Element, &K::Element),
    sign: PolynomialSign,
    merged: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let (first, second) = values;
    let combined = match sign {
        PolynomialSign::Plus => ring.coefficients.add(first, second, context)?,
        PolynomialSign::Minus => ring.coefficients.subtract(first, second, context)?,
    };
    if !is_zero(&ring.coefficients, &combined, context)? {
        merged.push(&ring.coefficients, degree, combined)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Products and powers

/// $a b$. The degree $\deg a + \deg b$ is checked first, in checked
/// arithmetic. Then the operand with fewer terms, `left` when they have as
/// many, gives the rows: each of its terms $c x^d$ charges one unit and
/// forms the row $c x^d \cdot q$ of the other operand $q$, one unit, a
/// product of coefficients and a zero test per term of $q$; the row is
/// added to the total of the rows before it as [`accumulate`] adds, and the
/// total is checked.
pub(super) fn multiply<K>(
    ring: &PolynomialRing<K>,
    left: &Polynomial<K>,
    right: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    check_product_degree(&left.terms, &right.terms, context)?;
    let total = if left.terms.len() <= right.terms.len() {
        product_rows(ring, &left.terms, &right.terms, context)?
    } else {
        product_rows(ring, &right.terms, &left.terms, context)?
    };
    admit(ring, total, context)
}

/// Checks the degree of the product of `left` and `right`, when neither is
/// zero, against `max_exponent` and the width of `i64`.
fn check_product_degree<E>(
    left: &PolynomialTerms<E>,
    right: &PolynomialTerms<E>,
    context: &Context,
) -> Result<()> {
    match (left.last_degree(), right.last_degree()) {
        (Some(first), Some(second)) => terms::check_degree(first.checked_add(second), context),
        _ => Ok(()),
    }
}

/// The terms of the product of `rows` and `other`, summed row by row.
fn product_rows<K>(
    ring: &PolynomialRing<K>,
    rows: &PolynomialTerms<K::Element>,
    other: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut total = PolynomialTerms::new();
    let mut index = 0;
    while index < rows.len() {
        context.charge(STEP_CHARGE)?;
        let row = product_row(ring, rows, index, other, context)?;
        total = sum_terms(ring, total, row, context)?;
        terms::check(&total, &ring.variable, context)?;
        index += 1;
    }
    Ok(total)
}

/// The row of the term at `index` of `rows`: that term times `other`.
fn product_row<K>(
    ring: &PolynomialRing<K>,
    rows: &PolynomialTerms<K::Element>,
    index: usize,
    other: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    match rows.term(index) {
        Some(factor) => scaled_terms(ring, factor, other, context),
        None => Err(internal("a row past the last term")),
    }
}

/// The terms of `factor` $= c x^d$ times `other`, in the order of `other`:
/// one unit, a product of coefficients and a zero test per term.
fn scaled_terms<K>(
    ring: &PolynomialRing<K>,
    factor: (u64, &K::Element),
    other: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut row = PolynomialTerms::with_capacity(other.len());
    let mut position = 0;
    while position < other.len() {
        context.charge(STEP_CHARGE)?;
        push_product(ring, factor, other, position, &mut row, context)?;
        position += 1;
    }
    Ok(row)
}

/// Appends `factor` times the term at `position` of `other` to `row`, unless
/// the zero test finds the product zero, as it can be in a ring with zero
/// divisors.
fn push_product<K>(
    ring: &PolynomialRing<K>,
    factor: (u64, &K::Element),
    other: &PolynomialTerms<K::Element>,
    position: usize,
    row: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let (shift, scale) = factor;
    let (degree, value) = match other.term(position) {
        Some(term) => term,
        None => return Err(internal("a product term past the last term")),
    };
    // The degree of the product was checked before the rows, so the sum
    // fits; a sum that does not is a broken invariant.
    let shifted = match shift.checked_add(degree) {
        Some(shifted) => shifted,
        None => return Err(internal("a product degree beyond u64::MAX")),
    };
    let product = ring.coefficients.multiply(scale, value, context)?;
    if !is_zero(&ring.coefficients, &product, context)? {
        row.push(&ring.coefficients, shifted, product)?;
    }
    Ok(())
}

/// $a^k$ by repeated squaring, with $a^0 = 1$, also for $a = 0$. The
/// exponent is checked first, then the degree $k \deg a$ in checked
/// arithmetic, both against `max_exponent` and the width of `i64`. For
/// $k \ge 1$ the power starts from a copy of $a$, and each bit of $k$ below
/// its highest one, from the top, charges one unit, squares the power and,
/// when the bit is set, multiplies it by $a$.
pub(super) fn power<K>(
    ring: &PolynomialRing<K>,
    base: &Polynomial<K>,
    exponent: u64,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    terms::check_degree(Some(exponent), context)?;
    check_power_degree(&base.terms, exponent, context)?;
    if exponent == 0 {
        let one = ring.coefficients.one(context)?;
        return monomial(ring, one, 0, context);
    }
    raise(ring, base, exponent, context)
}

/// Checks the degree of the power `exponent` of `base`, when `base` is not
/// zero, against `max_exponent` and the width of `i64`.
fn check_power_degree<E>(
    base: &PolynomialTerms<E>,
    exponent: u64,
    context: &Context,
) -> Result<()> {
    match base.last_degree() {
        Some(degree) => terms::check_degree(degree.checked_mul(exponent), context),
        None => Ok(()),
    }
}

/// $a^k$ for $k \ge 1$, from the highest bit of $k$ down.
fn raise<K>(
    ring: &PolynomialRing<K>,
    base: &Polynomial<K>,
    exponent: u64,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut bit = highest_bit(exponent) / 2;
    let mut result = copy(ring, base, context)?;
    while bit > 0 {
        context.charge(STEP_CHARGE)?;
        result = multiply(ring, &result, &result, context)?;
        if exponent & bit != 0 {
            result = multiply(ring, &result, base, context)?;
        }
        bit /= 2;
    }
    Ok(result)
}

/// The highest power of two that is at most `value`, for `value` at least
/// 1; at most 63 doublings.
pub(super) fn highest_bit(value: u64) -> u64 {
    let mut bit: u64 = 1;
    while bit <= value / 2 {
        bit *= 2;
    }
    bit
}

// ---------------------------------------------------------------------------
// The derivative

/// $a'$, the derivative by the variable: for each term $c x^d$, one unit,
/// and for $d \ge 1$ the image $d \cdot 1$ of $d$ by `from_integer`, the
/// product $(d \cdot 1) \, c$ and its zero test, which drops the term when
/// the characteristic divides $d$. No coefficient is divided.
pub(super) fn derivative<K>(
    ring: &PolynomialRing<K>,
    polynomial: &Polynomial<K>,
    context: &mut Context,
) -> Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let derived = derived_terms(ring, &polynomial.terms, context)?;
    admit(ring, derived, context)
}

/// The terms of the derivative of `terms`.
fn derived_terms<K>(
    ring: &PolynomialRing<K>,
    terms: &PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<PolynomialTerms<K::Element>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let mut derived = PolynomialTerms::with_capacity(terms.len());
    let mut index = 0;
    while index < terms.len() {
        context.charge(STEP_CHARGE)?;
        push_derived(ring, terms, index, &mut derived, context)?;
        index += 1;
    }
    Ok(derived)
}

/// Appends the derivative of the term at `index` of `terms` to `derived`:
/// nothing for a constant term.
fn push_derived<K>(
    ring: &PolynomialRing<K>,
    terms: &PolynomialTerms<K::Element>,
    index: usize,
    derived: &mut PolynomialTerms<K::Element>,
    context: &mut Context,
) -> Result<()>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let (degree, coefficient) = match terms.term(index) {
        Some(term) => term,
        None => return Err(internal("a derived term past the last term")),
    };
    if degree == 0 {
        return Ok(());
    }
    let multiple = ring
        .coefficients
        .from_integer(&Integer::from(degree), context)?;
    let value = ring
        .coefficients
        .multiply(&multiple, coefficient, context)?;
    if !is_zero(&ring.coefficients, &value, context)? {
        derived.push(&ring.coefficients, degree - 1, value)?;
    }
    Ok(())
}
