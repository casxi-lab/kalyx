//! The kernels of rational arithmetic on the parts of canonical rationals:
//! the bit bounds that every operation checks before it charges, the
//! power-of-two (dyadic) fast paths, canonical reduction and the general
//! paths of sums, products and quotients.
//!
//! The kernels take and return the parts of a rational, a numerator and a
//! denominator, and never touch the request context; the operations of
//! [`Rational`](super::Rational) check, charge and validate around them. A
//! kernel never panics: every call of the big-integer library that would
//! panic on a zero divisor is preceded by a test, and a failed test is an
//! `Internal` error.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::Ratio;
use num_traits::{One, Signed, Zero};

use crate::{Error, FaultKind, Result, Span};

/// A binary operation of rational arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArithmeticOperation {
    /// $a + b$.
    Add,
    /// $a - b$.
    Subtract,
    /// $a \cdot b$.
    Multiply,
    /// $a / b$, for $b \ne 0$.
    Divide,
}

/// The parts of a rational: a numerator and a denominator. The kernels
/// return them canonical, in lowest terms with a positive denominator.
pub(crate) type Parts = (BigInt, BigInt);

/// The error of a broken internal invariant of the kernels.
pub(crate) fn internal(span: Option<Span>, what: &str) -> Error {
    Error::new(FaultKind::Internal, span, what)
}

/// The canonical zero, $0/1$.
pub(crate) fn zero_parts() -> Parts {
    (BigInt::zero(), BigInt::one())
}

/// The bit bound of the result of `operation` on $a/b$ and $c/d$, from the bit
/// lengths `(|a|, |b|, |c|, |d|)` of the parts of the operands:
///
/// - sum and difference: $\max(\max(|a| + |d|, |c| + |b|) + 1, |b| + |d|)$;
/// - product: $\max(|a| + |c|, |b| + |d|)$;
/// - quotient: $\max(|a| + |d|, |b| + |c|)$.
///
/// It bounds the numerator and the denominator of the unreduced result, and
/// so every intermediate value of the kernels and the canonical result, since
/// reduction never lengthens a part. Sums saturate at `u64::MAX`.
pub(crate) fn operation_bound(bits: (u64, u64, u64, u64), operation: ArithmeticOperation) -> u64 {
    let (a, b, c, d) = bits;
    match operation {
        ArithmeticOperation::Add | ArithmeticOperation::Subtract => a
            .saturating_add(d)
            .max(c.saturating_add(b))
            .saturating_add(1)
            .max(b.saturating_add(d)),
        ArithmeticOperation::Multiply => a.saturating_add(c).max(b.saturating_add(d)),
        ArithmeticOperation::Divide => a.saturating_add(d).max(b.saturating_add(c)),
    }
}

/// The exponent $k$ when `denominator` is exactly $2^k$ and positive.
pub(crate) fn dyadic_exponent(denominator: &BigInt) -> Option<u64> {
    if !denominator.is_positive() {
        return None;
    }
    let zeros = denominator.trailing_zeros()?;
    if zeros.checked_add(1) == Some(denominator.bits()) {
        Some(zeros)
    } else {
        None
    }
}

/// The canonical parts of $n / 2^k$. An integer and a power of two share only
/// powers of two, so counting trailing zero bits replaces a general GCD.
pub(crate) fn dyadic(numerator: BigInt, exponent: u64) -> Parts {
    let zeros = match numerator.trailing_zeros() {
        Some(zeros) => zeros,
        None => return zero_parts(),
    };
    let common = zeros.min(exponent);
    if common == 0 {
        (numerator, BigInt::one() << exponent)
    } else {
        (numerator >> common, BigInt::one() << (exponent - common))
    }
}

/// The canonical parts of $n / d$ through the reduction of num-rational.
///
/// # Errors
///
/// `Internal` when `denominator` is zero; callers reject a zero denominator
/// first.
pub(crate) fn reduce(numerator: BigInt, denominator: BigInt) -> Result<Parts> {
    if denominator.is_zero() {
        return Err(internal(None, "reduction with a zero denominator"));
    }
    Ok(Ratio::new(numerator, denominator).into_raw())
}

/// The canonical parts equal to $n / d$, whose parts may share a factor or
/// whose denominator may be negative; a positive power-of-two denominator
/// takes the dyadic path.
///
/// # Errors
///
/// `Internal` when `denominator` is zero.
pub(crate) fn canonical(numerator: &BigInt, denominator: &BigInt) -> Result<Parts> {
    match dyadic_exponent(denominator) {
        Some(exponent) => Ok(dyadic(numerator.clone(), exponent)),
        None => reduce(numerator.clone(), denominator.clone()),
    }
}

/// The result of `operation` on $a / 2^p$ and $c / 2^q$ when both
/// denominators are positive powers of two and the result is dyadic; `None`
/// for other operands. A quotient qualifies only when the divisor is
/// $\pm 2^k / 2^q$. The result is the canonical value of the general path;
/// the parts of the operands need not be reduced.
pub(crate) fn dyadic_binary(
    left: (&BigInt, &BigInt),
    right: (&BigInt, &BigInt),
    operation: ArithmeticOperation,
) -> Option<Parts> {
    let p = dyadic_exponent(left.1)?;
    let q = dyadic_exponent(right.1)?;
    let (a, c) = (left.0, right.0);
    match operation {
        ArithmeticOperation::Divide => {
            // (a / 2^p) / (±2^k / 2^q) = ±a 2^q / 2^(p + k). A zero divisor has no
            // trailing zeros and is left to the caller's earlier rejection.
            let zeros = c.trailing_zeros()?;
            if zeros.checked_add(1) != Some(c.bits()) {
                return None;
            }
            let shifted = a << q;
            let numerator = if c.is_negative() { -shifted } else { shifted };
            Some(dyadic(numerator, p.checked_add(zeros)?))
        }
        ArithmeticOperation::Multiply => Some(dyadic(a * c, p.checked_add(q)?)),
        ArithmeticOperation::Add | ArithmeticOperation::Subtract => {
            let add = operation == ArithmeticOperation::Add;
            Some(match p.cmp(&q) {
                Ordering::Equal => dyadic(if add { a + c } else { a - c }, p),
                Ordering::Greater => {
                    let c = c << (p - q);
                    dyadic(if add { a + c } else { a - c }, p)
                }
                Ordering::Less => {
                    let a = a << (q - p);
                    dyadic(if add { a + c } else { a - c }, q)
                }
            })
        }
    }
}

/// The order of $a / 2^p$ and $c / 2^q$ by aligning their binary points;
/// `None` unless both denominators are positive powers of two. No product is
/// formed.
pub(crate) fn dyadic_cmp(left: (&BigInt, &BigInt), right: (&BigInt, &BigInt)) -> Option<Ordering> {
    let p = dyadic_exponent(left.1)?;
    let q = dyadic_exponent(right.1)?;
    let (a, c) = (left.0, right.0);
    Some(match p.cmp(&q) {
        Ordering::Equal => a.cmp(c),
        Ordering::Greater => a.cmp(&(c << (p - q))),
        Ordering::Less => (a << (q - p)).cmp(c),
    })
}

/// The canonical result of `operation` on the canonical rationals $a/b$ and
/// $c/d$. Integers keep the denominator one without a reduction, dyadic
/// operands take the dyadic paths, and other operands the general paths. A
/// quotient requires $c \ne 0$.
///
/// # Errors
///
/// `Internal` for a zero divisor, which the caller rejects first.
pub(crate) fn binary(
    left: (&BigInt, &BigInt),
    right: (&BigInt, &BigInt),
    operation: ArithmeticOperation,
) -> Result<Parts> {
    let (a, b) = left;
    let (c, d) = right;
    if operation == ArithmeticOperation::Divide && c.is_zero() {
        return Err(internal(None, "a quotient with a zero divisor"));
    }
    if b.is_one() && d.is_one() {
        return integer_binary(a, c, operation);
    }
    match dyadic_binary(left, right, operation) {
        Some(parts) => Ok(parts),
        None => general_binary(left, right, operation),
    }
}

/// `operation` on canonical rationals that are not both integers and not
/// both dyadic, with $c \ne 0$ for a quotient.
fn general_binary(
    left: (&BigInt, &BigInt),
    right: (&BigInt, &BigInt),
    operation: ArithmeticOperation,
) -> Result<Parts> {
    let (c, d) = right;
    match operation {
        ArithmeticOperation::Add => sum(left, right, true),
        ArithmeticOperation::Subtract => sum(left, right, false),
        ArithmeticOperation::Multiply => product(left, right),
        ArithmeticOperation::Divide => {
            // c/d inverted is (sign(c) d) / |c|, which is canonical.
            let numerator = if c.is_negative() { -d } else { d.clone() };
            let denominator = BigInt::from(c.magnitude().clone());
            product(left, (&numerator, &denominator))
        }
    }
}

/// `operation` on the integers $a$ and $c$, with $c \ne 0$ for a quotient.
fn integer_binary(a: &BigInt, c: &BigInt, operation: ArithmeticOperation) -> Result<Parts> {
    match operation {
        ArithmeticOperation::Add => Ok((a + c, BigInt::one())),
        ArithmeticOperation::Subtract => Ok((a - c, BigInt::one())),
        ArithmeticOperation::Multiply => Ok((a * c, BigInt::one())),
        ArithmeticOperation::Divide => {
            if c.magnitude().is_one() {
                let quotient = if c.is_negative() { -a } else { a.clone() };
                return Ok((quotient, BigInt::one()));
            }
            let one = BigInt::one();
            match dyadic_binary((a, &one), (c, &one), operation) {
                Some(parts) => Ok(parts),
                None => reduce(a.clone(), c.clone()),
            }
        }
    }
}

/// The sum or difference of the canonical rationals $a/b$ and $c/d$.
///
/// Write $g = \gcd(b, d)$, $b = g u$ and $d = g v$. The numerator
/// $t = a v \pm c u$ is coprime to $u$ and $v$, so only $\gcd(t, g)$ remains
/// to cancel, and the reduced result is $(t/h) / (u v (g/h))$ with
/// $h = \gcd(t, g)$.
fn sum(left: (&BigInt, &BigInt), right: (&BigInt, &BigInt), add: bool) -> Result<Parts> {
    let (a, b) = left;
    let (c, d) = right;
    if b == d {
        return reduce(if add { a + c } else { a - c }, b.clone());
    }
    let (u, v) = reduce(b.clone(), d.clone())?;
    let left_term = a * &v;
    let right_term = c * &u;
    let t = if add {
        left_term + right_term
    } else {
        left_term - right_term
    };
    if t.is_zero() {
        return Ok(zero_parts());
    }
    if &u == b {
        // g = 1: the denominators are coprime and the result is canonical.
        return Ok((t, u * v));
    }
    if u.is_zero() {
        return Err(internal(None, "a reduced denominator is zero"));
    }
    let g = b / &u;
    let (t, h) = reduce(t, g)?;
    Ok((t, u * v * h))
}

/// The product of the canonical rationals $a/b$ and $c/d$, with $b, d > 0$:
/// cancelling $\gcd(a, d)$ and $\gcd(c, b)$ leaves every factor of the new
/// numerator coprime to every factor of the new denominator.
fn product(left: (&BigInt, &BigInt), right: (&BigInt, &BigInt)) -> Result<Parts> {
    let (a, b) = left;
    let (c, d) = right;
    if a.is_zero() || c.is_zero() {
        return Ok(zero_parts());
    }
    let (a, d) = reduce(a.clone(), d.clone())?;
    let (c, b) = reduce(c.clone(), b.clone())?;
    Ok((a * c, b * d))
}

/// The order of the rationals $a/b$ and $c/d$ with positive denominators,
/// whose parts need not be reduced.
pub(crate) fn order(left: (&BigInt, &BigInt), right: (&BigInt, &BigInt)) -> Ordering {
    let (a, b) = left;
    let (c, d) = right;
    let signs = sign_rank(a.sign()).cmp(&sign_rank(c.sign()));
    if signs != Ordering::Equal {
        return signs;
    }
    if a.is_zero() {
        return Ordering::Equal;
    }
    let magnitudes = match dyadic_cmp(left, right) {
        Some(ordering) => return ordering,
        None => order_magnitudes(a.magnitude(), b.magnitude(), c.magnitude(), d.magnitude()),
    };
    if a.is_negative() {
        magnitudes.reverse()
    } else {
        magnitudes
    }
}

/// The rank of a sign in the order of the rationals.
const fn sign_rank(sign: Sign) -> i8 {
    match sign {
        Sign::Minus => -1,
        Sign::NoSign => 0,
        Sign::Plus => 1,
    }
}

/// The order of the positive rationals $a/b$ and $c/d$. For positive $u$
/// and $v$, $|u v|$ is $|u| + |v| - 1$ or $|u| + |v|$, so bit lengths that
/// differ by two or more decide; otherwise the cross products are compared.
fn order_magnitudes(a: &BigUint, b: &BigUint, c: &BigUint, d: &BigUint) -> Ordering {
    if b == d {
        return a.cmp(c);
    }
    let first = a.bits().saturating_add(d.bits());
    let second = c.bits().saturating_add(b.bits());
    if first.saturating_add(1) < second {
        return Ordering::Less;
    }
    if second.saturating_add(1) < first {
        return Ordering::Greater;
    }
    (a * d).cmp(&(c * b))
}
