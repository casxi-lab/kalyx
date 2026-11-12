//! Exact numbers: arbitrary-size integers and rationals.
//!
//! [`Integer`] is an integer of any size, and [`Rational`] a fraction of two
//! integers that is always canonical: in lowest terms, with a positive
//! denominator, and zero is $0/1$. Two rationals are equal exactly when their
//! values are, so the derived equality and hash compare values.
//!
//! Every operation that builds a new rational takes the request context last.
//! It first checks a bound on the bits of its result, computed from its
//! operands alone, against `max_integer_bits`; then it charges work, an amount
//! that depends only on its operands; and only then does it compute. A
//! rejected operation therefore charges nothing and allocates nothing but its
//! error.
//!
//! The integer kernel follows the same order: the arithmetic of [`Integer`]
//! and the functions [`gcd`], [`lcm`], [`extended_gcd`], [`modular_inverse`],
//! [`modular_power`] and [`crt`] over [`Congruence`]. It tests its domain
//! first, then checks its bounds, then charges, and checks the storage cost
//! of each value that it returns. A missing inverse
//! ([`ModularInverse::NonUnit`]), an inexact quotient
//! ([`ExactQuotient::NotDivisible`]) and an inconsistent system
//! ([`CrtResult::Inconsistent`]) are values; a modulus that is not positive
//! is the fault `OutsideDomain`.
//!
//! ```
//! use kalyx::context::CancelFlag;
//! use kalyx::number::Rational;
//! use kalyx::{Context, Limits};
//!
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let tenth = Rational::parse_decimal("0.1", &mut context)?;
//! let fifth = Rational::parse_decimal("0.2", &mut context)?;
//! let sum = tenth.add(&fifth, &mut context)?;
//! assert_eq!(sum.to_string(), "3/10");
//! # Ok::<(), kalyx::Error>(())
//! ```
//!
//! The integers and rationals are built on the num-bigint and num-rational
//! packages, but no type of those packages is part of this interface.
//! The rules of this module are stated in the component contract,
//! `docs/components/numbers/contract.md`.

mod arithmetic;
mod integer;
mod literal;
mod power;

#[cfg(test)]
mod dyadic_tests;
#[cfg(test)]
mod integer_tests;
#[cfg(test)]
mod positive_compare_tests;

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::context::{Storage, StorageCost};
use crate::{Context, Error, FaultKind, LimitField, Result, Span};
use arithmetic::{ArithmeticOperation, OrderPath, Parts};
pub use integer::{
    Congruence, CrtResult, ExactQuotient, IntegerBezout, IntegerDivision, ModularInverse, crt,
    extended_gcd, gcd, lcm, modular_inverse, modular_power,
};

/// The work units charged by every operation on rationals except a power and
/// a decimal literal.
const OPERATION_CHARGE: u64 = 1;

/// An integer of any size.
///
/// Integers are built from machine integers with `From`, are read from
/// rationals with [`Rational::numerator`] and [`Rational::denominator`], and
/// are computed by the checked arithmetic below, such as [`Integer::add`]
/// and [`Integer::divide_with_remainder`], and by the integer kernel.
///
/// ```
/// use kalyx::number::Integer;
///
/// let integer = Integer::from(-12_i64);
/// assert!(integer.is_negative());
/// assert_eq!(integer.bits(), 4);
/// assert_eq!(integer.to_string(), "-12");
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Integer(BigInt);

impl Integer {
    /// The bit length of the absolute value: 0 for zero, otherwise
    /// $\lfloor \log_2 \lvert x \rvert \rfloor + 1$.
    #[must_use]
    pub fn bits(&self) -> u64 {
        self.0.bits()
    }

    /// Whether the integer is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// Whether the integer is greater than zero.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    /// Whether the integer is less than zero.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.0.is_negative()
    }

    /// The absolute value as a `u64`, or `None` when it has more than 64
    /// bits. The parser reads an integer exponent through it.
    pub(crate) fn magnitude_u64(&self) -> Option<u64> {
        ToPrimitive::to_u64(self.0.magnitude())
    }
}

impl From<i64> for Integer {
    fn from(value: i64) -> Self {
        Self(BigInt::from(value))
    }
}

impl From<u64> for Integer {
    fn from(value: u64) -> Self {
        Self(BigInt::from(value))
    }
}

impl fmt::Display for Integer {
    /// The decimal digits, with a leading `-` when negative.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A rational number, always canonical: the numerator and the denominator
/// have no common factor, the denominator is positive, and zero is $0/1$.
///
/// Every public way to build a rational establishes the canonical form;
/// there is no constructor that takes the parts unchecked. The derived
/// `PartialEq`, `Eq` and `Hash` therefore compare values. Rationals have no
/// `Ord`: comparing two of them may form cross products of their parts, so
/// they are ordered only by the charged [`compare`](Rational::compare).
///
/// ```
/// use kalyx::context::CancelFlag;
/// use kalyx::number::{Integer, Rational};
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let half = Rational::new(Integer::from(-6_i64), Integer::from(-12_i64), &mut context)?;
/// assert_eq!(half.numerator(), &Integer::from(1_i64));
/// assert_eq!(half.denominator(), &Integer::from(2_i64));
/// assert_eq!(half.to_string(), "1/2");
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// The unchecked constructor of the underlying num-rational type is not
/// available:
///
/// ```compile_fail,E0599
/// use kalyx::number::{Integer, Rational};
///
/// let half = Rational::new_raw(Integer::from(2_i64), Integer::from(4_i64));
/// ```
///
/// nor is a conversion from that type:
///
/// ```compile_fail,E0277
/// use kalyx::number::Rational;
///
/// let raw = num_rational::BigRational::new_raw(2.into(), 4.into());
/// let half = Rational::from(raw);
/// ```
///
/// Rationals have no comparison operators; they are ordered only by
/// [`compare`](Rational::compare), which takes the context:
///
/// ```compile_fail,E0369
/// use kalyx::number::Rational;
///
/// let less = Rational::from(1_i64) < Rational::from(2_i64);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rational {
    // Invariant: gcd(numerator, denominator) = 1 and denominator > 0.
    numerator: Integer,
    denominator: Integer,
}

impl Rational {
    /// The rational of parts that are canonical by construction: the results
    /// of the kernels in `arithmetic`, `literal` and `power`.
    fn from_canonical(parts: Parts) -> Self {
        Self {
            numerator: Integer(parts.0),
            denominator: Integer(parts.1),
        }
    }

    /// The parts of the rational, for the kernels.
    const fn parts(&self) -> (&BigInt, &BigInt) {
        (&self.numerator.0, &self.denominator.0)
    }

    /// The bit lengths of the numerator and the denominator.
    fn part_bits(&self) -> (u64, u64) {
        (self.numerator.bits(), self.denominator.bits())
    }

    /// The bits of the rational: the larger bit length of its parts, the
    /// quantity that `max_integer_bits` bounds. At least 1, since the
    /// denominator is at least 1.
    fn bits(&self) -> u64 {
        self.numerator.bits().max(self.denominator.bits())
    }

    /// The canonical rational $n / d$.
    ///
    /// Checks the zero denominator first, then the bound of
    /// $\max(\lvert n \rvert, \lvert d \rvert)$ bits, then charges one unit, then
    /// reduces.
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `denominator` is zero, before any check or
    /// charge; `ResourceLimit` with `LimitField::IntegerBits` when a part has
    /// more than `max_integer_bits` bits, before the charge; and the request
    /// failures of the charge.
    pub fn new(numerator: Integer, denominator: Integer, context: &mut Context) -> Result<Self> {
        if denominator.is_zero() {
            return Err(division_by_zero(None));
        }
        let bound = numerator.bits().max(denominator.bits());
        context.check(LimitField::IntegerBits, bound)?;
        context.charge(OPERATION_CHARGE)?;
        let parts = arithmetic::canonical(&numerator.0, &denominator.0)?;
        Self::validated(parts, None, context)
    }

    /// The exact value of the decimal literal `source`: one or more ASCII
    /// digits, optionally followed by a point and one or more digits, without
    /// a sign or an exponent. `0.1` is $1/10$, and leading and trailing zeros
    /// do not change the value.
    ///
    /// Scans the text first; then checks a bound of 4 bits per digit, leading
    /// zeros included, against `max_integer_bits`; then charges one work unit
    /// per digit; then converts.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::{Context, ErrorKind, FaultKind, Limits, Span};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// assert_eq!(Rational::parse_decimal("001.2500", &mut context)?.to_string(), "5/4");
    /// let error = Rational::parse_decimal("1e-3", &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    /// assert_eq!(error.span(), Span::new(1, 2));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `Fault(Syntax)` for text that is not such a literal, with the span of
    /// the first offending character, or an empty span at the end when a digit
    /// is missing; `ResourceLimit` with `LimitField::IntegerBits` when 4 bits
    /// per digit exceed `max_integer_bits`, before the charge; and the request
    /// failures of the charge.
    pub fn parse_decimal(source: &str, context: &mut Context) -> Result<Self> {
        Self::literal_at(source, 0, context)
    }

    /// [`parse_decimal`](Rational::parse_decimal) for a literal whose text
    /// starts at byte `offset` of a larger source: the spans of the errors are
    /// shifted by `offset`, and a limit carries the span of the literal.
    pub(crate) fn literal_at(text: &str, offset: usize, context: &mut Context) -> Result<Self> {
        let parts = literal::literal(text, offset, context)?;
        let span = Span::new(offset, offset.saturating_add(text.len()));
        Self::validated(parts, span, context)
    }

    /// The numerator, which carries the sign.
    #[must_use]
    pub const fn numerator(&self) -> &Integer {
        &self.numerator
    }

    /// The denominator, which is positive.
    #[must_use]
    pub const fn denominator(&self) -> &Integer {
        &self.denominator
    }

    /// Whether the rational is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    /// Whether the rational is greater than zero.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        self.numerator.is_positive()
    }

    /// Whether the rational is less than zero.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.numerator.is_negative()
    }

    /// Whether the rational is an integer: its denominator is 1.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.denominator.0.is_one()
    }

    /// The sum `self + other`.
    ///
    /// For $a/b + c/d$, checks the bound
    /// $\max(\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert) + 1, \lvert b \rvert + \lvert d \rvert)$
    /// against `max_integer_bits`, then charges one unit.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when the bound exceeds
    /// `max_integer_bits`, before the charge, and the request failures of the
    /// charge.
    pub fn add(&self, other: &Self, context: &mut Context) -> Result<Self> {
        self.binary(other, ArithmeticOperation::Add, None, context)
    }

    /// The difference `self - other`, with the bound and the charge of
    /// [`add`](Rational::add).
    ///
    /// # Errors
    ///
    /// As [`add`](Rational::add).
    pub fn subtract(&self, other: &Self, context: &mut Context) -> Result<Self> {
        self.binary(other, ArithmeticOperation::Subtract, None, context)
    }

    /// The product `self * other`.
    ///
    /// For $a/b \cdot c/d$, checks the bound
    /// $\max(\lvert a \rvert + \lvert c \rvert, \lvert b \rvert + \lvert d \rvert)$,
    /// then charges one unit.
    ///
    /// # Errors
    ///
    /// As [`add`](Rational::add).
    pub fn multiply(&self, other: &Self, context: &mut Context) -> Result<Self> {
        self.binary(other, ArithmeticOperation::Multiply, None, context)
    }

    /// The quotient `self / other`.
    ///
    /// Tests the divisor for zero first; then, for $(a/b) / (c/d)$, checks the
    /// bound $\max(\lvert a \rvert + \lvert d \rvert, \lvert b \rvert + \lvert c \rvert)$,
    /// then charges one unit.
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `other` is zero, before any check or
    /// charge; otherwise as [`add`](Rational::add).
    pub fn divide(&self, other: &Self, context: &mut Context) -> Result<Self> {
        self.binary(other, ArithmeticOperation::Divide, None, context)
    }

    /// The negation `-self`.
    ///
    /// Checks the bits of `self`, then charges one unit.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when `self` has more than
    /// `max_integer_bits` bits, before the charge, and the request failures of
    /// the charge.
    pub fn negate(&self, context: &mut Context) -> Result<Self> {
        context.check(LimitField::IntegerBits, self.bits())?;
        context.charge(OPERATION_CHARGE)?;
        let parts = (-&self.numerator.0, self.denominator.0.clone());
        Self::validated(parts, None, context)
    }

    /// The inverse $1 / \mathrm{self}$.
    ///
    /// Tests `self` for zero first, then checks its bits, then charges one
    /// unit.
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `self` is zero, before any check or charge;
    /// otherwise as [`negate`](Rational::negate).
    pub fn inverse(&self, context: &mut Context) -> Result<Self> {
        if self.is_zero() {
            return Err(division_by_zero(None));
        }
        context.check(LimitField::IntegerBits, self.bits())?;
        context.charge(OPERATION_CHARGE)?;
        let parts = inverted(self.parts());
        Self::validated(parts, None, context)
    }

    /// The power $\mathrm{self}^e$ for the integer exponent `exponent`, with
    /// $x^0 = 1$ for every $x$, including $0^0 = 1$; a negative exponent
    /// inverts the base.
    ///
    /// With $m = \lvert e \rvert$: checks $m$ against `max_exponent`; then
    /// tests a zero base with a negative exponent; then checks a bound on the
    /// bits of the result, computed from $m$ and the parts of the base and at
    /// least the bits of the base, against `max_integer_bits`; then charges
    /// $1 + \lvert m \rvert + w(m)$ units, where $\lvert m \rvert$ is the bit
    /// length of $m$ and $w(m)$ the number of its one bits; then computes the
    /// power of each part by binary powering. The bound of a part $x$ is exact
    /// when $x$ is a power of two, never above $m \lvert x \rvert + 1$, and at
    /// most one bit above the bits of $x^m$ for $m \lt 2^{31}$; a bound that
    /// does not fit in a `u64` exceeds every limit.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::{Context, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let two_thirds = Rational::parse_decimal("2", &mut context)?
    ///     .divide(&Rational::from(3_i64), &mut context)?;
    /// assert_eq!(two_thirds.power(-5, &mut context)?.to_string(), "243/32");
    /// assert_eq!(Rational::from(0_i64).power(0, &mut context)?, Rational::from(1_i64));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::Exponent` when $m$ exceeds
    /// `max_exponent`; `Fault(DivisionByZero)` for a zero base with a negative
    /// exponent; `ResourceLimit` with `LimitField::IntegerBits` when the bound
    /// exceeds `max_integer_bits`, with `LimitAmount::Bound(u64::MAX)` when it
    /// does not fit in a `u64`; each before any charge; and the request
    /// failures of the charge.
    pub fn power(&self, exponent: i64, context: &mut Context) -> Result<Self> {
        let magnitude = exponent.unsigned_abs();
        context.check(LimitField::Exponent, magnitude)?;
        if exponent < 0 && self.is_zero() {
            return Err(division_by_zero(None));
        }
        // The bits of the base count as well, so that a base above the
        // receiving limit is rejected even for the exponent 0.
        let bound = match (
            power::power_bits(self.numerator.0.magnitude(), magnitude),
            power::power_bits(self.denominator.0.magnitude(), magnitude),
        ) {
            (Some(numerator), Some(denominator)) => {
                Some(numerator.max(denominator).max(self.bits()))
            }
            _ => None,
        };
        context.check_bound_at(LimitField::IntegerBits, bound, None)?;
        context.charge(power::power_charge(magnitude))?;
        if magnitude == 0 {
            return Self::validated((BigInt::one(), BigInt::one()), None, context);
        }
        let (numerator, denominator) = if exponent < 0 {
            inverted(self.parts())
        } else {
            (self.numerator.0.clone(), self.denominator.0.clone())
        };
        // The parts of a canonical base are coprime, and so are their powers;
        // the denominator stays positive.
        let parts = (
            power::power_part(numerator, magnitude),
            power::power_part(denominator, magnitude),
        );
        Self::validated(parts, None, context)
    }

    /// The order of `self` and `other`, without forming their difference.
    ///
    /// For $a/b$ and $c/d$, decides by the first of these that applies:
    /// equal parts; the signs; the binary points of two power-of-two
    /// denominators, aligned; equal denominators, by the numerators; the sums
    /// $\lvert a \rvert + \lvert d \rvert$ and
    /// $\lvert c \rvert + \lvert b \rvert$ of the bit lengths, which bound
    /// the bit lengths of the cross products, when they differ by at least
    /// two; and otherwise the cross products $a d$ and $c b$. Only the last
    /// forms products, and only it checks a bound: that
    /// of the cross products,
    /// $\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert)$,
    /// against `max_integer_bits`. Every path then charges one unit, and only
    /// then compares. Two equal rationals therefore compare `Equal` under
    /// every `max_integer_bits`, even where their difference would exceed
    /// it; the charge still observes `max_work`, cancellation and the
    /// deadline.
    ///
    /// ```
    /// use std::cmp::Ordering;
    ///
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::{Context, ErrorKind, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let one = Rational::from(1_i64);
    /// let third = one.divide(&Rational::from(3_i64), &mut context)?;
    /// let half = one.divide(&Rational::from(2_i64), &mut context)?;
    /// // Equal parts decide without a bound.
    /// let mut none = Context::new(Limits::new().with_max_integer_bits(0), CancelFlag::new());
    /// assert_eq!(third.compare(&third, &mut none)?, Ordering::Equal);
    /// // 1/3 and 1/2 need the cross products 1 * 2 and 1 * 3, whose bound
    /// // max(|1| + |2|, |1| + |3|) is 3 bits.
    /// let error = third.compare(&half, &mut none).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    /// assert_eq!(third.compare(&half, &mut context)?, Ordering::Less);
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// This is the only order of rationals: `Rational` implements neither
    /// `PartialOrd` nor `Ord`, since a comparison may form cross products of
    /// the parts.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when the cross products
    /// are needed and their bound exceeds `max_integer_bits`, before the
    /// charge, and the request failures of the charge.
    pub fn compare(&self, other: &Self, context: &mut Context) -> Result<Ordering> {
        let path = arithmetic::order_path(self.parts(), other.parts());
        if let OrderPath::CrossProducts(bound) = path {
            context.check(LimitField::IntegerBits, bound)?;
        }
        context.charge(OPERATION_CHARGE)?;
        Ok(arithmetic::order(self.parts(), other.parts(), path))
    }

    /// The bit bound of `operation` on `self` and `other`.
    fn bound(&self, other: &Self, operation: ArithmeticOperation) -> u64 {
        let (a, b) = self.part_bits();
        let (c, d) = other.part_bits();
        arithmetic::operation_bound((a, b, c, d), operation)
    }

    /// A binary operation: the zero divisor, then the bound, then the charge,
    /// then the kernel, then the check of the result; errors carry `span`.
    pub(crate) fn binary(
        &self,
        other: &Self,
        operation: ArithmeticOperation,
        span: Option<Span>,
        context: &mut Context,
    ) -> Result<Self> {
        if operation == ArithmeticOperation::Divide && other.is_zero() {
            return Err(division_by_zero(span));
        }
        let bound = self.bound(other, operation);
        context.check_at(LimitField::IntegerBits, bound, span)?;
        context.charge_at(OPERATION_CHARGE, span)?;
        let parts = arithmetic::binary(self.parts(), other.parts(), operation)?;
        Self::validated(parts, span, context)
    }

    /// The rational of canonical `parts`, after checking its bits against
    /// `max_integer_bits`. Every operation checked a bound of at least these
    /// bits before it charged, so this check fails only if a bound is wrong.
    fn validated(parts: Parts, span: Option<Span>, context: &Context) -> Result<Self> {
        let value = Self::from_canonical(parts);
        context.check_at(LimitField::IntegerBits, value.bits(), span)?;
        Ok(value)
    }
}

/// The inverse of the nonzero canonical $n/d$: $(\mathrm{sign}(n)\, d) / \lvert n \rvert$,
/// which is canonical.
fn inverted(parts: (&BigInt, &BigInt)) -> Parts {
    let (numerator, denominator) = parts;
    let new_numerator = if numerator.is_negative() {
        -denominator
    } else {
        denominator.clone()
    };
    (new_numerator, BigInt::from(numerator.magnitude().clone()))
}

/// The division-by-zero fault.
fn division_by_zero(span: Option<Span>) -> Error {
    Error::new(FaultKind::DivisionByZero, span, "division by zero")
}

impl From<Integer> for Rational {
    /// The integer $n$ as $n/1$.
    fn from(value: Integer) -> Self {
        Self {
            numerator: value,
            denominator: Integer(BigInt::one()),
        }
    }
}

impl From<i64> for Rational {
    /// The integer $n$ as $n/1$.
    fn from(value: i64) -> Self {
        Self::from(Integer::from(value))
    }
}

impl fmt::Display for Rational {
    /// The numerator, followed by `/` and the denominator unless the
    /// denominator is 1: `-3/4`, `5`, `0`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_integer() {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl StorageCost for Rational {
    /// One node and $\lvert n \rvert + \lvert d \rvert + 3$ bytes for $n/d$,
    /// with $\lvert x \rvert$ the bit length; saturating at `u64::MAX`.
    fn storage(&self) -> Storage {
        let bytes = self
            .numerator
            .bits()
            .saturating_add(self.denominator.bits())
            .saturating_add(3);
        Storage::new(1, bytes)
    }
}
