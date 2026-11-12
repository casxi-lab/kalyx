//! The integer kernel: the checked arithmetic of [`Integer`] and the
//! functions of elementary number theory on it, the GCD, the LCM, the
//! extended GCD, the modular inverse, the modular power and Chinese
//! remaindering.
//!
//! Every entry runs in the order of the exact numbers: the domain test,
//! where it has one; the check of a bound on the bits of the integers that it
//! computes against `max_integer_bits`, computed from its operands alone; the
//! charge, whose amount depends only on the operands; the computation; the
//! check of the bits of the integers that it computes; and the check of the
//! storage cost of the returned value with `check_storage` at
//! `LimitScope::Value`. An entry that runs several steps checks its bound on
//! entry, before any charge; the one domain test that comes later, of a
//! negative power in `modular_power` whose base is not a unit, follows the
//! charges of the inverse. Euclid's steps in `gcd` and `lcm` are covered by
//! that bound, since their remainders decrease, and are only charged; every
//! other step checks its own bound and charges before it computes, and
//! checks the bits of the integers that it computes. An integer that an
//! entry returns without computing it, such as the power $a^0 \bmod m = 1$
//! for $m \gt 1$, is covered by the bound on entry. The intermediate values
//! are checked by their bits only, never by their storage. The kernel charges
//! work and checks storage, and opens no frame and reserves no temporary.
//!
//! The amounts are counted in machine words: with
//! $W(x) = \max(1, \lceil \lvert x \rvert / 64 \rceil)$ for the bit length
//! $\lvert x \rvert$, a product, a quotient and a remainder of $x$ and $y$
//! charge $W(x) W(y)$ units, a sum, a difference, a negation and an absolute
//! value one unit.
//!
//! The code follows the shapes of the provable subset of Rust: `match` and
//! `if` instead of combinators with closures, index loops over slices, at most
//! one loop per function, and every loop in a helper that leaves before its
//! loop through no `?` and no `return`. The kernel is not a proof target: its
//! integers are those of num-bigint, whose operations would be trusted
//! external functions. The rules are stated in the component contract,
//! `docs/components/numbers/contract.md`.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{Euclid, One, Signed, Zero};

use super::arithmetic::internal;
use super::{Integer, division_by_zero, words};
use crate::context::{Storage, StorageCost};
use crate::{Context, Error, FaultKind, LimitField, LimitScope, Result};

// ---------------------------------------------------------------------------
// Words, bounds and checks

/// The charge of a product, a quotient or a remainder of `x` and `y`: the
/// product $W(x) W(y)$ of their words, saturating at `u64::MAX`.
fn word_product(x: &BigInt, y: &BigInt) -> u64 {
    words(x.bits()).saturating_mul(words(y.bits()))
}

/// The larger of two bit lengths.
const fn larger(a: u64, b: u64) -> u64 {
    if a < b { b } else { a }
}

/// Checks `bound` against `max_integer_bits`, then charges `units`.
fn admit(bound: u64, units: u64, context: &mut Context) -> Result<()> {
    context.check(LimitField::IntegerBits, bound)?;
    context.charge(units)
}

/// `value` after the check of its bits against `max_integer_bits`. A bound
/// of at least these bits was checked before the charge, by the step or on
/// entry, so this check fails only if a bound is wrong.
fn checked(value: BigInt, context: &Context) -> Result<BigInt> {
    context.check(LimitField::IntegerBits, value.bits())?;
    Ok(value)
}

/// `value` after the check of its storage cost, together with the open
/// frames and the reserved temporaries, at `LimitScope::Value`.
fn admitted<T: StorageCost>(value: T, context: &Context) -> Result<T> {
    context.check_storage(value.storage(), LimitScope::Value)?;
    Ok(value)
}

/// The fault of an argument outside the domain of an operation.
fn outside_domain(what: &str) -> Error {
    Error::new(FaultKind::OutsideDomain, None, what)
}

/// The fault of a modulus that is not positive.
fn non_positive_modulus() -> Error {
    outside_domain("the modulus is not positive")
}

// ---------------------------------------------------------------------------
// The steps: checked, charged and computed, without a storage check

/// $a + b$, with the bound $\max(\lvert a \rvert, \lvert b \rvert) + 1$ and
/// one unit.
fn sum(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<BigInt> {
    admit(larger(a.bits(), b.bits()).saturating_add(1), 1, context)?;
    checked(a + b, context)
}

/// $a - b$, with the bound $\max(\lvert a \rvert, \lvert b \rvert) + 1$ and
/// one unit.
fn difference(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<BigInt> {
    admit(larger(a.bits(), b.bits()).saturating_add(1), 1, context)?;
    checked(a - b, context)
}

/// $a b$, with the bound $\lvert a \rvert + \lvert b \rvert$ and
/// $W(a) W(b)$ units.
fn product(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<BigInt> {
    admit(
        a.bits().saturating_add(b.bits()),
        word_product(a, b),
        context,
    )?;
    checked(a * b, context)
}

/// The Euclidean division of $a$ by $b \ne 0$: $(q, r)$ with $a = q b + r$
/// and $0 \le r \lt \lvert b \rvert$, with the bound
/// $\max(\lvert a \rvert, \lvert b \rvert)$ and $W(a) W(b)$ units.
///
/// # Errors
///
/// `Internal` for $b = 0$, which every caller rejects or excludes first.
fn division(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<(BigInt, BigInt)> {
    if b.is_zero() {
        return Err(internal(None, "an integer division by zero"));
    }
    admit(larger(a.bits(), b.bits()), word_product(a, b), context)?;
    let (quotient, remainder) = Euclid::div_rem_euclid(a, b);
    let quotient = checked(quotient, context)?;
    let remainder = checked(remainder, context)?;
    Ok((quotient, remainder))
}

/// The least nonnegative residue of $a$ modulo $m \gt 0$, with the bound
/// $\max(\lvert a \rvert, \lvert m \rvert)$ and $W(a) W(m)$ units.
///
/// # Errors
///
/// `Internal` for $m \le 0$, which every caller rejects or excludes first.
fn remainder(a: &BigInt, m: &BigInt, context: &mut Context) -> Result<BigInt> {
    if !m.is_positive() {
        return Err(internal(
            None,
            "a remainder modulo a modulus that is not positive",
        ));
    }
    admit(larger(a.bits(), m.bits()), word_product(a, m), context)?;
    checked(Euclid::rem_euclid(a, m), context)
}

/// $a b \bmod m$ for $m \gt 0$ on one path: the product, then its
/// remainder.
fn modular_product(a: &BigInt, b: &BigInt, m: &BigInt, context: &mut Context) -> Result<BigInt> {
    let value = product(a, b, context)?;
    remainder(&value, m, context)
}

// ---------------------------------------------------------------------------
// The arithmetic of `Integer`

impl Integer {
    /// The sum $a + b$ of `self` $= a$ and `other` $= b$.
    ///
    /// Checks the bound $\max(\lvert a \rvert, \lvert b \rvert) + 1$ against
    /// `max_integer_bits`, then charges one unit.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Integer;
    /// use kalyx::{Context, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let sum = Integer::from(-12_i64).add(&Integer::from(18_i64), &mut context)?;
    /// assert_eq!(sum, Integer::from(6_i64));
    /// assert_eq!(context.work_used(), 1);
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when the bound exceeds
    /// `max_integer_bits`, before the charge; the request failures of the
    /// charge; and `ResourceLimit` with `LimitField::Nodes` or
    /// `LimitField::StorageBytes` and `LimitScope::Value` when the result does
    /// not fit together with what the context retains.
    pub fn add(&self, other: &Self, context: &mut Context) -> Result<Self> {
        let value = sum(&self.0, &other.0, context)?;
        admitted(Self(value), context)
    }

    /// The difference $a - b$ of `self` $= a$ and `other` $= b$, with the
    /// bound and the charge of [`add`](Integer::add).
    ///
    /// # Errors
    ///
    /// As [`add`](Integer::add).
    pub fn subtract(&self, other: &Self, context: &mut Context) -> Result<Self> {
        let value = difference(&self.0, &other.0, context)?;
        admitted(Self(value), context)
    }

    /// The product $a b$ of `self` $= a$ and `other` $= b$.
    ///
    /// Checks the bound $\lvert a \rvert + \lvert b \rvert$, then charges
    /// $W(a) W(b)$ units, the product of the machine words of the operands.
    ///
    /// # Errors
    ///
    /// As [`add`](Integer::add).
    pub fn multiply(&self, other: &Self, context: &mut Context) -> Result<Self> {
        let value = product(&self.0, &other.0, context)?;
        admitted(Self(value), context)
    }

    /// The negation $-a$ of `self` $= a$.
    ///
    /// Checks the bits $\lvert a \rvert$, then charges one unit.
    ///
    /// # Errors
    ///
    /// As [`add`](Integer::add).
    pub fn negate(&self, context: &mut Context) -> Result<Self> {
        admit(self.bits(), 1, context)?;
        let value = checked(-&self.0, context)?;
        admitted(Self(value), context)
    }

    /// The absolute value $\lvert \mathrm{self} \rvert$, with the bound and
    /// the charge of [`negate`](Integer::negate).
    ///
    /// # Errors
    ///
    /// As [`add`](Integer::add).
    pub fn absolute(&self, context: &mut Context) -> Result<Self> {
        admit(self.bits(), 1, context)?;
        let value = checked(self.0.abs(), context)?;
        admitted(Self(value), context)
    }

    /// The Euclidean division of `self` $= a$ by `divisor` $= b$: the quotient $q$ and
    /// the remainder $r$ with $a = q b + r$ and $0 \le r \lt \lvert b \rvert$,
    /// so $q = \mathrm{sign}(b) \lfloor a / \lvert b \rvert \rfloor$: rounded
    /// down for $b \gt 0$ and up for $b \lt 0$.
    ///
    /// Tests the divisor for zero first; then checks the bound
    /// $\max(\lvert a \rvert, \lvert b \rvert)$, then charges $W(a) W(b)$
    /// units.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Integer;
    /// use kalyx::{Context, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let division = Integer::from(-7_i64).divide_with_remainder(&Integer::from(-2_i64), &mut context)?;
    /// assert_eq!(division.quotient(), &Integer::from(4_i64));
    /// assert_eq!(division.remainder(), &Integer::from(1_i64));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `divisor` is zero, before any check or
    /// charge; otherwise as [`add`](Integer::add).
    pub fn divide_with_remainder(
        &self,
        divisor: &Self,
        context: &mut Context,
    ) -> Result<IntegerDivision> {
        if divisor.is_zero() {
            return Err(division_by_zero(None));
        }
        let (quotient, remainder) = division(&self.0, &divisor.0, context)?;
        admitted(
            IntegerDivision {
                quotient: Self(quotient),
                remainder: Self(remainder),
            },
            context,
        )
    }

    /// The exact quotient $a / b$ of `self` $= a$ by `divisor` $= b$: the
    /// quotient when $b$ divides $a$, and otherwise [`ExactQuotient::NotDivisible`], which
    /// is a value, not an error.
    ///
    /// Tests the divisor for zero first; then checks the bound and charges
    /// the amount of [`divide_with_remainder`](Integer::divide_with_remainder).
    ///
    /// # Errors
    ///
    /// As [`divide_with_remainder`](Integer::divide_with_remainder).
    pub fn exact_quotient(&self, divisor: &Self, context: &mut Context) -> Result<ExactQuotient> {
        if divisor.is_zero() {
            return Err(division_by_zero(None));
        }
        let (quotient, remainder) = division(&self.0, &divisor.0, context)?;
        let result = if remainder.is_zero() {
            ExactQuotient::Quotient(Self(quotient))
        } else {
            ExactQuotient::NotDivisible
        };
        admitted(result, context)
    }
}

impl StorageCost for Integer {
    /// One node and $\lvert z \rvert + 4$ bytes, the cost of the rational
    /// $z/1$; saturating at `u64::MAX`.
    fn storage(&self) -> Storage {
        Storage::new(1, self.bits().saturating_add(4))
    }
}

/// The quotient and the remainder of a Euclidean division, returned by
/// [`Integer::divide_with_remainder`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntegerDivision {
    quotient: Integer,
    remainder: Integer,
}

impl IntegerDivision {
    /// The quotient $q$.
    #[must_use]
    pub const fn quotient(&self) -> &Integer {
        &self.quotient
    }

    /// The remainder $r$, with $0 \le r \lt \lvert b \rvert$.
    #[must_use]
    pub const fn remainder(&self) -> &Integer {
        &self.remainder
    }
}

impl StorageCost for IntegerDivision {
    /// The costs of the quotient and the remainder added:
    /// $(2, \lvert q \rvert + \lvert r \rvert + 8)$.
    fn storage(&self) -> Storage {
        self.quotient
            .storage()
            .saturating_add(self.remainder.storage())
    }
}

/// The outcome of [`Integer::exact_quotient`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExactQuotient {
    /// The divisor divides the dividend, with this quotient.
    Quotient(Integer),
    /// The divisor does not divide the dividend.
    NotDivisible,
}

impl StorageCost for ExactQuotient {
    /// The cost of the quotient, or $(1, 4)$ when there is none.
    fn storage(&self) -> Storage {
        match self {
            Self::Quotient(quotient) => quotient.storage(),
            Self::NotDivisible => Storage::new(1, 4),
        }
    }
}

// ---------------------------------------------------------------------------
// GCD, LCM and the extended GCD

/// The greatest common divisor of `a` and `b`, nonnegative, with
/// $\gcd(0, 0) = 0$.
///
/// Checks the bound $\max(\lvert a \rvert, \lvert b \rvert)$, which covers
/// every step, then runs Euclid's algorithm on $\lvert a \rvert$ and
/// $\lvert b \rvert$, charging each step $(x, y) \mapsto (y, x \bmod y)$
/// $W(x) W(y)$ units before it computes the remainder.
///
/// ```
/// use kalyx::context::CancelFlag;
/// use kalyx::number::{self, Integer};
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let g = number::gcd(&Integer::from(-12_i64), &Integer::from(18_i64), &mut context)?;
/// assert_eq!(g, Integer::from(6_i64));
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// # Errors
///
/// As [`Integer::add`].
pub fn gcd(a: &Integer, b: &Integer, context: &mut Context) -> Result<Integer> {
    context.check(LimitField::IntegerBits, larger(a.bits(), b.bits()))?;
    let value = euclid(&a.0, &b.0, context)?;
    let value = checked(value, context)?;
    admitted(Integer(value), context)
}

/// Euclid's algorithm on $\lvert a \rvert$ and $\lvert b \rvert$, charging
/// each step before it.
fn euclid(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<BigInt> {
    let mut left = a.abs();
    let mut right = b.abs();
    while !right.is_zero() {
        context.charge(word_product(&left, &right))?;
        let next = &left % &right;
        left = right;
        right = next;
    }
    Ok(left)
}

/// The least common multiple of `a` and `b`, nonnegative, and 0 when an
/// operand is 0.
///
/// Checks the bound $\max(\lvert a \rvert, \lvert b \rvert)$; runs the
/// steps of [`gcd`]; and for $g = \gcd(a, b) \ne 0$ computes the exact
/// quotient $\lvert a \rvert / g$ and the product
/// $(\lvert a \rvert / g) \lvert b \rvert$, each with its own bound and
/// charge.
///
/// # Errors
///
/// As [`Integer::add`].
pub fn lcm(a: &Integer, b: &Integer, context: &mut Context) -> Result<Integer> {
    context.check(LimitField::IntegerBits, larger(a.bits(), b.bits()))?;
    let divisor = euclid(&a.0, &b.0, context)?;
    if divisor.is_zero() {
        return admitted(Integer(BigInt::zero()), context);
    }
    let (quotient, _) = division(&a.0.abs(), &divisor, context)?;
    let value = product(&quotient, &b.0.abs(), context)?;
    admitted(Integer(value), context)
}

/// The GCD $g \ge 0$ of two integers $a$ and $b$ with coefficients $s$ and
/// $t$ such that $g = s a + t b$, returned by [`extended_gcd`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntegerBezout {
    gcd: Integer,
    left: Integer,
    right: Integer,
}

impl IntegerBezout {
    /// The GCD $g$.
    #[must_use]
    pub const fn gcd(&self) -> &Integer {
        &self.gcd
    }

    /// The coefficient $s$ of $a$.
    #[must_use]
    pub const fn left(&self) -> &Integer {
        &self.left
    }

    /// The coefficient $t$ of $b$.
    #[must_use]
    pub const fn right(&self) -> &Integer {
        &self.right
    }
}

impl StorageCost for IntegerBezout {
    /// The costs of the three integers added:
    /// $(3, \lvert g \rvert + \lvert s \rvert + \lvert t \rvert + 12)$.
    fn storage(&self) -> Storage {
        self.gcd
            .storage()
            .saturating_add(self.left.storage())
            .saturating_add(self.right.storage())
    }
}

impl fmt::Display for IntegerBezout {
    /// `gcd: g; left: s; right: t`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "gcd: {}; left: {}; right: {}",
            self.gcd, self.left, self.right
        )
    }
}

/// The GCD of `a` and `b` with Bézout coefficients: $g = s a + t b$ with
/// $g \ge 0$.
///
/// The extended Euclidean algorithm runs on $\lvert a \rvert$ and
/// $\lvert b \rvert$ and the signs of $a$ and $b$ are then given to $s$ and
/// $t$, so $(240, 46)$ gives $(2, -9, 47)$, and $(0, 0)$ gives $(0, 0, 0)$.
/// Checks the bound $\max(\lvert a \rvert, \lvert b \rvert) + 2$, which
/// covers the products and differences of the coefficients; then each round
/// charges one Euclidean division, two products and two differences, each
/// with its own bound and charge.
///
/// # Errors
///
/// As [`Integer::add`].
pub fn extended_gcd(a: &Integer, b: &Integer, context: &mut Context) -> Result<IntegerBezout> {
    let (gcd, left, right) = checked_bezout(&a.0, &b.0, context)?;
    let left = if a.is_negative() { -left } else { left };
    let right = if b.is_negative() { -right } else { right };
    admitted(
        IntegerBezout {
            gcd: Integer(gcd),
            left: Integer(left),
            right: Integer(right),
        },
        context,
    )
}

/// [`bezout`] after the check of its bound
/// $\max(\lvert a \rvert, \lvert b \rvert) + 2$.
fn checked_bezout(
    a: &BigInt,
    b: &BigInt,
    context: &mut Context,
) -> Result<(BigInt, BigInt, BigInt)> {
    context.check(
        LimitField::IntegerBits,
        larger(a.bits(), b.bits()).saturating_add(2),
    )?;
    bezout(a, b, context)
}

/// The extended Euclidean algorithm on $\lvert a \rvert$ and
/// $\lvert b \rvert$: $(g, s, t)$ with $g = s \lvert a \rvert + t \lvert b \rvert$.
fn bezout(a: &BigInt, b: &BigInt, context: &mut Context) -> Result<(BigInt, BigInt, BigInt)> {
    let mut old_r = a.abs();
    let mut r = b.abs();
    let mut old_s = if a.is_zero() && b.is_zero() {
        BigInt::zero()
    } else {
        BigInt::one()
    };
    let mut s = BigInt::zero();
    let mut old_t = BigInt::zero();
    let mut t = BigInt::one();
    while !r.is_zero() {
        let (q, next_r) = division(&old_r, &r, context)?;
        let qs = product(&q, &s, context)?;
        let next_s = difference(&old_s, &qs, context)?;
        let qt = product(&q, &t, context)?;
        let next_t = difference(&old_t, &qt, context)?;
        old_r = r;
        r = next_r;
        old_s = s;
        s = next_s;
        old_t = t;
        t = next_t;
    }
    Ok((old_r, old_s, old_t))
}

// ---------------------------------------------------------------------------
// Modular inverse and modular power

/// The outcome of [`modular_inverse`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ModularInverse {
    /// The residue is a unit, with this inverse $v$, $0 \le v \lt m$.
    Inverse(Integer),
    /// The residue is not a unit: $g = \gcd(a \bmod m, m) \gt 1$, which is
    /// $m$ for a residue of zero.
    NonUnit(Integer),
}

impl StorageCost for ModularInverse {
    /// The cost of the integer that it carries.
    fn storage(&self) -> Storage {
        match self {
            Self::Inverse(inverse) => inverse.storage(),
            Self::NonUnit(divisor) => divisor.storage(),
        }
    }
}

/// The inverse of `a` modulo `modulus`: [`ModularInverse::Inverse`] with $v$,
/// $0 \le v \lt m$ and $a v \equiv 1 \pmod m$, when $\gcd(a, m) = 1$, and
/// otherwise [`ModularInverse::NonUnit`] with $g = \gcd(a \bmod m, m)$.
/// Modulo 1 every residue is the unit 0, whose inverse is 0.
///
/// Tests the modulus first; then checks the bound
/// $\max(\lvert a \rvert, \lvert m \rvert)$ and, for $m \gt 1$, also
/// $\lvert m \rvert + 2$, the bound of the extended Euclidean algorithm on
/// $a \bmod m$ and $m$, whatever the residue; then charges the remainder
/// $a \bmod m$ and, for $m \gt 1$, the rounds of [`extended_gcd`] on it and
/// $m$ and, for a unit, the remainder of its coefficient modulo $m$.
///
/// ```
/// use kalyx::context::CancelFlag;
/// use kalyx::number::{self, Integer, ModularInverse};
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let seven = Integer::from(7_i64);
/// assert_eq!(
///     number::modular_inverse(&Integer::from(3_i64), &seven, &mut context)?,
///     ModularInverse::Inverse(Integer::from(5_i64))
/// );
/// assert_eq!(
///     number::modular_inverse(&Integer::from(6_i64), &Integer::from(9_i64), &mut context)?,
///     ModularInverse::NonUnit(Integer::from(3_i64))
/// );
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// # Errors
///
/// `Fault(OutsideDomain)` when the modulus is not positive, before any check
/// or charge; otherwise as [`Integer::add`].
pub fn modular_inverse(
    a: &Integer,
    modulus: &Integer,
    context: &mut Context,
) -> Result<ModularInverse> {
    if !modulus.is_positive() {
        return Err(non_positive_modulus());
    }
    context.check(LimitField::IntegerBits, inverse_bound(a, modulus))?;
    let inverse = residue_inverse(&a.0, &modulus.0, context)?;
    admitted(inverse, context)
}

/// The bound of [`modular_inverse`]: the bits of the operands and, for a
/// modulus above 1, its bits plus 2.
fn inverse_bound(a: &Integer, modulus: &Integer) -> u64 {
    let operands = larger(a.bits(), modulus.bits());
    if modulus.0.is_one() {
        operands
    } else {
        larger(operands, modulus.bits().saturating_add(2))
    }
}

/// The inverse of $a$ modulo $m \gt 0$, after the check of the bound.
fn residue_inverse(a: &BigInt, m: &BigInt, context: &mut Context) -> Result<ModularInverse> {
    let residue = remainder(a, m, context)?;
    if m.is_one() {
        return Ok(ModularInverse::Inverse(Integer(residue)));
    }
    let (gcd, left, _) = bezout(&residue, m, context)?;
    if !gcd.is_one() {
        return Ok(ModularInverse::NonUnit(Integer(gcd)));
    }
    let inverse = remainder(&left, m, context)?;
    Ok(ModularInverse::Inverse(Integer(inverse)))
}

/// The power $a^e \bmod m$ in $[0, m)$, with $a^0 \equiv 1$, so the result
/// is 0 modulo 1; a negative exponent raises the inverse of $a$.
///
/// Tests the modulus first; then checks the bound
/// $\max(\lvert a \rvert, \lvert e \rvert, \lvert m \rvert)$ and, for
/// $e \ne 0$, also $2 \lvert m \rvert$, the bound of the product of two
/// residues, which covers the inverse; the exponent is checked by its bits
/// only, never against `max_exponent`. Then it charges the remainder
/// $a \bmod m$, or for $e \lt 0$ the steps of [`modular_inverse`], and
/// binary powering over the bits of $\lvert e \rvert$ from the lowest: each
/// multiplication by the base and each squaring is one product and one
/// remainder modulo $m$, on one path under every limit.
///
/// ```
/// use kalyx::context::CancelFlag;
/// use kalyx::number::{self, Integer};
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// // 3 * 4 = 12 = 1 (mod 11), so 3^-2 = 4^2 = 16 = 5 (mod 11).
/// let power = number::modular_power(
///     &Integer::from(3_i64),
///     &Integer::from(-2_i64),
///     &Integer::from(11_i64),
///     &mut context,
/// )?;
/// assert_eq!(power, Integer::from(5_i64));
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// # Errors
///
/// `Fault(OutsideDomain)` when the modulus is not positive, before any check
/// or charge, and for a negative exponent when the base is not a unit modulo
/// $m$, after the charges of the inverse; otherwise as [`Integer::add`].
pub fn modular_power(
    base: &Integer,
    exponent: &Integer,
    modulus: &Integer,
    context: &mut Context,
) -> Result<Integer> {
    if !modulus.is_positive() {
        return Err(non_positive_modulus());
    }
    context.check(
        LimitField::IntegerBits,
        power_bound(base, exponent, modulus),
    )?;
    let residue = power_base(&base.0, &exponent.0, &modulus.0, context)?;
    let value = powering(residue, exponent.0.magnitude(), &modulus.0, context)?;
    admitted(Integer(value), context)
}

/// The bound of [`modular_power`]: the bits of the operands and, for a
/// nonzero exponent, twice the bits of the modulus.
fn power_bound(base: &Integer, exponent: &Integer, modulus: &Integer) -> u64 {
    let operands = larger(larger(base.bits(), exponent.bits()), modulus.bits());
    if exponent.is_zero() {
        operands
    } else {
        larger(operands, modulus.bits().saturating_add(modulus.bits()))
    }
}

/// The residue that binary powering raises: $a \bmod m$, or for a negative
/// exponent the inverse of $a$ modulo $m$.
fn power_base(
    base: &BigInt,
    exponent: &BigInt,
    modulus: &BigInt,
    context: &mut Context,
) -> Result<BigInt> {
    if !exponent.is_negative() {
        return remainder(base, modulus, context);
    }
    match residue_inverse(base, modulus, context)? {
        ModularInverse::Inverse(inverse) => Ok(inverse.0),
        ModularInverse::NonUnit(_) => Err(outside_domain(
            "a negative power of a residue that is not a unit",
        )),
    }
}

/// $b^e \bmod m$ for a residue $b$ and $m \gt 0$ by binary powering over
/// the bits of $e$ from the lowest.
fn powering(
    base: BigInt,
    exponent: &BigUint,
    modulus: &BigInt,
    context: &mut Context,
) -> Result<BigInt> {
    let length = exponent.bits();
    let mut square = base;
    let mut power = if modulus.is_one() {
        BigInt::zero()
    } else {
        BigInt::one()
    };
    let mut bit = 0;
    while bit < length {
        if exponent.bit(bit) {
            power = modular_product(&power, &square, modulus, context)?;
        }
        bit += 1;
        if bit < length {
            square = modular_product(&square, &square, modulus, context)?;
        }
    }
    Ok(power)
}

// ---------------------------------------------------------------------------
// Congruences and Chinese remaindering

/// The congruence $x \equiv r \pmod m$, with $m \gt 0$ and the least
/// nonnegative residue $0 \le r \lt m$.
///
/// A congruence is built only by [`Congruence::new`] and [`crt`], so its
/// fields are private:
///
/// ```compile_fail,E0451
/// use kalyx::number::{Congruence, Integer};
///
/// let wrong = Congruence { residue: Integer::from(9_i64), modulus: Integer::from(0_i64) };
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Congruence {
    // Invariant: 0 <= residue < modulus.
    residue: Integer,
    modulus: Integer,
}

impl Congruence {
    /// The congruence $x \equiv r \pmod m$, with the residue reduced into
    /// $[0, m)$.
    ///
    /// Tests the modulus first; then checks the bound
    /// $\max(\lvert r \rvert, \lvert m \rvert)$, then charges the remainder,
    /// $W(r) W(m)$ units.
    ///
    /// # Errors
    ///
    /// `Fault(OutsideDomain)` when the modulus is not positive, before any
    /// check or charge; otherwise as [`Integer::add`].
    pub fn new(residue: &Integer, modulus: &Integer, context: &mut Context) -> Result<Self> {
        if !modulus.is_positive() {
            return Err(non_positive_modulus());
        }
        context.check(
            LimitField::IntegerBits,
            larger(residue.bits(), modulus.bits()),
        )?;
        let value = remainder(&residue.0, &modulus.0, context)?;
        admitted(
            Self {
                residue: Integer(value),
                modulus: modulus.clone(),
            },
            context,
        )
    }

    /// The residue $r$, $0 \le r \lt m$.
    #[must_use]
    pub const fn residue(&self) -> &Integer {
        &self.residue
    }

    /// The modulus $m \gt 0$.
    #[must_use]
    pub const fn modulus(&self) -> &Integer {
        &self.modulus
    }
}

impl StorageCost for Congruence {
    /// The costs of the residue and the modulus added:
    /// $(2, \lvert r \rvert + \lvert m \rvert + 8)$.
    fn storage(&self) -> Storage {
        self.residue
            .storage()
            .saturating_add(self.modulus.storage())
    }
}

impl fmt::Display for Congruence {
    /// `r mod m`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} mod {}", self.residue, self.modulus)
    }
}

/// The outcome of [`crt`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CrtResult {
    /// The solutions are exactly this congruence, modulo the LCM of the
    /// moduli.
    Solution(Congruence),
    /// The congruences have no common solution.
    Inconsistent,
}

impl StorageCost for CrtResult {
    /// The cost of the congruence, or $(1, 4)$ when there is none.
    fn storage(&self) -> Storage {
        match self {
            Self::Solution(solution) => solution.storage(),
            Self::Inconsistent => Storage::new(1, 4),
        }
    }
}

impl fmt::Display for CrtResult {
    /// The congruence, or `inconsistent`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Solution(solution) => fmt::Display::fmt(solution, f),
            Self::Inconsistent => f.write_str("inconsistent"),
        }
    }
}

/// The common solutions of `congruences`, whose moduli need not be coprime:
/// [`CrtResult::Solution`] with $r \bmod l$, $l$ the LCM of the moduli, or
/// [`CrtResult::Inconsistent`]. The empty system is $0 \bmod 1$.
///
/// Checks the bits of every residue and modulus against the receiving
/// `max_integer_bits`, and at least one bit, the bits of the modulus 1 of the
/// empty system, before any charge; then merges the congruences in
/// order into $r \bmod M$, from $0 \bmod 1$, and returns `Inconsistent` at
/// the first congruence that contradicts the ones before it. Merging
/// $x \equiv r_i \pmod{m_i}$ runs, each with its own bound and charge: the
/// extended GCD $g = s M + t m_i$; the difference $\delta = r_i - r$; the
/// Euclidean division of $\delta$ by $g$, whose remainder decides
/// consistency and whose quotient is $\delta / g$; the exact quotient
/// $n = m_i / g$; the remainders of $\delta / g$ and of $s$ modulo $n$; their
/// product modulo $n$, $k$; and the products $M n$ and $M k$ and the sum
/// $r + M k$, the merged residue modulo $M n$.
///
/// ```
/// use kalyx::context::CancelFlag;
/// use kalyx::number::{self, Congruence, CrtResult, Integer};
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let mut congruence = |r: i64, m: i64| Congruence::new(&Integer::from(r), &Integer::from(m), &mut context);
/// let system = [congruence(2, 6)?, congruence(8, 9)?];
/// let odd_and_even = [congruence(1, 4)?, congruence(2, 6)?];
/// assert_eq!(number::crt(&system, &mut context)?.to_string(), "8 mod 18");
/// assert_eq!(number::crt(&odd_and_even, &mut context)?, CrtResult::Inconsistent);
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// # Errors
///
/// As [`Integer::add`].
pub fn crt(congruences: &[Congruence], context: &mut Context) -> Result<CrtResult> {
    context.check(LimitField::IntegerBits, widest(congruences))?;
    let result = combine(congruences, context)?;
    admitted(result, context)
}

/// The largest bit length of the residues and moduli of `congruences`, and
/// at least 1, which covers the modulus 1 of the solution of the empty
/// system.
fn widest(congruences: &[Congruence]) -> u64 {
    let mut bits = 1;
    let mut index = 0;
    while index < congruences.len() {
        let congruence = &congruences[index];
        bits = larger(
            bits,
            larger(congruence.residue.bits(), congruence.modulus.bits()),
        );
        index += 1;
    }
    bits
}

/// Merges `congruences` in order, from $0 \bmod 1$.
fn combine(congruences: &[Congruence], context: &mut Context) -> Result<CrtResult> {
    let mut residue = BigInt::zero();
    let mut modulus = BigInt::one();
    let mut index = 0;
    while index < congruences.len() {
        match merge(&residue, &modulus, &congruences[index], context)? {
            Some((next_residue, next_modulus)) => {
                residue = next_residue;
                modulus = next_modulus;
            }
            None => return Ok(CrtResult::Inconsistent),
        }
        index += 1;
    }
    Ok(CrtResult::Solution(Congruence {
        residue: Integer(residue),
        modulus: Integer(modulus),
    }))
}

/// The merge of $x \equiv r \pmod M$ with `next`: the residue and the
/// modulus of the merged congruence, or `None` when they contradict.
fn merge(
    residue: &BigInt,
    modulus: &BigInt,
    next: &Congruence,
    context: &mut Context,
) -> Result<Option<(BigInt, BigInt)>> {
    let (gcd, left, _) = checked_bezout(modulus, &next.modulus.0, context)?;
    let delta = difference(&next.residue.0, residue, context)?;
    let (quotient, rest) = division(&delta, &gcd, context)?;
    if !rest.is_zero() {
        return Ok(None);
    }
    let (reduced, _) = division(&next.modulus.0, &gcd, context)?;
    let step = remainder(&quotient, &reduced, context)?;
    let inverse = remainder(&left, &reduced, context)?;
    let shift = modular_product(&step, &inverse, &reduced, context)?;
    let merged = product(modulus, &reduced, context)?;
    let lift = product(modulus, &shift, context)?;
    let value = sum(residue, &lift, context)?;
    Ok(Some((value, merged)))
}
