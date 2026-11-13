//! The prime fields $\mathbb F_p$ of the primes $p \lt 2^{32}$: the parent
//! [`PrimeField`] and its elements, the [`PrimeResidue`]s.
//!
//! An element is the least nonnegative residue $0 \le r \lt p$ in a machine
//! word, and it does not repeat its parent. The arithmetic is that of four
//! private kernels over machine words, `add`, `sub`, `mul` and `inverse`,
//! pure functions of the modulus and the residues that take no context and
//! cannot fail: the sum, the difference and the product use 64-bit
//! intermediates, which hold $(p - 1)^2 \lt 2^{64}$, and the inverse is the
//! power $a^{p - 2}$ by binary powering. The methods of the coefficient
//! traits run in the order of the exact numbers: the domain tests come
//! first, of a residue at or above $p$, which can belong only to another
//! field, and of a zero divisor; then the bits of the new element are
//! checked against `max_integer_bits`, then the operation is charged, and
//! only then does a kernel compute. The constructor decides that the modulus
//! is prime with the modular power of the integer kernel.
//!
//! The code follows the shapes of the provable subset of Rust: no
//! combinators with closures, at most one loop per function, and every loop
//! in a helper that leaves before its loop through no `?` and no `return`.
//! The rules are stated in the component contract,
//! `docs/components/numbers/contract.md`.

use std::convert::Infallible;

use super::{CoefficientField, CoefficientRing, ZeroTest, sealed};
use crate::context::Storage;
use crate::number::{Integer, modular_power};
use crate::{Context, Error, FaultKind, LimitField, Result};

#[cfg(test)]
mod tests;

/// The bases of the strong probable-prime test of the constructor. No
/// composite below $4\,759\,123\,141$ passes the test to all three, so the
/// test is exact for every `u32`.
const BASES: [u32; 3] = [2, 7, 61];

/// The work units charged for a new element: zero, one, a negation, a sum,
/// a difference, a product, and the image of an integer before the division
/// that reduces it.
const ELEMENT_CHARGE: u64 = 1;

/// The work units charged for an inverse and for a quotient: the kernel
/// `inverse` runs at most 32 rounds, one for each bit of $p - 2$.
const INVERSE_CHARGE: u64 = 32;

/// The prime field $\mathbb F_p$ of a prime $p \lt 2^{32}$, whose elements
/// are the [`PrimeResidue`]s $0 \le r \lt p$.
///
/// A prime field is built only by [`PrimeField::new`], which decides that
/// its modulus is prime. Two prime fields are the same parent exactly when
/// their moduli are equal, which the derived `PartialEq`, `Eq` and `Hash`
/// and [`same_parent`](CoefficientRing::same_parent) compare. The zero test
/// is structural and always decides, so its reason type is [`Infallible`].
///
/// ```
/// use kalyx::coefficient::{CoefficientField, CoefficientRing, PrimeField, ZeroTest};
/// use kalyx::context::{CancelFlag, Storage};
/// use kalyx::number::Integer;
/// use kalyx::{Context, ErrorKind, FaultKind, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let f7 = PrimeField::new(7, &mut context)?;
/// let three = f7.from_integer(&Integer::from(3_i64), &mut context)?;
/// let inverse = f7.inverse(&three, &mut context)?;
/// assert_eq!(inverse.value(), 5);
/// let minus_one = f7.from_integer(&Integer::from(-1_i64), &mut context)?;
/// assert_eq!(minus_one.value(), 6);
/// let seven = f7.from_integer(&Integer::from(7_i64), &mut context)?;
/// assert_eq!(f7.zero_test(&seven, &mut context)?, ZeroTest::Zero);
/// // The residue 6 costs one node and |6| + 4 = 7 bytes.
/// assert_eq!(f7.measure(&minus_one), Storage::new(1, 7));
/// let error = PrimeField::new(91, &mut context).unwrap_err();
/// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::OutsideDomain));
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// Its field is private, so a prime field cannot be built from a modulus
/// that the constructor did not check:
///
/// ```compile_fail,E0451
/// use kalyx::coefficient::PrimeField;
///
/// let four = PrimeField { p: 4 };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PrimeField {
    // Invariant: p is a prime.
    p: u32,
}

/// An element of a [`PrimeField`]: the least nonnegative residue
/// $0 \le r \lt p$ of its class modulo $p$.
///
/// A residue is built only by the methods of its field, and it does not
/// repeat its field: the methods of a field assume that their residues
/// belong to it. A residue at or above the modulus can belong only to
/// another field, and every method of the field that takes it, but
/// [`measure`](CoefficientRing::measure), fails with `Fault(OutsideDomain)`
/// before any check or charge. Residues have no equality, since residues of
/// different fields could compare equal; they are compared through
/// [`value`](PrimeResidue::value) or through their field.
///
/// ```compile_fail,E0451
/// use kalyx::coefficient::PrimeResidue;
///
/// let nine = PrimeResidue { residue: 9 };
/// ```
///
/// ```compile_fail,E0369
/// use kalyx::coefficient::{CoefficientRing, PrimeField};
/// use kalyx::context::CancelFlag;
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let field = PrimeField::new(7, &mut context).unwrap();
/// let one = field.one(&mut context).unwrap();
/// let same = one == one;
/// ```
#[derive(Clone, Copy, Debug)]
pub struct PrimeResidue {
    // Invariant: residue < p for the field that built it.
    residue: u32,
}

impl PrimeResidue {
    /// The residue $r$, the least nonnegative representative
    /// $0 \le r \lt p$ of the class: in $\mathbb F_7$, $-1$ is 6.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.residue
    }
}

/// The fault of a modulus that is not a prime.
fn not_prime() -> Error {
    Error::new(
        FaultKind::OutsideDomain,
        None,
        "the modulus of a prime field is not a prime",
    )
}

/// The fault of a zero element to invert or a zero divisor.
fn division_by_zero() -> Error {
    Error::new(FaultKind::DivisionByZero, None, "division by zero")
}

/// The integer of a residue or a modulus.
fn integer(value: u32) -> Integer {
    Integer::from(u64::from(value))
}

impl PrimeField {
    /// The prime field $\mathbb F_p$ of the prime `p`.
    ///
    /// A modulus below 2, and an even modulus other than 2, fails before any
    /// check or charge; the modulus 2 is accepted at once. An odd modulus
    /// $p \ge 3$ is decided by the strong probable-prime test to the bases
    /// 2, 7 and 61, skipping a base equal to $p$: with
    /// $p - 1 = d \cdot 2^s$ and $d$ odd, each base $a$ gives
    /// $x = a^d \bmod p$, and the base is passed when $x$ is 1 or $p - 1$,
    /// or when one of at most $s - 1$ squarings modulo $p$ reaches $p - 1$.
    /// A prime passes every base; a composite below $4\,759\,123\,141$, the
    /// least composite that passes the three bases, fails one, so the test
    /// is exact for every `u32`. Each power and each squaring is a call of
    /// [`modular_power`](crate::number::modular_power), with its checks of
    /// `max_integer_bits`, $\max(6, 2 \lvert p \rvert)$ bits for a power
    /// and $2 \lvert p \rvert$ for a squaring, and its charges, so the
    /// constructor's work depends only on $p$. A composite modulus fails
    /// after those charges, and no field is built from it.
    ///
    /// # Errors
    ///
    /// `Fault(OutsideDomain)` when `p` is not a prime: before any check or
    /// charge for $p \lt 2$ and an even $p \ne 2$, after the charges of the
    /// test for an odd composite; otherwise the limits and request failures
    /// of `modular_power`.
    pub fn new(p: u32, context: &mut Context) -> Result<Self> {
        if p < 2 {
            return Err(not_prime());
        }
        if p == 2 {
            return Ok(Self { p });
        }
        if p.is_multiple_of(2) {
            return Err(not_prime());
        }
        if passes_every_base(p, context)? {
            Ok(Self { p })
        } else {
            Err(not_prime())
        }
    }

    /// The modulus $p$.
    #[must_use]
    pub const fn modulus(&self) -> u32 {
        self.p
    }

    /// The bit length $\lvert p \rvert$ of the modulus, the bound on the
    /// bits of every new element.
    const fn modulus_bits(self) -> u64 {
        (u32::BITS - self.p.leading_zeros()) as u64
    }

    /// Checks the bound $\lvert p \rvert$ of a new element against
    /// `max_integer_bits`, then charges `units`.
    fn admit(self, units: u64, context: &mut Context) -> Result<()> {
        context.check(LimitField::IntegerBits, self.modulus_bits())?;
        context.charge(units)
    }

    /// The residue of `a`, which must be below $p$: a residue at or above
    /// $p$ belongs to another field and is outside the domain of the
    /// operations of this one, whose kernel `sub` would go below zero on it.
    fn residue(self, a: &PrimeResidue) -> Result<u32> {
        if a.residue < self.p {
            Ok(a.residue)
        } else {
            Err(Error::new(
                FaultKind::OutsideDomain,
                None,
                "a residue at or above the modulus of the prime field",
            ))
        }
    }

    // The four kernels. Their residues are below p, which `residue` checks,
    // and the constructor makes p at least 2, so `add` and `mul` never divide
    // by zero, `sub` never goes below zero and `inverse` never lowers p below
    // zero.

    fn add(self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(b)) % u64::from(self.p)) as u32
    }
    fn sub(self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(self.p) - u64::from(b)) % u64::from(self.p)) as u32
    }
    fn mul(self, a: u32, b: u32) -> u32 {
        ((u64::from(a) * u64::from(b)) % u64::from(self.p)) as u32
    }

    /// $a^{p - 2} \bmod p$ by binary powering from the lowest bit of
    /// $p - 2$: the inverse of a nonzero residue $a$, by Fermat's little
    /// theorem.
    fn inverse(self, a: u32) -> u32 {
        let mut a = a;
        let mut n = self.p - 2;
        let mut result = 1;
        while n != 0 {
            if n & 1 != 0 {
                result = self.mul(result, a);
            }
            n >>= 1;
            if n != 0 {
                a = self.mul(a, a);
            }
        }
        result
    }
}

/// Whether the odd `p` $\ge 3$ passes the strong probable-prime test to
/// every base of [`BASES`] other than `p` itself.
fn passes_every_base(p: u32, context: &mut Context) -> Result<bool> {
    let below = p - 1;
    let twos = below.trailing_zeros();
    let odd = below >> twos;
    let mut index = 0;
    while index < BASES.len() {
        let base = BASES[index];
        if base != p && !passes_base(base, p, (odd, twos), context)? {
            return Ok(false);
        }
        index += 1;
    }
    Ok(true)
}

/// Whether `p` passes the test to `base`, with $p - 1 = d \cdot 2^s$ for
/// `split` $= (d, s)$: $x = a^d \bmod p$ is 1 or $p - 1$, or squaring it
/// reaches $p - 1$.
fn passes_base(base: u32, p: u32, split: (u32, u32), context: &mut Context) -> Result<bool> {
    let (odd, twos) = split;
    let modulus = integer(p);
    let minus_one = integer(p - 1);
    let x = modular_power(&integer(base), &integer(odd), &modulus, context)?;
    if x == integer(1) || x == minus_one {
        return Ok(true);
    }
    squares_reach(x, &modulus, &minus_one, twos - 1, context)
}

/// Whether squaring `x` modulo `modulus` at most `squarings` times reaches
/// `target`.
fn squares_reach(
    x: Integer,
    modulus: &Integer,
    target: &Integer,
    squarings: u32,
    context: &mut Context,
) -> Result<bool> {
    let two = integer(2);
    let mut x = x;
    let mut step = 0;
    while step < squarings {
        x = modular_power(&x, &two, modulus, context)?;
        if x == *target {
            return Ok(true);
        }
        step += 1;
    }
    Ok(false)
}

impl sealed::Sealed for PrimeField {}

impl CoefficientRing for PrimeField {
    type Element = PrimeResidue;
    type Undecided = Infallible;

    /// Whether the moduli are equal, without a charge.
    fn same_parent(&self, other: &Self, _context: &mut Context) -> Result<bool> {
        Ok(self.p == other.p)
    }

    /// The residue 0, after the check of $\lvert p \rvert$ bits and one
    /// unit.
    fn zero(&self, context: &mut Context) -> Result<PrimeResidue> {
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue { residue: 0 })
    }

    /// The residue 1, after the check of $\lvert p \rvert$ bits and one
    /// unit.
    fn one(&self, context: &mut Context) -> Result<PrimeResidue> {
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue { residue: 1 })
    }

    /// The residue $n \bmod p$: checks the bound
    /// $\max(\lvert n \rvert, \lvert p \rvert)$ against `max_integer_bits`,
    /// then charges one unit, then divides $n$ by $p$ with
    /// [`Integer::divide_with_remainder`], with its checks and charges, and
    /// reads the remainder.
    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<PrimeResidue> {
        context.check(LimitField::IntegerBits, n.bits().max(self.modulus_bits()))?;
        context.charge(ELEMENT_CHARGE)?;
        let division = n.divide_with_remainder(&integer(self.p), context)?;
        match division.remainder().magnitude_u64() {
            Some(value) => match u32::try_from(value) {
                Ok(residue) => Ok(PrimeResidue { residue }),
                Err(_) => Err(Error::new(
                    FaultKind::Internal,
                    None,
                    "a remainder modulo a prime field beyond 32 bits",
                )),
            },
            None => Err(Error::new(
                FaultKind::Internal,
                None,
                "a remainder modulo a prime field beyond 64 bits",
            )),
        }
    }

    /// $(p - a) \bmod p$ by the kernel `sub`, after the check and the
    /// charge of a new element.
    fn negate(&self, a: &PrimeResidue, context: &mut Context) -> Result<PrimeResidue> {
        let a = self.residue(a)?;
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::sub(*self, 0, a),
        })
    }

    /// $(a + b) \bmod p$ by the kernel `add`, after the check and the
    /// charge of a new element.
    fn add(
        &self,
        a: &PrimeResidue,
        b: &PrimeResidue,
        context: &mut Context,
    ) -> Result<PrimeResidue> {
        let (a, b) = (self.residue(a)?, self.residue(b)?);
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::add(*self, a, b),
        })
    }

    /// $(a - b) \bmod p$ by the kernel `sub`, after the check and the
    /// charge of a new element.
    fn subtract(
        &self,
        a: &PrimeResidue,
        b: &PrimeResidue,
        context: &mut Context,
    ) -> Result<PrimeResidue> {
        let (a, b) = (self.residue(a)?, self.residue(b)?);
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::sub(*self, a, b),
        })
    }

    /// $a b \bmod p$ by the kernel `mul`, after the check and the charge of
    /// a new element.
    fn multiply(
        &self,
        a: &PrimeResidue,
        b: &PrimeResidue,
        context: &mut Context,
    ) -> Result<PrimeResidue> {
        let (a, b) = (self.residue(a)?, self.residue(b)?);
        self.admit(ELEMENT_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::mul(*self, a, b),
        })
    }

    /// [`ZeroTest::Zero`] exactly for the residue 0, otherwise
    /// [`ZeroTest::Nonzero`], without a charge.
    fn zero_test(&self, a: &PrimeResidue, _context: &mut Context) -> Result<ZeroTest<Infallible>> {
        if self.residue(a)? == 0 {
            Ok(ZeroTest::Zero)
        } else {
            Ok(ZeroTest::Nonzero)
        }
    }

    /// One node and $\lvert r \rvert + 4$ bytes for the residue $r$, the
    /// cost of the integer $r$.
    fn measure(&self, a: &PrimeResidue) -> Storage {
        let bits = u32::BITS - a.residue.leading_zeros();
        Storage::new(1, u64::from(bits) + 4)
    }
}

impl CoefficientField for PrimeField {
    /// $a^{p - 2} \bmod p$ by the kernel `inverse`: tests $a$ for zero
    /// first, then checks $\lvert p \rvert$ bits and charges 32 units.
    fn inverse(&self, a: &PrimeResidue, context: &mut Context) -> Result<PrimeResidue> {
        let a = self.residue(a)?;
        if a == 0 {
            return Err(division_by_zero());
        }
        self.admit(INVERSE_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::inverse(*self, a),
        })
    }

    /// $a b^{-1} \bmod p$ by the kernels `inverse` and `mul`: tests $b$ for
    /// zero first, then checks $\lvert p \rvert$ bits and charges 32 units.
    fn divide(
        &self,
        a: &PrimeResidue,
        b: &PrimeResidue,
        context: &mut Context,
    ) -> Result<PrimeResidue> {
        let (a, b) = (self.residue(a)?, self.residue(b)?);
        if b == 0 {
            return Err(division_by_zero());
        }
        self.admit(INVERSE_CHARGE, context)?;
        Ok(PrimeResidue {
            residue: Self::mul(*self, a, Self::inverse(*self, b)),
        })
    }
}
