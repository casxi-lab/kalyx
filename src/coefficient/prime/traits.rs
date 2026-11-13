//! The coefficient traits of the prime fields: `CoefficientRing` and
//! `CoefficientField` for [`PrimeField`], over the kernels of the parent
//! module.
//!
//! Each method tests its residues first, then a zero divisor, then checks
//! the bits of the new residue against `max_integer_bits`, then charges,
//! and only then calls the kernels, as `docs/components/numbers/contract.md`
//! states.

use std::convert::Infallible;

use super::{PrimeField, PrimeResidue, integer};
use crate::coefficient::{CoefficientField, CoefficientRing, ZeroTest, sealed};
use crate::context::Storage;
use crate::number::Integer;
use crate::{Context, Error, FaultKind, LimitField, Result};

/// The work units charged for a new element: zero, one, a negation, a sum,
/// a difference, a product, and the image of an integer before the division
/// that reduces it.
const ELEMENT_CHARGE: u64 = 1;

/// The work units charged for an inverse and for a quotient: the kernel
/// `inverse` runs at most 32 rounds, one for each bit of $p - 2$.
const INVERSE_CHARGE: u64 = 32;

/// The fault of a zero element to invert or a zero divisor.
fn division_by_zero() -> Error {
    Error::new(FaultKind::DivisionByZero, None, "division by zero")
}

impl PrimeField {
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
