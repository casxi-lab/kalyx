//! Test-only coefficient fields of residues modulo a prime $p$, for the
//! tests of code that is generic over the coefficient traits, such as the
//! elimination skeleton.
//!
//! The coefficient traits are sealed, and the seal is visible only in this
//! module tree, so the test fields that other modules need are defined here.
//! Neither field charges the context: the code under test is then the only
//! source of checks and charges. [`UndecidedResidues`] answers undecided for
//! the zero test of the values of a chosen set, which may contain zero, and
//! reports every zero test that it answers; [`ExactResidues`] always decides.

use std::convert::Infallible;

use crate::coefficient::{CoefficientField, CoefficientRing, ZeroTest, sealed};
use crate::context::{CancelFlag, Storage};
use crate::number::Integer;
use crate::{Context, Error, FaultKind, Limits, Result};

/// `a * b` modulo `p`.
pub(crate) fn residue_product(p: u32, a: u32, b: u32) -> u32 {
    ((u64::from(a) * u64::from(b)) % u64::from(p)) as u32
}

/// `a^(p-2)`, the inverse of a nonzero residue, by repeated multiplication.
fn residue_inverse(p: u32, a: u32) -> Result<u32> {
    if a == 0 {
        return Err(Error::new(FaultKind::DivisionByZero, None, "zero residue"));
    }
    Ok((0..p - 2).fold(1, |result, _| residue_product(p, result, a)))
}

/// The residue of `n` modulo `p`, computed under a context of its own so
/// that the caller's context is not charged.
fn residue_of(p: u32, n: &Integer) -> Result<u32> {
    let mut scratch = Context::new(Limits::new(), CancelFlag::new());
    let division = n.divide_with_remainder(&Integer::from(u64::from(p)), &mut scratch)?;
    match division.remainder().magnitude_u64() {
        Some(value) => Ok((value % u64::from(p)) as u32),
        None => Err(Error::new(
            FaultKind::Internal,
            None,
            "a remainder beyond 64 bits",
        )),
    }
}

/// The residues modulo `p` whose zero test answers undecided, with the value
/// as its reason, for the values in `undecided`, and decides every other
/// value. Every answer is passed to `report`.
pub(crate) struct UndecidedResidues<'a> {
    pub(crate) p: u32,
    pub(crate) undecided: &'a [u32],
    pub(crate) report: &'a dyn Fn(u32, &ZeroTest<u32>),
}

impl sealed::Sealed for UndecidedResidues<'_> {}

impl CoefficientRing for UndecidedResidues<'_> {
    type Element = u32;
    type Undecided = u32;

    fn same_parent(&self, other: &Self, _context: &mut Context) -> Result<bool> {
        Ok(self.p == other.p && self.undecided == other.undecided)
    }

    fn zero(&self, _context: &mut Context) -> Result<u32> {
        Ok(0)
    }

    fn one(&self, _context: &mut Context) -> Result<u32> {
        Ok(1)
    }

    fn from_integer(&self, n: &Integer, _context: &mut Context) -> Result<u32> {
        residue_of(self.p, n)
    }

    fn negate(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        Ok((self.p - a) % self.p)
    }

    fn add(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(((u64::from(*a) + u64::from(*b)) % u64::from(self.p)) as u32)
    }

    fn subtract(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(((u64::from(*a) + u64::from(self.p) - u64::from(*b)) % u64::from(self.p)) as u32)
    }

    fn multiply(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_product(self.p, *a, *b))
    }

    fn zero_test(&self, a: &u32, _context: &mut Context) -> Result<ZeroTest<u32>> {
        let answer = if self.undecided.contains(a) {
            ZeroTest::Undecided(*a)
        } else if *a == 0 {
            ZeroTest::Zero
        } else {
            ZeroTest::Nonzero
        };
        (self.report)(*a, &answer);
        Ok(answer)
    }

    fn measure(&self, _a: &u32) -> Storage {
        Storage::new(1, 4)
    }
}

impl CoefficientField for UndecidedResidues<'_> {
    fn inverse(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        residue_inverse(self.p, *a)
    }

    fn divide(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_product(self.p, *a, residue_inverse(self.p, *b)?))
    }
}

/// The residues modulo `p` with a zero test that always decides.
pub(crate) struct ExactResidues {
    pub(crate) p: u32,
}

impl sealed::Sealed for ExactResidues {}

impl CoefficientRing for ExactResidues {
    type Element = u32;
    type Undecided = Infallible;

    fn same_parent(&self, other: &Self, _context: &mut Context) -> Result<bool> {
        Ok(self.p == other.p)
    }

    fn zero(&self, _context: &mut Context) -> Result<u32> {
        Ok(0)
    }

    fn one(&self, _context: &mut Context) -> Result<u32> {
        Ok(1)
    }

    fn from_integer(&self, n: &Integer, _context: &mut Context) -> Result<u32> {
        residue_of(self.p, n)
    }

    fn negate(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        Ok((self.p - a) % self.p)
    }

    fn add(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(((u64::from(*a) + u64::from(*b)) % u64::from(self.p)) as u32)
    }

    fn subtract(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(((u64::from(*a) + u64::from(self.p) - u64::from(*b)) % u64::from(self.p)) as u32)
    }

    fn multiply(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_product(self.p, *a, *b))
    }

    fn zero_test(&self, a: &u32, _context: &mut Context) -> Result<ZeroTest<Infallible>> {
        Ok(if *a == 0 {
            ZeroTest::Zero
        } else {
            ZeroTest::Nonzero
        })
    }

    fn measure(&self, _a: &u32) -> Storage {
        Storage::new(1, 4)
    }
}

impl CoefficientField for ExactResidues {
    fn inverse(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        residue_inverse(self.p, *a)
    }

    fn divide(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_product(self.p, *a, residue_inverse(self.p, *b)?))
    }
}
