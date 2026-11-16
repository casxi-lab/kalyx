//! Test-only coefficient fields of residues modulo a small prime $p$, for
//! the tests of code that is generic over the coefficient traits, such as
//! the elimination skeleton.
//!
//! The coefficient traits are sealed, and the seal is visible only in
//! `crate::coefficient` and its child modules, so the test fields that other
//! modules need are defined here. Neither field charges the context: the
//! code under test is then the only source of charges.
//! [`UndecidedResidues`] answers undecided for the zero test of the values
//! of a chosen set, which may contain zero, and reports every zero test that
//! it answers; [`ExactResidues`] always decides.

use std::convert::Infallible;

use crate::coefficient::{CoefficientField, CoefficientRing, ZeroTest, sealed};
use crate::context::{CancelFlag, Storage};
use crate::number::Integer;
use crate::{Context, Error, FaultKind, Limits, Result};

/// `a + b` modulo `p`.
fn residue_sum(p: u32, a: u32, b: u32) -> u32 {
    ((u64::from(a) + u64::from(b)) % u64::from(p)) as u32
}

/// `a - b` modulo `p`.
fn residue_difference(p: u32, a: u32, b: u32) -> u32 {
    ((u64::from(a) + u64::from(p) - u64::from(b)) % u64::from(p)) as u32
}

/// `a * b` modulo `p`.
pub(crate) fn residue_product(p: u32, a: u32, b: u32) -> u32 {
    ((u64::from(a) * u64::from(b)) % u64::from(p)) as u32
}

/// $a^{p-2}$, the inverse of a nonzero residue, by repeated multiplication:
/// $p - 2$ products, so only for the small primes of the tests, $p \ge 2$.
fn residue_inverse(p: u32, a: u32) -> Result<u32> {
    if a == 0 {
        return Err(Error::new(FaultKind::DivisionByZero, None, "zero residue"));
    }
    Ok((0..p - 2).fold(1, |result, _| residue_product(p, result, a)))
}

/// `a / b` modulo `p`, the product with the inverse of `b`.
fn residue_quotient(p: u32, a: u32, b: u32) -> Result<u32> {
    Ok(residue_product(p, a, residue_inverse(p, b)?))
}

/// The residue of `n` modulo `p`, computed under a context of its own so
/// that the caller's context is not charged; the remainder of
/// `divide_with_remainder` is not negative.
fn residue_of(p: u32, n: &Integer) -> Result<u32> {
    let mut scratch = Context::new(Limits::new(), CancelFlag::new());
    let division = n.divide_with_remainder(&Integer::from(u64::from(p)), &mut scratch)?;
    match division.remainder().magnitude_u64().map(u32::try_from) {
        Some(Ok(residue)) => Ok(residue),
        _ => Err(Error::new(
            FaultKind::Internal,
            None,
            "a remainder beyond 32 bits",
        )),
    }
}

/// The storage cost of a residue of a test field: one node of 4 bytes for
/// every residue, which the tests of the elimination skeleton do not read.
const RESIDUE_COST: Storage = Storage::new(1, 4);

/// The residues modulo `p` whose zero test answers undecided, with the value
/// as its reason, for the values in `undecided`, and decides every other
/// value. Every answer is passed to `report`, with the context that the zero
/// test receives.
pub(crate) struct UndecidedResidues<'a> {
    pub(crate) p: u32,
    pub(crate) undecided: &'a [u32],
    pub(crate) report: &'a dyn Fn(u32, &ZeroTest<u32>, &Context),
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
        Ok(residue_difference(self.p, 0, *a))
    }

    fn add(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_sum(self.p, *a, *b))
    }

    fn subtract(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_difference(self.p, *a, *b))
    }

    fn multiply(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_product(self.p, *a, *b))
    }

    fn zero_test(&self, a: &u32, context: &mut Context) -> Result<ZeroTest<u32>> {
        let answer = if self.undecided.contains(a) {
            ZeroTest::Undecided(*a)
        } else if *a == 0 {
            ZeroTest::Zero
        } else {
            ZeroTest::Nonzero
        };
        (self.report)(*a, &answer, context);
        Ok(answer)
    }

    fn measure(&self, _a: &u32) -> Storage {
        RESIDUE_COST
    }
}

impl CoefficientField for UndecidedResidues<'_> {
    fn inverse(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        residue_inverse(self.p, *a)
    }

    fn divide(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        residue_quotient(self.p, *a, *b)
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
        Ok(residue_difference(self.p, 0, *a))
    }

    fn add(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_sum(self.p, *a, *b))
    }

    fn subtract(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        Ok(residue_difference(self.p, *a, *b))
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
        RESIDUE_COST
    }
}

impl CoefficientField for ExactResidues {
    fn inverse(&self, a: &u32, _context: &mut Context) -> Result<u32> {
        residue_inverse(self.p, *a)
    }

    fn divide(&self, a: &u32, b: &u32, _context: &mut Context) -> Result<u32> {
        residue_quotient(self.p, *a, *b)
    }
}
