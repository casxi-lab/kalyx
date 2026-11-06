//! The coefficient-field trait: the element operations of the rings and
//! fields whose elements are the coefficients of polynomials, and the field
//! of rational numbers $\mathbb{Q}$, [`Rationals`].
//!
//! A trait is implemented by a value that describes the ring or field, its
//! *parent structure*, and the elements are its associated type: [`Rationals`]
//! is a zero-sized parent whose elements are [`Rational`]s. Fields defined by
//! data known only at run time, such as a prime modulus, take the same shape,
//! and their elements do not repeat the parent.
//!
//! There are two layers. [`CoefficientRing`] holds the ring operations and the
//! zero test; [`CoefficientField`] adds the inverse and the quotient, so a
//! division algorithm bounded by `CoefficientField` cannot be called on a ring
//! that is not a field. Every method takes the parent as `&self` and the
//! request context last, and returns a `Result`. Both traits are sealed: only
//! this library implements them, so later releases can add required methods
//! without breaking callers, and callers cannot define their own coefficient
//! fields yet. Neither trait has a default method.
//!
//! ```
//! use kalyx::coefficient::{CoefficientField, CoefficientRing, Rationals, ZeroTest};
//! use kalyx::context::CancelFlag;
//! use kalyx::number::Integer;
//! use kalyx::{Context, Limits};
//!
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let q = Rationals;
//! let three = q.from_integer(&Integer::from(3_i64), &mut context)?;
//! let third = q.inverse(&three, &mut context)?;
//! let one = q.multiply(&three, &third, &mut context)?;
//! assert_eq!(one, q.one(&mut context)?);
//! let zero = q.subtract(&one, &one, &mut context)?;
//! assert_eq!(q.zero_test(&zero, &mut context)?, ZeroTest::Zero);
//! # Ok::<(), kalyx::Error>(())
//! ```
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/numbers/contract.md`.

use std::convert::Infallible;

use crate::number::{Integer, Rational};
use crate::{Context, LimitField, Result};

mod sealed {
    /// The seal of the coefficient traits: implemented only in this library.
    pub trait Sealed {}
}

/// The answer of a zero test: the element is zero, it is not, or the test
/// cannot decide, with the reason `U` that the ring gives.
///
/// The three cases are mathematically complete, so this enum is the one
/// public enum of the library that is not `#[non_exhaustive]`. A ring whose
/// zero test always decides has the reason type [`Infallible`], so
/// `Undecided` cannot occur.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ZeroTest<U> {
    /// The element is zero.
    Zero,
    /// The element is not zero.
    Nonzero,
    /// The test cannot decide, for the reason given.
    Undecided(U),
}

/// The element operations of a commutative ring with one, implemented by its
/// parent structure.
///
/// The methods assume that their elements belong to `self`; whether two
/// parents are the same is checked with
/// [`same_parent`](CoefficientRing::same_parent) only where a parent and an
/// element are stored together. Each operation checks the sizes of its
/// result before it works, charges the context for itself, and charges an
/// amount that depends only on its operands.
///
/// The trait is sealed: a type outside this library cannot implement it, even
/// with every method, since the seal is in a private module.
///
/// ```compile_fail,E0603
/// use kalyx::coefficient::{CoefficientRing, ZeroTest};
/// use kalyx::number::Integer;
/// use kalyx::{Context, Result};
///
/// struct Mine;
///
/// impl kalyx::coefficient::sealed::Sealed for Mine {}
///
/// impl CoefficientRing for Mine {
///     type Element = ();
///     type Undecided = ();
///     fn same_parent(&self, _: &Self, _: &mut Context) -> Result<bool> { Ok(true) }
///     fn zero(&self, _: &mut Context) -> Result<()> { Ok(()) }
///     fn one(&self, _: &mut Context) -> Result<()> { Ok(()) }
///     fn from_integer(&self, _: &Integer, _: &mut Context) -> Result<()> { Ok(()) }
///     fn negate(&self, _: &(), _: &mut Context) -> Result<()> { Ok(()) }
///     fn add(&self, _: &(), _: &(), _: &mut Context) -> Result<()> { Ok(()) }
///     fn subtract(&self, _: &(), _: &(), _: &mut Context) -> Result<()> { Ok(()) }
///     fn multiply(&self, _: &(), _: &(), _: &mut Context) -> Result<()> { Ok(()) }
///     fn zero_test(&self, _: &(), _: &mut Context) -> Result<ZeroTest<()>> {
///         Ok(ZeroTest::Zero)
///     }
/// }
/// ```
pub trait CoefficientRing: sealed::Sealed {
    /// The type of the elements. It need not have an equality: elements whose
    /// representation is not unique compare through the ring.
    type Element: Clone;

    /// Why the zero test could not decide; [`Infallible`] for a ring whose
    /// zero test always decides.
    type Undecided;

    /// Whether `self` and `other` are the same ring, by their defining data.
    ///
    /// # Errors
    ///
    /// The request failures of the context, for a ring whose comparison is
    /// charged.
    fn same_parent(&self, other: &Self, context: &mut Context) -> Result<bool>;

    /// The zero of the ring.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn zero(&self, context: &mut Context) -> Result<Self::Element>;

    /// The one of the ring.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn one(&self, context: &mut Context) -> Result<Self::Element>;

    /// The image $n \cdot 1$ of the integer `n`.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    #[allow(
        clippy::wrong_self_convention,
        reason = "the image of an integer in the ring that `self` describes needs the ring"
    )]
    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<Self::Element>;

    /// The negation $-a$.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn negate(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;

    /// The sum $a + b$.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn add(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;

    /// The difference $a - b$.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn subtract(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;

    /// The product $a \cdot b$.
    ///
    /// # Errors
    ///
    /// The limits and request failures of the context.
    fn multiply(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;

    /// Whether `a` is zero: a decided answer is correct, and
    /// [`ZeroTest::Undecided`] carries the reason when the ring cannot decide.
    ///
    /// # Errors
    ///
    /// The request failures of the context, for a ring whose zero test is
    /// charged.
    fn zero_test(
        &self,
        a: &Self::Element,
        context: &mut Context,
    ) -> Result<ZeroTest<Self::Undecided>>;
}

/// The element operations of a field beyond those of its ring: the inverse
/// and the quotient.
///
/// Both fail with `Fault(DivisionByZero)` on a zero element or divisor. A
/// field whose zero test is structural tests the divisor before any charge
/// of the operation; a field whose zero test is charged pays for the test
/// first.
pub trait CoefficientField: CoefficientRing {
    /// The inverse $a^{-1}$ of a nonzero `a`.
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `a` is zero; the limits and request
    /// failures of the context.
    fn inverse(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;

    /// The quotient $a / b$ for a nonzero `b`.
    ///
    /// # Errors
    ///
    /// `Fault(DivisionByZero)` when `b` is zero; the limits and request
    /// failures of the context.
    fn divide(
        &self,
        a: &Self::Element,
        b: &Self::Element,
        context: &mut Context,
    ) -> Result<Self::Element>;
}

/// The field $\mathbb{Q}$ of rational numbers, whose elements are the
/// canonical [`Rational`]s.
///
/// Its zero test is structural and always decides, so its reason type is
/// [`Infallible`]. Its operations are those of [`Rational`], with the same
/// checks and charges; [`zero`](CoefficientRing::zero),
/// [`one`](CoefficientRing::one) and
/// [`from_integer`](CoefficientRing::from_integer) check the bits of the new
/// element and charge one unit each.
/// [`same_parent`](CoefficientRing::same_parent) and
/// [`zero_test`](CoefficientRing::zero_test) take constant time and charge
/// nothing: there is only one $\mathbb{Q}$, and its zero test reads the
/// numerator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Rationals;

impl sealed::Sealed for Rationals {}

/// The work units charged for a new element of [`Rationals`].
const ELEMENT_CHARGE: u64 = 1;

/// Admits a new element of [`Rationals`] with `bits` bits, at least 1 since
/// its denominator is 1: checks them against `max_integer_bits`, then charges
/// one unit. The caller builds the element only afterwards, so a rejected
/// element builds nothing but its error.
fn admit_element(bits: u64, context: &mut Context) -> Result<()> {
    context.check(LimitField::IntegerBits, bits.max(1))?;
    context.charge(ELEMENT_CHARGE)
}

impl CoefficientRing for Rationals {
    type Element = Rational;
    type Undecided = Infallible;

    /// Always `true`, without a charge.
    fn same_parent(&self, _other: &Self, _context: &mut Context) -> Result<bool> {
        Ok(true)
    }

    /// $0/1$.
    fn zero(&self, context: &mut Context) -> Result<Rational> {
        admit_element(1, context)?;
        Ok(Rational::from(0_i64))
    }

    /// $1/1$.
    fn one(&self, context: &mut Context) -> Result<Rational> {
        admit_element(1, context)?;
        Ok(Rational::from(1_i64))
    }

    /// $n/1$.
    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<Rational> {
        admit_element(n.bits(), context)?;
        Ok(Rational::from(n.clone()))
    }

    fn negate(&self, a: &Rational, context: &mut Context) -> Result<Rational> {
        a.negate(context)
    }

    fn add(&self, a: &Rational, b: &Rational, context: &mut Context) -> Result<Rational> {
        a.add(b, context)
    }

    fn subtract(&self, a: &Rational, b: &Rational, context: &mut Context) -> Result<Rational> {
        a.subtract(b, context)
    }

    fn multiply(&self, a: &Rational, b: &Rational, context: &mut Context) -> Result<Rational> {
        a.multiply(b, context)
    }

    /// [`ZeroTest::Zero`] or [`ZeroTest::Nonzero`], from the numerator,
    /// without a charge.
    fn zero_test(&self, a: &Rational, _context: &mut Context) -> Result<ZeroTest<Infallible>> {
        if a.is_zero() {
            Ok(ZeroTest::Zero)
        } else {
            Ok(ZeroTest::Nonzero)
        }
    }
}

impl CoefficientField for Rationals {
    fn inverse(&self, a: &Rational, context: &mut Context) -> Result<Rational> {
        a.inverse(context)
    }

    fn divide(&self, a: &Rational, b: &Rational, context: &mut Context) -> Result<Rational> {
        a.divide(b, context)
    }
}
