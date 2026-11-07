//! Univariate polynomials: the ring $K\[x\]$ of one variable over a
//! coefficient ring $K$, its polynomials, and over $\mathbb{Q}$ the
//! expansion of terms into polynomials, the conversion back to terms and
//! differentiation.
//!
//! A [`PolynomialRing`] is the parent structure: it holds the coefficient
//! ring $K$, a parent of the [coefficient-field trait](crate::coefficient),
//! and the name of the variable. A [`Polynomial`] holds only its terms, in
//! increasing degree and none with the coefficient zero: it stores neither
//! $K$ nor the variable, its fields are private, and only the methods of a
//! ring build one. Every operation takes the ring as its receiver and
//! assumes that the polynomials it is given belong to that ring. The ring
//! over $\mathbb{Q}$ is `PolynomialRing<Rationals>`, and its polynomials are
//! `Polynomial<Rationals>`, which is `Polynomial`: the same public type
//! holds the polynomials of the coefficient rings of later releases.
//!
//! The arithmetic is generic: zero, one, the variable $x$, constants, sums,
//! differences, negation, products, powers by repeated squaring and the
//! derivative reach the coefficients only through the methods of the
//! coefficient-field trait, for every ring whose zero test always decides,
//! and take the storage cost of each coefficient from
//! [`measure`](crate::coefficient::CoefficientRing::measure); they place no
//! other bound on the elements.
//! Every polynomial is checked before it is returned: its degree against
//! `max_exponent`, and its storage cost, which bounds its number of terms,
//! with `check_storage`. Every step is charged to the context.
//!
//! ```
//! use kalyx::coefficient::Rationals;
//! use kalyx::context::CancelFlag;
//! use kalyx::polynomial::PolynomialRing;
//! use kalyx::{Context, Limits, parse};
//!
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let ring = PolynomialRing::new(Rationals, "x", &mut context)?;
//! let term = parse("(x + 1)^3 - x^3", &mut context)?;
//! let polynomial = ring.expand(&term, &mut context)?;
//! assert_eq!(polynomial.degree(), Some(2));
//! assert_eq!(polynomial.degrees(), &[0, 1, 2]);
//! let expanded = ring.to_term(&polynomial, &mut context)?;
//! assert_eq!(expanded.display(&mut context)?, "1 + 3*x + 3*x^2");
//! let derivative = ring.differentiate(&term, &mut context)?;
//! assert_eq!(derivative.display(&mut context)?, "3 + 6*x");
//! # Ok::<(), kalyx::Error>(())
//! ```
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/polynomials/contract.md`.

mod arithmetic;
mod conversion;
mod expansion;
mod terms;
#[cfg(test)]
mod tests;

use std::convert::Infallible;
use std::fmt;

use crate::coefficient::{CoefficientRing, Rationals};
use crate::context::Storage;
use crate::term::{Term, check_name};
use crate::{Context, Result};
use terms::PolynomialTerms;

/// The work units charged for a new ring, besides one per byte of the name
/// of its variable.
const RING_CHARGE: u64 = 1;

/// The ring $K\[x\]$ of polynomials in one variable over the coefficient ring
/// $K$: the parent structure of its polynomials.
///
/// It holds the coefficient ring and the name of the variable, and every
/// operation on its polynomials is a method that takes it as `&self`. The
/// methods assume that the polynomials they are given belong to this ring,
/// built by it or by a ring with the same coefficient ring and variable;
/// they never compare rings.
///
/// ```
/// use kalyx::coefficient::Rationals;
/// use kalyx::context::CancelFlag;
/// use kalyx::number::Rational;
/// use kalyx::polynomial::PolynomialRing;
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let ring = PolynomialRing::new(Rationals, "t", &mut context)?;
/// let t = ring.generator(&mut context)?;
/// let two = ring.constant(&Rational::from(2_i64), &mut context)?;
/// let sum = ring.add(&t, &two, &mut context)?;
/// let square = ring.power(&sum, 2, &mut context)?;
/// assert_eq!(square.degrees(), &[0, 1, 2]);
/// let expected = [4_i64, 4, 1].map(Rational::from);
/// assert_eq!(square.coefficients(), &expected);
/// let derivative = ring.derivative(&square, &mut context)?;
/// let term = ring.to_term(&derivative, &mut context)?;
/// assert_eq!(term.display(&mut context)?, "4 + 2*t");
/// # Ok::<(), kalyx::Error>(())
/// ```
#[derive(Clone, Debug)]
pub struct PolynomialRing<K: CoefficientRing = Rationals> {
    /// The coefficient ring.
    coefficients: K,
    /// The name of the variable, a valid symbol name.
    variable: Box<str>,
}

/// A polynomial of a [`PolynomialRing`]: its terms $c x^k$ in increasing
/// degree, none with the coefficient zero, so the zero polynomial has no
/// term.
///
/// The polynomial stores neither its coefficient ring nor its variable, and
/// only the methods of a ring build one, each of which checks it against the
/// limits of the context. The accessors read the degree and the terms
/// without a context. `Polynomial<Rationals>` is `Polynomial`.
///
/// A polynomial cannot be compared with `==`: its coefficients are compared
/// through [`coefficients`](Polynomial::coefficients), or through the
/// coefficient ring.
///
/// ```compile_fail,E0369
/// use kalyx::coefficient::Rationals;
/// use kalyx::context::CancelFlag;
/// use kalyx::polynomial::PolynomialRing;
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let ring = PolynomialRing::new(Rationals, "x", &mut context).unwrap();
/// let x = ring.generator(&mut context).unwrap();
/// let same = x == x.clone();
/// ```
pub struct Polynomial<K: CoefficientRing = Rationals> {
    terms: PolynomialTerms<K::Element>,
}

impl<K: CoefficientRing> PolynomialRing<K> {
    /// The ring of polynomials in the variable `variable` over
    /// `coefficients`.
    ///
    /// The name follows the rule of symbol names of the term core: an ASCII
    /// letter or `_`, followed by ASCII letters, digits and `_`, and not one
    /// of the names `pi`, `i` and `undefined` reserved for constants. The
    /// name is checked first, then one unit and one more per byte of the
    /// name are charged.
    ///
    /// ```
    /// use kalyx::coefficient::Rationals;
    /// use kalyx::context::CancelFlag;
    /// use kalyx::polynomial::PolynomialRing;
    /// use kalyx::{Context, ErrorKind, FaultKind, Limits, Span};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let ring = PolynomialRing::new(Rationals, "x_1", &mut context)?;
    /// assert_eq!(ring.variable(), "x_1");
    /// let error = PolynomialRing::new(Rationals, "pi", &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    /// let error = PolynomialRing::new(Rationals, "1x", &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    /// assert_eq!(error.span(), Span::new(0, 1));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// The errors of `Term::symbol` for the name: `Fault(Syntax)` with the
    /// span of the first character that a name does not allow, or an empty
    /// span at 0 for the empty name, and `Fault(Unsupported)` with the span
    /// of the name for a reserved name; and the request failures of the
    /// charge.
    pub fn new(coefficients: K, variable: &str, context: &mut Context) -> Result<Self> {
        check_name(variable)?;
        context.charge((variable.len() as u64).saturating_add(RING_CHARGE))?;
        Ok(Self {
            coefficients,
            variable: Box::from(variable),
        })
    }

    /// The coefficient ring.
    #[must_use]
    pub const fn coefficient_ring(&self) -> &K {
        &self.coefficients
    }

    /// The name of the variable.
    #[must_use]
    pub fn variable(&self) -> &str {
        &self.variable
    }

    /// The storage cost of `polynomial` in this ring, by the formula of the
    /// contract, which counts the bytes of the variable name: the zero
    /// polynomial costs $(1, 4)$; otherwise, with $(n_c, b_c)$ the cost of a
    /// coefficient $c$, its [`measure`](CoefficientRing::measure) in the
    /// coefficient ring, and $\ell$ the bytes of the variable name, a term of
    /// degree 0 costs $(n_c, b_c)$, of degree 1 $(n_c + 2, b_c + \ell + 4)$,
    /// and of degree $k \ge 2$ $(n_c + 4, b_c + \ell + \lvert k \rvert + 12)$,
    /// each addition between terms $(1, 4)$, and a constant $(0, \ell)$ more
    /// for the variable name. Here $\lvert k \rvert$ is the bit length of
    /// $k$. Over $\mathbb{Q}$, $(n_c, b_c)$ is $(1, \mathrm{rb}(c))$, where
    /// $\mathrm{rb}(n/d) = \lvert n \rvert + \lvert d \rvert + 3$.
    ///
    /// It is the storage cost of a polynomial, a method of the ring since it
    /// needs the variable name, and like `measure` it takes no context and
    /// charges nothing. It takes constant time, since a polynomial keeps the
    /// cost of its terms, and stops at `u64::MAX`.
    #[must_use]
    pub fn storage(&self, polynomial: &Polynomial<K>) -> Storage {
        let (nodes, bytes) = polynomial.terms.cost(self.variable.len() as u64);
        Storage::new(saturated(nodes), saturated(bytes))
    }
}

/// `value`, or `u64::MAX` for an amount beyond it.
const fn saturated(value: Option<u64>) -> u64 {
    match value {
        Some(value) => value,
        None => u64::MAX,
    }
}

impl<K> PolynomialRing<K>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    /// The zero polynomial.
    ///
    /// Every polynomial that an operation returns is checked before it is
    /// returned: its degree against `max_exponent` and the width of `i64`,
    /// then its storage cost with `check_storage` at scope `Value`, together
    /// with the open frames and the reserved temporaries. Then one unit is
    /// charged for it.
    ///
    /// The operations of the ring need a zero test that always decides, so
    /// that no term keeps a zero coefficient: they exist only for a
    /// coefficient ring whose reason type of an undecided zero test is
    /// [`Infallible`]. They place no other bound on the coefficient ring or
    /// its elements, and take the cost of each coefficient from
    /// [`measure`](CoefficientRing::measure). Code generic over every
    /// coefficient ring cannot call them:
    ///
    /// ```compile_fail,E0599
    /// use kalyx::coefficient::CoefficientRing;
    /// use kalyx::polynomial::{Polynomial, PolynomialRing};
    /// use kalyx::{Context, Result};
    ///
    /// fn zero<K: CoefficientRing>(
    ///     ring: &PolynomialRing<K>,
    ///     context: &mut Context,
    /// ) -> Result<Polynomial<K>> {
    ///     ring.zero(context)
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::Exponent` for the degree of the
    /// result, with `LimitField::Nodes` or `LimitField::StorageBytes` and the
    /// scope `Value` for its cost, and the request failures of the charges;
    /// so for every operation of the ring.
    pub fn zero(&self, context: &mut Context) -> Result<Polynomial<K>> {
        arithmetic::admit(self, PolynomialTerms::new(), context)
    }

    /// The polynomial 1: the one of the coefficient ring as a constant.
    ///
    /// # Errors
    ///
    /// As [`zero`](PolynomialRing::zero), and the errors of `one` and
    /// `zero_test` of the coefficient ring.
    pub fn one(&self, context: &mut Context) -> Result<Polynomial<K>> {
        let one = self.coefficients.one(context)?;
        arithmetic::monomial(self, one, 0, context)
    }

    /// The polynomial $x$ of the variable. The degree 1 is checked against
    /// `max_exponent` first.
    ///
    /// # Errors
    ///
    /// As [`one`](PolynomialRing::one).
    pub fn generator(&self, context: &mut Context) -> Result<Polynomial<K>> {
        terms::check_degree(Some(1), context)?;
        let one = self.coefficients.one(context)?;
        arithmetic::monomial(self, one, 1, context)
    }

    /// The constant polynomial `value`, which is the zero polynomial when
    /// the zero test of the coefficient ring finds `value` zero. The element
    /// is taken as it is; its cost is part of the storage cost of the
    /// polynomial.
    ///
    /// # Errors
    ///
    /// As [`zero`](PolynomialRing::zero), and the errors of `zero_test`.
    pub fn constant(&self, value: &K::Element, context: &mut Context) -> Result<Polynomial<K>> {
        arithmetic::monomial(self, value.clone(), 0, context)
    }

    /// The negation $-a$: one unit and the negation of the coefficient for
    /// each term.
    ///
    /// # Errors
    ///
    /// As [`zero`](PolynomialRing::zero), and the errors of the coefficient
    /// operations.
    pub fn negate(
        &self,
        polynomial: &Polynomial<K>,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::negate(self, polynomial, context)
    }

    /// The sum $a + b$. The terms of both are merged in increasing degree:
    /// each step charges one unit and takes the next term of one of them, or
    /// the next terms of both when their degrees are equal, whose
    /// coefficients are added and tested for zero.
    ///
    /// # Errors
    ///
    /// As [`negate`](PolynomialRing::negate).
    pub fn add(
        &self,
        left: &Polynomial<K>,
        right: &Polynomial<K>,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::add(self, left, right, context)
    }

    /// The difference $a - b$, merged as [`add`](PolynomialRing::add)
    /// merges: the coefficients of equal degrees are subtracted, and a term
    /// of $b$ alone is negated.
    ///
    /// # Errors
    ///
    /// As [`negate`](PolynomialRing::negate).
    pub fn subtract(
        &self,
        left: &Polynomial<K>,
        right: &Polynomial<K>,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::subtract(self, left, right, context)
    }

    /// The product $a b$. The degree $\deg a + \deg b$ is checked against
    /// `max_exponent` first, in checked arithmetic. Then each term of the
    /// operand with fewer terms, `left` when they have as many, gives a row,
    /// the product of that term and the other operand, and the rows are
    /// summed in turn; every partial sum is checked as a result is.
    ///
    /// # Errors
    ///
    /// As [`negate`](PolynomialRing::negate); `ResourceLimit` with
    /// `LimitField::Exponent` for the degree of the product comes before any
    /// charge.
    pub fn multiply(
        &self,
        left: &Polynomial<K>,
        right: &Polynomial<K>,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::multiply(self, left, right, context)
    }

    /// The power $a^k$ by repeated squaring, with $a^0 = 1$, also for
    /// $a = 0$. The exponent $k$ is checked against `max_exponent` and the
    /// width of `i64` first, then the degree $k \deg a$, in checked
    /// arithmetic. For $k \ge 1$ the power starts from a copy of $a$, and
    /// each bit of $k$ below its highest one, from the top, charges one
    /// unit, squares the power and, when the bit is set, multiplies it by
    /// $a$, each as [`multiply`](PolynomialRing::multiply).
    ///
    /// # Errors
    ///
    /// As [`multiply`](PolynomialRing::multiply); `ResourceLimit` with
    /// `LimitField::Exponent` for the exponent or the degree comes before
    /// any charge.
    pub fn power(
        &self,
        base: &Polynomial<K>,
        exponent: u64,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::power(self, base, exponent, context)
    }

    /// The derivative $a'$ by the variable. Each term $c x^d$ charges one
    /// unit, and for $d \ge 1$ becomes $(d \cdot 1) \, c \, x^{d - 1}$: the
    /// integer $d$ enters as `from_integer`, the product is that of the
    /// coefficient ring, and the term is dropped when the zero test finds it
    /// zero. No coefficient is divided.
    ///
    /// # Errors
    ///
    /// As [`negate`](PolynomialRing::negate).
    pub fn derivative(
        &self,
        polynomial: &Polynomial<K>,
        context: &mut Context,
    ) -> Result<Polynomial<K>> {
        arithmetic::derivative(self, polynomial, context)
    }
}

impl PolynomialRing<Rationals> {
    /// The polynomial of `term`: its expansion in $\mathbb{Q}\[x\]$ for the
    /// variable $x$ of this ring.
    ///
    /// The depth of the term is checked against `max_depth` first, before
    /// any charge. Then the term is walked with a stack on the heap, the
    /// children of a node in their stored order, and every occurrence of a
    /// node charges one unit when it is entered, before its children, while
    /// its polynomial is formed after theirs: a number is a constant, the
    /// variable is $x$, a power with a nonnegative exponent is the power of
    /// the polynomial of its base, a product multiplies the constant of its
    /// coefficient by the polynomials of its factors, and a sum adds the
    /// polynomials of its monomials, each the constant of its coefficient
    /// times the polynomial of its core, to the constant of its constant.
    /// Coefficients that cancel leave no term, so the expansion of
    /// `(x + 1)^2 - x^2 - 2*x - 1` is the zero polynomial.
    ///
    /// ```
    /// use kalyx::coefficient::Rationals;
    /// use kalyx::context::CancelFlag;
    /// use kalyx::polynomial::PolynomialRing;
    /// use kalyx::{Context, ErrorKind, FaultKind, Limits, parse};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let ring = PolynomialRing::new(Rationals, "x", &mut context)?;
    /// let term = parse("(x + 1)^2 - x^2 - 2*x - 1", &mut context)?;
    /// assert!(ring.expand(&term, &mut context)?.is_zero());
    /// let term = parse("x + y", &mut context)?;
    /// let error = ring.expand(&term, &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::UnknownSymbol));
    /// let term = parse("(x^2 - 1)/(x - 1)", &mut context)?;
    /// let error = ring.expand(&term, &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::NotPolynomial));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// The first failure of the walk, in the order that the component
    /// contract states: `ResourceLimit` with `LimitField::Depth` for the
    /// depth of the term, before any charge; `Fault(UnknownSymbol)` for a
    /// symbol other than the variable; `Fault(NotPolynomial)` for a power
    /// with a negative exponent, after its base, and for a call, before its
    /// arguments; and the errors of the operations of the ring and of the
    /// charges, each node charged when it is entered, before its children.
    pub fn expand(&self, term: &Term, context: &mut Context) -> Result<Polynomial> {
        expansion::expand(self, term, context)
    }

    /// The canonical term of `polynomial`: the sum of the terms $c x^k$ of
    /// its terms, each charged one unit and built through the constructors
    /// of the term core, which check and charge every node. The symbol of
    /// the variable is built once, when there is a term of positive degree,
    /// and the zero polynomial is the number 0.
    ///
    /// # Errors
    ///
    /// The errors of the constructors of the term core, such as
    /// `ResourceLimit` with `LimitField::IntegerBits` for a coefficient
    /// beyond `max_integer_bits`, with `LimitField::Exponent` for a degree
    /// beyond `max_exponent`, and with `LimitField::Nodes`,
    /// `LimitField::StorageBytes` or `LimitField::Depth` for a node; and the
    /// request failures of the charges.
    pub fn to_term(&self, polynomial: &Polynomial, context: &mut Context) -> Result<Term> {
        conversion::to_term(self, polynomial, context)
    }

    /// The derivative of `term` by the variable of this ring, as a term: the
    /// expansion of `term`, its [`derivative`](PolynomialRing::derivative)
    /// and the term of the result, in that order.
    ///
    /// ```
    /// use kalyx::coefficient::Rationals;
    /// use kalyx::context::CancelFlag;
    /// use kalyx::polynomial::PolynomialRing;
    /// use kalyx::{Context, Limits, parse};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let ring = PolynomialRing::new(Rationals, "t", &mut context)?;
    /// let term = parse("(t^3 - 2*t)/3", &mut context)?;
    /// let derivative = ring.differentiate(&term, &mut context)?;
    /// assert_eq!(derivative.display(&mut context)?, "-2/3 + t^2");
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// The errors of [`expand`](PolynomialRing::expand),
    /// [`derivative`](PolynomialRing::derivative) and
    /// [`to_term`](PolynomialRing::to_term).
    pub fn differentiate(&self, term: &Term, context: &mut Context) -> Result<Term> {
        let polynomial = self.expand(term, context)?;
        let derivative = self.derivative(&polynomial, context)?;
        self.to_term(&derivative, context)
    }
}

impl<K: CoefficientRing> Polynomial<K> {
    /// The degree: the highest degree of a term, or `None` for the zero
    /// polynomial.
    #[must_use]
    pub fn degree(&self) -> Option<u64> {
        self.terms.last_degree()
    }

    /// Whether this is the zero polynomial, which has no term.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The degrees of the terms, in increasing order.
    #[must_use]
    pub fn degrees(&self) -> &[u64] {
        self.terms.degrees()
    }

    /// The coefficients of the terms, in the order of
    /// [`degrees`](Polynomial::degrees): the coefficient of the term of
    /// degree `degrees()[i]` is `coefficients()[i]`, and none is zero.
    #[must_use]
    pub fn coefficients(&self) -> &[K::Element] {
        self.terms.coefficients()
    }
}

impl<K: CoefficientRing> Clone for Polynomial<K> {
    /// A copy of the terms.
    fn clone(&self) -> Self {
        Self {
            terms: self.terms.clone(),
        }
    }
}

impl<K: CoefficientRing> fmt::Debug for Polynomial<K> {
    /// A shallow view: the degree and the number of terms, never the
    /// coefficients, so the output does not grow with the polynomial.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Polynomial")
            .field("degree", &self.degree())
            .field("terms", &self.terms.len())
            .finish_non_exhaustive()
    }
}
