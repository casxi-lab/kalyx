//! The term core: one immutable representation of numbers, symbols, sums,
//! products and integer powers, which its constructors keep in canonical
//! form.
//!
//! A [`Term`] is a shared, immutable tree: a reference-counted node that
//! holds its kind, its children and cached values, the tree size, the
//! depth, the logical bytes and whether the term holds a power with a
//! negative exponent. Cloning a term is $O(1)$ and subterms may be shared,
//! but sharing is invisible: equality and ordering compare structure, and
//! there is no intern table and no global state.
//!
//! Every constructor takes the request context last, checks the depth and
//! the storage of each node before allocating it, charges every step, and
//! returns a canonical term:
//!
//! - **Products** are flattened, multiply their numbers exactly into one
//!   coefficient, and merge factors with the same base and the same sign of
//!   exponent; factors with exponents of opposite sign are never merged.
//! - **Powers** have integer exponents; a numeric base is evaluated
//!   strictly, an integer power distributes over a product, and a power of a
//!   sum is not expanded.
//! - **Sums** are flattened and add the coefficients of equal monomials. A
//!   number other than 0 and 1 times a sum multiplies its constant and its
//!   coefficients, $2 (x + y) = 2x + 2y$, so no monomial of a sum has a sum
//!   as its core.
//! - **Sums as factors and bases** are primitive: a sum $s$ is written as
//!   $c \cdot p$, with its content $c$, the coefficient of its first
//!   monomial whose coefficient is not 0 or its constant when there is
//!   none, and its primitive part $p = s / c$; $c$ joins the coefficient of
//!   the product, and $s^k = c^k p^k$. So $(2x + 2y) z = 2 (x + y) z$ and
//!   $(2x + 2y)^2 = 4 (x + y)^2$.
//! - **Negative exponents** are never lost: where a simplification would
//!   drop a base that occurs with a negative exponent, the term keeps a
//!   witness of it, so $x^2 x^{-1}$, $x x^{-1}$, $0 \cdot x^{-1}$ and
//!   $(x^{-1})^0$ stay as written.
//!
//! Comparison, display, the collection of negative-exponent bases and drop
//! each run as one loop over a stack on the heap, so the native stack use
//! does not grow with the depth of a term.
//!
//! ```
//! use kalyx::context::CancelFlag;
//! use kalyx::number::Rational;
//! use kalyx::term::Term;
//! use kalyx::{Context, Limits};
//!
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let x = Term::symbol("x", &mut context)?;
//! let y = Term::symbol("y", &mut context)?;
//! let two = Term::number(Rational::from(2_i64), &mut context)?;
//! let sum = Term::sum(&[y.clone(), x.clone(), two.clone()], &mut context)?;
//! assert_eq!(sum.display(&mut context)?, "2 + x + y");
//!
//! let square = sum.power(2, &mut context)?;
//! let product = Term::product(&[x.clone(), square, x.power(-1, &mut context)?], &mut context)?;
//! assert_eq!(product.display(&mut context)?, "x*x^(-1)*(2 + x + y)^2");
//!
//! let pair = Term::sum(&[x.clone(), y.clone()], &mut context)?;
//! let doubled = Term::product(&[two, pair.clone()], &mut context)?;
//! assert_eq!(doubled.display(&mut context)?, "2*x + 2*y");
//! let z = Term::symbol("z", &mut context)?;
//! let scaled = Term::product(&[doubled.clone(), z], &mut context)?;
//! assert_eq!(scaled.display(&mut context)?, "2*z*(x + y)");
//! let twice = Term::sum(&[pair.clone(), pair], &mut context)?;
//! assert_eq!(doubled.subtract(&twice, &mut context)?.display(&mut context)?, "0");
//! # Ok::<(), kalyx::Error>(())
//! ```
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/terms/contract.md`.

mod display;
mod exponent;
mod node;
mod order;
mod power;
mod product;
mod sort;
mod sum;
mod symbol;
#[cfg(test)]
mod tests;
mod witness;

use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use crate::context::{Storage, StorageCost};
use crate::number::Rational;
use crate::{Context, Result};
use node::{TermNode, TermShape};

// The parser reads identifiers by the rule of symbol names, rejects the
// reserved names and reads the exponent of a power through these; the
// polynomial rings check the name of their variable with `check_name`.
pub(crate) use exponent::integer_exponent;
pub(crate) use symbol::{
    character_length, check_name, continues_name, is_digit, is_reserved, starts_name,
};

/// A canonical term: a shared handle to an immutable node.
///
/// Terms are built only by the constructors of this type, each of which
/// returns a canonical term, and read through its accessors. Cloning a term
/// only increments a count. A term is not `Send`; its `Debug` output is
/// shallow, and its text comes from the charged [`display`](Term::display).
///
/// A term cannot be compared with `==` or ordered with `<`: comparing two
/// terms walks both trees, so [`compare`](Term::compare) and
/// [`equals`](Term::equals) take the context and charge each step.
///
/// ```compile_fail,E0369
/// use kalyx::context::CancelFlag;
/// use kalyx::term::Term;
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let x = Term::symbol("x", &mut context).unwrap();
/// let same = x == x.clone();
/// ```
///
/// Terms share their nodes through a count that is not atomic, so a term
/// does not move to another thread:
///
/// ```compile_fail,E0277
/// use kalyx::context::CancelFlag;
/// use kalyx::term::Term;
/// use kalyx::{Context, Limits};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let x = Term::symbol("x", &mut context).unwrap();
/// std::thread::spawn(move || drop(x));
/// ```
#[derive(Clone)]
pub struct Term(Rc<TermNode>);

/// The kind of a term.
///
/// Terms are ordered by the rank of their kind first: number 0, symbol 2,
/// call 3, power 4, product 5 and sum 6. The rank 1 is reserved for exact
/// constants such as $\pi$ and $i$, which a later release adds; a new kind
/// takes a new rank and never changes the order of the existing kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TermKind {
    /// An exact rational number.
    Number,
    /// A symbol.
    Symbol,
    /// A call of a function. Reserved: no constructor of this release builds
    /// a call.
    Call,
    /// An integer power of a base.
    Power,
    /// A product of a coefficient and factors.
    Product,
    /// A sum of a constant and monomials.
    Sum,
}

impl TermKind {
    /// The rank of the kind in the total order of terms.
    #[must_use]
    pub const fn rank(self) -> u8 {
        match self {
            Self::Number => 0,
            Self::Symbol => 2,
            Self::Call => 3,
            Self::Power => 4,
            Self::Product => 5,
            Self::Sum => 6,
        }
    }
}

impl Term {
    /// The number `value`.
    ///
    /// Checks the bits of `value` against `max_integer_bits`, then checks the
    /// node as every constructor does and charges one unit.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when `value` has more
    /// bits than `max_integer_bits`, with `LimitField::Depth`,
    /// `LimitField::Nodes` or `LimitField::StorageBytes` when the node does
    /// not fit, and the request failures of the charge.
    pub fn number(value: Rational, context: &mut Context) -> Result<Self> {
        node::number(value, context)
    }

    /// The symbol `name`.
    ///
    /// A name is an ASCII letter or `_`, followed by ASCII letters, digits
    /// and `_`. The names `pi`, `i` and `undefined` are reserved for
    /// constants of a later release and are not symbols. Checks the name,
    /// then checks the node and charges one unit and one more per byte of the
    /// name.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::term::Term;
    /// use kalyx::{Context, ErrorKind, FaultKind, Limits, Span};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// assert_eq!(Term::symbol("x_1", &mut context)?.as_symbol(), Some("x_1"));
    /// let error = Term::symbol("pi", &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    /// let error = Term::symbol("x-1", &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    /// assert_eq!(error.span(), Span::new(1, 2));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `Fault(Syntax)` for a name that is not of that form, with the span of
    /// its first character that the form does not allow, or an empty span at
    /// 0 for the empty name; `Fault(Unsupported)` for a reserved name, with
    /// the span of the name; `ResourceLimit` when the node does not fit; and
    /// the request failures of the charge.
    pub fn symbol(name: &str, context: &mut Context) -> Result<Self> {
        symbol::check_name(name)?;
        node::make_symbol(name, context)
    }

    /// The canonical sum of `terms`; the empty sum is the number 0.
    ///
    /// Nested sums are flattened and monomials with equal cores add their
    /// coefficients; no core of the result is a sum. Monomials that cancel
    /// keep the bases that they hold with a negative exponent in a witness
    /// monomial with the coefficient 0.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::IntegerBits` when a constant or a
    /// coefficient needs more bits than `max_integer_bits`, with
    /// `LimitField::Depth`, `LimitField::Nodes` or `LimitField::StorageBytes`
    /// when a node does not fit, and with `LimitField::Work` when the work
    /// exceeds `max_work`; the other request failures of the charges; and
    /// `Fault(Internal)` when an internal invariant is broken.
    pub fn sum(terms: &[Self], context: &mut Context) -> Result<Self> {
        sum::sum(terms, context)
    }

    /// The canonical product of `terms`; the empty product is the number 1.
    ///
    /// A sum among the factors is taken by its primitive part: its content,
    /// the coefficient of its first monomial whose coefficient is not 0, or
    /// its constant when it has none, joins the coefficient, and the sum
    /// divided by its content is the factor. A coefficient other than 0 and
    /// 1 times a single sum is that sum with its constant and coefficients
    /// multiplied by the coefficient.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::term::Term;
    /// use kalyx::{Context, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let x = Term::symbol("x", &mut context)?;
    /// let y = Term::symbol("y", &mut context)?;
    /// let z = Term::symbol("z", &mut context)?;
    /// let three = Term::number(Rational::from(3_i64), &mut context)?;
    /// let two = Term::number(Rational::from(2_i64), &mut context)?;
    /// let three_x = Term::product(&[three, x], &mut context)?;
    /// let two_y = Term::product(&[two.clone(), y], &mut context)?;
    /// let sum = Term::sum(&[two_y, three_x], &mut context)?;
    /// assert_eq!(sum.display(&mut context)?, "3*x + 2*y");
    /// let factor = Term::product(&[sum.clone(), z], &mut context)?;
    /// assert_eq!(factor.display(&mut context)?, "3*z*(x + 2/3*y)");
    /// let doubled = Term::product(&[two, sum], &mut context)?;
    /// assert_eq!(doubled.display(&mut context)?, "6*x + 4*y");
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// As [`sum`](Term::sum), and `ResourceLimit` with
    /// `LimitField::Exponent` when the sum of the exponents of one base and
    /// one sign exceeds `max_exponent` or $2^{63} - 1$.
    pub fn product(terms: &[Self], context: &mut Context) -> Result<Self> {
        product::product(Rational::from(1), terms, context)
    }

    /// The canonical power $\mathrm{self}^k$ for the integer exponent
    /// `exponent`.
    ///
    /// The exponent is checked first, against `max_exponent` and the width
    /// of `i64`. A numeric base is evaluated strictly: $0^0 = 1$ and a
    /// negative power of 0 fails. The exponent 1 gives the base, and an
    /// integer power distributes over a product. A power of a sum is not
    /// expanded: the content $c$ of the sum $s = c \cdot p$ comes out as
    /// $c^k$, computed strictly, and the power is that of its primitive part
    /// $p$, so $(1 - x)^{-1} = -(x - 1)^{-1}$. Raising a power to a power
    /// multiplies the exponents only where no base that occurs with a
    /// negative exponent is lost.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::term::Term;
    /// use kalyx::{Context, ErrorKind, FaultKind, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let x = Term::symbol("x", &mut context)?;
    /// let inverse = x.power(-1, &mut context)?;
    /// assert_eq!(inverse.power(0, &mut context)?.display(&mut context)?, "(x^(-1))^0");
    /// assert_eq!(inverse.power(-1, &mut context)?.display(&mut context)?, "(x^(-1))^(-1)");
    /// assert_eq!(inverse.power(3, &mut context)?.display(&mut context)?, "x^(-3)");
    /// let one = Term::number(Rational::from(1_i64), &mut context)?;
    /// let difference = one.subtract(&x, &mut context)?;
    /// assert_eq!(difference.display(&mut context)?, "1 - x");
    /// let reciprocal = difference.power(-1, &mut context)?;
    /// assert_eq!(reciprocal.display(&mut context)?, "-(-1 + x)^(-1)");
    /// let zero = Term::number(Rational::from(0_i64), &mut context)?;
    /// let error = zero.power(-1, &mut context).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::Exponent` when the magnitude of
    /// `exponent` exceeds `max_exponent` or $2^{63} - 1$, before any other
    /// check or charge, or when a product of exponents does;
    /// `Fault(DivisionByZero)` for a negative power of 0 or of a product
    /// with the coefficient 0; the bit limit of the power of a number; and
    /// the errors of [`product`](Term::product).
    pub fn power(&self, exponent: i64, context: &mut Context) -> Result<Self> {
        power::power(self, exponent, context)
    }

    /// The canonical negation $-\mathrm{self}$: the product of $-1$ and
    /// `self`, so the negation of a sum negates its constant and every
    /// coefficient, $-(x + y) = -x - y$.
    ///
    /// # Errors
    ///
    /// As [`product`](Term::product).
    pub fn negate(&self, context: &mut Context) -> Result<Self> {
        product::product(Rational::from(-1), std::slice::from_ref(self), context)
    }

    /// The canonical difference $\mathrm{self} - \mathrm{other}$: the sum of
    /// `self` and the negation of `other`.
    ///
    /// # Errors
    ///
    /// As [`product`](Term::product).
    pub fn subtract(&self, other: &Self, context: &mut Context) -> Result<Self> {
        let negated = other.negate(context)?;
        sum::sum(&[self.clone(), negated], context)
    }

    /// The canonical quotient $\mathrm{self} / \mathrm{other}$: the product
    /// of `self` and $\mathrm{other}^{-1}$.
    ///
    /// # Errors
    ///
    /// As [`power`](Term::power) and [`product`](Term::product); in
    /// particular `Fault(DivisionByZero)` when `other` is 0 or a product with
    /// the coefficient 0, such as $0 \cdot x^{-1}$.
    pub fn divide(&self, other: &Self, context: &mut Context) -> Result<Self> {
        let inverse = other.power(-1, context)?;
        product::product(Rational::from(1), &[self.clone(), inverse], context)
    }

    /// The order of `self` and `other` in the total order of terms.
    ///
    /// Terms are ordered by the rank of their kind first; within a kind,
    /// numbers by value, symbols by the bytes of their names, powers by base
    /// and then exponent, products by their factors one by one, the number
    /// of factors and then the coefficient, and sums by their monomials one
    /// by one (core, then coefficient), the number of monomials and then the
    /// constant. The comparison is structural and never consults whether two
    /// terms share a node. It walks the children of two nodes one pair at a
    /// time and stops at the first pair that differs. It charges one unit
    /// per step, where the walk over the children of two nodes takes one
    /// step at each position it reaches and one past the last, one more per
    /// byte of the shorter of two compared names, and compares numbers with
    /// the charged `Rational::compare`.
    ///
    /// # Errors
    ///
    /// The errors of `Rational::compare`, which checks a bound on the bits of
    /// two compared numbers against `max_integer_bits`; the request failures
    /// of the charges; and `Fault(Internal)` when an internal invariant is
    /// broken.
    pub fn compare(&self, other: &Self, context: &mut Context) -> Result<Ordering> {
        order::compare(self, other, context)
    }

    /// Whether `self` and `other` are the same term: [`compare`](Term::compare)
    /// gives `Equal`. Canonical forms are unique, so structurally equal terms
    /// are the same value, and terms of different structure are different
    /// terms.
    ///
    /// # Errors
    ///
    /// As [`compare`](Term::compare).
    pub fn equals(&self, other: &Self, context: &mut Context) -> Result<bool> {
        Ok(order::compare(self, other, context)? == Ordering::Equal)
    }

    /// The display text of the term, with minimal parentheses, in the grammar
    /// that the contract states.
    ///
    /// The text depends only on the term, so it is the same for every way of
    /// building the term and in every run. Charges one unit per step and,
    /// with `charge_output`, each piece of text before it is written: a
    /// failure returns no text.
    ///
    /// # Errors
    ///
    /// `ResourceLimit` with `LimitField::OutputBytes` when the request's
    /// output exceeds `max_output_bytes`, with `LimitField::IntegerBits` when
    /// a number has more bits than `max_integer_bits`; the request failures
    /// of the charges; and `Fault(Internal)` when an internal invariant is
    /// broken.
    pub fn display(&self, context: &mut Context) -> Result<String> {
        display::display(self, context)
    }

    /// $N(\mathrm{self})$: the bases that occur with a negative exponent in
    /// the term, sorted in the total order and without repetitions. A base
    /// that is a sum is primitive, since a power of a sum raises its
    /// primitive part. Canonicalization never shrinks this set: the set of a
    /// term built from operands holds the sets of the operands.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::number::Rational;
    /// use kalyx::term::Term;
    /// use kalyx::{Context, Limits};
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let x = Term::symbol("x", &mut context)?;
    /// let zero = Term::number(Rational::from(0_i64), &mut context)?;
    /// let inverse = x.power(-1, &mut context)?;
    /// let product = Term::product(&[zero, inverse], &mut context)?;
    /// assert_eq!(product.display(&mut context)?, "0*x^(-1)");
    /// let bases = product.negative_bases(&mut context)?;
    /// assert_eq!(bases.len(), 1);
    /// assert!(bases[0].equals(&x, &mut context)?);
    /// # Ok::<(), kalyx::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// As [`compare`](Term::compare), and the request failures of the
    /// charges.
    pub fn negative_bases(&self, context: &mut Context) -> Result<Vec<Self>> {
        witness::negative_bases(std::slice::from_ref(self), context)
    }

    /// The kind of the term.
    #[must_use]
    pub fn kind(&self) -> TermKind {
        match &self.0.shape {
            TermShape::Number(_) => TermKind::Number,
            TermShape::Symbol(_) => TermKind::Symbol,
            TermShape::Call(_) => TermKind::Call,
            TermShape::Power(_) => TermKind::Power,
            TermShape::Product(_) => TermKind::Product,
            TermShape::Sum(_, _) => TermKind::Sum,
        }
    }

    /// The tree size of the term: its nodes, a shared subterm counted once
    /// for each occurrence. Coefficients, constants and exponents add no
    /// nodes.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.0.size
    }

    /// The depth of the term: 1 for a number or a symbol, and one more than
    /// the largest depth of its children otherwise.
    #[must_use]
    pub fn depth(&self) -> u64 {
        self.0.depth
    }

    /// Whether the term holds a power with a negative exponent, that is,
    /// whether $N(\mathrm{self})$ is not empty.
    #[must_use]
    pub fn has_negative_power(&self) -> bool {
        self.0.negative
    }

    /// The children of the term in their stored order: the base of a power,
    /// the factors of a product, the cores of the monomials of a sum, and
    /// none for a number or a symbol.
    #[must_use]
    pub fn children(&self) -> &[Self] {
        &self.0.children
    }

    /// The value of a number.
    #[must_use]
    pub fn as_number(&self) -> Option<&Rational> {
        match &self.0.shape {
            TermShape::Number(value) => Some(value),
            TermShape::Symbol(_)
            | TermShape::Call(_)
            | TermShape::Power(_)
            | TermShape::Product(_)
            | TermShape::Sum(_, _) => None,
        }
    }

    /// The name of a symbol.
    #[must_use]
    pub fn as_symbol(&self) -> Option<&str> {
        match &self.0.shape {
            TermShape::Symbol(name) => Some(name),
            TermShape::Number(_)
            | TermShape::Call(_)
            | TermShape::Power(_)
            | TermShape::Product(_)
            | TermShape::Sum(_, _) => None,
        }
    }

    /// The base and the exponent of a power. The base is never a number or a
    /// product, a base that is a sum is primitive, and the exponent is never
    /// 1; the exponent 0 occurs only in a witness $(b^{-1})^0$.
    #[must_use]
    pub fn as_power(&self) -> Option<(&Self, i64)> {
        match &self.0.shape {
            TermShape::Power(exponent) => match self.0.children.first() {
                Some(base) => Some((base, *exponent)),
                None => None,
            },
            TermShape::Number(_)
            | TermShape::Symbol(_)
            | TermShape::Call(_)
            | TermShape::Product(_)
            | TermShape::Sum(_, _) => None,
        }
    }

    /// The coefficient and the factors of a product. There is at least one
    /// factor, and a single factor has a coefficient other than 1 and is not
    /// a sum. The factors are sorted by their base and the sign of their
    /// exponent, none of them is a number or a product, and a factor that is
    /// a sum is primitive; with the coefficient 0, every factor is a
    /// reciprocal $b^{-1}$.
    #[must_use]
    pub fn as_product(&self) -> Option<(&Rational, &[Self])> {
        match &self.0.shape {
            TermShape::Product(coefficient) => Some((coefficient, &self.0.children)),
            TermShape::Number(_)
            | TermShape::Symbol(_)
            | TermShape::Call(_)
            | TermShape::Power(_)
            | TermShape::Sum(_, _) => None,
        }
    }

    /// The constant of a sum, the coefficients of its monomials and their
    /// cores. The two lists have the same length and are in the order of the
    /// cores, and the constant and the monomials are at least two parts. No
    /// core is a number or a sum, a core that is a product has the
    /// coefficient 1, and at most one monomial, the witness, has the
    /// coefficient 0.
    #[must_use]
    pub fn as_sum(&self) -> Option<(&Rational, &[Rational], &[Self])> {
        match &self.0.shape {
            TermShape::Sum(constant, coefficients) => {
                Some((constant, coefficients, &self.0.children))
            }
            TermShape::Number(_)
            | TermShape::Symbol(_)
            | TermShape::Call(_)
            | TermShape::Power(_)
            | TermShape::Product(_) => None,
        }
    }
}

impl StorageCost for Term {
    /// The tree size of the term in nodes, and its logical bytes by the term
    /// formula of the contract, both cached in its node.
    fn storage(&self) -> Storage {
        Storage::new(self.0.size, self.0.bytes)
    }
}

impl fmt::Debug for Term {
    /// A shallow view of the node: its kind, the value of a number, the name
    /// of a symbol or the exponent of a power, the number of its children,
    /// its size and its depth; never the children themselves, so the output
    /// does not grow with the term.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut view = f.debug_struct("Term");
        view.field("kind", &self.kind());
        match &self.0.shape {
            TermShape::Number(value) => {
                view.field("value", &format_args!("{value}"));
            }
            TermShape::Symbol(name) => {
                view.field("name", name);
            }
            TermShape::Power(exponent) => {
                view.field("exponent", exponent);
            }
            TermShape::Call(_) | TermShape::Product(_) | TermShape::Sum(_, _) => {}
        }
        view.field("children", &self.0.children.len())
            .field("size", &self.0.size)
            .field("depth", &self.0.depth)
            .finish_non_exhaustive()
    }
}

/// A test-only constructor of the reserved call node, which no constructor
/// of this release builds: the tests pin its place in the order and in the
/// rules of sums, products and powers.
#[cfg(test)]
fn reserved_call(
    name: &str,
    class: node::CallClass,
    arguments: &[Term],
    context: &mut Context,
) -> Result<Term> {
    let head = node::CallHead {
        name: Box::from(name),
        class,
    };
    node::make(TermShape::Call(head), arguments.to_vec(), context)
}

// A term is not `Send`: its nodes are shared through `Rc`. This fails to
// compile once `Term` implements `Send`, since the parameter `A` of
// `not_send` can then be inferred in two ways; moving the nodes to `Arc` is
// a deliberate change that removes it.
mod send_guard {
    pub(super) trait AmbiguousIfSend<A> {}
    impl<T: ?Sized> AmbiguousIfSend<()> for T {}
    impl<T: ?Sized + Send> AmbiguousIfSend<u8> for T {}

    pub(super) const fn not_send<T: ?Sized + AmbiguousIfSend<A>, A>() {}
}
const _: () = send_guard::not_send::<Term, _>();
