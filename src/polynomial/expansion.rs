//! The expansion of a term into a polynomial of $\mathbb{Q}\[x\]$.
//!
//! The expansion walks the term with an explicit stack on the heap: each
//! node is entered before its children, which follow in their stored order,
//! and its polynomial is formed after theirs. A frame of the stack holds
//! owned terms, copied scalars and the owned total of an open sum or
//! product, never a borrowed reference. A result register carries the
//! polynomial of the last finished subterm to the frame that waits for it,
//! so it holds at most one polynomial.
//!
//! Every occurrence of a node charges one unit when it is entered, before
//! its children, and a symbol one more per byte of the shorter of its name
//! and the variable name, before the two are compared:
//!
//! - a number is the constant polynomial of its value;
//! - the variable of the ring is the polynomial $x$, and any other symbol
//!   fails with `UnknownSymbol`;
//! - a power with an exponent $k \ge 0$ is the power $p^k$ of the polynomial
//!   $p$ of its base, and a power with a negative exponent fails with
//!   `NotPolynomial` once its base is expanded;
//! - a product builds the constant of its coefficient when it is entered and
//!   multiplies it by the polynomial of each factor in turn;
//! - a sum builds the constant of its constant when it is entered and adds
//!   to it, for each monomial in turn, the product of the constant of its
//!   coefficient and the polynomial of its core;
//! - a call fails with `NotPolynomial` when it is entered, before its
//!   arguments; no term of this release is a call.
//!
//! The first failure in this order ends the expansion. Since a base is
//! never a number, a base whose expansion succeeds holds the variable, so
//! every negative power whose base holds the variable and no other symbol
//! fails with `NotPolynomial`, the witnesses of the term core among them,
//! while a base that holds another symbol fails with `UnknownSymbol` first.

use crate::coefficient::Rationals;
use crate::term::{Term, TermKind};
use crate::{Context, Error, FaultKind, LimitField, Result};

use super::arithmetic;
use super::terms::internal;
use super::{Polynomial, PolynomialRing};

/// The work units charged for each occurrence of a node, when it is
/// entered, before its children.
const NODE_CHARGE: u64 = 1;

/// A frame of the expansion stack.
enum PolynomialFrame {
    /// A term to visit.
    Enter(Term),
    /// A power with this exponent, waiting for the polynomial of its base.
    Raise(i64),
    /// A product waiting for the polynomial of the factor at `index`;
    /// `total` is the product of its coefficient and the factors before it.
    Factor {
        product: Term,
        index: usize,
        total: Polynomial,
    },
    /// A sum waiting for the polynomial of the core of the monomial at
    /// `index`; `total` is the sum of its constant and the monomials before
    /// it.
    Monomial {
        sum: Term,
        index: usize,
        total: Polynomial,
    },
}

/// The stack of an expansion and its result register.
struct PolynomialExpansion {
    stack: Vec<PolynomialFrame>,
    result: Option<Polynomial>,
}

/// The polynomial of `term` in the ring `ring`. The depth of the term is
/// checked against `max_depth` first, before any charge; then the term is
/// walked, each node charged when it is entered, before its children.
pub(super) fn expand(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    context: &mut Context,
) -> Result<Polynomial> {
    context.check(LimitField::Depth, term.depth())?;
    visit(ring, term, context)
}

/// The loop of the expansion over its stack.
fn visit(
    ring: &PolynomialRing<Rationals>,
    root: &Term,
    context: &mut Context,
) -> Result<Polynomial> {
    let mut expansion = PolynomialExpansion {
        stack: vec![PolynomialFrame::Enter(root.clone())],
        result: None,
    };
    while let Some(frame) = expansion.stack.pop() {
        step(ring, frame, &mut expansion, context)?;
    }
    finish(expansion.result)
}

/// The polynomial of the root, which the register holds once the stack is
/// empty.
fn finish(result: Option<Polynomial>) -> Result<Polynomial> {
    match result {
        Some(polynomial) => Ok(polynomial),
        None => Err(internal("an expansion without a result")),
    }
}

/// Takes one frame from the stack.
fn step(
    ring: &PolynomialRing<Rationals>,
    frame: PolynomialFrame,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    match frame {
        PolynomialFrame::Enter(term) => enter(ring, &term, expansion, context),
        PolynomialFrame::Raise(exponent) => raise(ring, exponent, expansion, context),
        PolynomialFrame::Factor {
            product,
            index,
            total,
        } => next_factor(ring, product, (index, total), expansion, context),
        PolynomialFrame::Monomial { sum, index, total } => {
            next_monomial(ring, sum, (index, total), expansion, context)
        }
    }
}

/// Enters `term`: charges one unit, then delivers the polynomial of a leaf,
/// or opens the frame of a power, a product or a sum and pushes its first
/// child.
fn enter(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    context.charge(NODE_CHARGE)?;
    match term.kind() {
        TermKind::Number => number(ring, term, expansion, context),
        TermKind::Symbol => symbol(ring, term, expansion, context),
        TermKind::Power => open_power(term, expansion),
        TermKind::Product => open_product(ring, term, expansion, context),
        TermKind::Sum => open_sum(ring, term, expansion, context),
        TermKind::Call => Err(Error::new(
            FaultKind::NotPolynomial,
            None,
            "a function call is not a polynomial",
        )),
    }
}

/// The constant polynomial of a number.
fn number(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let constant = match term.as_number() {
        Some(value) => ring.constant(value, context)?,
        None => return Err(internal("a number without a value")),
    };
    deliver(expansion, constant)
}

/// The polynomial $x$ of the variable; any other symbol fails. Charges one
/// unit per byte of the shorter name before the comparison.
fn symbol(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let name = match term.as_symbol() {
        Some(name) => name,
        None => return Err(internal("a symbol without a name")),
    };
    let variable = ring.variable();
    context.charge(shorter(name.len(), variable.len()))?;
    if !same_name(name.as_bytes(), variable.as_bytes()) {
        return Err(Error::new(
            FaultKind::UnknownSymbol,
            None,
            "a symbol other than the variable of the polynomial ring",
        ));
    }
    let generator = ring.generator(context)?;
    deliver(expansion, generator)
}

/// The smaller of two lengths, as work units.
const fn shorter(left: usize, right: usize) -> u64 {
    if left < right {
        left as u64
    } else {
        right as u64
    }
}

/// Whether two names have the same bytes.
fn same_name(left: &[u8], right: &[u8]) -> bool {
    let mut index = 0;
    while index < left.len() && index < right.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    left.len() == right.len()
}

/// Opens a power: its exponent waits for the polynomial of its base.
fn open_power(term: &Term, expansion: &mut PolynomialExpansion) -> Result<()> {
    let (base, exponent) = match term.as_power() {
        Some(power) => power,
        None => return Err(internal("a power without a base")),
    };
    expansion.stack.push(PolynomialFrame::Raise(exponent));
    expansion.stack.push(PolynomialFrame::Enter(base.clone()));
    Ok(())
}

/// The power of the polynomial of the base, which the register holds; a
/// negative exponent fails.
fn raise(
    ring: &PolynomialRing<Rationals>,
    exponent: i64,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let base = take(expansion)?;
    if exponent < 0 {
        return Err(Error::new(
            FaultKind::NotPolynomial,
            None,
            "a negative power of a base that holds the variable",
        ));
    }
    // The exponent is not negative, so the conversion is exact.
    let power = ring.power(&base, exponent as u64, context)?;
    deliver(expansion, power)
}

/// Opens a product: its total starts from the constant of its coefficient,
/// and its first factor is pushed.
fn open_product(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let (coefficient, factors) = match term.as_product() {
        Some(product) => product,
        None => return Err(internal("a product without factors")),
    };
    let first = match factors.first() {
        Some(factor) => factor.clone(),
        None => return Err(internal("a product without factors")),
    };
    let total = ring.constant(coefficient, context)?;
    expansion.stack.push(PolynomialFrame::Factor {
        product: term.clone(),
        index: 0,
        total,
    });
    expansion.stack.push(PolynomialFrame::Enter(first));
    Ok(())
}

/// Multiplies the total of a product by the polynomial of its factor at
/// `index`, which the register holds, then pushes the next factor or
/// delivers the total.
fn next_factor(
    ring: &PolynomialRing<Rationals>,
    product: Term,
    progress: (usize, Polynomial),
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let (index, total) = progress;
    let factor = take(expansion)?;
    let total = ring.multiply(&total, &factor, context)?;
    let next = index + 1;
    let following = match product.as_product() {
        Some((_, factors)) => term_at(factors, next),
        None => return Err(internal("a product without factors")),
    };
    match following {
        Some(factor) => {
            expansion.stack.push(PolynomialFrame::Factor {
                product,
                index: next,
                total,
            });
            expansion.stack.push(PolynomialFrame::Enter(factor));
            Ok(())
        }
        None => deliver(expansion, total),
    }
}

/// Opens a sum: its total starts from the constant of its constant, and the
/// core of its first monomial is pushed.
fn open_sum(
    ring: &PolynomialRing<Rationals>,
    term: &Term,
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let (constant, _, cores) = match term.as_sum() {
        Some(sum) => sum,
        None => return Err(internal("a sum without monomials")),
    };
    let first = match cores.first() {
        Some(core) => core.clone(),
        None => return Err(internal("a sum without monomials")),
    };
    let total = ring.constant(constant, context)?;
    expansion.stack.push(PolynomialFrame::Monomial {
        sum: term.clone(),
        index: 0,
        total,
    });
    expansion.stack.push(PolynomialFrame::Enter(first));
    Ok(())
}

/// Adds the monomial at `index` of a sum to its total: the product of the
/// constant of its coefficient and the polynomial of its core, which the
/// register holds. Then pushes the next core or delivers the total.
fn next_monomial(
    ring: &PolynomialRing<Rationals>,
    sum: Term,
    progress: (usize, Polynomial),
    expansion: &mut PolynomialExpansion,
    context: &mut Context,
) -> Result<()> {
    let (index, total) = progress;
    let core = take(expansion)?;
    let next = index + 1;
    let (scale, following) = match sum.as_sum() {
        Some((_, coefficients, cores)) => match coefficients.get(index) {
            Some(coefficient) => (ring.constant(coefficient, context)?, term_at(cores, next)),
            None => return Err(internal("a monomial without a coefficient")),
        },
        None => return Err(internal("a sum without monomials")),
    };
    let monomial = ring.multiply(&scale, &core, context)?;
    let total = arithmetic::accumulate(ring, total, monomial, context)?;
    match following {
        Some(core) => {
            expansion.stack.push(PolynomialFrame::Monomial {
                sum,
                index: next,
                total,
            });
            expansion.stack.push(PolynomialFrame::Enter(core));
            Ok(())
        }
        None => deliver(expansion, total),
    }
}

/// An owned copy of the term at `index` of `terms`, or `None` past the last
/// one.
fn term_at(terms: &[Term], index: usize) -> Option<Term> {
    if index < terms.len() {
        Some(terms[index].clone())
    } else {
        None
    }
}

/// Puts the polynomial of a finished subterm into the register, which is
/// empty between a subterm and the frame that waits for it.
fn deliver(expansion: &mut PolynomialExpansion, polynomial: Polynomial) -> Result<()> {
    match expansion.result.replace(polynomial) {
        None => Ok(()),
        Some(_) => Err(internal("an expansion result that no frame took")),
    }
}

/// Takes the polynomial of the subterm that a frame waits for from the
/// register.
fn take(expansion: &mut PolynomialExpansion) -> Result<Polynomial> {
    match expansion.result.take() {
        Some(polynomial) => Ok(polynomial),
        None => Err(internal("a frame without the result of its child")),
    }
}
