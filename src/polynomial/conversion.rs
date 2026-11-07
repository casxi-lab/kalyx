//! The conversion of a polynomial of $\mathbb{Q}\[x\]$ back into a term.
//!
//! The term is built only through the constructors of the term core, which
//! check and charge every node and keep it canonical: the term of each
//! term $c x^k$ of the polynomial is the number $c$ for $k = 0$, the product
//! of $c$ and the symbol $x$ for $k = 1$, and the product of $c$ and the
//! power $x^k$ for $k \ge 2$; the term of the polynomial is their sum, so
//! the zero polynomial is the number 0. The symbol of the variable is built
//! once, when the polynomial has a term of positive degree.

use crate::coefficient::Rationals;
use crate::term::Term;
use crate::{Context, Result};

use super::terms::{DEGREE_WIDTH, PolynomialTerms, internal};
use super::{Polynomial, PolynomialRing};

/// The work units charged for each term of the polynomial, before its term
/// is built.
const TERM_CHARGE: u64 = 1;

/// The canonical term of `polynomial`, whose variable is that of `ring`.
pub(super) fn to_term(
    ring: &PolynomialRing<Rationals>,
    polynomial: &Polynomial,
    context: &mut Context,
) -> Result<Term> {
    let variable = variable_term(ring, polynomial, context)?;
    let monomials = monomial_terms(&polynomial.terms, variable.as_ref(), context)?;
    Term::sum(&monomials, context)
}

/// The symbol of the variable, when `polynomial` has a term of positive
/// degree.
fn variable_term(
    ring: &PolynomialRing<Rationals>,
    polynomial: &Polynomial,
    context: &mut Context,
) -> Result<Option<Term>> {
    match polynomial.degree() {
        Some(degree) => {
            if degree > 0 {
                Ok(Some(Term::symbol(ring.variable(), context)?))
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// The terms of the terms of `terms`, in increasing degree: one unit each,
/// then the constructors of the term core.
fn monomial_terms(
    terms: &PolynomialTerms<crate::number::Rational>,
    variable: Option<&Term>,
    context: &mut Context,
) -> Result<Vec<Term>> {
    let mut monomials = Vec::with_capacity(terms.len());
    let mut index = 0;
    while index < terms.len() {
        context.charge(TERM_CHARGE)?;
        monomials.push(monomial_term(terms, index, variable, context)?);
        index += 1;
    }
    Ok(monomials)
}

/// The term $c x^k$ of the term at `index` of `terms`.
fn monomial_term(
    terms: &PolynomialTerms<crate::number::Rational>,
    index: usize,
    variable: Option<&Term>,
    context: &mut Context,
) -> Result<Term> {
    let (degree, coefficient) = match terms.term(index) {
        Some(term) => term,
        None => return Err(internal("a converted term past the last term")),
    };
    let number = Term::number(coefficient.clone(), context)?;
    if degree == 0 {
        return Ok(number);
    }
    let factor = match variable {
        Some(symbol) => variable_power(symbol, degree, context)?,
        None => return Err(internal("a term of positive degree without the variable")),
    };
    Term::product(&[number, factor], context)
}

/// $x^k$ for $k \ge 1$: the symbol itself for $k = 1$.
pub(super) fn variable_power(symbol: &Term, degree: u64, context: &mut Context) -> Result<Term> {
    if degree == 1 {
        return Ok(symbol.clone());
    }
    // Every degree was checked against the width of `i64` when its
    // polynomial was admitted.
    if degree > DEGREE_WIDTH {
        return Err(internal("a degree beyond the width of i64"));
    }
    symbol.power(degree as i64, context)
}
