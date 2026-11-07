//! The bases that occur with a negative exponent, and the witnesses that keep
//! them where a simplification would drop them.
//!
//! Write $N(t)$ for the set of bases that occur with a negative exponent in
//! a term $t$, and $\max N(t)$ for those elements of $N(t)$ that do not occur
//! with a negative exponent inside another element. Canonicalization never
//! shrinks $N$: where it would lose a base, the term keeps a witness of it.
//! There are three witness shapes:
//!
//! - the zero product $0 \cdot \prod_{b \in \max N} b^{-1}$, or the number 0
//!   when the set is empty;
//! - the one $(b^{-1})^0$, a power with exponent 0 of a reciprocal; for a
//!   set, the product of the ones of its maximal elements;
//! - in a sum, one monomial with coefficient 0 whose core is
//!   $\prod_{b} b^{-1}$ over the bases that the other monomials do not
//!   cover.
//!
//! Since every element of $N$ that is not maximal occurs with a negative
//! exponent inside a maximal one, the witnesses of $\max N$ keep all of $N$.
//! The traversal that collects $N$ also collects its inner bases, the bases
//! that occur with a negative exponent inside the base of a negative power,
//! so $\max N$ is $N$ without its inner bases, one set difference away.
//!
//! A base that is a sum is taken by its primitive part, here and inside the
//! witnesses: a power raises the primitive part $p$ of a sum $s = c \cdot p$,
//! so every base of a canonical term that is a sum is primitive, and $N$ and
//! the witnesses read them as they are. The content $c$ is not 0, so $s$ and
//! $p$ are 0 at the same points, and keeping $p$ keeps every point where $s$
//! raised to a negative power is undefined.

use crate::number::Rational;
use crate::{Context, Result};

use super::Term;
use super::node::{self, TermShape, first_child};
use super::sort;

/// $N$ of `roots`: the bases that occur with a negative exponent in any of
/// `roots`, sorted and without repetitions. Charges one unit per node
/// visited; a subterm without a negative power is not entered.
pub(super) fn negative_bases(roots: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let (found, _) = occurrences(roots, context)?;
    sort::unique_sorted(&found, context)
}

/// $N$ of `roots` and its inner bases, the elements of $N$ that occur with a
/// negative exponent inside an element of $N$, both sorted and without
/// repetitions, from one traversal: one unit per node visited, then the
/// sorting and merging of both lists.
pub(super) fn negative_bases_with_inner(
    roots: &[Term],
    context: &mut Context,
) -> Result<(Vec<Term>, Vec<Term>)> {
    let (found, inside) = occurrences(roots, context)?;
    let all = sort::unique_sorted(&found, context)?;
    let inner = sort::unique_sorted(&inside, context)?;
    Ok((all, inner))
}

/// $\max N$ of `roots`, sorted: $N$ without its inner bases.
pub(super) fn maximal_bases(roots: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let (all, inner) = negative_bases_with_inner(roots, context)?;
    difference(&all, &inner, context)
}

/// Every occurrence of a base with a negative exponent in `roots`, and the
/// occurrences among them that lie inside the base of a negative power. A
/// frame of the stack holds a term and whether it lies inside such a base.
fn occurrences(roots: &[Term], context: &mut Context) -> Result<(Vec<Term>, Vec<Term>)> {
    let mut found = Vec::new();
    let mut inner = Vec::new();
    let mut stack = Vec::with_capacity(roots.len());
    push_tagged(&mut stack, roots, false);
    while let Some((term, inside)) = stack.pop() {
        context.charge(1)?;
        visit(&term, inside, &mut stack, &mut found, &mut inner)?;
    }
    Ok((found, inner))
}

/// Records the base of `term` when it is a negative power, as an inner base
/// too when `term` lies inside the base of a negative power, and pushes the
/// children of `term` when it holds a negative power; they lie inside such a
/// base when `term` does or is a negative power itself.
fn visit(
    term: &Term,
    inside: bool,
    stack: &mut Vec<(Term, bool)>,
    found: &mut Vec<Term>,
    inner: &mut Vec<Term>,
) -> Result<()> {
    if !term.0.negative {
        return Ok(());
    }
    let negative_power = node::is_negative_power(&term.0.shape);
    if negative_power {
        let base = first_child(term)?;
        if inside {
            inner.push(base.clone());
        }
        found.push(base);
    }
    push_tagged(stack, &term.0.children, inside || negative_power);
    Ok(())
}

/// Pushes clones of `terms` onto `stack`, each with the flag `inside`.
fn push_tagged(stack: &mut Vec<(Term, bool)>, terms: &[Term], inside: bool) {
    let mut index = 0;
    while index < terms.len() {
        stack.push((terms[index].clone(), inside));
        index += 1;
    }
}

/// The elements of the sorted list `all` that the sorted list `covered` does
/// not hold, in order; one unit per element of `all` and the comparisons of
/// a binary search.
pub(super) fn difference(
    all: &[Term],
    covered: &[Term],
    context: &mut Context,
) -> Result<Vec<Term>> {
    let mut rest = Vec::new();
    let mut index = 0;
    while index < all.len() {
        context.charge(1)?;
        if !sort::contains(covered, &all[index], context)? {
            rest.push(all[index].clone());
        }
        index += 1;
    }
    Ok(rest)
}

/// $b^{-1}$ for each $b$ of the sorted list `bases`: the factors of a zero
/// product, sorted by their bases.
fn reciprocals(bases: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let mut result = Vec::with_capacity(bases.len());
    let mut index = 0;
    while index < bases.len() {
        result.push(reciprocal(&bases[index], context)?);
        index += 1;
    }
    Ok(result)
}

/// $b^{-1}$. A base with a negative exponent is never a number or a product,
/// a base that is a sum is primitive, and the power never merges with it, so
/// the node is canonical.
fn reciprocal(base: &Term, context: &mut Context) -> Result<Term> {
    node::make(TermShape::Power(-1), vec![base.clone()], context)
}

/// The ones $(b^{-1})^0$ of the sorted list `bases`, sorted: the witness
/// factors of a product.
pub(super) fn ones(bases: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let mut result = Vec::with_capacity(bases.len());
    let mut index = 0;
    while index < bases.len() {
        let inverse = reciprocal(&bases[index], context)?;
        result.push(node::make(TermShape::Power(0), vec![inverse], context)?);
        index += 1;
    }
    Ok(result)
}

/// $0 \cdot \prod_{b} b^{-1}$ over the sorted list `bases`, or the number 0
/// when it is empty.
pub(super) fn zero_with(bases: &[Term], context: &mut Context) -> Result<Term> {
    if bases.is_empty() {
        return node::number(Rational::from(0), context);
    }
    let factors = reciprocals(bases, context)?;
    node::make(TermShape::Product(Rational::from(0)), factors, context)
}

/// $t^0$: the number 1 when $t$ holds no negative power, and otherwise the
/// product of the ones $(b^{-1})^0$ of $\max N(t)$.
pub(super) fn power_zero(term: &Term, context: &mut Context) -> Result<Term> {
    if !term.0.negative {
        return node::number(Rational::from(1), context);
    }
    let top = maximal_bases(std::slice::from_ref(term), context)?;
    let mut factors = ones(&top, context)?;
    if factors.len() == 1 {
        return match factors.pop() {
            Some(factor) => Ok(factor),
            None => Err(node::internal("a witness disappeared")),
        };
    }
    node::make(TermShape::Product(Rational::from(1)), factors, context)
}

/// The core of the zero monomial of a sum: $\prod_{b} b^{-1}$ over the
/// sorted, nonempty list `bases`, or the reciprocal alone for one base.
pub(super) fn witness_core(bases: &[Term], context: &mut Context) -> Result<Term> {
    let mut factors = reciprocals(bases, context)?;
    if factors.len() == 1 {
        return match factors.pop() {
            Some(factor) => Ok(factor),
            None => Err(node::internal("a witness disappeared")),
        };
    }
    node::make(TermShape::Product(Rational::from(1)), factors, context)
}
