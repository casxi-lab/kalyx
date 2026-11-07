//! Canonical sums, their scaling by a number and their primitive parts.
//!
//! A sum is collected from a work stack of summands: numbers and the
//! constants of nested sums add into one constant, nested sums are
//! flattened into their monomials, a product becomes the monomial of its
//! coefficient and its core, the product without the coefficient, and every
//! other summand is a monomial with coefficient 1. The monomials are sorted
//! by their cores, and monomials with equal cores add their coefficients.
//! Monomials that cancel to 0 leave one witness monomial with coefficient 0
//! for the bases that the remaining monomials do not cover.
//!
//! No core of a sum is a sum. A number $c$ other than 0 and 1 times a sum
//! $s$ is the sum whose constant and coefficients are those of $s$
//! multiplied by $c$, over the same cores ([`scaled`]), so
//! $2 (x + y) = 2x + 2y$. A sum that is a factor of a product or the base of
//! a power is written as $s = c \cdot p$ ([`primitive`]): its content $c$,
//! the coefficient of its first monomial whose coefficient is not 0, or its
//! constant when its only monomial is the witness, and its primitive part
//! $p = s / c$, whose content is 1. Only the division of rationals is used,
//! never a greatest common divisor.

use std::cmp::Ordering;

use crate::number::Rational;
use crate::{Context, Result};

use super::Term;
use super::node::{self, TermShape, add_rationals, internal, is_one, is_sum, multiply_rationals};
use super::order;
use super::sort::{self, SortItem, item_at};
use super::witness;

/// A monomial: `coefficient` times `core`.
struct SumMonomial {
    core: Term,
    coefficient: Rational,
}

impl SortItem for SumMonomial {
    fn sort_term(&self) -> &Term {
        &self.core
    }

    fn sort_negative(&self) -> bool {
        false
    }
}

/// A summand waiting on the work stack.
enum SumOperand {
    /// A whole term.
    Whole(Term),
    /// A monomial of a canonical sum: its coefficient and its core.
    Scaled(Rational, Term),
}

/// The state of a sum being collected.
struct SumState {
    constant: Rational,
    items: Vec<SumMonomial>,
}

/// The canonical sum of `operands`.
pub(super) fn sum(operands: &[Term], context: &mut Context) -> Result<Term> {
    let mut state = SumState {
        constant: Rational::from(0),
        items: Vec::new(),
    };
    drain(&mut state, wholes(operands), context)?;
    let monomials = collect(&state.items, context)?;
    finish(state.constant, monomials, context)
}

/// The operands as whole summands, the first on top of the stack.
fn wholes(operands: &[Term]) -> Vec<SumOperand> {
    let mut pending = Vec::with_capacity(operands.len());
    let mut index = operands.len();
    while index > 0 {
        index -= 1;
        pending.push(SumOperand::Whole(operands[index].clone()));
    }
    pending
}

/// Takes the summands from the work stack, one unit each.
fn drain(state: &mut SumState, mut pending: Vec<SumOperand>, context: &mut Context) -> Result<()> {
    while let Some(summand) = pending.pop() {
        context.charge(1)?;
        take(state, &mut pending, summand, context)?;
    }
    Ok(())
}

/// Collects one summand.
fn take(
    state: &mut SumState,
    pending: &mut Vec<SumOperand>,
    summand: SumOperand,
    context: &mut Context,
) -> Result<()> {
    match summand {
        SumOperand::Scaled(coefficient, core) => {
            state.items.push(SumMonomial { core, coefficient });
            Ok(())
        }
        SumOperand::Whole(term) => take_whole(state, pending, &term, context),
    }
}

/// Collects one whole term.
fn take_whole(
    state: &mut SumState,
    pending: &mut Vec<SumOperand>,
    term: &Term,
    context: &mut Context,
) -> Result<()> {
    match &term.0.shape {
        TermShape::Number(value) => {
            state.constant = add_rationals(&state.constant, value, context)?;
            Ok(())
        }
        TermShape::Sum(constant, coefficients) => {
            state.constant = add_rationals(&state.constant, constant, context)?;
            take_monomials(pending, &term.0.children, coefficients)
        }
        TermShape::Product(coefficient) => {
            let core = product_core(term, coefficient, context)?;
            state.items.push(SumMonomial {
                core,
                coefficient: coefficient.clone(),
            });
            Ok(())
        }
        TermShape::Symbol(_) | TermShape::Call(_) | TermShape::Power(_) => {
            state.items.push(SumMonomial {
                core: term.clone(),
                coefficient: Rational::from(1),
            });
            Ok(())
        }
    }
}

/// Pushes the monomials of a canonical sum, after checking that every core
/// has its coefficient.
fn take_monomials(
    pending: &mut Vec<SumOperand>,
    cores: &[Term],
    coefficients: &[Rational],
) -> Result<()> {
    if cores.len() != coefficients.len() {
        return Err(internal("a sum with a monomial without a coefficient"));
    }
    push_monomials(pending, cores, coefficients);
    Ok(())
}

/// Pushes the monomials of a canonical sum, the first on top of the stack;
/// `cores` and `coefficients` have the same length.
fn push_monomials(pending: &mut Vec<SumOperand>, cores: &[Term], coefficients: &[Rational]) {
    let mut index = cores.len();
    while index > 0 {
        index -= 1;
        pending.push(SumOperand::Scaled(
            coefficients[index].clone(),
            cores[index].clone(),
        ));
    }
}

/// The core of a product: the product itself when its coefficient is 1, its
/// only factor when it has one, and otherwise the product of its factors
/// with the coefficient 1.
fn product_core(term: &Term, coefficient: &Rational, context: &mut Context) -> Result<Term> {
    if is_one(coefficient) {
        return Ok(term.clone());
    }
    let factors = &term.0.children;
    if factors.len() == 1 {
        return lone_factor(term);
    }
    node::make(
        TermShape::Product(Rational::from(1)),
        factors.clone(),
        context,
    )
}

/// The only factor of a product whose coefficient is not 1. It is never a
/// sum: a number other than 0 and 1 times a single sum is the scaled sum, so
/// no core of a sum becomes a sum.
fn lone_factor(term: &Term) -> Result<Term> {
    let factor = node::first_child(term)?;
    if is_sum(&factor) {
        return Err(internal("a product whose only factor is a sum"));
    }
    Ok(factor)
}

/// The monomials sorted by core, with the monomials of equal cores merged:
/// their coefficients add.
fn collect(items: &[SumMonomial], context: &mut Context) -> Result<Vec<SumMonomial>> {
    let positions = sort::sorted_order(items, context)?;
    let mut monomials: Vec<SumMonomial> = Vec::with_capacity(items.len());
    let mut index = 0;
    while index < positions.len() {
        context.charge(1)?;
        absorb(&mut monomials, item_at(items, &positions, index)?, context)?;
        index += 1;
    }
    Ok(monomials)
}

/// Adds `item` to the sorted monomials: merged into the last monomial when
/// their cores are equal, appended otherwise.
fn absorb(
    monomials: &mut Vec<SumMonomial>,
    item: &SumMonomial,
    context: &mut Context,
) -> Result<()> {
    let merged = match monomials.last() {
        Some(last) => {
            if order::compare(&last.core, &item.core, context)? == Ordering::Equal {
                Some(add_rationals(
                    &last.coefficient,
                    &item.coefficient,
                    context,
                )?)
            } else {
                None
            }
        }
        None => None,
    };
    match merged {
        Some(coefficient) => match monomials.last_mut() {
            Some(last) => {
                last.coefficient = coefficient;
                Ok(())
            }
            None => Err(internal("a merged monomial disappeared")),
        },
        None => {
            monomials.push(SumMonomial {
                core: item.core.clone(),
                coefficient: item.coefficient.clone(),
            });
            Ok(())
        }
    }
}

/// The sum of `constant` and the sorted monomials, with the witness of the
/// monomials that cancelled.
fn finish(
    constant: Rational,
    mut monomials: Vec<SumMonomial>,
    context: &mut Context,
) -> Result<Term> {
    let zeros = split_zeros(&mut monomials, context)?;
    let top = if zeros.is_empty() {
        Vec::new()
    } else {
        uncovered(&zeros, &monomials, context)?
    };
    if monomials.is_empty() && constant.is_zero() {
        return witness::zero_with(&top, context);
    }
    if !top.is_empty() {
        insert_witness(&mut monomials, &top, context)?;
    }
    assemble(constant, monomials, context)
}

/// Removes the monomials whose coefficient is 0 and returns their cores;
/// one unit per monomial scanned, and the others keep their order.
fn split_zeros(monomials: &mut Vec<SumMonomial>, context: &mut Context) -> Result<Vec<Term>> {
    let mut zeros = Vec::new();
    let mut kept = 0;
    let mut index = 0;
    while index < monomials.len() {
        context.charge(1)?;
        if monomials[index].coefficient.is_zero() {
            zeros.push(monomials[index].core.clone());
        } else {
            monomials.swap(kept, index);
            kept += 1;
        }
        index += 1;
    }
    monomials.truncate(kept);
    Ok(zeros)
}

/// The maximal bases that occur with a negative exponent in the cancelled
/// cores `zeros` and in no remaining monomial. Such a base is maximal exactly
/// when it is not an inner base of the cancelled cores: $N$ of the remaining
/// cores holds every base inside each of its elements. Without a negative
/// base in the cancelled cores, the remaining cores are not read.
fn uncovered(
    zeros: &[Term],
    monomials: &[SumMonomial],
    context: &mut Context,
) -> Result<Vec<Term>> {
    let (needed, inner) = witness::negative_bases_with_inner(zeros, context)?;
    if needed.is_empty() {
        return Ok(needed);
    }
    let cores = cores_of(monomials, context)?;
    let covered = witness::negative_bases(&cores, context)?;
    let rest = witness::difference(&needed, &covered, context)?;
    witness::difference(&rest, &inner, context)
}

/// The cores of the monomials, one unit each.
fn cores_of(monomials: &[SumMonomial], context: &mut Context) -> Result<Vec<Term>> {
    let mut cores = Vec::with_capacity(monomials.len());
    let mut index = 0;
    while index < monomials.len() {
        context.charge(1)?;
        cores.push(monomials[index].core.clone());
        index += 1;
    }
    Ok(cores)
}

/// Inserts the witness monomial $0 \cdot \prod b^{-1}$ of `bases` at its
/// place among the sorted monomials. No remaining monomial has its core:
/// such a monomial would cover the bases.
fn insert_witness(
    monomials: &mut Vec<SumMonomial>,
    bases: &[Term],
    context: &mut Context,
) -> Result<()> {
    let core = witness::witness_core(bases, context)?;
    let (position, found) = sort::search(monomials, &core, context)?;
    if found {
        return Err(internal("a witness core is the core of a monomial"));
    }
    monomials.insert(
        position,
        SumMonomial {
            core,
            coefficient: Rational::from(0),
        },
    );
    Ok(())
}

/// The sum node of `constant` and the sorted monomials: the constant alone
/// without monomials, the monomial alone for the constant 0 and one
/// monomial.
fn assemble(
    constant: Rational,
    mut monomials: Vec<SumMonomial>,
    context: &mut Context,
) -> Result<Term> {
    if monomials.is_empty() {
        return node::number(constant, context);
    }
    if constant.is_zero() && monomials.len() == 1 {
        return match monomials.pop() {
            Some(monomial) => monomial_term(monomial, context),
            None => Err(internal("a monomial disappeared")),
        };
    }
    let (coefficients, cores) = split_monomials(monomials, context)?;
    node::make(TermShape::Sum(constant, coefficients), cores, context)
}

/// The coefficients and the cores of the monomials, in order, one unit
/// each.
fn split_monomials(
    mut monomials: Vec<SumMonomial>,
    context: &mut Context,
) -> Result<(Vec<Rational>, Vec<Term>)> {
    let mut coefficients = Vec::with_capacity(monomials.len());
    let mut cores = Vec::with_capacity(monomials.len());
    monomials.reverse();
    while let Some(monomial) = monomials.pop() {
        context.charge(1)?;
        coefficients.push(monomial.coefficient);
        cores.push(monomial.core);
    }
    Ok((coefficients, cores))
}

/// The term of one monomial with a coefficient that is not 0: the core for
/// the coefficient 1, and otherwise the product of the coefficient and the
/// factors of the core. The core is not a sum, so the product is canonical.
fn monomial_term(monomial: SumMonomial, context: &mut Context) -> Result<Term> {
    let SumMonomial { core, coefficient } = monomial;
    if is_one(&coefficient) {
        return Ok(core);
    }
    let factors = if matches!(core.0.shape, TermShape::Product(_)) {
        core.0.children.clone()
    } else {
        vec![core]
    };
    node::make(TermShape::Product(coefficient), factors, context)
}

/// `factor` times the canonical sum `sum`, for a `factor` other than 0: the
/// sum of the same cores, in the same order, whose constant and coefficients
/// are those of `sum` multiplied by `factor`. The cores, their order and the
/// witness monomial do not change, and no other coefficient becomes 0, so
/// the node is canonical as it is built. Charges the product of `factor` and
/// the constant, then one unit and the product of `factor` and the
/// coefficient for each monomial, then the node, whose checks come before
/// its allocation; every product checks the bits of the scaled number.
pub(super) fn scaled(factor: &Rational, sum: &Term, context: &mut Context) -> Result<Term> {
    if factor.is_zero() {
        return Err(internal("a sum scaled by 0"));
    }
    let (constant, coefficients) = sum_parts(sum)?;
    let cores = &sum.0.children;
    if cores.len() != coefficients.len() {
        return Err(internal("a sum with a monomial without a coefficient"));
    }
    let scaled_constant = multiply_rationals(factor, constant, context)?;
    let scaled_coefficients = scale_coefficients(factor, coefficients, context)?;
    node::make(
        TermShape::Sum(scaled_constant, scaled_coefficients),
        cores.clone(),
        context,
    )
}

/// `factor` times each of `coefficients`, in order: one unit and the product
/// of two coefficients each.
fn scale_coefficients(
    factor: &Rational,
    coefficients: &[Rational],
    context: &mut Context,
) -> Result<Vec<Rational>> {
    let mut result = Vec::with_capacity(coefficients.len());
    let mut index = 0;
    while index < coefficients.len() {
        context.charge(1)?;
        result.push(multiply_rationals(factor, &coefficients[index], context)?);
        index += 1;
    }
    Ok(result)
}

/// The content $c$ and the primitive part $p = s / c$ of the canonical sum
/// $s$ `sum`. Charges one unit for the content; a sum whose content is 1 is
/// its own primitive part, and otherwise $p$ is the scaling of $s$ by
/// $1 / c$, after the inverse, as `Rational::inverse`. The content of $p$ is
/// 1, and $p$ has the cores of $s$, so $N(p) = N(s)$, and $p$ is 0 exactly
/// where $s$ is.
pub(super) fn primitive(sum: &Term, context: &mut Context) -> Result<(Rational, Term)> {
    let content = content_of(sum)?;
    context.charge(1)?;
    if is_one(&content) {
        return Ok((content, sum.clone()));
    }
    let inverse = content.inverse(context)?;
    let part = scaled(&inverse, sum, context)?;
    Ok((content, part))
}

/// The content of the canonical sum `sum`: the coefficient of its first
/// monomial whose coefficient is not 0, or its constant when its only
/// monomial has the coefficient 0. At most one monomial of a canonical sum,
/// the witness, has the coefficient 0, so the content is the coefficient of
/// its first or its second monomial, or its constant; a content 0 is a
/// broken invariant.
fn content_of(sum: &Term) -> Result<Rational> {
    let (constant, coefficients) = sum_parts(sum)?;
    let content = leading_coefficient(constant, coefficients);
    if content.is_zero() {
        return Err(internal("a sum whose parts are all 0"));
    }
    Ok(content.clone())
}

/// The first coefficient when it is not 0, otherwise the second when there
/// is one, and otherwise `constant`: with at most one coefficient 0, the
/// first coefficient that is not 0, or the constant when there is none.
fn leading_coefficient<'a>(constant: &'a Rational, coefficients: &'a [Rational]) -> &'a Rational {
    match coefficients.first() {
        Some(first) => {
            if !first.is_zero() {
                return first;
            }
            match coefficients.get(1) {
                Some(second) => second,
                None => constant,
            }
        }
        None => constant,
    }
}

/// The constant and the coefficients of the sum `sum`.
fn sum_parts(sum: &Term) -> Result<(&Rational, &[Rational])> {
    match &sum.0.shape {
        TermShape::Sum(constant, coefficients) => Ok((constant, coefficients)),
        TermShape::Number(_)
        | TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Power(_)
        | TermShape::Product(_) => Err(internal("the parts of a sum of a term that is not a sum")),
    }
}
