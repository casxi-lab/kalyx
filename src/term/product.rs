//! Canonical products.
//!
//! A product is collected from a work stack of operands: nested products are
//! flattened, numbers and the coefficients of nested products are multiplied
//! exactly into one coefficient, ones $(b^{-1})^0$ are set aside as
//! witnesses, and every other operand becomes a factor item: a base and its
//! exponent, 1 for an operand that is not a power. A sum $s$ is taken as
//! $s = c \cdot p$, its content $c$ and its primitive part $p$: $c$
//! multiplies into the coefficient and $p$ is the item, so
//! $(2x + 2y) z = 2 (x + y) z$. The items are sorted by their key, the base
//! and the sign of the exponent, and items with equal keys merge by adding
//! their exponents, so $(2x + 2y)(x + y) = 2 (x + y)^2$; items of one base
//! with exponents of opposite sign have different keys and never merge, so
//! the product keeps every base that occurs with a negative exponent. A zero
//! coefficient keeps the witness $0 \cdot \prod b^{-1}$ of the bases it would
//! drop, and a one $(b^{-1})^0$ stays only where the other factors do not
//! cover its base. A coefficient other than 0 and 1 times a single factor
//! that is a sum is that sum scaled by the coefficient, so no product has a
//! sum as its only factor.

use std::cmp::Ordering;

use crate::number::Rational;
use crate::{Context, Result};

use super::Term;
use super::exponent;
use super::node::{self, TermShape, first_child, internal, is_one, is_sum, multiply_rationals};
use super::sort::{self, SortItem, compare_items, item_at};
use super::sum;
use super::witness;

/// A collected factor: `base` raised to `exponent`, which is not 0.
struct FactorItem {
    base: Term,
    exponent: i64,
}

impl SortItem for FactorItem {
    fn sort_term(&self) -> &Term {
        &self.base
    }

    fn sort_negative(&self) -> bool {
        self.exponent < 0
    }
}

/// A finished factor with its key: the base and the sign of its exponent,
/// the factor itself for a factor that is not a power.
struct FactorSlot {
    key: Term,
    negative: bool,
    factor: Term,
}

impl SortItem for FactorSlot {
    fn sort_term(&self) -> &Term {
        &self.key
    }

    fn sort_negative(&self) -> bool {
        self.negative
    }
}

/// The state of a product being collected.
struct ProductState {
    coefficient: Rational,
    items: Vec<FactorItem>,
    witnesses: Vec<Term>,
}

/// The canonical product of `coefficient` and `operands`.
pub(super) fn product(
    coefficient: Rational,
    operands: &[Term],
    context: &mut Context,
) -> Result<Term> {
    let mut state = ProductState {
        coefficient,
        items: Vec::new(),
        witnesses: Vec::new(),
    };
    let mut pending = Vec::with_capacity(operands.len());
    push_reversed(&mut pending, operands);
    drain(&mut state, pending, context)?;
    let entries = collect(&state.items, context)?;
    finish(state.coefficient, &entries, &state.witnesses, context)
}

/// Pushes clones of `terms` in reverse, so that the first is taken first.
fn push_reversed(stack: &mut Vec<Term>, terms: &[Term]) {
    let mut index = terms.len();
    while index > 0 {
        index -= 1;
        stack.push(terms[index].clone());
    }
}

/// Takes the operands from the work stack, one unit each.
fn drain(state: &mut ProductState, mut pending: Vec<Term>, context: &mut Context) -> Result<()> {
    while let Some(term) = pending.pop() {
        context.charge(1)?;
        take(state, &mut pending, &term, context)?;
    }
    Ok(())
}

/// Collects one operand.
fn take(
    state: &mut ProductState,
    pending: &mut Vec<Term>,
    term: &Term,
    context: &mut Context,
) -> Result<()> {
    match &term.0.shape {
        TermShape::Number(value) => {
            state.coefficient = multiply_rationals(&state.coefficient, value, context)?;
            Ok(())
        }
        TermShape::Product(coefficient) => {
            state.coefficient = multiply_rationals(&state.coefficient, coefficient, context)?;
            push_reversed(pending, &term.0.children);
            Ok(())
        }
        TermShape::Power(exponent) => {
            if *exponent == 0 {
                state.witnesses.push(term.clone());
            } else {
                state.items.push(FactorItem {
                    base: first_child(term)?,
                    exponent: *exponent,
                });
            }
            Ok(())
        }
        TermShape::Sum(_, _) => {
            let (content, part) = sum::primitive(term, context)?;
            state.coefficient = multiply_rationals(&state.coefficient, &content, context)?;
            state.items.push(FactorItem {
                base: part,
                exponent: 1,
            });
            Ok(())
        }
        TermShape::Symbol(_) | TermShape::Call(_) => {
            state.items.push(FactorItem {
                base: term.clone(),
                exponent: 1,
            });
            Ok(())
        }
    }
}

/// The factor items sorted by key, with the items of equal keys merged:
/// their exponents, of one sign, add.
fn collect(items: &[FactorItem], context: &mut Context) -> Result<Vec<FactorItem>> {
    let positions = sort::sorted_order(items, context)?;
    let mut entries: Vec<FactorItem> = Vec::with_capacity(items.len());
    let mut index = 0;
    while index < positions.len() {
        context.charge(1)?;
        absorb(&mut entries, item_at(items, &positions, index)?, context)?;
        index += 1;
    }
    Ok(entries)
}

/// Adds `item` to the sorted entries: merged into the last entry when their
/// keys are equal, appended otherwise.
fn absorb(entries: &mut Vec<FactorItem>, item: &FactorItem, context: &mut Context) -> Result<()> {
    let same = match entries.last() {
        Some(last) => compare_items(last, item, context)? == Ordering::Equal,
        None => false,
    };
    if !same {
        entries.push(FactorItem {
            base: item.base.clone(),
            exponent: item.exponent,
        });
        return Ok(());
    }
    let last_exponent = match entries.last() {
        Some(last) => last.exponent,
        None => return Err(internal("a merged factor disappeared")),
    };
    let merged = exponent::sum(last_exponent, item.exponent, context)?;
    match entries.last_mut() {
        Some(last) => {
            last.exponent = merged;
            Ok(())
        }
        None => Err(internal("a merged factor disappeared")),
    }
}

/// The product of `coefficient`, the sorted entries and the witnesses.
fn finish(
    coefficient: Rational,
    entries: &[FactorItem],
    witnesses: &[Term],
    context: &mut Context,
) -> Result<Term> {
    let factors = entry_factors(entries, context)?;
    if coefficient.is_zero() {
        return zero_product(factors, witnesses, context);
    }
    if witnesses.is_empty() {
        return assemble(coefficient, factors, context);
    }
    let factors = with_witnesses(factors, witnesses, context)?;
    assemble(coefficient, factors, context)
}

/// The factors of the entries, in order: the base for the exponent 1, and
/// otherwise its power, one unit each. The base of an entry is never a
/// number or a product, a base that is a sum is primitive, and its exponent
/// never merges with it, so each power is canonical as it is built.
fn entry_factors(entries: &[FactorItem], context: &mut Context) -> Result<Vec<Term>> {
    let mut factors = Vec::with_capacity(entries.len());
    let mut index = 0;
    while index < entries.len() {
        context.charge(1)?;
        let entry = &entries[index];
        if entry.exponent == 1 {
            factors.push(entry.base.clone());
        } else {
            factors.push(node::make(
                TermShape::Power(entry.exponent),
                vec![entry.base.clone()],
                context,
            )?);
        }
        index += 1;
    }
    Ok(factors)
}

/// A product whose coefficient is 0: $0 \cdot \prod b^{-1}$ over the maximal
/// bases that occur with a negative exponent in its factors and witnesses,
/// or the number 0 when there are none.
fn zero_product(mut factors: Vec<Term>, witnesses: &[Term], context: &mut Context) -> Result<Term> {
    factors.extend_from_slice(witnesses);
    let top = witness::maximal_bases(&factors, context)?;
    witness::zero_with(&top, context)
}

/// The factors with the ones $(b^{-1})^0$ that the witnesses need: the
/// maximal bases of the witnesses that the factors do not cover, in the
/// order of the factor keys. A base of the witnesses that the factors do not
/// cover is maximal exactly when it is not an inner base of the witnesses:
/// $N$ of the factors holds every base inside each of its elements.
fn with_witnesses(
    factors: Vec<Term>,
    witnesses: &[Term],
    context: &mut Context,
) -> Result<Vec<Term>> {
    let (needed, inner) = witness::negative_bases_with_inner(witnesses, context)?;
    let covered = witness::negative_bases(&factors, context)?;
    let rest = witness::difference(&needed, &covered, context)?;
    let top = witness::difference(&rest, &inner, context)?;
    if top.is_empty() {
        return Ok(factors);
    }
    let mut extra = witness::ones(&top, context)?;
    let mut all = factors;
    all.append(&mut extra);
    sort_factors(&all, context)
}

/// `factors` in the order of their keys, each charged when the key is
/// formed.
fn sort_factors(factors: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let slots = factor_slots(factors, context)?;
    ordered_factors(&slots, context)
}

/// The factors of `slots` in the order of their keys.
fn ordered_factors(slots: &[FactorSlot], context: &mut Context) -> Result<Vec<Term>> {
    let positions = sort::sorted_order(slots, context)?;
    let mut sorted = Vec::with_capacity(slots.len());
    let mut index = 0;
    while index < positions.len() {
        sorted.push(item_at(slots, &positions, index)?.factor.clone());
        index += 1;
    }
    Ok(sorted)
}

/// The key of each factor: the base and the sign of its exponent for a
/// power, the factor itself otherwise.
fn factor_slots(factors: &[Term], context: &mut Context) -> Result<Vec<FactorSlot>> {
    let mut slots = Vec::with_capacity(factors.len());
    let mut index = 0;
    while index < factors.len() {
        context.charge(1)?;
        slots.push(factor_slot(&factors[index])?);
        index += 1;
    }
    Ok(slots)
}

/// The key of one factor.
fn factor_slot(factor: &Term) -> Result<FactorSlot> {
    match &factor.0.shape {
        TermShape::Power(exponent) => Ok(FactorSlot {
            key: first_child(factor)?,
            negative: *exponent < 0,
            factor: factor.clone(),
        }),
        TermShape::Number(_)
        | TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Product(_)
        | TermShape::Sum(_, _) => Ok(FactorSlot {
            key: factor.clone(),
            negative: false,
            factor: factor.clone(),
        }),
    }
}

/// The product of a coefficient that is not 0 and sorted factors: the number
/// alone without factors, [`assemble_one`] for one factor, and otherwise a
/// product node.
pub(super) fn assemble(
    coefficient: Rational,
    mut factors: Vec<Term>,
    context: &mut Context,
) -> Result<Term> {
    if factors.is_empty() {
        return node::number(coefficient, context);
    }
    if factors.len() == 1 {
        return match factors.pop() {
            Some(factor) => assemble_one(coefficient, factor, context),
            None => Err(internal("a factor disappeared")),
        };
    }
    node::make(TermShape::Product(coefficient), factors, context)
}

/// The product of a coefficient that is not 0 and one factor: the factor
/// alone for the coefficient 1; for another coefficient, the factor scaled
/// by it when the factor is a sum, and otherwise a product node.
fn assemble_one(coefficient: Rational, factor: Term, context: &mut Context) -> Result<Term> {
    if is_one(&coefficient) {
        return Ok(factor);
    }
    if is_sum(&factor) {
        return sum::scaled(&coefficient, &factor, context);
    }
    node::make(TermShape::Product(coefficient), vec![factor], context)
}
