//! Canonical integer powers.
//!
//! The exponent is checked against `max_exponent` before anything else. A
//! numeric base is evaluated strictly with the exact power of the number:
//! $0^0 = 1$, and a negative power of zero fails with `DivisionByZero`. For
//! any other base, the exponent 1 returns the base and the exponent 0 gives
//! one, or the witness of the bases that would be lost. An integer power
//! distributes over a product, $(c \prod f)^k = c^k \prod f^k$. A sum
//! $s = c \cdot p$, with its content $c$ and its primitive part $p$, gives
//! $s^k = c^k p^k$ with $c^k$ computed strictly, so
//! $(2x + 2y)^2 = 4 (x + y)^2$ and $(1 - x)^{-1} = -(x - 1)^{-1}$; a power of
//! a sum is not expanded. A power of a power $(b^j)^k$ becomes $b^{jk}$ only
//! when $jk \lt 0$, when $j, k \ge 0$, or when $j = 0$; every integer power
//! of a witness $(b^{-1})^0$ is therefore the witness itself.

use crate::number::Rational;
use crate::{Context, Result};

use super::Term;
use super::exponent;
use super::node::{self, TermShape, first_child, is_one};
use super::product;
use super::sum;
use super::witness;

/// The canonical power `base^exponent`.
pub(super) fn power(base: &Term, exponent: i64, context: &mut Context) -> Result<Term> {
    exponent::check(exponent, context)?;
    context.charge(1)?;
    match &base.0.shape {
        TermShape::Number(value) => {
            let value = value.power(exponent, context)?;
            node::number(value, context)
        }
        TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Power(_)
        | TermShape::Product(_)
        | TermShape::Sum(_, _) => power_of_term(base, exponent, context),
    }
}

/// The power of a base that is not a number.
fn power_of_term(base: &Term, exponent: i64, context: &mut Context) -> Result<Term> {
    if exponent == 1 {
        return Ok(base.clone());
    }
    if exponent == 0 {
        return witness::power_zero(base, context);
    }
    match &base.0.shape {
        TermShape::Product(coefficient) => {
            power_of_product(coefficient, &base.0.children, exponent, context)
        }
        TermShape::Sum(_, _) => power_of_sum(base, exponent, context),
        TermShape::Number(_) | TermShape::Symbol(_) | TermShape::Call(_) | TermShape::Power(_) => {
            power_of_atom(base.clone(), exponent, context)
        }
    }
}

/// $(c \prod f)^k = c^k \prod f^k$, for $k \ne 0, 1$. The power of the
/// coefficient is strict: a zero coefficient with a negative exponent fails
/// with `DivisionByZero`. A factor that is a sum is primitive already.
fn power_of_product(
    coefficient: &Rational,
    factors: &[Term],
    exponent: i64,
    context: &mut Context,
) -> Result<Term> {
    let scaled = coefficient.power(exponent, context)?;
    let mut parts = Vec::with_capacity(factors.len());
    let mut index = 0;
    while index < factors.len() {
        context.charge(1)?;
        parts.push(power_of_atom(factors[index].clone(), exponent, context)?);
        index += 1;
    }
    product::product(scaled, &parts, context)
}

/// $s^k = c^k p^k$ for the content $c$ and the primitive part $p$ of the sum
/// $s$, for $k \ne 0, 1$: a sum whose content is 1 is its own primitive
/// part and gives the power node $s^k$; otherwise $c^k$, which is not 0, is
/// computed strictly, and the product of $c^k$ and the power node $p^k$ is
/// assembled, which is $p^k$ alone when $c^k = 1$.
fn power_of_sum(base: &Term, exponent: i64, context: &mut Context) -> Result<Term> {
    let (content, part) = sum::primitive(base, context)?;
    if is_one(&content) {
        return power_of_atom(part, exponent, context);
    }
    let scale = content.power(exponent, context)?;
    let power = power_of_atom(part, exponent, context)?;
    product::assemble(scale, vec![power], context)
}

/// The power of a base that is neither a number nor a product, for an
/// exponent that is not 0: merges $(b^j)^k$ into $b^{jk}$ as long as the
/// merge condition allows it, one unit per merge. A base that is a sum is
/// primitive.
fn power_of_atom(base: Term, exponent: i64, context: &mut Context) -> Result<Term> {
    let mut base = base;
    let mut exponent = exponent;
    while let Some((inner, merged)) = merge_step(&base, exponent, context)? {
        context.charge(1)?;
        base = inner;
        exponent = merged;
    }
    finish(base, exponent, context)
}

/// The base and exponent after merging `base^exponent` once, or `None` when
/// the base is not a power or the merge condition does not hold.
fn merge_step(base: &Term, exponent: i64, context: &Context) -> Result<Option<(Term, i64)>> {
    let inner = match &base.0.shape {
        TermShape::Power(inner) => *inner,
        TermShape::Number(_)
        | TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Product(_)
        | TermShape::Sum(_, _) => return Ok(None),
    };
    if !exponent::mergeable(inner, exponent) {
        return Ok(None);
    }
    let merged = exponent::product(inner, exponent, context)?;
    Ok(Some((first_child(base)?, merged)))
}

/// The power node of a base that is not a number or a product and does not
/// merge with the exponent.
fn finish(base: Term, exponent: i64, context: &mut Context) -> Result<Term> {
    if exponent == 1 {
        return Ok(base);
    }
    if exponent == 0 {
        return witness::power_zero(&base, context);
    }
    node::make(TermShape::Power(exponent), vec![base], context)
}
