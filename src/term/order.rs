//! The total order of terms: one loop over one stack of owned comparison
//! steps, charged per step.
//!
//! Terms are ordered by the rank of their kind first. Within a rank, numbers
//! compare by value through the charged `Rational::compare`, symbols by the
//! UTF-8 bytes of their names, calls by head name, head class, arguments one
//! by one and the number of arguments, powers by base and then exponent,
//! products by their factors one by one, the number of factors and then the
//! coefficient, and sums by their monomials one by one (core, then
//! coefficient), the number of monomials and then the constant. The
//! comparison is structural and never consults pointer identity.
//!
//! The steps hold owned terms, whose clones only increment a count, and
//! copied scalars, never borrowed references; a field inside a node, such as
//! a coefficient or a head, is read when the step that holds both nodes is
//! taken from the stack. The children of two nodes are walked by a cursor
//! step that pushes one pair at a time with the cursor of the next pair, so
//! every step does a bounded amount of work, and the pairs after the one
//! that decides are never touched.

use std::cmp::Ordering;

use crate::{Context, Result};

use super::Term;
use super::node::{CallClass, TermShape, internal};

/// A pending comparison of the total order.
enum TermOrderStep {
    /// Two terms.
    Terms(Term, Term),
    /// The coefficients of two products, or the constants of two sums.
    Coefficients(Term, Term),
    /// The coefficients of the monomials at this position of two sums.
    MonomialCoefficients(Term, Term, usize),
    /// The exponents of two powers.
    Exponents(i64, i64),
    /// The numbers of children of two nodes of one kind.
    Lengths(usize, usize),
    /// The heads of two calls.
    Heads(Term, Term),
    /// The cursor of the children of two nodes at this position: the
    /// arguments of two calls, the bases of two powers or the factors of two
    /// products.
    Children(Term, Term, usize),
    /// The cursor of the monomials of two sums at this position.
    Monomials(Term, Term, usize),
}

/// The order of `left` and `right`, charging one unit per step, and for two
/// names one more per byte of the shorter name.
pub(super) fn compare(left: &Term, right: &Term, context: &mut Context) -> Result<Ordering> {
    let mut stack = Vec::new();
    stack.push(TermOrderStep::Terms(left.clone(), right.clone()));
    while let Some(step) = stack.pop() {
        context.charge(1)?;
        let order = order_step(step, &mut stack, context)?;
        match order {
            Ordering::Equal => {}
            Ordering::Less | Ordering::Greater => return Ok(order),
        }
    }
    Ok(Ordering::Equal)
}

/// Takes one step: decides it, or pushes the steps that decide it.
fn order_step(
    step: TermOrderStep,
    stack: &mut Vec<TermOrderStep>,
    context: &mut Context,
) -> Result<Ordering> {
    match step {
        TermOrderStep::Terms(left, right) => order_terms(&left, &right, stack, context),
        TermOrderStep::Coefficients(left, right) => order_coefficients(&left, &right, context),
        TermOrderStep::MonomialCoefficients(left, right, index) => {
            order_monomial_coefficients(&left, &right, index, context)
        }
        TermOrderStep::Exponents(left, right) => Ok(order_integers(left, right)),
        TermOrderStep::Lengths(left, right) => Ok(order_lengths(left, right)),
        TermOrderStep::Heads(left, right) => order_heads(&left, &right, context),
        TermOrderStep::Children(left, right, index) => {
            next_children(stack, left, right, index);
            Ok(Ordering::Equal)
        }
        TermOrderStep::Monomials(left, right, index) => {
            next_monomials(stack, left, right, index);
            Ok(Ordering::Equal)
        }
    }
}

/// Compares the ranks of two terms, then their own data, and pushes the
/// steps that compare the rest, with the cursor of their children at the
/// first position.
fn order_terms(
    left: &Term,
    right: &Term,
    stack: &mut Vec<TermOrderStep>,
    context: &mut Context,
) -> Result<Ordering> {
    let by_rank = order_integers(rank(left) as i64, rank(right) as i64);
    if by_rank != Ordering::Equal {
        return Ok(by_rank);
    }
    let (lefts, rights) = (&left.0.children, &right.0.children);
    match (&left.0.shape, &right.0.shape) {
        (TermShape::Number(a), TermShape::Number(b)) => a.compare(b, context),
        (TermShape::Symbol(a), TermShape::Symbol(b)) => order_names(a, b, context),
        (TermShape::Call(_), TermShape::Call(_)) => {
            stack.push(TermOrderStep::Lengths(lefts.len(), rights.len()));
            stack.push(TermOrderStep::Children(left.clone(), right.clone(), 0));
            stack.push(TermOrderStep::Heads(left.clone(), right.clone()));
            Ok(Ordering::Equal)
        }
        (TermShape::Power(j), TermShape::Power(k)) => {
            stack.push(TermOrderStep::Exponents(*j, *k));
            stack.push(TermOrderStep::Children(left.clone(), right.clone(), 0));
            Ok(Ordering::Equal)
        }
        (TermShape::Product(_), TermShape::Product(_)) => {
            stack.push(TermOrderStep::Coefficients(left.clone(), right.clone()));
            stack.push(TermOrderStep::Lengths(lefts.len(), rights.len()));
            stack.push(TermOrderStep::Children(left.clone(), right.clone(), 0));
            Ok(Ordering::Equal)
        }
        (TermShape::Sum(_, _), TermShape::Sum(_, _)) => {
            stack.push(TermOrderStep::Coefficients(left.clone(), right.clone()));
            stack.push(TermOrderStep::Lengths(lefts.len(), rights.len()));
            stack.push(TermOrderStep::Monomials(left.clone(), right.clone(), 0));
            Ok(Ordering::Equal)
        }
        _ => Err(internal("two terms of one rank have different kinds")),
    }
}

/// The rank of the kind of `term`.
pub(super) fn rank(term: &Term) -> u8 {
    match &term.0.shape {
        TermShape::Number(_) => 0,
        TermShape::Symbol(_) => 2,
        TermShape::Call(_) => 3,
        TermShape::Power(_) => 4,
        TermShape::Product(_) => 5,
        TermShape::Sum(_, _) => 6,
    }
}

/// Takes the cursor of the children of `left` and `right` at `index`: past
/// the common positions of the two child lists it pushes nothing, and
/// otherwise the cursor of the next position and then the pair of children
/// at `index`, which is compared first.
fn next_children(stack: &mut Vec<TermOrderStep>, left: Term, right: Term, index: usize) {
    let (lefts, rights) = (&left.0.children, &right.0.children);
    if index >= shorter(lefts.len(), rights.len()) {
        return;
    }
    let pair = TermOrderStep::Terms(lefts[index].clone(), rights[index].clone());
    stack.push(TermOrderStep::Children(left, right, index + 1));
    stack.push(pair);
}

/// Takes the cursor of the monomials of the sums `left` and `right` at
/// `index`: past the common positions it pushes nothing, and otherwise the
/// cursor of the next position, the coefficients of the monomials at
/// `index` and their cores, so that the core is compared before the
/// coefficient.
fn next_monomials(stack: &mut Vec<TermOrderStep>, left: Term, right: Term, index: usize) {
    let (lefts, rights) = (&left.0.children, &right.0.children);
    if index >= shorter(lefts.len(), rights.len()) {
        return;
    }
    let cores = TermOrderStep::Terms(lefts[index].clone(), rights[index].clone());
    let coefficients = TermOrderStep::MonomialCoefficients(left.clone(), right.clone(), index);
    stack.push(TermOrderStep::Monomials(left, right, index + 1));
    stack.push(coefficients);
    stack.push(cores);
}

/// The coefficients of two products or the constants of two sums, by value.
fn order_coefficients(left: &Term, right: &Term, context: &mut Context) -> Result<Ordering> {
    match (&left.0.shape, &right.0.shape) {
        (TermShape::Product(a), TermShape::Product(b)) => a.compare(b, context),
        (TermShape::Sum(a, _), TermShape::Sum(b, _)) => a.compare(b, context),
        _ => Err(internal(
            "coefficients of terms that are not products or sums",
        )),
    }
}

/// The coefficients of the monomials at `index` of two sums, by value.
fn order_monomial_coefficients(
    left: &Term,
    right: &Term,
    index: usize,
    context: &mut Context,
) -> Result<Ordering> {
    match (&left.0.shape, &right.0.shape) {
        (TermShape::Sum(_, lefts), TermShape::Sum(_, rights)) => {
            match (lefts.get(index), rights.get(index)) {
                (Some(a), Some(b)) => a.compare(b, context),
                _ => Err(internal("a monomial without a coefficient")),
            }
        }
        _ => Err(internal("monomials of terms that are not sums")),
    }
}

/// The heads of two calls: the bytes of their names, then their classes.
fn order_heads(left: &Term, right: &Term, context: &mut Context) -> Result<Ordering> {
    match (&left.0.shape, &right.0.shape) {
        (TermShape::Call(a), TermShape::Call(b)) => {
            let by_name = order_names(&a.name, &b.name, context)?;
            if by_name != Ordering::Equal {
                return Ok(by_name);
            }
            Ok(order_integers(
                class_rank(a.class) as i64,
                class_rank(b.class) as i64,
            ))
        }
        _ => Err(internal("heads of terms that are not calls")),
    }
}

/// The position of a call class in the order: `Registered` first.
const fn class_rank(class: CallClass) -> u8 {
    match class {
        CallClass::Registered => 0,
        CallClass::Formal => 1,
    }
}

/// Two names by their UTF-8 bytes, charging one unit per byte of the
/// shorter name.
fn order_names(left: &str, right: &str, context: &mut Context) -> Result<Ordering> {
    let (left, right) = (left.as_bytes(), right.as_bytes());
    let common = shorter(left.len(), right.len());
    if common > 0 {
        context.charge(common as u64)?;
    }
    Ok(order_bytes(left, right))
}

/// Two byte strings in lexicographic order.
fn order_bytes(left: &[u8], right: &[u8]) -> Ordering {
    let mut index = 0;
    while index < left.len() && index < right.len() {
        if left[index] != right[index] {
            return order_integers(left[index] as i64, right[index] as i64);
        }
        index += 1;
    }
    order_lengths(left.len(), right.len())
}

/// The order of two integers.
const fn order_integers(left: i64, right: i64) -> Ordering {
    if left < right {
        Ordering::Less
    } else if left > right {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// The order of two lengths.
const fn order_lengths(left: usize, right: usize) -> Ordering {
    if left < right {
        Ordering::Less
    } else if left > right {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// The smaller of two lengths.
const fn shorter(left: usize, right: usize) -> usize {
    if left < right { left } else { right }
}
