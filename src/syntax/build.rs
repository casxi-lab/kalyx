//! The builder: turns the syntax tree into a term through the constructors
//! of the term core.
//!
//! The nodes of the tree are in postorder, so the builder takes them in
//! order, in one loop without a stack: the terms of the operands of a node
//! are built before the node, from left to right, and each is taken once by
//! the node that holds it. Each syntax node charges one unit before the
//! builder calls the term core for it, and an error of the term core, which
//! carries no span, gets the span of the node whose term failed:
//!
//! - a number is `Term::number` of its value, and an identifier
//!   `Term::symbol` of its name;
//! - a unary minus is the negation of its operand;
//! - a chain of `+` and `-` is the canonical sum of its operands, where the
//!   operand after a `-` is negated as soon as it is built, with the span of
//!   its subtraction;
//! - a chain of `*` and `/` is the canonical product of its operands, where
//!   the operand after a `/` is raised to the power $-1$ as soon as it is
//!   built, with the span of its division, so a divisor 0 fails with
//!   `DivisionByZero` there, before the next operand is built;
//! - a power raises its base to its exponent, which must be a number that is
//!   an integer: otherwise it fails with `NonIntegerExponent`, and an integer
//!   beyond `max_exponent` or the width of `i64` with `ResourceLimit`, both
//!   with the span of the exponent and its parentheses.

use crate::term::{Term, integer_exponent};
use crate::{Context, Error, FaultKind, Result};

use super::tree::{
    SyntaxNode, SyntaxOperand, SyntaxOperator, SyntaxRange, SyntaxShape, SyntaxTree, text_at,
};

/// The work units charged for each syntax node, before the term core builds
/// its term.
const BUILD_CHARGE: u64 = 1;

/// The term of the syntax tree `tree` of `source`.
///
/// # Errors
///
/// The errors of the term core and of the charges, each with the span of the
/// syntax node whose term failed; `Fault(NonIntegerExponent)` and
/// `ResourceLimit` with `LimitField::Exponent` for an exponent that is not an
/// integer within the limits; and `Fault(Internal)` when the tree is not in
/// postorder.
pub(super) fn build(source: &str, tree: SyntaxTree, context: &mut Context) -> Result<Term> {
    let mut nodes = tree.nodes;
    nodes.reverse();
    let mut terms: Vec<Option<Term>> = Vec::with_capacity(nodes.len());
    while let Some(node) = nodes.pop() {
        let term = build_node(source, node, &mut terms, context)?;
        terms.push(Some(term));
    }
    root(terms, SyntaxRange::new(0, source.len()))
}

/// The term of the root, the last node of the tree; `whole` is the range of
/// the whole source.
fn root(mut terms: Vec<Option<Term>>, whole: SyntaxRange) -> Result<Term> {
    match terms.pop() {
        Some(Some(term)) => Ok(term),
        Some(None) | None => Err(Error::new(
            FaultKind::Internal,
            whole.span(),
            "a syntax tree without a root",
        )),
    }
}

/// The term of `node`, whose operands are built and wait in `terms`.
fn build_node(
    source: &str,
    node: SyntaxNode,
    terms: &mut [Option<Term>],
    context: &mut Context,
) -> Result<Term> {
    let range = node.range;
    match node.shape {
        SyntaxShape::Number(value) => {
            context.charge_at(BUILD_CHARGE, range.span())?;
            spanned(Term::number(value, context), range)
        }
        SyntaxShape::Symbol => {
            context.charge_at(BUILD_CHARGE, range.span())?;
            let name = text_at(source, range)?;
            spanned(Term::symbol(name, context), range)
        }
        SyntaxShape::Negate(operand) => {
            context.charge_at(BUILD_CHARGE, range.span())?;
            let operand = take(terms, operand, range)?;
            spanned(operand.negate(context), range)
        }
        SyntaxShape::Reciprocal(operand) => {
            context.charge_at(BUILD_CHARGE, range.span())?;
            let operand = take(terms, operand, range)?;
            spanned(operand.power(-1, context), range)
        }
        SyntaxShape::Power {
            base,
            exponent,
            exponent_range,
        } => power(terms, base, exponent, exponent_range, range, context),
        SyntaxShape::Sum(operands) => {
            let summands = chain_terms(&operands, terms, context)?;
            spanned(Term::sum(&summands, context), range)
        }
        SyntaxShape::Product(operands) => {
            let factors = chain_terms(&operands, terms, context)?;
            spanned(Term::product(&factors, context), range)
        }
    }
}

/// The power of the node over `range`: the term of `base` raised to the
/// term of `exponent`, which must be an integer number.
fn power(
    terms: &mut [Option<Term>],
    base: usize,
    exponent: usize,
    exponent_range: SyntaxRange,
    range: SyntaxRange,
    context: &mut Context,
) -> Result<Term> {
    context.charge_at(BUILD_CHARGE, range.span())?;
    let base = take(terms, base, range)?;
    let exponent = take(terms, exponent, range)?;
    let value = exponent_value(&exponent, exponent_range, context)?;
    spanned(base.power(value, context), range)
}

/// The integer value of the exponent term `exponent`, written at `range`.
///
/// # Errors
///
/// `Fault(NonIntegerExponent)` when the term is not a number or not an
/// integer; `ResourceLimit` with `LimitField::Exponent` when its magnitude
/// exceeds `max_exponent` or $2^{63} - 1$; both with the span of `range`.
fn exponent_value(exponent: &Term, range: SyntaxRange, context: &Context) -> Result<i64> {
    match exponent.as_number() {
        Some(value) => {
            if value.is_integer() {
                spanned(
                    integer_exponent(value.numerator(), range.span(), context),
                    range,
                )
            } else {
                Err(not_an_integer(range))
            }
        }
        None => Err(not_an_integer(range)),
    }
}

/// The fault of an exponent at `range` that is not an integer constant.
fn not_an_integer(range: SyntaxRange) -> Error {
    Error::new(
        FaultKind::NonIntegerExponent,
        range.span(),
        "an exponent is an integer constant",
    )
}

/// The terms of the operands of a chain, in order; the operand after a `-`
/// or a `/` is the term of its negation or its reciprocal, which is built.
fn chain_terms(
    operands: &[SyntaxOperand],
    terms: &mut [Option<Term>],
    context: &mut Context,
) -> Result<Vec<Term>> {
    let mut list = Vec::with_capacity(operands.len());
    let mut index = 0;
    while index < operands.len() {
        let term = chain_term(operands[index], terms, context)?;
        list.push(term);
        index += 1;
    }
    Ok(list)
}

/// The term of one operand of a chain. The syntax node of a `+` or a `*`
/// is charged here; that of a `-` or a `/` was charged with the negation or
/// the reciprocal of its operand.
fn chain_term(
    operand: SyntaxOperand,
    terms: &mut [Option<Term>],
    context: &mut Context,
) -> Result<Term> {
    let range = operand.range;
    match operand.operator {
        SyntaxOperator::Add | SyntaxOperator::Multiply => {
            context.charge_at(BUILD_CHARGE, range.span())?;
            take(terms, operand.node, range)
        }
        SyntaxOperator::Leading | SyntaxOperator::Subtract | SyntaxOperator::Divide => {
            take(terms, operand.node, range)
        }
    }
}

/// Takes the term of the node `index` out of `terms`, where it waits for the
/// one node that holds it.
fn take(terms: &mut [Option<Term>], index: usize, range: SyntaxRange) -> Result<Term> {
    let taken = match terms.get_mut(index) {
        Some(slot) => slot.take(),
        None => None,
    };
    match taken {
        Some(term) => Ok(term),
        None => Err(Error::new(
            FaultKind::Internal,
            range.span(),
            "a syntax node whose operand is not built or already taken",
        )),
    }
}

/// `result`, with the span of `range` on an error that has no span.
fn spanned<T>(result: Result<T>, range: SyntaxRange) -> Result<T> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => Err(error.with_default_span(range.span())),
    }
}
