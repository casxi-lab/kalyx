//! The display text of terms: deterministic, byte-stable, charged, and
//! written from one loop over one stack of owned steps.
//!
//! The grammar, with minimal parentheses, is stated in the contract of the
//! term core:
//!
//! - a number is its decimal integer or fraction, `-3/4`;
//! - a symbol is its name;
//! - a power is its base, `^` and its exponent, as `x^2` or `x^(-1)`, with
//!   the base in parentheses unless it is a symbol or a call;
//! - a product is its factors in their stored order, joined by `*`, each sum
//!   among them in parentheses, after the prefix of its coefficient: nothing
//!   for 1, `-` for -1, and the number and `*` otherwise;
//! - a sum is its constant when that is not 0, then its monomials in their
//!   stored order, each after ` + `, or ` - ` and the magnitude of a negative
//!   coefficient; a first monomial takes no separator, only `-` when its
//!   coefficient is negative; a coefficient whose magnitude is not 1 is
//!   written before its core with `*`; a core is never a sum, so it needs no
//!   parentheses;
//! - a call, reserved, is its name and its arguments in parentheses, joined
//!   by `, `.
//!
//! Each step charges one unit, and each piece of text charges its bytes with
//! `charge_output` before it is written, so a failure leaves no output: the
//! text is returned only when the whole term was written.

use crate::number::Rational;
use crate::{Context, LimitField, Result};

use super::Term;
use super::exponent;
use super::node::{TermShape, internal, is_minus_one, is_one, is_sum, rational_bits};

/// A pending step of the display.
enum TermDisplayStep {
    /// A term, in parentheses when the flag is set.
    Term(Term, bool),
    /// A fixed piece of text.
    Token(TermDisplayToken),
    /// The exponent of a power, with its `^`.
    Exponent(i64),
    /// The separator, the coefficient and the core of the monomial at this
    /// position of a sum.
    Monomial(Term, usize),
}

/// A fixed piece of text.
#[derive(Clone, Copy)]
enum TermDisplayToken {
    /// `)`.
    Close,
    /// `*`, between two factors.
    Times,
    /// `, `, between two arguments.
    Comma,
}

/// The display text of `term`.
pub(super) fn display(term: &Term, context: &mut Context) -> Result<String> {
    let mut text = String::new();
    let mut stack = Vec::new();
    stack.push(TermDisplayStep::Term(term.clone(), false));
    while let Some(step) = stack.pop() {
        context.charge(1)?;
        display_step(step, &mut stack, &mut text, context)?;
    }
    Ok(text)
}

/// Takes one step: writes its text, or pushes the steps that write it.
fn display_step(
    step: TermDisplayStep,
    stack: &mut Vec<TermDisplayStep>,
    text: &mut String,
    context: &mut Context,
) -> Result<()> {
    match step {
        TermDisplayStep::Term(term, parenthesized) => {
            if parenthesized {
                write(text, "(", context)?;
                stack.push(TermDisplayStep::Token(TermDisplayToken::Close));
            }
            display_term(&term, stack, text, context)
        }
        TermDisplayStep::Token(token) => write_token(text, token, context),
        TermDisplayStep::Exponent(exponent) => write(text, &exponent_text(exponent), context),
        TermDisplayStep::Monomial(sum, index) => {
            display_monomial(&sum, index, stack, text, context)
        }
    }
}

/// Writes a fixed piece of text.
fn write_token(text: &mut String, token: TermDisplayToken, context: &mut Context) -> Result<()> {
    match token {
        TermDisplayToken::Close => write(text, ")", context),
        TermDisplayToken::Times => write(text, "*", context),
        TermDisplayToken::Comma => write(text, ", ", context),
    }
}

/// Writes the text of one node and pushes the steps of its children.
fn display_term(
    term: &Term,
    stack: &mut Vec<TermDisplayStep>,
    text: &mut String,
    context: &mut Context,
) -> Result<()> {
    match &term.0.shape {
        TermShape::Number(value) => write(text, &number_text(value, context)?, context),
        TermShape::Symbol(name) => write(text, name, context),
        TermShape::Call(head) => {
            write(text, &head.name, context)?;
            write(text, "(", context)?;
            stack.push(TermDisplayStep::Token(TermDisplayToken::Close));
            push_joined(stack, &term.0.children, TermDisplayToken::Comma);
            Ok(())
        }
        TermShape::Power(exponent) => {
            let base = match term.0.children.first() {
                Some(base) => base,
                None => return Err(internal("a power without a base")),
            };
            stack.push(TermDisplayStep::Exponent(*exponent));
            stack.push(TermDisplayStep::Term(base.clone(), !is_atom(base)));
            Ok(())
        }
        TermShape::Product(coefficient) => {
            let prefix = coefficient_prefix(coefficient, context)?;
            write(text, &prefix, context)?;
            push_joined(stack, &term.0.children, TermDisplayToken::Times);
            Ok(())
        }
        TermShape::Sum(constant, _) => {
            if !constant.is_zero() {
                write(text, &number_text(constant, context)?, context)?;
            }
            push_monomials(stack, term);
            Ok(())
        }
    }
}

/// Writes the separator and the coefficient of the monomial at `index` of
/// `sum`, and pushes its core, which is never a sum.
fn display_monomial(
    sum: &Term,
    index: usize,
    stack: &mut Vec<TermDisplayStep>,
    text: &mut String,
    context: &mut Context,
) -> Result<()> {
    let (constant, coefficients) = match &sum.0.shape {
        TermShape::Sum(constant, coefficients) => (constant, coefficients),
        TermShape::Number(_)
        | TermShape::Symbol(_)
        | TermShape::Call(_)
        | TermShape::Power(_)
        | TermShape::Product(_) => return Err(internal("a monomial of a term that is not a sum")),
    };
    let (coefficient, core) = match (coefficients.get(index), sum.0.children.get(index)) {
        (Some(coefficient), Some(core)) => (coefficient, core),
        _ => return Err(internal("a monomial without a coefficient")),
    };
    let first = index == 0 && constant.is_zero();
    let mut piece = String::new();
    push_separator(&mut piece, first, coefficient.is_negative());
    if !is_one(coefficient) && !is_minus_one(coefficient) {
        let magnitude = number_text(coefficient, context)?;
        piece.push_str(without_sign(&magnitude));
        piece.push('*');
    }
    write(text, &piece, context)?;
    stack.push(TermDisplayStep::Term(core.clone(), false));
    Ok(())
}

/// Appends the separator before a monomial: nothing or `-` for the first
/// monomial, ` + ` or ` - ` for the others.
fn push_separator(piece: &mut String, first: bool, negative: bool) {
    if first {
        if negative {
            piece.push('-');
        }
    } else if negative {
        piece.push_str(" - ");
    } else {
        piece.push_str(" + ");
    }
}

/// `text` without a leading `-`.
fn without_sign(text: &str) -> &str {
    match text.strip_prefix('-') {
        Some(rest) => rest,
        None => text,
    }
}

/// The prefix of a product: nothing for the coefficient 1, `-` for -1, and
/// the number and `*` otherwise.
fn coefficient_prefix(coefficient: &Rational, context: &Context) -> Result<String> {
    if is_one(coefficient) {
        return Ok(String::new());
    }
    if is_minus_one(coefficient) {
        return Ok(String::from("-"));
    }
    let mut prefix = number_text(coefficient, context)?;
    prefix.push('*');
    Ok(prefix)
}

/// The decimal text of a number, after checking its bits against
/// `max_integer_bits` of the receiving context, which bounds the work of
/// the conversion.
fn number_text(value: &Rational, context: &Context) -> Result<String> {
    context.check(LimitField::IntegerBits, rational_bits(value))?;
    Ok(value.to_string())
}

/// The text of an exponent with its `^`: `^k`, or `^(-k)` for a negative
/// exponent.
fn exponent_text(exponent: i64) -> String {
    let magnitude = exponent::magnitude(exponent).to_string();
    let mut text = String::from("^");
    if exponent < 0 {
        text.push_str("(-");
        text.push_str(&magnitude);
        text.push(')');
    } else {
        text.push_str(&magnitude);
    }
    text
}

/// Pushes `terms`, so that they are written in order, with `token` between
/// two of them. Between factors, a sum is in parentheses; between
/// arguments, nothing is.
fn push_joined(stack: &mut Vec<TermDisplayStep>, terms: &[Term], token: TermDisplayToken) {
    let factors = matches!(token, TermDisplayToken::Times);
    let mut index = terms.len();
    while index > 0 {
        index -= 1;
        let term = &terms[index];
        stack.push(TermDisplayStep::Term(term.clone(), factors && is_sum(term)));
        if index > 0 {
            stack.push(TermDisplayStep::Token(token));
        }
    }
}

/// Pushes the monomials of `sum`, so that they are written in order.
fn push_monomials(stack: &mut Vec<TermDisplayStep>, sum: &Term) {
    let mut index = sum.0.children.len();
    while index > 0 {
        index -= 1;
        stack.push(TermDisplayStep::Monomial(sum.clone(), index));
    }
}

/// Writes `piece`, after charging its bytes as output.
fn write(text: &mut String, piece: &str, context: &mut Context) -> Result<()> {
    if piece.is_empty() {
        return Ok(());
    }
    context.charge_output(piece.len() as u64)?;
    text.push_str(piece);
    Ok(())
}

/// Whether `term` is written without parentheses as the base of a power: a
/// symbol or a call.
fn is_atom(term: &Term) -> bool {
    matches!(term.0.shape, TermShape::Symbol(_) | TermShape::Call(_))
}
