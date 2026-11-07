//! The dispatch table of the command entry and its three operations.
//!
//! The table is the one place that names the operations: a request names
//! its operation, the table gives the operation of that name, and a `match`
//! runs it. A name that the table does not hold is an unknown operation.

use crate::coefficient::Rationals;
use crate::polynomial::PolynomialRing;
use crate::syntax::parse;
use crate::term::Term;
use crate::{Context, Error, ErrorKind, FaultKind, Result, Settled};

use super::Request;

/// An operation of the command entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CommandOperation {
    /// `eval`: the exact number of the input.
    Eval,
    /// `expand`: the polynomial of the input in the variable, as a term.
    Expand,
    /// `diff`: the derivative of that polynomial by the variable, as a term.
    Diff,
}

/// The dispatch table: each operation and its name.
pub(super) const OPERATIONS: [(&str, CommandOperation); 3] = [
    ("eval", CommandOperation::Eval),
    ("expand", CommandOperation::Expand),
    ("diff", CommandOperation::Diff),
];

/// The operation of the table named `name`, compared byte for byte; reads at
/// most the bytes of the longest name of the table, and charges nothing.
///
/// # Errors
///
/// `Fault(Unsupported)`, without a span, when no operation has that name.
pub(super) fn lookup(name: &str) -> Result<CommandOperation> {
    let mut index = 0;
    while index < OPERATIONS.len() {
        let (known, operation) = OPERATIONS[index];
        if name == known {
            return Ok(operation);
        }
        index += 1;
    }
    Err(Error::new(
        FaultKind::Unsupported,
        None,
        "unknown operation: the operations of this release are eval, expand and diff",
    ))
}

/// Runs `operation` on `request`.
pub(super) fn run(
    operation: CommandOperation,
    request: &Request,
    context: &mut Context,
) -> Result<Settled<Term>> {
    match operation {
        CommandOperation::Eval => eval(request, context),
        CommandOperation::Expand => expand(request, context),
        CommandOperation::Diff => diff(request, context),
    }
}

/// `eval`: the canonical term of the input, which must be a number. A term
/// of this release that is not a number holds a symbol, and no symbol has a
/// value in an evaluation; the variable of the request is not read.
fn eval(request: &Request, context: &mut Context) -> Result<Settled<Term>> {
    let term = parse(&request.input, context)?;
    match term.as_number() {
        Some(_) => Ok(Settled::Value(term)),
        None => Err(Error::new(
            FaultKind::UnknownSymbol,
            None,
            "eval needs a number, and the input holds a symbol, which has no value",
        )),
    }
}

/// `expand`: the polynomial of the input in the variable, converted back to
/// a term by the ring that built it.
fn expand(request: &Request, context: &mut Context) -> Result<Settled<Term>> {
    let ring = ring(&request.variable, context)?;
    let term = parse(&request.input, context)?;
    let polynomial = ring.expand(&term, context)?;
    let expanded = ring.to_term(&polynomial, context)?;
    Ok(Settled::Value(expanded))
}

/// `diff`: the derivative by the variable of the polynomial of the input, as
/// a term.
fn diff(request: &Request, context: &mut Context) -> Result<Settled<Term>> {
    let ring = ring(&request.variable, context)?;
    let term = parse(&request.input, context)?;
    let derivative = ring.differentiate(&term, context)?;
    Ok(Settled::Value(derivative))
}

/// The ring $\mathbb{Q}[x]$ of the variable `variable`. The ring checks the
/// name by the rule of symbol names before it charges; the span of such an
/// error lies in the variable, not in the input, so it is left out.
fn ring(variable: &str, context: &mut Context) -> Result<PolynomialRing> {
    match PolynomialRing::new(Rationals, variable, context) {
        Ok(ring) => Ok(ring),
        Err(error) => Err(variable_error(error)),
    }
}

/// The error of a variable that the ring rejected, without a span; a request
/// failure of the charge, which has no span, stays as it is.
fn variable_error(error: Error) -> Error {
    match error.kind() {
        ErrorKind::Fault(FaultKind::Syntax) => Error::new(
            FaultKind::Syntax,
            None,
            "the variable is not a symbol name: a letter or `_` followed by letters, digits and `_`",
        ),
        ErrorKind::Fault(FaultKind::Unsupported) => Error::new(
            FaultKind::Unsupported,
            None,
            "the variable is a name reserved for a constant of a later release",
        ),
        ErrorKind::ResourceLimit
        | ErrorKind::Cancelled
        | ErrorKind::DeadlineExceeded
        | ErrorKind::Fault(_) => error,
    }
}
