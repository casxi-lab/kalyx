//! The dispatch table of the command entry and its three operations.
//!
//! The table is the one place that names the operations: a request names
//! its operation, the table gives the operation of that name, and a `match`
//! runs it. A name that the table does not hold is an unknown operation.
//! Each operation has a signature, the roles of the operand table that it
//! reads; `eval`, `expand` and `diff` read the input alone.

use crate::coefficient::Rationals;
use crate::polynomial::PolynomialRing;
use crate::{Context, Error, ErrorKind, FaultKind, Result, Settled};

use super::operands::{self, Signature, Table};
use super::{Answer, Request};

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

/// The names of the nested categories: the fixed steps of the library that
/// an operation enters and that are not operations of the dispatch table. A
/// nested frame of an error takes the name of the operation that its step
/// is, or one of these names; no category name is the name of an operation.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no operation of this release enters a nested category; the unit tests reach it"
    )
)]
pub(super) const CATEGORY_NAMES: [&str; 3] =
    ["algebraic-evaluation", "complex-embedding", "membership"];

/// The most nested frames that an error of a request has, the frames after
/// its entry frame.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no operation of this release enters a nested category; the unit tests reach it"
    )
)]
pub(super) const NESTED_FRAMES: usize = 1;

/// The entry of the table named `name`, compared byte for byte: the name of
/// the table and its operation. Reads at most the bytes of the longest name
/// of the table, and charges nothing.
///
/// # Errors
///
/// `Fault(Unsupported)`, without a span, when no operation has that name.
pub(super) fn lookup(name: &str) -> Result<(&'static str, CommandOperation)> {
    let mut index = 0;
    while index < OPERATIONS.len() {
        let (known, operation) = OPERATIONS[index];
        if name == known {
            return Ok((known, operation));
        }
        index += 1;
    }
    Err(Error::new(
        FaultKind::Unsupported,
        None,
        "unknown operation: the operations of this release are eval, expand and diff",
    ))
}

/// The signature of `operation`.
pub(super) const fn signature(operation: CommandOperation) -> Signature {
    match operation {
        CommandOperation::Eval | CommandOperation::Expand | CommandOperation::Diff => {
            Signature::INPUT_ONLY
        }
    }
}

/// Runs `operation`, named `name` in the table, on `request`: steps 3 to 8
/// of the order of a request.
pub(super) fn run(
    name: &'static str,
    operation: CommandOperation,
    request: &Request,
    context: &mut Context,
) -> Result<Settled<Answer>> {
    let table = operands::check_table(name, &signature(operation), &request.operands, context)?;
    match operation {
        CommandOperation::Eval => eval(name, &table, request, context),
        CommandOperation::Expand => expand(name, &table, request, context),
        CommandOperation::Diff => diff(name, &table, request, context),
    }
}

/// `eval`: the canonical term of the input, which must be a number. A term
/// of this release that is not a number holds a symbol, and no symbol has a
/// value in an evaluation; the variable of the request is not read.
fn eval(
    name: &'static str,
    table: &Table<'_>,
    request: &Request,
    context: &mut Context,
) -> Result<Settled<Answer>> {
    let term = operands::read(name, table, request, context)?.input;
    if term.as_number().is_some() {
        Ok(Settled::Value(Answer::Term(term)))
    } else {
        Err(operands::at_operand(
            Error::new(
                FaultKind::UnknownSymbol,
                None,
                "eval needs a number, and the input holds a symbol, which has no value",
            ),
            name,
            0,
        ))
    }
}

/// `expand`: the polynomial of the input in the variable, converted back to
/// a term by the ring that built it.
fn expand(
    name: &'static str,
    table: &Table<'_>,
    request: &Request,
    context: &mut Context,
) -> Result<Settled<Answer>> {
    let ring = ring(&request.variable, context)?;
    let term = operands::read(name, table, request, context)?.input;
    let polynomial = operands::in_operand(ring.expand(&term, context), name, 0)?;
    let expanded = operands::in_operand(ring.to_term(&polynomial, context), name, 0)?;
    Ok(Settled::Value(Answer::Term(expanded)))
}

/// `diff`: the derivative by the variable of the polynomial of the input, as
/// a term.
fn diff(
    name: &'static str,
    table: &Table<'_>,
    request: &Request,
    context: &mut Context,
) -> Result<Settled<Answer>> {
    let ring = ring(&request.variable, context)?;
    let term = operands::read(name, table, request, context)?.input;
    let derivative = operands::in_operand(ring.differentiate(&term, context), name, 0)?;
    Ok(Settled::Value(Answer::Term(derivative)))
}

/// Step 5 of the order of a request: the ring $\mathbb{Q}[x]$ of the
/// variable `variable`. The ring checks the name by the rule of symbol names
/// before it charges; the span of such an error lies in the variable, not in
/// an operand, so it is left out, and the error has no frame.
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
