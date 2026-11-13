//! The operand table of a request: its check against the signature of the
//! operation, the byte sum of its text operands and the reading of its
//! operands.
//!
//! The operand index 0 is the input of a request, and an index $k \ge 1$ is
//! the entry `operands[k-1]` of its table. A signature lists the roles of the
//! table that an operation reads, in its order, each required, optional or
//! repeatable; every signature reads the input first. This release has one
//! start symbol, `input`, so every operand is read by `parse` and a
//! signature does not name its start symbol. The operations of this release
//! read no role of the table, so only the unit tests build a signature with
//! roles.

use crate::context::Context;
use crate::syntax::parse;
use crate::term::Term;
use crate::{CauseFrame, Error, FaultKind, LimitField, Result};

use super::{Operand, Request};

/// How often a role of a signature may appear in the operand table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Presence {
    /// Exactly once.
    Required,
    /// At most once; the operation applies the default that its signature
    /// states when the table does not hold the role.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "no operation of this release reads a role of the table; the unit tests reach it"
        )
    )]
    Optional,
    /// Any number of times, in the order of the table.
    Repeatable,
}

/// A role of the operand table that a signature reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Role {
    /// The name of the role, a name of the library of the form
    /// `[a-z][a-z0-9_]*`.
    pub(super) name: &'static str,
    /// How often the role may appear.
    pub(super) presence: Presence,
}

/// The signature of an operation: the roles of the operand table that it
/// reads, in their order. The input, the operand 0, comes before them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Signature {
    /// The roles of the table, in the order of the signature.
    pub(super) roles: &'static [Role],
}

impl Signature {
    /// The signature that reads the input alone and no role of the table,
    /// the signature of `eval`, `expand` and `diff`.
    pub(super) const INPUT_ONLY: Self = Self { roles: &[] };
}

/// An entry of the operand table that a role of the signature took: its
/// operand index and its text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Entry<'a> {
    /// The operand index of the entry, at least 1.
    pub(super) index: u64,
    /// The text of the entry.
    pub(super) text: &'a str,
}

/// The operand table of a request after its check: for each role of the
/// signature, in its order, the entries that took it, in the order of the
/// table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Table<'a> {
    /// The entries of each role of the signature.
    pub(super) roles: Vec<Vec<Entry<'a>>>,
}

/// The operands of a request after they are read: the term of the input and,
/// for each role of the signature, the terms of its entries in the order of
/// the table. An optional role that the table does not hold has no term, and
/// the operation applies its default.
#[derive(Clone, Debug)]
pub(super) struct Operands {
    /// The term of the input, the operand 0.
    pub(super) input: Term,
    /// The terms of each role of the signature.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "no operation of this release reads a role of the table; the unit tests reach it"
        )
    )]
    pub(super) roles: Vec<Vec<Term>>,
}

/// The error `error` with the entry frame of the operation `name` at the
/// operand `index` as its outermost cause frame.
pub(super) fn at_operand(error: Error, name: &'static str, index: u64) -> Error {
    error.with_outer_frame(CauseFrame::new(name, index))
}

/// The result `result` of a step at the operand `index` of the operation
/// `name`, with the entry frame on its error.
pub(super) fn in_operand<T>(result: Result<T>, name: &'static str, index: u64) -> Result<T> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => Err(at_operand(error, name, index)),
    }
}

/// Steps 3 and 4 of the order of a request: checks the operand table
/// `operands` of the operation `name` against `signature`.
///
/// Step 3 takes the entries in the order of the table: each first charges
/// one work unit, then its role is looked up in the signature, compared byte
/// for byte, so the comparison reads at most the bytes of the longest role
/// of the signature. Step 4 takes the required roles of the signature in its
/// order: each first charges one work unit, then the table must hold it. An
/// empty table with a signature without required roles charges nothing.
///
/// # Errors
///
/// At step 3, with the entry frame of the entry and without a span:
/// `Fault(Unsupported)` for a role that the signature does not read, and
/// `Fault(Syntax)` for the second entry of a role that is not repeatable;
/// the request failures of the charge carry that frame as well. At step 4,
/// without a frame and without a span: `Fault(Syntax)` for a required role
/// that the table does not hold, whose message names the role of the
/// signature, and the request failures of the charge.
pub(super) fn check_table<'a>(
    name: &'static str,
    signature: &Signature,
    operands: &'a [Operand],
    context: &mut Context,
) -> Result<Table<'a>> {
    let mut roles = Vec::with_capacity(signature.roles.len());
    let mut position = 0;
    while position < signature.roles.len() {
        roles.push(Vec::new());
        position += 1;
    }
    let mut entry = 0;
    while entry < operands.len() {
        let operand = &operands[entry];
        // `usize` is 64 bits wide on every target of the library.
        let index = (entry as u64).saturating_add(1);
        in_operand(context.charge(1), name, index)?;
        let Some(role) = find_role(signature, &operand.role) else {
            return Err(at_operand(
                Error::new(
                    FaultKind::Unsupported,
                    None,
                    "unknown role: the operation reads no operand of this role",
                ),
                name,
                index,
            ));
        };
        let taken = &mut roles[role];
        if signature.roles[role].presence != Presence::Repeatable && !taken.is_empty() {
            return Err(at_operand(
                Error::new(
                    FaultKind::Syntax,
                    None,
                    "a second operand of a role that the operation reads at most once",
                ),
                name,
                index,
            ));
        }
        taken.push(Entry {
            index,
            text: &operand.text,
        });
        entry += 1;
    }
    let mut required = 0;
    while required < signature.roles.len() {
        let role = signature.roles[required];
        if role.presence == Presence::Required {
            context.charge(1)?;
            if roles[required].is_empty() {
                let mut message = String::from("missing operand: the operation requires the role ");
                message.push_str(role.name);
                return Err(Error::new(FaultKind::Syntax, None, message));
            }
        }
        required += 1;
    }
    Ok(Table { roles })
}

/// The position in `signature` of the role named `role`, compared byte for
/// byte.
fn find_role(signature: &Signature, role: &str) -> Option<usize> {
    let mut position = 0;
    while position < signature.roles.len() {
        if signature.roles[position].name == role {
            return Some(position);
        }
        position += 1;
    }
    None
}

/// Step 6 of the order of a request: with a nonempty operand table, checks
/// the byte sum of every text operand of `request`, its input and each entry
/// of the table, against `max_input_bytes`; not a charge point. An empty
/// table leaves the check of the input to the parser, as `parse` checks every
/// source text before it reads it.
///
/// # Errors
///
/// `ResourceLimit` naming `max_input_bytes`, without a span and without a
/// frame, with `Required` of the byte sum, or `Bound(u64::MAX)` when the sum
/// does not fit in a `u64`, which exceeds every value of the limit.
pub(super) fn check_input_bytes(request: &Request, context: &Context) -> Result<()> {
    if request.operands.is_empty() {
        return Ok(());
    }
    let mut lengths = Vec::with_capacity(request.operands.len().saturating_add(1));
    // `usize` is 64 bits wide on every target of the library.
    lengths.push(request.input.len() as u64);
    let mut entry = 0;
    while entry < request.operands.len() {
        lengths.push(request.operands[entry].text.len() as u64);
        entry += 1;
    }
    check_byte_sum(&lengths, context)
}

/// Checks the sum of the byte lengths `lengths` against `max_input_bytes`,
/// adding them with checked addition; charges nothing.
///
/// # Errors
///
/// As [`check_input_bytes`].
pub(super) fn check_byte_sum(lengths: &[u64], context: &Context) -> Result<()> {
    context.check_bound_at(LimitField::InputBytes, byte_sum(lengths), None)
}

/// The sum of `lengths` by checked addition, or `None` when it does not fit
/// in a `u64`.
fn byte_sum(lengths: &[u64]) -> Option<u64> {
    let mut sum: u64 = 0;
    let mut position = 0;
    while position < lengths.len() {
        sum = sum.checked_add(lengths[position])?;
        position += 1;
    }
    Some(sum)
}

/// Steps 6 and 7 of the order of a request: checks the byte sum of the text
/// operands of `request`, then reads its operands in the order of the
/// signature that gave `table`: the input, then the entries of each role, a
/// repeatable role in the order of the table.
///
/// # Errors
///
/// The error of the byte sum, and the errors of `parse` for an operand, each
/// with the entry frame of the operation `name` at the index of the operand
/// and with its span into the text of that operand.
pub(super) fn read(
    name: &'static str,
    table: &Table<'_>,
    request: &Request,
    context: &mut Context,
) -> Result<Operands> {
    check_input_bytes(request, context)?;
    let input = in_operand(parse(&request.input, context), name, 0)?;
    let mut roles = Vec::with_capacity(table.roles.len());
    let mut role = 0;
    while role < table.roles.len() {
        let entries = &table.roles[role];
        let mut terms = Vec::with_capacity(entries.len());
        let mut entry = 0;
        while entry < entries.len() {
            let Entry { index, text } = entries[entry];
            terms.push(in_operand(parse(text, context), name, index)?);
            entry += 1;
        }
        roles.push(terms);
        role += 1;
    }
    Ok(Operands { input, roles })
}
