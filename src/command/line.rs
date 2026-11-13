//! The line bytes of an outcome: the only output format of the library.
//!
//! A line is a run of fields separated by tabs and ended by a line feed. The
//! first field says what the line holds, `value`, `state`, `error`,
//! `error-at` or `answer`, and the next three are the input, context and
//! settings versions of the request. A value line adds the display text of
//! its term, a state line the name of its state, an error line its kind,
//! span, limit, scope, allowed value, amount and message, and an `error-at`
//! line the same fields and the location of the error, written from its
//! cause frames. An answer line adds the kind, the text, the condition and
//! the assumptions of a value. `docs/semantics.md` states the bytes of every
//! field.
//!
//! Before it writes a line, `serialize` estimates its size from the fields
//! that it knows, every field but the display text of a value, and reserves
//! that much of the buffer of the line, at most the output that the request
//! has left. The estimate only reserves: each field is still charged with
//! `charge_output` before it is written into the line, and the display text
//! of a term charges its own pieces, so every byte of the line is charged
//! exactly once and cancellation is polled at every field. The line is
//! returned only when it is complete: a failure returns the error and no
//! bytes. The bytes depend only on the outcome, never on addresses, hashing,
//! time or the context.

use crate::{
    CauseFrame, Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, LimitScope,
    MathState, Result, Settled, Span,
};

use super::{Answer, Outcome};

/// The separator of two fields.
const TAB: &[u8] = b"\t";

/// The end of a line.
const LINE_FEED: &[u8] = b"\n";

/// The field of a part that an error or a value does not have.
const NONE: &[u8] = b"-";

/// The digits of the `\x` escape.
const HEX: &[u8; 16] = b"0123456789abcdef";

/// The line bytes of `outcome`: one line, ended by a line feed, in the
/// format of `docs/semantics.md`.
///
/// Every byte is charged to `context` with `charge_output`, which first
/// checks the request's cumulative `max_output_bytes`, then charges one work
/// unit per byte, and polls cancellation and the deadline at every field.
/// The display text of a value charges its own steps and pieces. The line is
/// returned only when every charge has succeeded, so a failure leaves no
/// partial output. The same outcome gives the same bytes in every run and
/// under every context. An error is written as an `error` line when it has
/// no cause frame or only the entry frame of the input, the operand 0, and
/// as an `error-at` line, which adds its location, otherwise.
///
/// ```
/// use kalyx::command::serialize;
/// use kalyx::context::CancelFlag;
/// use kalyx::{Context, ErrorKind, LimitField, LimitId, Limits, Request, execute};
///
/// let request = Request::new("eval", "x", "1/3 + 1/6");
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let outcome = execute(&request, &mut context);
/// assert_eq!(serialize(&outcome, &mut context)?, b"value\t0\t0\t0\t1/2\n");
///
/// let mut small = Context::new(Limits::new().with_max_output_bytes(12), CancelFlag::new());
/// let error = serialize(&outcome, &mut small).unwrap_err();
/// assert_eq!(error.kind(), ErrorKind::ResourceLimit);
/// let exceeded = error.exceeded().expect("a resource limit names its limit");
/// assert_eq!(exceeded.id(), &LimitId::Field(LimitField::OutputBytes));
///
/// // `eval` reads no role of the operand table, so the entry 1 is an
/// // unknown role, and its error line ends with its location, the index 1.
/// let request = Request::new("eval", "x", "1").with_operand("scope", "x: real");
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let outcome = execute(&request, &mut context);
/// let line = serialize(&outcome, &mut context)?;
/// assert!(line.starts_with(b"error-at\t0\t0\t0\tUnsupported\t-\t"));
/// assert!(line.ends_with(b"\t1\n"));
/// # Ok::<(), kalyx::Error>(())
/// ```
///
/// # Errors
///
/// `ResourceLimit` naming `max_output_bytes` when the line does not fit the
/// output that the request has left, or `max_work` when its charges do not
/// fit the work; `Cancelled` and `DeadlineExceeded` at a charge point; and
/// the errors of the display of a term, such as `ResourceLimit` naming
/// `max_integer_bits` for a number beyond that limit of `context`.
pub fn serialize(outcome: &Outcome, context: &mut Context) -> Result<Vec<u8>> {
    match &outcome.result {
        Ok(Settled::Value(Answer::Term(term))) => {
            let mut line = Vec::new();
            reserve(&mut line, b"value", outcome, &[Vec::new()], context);
            write_head(&mut line, b"value", outcome, context)?;
            write(&mut line, TAB, context)?;
            let text = term.display(context)?;
            // The display charged every byte of its text.
            line.extend_from_slice(text.as_bytes());
            write(&mut line, LINE_FEED, context)?;
            Ok(line)
        }
        Ok(Settled::State(state)) => {
            write_line(b"state", outcome, &[state_name(*state).to_vec()], context)
        }
        Err(error) => match location(error.frames()) {
            None => write_line(b"error", outcome, &error_fields(error), context),
            Some(location) => {
                let [kind, span, limit, scope, allowed, amount, message] = error_fields(error);
                let fields = [kind, span, limit, scope, allowed, amount, message, location];
                write_line(b"error-at", outcome, &fields, context)
            }
        },
    }
}

/// The answer line of a value of the kind `kind` with the display text
/// `text`, the condition `condition` and the assumptions `assumptions`, each
/// `-` when the value has none, after the versions of `outcome`: the line of
/// every value kind but a term. The kind is a name of the table of value
/// kinds, and the display of the kind gives the other three fields as
/// printable ASCII, so none is escaped.
///
/// # Errors
///
/// As [`serialize`], without the errors of a display.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "every answer of this release is a term, written as a value line; the unit tests reach it"
    )
)]
pub(super) fn answer_line(
    outcome: &Outcome,
    kind: &[u8],
    text: &[u8],
    condition: Option<&[u8]>,
    assumptions: Option<&[u8]>,
    context: &mut Context,
) -> Result<Vec<u8>> {
    let fields = [
        kind.to_vec(),
        text.to_vec(),
        condition.unwrap_or(NONE).to_vec(),
        assumptions.unwrap_or(NONE).to_vec(),
    ];
    write_line(b"answer", outcome, &fields, context)
}

/// The line of the first field `tag`, the versions of `outcome` and
/// `fields`, each field charged with the tab before it, then the line feed.
fn write_line(
    tag: &[u8],
    outcome: &Outcome,
    fields: &[Vec<u8>],
    context: &mut Context,
) -> Result<Vec<u8>> {
    let mut line = Vec::new();
    reserve(&mut line, tag, outcome, fields, context);
    write_head(&mut line, tag, outcome, context)?;
    let mut index = 0;
    while index < fields.len() {
        write_field(&mut line, &fields[index], context)?;
        index += 1;
    }
    write(&mut line, LINE_FEED, context)?;
    Ok(line)
}

/// Reserves the estimated size of the line of the first field `tag`, the
/// versions of `outcome` and `fields`, with their tabs and the line feed, at
/// most the output that `context` has left; charges nothing. A value line
/// gives one empty field, its tab, and the display text of its term adds to
/// the line as it is written. The reserved size never decides whether a line
/// fits: every byte is charged as it is written.
fn reserve(
    line: &mut Vec<u8>,
    tag: &[u8],
    outcome: &Outcome,
    fields: &[Vec<u8>],
    context: &Context,
) {
    // `usize` is 64 bits wide on every target of the library.
    let mut estimate = tag.len() as u64;
    let versions = [
        outcome.input_version,
        outcome.context_version,
        outcome.settings_version,
    ];
    let mut index = 0;
    while index < versions.len() {
        estimate = estimate
            .saturating_add(1)
            .saturating_add(digits(versions[index]));
        index += 1;
    }
    index = 0;
    while index < fields.len() {
        estimate = estimate
            .saturating_add(1)
            .saturating_add(fields[index].len() as u64);
        index += 1;
    }
    estimate = estimate.saturating_add(1);
    let left = context
        .limits()
        .get(LimitField::OutputBytes)
        .saturating_sub(context.output_used());
    line.reserve(estimate.min(left) as usize);
}

/// The number of decimal digits of `value`.
const fn digits(value: u64) -> u64 {
    let mut count = 1;
    let mut rest = value / 10;
    while rest > 0 {
        count += 1;
        rest /= 10;
    }
    count
}

/// Writes the first field `tag` and the three versions of `outcome`.
fn write_head(
    line: &mut Vec<u8>,
    tag: &[u8],
    outcome: &Outcome,
    context: &mut Context,
) -> Result<()> {
    write(line, tag, context)?;
    write_field(line, &decimal(outcome.input_version), context)?;
    write_field(line, &decimal(outcome.context_version), context)?;
    write_field(line, &decimal(outcome.settings_version), context)
}

/// The seven fields of `error` after the versions: its kind, span, limit,
/// scope, allowed value, amount and escaped message.
fn error_fields(error: &Error) -> [Vec<u8>; 7] {
    let kind = kind_name(error.kind()).to_vec();
    let span = span_text(error.span());
    let message = escape(error.message().as_bytes());
    match error.exceeded() {
        Some(exceeded) => [
            kind,
            span,
            limit_text(exceeded.id()),
            scope_name(exceeded.scope()).to_vec(),
            decimal(exceeded.allowed()),
            amount_text(exceeded.amount()),
            message,
        ],
        None => [
            kind,
            span,
            NONE.to_vec(),
            NONE.to_vec(),
            NONE.to_vec(),
            NONE.to_vec(),
            message,
        ],
    }
}

/// The location of an error with the cause frames `frames`, outer first:
/// the operand index of the entry frame, then `>`, the name, `#` and the
/// operand index of each nested frame. `None`, for an `error` line, when
/// the error has no frame, or only the entry frame of the operand 0.
fn location(frames: &[CauseFrame]) -> Option<Vec<u8>> {
    let (entry, nested) = frames.split_first()?;
    if nested.is_empty() && entry.operand_index() == 0 {
        return None;
    }
    let mut text = decimal(entry.operand_index());
    let mut index = 0;
    while index < nested.len() {
        let frame = &nested[index];
        text.extend_from_slice(b">");
        text.extend_from_slice(frame.name().as_bytes());
        text.extend_from_slice(b"#");
        text.extend_from_slice(&decimal(frame.operand_index()));
        index += 1;
    }
    Some(text)
}

/// Writes a tab and `field`, after charging their bytes as output.
fn write_field(line: &mut Vec<u8>, field: &[u8], context: &mut Context) -> Result<()> {
    context.charge_output((field.len() as u64).saturating_add(1))?;
    line.extend_from_slice(TAB);
    line.extend_from_slice(field);
    Ok(())
}

/// Writes `piece`, after charging its bytes as output.
fn write(line: &mut Vec<u8>, piece: &[u8], context: &mut Context) -> Result<()> {
    context.charge_output(piece.len() as u64)?;
    line.extend_from_slice(piece);
    Ok(())
}

/// The decimal digits of `value`, without a sign, leading zeros or
/// separators.
fn decimal(value: u64) -> Vec<u8> {
    value.to_string().into_bytes()
}

/// The name of the kind of an error: the request failures by their own
/// names, a fault by the name of its fault kind.
fn kind_name(kind: ErrorKind) -> &'static [u8] {
    match kind {
        ErrorKind::ResourceLimit => b"ResourceLimit",
        ErrorKind::Cancelled => b"Cancelled",
        ErrorKind::DeadlineExceeded => b"DeadlineExceeded",
        ErrorKind::Fault(fault) => fault_name(fault),
    }
}

/// The name of a fault kind.
fn fault_name(fault: FaultKind) -> &'static [u8] {
    match fault {
        FaultKind::Syntax => b"Syntax",
        FaultKind::UnknownSymbol => b"UnknownSymbol",
        FaultKind::DivisionByZero => b"DivisionByZero",
        FaultKind::NonIntegerExponent => b"NonIntegerExponent",
        FaultKind::NotPolynomial => b"NotPolynomial",
        FaultKind::Unsupported => b"Unsupported",
        FaultKind::Internal => b"Internal",
        FaultKind::OutsideDomain => b"OutsideDomain",
        FaultKind::VariableMismatch => b"VariableMismatch",
    }
}

/// The name of a mathematical state.
fn state_name(state: MathState) -> &'static [u8] {
    match state {
        MathState::NotConverged => b"NotConverged",
        MathState::Unevaluated => b"Unevaluated",
        MathState::NotApplicable => b"NotApplicable",
        MathState::Undecided => b"Undecided",
        MathState::IterationLimit => b"IterationLimit",
    }
}

/// The span as `start..end`, its byte offsets into the text of the operand
/// that the innermost cause frame names, the input for an error without a
/// location, or `-`.
fn span_text(span: Option<Span>) -> Vec<u8> {
    match span {
        Some(span) => {
            // `usize` is 64 bits wide on every target of the library.
            let mut text = decimal(span.start() as u64);
            text.extend_from_slice(b"..");
            text.extend_from_slice(&decimal(span.end() as u64));
            text
        }
        None => NONE.to_vec(),
    }
}

/// The identifier of a limit: `Field(name)` with the name of the field of
/// `Limits`, or `Parameter(name)` with the escaped name of the parameter.
fn limit_text(id: &LimitId) -> Vec<u8> {
    match id {
        LimitId::Field(field) => {
            let mut text = b"Field(".to_vec();
            text.extend_from_slice(field.name().as_bytes());
            text.extend_from_slice(b")");
            text
        }
        LimitId::Parameter(name) => {
            let mut text = b"Parameter(".to_vec();
            text.extend_from_slice(&escape(name.as_bytes()));
            text.extend_from_slice(b")");
            text
        }
    }
}

/// The scope of a limit, or `-` for a limit without one.
fn scope_name(scope: Option<LimitScope>) -> &'static [u8] {
    match scope {
        Some(LimitScope::Value) => b"Value",
        Some(LimitScope::Frame) => b"Frame",
        Some(LimitScope::Temporary) => b"Temporary",
        None => NONE,
    }
}

/// The amount of a limit: `Used(n)`, `Required(n)` or `Bound(n)`.
fn amount_text(amount: LimitAmount) -> Vec<u8> {
    let (name, value): (&[u8], u64) = match amount {
        LimitAmount::Used(value) => (b"Used(", value),
        LimitAmount::Required(value) => (b"Required(", value),
        LimitAmount::Bound(value) => (b"Bound(", value),
    };
    let mut text = name.to_vec();
    text.extend_from_slice(&decimal(value));
    text.extend_from_slice(b")");
    text
}

/// `text` with its backslashes, tabs, line feeds, carriage returns and other
/// control characters escaped: `\\`, `\t`, `\n`, `\r`, and `\xhh` with two
/// lowercase hexadecimal digits for every other byte below `0x20` and for
/// `0x7f`. Every other byte is kept, so UTF-8 text stays UTF-8.
fn escape(text: &[u8]) -> Vec<u8> {
    let mut escaped = Vec::with_capacity(text.len());
    let mut index = 0;
    while index < text.len() {
        let byte = text[index];
        match byte {
            b'\\' => escaped.extend_from_slice(b"\\\\"),
            b'\t' => escaped.extend_from_slice(b"\\t"),
            b'\n' => escaped.extend_from_slice(b"\\n"),
            b'\r' => escaped.extend_from_slice(b"\\r"),
            0x00..=0x1f | 0x7f => {
                escaped.extend_from_slice(b"\\x");
                escaped.push(HEX[(byte >> 4) as usize]);
                escaped.push(HEX[(byte & 0x0f) as usize]);
            }
            _ => escaped.push(byte),
        }
        index += 1;
    }
    escaped
}
