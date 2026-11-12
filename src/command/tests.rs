//! Unit tests of the command entry for what code outside the library cannot
//! build: the dispatch table, the rejection of settings other than the
//! default, and the lines of a state, of a request parameter and of
//! messages that need escaping. Errors are compared by kind, span and
//! exceeded limit, never by message.

use crate::context::CancelFlag;
use crate::term::Term;
use crate::{
    Context, Error, ErrorKind, FaultKind, LimitAmount, LimitExceeded, LimitField, LimitId,
    LimitScope, Limits, MathState, Result, Settled, Span,
};

use super::dispatch::{CommandOperation, OPERATIONS, lookup};
use super::{Outcome, check_default, serialize};

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

/// An outcome with the versions 1, 2 and 3 and the result `result`.
fn outcome(result: Result<Settled<Term>>) -> Outcome {
    Outcome {
        input_version: 1,
        context_version: 2,
        settings_version: 3,
        result,
    }
}

/// The line of `outcome` under the default limits, with the output that it
/// charged.
fn line(outcome: &Outcome) -> (String, u64) {
    let c = &mut context(Limits::new());
    let bytes = serialize(outcome, c).unwrap();
    assert_eq!(
        c.output_used(),
        bytes.len() as u64,
        "every byte is charged once"
    );
    (String::from_utf8(bytes).unwrap(), c.output_used())
}

// The dispatch table holds the three operations of this release, each once,
// and a lookup finds each by its name, byte for byte, and nothing else.
#[test]
fn the_dispatch_table_holds_eval_expand_and_diff() {
    assert_eq!(
        OPERATIONS,
        [
            ("eval", CommandOperation::Eval),
            ("expand", CommandOperation::Expand),
            ("diff", CommandOperation::Diff),
        ]
    );
    for (name, operation) in OPERATIONS {
        assert_eq!(lookup(name).unwrap(), operation);
    }
    for name in ["", "Eval", "eval ", " eval", "evaluate", "simplify", "dif"] {
        let error = lookup(name).unwrap_err();
        assert_eq!(
            error.kind(),
            ErrorKind::Fault(FaultKind::Unsupported),
            "{name:?}"
        );
        assert_eq!(error.span(), None);
    }
}

/// A settings record with one setting, standing in for a later release: its
/// default is `0`.
#[derive(Debug, Default, PartialEq)]
struct LaterSettings {
    precision: u32,
}

// Settings other than the default are unsupported. The settings of this
// release have no field, so their only value is the default, which the
// check accepts; the same check rejects a record with a setting other than
// its default and accepts that record at its default.
#[test]
fn a_settings_record_other_than_its_default_is_unsupported() {
    check_default(&super::Settings::new()).unwrap();
    check_default(&LaterSettings::default()).unwrap();
    let error = check_default(&LaterSettings { precision: 53 }).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    assert_eq!(error.span(), None);
    assert!(error.exceeded().is_none());
}

// A state is written as a state line with the name of the state, after the
// versions.
#[test]
fn a_state_is_written_as_a_state_line() {
    for (state, name) in [
        (MathState::NotConverged, "NotConverged"),
        (MathState::Unevaluated, "Unevaluated"),
        (MathState::NotApplicable, "NotApplicable"),
        (MathState::Undecided, "Undecided"),
        (MathState::IterationLimit, "IterationLimit"),
    ] {
        let (text, _) = line(&outcome(Ok(Settled::State(state))));
        assert_eq!(text, format!("state\t1\t2\t3\t{name}\n"));
    }
}

// A limit of a request parameter is written as `Parameter(name)`, with the
// name escaped, no scope, the allowed value and the amount.
#[test]
fn a_parameter_limit_is_written_with_its_escaped_name() {
    let c = context(Limits::new());
    let error = c.check_parameter("max_terms", 3, 4).unwrap_err();
    let (text, _) = line(&outcome(Err(error.clone())));
    assert_eq!(
        text,
        format!(
            "error\t1\t2\t3\tResourceLimit\t-\tParameter(max_terms)\t-\t3\tRequired(4)\t{}\n",
            error.message()
        )
    );
    let odd = c
        .check_parameter("a\tb\nc\\d\re\u{1}\u{7f}é", 0, 1)
        .unwrap_err();
    let (text, _) = line(&outcome(Err(odd.clone())));
    let fields: Vec<&str> = text.trim_end_matches('\n').split('\t').collect();
    assert_eq!(fields.len(), 11, "{text:?}");
    assert_eq!(fields[6], "Parameter(a\\tb\\nc\\\\d\\re\\x01\\x7fé)");
    assert_eq!(fields[10], reference_escape(odd.message()));
}

/// The escaping of the format, written here: a backslash, a tab, a line
/// feed and a carriage return by their letters, every other control
/// character as `\xhh`.
fn reference_escape(text: &str) -> String {
    let mut escaped = String::new();
    for character in text.chars() {
        match character {
            '\\' => escaped.push_str("\\\\"),
            '\t' => escaped.push_str("\\t"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\u{0}'..='\u{1f}' | '\u{7f}' => {
                escaped.push_str(&format!("\\x{:02x}", u32::from(character)));
            }
            other => escaped.push(other),
        }
    }
    escaped
}

// A message is written with its backslashes, tabs, line feeds, carriage
// returns and other control characters escaped, so that the line keeps its
// fields; other text, UTF-8 included, is kept.
#[test]
fn messages_are_escaped() {
    let error = Error::new(
        FaultKind::Internal,
        Span::new(2, 5),
        "one\ttwo\nthree\\four\r\u{0}\u{1b}\u{7f} λ ok",
    );
    let (text, output) = line(&outcome(Err(error)));
    assert_eq!(
        text,
        "error\t1\t2\t3\tInternal\t2..5\t-\t-\t-\t-\tone\\ttwo\\nthree\\\\four\\r\\x00\\x1b\\x7f λ ok\n"
    );
    assert_eq!(output, text.len() as u64);
}

// Every kind of error has its name: the request failures by their own
// names, a fault by the name of its kind.
#[test]
fn every_kind_has_its_name() {
    for (fault, name) in [
        (FaultKind::Syntax, "Syntax"),
        (FaultKind::UnknownSymbol, "UnknownSymbol"),
        (FaultKind::DivisionByZero, "DivisionByZero"),
        (FaultKind::NonIntegerExponent, "NonIntegerExponent"),
        (FaultKind::NotPolynomial, "NotPolynomial"),
        (FaultKind::Unsupported, "Unsupported"),
        (FaultKind::Internal, "Internal"),
        (FaultKind::OutsideDomain, "OutsideDomain"),
    ] {
        let (text, _) = line(&outcome(Err(Error::new(fault, None, "fault"))));
        assert_eq!(
            text,
            format!("error\t1\t2\t3\t{name}\t-\t-\t-\t-\t-\tfault\n")
        );
    }
    let c = &mut context(Limits::new());
    let flag = CancelFlag::new();
    let mut cancelled = Context::new(Limits::new(), flag.clone());
    flag.cancel();
    let mut expired = context(Limits::new()).with_timeout(0);
    for (error, name) in [
        (c.charge(u64::MAX).unwrap_err(), "ResourceLimit"),
        (cancelled.charge(1).unwrap_err(), "Cancelled"),
        (expired.charge(1).unwrap_err(), "DeadlineExceeded"),
    ] {
        let (text, _) = line(&outcome(Err(error)));
        let fields: Vec<&str> = text.split('\t').collect();
        assert_eq!(fields[4], name, "{text:?}");
    }
}

// The identifier, the scope, the allowed value and the amount of a limit are
// written by their names: every field of `Limits`, every scope and every
// kind of amount, with the span of the error when it has one.
#[test]
fn every_limit_field_scope_and_amount_has_its_text() {
    for (field, name) in [
        (LimitField::Work, "max_work"),
        (LimitField::InputBytes, "max_input_bytes"),
        (LimitField::OutputBytes, "max_output_bytes"),
        (LimitField::Depth, "max_depth"),
        (LimitField::Nodes, "max_nodes"),
        (LimitField::StorageBytes, "max_storage_bytes"),
        (LimitField::IntegerBits, "max_integer_bits"),
        (LimitField::Exponent, "max_exponent"),
        (LimitField::Frames, "max_frames"),
    ] {
        let exceeded = LimitExceeded::new(LimitId::Field(field), None, 7, LimitAmount::Used(8));
        let error = Error::resource_limit(exceeded, Span::new(0, 3));
        let (text, _) = line(&outcome(Err(error)));
        let fields: Vec<&str> = text.split('\t').collect();
        let id = format!("Field({name})");
        assert_eq!(
            fields[4..10],
            ["ResourceLimit", "0..3", id.as_str(), "-", "7", "Used(8)"],
            "{text:?}"
        );
    }
    for (scope, amount, scope_text, amount_text) in [
        (
            LimitScope::Value,
            LimitAmount::Required(9),
            "Value",
            "Required(9)",
        ),
        (
            LimitScope::Frame,
            LimitAmount::Bound(u64::MAX),
            "Frame",
            "Bound(18446744073709551615)",
        ),
        (
            LimitScope::Temporary,
            LimitAmount::Used(0),
            "Temporary",
            "Used(0)",
        ),
    ] {
        let id = LimitId::Field(LimitField::StorageBytes);
        let exceeded = LimitExceeded::new(id, Some(scope), u64::MAX, amount);
        let error = Error::resource_limit(exceeded, None);
        let (text, _) = line(&outcome(Err(error)));
        let fields: Vec<&str> = text.split('\t').collect();
        assert_eq!(
            fields[5..10],
            [
                "-",
                "Field(max_storage_bytes)",
                scope_text,
                "18446744073709551615",
                amount_text
            ],
            "{text:?}"
        );
    }
}
