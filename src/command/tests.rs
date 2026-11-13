//! Unit tests of the command entry for what code outside the library cannot
//! build: the dispatch table and its index in the contract, the rejection
//! of settings other than the default, the operand table under signatures
//! with roles, which no operation of this release has, the lines of a
//! state, of an answer, of a request parameter, of messages that need
//! escaping and of errors with cause frames, the representative lines of
//! the serialization at their limits and under cancellation, the bound of
//! the fallback line and the table of value kinds. Errors are compared by
//! kind, span, cause frames and exceeded limit, never by message, but for
//! the one rule that the message of a missing role names its role.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::context::{CancelFlag, CancelProbe, Clock};
use crate::term::{Term, TermKind};
use crate::{
    CauseFrame, Context, Error, ErrorKind, FaultKind, LimitAmount, LimitExceeded, LimitField,
    LimitId, LimitScope, Limits, MathState, Result, Settled, Span,
};

use super::dispatch::{CATEGORY_NAMES, CommandOperation, NESTED_FRAMES, OPERATIONS, lookup};
use super::line::answer_line;
use super::operands::{self, Operands, Presence, Role, Signature};
use super::{Answer, Outcome, Request, check_default, execute, serialize};

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

/// An outcome with the versions 1, 2 and 3 and the result `result`.
fn outcome(result: Result<Settled<Answer>>) -> Outcome {
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

/// The contract of the command entry.
const CONTRACT: &str = include_str!("../../docs/components/command/contract.md");

/// The input syntax and semantics, with the output lines and the table of
/// value kinds.
const SEMANTICS: &str = include_str!("../../docs/semantics.md");

/// The rows of the Markdown table under the header line `header` in
/// `text`, each as its cells without their surrounding spaces.
fn table_rows<'a>(text: &'a str, header: &str) -> Vec<Vec<&'a str>> {
    let mut lines = text.lines().skip_while(|line| *line != header);
    assert_eq!(lines.next(), Some(header), "no table {header:?}");
    assert!(
        lines.next().is_some_and(|rule| rule.starts_with("| ---")),
        "{header:?}"
    );
    lines
        .take_while(|line| line.starts_with('|'))
        .map(|line| line.trim_matches('|').split(" | ").map(str::trim).collect())
        .collect()
}

// The dispatch table holds the three operations of this release, each once,
// and a lookup finds each by its name, byte for byte, and nothing else. The
// operation index of the contract names the same operations in the same
// order: the table is the one place that registers an operation, by name.
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
        assert_eq!(lookup(name).unwrap(), (name, operation));
    }
    for name in ["", "Eval", "eval ", " eval", "evaluate", "simplify", "dif"] {
        let error = lookup(name).unwrap_err();
        assert_eq!(
            error.kind(),
            ErrorKind::Fault(FaultKind::Unsupported),
            "{name:?}"
        );
        assert_eq!(error.span(), None);
        assert!(error.frames().is_empty());
    }
    let index = table_rows(
        CONTRACT,
        "| Operation | Contract | Signature | Result | Since |",
    );
    let names: Vec<String> = index.iter().map(|row| row[0].replace('`', "")).collect();
    let registered: Vec<&str> = OPERATIONS.iter().map(|(name, _)| *name).collect();
    assert_eq!(names, registered);
    for row in &index {
        assert_eq!(row.len(), 5, "{row:?}");
        assert_eq!(row[3], "`Answer::Term`", "{row:?}");
        assert_eq!(row[4], "`v0.1.0`", "{row:?}");
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
    assert!(error.frames().is_empty());
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
        (FaultKind::VariableMismatch, "VariableMismatch"),
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

// ---------------------------------------------------------------------------
// The operand table, under signatures that only these tests build

/// The operation of the signatures of these tests, which the dispatch table
/// does not hold.
const PROBE: &str = "probe";

/// A signature with one required role of the table.
const ONE_REQUIRED: Signature = Signature {
    roles: &[Role {
        name: "left",
        presence: Presence::Required,
    }],
};

/// A signature with a required, a repeatable, an optional and a second
/// required role, in this order.
const MIXED: Signature = Signature {
    roles: &[
        Role {
            name: "left",
            presence: Presence::Required,
        },
        Role {
            name: "items",
            presence: Presence::Repeatable,
        },
        Role {
            name: "order",
            presence: Presence::Optional,
        },
        Role {
            name: "right",
            presence: Presence::Required,
        },
    ],
};

/// Steps 3, 4, 6 and 7 of the order of a request of `PROBE` with
/// `signature`: the steps of the operand table of an operation that does
/// not read the variable, as the dispatch table runs them.
fn probe(signature: &Signature, request: &Request, context: &mut Context) -> Result<Operands> {
    let table = operands::check_table(PROBE, signature, &request.operands, context)?;
    operands::read(PROBE, &table, request, context)
}

/// The cause frames of `error`, each as its name and operand index.
fn frames(error: &Error) -> Vec<(&str, u64)> {
    error
        .frames()
        .iter()
        .map(|frame| (frame.name(), frame.operand_index()))
        .collect()
}

/// The display texts of `terms`, under the default limits.
fn texts(terms: &[Term]) -> Vec<String> {
    let c = &mut context(Limits::new());
    terms.iter().map(|term| term.display(c).unwrap()).collect()
}

/// A context whose flag is cancelled.
fn cancelled() -> Context {
    let flag = CancelFlag::new();
    flag.cancel();
    Context::new(Limits::new(), flag)
}

/// The fields of a line, without its line feed.
fn fields_of(text: &str) -> Vec<&str> {
    text.strip_suffix('\n')
        .expect("a line ends with a line feed")
        .split('\t')
        .collect()
}

// A required role that the table does not hold is a missing operand: step 4
// charges one unit for the role, then fails with `Syntax`, without a span,
// without a frame and so without a location, and its message names the
// role of the signature, a name of the library. Under a cancelled flag the
// charge fails first, with `Cancelled`. The operations of this release read
// no role of the table, so a signature of this test stands in for one.
#[test]
fn a_missing_required_role_is_a_syntax_error_without_a_location() {
    let request = Request::new(PROBE, "", "1");
    let c = &mut context(Limits::new());
    let error = probe(&ONE_REQUIRED, &request, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert_eq!(error.span(), None);
    assert!(error.frames().is_empty());
    assert_eq!(c.work_used(), 1, "one unit for the required role");
    assert!(error.message().ends_with(" left"), "{}", error.message());
    let (text, _) = line(&outcome(Err(error)));
    let found = fields_of(&text);
    assert_eq!(found.len(), 11, "{text:?}");
    assert_eq!(
        found[..10],
        ["error", "1", "2", "3", "Syntax", "-", "-", "-", "-", "-"]
    );
    let c = &mut cancelled();
    let error = probe(&ONE_REQUIRED, &request, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Cancelled);
    assert_eq!(c.work_used(), 0);
}

// A second entry of a role that is not repeatable fails at its own index:
// step 3 charges one unit for the entry, then fails with `Syntax`, without a
// span, with the frame of the entry, so its line is an `error-at` line whose
// location is the index of the second entry. An optional role cannot repeat
// either, and a repeatable role can.
#[test]
fn a_role_that_cannot_repeat_is_a_syntax_error_at_its_second_index() {
    let request = Request::new(PROBE, "", "1")
        .with_operand("left", "2")
        .with_operand("left", "3");
    let c = &mut context(Limits::new());
    let error = probe(&ONE_REQUIRED, &request, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert_eq!(error.span(), None);
    assert_eq!(frames(&error), [(PROBE, 2)]);
    assert_eq!(c.work_used(), 2, "one unit for each entry up to the second");
    let (text, _) = line(&outcome(Err(error)));
    let found = fields_of(&text);
    assert_eq!(found.len(), 12, "{text:?}");
    assert_eq!(
        (found[0], found[4], found[5], found[11]),
        ("error-at", "Syntax", "-", "2")
    );
    let request = Request::new(PROBE, "", "1")
        .with_operand("order", "1")
        .with_operand("left", "2")
        .with_operand("order", "3");
    let error = probe(&MIXED, &request, &mut context(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert_eq!(frames(&error), [(PROBE, 3)]);
    let request = Request::new(PROBE, "", "1")
        .with_operand("items", "1")
        .with_operand("left", "2")
        .with_operand("items", "3")
        .with_operand("right", "4")
        .with_operand("items", "5");
    let read = probe(&MIXED, &request, &mut context(Limits::new())).unwrap();
    assert_eq!(texts(&read.roles[1]), ["1", "3", "5"]);
}

// With a nonempty table, the entry checks the byte sum of every text
// operand, the input and each entry, against `max_input_bytes`: the sum at
// the limit passes, and one byte more fails with `ResourceLimit` naming
// `max_input_bytes`, `Required` of the sum, without a span and without a
// frame. The check is not a charge point: it charges and polls nothing, so
// a cancelled flag does not change it. With an empty table the parser
// checks the input alone before it reads it, as in release 0.1, with the
// span of the whole input.
#[test]
fn the_byte_sum_of_the_operands_is_checked_against_max_input_bytes() {
    let request = Request::new(PROBE, "", "1")
        .with_operand("left", "22")
        .with_operand("right", "333");
    let c = &mut context(Limits::new().with_max_input_bytes(6));
    probe(&MIXED, &request, c).unwrap();
    let c = &mut context(Limits::new().with_max_input_bytes(5));
    let error = probe(&MIXED, &request, c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(error.span(), None);
    assert!(error.frames().is_empty());
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::InputBytes));
    assert_eq!(exceeded.scope(), None);
    assert_eq!(exceeded.allowed(), 5);
    assert_eq!(exceeded.amount(), LimitAmount::Required(6));
    for (limit, passes) in [(6, true), (5, false)] {
        let flag = CancelFlag::new();
        flag.cancel();
        let c = Context::new(Limits::new().with_max_input_bytes(limit), flag).with_timeout(0);
        match operands::check_input_bytes(&request, &c) {
            Ok(()) => assert!(passes),
            Err(error) => {
                assert!(!passes);
                assert_eq!(error.kind(), ErrorKind::ResourceLimit, "not a charge point");
            }
        }
        assert_eq!((c.work_used(), c.output_used()), (0, 0));
    }
    let request = Request::new("eval", "x", "1234567");
    let limited = context(Limits::new().with_max_input_bytes(6));
    operands::check_input_bytes(&request, &limited).unwrap();
    let mut limited = limited;
    let outcome = execute(&request, &mut limited);
    let error = outcome.result().as_ref().unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    assert_eq!(error.span(), Span::new(0, 7));
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(LimitField::InputBytes));
    assert_eq!(exceeded.amount(), LimitAmount::Required(7));
    assert_eq!(frames(error), [("eval", 0)]);
}

// The byte sum is added with checked addition: a sum that does not fit in a
// `u64` is reported as `Bound(u64::MAX)` and fails under every value of
// `max_input_bytes`, `u64::MAX` included, while a sum of exactly `u64::MAX`
// passes under that limit.
#[test]
fn an_overflowing_byte_sum_is_reported_as_the_u64_bound() {
    for limit in [0, 1, 1 << 40, u64::MAX] {
        let c = &context(Limits::new().with_max_input_bytes(limit));
        for lengths in [
            &[u64::MAX, 1][..],
            &[1, u64::MAX - 1, 1],
            &[u64::MAX, u64::MAX],
        ] {
            let error = operands::check_byte_sum(lengths, c).unwrap_err();
            assert_eq!(error.kind(), ErrorKind::ResourceLimit);
            assert_eq!(error.span(), None);
            let exceeded = error.exceeded().unwrap();
            assert_eq!(exceeded.id(), &LimitId::Field(LimitField::InputBytes));
            assert_eq!(exceeded.allowed(), limit);
            assert_eq!(exceeded.amount(), LimitAmount::Bound(u64::MAX));
        }
    }
    let c = &context(Limits::new().with_max_input_bytes(u64::MAX));
    operands::check_byte_sum(&[u64::MAX - 1, 1], c).unwrap();
    operands::check_byte_sum(&[], c).unwrap();
}

// The operands are read in the order of the signature: the input first,
// then each role, the entries of a repeatable role in the order of the
// table, and an optional role that the table does not hold gives no term,
// so that its operation applies its default. An error of an operand has the
// frame of its index and its span into the text of that operand, and the
// first error in the order of the signature is the one reported, not the
// first of the table. The steps come in their order: the entries, the
// required roles, the byte sum, then the reading.
#[test]
fn operands_are_read_in_the_order_of_the_signature() {
    let request = Request::new(PROBE, "", "0")
        .with_operand("items", "2")
        .with_operand("right", "4")
        .with_operand("items", "3")
        .with_operand("left", "1");
    let c = &mut context(Limits::new());
    let read = probe(&MIXED, &request, c).unwrap();
    assert_eq!(texts(&[read.input]), ["0"]);
    let roles: Vec<Vec<String>> = read.roles.iter().map(|terms| texts(terms)).collect();
    assert_eq!(roles, [vec!["1"], vec!["2", "3"], vec![], vec!["4"]]);
    let request = request.with_operand("order", "5");
    let read = probe(&MIXED, &request, &mut context(Limits::new())).unwrap();
    assert_eq!(texts(&read.roles[2]), ["5"]);

    let span_of = |text: &str| {
        crate::parse(text, &mut context(Limits::new()))
            .unwrap_err()
            .span()
    };
    let request = Request::new(PROBE, "", "0")
        .with_operand("items", "2 +")
        .with_operand("right", "4")
        .with_operand("left", "(1");
    let error = probe(&MIXED, &request, &mut context(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert_eq!(frames(&error), [(PROBE, 3)], "left comes before items");
    assert_eq!(error.span(), span_of("(1"));
    let request = Request::new(PROBE, "", "0")
        .with_operand("items", "2 +")
        .with_operand("right", "4")
        .with_operand("left", "1");
    let error = probe(&MIXED, &request, &mut context(Limits::new())).unwrap_err();
    assert_eq!(frames(&error), [(PROBE, 1)]);
    assert_eq!(error.span(), span_of("2 +"));
    let request = Request::new(PROBE, "", "1/0")
        .with_operand("left", "(1")
        .with_operand("right", "4");
    let error = probe(&MIXED, &request, &mut context(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
    assert_eq!(frames(&error), [(PROBE, 0)], "the input comes first");

    // An unknown role comes before a missing role, which comes before the
    // byte sum, which comes before the reading.
    let request = Request::new(PROBE, "", "(").with_operand("other", "1");
    let error = probe(&MIXED, &request, &mut context(Limits::new())).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    assert_eq!(frames(&error), [(PROBE, 1)]);
    let request = Request::new(PROBE, "", "(").with_operand("left", "1");
    let limits = Limits::new().with_max_input_bytes(1);
    let error = probe(&MIXED, &request, &mut context(limits)).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert!(error.frames().is_empty(), "the missing role `right`");
    let request = request.with_operand("right", "1");
    let error = probe(&MIXED, &request, &mut context(limits)).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::ResourceLimit);
    // One unit for each entry and for each required role, then the parser.
    let request = Request::new(PROBE, "", "")
        .with_operand("left", "")
        .with_operand("right", "");
    let c = &mut context(Limits::new());
    let error = probe(&MIXED, &request, c).unwrap_err();
    assert_eq!(frames(&error), [(PROBE, 0)]);
    let parsed = &mut context(Limits::new());
    crate::parse("", parsed).unwrap_err();
    assert_eq!(c.work_used(), 2 + 2 + parsed.work_used());
}

// Errors outside the operands have no cause frame: settings other than the
// default, an unknown operation, a missing role and the byte sum, and a
// request failure at the charge of a required role, whose line is then an
// `error` line, also as the fallback line under a fresh context.
#[test]
fn errors_outside_the_operands_have_no_frame() {
    let settings = check_default(&LaterSettings { precision: 53 }).unwrap_err();
    let operation = lookup("simplify").unwrap_err();
    let missing = probe(
        &ONE_REQUIRED,
        &Request::new(PROBE, "", "1"),
        &mut context(Limits::new()),
    )
    .unwrap_err();
    let request = Request::new(PROBE, "", "1").with_operand("left", "2");
    let limits = Limits::new().with_max_input_bytes(1);
    let bytes = probe(&ONE_REQUIRED, &request, &mut context(limits)).unwrap_err();
    for error in [&settings, &operation, &missing, &bytes] {
        assert!(error.frames().is_empty(), "{error}");
    }
    let c = &mut cancelled();
    let error = probe(&ONE_REQUIRED, &Request::new(PROBE, "", "1"), c).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Cancelled);
    assert!(error.frames().is_empty());
    let failed = outcome(Err(error));
    assert_eq!(
        serialize(&failed, c).unwrap_err().kind(),
        ErrorKind::Cancelled
    );
    let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
    let text = String::from_utf8(serialize(&failed, fresh).unwrap()).unwrap();
    assert_eq!(fields_of(&text)[..5], ["error", "1", "2", "3", "Cancelled"]);
}

// ---------------------------------------------------------------------------
// The lines of answers and of errors with cause frames

/// An outcome with the versions 0 and the result `result`.
fn plain(result: Result<Settled<Answer>>) -> Outcome {
    Outcome {
        input_version: 0,
        context_version: 0,
        settings_version: 0,
        result,
    }
}

/// `error` with the frames `frames`, outer first.
fn framed(error: Error, frames: &[(&'static str, u64)]) -> Error {
    let mut error = error;
    for (name, index) in frames.iter().rev() {
        error = error.with_outer_frame(CauseFrame::new(name, *index));
    }
    error
}

// An answer line has eight fields: `answer`, the three versions, the kind,
// the text, the condition and the assumptions, `-` for a part that the
// value does not have. Each field with its tab is charged and written, so
// the output charged is the length of the line, and the three texts are
// printable ASCII. No answer of this release is written as an answer line,
// so the line is written here from its parts.
#[test]
fn an_answer_line_has_its_eight_fields() {
    let versions = outcome(Ok(Settled::State(MathState::Undecided)));
    for (condition, assumptions, expected) in [
        (
            Some(&b"x != 0"[..]),
            None,
            "answer\t1\t2\t3\tfunction-value\tlog(x)\tx != 0\t-\n",
        ),
        (
            Some(b"x != 0"),
            Some(&b"x: positive"[..]),
            "answer\t1\t2\t3\tfunction-value\tlog(x)\tx != 0\tx: positive\n",
        ),
        (
            None,
            None,
            "answer\t1\t2\t3\tfunction-value\tlog(x)\t-\t-\n",
        ),
    ] {
        let probe = CountingProbe::never();
        let c = &mut observed(Limits::new(), &probe);
        let bytes = answer_line(
            &versions,
            b"function-value",
            b"log(x)",
            condition,
            assumptions,
            c,
        )
        .unwrap();
        let text = String::from_utf8(bytes).unwrap();
        assert_eq!(text, expected);
        assert_eq!(c.output_used(), text.len() as u64);
        assert_eq!(probe.polls(), 9, "one charge per field and the line feed");
        let found = fields_of(&text);
        assert_eq!(found.len(), 8);
        for field in &found[5..8] {
            assert!(
                field.bytes().all(|byte| (0x20..0x7f).contains(&byte)),
                "{field:?}"
            );
        }
    }
}

// An `error-at` line has twelve fields: its fields 2 to 11 are byte for
// byte those of the `error` line of the same error without frames, and the
// twelfth is the location. An error whose only frame is the entry frame of
// the input, the operand 0, is written as an `error` line.
#[test]
fn an_error_at_line_has_its_twelve_fields() {
    let c = &mut context(Limits::new().with_max_work(3));
    let limit = c.charge(4).unwrap_err().with_default_span(Span::new(1, 2));
    for error in [
        Error::new(
            FaultKind::Syntax,
            Span::new(0, 3),
            "an operand that ends early",
        ),
        Error::new(FaultKind::Unsupported, None, "unknown role"),
        limit,
    ] {
        let (plain_line, _) = line(&outcome(Err(error.clone())));
        let (at_input, _) = line(&outcome(Err(framed(error.clone(), &[("eval", 0)]))));
        assert_eq!(at_input, plain_line, "the entry frame of the input");
        for (frames, location) in [
            (&[("eval", 1)][..], "1"),
            (&[("eval", 2)], "2"),
            (&[("rel-and", 0), ("ineq", 0)], "0>ineq#0"),
            (
                &[("eval", 18_446_744_073_709_551_615)],
                "18446744073709551615",
            ),
        ] {
            let (text, output) = line(&outcome(Err(framed(error.clone(), frames))));
            let found = fields_of(&text);
            let plain_fields = fields_of(&plain_line);
            assert_eq!(found.len(), 12, "{text:?}");
            assert_eq!(found[0], "error-at");
            assert_eq!(found[1..11], plain_fields[1..11], "{text:?}");
            assert_eq!(found[11], location);
            assert_eq!(output, text.len() as u64);
        }
    }
}

// The output lines of the examples in `docs/semantics.md` that no request
// of this release writes: the state line, the two answer lines and the
// three `error-at` lines, each built here from its parts, with every field
// but the message, which the examples leave out.
#[test]
fn the_examples_of_answers_and_locations_hold() {
    let examples: Vec<&str> = SEMANTICS
        .lines()
        .filter(|line| {
            ["value⇥", "state⇥", "error⇥", "error-at⇥", "answer⇥"]
                .iter()
                .any(|kind| line.starts_with(kind))
        })
        .collect();
    let example = |prefix: &str| -> String {
        let found: Vec<&&str> = examples
            .iter()
            .filter(|line| line.starts_with(prefix))
            .collect();
        assert_eq!(found.len(), 1, "{prefix:?} in {examples:?}");
        found[0].replace('⇥', "\t")
    };
    let state = String::from_utf8(
        serialize(
            &plain(Ok(Settled::State(MathState::IterationLimit))),
            &mut context(Limits::new()),
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(state, format!("{}\n", example("state⇥")));
    for (assumptions, prefix) in [
        (None, "answer⇥0⇥0⇥0⇥function-value⇥log(x)⇥x != 0⇥-"),
        (
            Some(&b"x: positive"[..]),
            "answer⇥0⇥0⇥0⇥function-value⇥log(x)⇥x != 0⇥x: positive",
        ),
    ] {
        let line = answer_line(
            &plain(Ok(Settled::State(MathState::Undecided))),
            b"function-value",
            b"log(x)",
            Some(b"x != 0"),
            assumptions,
            &mut context(Limits::new()),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(line).unwrap(),
            format!("{}\n", example(prefix))
        );
    }
    for (error, frames, prefix) in [
        (
            Error::new(
                FaultKind::Syntax,
                Span::new(0, 3),
                "an operand that ends early",
            ),
            &[("eval", 1)][..],
            "error-at⇥0⇥0⇥0⇥Syntax⇥0..3⇥",
        ),
        (
            Error::new(FaultKind::Unsupported, None, "unknown role"),
            &[("eval", 2)],
            "error-at⇥0⇥0⇥0⇥Unsupported⇥-⇥-⇥-⇥-⇥-⇥<message>⇥2",
        ),
        (
            Error::new(
                FaultKind::OutsideDomain,
                Span::new(3, 5),
                "outside the domain",
            ),
            &[("rel-and", 0), ("ineq", 0)],
            "error-at⇥0⇥0⇥0⇥OutsideDomain⇥3..5⇥",
        ),
    ] {
        let line = serialize(
            &plain(Err(framed(error, frames))),
            &mut context(Limits::new()),
        )
        .unwrap();
        let text = String::from_utf8(line).unwrap();
        let found = fields_of(&text);
        let expected = example(prefix);
        let expected: Vec<&str> = expected.split('\t').collect();
        assert_eq!(found.len(), 12);
        assert_eq!(found[..10], expected[..10], "{text:?}");
        assert_eq!(found[11], expected[11], "{text:?}");
    }
}

// ---------------------------------------------------------------------------
// Cancellation at every charge point

/// A probe that counts its polls and reports cancellation from the poll
/// after the first `cancel_after` polls on.
#[derive(Clone)]
struct CountingProbe {
    polls: Arc<AtomicU64>,
    cancel_after: u64,
}

impl CountingProbe {
    fn after(cancel_after: u64) -> Self {
        Self {
            polls: Arc::new(AtomicU64::new(0)),
            cancel_after,
        }
    }

    fn never() -> Self {
        Self::after(u64::MAX)
    }

    fn polls(&self) -> u64 {
        self.polls.load(Ordering::SeqCst)
    }
}

impl CancelProbe for CountingProbe {
    fn is_cancelled(&mut self) -> bool {
        let poll = self.polls.fetch_add(1, Ordering::SeqCst) + 1;
        poll > self.cancel_after
    }

    fn fork(&self) -> Box<dyn CancelProbe> {
        Box::new(self.clone())
    }
}

/// A clock that stays at 0.
#[derive(Clone, Copy)]
struct StoppedClock;

impl Clock for StoppedClock {
    fn now(&mut self) -> u64 {
        0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(*self)
    }
}

/// A context under `limits` on a stopped clock, with a deadline that never
/// passes, polling `probe`.
fn observed(limits: Limits, probe: &CountingProbe) -> Context {
    Context::with_observers(limits, Box::new(StoppedClock), Box::new(probe.clone()))
        .with_deadline(u64::MAX)
}

/// A writer of a line under a context.
type Writer<'a> = &'a dyn Fn(&mut Context) -> Result<Vec<u8>>;

/// The charge points of `write`: the polls of its probe when it writes its
/// line, with that line.
fn charge_points(write: Writer<'_>) -> (u64, Vec<u8>) {
    let probe = CountingProbe::never();
    let line = write(&mut observed(Limits::new(), &probe)).unwrap();
    (probe.polls(), line)
}

/// Asserts that a cancellation at each charge point of `write`, from the
/// first to the last, fails with `Cancelled` at that point and returns no
/// bytes, leaving the retained storage of the context as it was, and that a
/// cancellation after the last leaves the whole line. Returns the number of
/// charge points.
fn assert_whole_line_or_nothing(write: Writer<'_>) -> u64 {
    let (points, whole) = charge_points(write);
    for k in 0..points {
        let probe = CountingProbe::after(k);
        let c = &mut observed(Limits::new(), &probe);
        let before = c.retained();
        let error = write(c).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Cancelled, "charge point {}", k + 1);
        assert_eq!(probe.polls(), k + 1, "observed at its charge point");
        assert!(c.output_used() < whole.len() as u64);
        assert_eq!(c.retained(), before);
    }
    let probe = CountingProbe::after(points);
    assert_eq!(write(&mut observed(Limits::new(), &probe)).unwrap(), whole);
    points
}

// With an injected probe on a stopped clock, a cancellation injected at each
// charge point of a value, state, error, `error-at` and answer line, from
// the first to the last, gives `Cancelled` and no bytes, and after the last
// the whole line. Each field with its tab is one charge point and the line
// feed the last; the display of a value adds its own.
#[test]
fn a_cancellation_at_any_charge_point_writes_a_whole_line_or_nothing() {
    let value = execute(
        &Request::new("diff", "x", "(x+1)^3 - x"),
        &mut context(Limits::new()),
    );
    let state = outcome(Ok(Settled::State(MathState::NotConverged)));
    let fault = Error::new(
        FaultKind::DivisionByZero,
        Span::new(3, 6),
        "division by zero",
    );
    let error = outcome(Err(fault.clone()));
    let located = outcome(Err(framed(fault, &[("eval", 1)])));
    let answer = |c: &mut Context| {
        answer_line(
            &state,
            b"function-value",
            b"log(x)",
            Some(b"x != 0"),
            None,
            c,
        )
    };
    let points = assert_whole_line_or_nothing(&|c| serialize(&value, c));
    assert!(
        points > 7,
        "a poll at every field and in the display: {points}"
    );
    for (write, expected) in [
        (&(|c: &mut Context| serialize(&state, c)) as Writer<'_>, 6),
        (&|c: &mut Context| serialize(&error, c), 12),
        (&|c: &mut Context| serialize(&located, c), 13),
        (&answer, 9),
    ] {
        assert_eq!(assert_whole_line_or_nothing(write), expected);
    }
}

// ---------------------------------------------------------------------------
// The representative lines of the serialization

/// Asserts the two sides of the line of `write` and its cancellation: under
/// `max_output_bytes` and `max_work` at exactly what it needs, the line is
/// written; one less fails with `ResourceLimit` naming that field and gives
/// no bytes; and a cancellation at each of its charge points gives
/// `Cancelled`; each leaves the retained storage of the context as it was.
/// Returns the charge points, the work and the length of the line.
fn assert_representative(write: Writer<'_>) -> (u64, u64, u64) {
    let c = &mut context(Limits::new());
    let line = write(c).unwrap();
    let (work, length) = (c.work_used(), line.len() as u64);
    assert_eq!(c.output_used(), length);
    for (limits, field) in [
        (
            Limits::new().with_max_output_bytes(length),
            LimitField::OutputBytes,
        ),
        (Limits::new().with_max_work(work), LimitField::Work),
    ] {
        let c = &mut context(limits);
        assert_eq!(write(c).unwrap(), line);
        let less = match field {
            LimitField::OutputBytes => Limits::new().with_max_output_bytes(length - 1),
            _ => Limits::new().with_max_work(work - 1),
        };
        let c = &mut context(less);
        let before = c.retained();
        let error = write(c).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::ResourceLimit);
        assert_eq!(error.exceeded().unwrap().id(), &LimitId::Field(field));
        assert_eq!(c.retained(), before);
    }
    (assert_whole_line_or_nothing(write), work, length)
}

// The representative lines that no request of this release writes, at
// their limits and under cancellation: an `error-at` line with a nested
// frame, an answer line, a state line and the longest `error-at` line of
// the fallback step. Each needs one work unit per byte, and its charge
// points are its fields and its line feed.
#[test]
fn representative_lines_pass_at_their_exact_limits_and_fail_one_below() {
    let nested = plain(Err(framed(
        Error::new(
            FaultKind::OutsideDomain,
            Span::new(3, 5),
            "outside the domain",
        ),
        &[("rel-and", 0), ("ineq", 0)],
    )));
    let state = plain(Ok(Settled::State(MathState::IterationLimit)));
    let longest = longest_fallback_lines().swap_remove(0);
    let (points, work, length) = assert_representative(&|c| serialize(&nested, c));
    assert_eq!((points, work), (13, length));
    assert!(
        String::from_utf8(serialize(&nested, &mut context(Limits::new())).unwrap())
            .unwrap()
            .ends_with("\t0>ineq#0\n")
    );
    let (points, work, length) = assert_representative(&|c| {
        answer_line(
            &state,
            b"function-value",
            b"log(x)",
            Some(b"x != 0"),
            None,
            c,
        )
    });
    assert_eq!((points, work), (9, length));
    let (points, work, length) = assert_representative(&|c| serialize(&state, c));
    assert_eq!((points, work), (6, length));
    let (points, work, length) = assert_representative(&|c| serialize(&longest, c));
    assert_eq!((points, work), (13, length));
}

// Every representative line that no request writes, cancelled at each of
// its charge points, leaves no half line and the retained storage as it
// was; the same holds of the requests in `tests/command.rs`.
#[test]
fn representative_lines_cancelled_at_every_charge_point_leave_nothing() {
    let nested = plain(Err(framed(
        Error::new(
            FaultKind::OutsideDomain,
            Span::new(3, 5),
            "outside the domain",
        ),
        &[("rel-and", 0), ("ineq", 0)],
    )));
    let state = plain(Ok(Settled::State(MathState::IterationLimit)));
    let longest = longest_fallback_lines().swap_remove(0);
    let answer = |c: &mut Context| {
        answer_line(
            &state,
            b"function-value",
            b"log(x)",
            Some(b"x != 0"),
            None,
            c,
        )
    };
    for (write, points) in [
        (&(|c: &mut Context| serialize(&nested, c)) as Writer<'_>, 13),
        (&answer, 9),
        (&|c: &mut Context| serialize(&state, c), 6),
        (&|c: &mut Context| serialize(&longest, c), 13),
    ] {
        assert_eq!(assert_whole_line_or_nothing(write), points);
    }
}

// ---------------------------------------------------------------------------
// Nested categories and the bound of the fallback line

// Each nested category writes its frame in the location: an error with the
// entry frame of its operation and one nested frame, built here since the
// operations of the categories come with later releases, lists its frames
// outer first, writes the index of the entry frame, then `>`, the name of
// the nested frame, `#` and its index, and keeps its span, which counts
// bytes of the operand that the innermost frame names. A nested frame takes
// the name of an operation, as `ineq`, or of a category, and no category
// name is the name of an operation of the table.
#[test]
fn every_nested_category_writes_its_frame_in_the_location() {
    assert_eq!(
        CATEGORY_NAMES,
        ["algebraic-evaluation", "complex-embedding", "membership"]
    );
    for name in CATEGORY_NAMES.iter().chain(&["ineq"]) {
        let mut bytes = name.bytes();
        assert!(
            bytes.next().is_some_and(|first| first.is_ascii_lowercase()),
            "{name}"
        );
        assert!(
            bytes.all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-'),
            "{name}"
        );
        assert!(
            OPERATIONS.iter().all(|(operation, _)| operation != name),
            "{name}"
        );
    }
    assert!(!CATEGORY_NAMES.contains(&"ineq"), "ineq is an operation");
    for (entry, nested, location) in [
        (("rel-and", 0), ("ineq", 0), "0>ineq#0"),
        (
            ("alg-at", 1),
            (CATEGORY_NAMES[0], 2),
            "1>algebraic-evaluation#2",
        ),
        (
            ("field-value", 0),
            (CATEGORY_NAMES[1], 1),
            "0>complex-embedding#1",
        ),
        (("contains", 2), (CATEGORY_NAMES[2], 0), "2>membership#0"),
    ] {
        let error = framed(
            Error::new(
                FaultKind::OutsideDomain,
                Span::new(3, 5),
                "outside the domain",
            ),
            &[entry, nested],
        );
        assert_eq!(frames(&error), [entry, nested]);
        assert_eq!(error.span(), Span::new(3, 5));
        assert!(error.frames().len() - 1 <= NESTED_FRAMES);
        let (text, _) = line(&outcome(Err(error)));
        let found = fields_of(&text);
        assert_eq!(
            (found[0], found[5], found[11]),
            ("error-at", "3..5", location)
        );
    }
}

/// The current values of the bound of the fallback line: the longest kind
/// name $K$, the longest limit $Q$, the longest escaped message $M$, the
/// nested frames $d$ and the longest frame name $N$, as the contract of the
/// command entry states them, and the bound
/// $B = 181 + K + Q + M + 20 + d \cdot (N + 22)$.
const K: u64 = 18;
const Q: u64 = 24;
const M: u64 = 86;
const N: u64 = 20;
const B: u64 = 181 + K + Q + M + 20 + (NESTED_FRAMES as u64) * (N + 22);

/// The longest `error-at` lines that the fallback step can write: every
/// version, the span and the indices at `u64::MAX`, with one nested frame
/// of the longest frame name; the first a `ResourceLimit` with its longest
/// limit, scope, allowed value and amount, the second a fault with the
/// longest message of the library, that of a malformed variable.
fn longest_fallback_lines() -> Vec<Outcome> {
    let frames = [("expand", u64::MAX), (CATEGORY_NAMES[0], u64::MAX)];
    let exceeded = LimitExceeded::new(
        LimitId::Field(LimitField::StorageBytes),
        Some(LimitScope::Temporary),
        u64::MAX,
        LimitAmount::Required(u64::MAX),
    );
    let limit = Error::resource_limit(exceeded, Span::new(usize::MAX, usize::MAX));
    let variable = execute(
        &Request::new("expand", "1x", "x"),
        &mut context(Limits::new()),
    )
    .into_result()
    .unwrap_err()
    .with_default_span(Span::new(usize::MAX, usize::MAX));
    assert_eq!(variable.message().len() as u64, M, "the longest message");
    [limit, variable]
        .into_iter()
        .map(|error| Outcome {
            input_version: u64::MAX,
            context_version: u64::MAX,
            settings_version: u64::MAX,
            result: Err(framed(error, &frames)),
        })
        .collect()
}

// The longest `error-at` lines, with $d$ nested frames of the longest frame
// name, are written under `Context::new(Limits::new(), CancelFlag::new())`
// and are at most $B$ bytes, which is at most 65,536, the default
// `max_output_bytes`. $K$ and $Q$ are the longest kind and limit of the
// lines of this release, $N$ the longest frame name, and the contract states
// these values and $B$.
#[test]
fn a_fallback_line_with_d_nested_frames_fits_its_bound() {
    assert_eq!(B, 371);
    const { assert!(B <= 65_536) };
    assert!(CONTRACT.contains("$B = 371$"), "the contract states B");
    for (quantity, value) in [("K", K), ("Q", Q), ("M", M), ("d", 1), ("N", N)] {
        let stated = format!("${quantity} = {value}$");
        assert!(CONTRACT.contains(&stated), "the contract states {stated}");
    }
    assert_eq!(NESTED_FRAMES, 1);
    let longest_name = CATEGORY_NAMES
        .iter()
        .chain(OPERATIONS.iter().map(|(name, _)| name))
        .map(|name| name.len() as u64)
        .max();
    assert_eq!(longest_name, Some(N));
    let mut kinds = vec![
        FaultKind::Syntax,
        FaultKind::UnknownSymbol,
        FaultKind::DivisionByZero,
        FaultKind::NonIntegerExponent,
        FaultKind::NotPolynomial,
        FaultKind::Unsupported,
        FaultKind::Internal,
        FaultKind::OutsideDomain,
        FaultKind::VariableMismatch,
    ]
    .into_iter()
    .map(|fault| line(&outcome(Err(Error::new(fault, None, "fault")))).0)
    .collect::<Vec<_>>();
    for error in [
        context(Limits::new()).charge(u64::MAX).unwrap_err(),
        cancelled().charge(1).unwrap_err(),
        context(Limits::new())
            .with_timeout(0)
            .charge(1)
            .unwrap_err(),
    ] {
        kinds.push(line(&outcome(Err(error))).0);
    }
    let longest_kind = kinds
        .iter()
        .map(|text| fields_of(text)[4].len() as u64)
        .max();
    assert_eq!(longest_kind, Some(K));
    let longest_limit = LimitField::ALL
        .iter()
        .map(|field| {
            let exceeded =
                LimitExceeded::new(LimitId::Field(*field), None, 0, LimitAmount::Used(1));
            let (text, _) = line(&outcome(Err(Error::resource_limit(exceeded, None))));
            fields_of(&text)[6].len() as u64
        })
        .max();
    assert_eq!(longest_limit, Some(Q));
    for outcome in longest_fallback_lines() {
        let fresh = &mut Context::new(Limits::new(), CancelFlag::new());
        let bytes = serialize(&outcome, fresh).unwrap();
        assert!(bytes.len() as u64 <= B, "{} bytes", bytes.len());
        let text = String::from_utf8(bytes).unwrap();
        let found = fields_of(&text);
        assert_eq!(
            found[11],
            "18446744073709551615>algebraic-evaluation#18446744073709551615"
        );
        let nested = outcome.result().as_ref().unwrap_err().frames().len() - 1;
        assert!(nested <= NESTED_FRAMES);
    }
}

// ---------------------------------------------------------------------------
// The table of value kinds

/// The kind of an answer, as the table of value kinds names it: one name
/// for each variant of `Answer`, which this match lists.
fn answer_kind(answer: &Answer) -> &'static str {
    match answer {
        Answer::Term(_) => "term",
    }
}

/// The kind of a shape of a term with a display rule, as the table of value
/// kinds names it; the reserved call has no row.
fn shape_kind(kind: TermKind) -> Option<&'static str> {
    match kind {
        TermKind::Number => Some("number"),
        TermKind::Symbol => Some("symbol"),
        TermKind::Power => Some("power"),
        TermKind::Product => Some("product"),
        TermKind::Sum => Some("sum"),
        TermKind::Call => None,
    }
}

/// The test files that the table of value kinds names.
const TEST_FILES: [(&str, &str); 4] = [
    ("tests/terms.rs", include_str!("../../tests/terms.rs")),
    ("tests/command.rs", include_str!("../../tests/command.rs")),
    (
        "tests/syntax_properties.rs",
        include_str!("../../tests/syntax_properties.rs"),
    ),
    ("tests/syntax.rs", include_str!("../../tests/syntax.rs")),
];

/// Asserts that the cell `cell` names at least one test, as
/// `` `file::name` ``, and that each is a function of its file.
fn assert_tests_exist(cell: &str) {
    let named: Vec<&str> = cell.split('`').skip(1).step_by(2).collect();
    assert!(!named.is_empty(), "{cell:?}");
    for test in named {
        let (file, name) = test.split_once("::").unwrap_or_else(|| panic!("{test:?}"));
        let (_, source) = TEST_FILES
            .iter()
            .find(|(path, _)| *path == file)
            .unwrap_or_else(|| panic!("no test file {file}"));
        assert!(source.contains(&format!("fn {name}(")), "{test}");
    }
}

// The table of value kinds in `docs/semantics.md` has one row for every
// variant of `Answer` and one for each shape of a term with a display rule,
// and every row names its display tests and its round-trip tests, each a
// function of the test file that the row names, and the release of its
// value model and encoding.
#[test]
fn the_table_of_value_kinds_has_a_row_for_every_answer_variant_and_term_shape() {
    let rows = table_rows(
        SEMANTICS,
        "| Kind | Level | Component | Line | Condition | Scope | Display | Display tests | Reading | Round-trip tests | Encoding |",
    );
    let kinds: Vec<String> = rows.iter().map(|row| row[0].replace('`', "")).collect();
    let mut expected = vec![answer_kind(&Answer::Term(
        Term::symbol("x", &mut context(Limits::new())).unwrap(),
    ))];
    for kind in [
        TermKind::Number,
        TermKind::Symbol,
        TermKind::Power,
        TermKind::Product,
        TermKind::Sum,
        TermKind::Call,
    ] {
        expected.extend(shape_kind(kind));
    }
    assert_eq!(kinds, expected);
    for row in &rows {
        assert_eq!(row.len(), 11, "{row:?}");
        let level = if row[0] == "`term`" {
            "the answer `Answer::Term`".to_owned()
        } else {
            let kind = row[0].replace('`', "");
            let variant = kind[..1].to_uppercase() + &kind[1..];
            format!("a shape in a term, `TermKind::{variant}`")
        };
        assert_eq!(row[1], level, "{row:?}");
        assert_eq!(row[8], "the input grammar reads it back", "{row:?}");
        assert_eq!(row[10], "release 0.3, planned", "{row:?}");
        assert_tests_exist(row[7]);
        assert_tests_exist(row[9]);
    }
}
