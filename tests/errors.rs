//! The public interface of errors and result states, as code outside the
//! library sees it. Errors are compared by kind, span and exceeded limit,
//! never by message.

use kalyx::{
    CauseFrame, Error, ErrorClass, ErrorKind, FaultKind, LimitField, MathState, Settled, Span,
};

const FAULTS: [FaultKind; 9] = [
    FaultKind::Syntax,
    FaultKind::UnknownSymbol,
    FaultKind::DivisionByZero,
    FaultKind::NonIntegerExponent,
    FaultKind::NotPolynomial,
    FaultKind::Unsupported,
    FaultKind::Internal,
    FaultKind::OutsideDomain,
    FaultKind::VariableMismatch,
];

// Carried over: code outside the library constructs errors of its own, with
// and without a span.
#[test]
fn ex6_code_outside_the_library_constructs_its_own_errors() {
    let ragged = Error::new(FaultKind::Unsupported, None, "rows of unequal length");
    assert_eq!(ragged.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    assert_eq!(ragged.span(), None);
    assert!(ragged.exceeded().is_none());

    let span = Span::new(4, 9);
    let unsupported = Error::new(
        FaultKind::Unsupported,
        span,
        String::from("unsupported operand"),
    );
    assert_eq!(unsupported.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    assert_eq!(unsupported.span(), span);
    assert!(unsupported.exceeded().is_none());
}

// Carried over: `Error` implements the standard error trait.
#[test]
fn errors_implement_the_standard_error_trait() {
    let error: Box<dyn std::error::Error> = Box::new(Error::new(
        FaultKind::DivisionByZero,
        Span::new(0, 4),
        "division by zero",
    ));
    let error = error.downcast_ref::<Error>().unwrap();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::DivisionByZero));
    assert_eq!(error.span(), Span::new(0, 4));
}

// `Display` writes the message, followed by the span when there is one; the
// assertions do not depend on the text of the message.
#[test]
fn display_appends_the_span_to_the_message() {
    let spanned = Error::new(
        FaultKind::DivisionByZero,
        Span::new(0, 4),
        "division by zero",
    );
    assert_eq!(
        spanned.to_string(),
        format!("{} at bytes 0..4", spanned.message())
    );
    let ragged = Error::new(FaultKind::Unsupported, None, "rows of unequal length");
    assert_eq!(ragged.to_string(), ragged.message());
}

// `Error::new` builds every fault kind, without cause frames, and none of
// them is a request failure. Its compile-fail documentation test shows that
// it does not accept a request kind.
#[test]
fn error_new_builds_faults_and_never_request_failures() {
    for fault in FAULTS {
        let error = Error::new(fault, Span::new(1, 1), "fault");
        assert_eq!(error.kind(), ErrorKind::Fault(fault));
        assert_eq!(error.span(), Span::new(1, 1));
        let frames: &[CauseFrame] = error.frames();
        assert!(frames.is_empty());
        assert!(error.exceeded().is_none());
        assert_ne!(error.kind().class(), ErrorClass::Context);
        assert_ne!(error.kind(), ErrorKind::ResourceLimit);
        assert_ne!(error.kind(), ErrorKind::Cancelled);
        assert_ne!(error.kind(), ErrorKind::DeadlineExceeded);
    }
}

#[test]
fn request_kinds_are_of_the_context_class() {
    for kind in [
        ErrorKind::ResourceLimit,
        ErrorKind::Cancelled,
        ErrorKind::DeadlineExceeded,
    ] {
        assert_eq!(kind.class(), ErrorClass::Context);
    }
}

#[test]
fn a_span_is_never_inverted() {
    let empty = Span::new(4, 4).unwrap();
    assert_eq!((empty.start(), empty.end()), (4, 4));
    assert_eq!(Span::new(5, 4), None);
}

// The nine fields of `Limits`, in order, with their names.
#[test]
fn limit_fields_name_the_fields_of_limits() {
    let names: Vec<&str> = LimitField::ALL.iter().map(|field| field.name()).collect();
    assert_eq!(
        names,
        [
            "max_work",
            "max_input_bytes",
            "max_output_bytes",
            "max_depth",
            "max_nodes",
            "max_storage_bytes",
            "max_integer_bits",
            "max_exponent",
            "max_frames",
        ]
    );
}

#[test]
fn settled_holds_a_value_or_a_state() {
    let value = Settled::Value("answer");
    assert_eq!(value.value(), Some(&"answer"));
    assert!(value.is_value());
    let state = Settled::<&str>::State(MathState::NotConverged);
    assert_eq!(state.state(), Some(MathState::NotConverged));
    assert!(state.is_state());
}
