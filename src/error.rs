//! Errors and result states.
//!
//! A request that has no answer fails with an [`Error`]: the input is
//! invalid, a domain error such as division by zero occurred, a limit was
//! exhausted, the request was cancelled or its deadline passed. A method that
//! ends meaningfully without a complete answer returns a [`MathState`] inside
//! `Ok`, as [`Settled::State`]. The two are separate types, so a request
//! failure takes precedence over every state: it is on the `Err` side.
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/errors/contract.md`.

use std::fmt;

/// The result type of the library: a value, or the [`Error`] that ended the
/// request.
pub type Result<T> = std::result::Result<T, Error>;

/// A half-open range of byte offsets into the source text of a request.
///
/// `start` is at most `end`; an empty span (`start == end`) marks a position,
/// such as the end of incomplete input.
///
/// ```
/// use kalyx::Span;
///
/// let span = Span::new(4, 9).expect("4 is at most 9");
/// assert_eq!((span.start(), span.end()), (4, 9));
/// assert_eq!(Span::new(9, 4), None);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// The span from byte `start` up to, but not including, byte `end`, or
    /// `None` when `end` is less than `start`.
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    /// The offset of the first byte of the span.
    #[must_use]
    pub const fn start(self) -> usize {
        self.start
    }

    /// The offset just past the last byte of the span.
    #[must_use]
    pub const fn end(self) -> usize {
        self.end
    }
}

/// The kind of an [`Error`].
///
/// The first three kinds are request failures. Only the request context
/// constructs them; [`Error::new`] accepts only a [`FaultKind`]. Every other
/// error is a [`Fault`](ErrorKind::Fault).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// A limit of the request was exhausted; [`Error::exceeded`] names it.
    ResourceLimit,
    /// The request was cancelled.
    Cancelled,
    /// The deadline of the request passed.
    DeadlineExceeded,
    /// The input is invalid, a domain error occurred, the request is not
    /// supported or an internal invariant failed.
    Fault(FaultKind),
}

impl ErrorKind {
    /// The class of the kind: [`ErrorClass::Context`] for the three request
    /// failures, and the class of the [`FaultKind`] for a fault.
    ///
    /// ```
    /// use kalyx::{ErrorClass, ErrorKind, FaultKind};
    ///
    /// assert_eq!(ErrorKind::Cancelled.class(), ErrorClass::Context);
    /// assert_eq!(ErrorKind::Fault(FaultKind::Syntax).class(), ErrorClass::Input);
    /// assert_eq!(ErrorKind::Fault(FaultKind::Internal).class(), ErrorClass::Internal);
    /// ```
    #[must_use]
    pub const fn class(self) -> ErrorClass {
        match self {
            Self::ResourceLimit | Self::Cancelled | Self::DeadlineExceeded => ErrorClass::Context,
            Self::Fault(fault) => fault.class(),
        }
    }
}

/// The kind of a fault: an error that is not a request failure.
///
/// The first seven are the foundation kinds; the kinds after them were
/// appended by the features that brought them. A feature that needs a kind of
/// its own adds it in the release that brings the feature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FaultKind {
    /// The input does not follow the syntax, such as an unexpected character
    /// or a missing operand.
    Syntax,
    /// A name that the request does not define.
    UnknownSymbol,
    /// Division by zero, including a zero base with a negative exponent.
    DivisionByZero,
    /// An exponent that is not an integer constant.
    NonIntegerExponent,
    /// An expression that is not a polynomial where one is required.
    NotPolynomial,
    /// Valid input that this release does not support.
    Unsupported,
    /// An internal invariant of the library failed. This is a defect of the
    /// library, reported as an error instead of a panic.
    Internal,
    /// An argument outside the domain of the operation, such as a modulus
    /// that is not positive, or a negative power modulo $m$ of a residue
    /// that has no inverse.
    OutsideDomain,
    /// Values that must belong to the same parent structure belong to
    /// different ones: two parents stored with their elements differ, such
    /// as the prime fields of two different moduli. No operation of this
    /// release reports it, since none stores a parent together with an
    /// element; the methods of a coefficient field assume that their
    /// elements belong to the receiver and do not report it.
    VariableMismatch,
}

impl FaultKind {
    /// The class of the kind: [`ErrorClass::Internal`] for
    /// [`Internal`](FaultKind::Internal) and [`ErrorClass::Input`] for every
    /// other kind. A fault is never of class [`ErrorClass::Context`].
    #[must_use]
    pub const fn class(self) -> ErrorClass {
        match self {
            Self::Internal => ErrorClass::Internal,
            Self::Syntax
            | Self::UnknownSymbol
            | Self::DivisionByZero
            | Self::NonIntegerExponent
            | Self::NotPolynomial
            | Self::Unsupported
            | Self::OutsideDomain
            | Self::VariableMismatch => ErrorClass::Input,
        }
    }
}

/// Who can act on an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorClass {
    /// A request failure: a larger limit, a later deadline or no cancellation
    /// may let the same request succeed.
    Context,
    /// The request itself is at fault: invalid or unsupported input, or a
    /// domain error.
    Input,
    /// A defect of the library.
    Internal,
}

/// The error that ends a request without an answer.
///
/// An error has a [kind](Error::kind), an optional [span](Error::span) of the
/// source text, an English [message](Error::message) for people, its
/// [cause frames](Error::frames) and, for a [`ErrorKind::ResourceLimit`], the
/// [limit that was exceeded](Error::exceeded). Programs act on the kind, the
/// span, the cause frames and the exceeded limit; the message is not part of
/// the interface. `Error` therefore does not implement `PartialEq`: compare
/// those parts instead.
#[derive(Clone, Debug)]
pub struct Error {
    cause: ErrorCause,
    span: Option<Span>,
    message: String,
    frames: Box<[CauseFrame]>,
}

/// A cause frame of an [`Error`]: the name of an operation, or of a fixed
/// step of the library that an operation enters, and the index of the
/// operand of that operation or step in which the error arose.
///
/// [`Error::frames`] lists the frames of an error outer first. A frame is a
/// record on the error only: adding one charges nothing and opens no frame
/// of the request context, so it does not count against `max_frames`. The
/// name is a name that the library defines, never text of a request, and has
/// the form `[a-z][a-z0-9-]*`. The index counts the operands of that
/// operation or step from 0; for an operation, 0 is its input. For the
/// entry frame, the first, an index $k \ge 1$ is the entry `operands[k-1]`
/// of the operand table of the request; for a nested frame, the operand $k$
/// of the signature of its operation, or, for a fixed step, of the operands
/// of that step, which the contract of the component that delivers the step
/// numbers. Only the library builds frames: the command entry adds the entry
/// frame, the operation of the request and the index of the operand in which
/// an error arose, and no operation of this release enters a fixed step that
/// adds a nested frame.
/// Code outside the library reads frames but cannot build them:
///
/// ```compile_fail,E0624
/// let frame = kalyx::CauseFrame::new("eval", 0);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct CauseFrame {
    name: String,
    operand_index: u64,
}

impl CauseFrame {
    /// The frame of the operation or step `name` at its operand
    /// `operand_index`. The name is taken as a `&'static str`, a static name
    /// of the library, and stored as an owned string, since code meant to be
    /// proved returns no string literal. Text of a request could reach it
    /// only by leaking a string into a `&'static str`, which the library
    /// never does and review rejects.
    pub(crate) fn new(name: &'static str, operand_index: u64) -> Self {
        Self {
            name: String::from(name),
            operand_index,
        }
    }

    /// The name of the operation or step.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The index of the operand in which the error arose, counted from 0;
    /// for an operation, 0 is its input.
    #[must_use]
    pub const fn operand_index(&self) -> u64 {
        self.operand_index
    }
}

/// What an [`Error`] reports. Keeping the exceeded limit in the
/// `ResourceLimit` case makes [`Error::exceeded`] `Some` exactly for that kind.
#[derive(Clone, Debug)]
enum ErrorCause {
    ResourceLimit(LimitExceeded),
    Cancelled,
    DeadlineExceeded,
    Fault(FaultKind),
}

impl Error {
    /// Creates a fault of `kind` with an optional source `span` and an
    /// English `message`.
    ///
    /// The library creates its faults with this constructor, and code outside
    /// the library may use it for errors of its own. It takes only a
    /// [`FaultKind`]: a request failure ([`ErrorKind::ResourceLimit`],
    /// [`ErrorKind::Cancelled`] or [`ErrorKind::DeadlineExceeded`]) comes only
    /// from the request context, so no other code can report one.
    ///
    /// ```
    /// use kalyx::{Error, ErrorKind, FaultKind, Span};
    ///
    /// let error = Error::new(FaultKind::Unsupported, Span::new(4, 9), "unsupported operand");
    /// assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Unsupported));
    /// assert_eq!(error.span(), Span::new(4, 9));
    /// assert!(error.exceeded().is_none());
    /// ```
    ///
    /// The same call with a request kind does not compile, because the kind
    /// is an [`ErrorKind`], not a [`FaultKind`]:
    ///
    /// ```compile_fail,E0308
    /// use kalyx::{Error, ErrorKind, FaultKind, Span};
    ///
    /// let error = Error::new(ErrorKind::Cancelled, Span::new(4, 9), "unsupported operand");
    /// ```
    pub fn new(kind: FaultKind, span: Option<Span>, message: impl Into<String>) -> Self {
        Self {
            cause: ErrorCause::Fault(kind),
            span,
            message: message.into(),
            frames: Box::new([]),
        }
    }

    /// The request failure of an exhausted limit, reported by the request
    /// context at the check that failed, with the span that its caller gave.
    pub(crate) fn resource_limit(exceeded: LimitExceeded, span: Option<Span>) -> Self {
        let mut message = String::from("resource limit exceeded: ");
        message.push_str(exceeded.id().name());
        Self {
            cause: ErrorCause::ResourceLimit(exceeded),
            span,
            message,
            frames: Box::new([]),
        }
    }

    /// The request failure of a cancelled request, reported by the request
    /// context with the span that its caller gave.
    pub(crate) fn cancelled(span: Option<Span>) -> Self {
        Self {
            cause: ErrorCause::Cancelled,
            span,
            message: String::from("computation cancelled"),
            frames: Box::new([]),
        }
    }

    /// The request failure of a passed deadline, reported by the request
    /// context with the span that its caller gave.
    pub(crate) fn deadline_exceeded(span: Option<Span>) -> Self {
        Self {
            cause: ErrorCause::DeadlineExceeded,
            span,
            message: String::from("deadline exceeded"),
            frames: Box::new([]),
        }
    }

    /// The error with the source span `span` when it has none; an error that
    /// already has a span keeps it, so the innermost span is the one
    /// reported. The parser gives each error of the term core, which carries
    /// no span, the span of the syntax node whose term failed.
    pub(crate) fn with_default_span(mut self, span: Option<Span>) -> Self {
        if self.span.is_none() {
            self.span = span;
        }
        self
    }

    /// The error with `frame` as its outermost cause frame, before the frames
    /// that it has; its kind, span, message and exceeded limit stay the same.
    /// A frame is a record only: adding it charges nothing and does not count
    /// against `max_frames`.
    pub(crate) fn with_outer_frame(mut self, frame: CauseFrame) -> Self {
        let mut frames = self.frames.into_vec();
        frames.insert(0, frame);
        self.frames = frames.into_boxed_slice();
        self
    }

    /// The kind of the error.
    #[must_use]
    pub const fn kind(&self) -> ErrorKind {
        match &self.cause {
            ErrorCause::ResourceLimit(_) => ErrorKind::ResourceLimit,
            ErrorCause::Cancelled => ErrorKind::Cancelled,
            ErrorCause::DeadlineExceeded => ErrorKind::DeadlineExceeded,
            ErrorCause::Fault(fault) => ErrorKind::Fault(*fault),
        }
    }

    /// The byte range of the source text that the error refers to, or `None`
    /// when no single range applies.
    ///
    /// The range counts bytes of the text of the operand that the innermost
    /// [cause frame](Error::frames) names. With no frame, or with only an
    /// outer frame of the operand index 0, it counts bytes of the text that
    /// the entry was given: the input of a request, or the source text of a
    /// library function that is called directly.
    #[must_use]
    pub const fn span(&self) -> Option<Span> {
        self.span
    }

    /// The cause frames of the error, outer first: the outermost frame, the
    /// entry frame, names the operation of the request and the operand in
    /// which the error arose, and each later frame, a nested frame, an
    /// operation or a fixed step that the one before it entered, with the
    /// operand there. An operand index counts from 0: 0 is the input, and
    /// an index $k \ge 1$ is the entry `operands[k-1]` of the operand table
    /// of the request for the entry frame, and for a nested frame the
    /// operand $k$ of the signature of its operation, or, for a fixed step,
    /// of the operands of that step, which the contract of the component
    /// that delivers the step numbers. The command entry adds the entry
    /// frame to an error of an operand of a request and to an error of the
    /// operation itself; an error of the settings, of the operation name, of
    /// a missing role, of the byte sum of the operands or of the variable has
    /// no frame, and neither has an error of a library function that is
    /// called directly, or one that [`Error::new`] builds. No operation of
    /// this release adds a nested frame.
    ///
    /// ```
    /// use kalyx::context::CancelFlag;
    /// use kalyx::{Context, Error, FaultKind, Limits, Request, Span, execute};
    ///
    /// let error = Error::new(FaultKind::Syntax, Span::new(0, 1), "unexpected character");
    /// assert!(error.frames().is_empty());
    ///
    /// let mut context = Context::new(Limits::new(), CancelFlag::new());
    /// let outcome = execute(&Request::new("eval", "x", "1/0"), &mut context);
    /// let frames = outcome.result().as_ref().unwrap_err().frames();
    /// assert_eq!(frames.len(), 1);
    /// assert_eq!((frames[0].name(), frames[0].operand_index()), ("eval", 0));
    /// ```
    #[must_use]
    pub fn frames(&self) -> &[CauseFrame] {
        &self.frames
    }

    /// The English message of the error. It is text for people and not part
    /// of the interface; programs use [`kind`](Error::kind),
    /// [`span`](Error::span), [`frames`](Error::frames) and
    /// [`exceeded`](Error::exceeded).
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The limit that was exceeded: `Some` exactly when the kind is
    /// [`ErrorKind::ResourceLimit`].
    #[must_use]
    pub const fn exceeded(&self) -> Option<&LimitExceeded> {
        match &self.cause {
            ErrorCause::ResourceLimit(exceeded) => Some(exceeded),
            ErrorCause::Cancelled | ErrorCause::DeadlineExceeded | ErrorCause::Fault(_) => None,
        }
    }
}

impl fmt::Display for Error {
    /// The message, followed by ` at bytes <start>..<end>` when the error has
    /// a span.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)?;
        if let Some(span) = self.span {
            write!(f, " at bytes {}..{}", span.start, span.end)?;
        }
        Ok(())
    }
}

impl std::error::Error for Error {}

/// The limit that a [`ErrorKind::ResourceLimit`] error exceeded.
///
/// Only the request context creates it. Raising the limit that
/// [`id`](LimitExceeded::id) names, to at least the [amount](LimitExceeded::amount)
/// that was needed, lifts the error.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct LimitExceeded {
    id: LimitId,
    scope: Option<LimitScope>,
    allowed: u64,
    amount: LimitAmount,
}

impl LimitExceeded {
    /// The record of an exceeded limit. Callers pass a `scope` that is `Some`
    /// exactly for [`LimitField::Nodes`] and [`LimitField::StorageBytes`], and
    /// `None` for every other field and for a parameter, as the contract
    /// states; this constructor does not check it. In the request context,
    /// only the retained totals are reported with a scope, through a helper
    /// that takes one of those two fields.
    pub(crate) const fn new(
        id: LimitId,
        scope: Option<LimitScope>,
        allowed: u64,
        amount: LimitAmount,
    ) -> Self {
        Self {
            id,
            scope,
            allowed,
            amount,
        }
    }

    /// The limit: a field of `Limits` or a request parameter.
    #[must_use]
    pub const fn id(&self) -> &LimitId {
        &self.id
    }

    /// Where a [`LimitField::Nodes`] or [`LimitField::StorageBytes`] limit
    /// was reached; `None` for every other limit.
    #[must_use]
    pub const fn scope(&self) -> Option<LimitScope> {
        self.scope
    }

    /// The value of the limit that was in force.
    #[must_use]
    pub const fn allowed(&self) -> u64 {
        self.allowed
    }

    /// How much was used or needed.
    #[must_use]
    pub const fn amount(&self) -> LimitAmount {
        self.amount
    }
}

/// The identifier of a limit.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LimitId {
    /// A field of `Limits`. A bound derived from a field names that field.
    Field(LimitField),
    /// An explicit parameter of the request, by its name.
    Parameter(String),
}

impl LimitId {
    /// The name of the limit: the name of the field of `Limits`, such as
    /// `max_work`, or the name of the parameter.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Field(field) => field.name(),
            Self::Parameter(name) => name,
        }
    }
}

/// A field of [`Limits`](crate::Limits), the limits of a request. Each
/// variant corresponds to one field, named by [`name`](LimitField::name).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LimitField {
    /// `max_work`: the work units charged by the request.
    Work,
    /// `max_input_bytes`: the bytes of the request's input; for a request
    /// with a nonempty operand table, the sum of the bytes of every text
    /// operand, the input and each entry of the table, which the command
    /// entry adds with checked addition and reports as `Bound(u64::MAX)`
    /// when it does not fit in a `u64`.
    InputBytes,
    /// `max_output_bytes`: the bytes of all display and serialization of the
    /// request, cumulative.
    OutputBytes,
    /// `max_depth`: the nesting depth of syntax, terms and values.
    Depth,
    /// `max_nodes`: the nodes retained at one time.
    Nodes,
    /// `max_storage_bytes`: the logical storage bytes retained at one time.
    StorageBytes,
    /// `max_integer_bits`: the bits of one integer.
    IntegerBits,
    /// `max_exponent`: the absolute value of one integer exponent; also
    /// degrees and orders of derivatives.
    Exponent,
    /// `max_frames`: the frames open at one time.
    Frames,
}

impl LimitField {
    /// Every field, in the order of `Limits`.
    pub const ALL: &'static [Self] = &[
        Self::Work,
        Self::InputBytes,
        Self::OutputBytes,
        Self::Depth,
        Self::Nodes,
        Self::StorageBytes,
        Self::IntegerBits,
        Self::Exponent,
        Self::Frames,
    ];

    /// The name of the field of `Limits`, such as `max_work`.
    ///
    /// ```
    /// use kalyx::LimitField;
    ///
    /// assert_eq!(LimitField::StorageBytes.name(), "max_storage_bytes");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Work => "max_work",
            Self::InputBytes => "max_input_bytes",
            Self::OutputBytes => "max_output_bytes",
            Self::Depth => "max_depth",
            Self::Nodes => "max_nodes",
            Self::StorageBytes => "max_storage_bytes",
            Self::IntegerBits => "max_integer_bits",
            Self::Exponent => "max_exponent",
            Self::Frames => "max_frames",
        }
    }
}

// At most ten fields are listed, and `Limits` has one field for each; a new
// limit is a new field with a default.
const _: () = assert!(LimitField::ALL.len() <= 10, "Limits has at most ten fields");

/// Where a limit on retained nodes or storage bytes was reached.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LimitScope {
    /// Building or admitting a value.
    Value,
    /// The cost of an open frame.
    Frame,
    /// A reserved temporary.
    Temporary,
}

/// How much of a limit was used or needed when it was exceeded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LimitAmount {
    /// The total at the check that failed.
    Used(u64),
    /// The exact amount that was needed.
    Required(u64),
    /// A reliable upper estimate of the amount, beyond the allowed value;
    /// `u64::MAX` when the amount does not fit in a `u64`.
    Bound(u64),
}

impl LimitAmount {
    /// The number, whichever of the three it is.
    #[must_use]
    pub const fn value(self) -> u64 {
        match self {
            Self::Used(value) | Self::Required(value) | Self::Bound(value) => value,
        }
    }
}

/// A mathematical state: a meaningful outcome of a method that is not a
/// complete answer. It is a value inside `Ok`, never an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MathState {
    /// The method did not reach its tolerance.
    NotConverged,
    /// The expression is kept unevaluated.
    Unevaluated,
    /// The method does not apply to this input and gave up.
    NotApplicable,
    /// The question could not be decided.
    Undecided,
    /// The method reached the iteration cap that its caller gave it.
    IterationLimit,
}

/// The outcome of a method that has result states: a value, or the
/// [`MathState`] in which the method ended.
///
/// A method without states returns `Result<T>`; a method with states returns
/// `Result<Settled<T>>`, so an `Err` still means that the request has no
/// answer.
///
/// ```
/// use kalyx::{MathState, Settled};
///
/// let value = Settled::Value(3);
/// assert_eq!(value.value(), Some(&3));
/// let undecided = Settled::<u8>::State(MathState::Undecided);
/// assert_eq!(undecided.state(), Some(MathState::Undecided));
/// assert_eq!(undecided.into_value(), None);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
#[must_use = "a result state must be checked"]
pub enum Settled<T> {
    /// The method reached its answer.
    Value(T),
    /// The method ended in a state.
    State(MathState),
}

impl<T> Settled<T> {
    /// The value, or `None` in a state.
    #[must_use]
    pub const fn value(&self) -> Option<&T> {
        match self {
            Self::Value(value) => Some(value),
            Self::State(_) => None,
        }
    }

    /// The value, or `None` in a state.
    #[must_use]
    pub fn into_value(self) -> Option<T> {
        match self {
            Self::Value(value) => Some(value),
            Self::State(_) => None,
        }
    }

    /// The state, or `None` for a value.
    #[must_use]
    pub const fn state(&self) -> Option<MathState> {
        match self {
            Self::Value(_) => None,
            Self::State(state) => Some(*state),
        }
    }

    /// Whether the method reached its answer.
    #[must_use]
    pub const fn is_value(&self) -> bool {
        matches!(self, Self::Value(_))
    }

    /// Whether the method ended in a state.
    #[must_use]
    pub const fn is_state(&self) -> bool {
        matches!(self, Self::State(_))
    }
}

/// Where a cap was reached inside the library.
///
/// No method of this release has a cap of its own, so there is one general
/// variant. A method family that brings a cap adds a variant that names its
/// place, with a fixed diagnostic text, in the release that brings it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no method of this release has a cap; the unit tests reach every case"
    )
)]
pub(crate) enum Cap {
    /// A method reached the iteration bound that its caller gave it.
    IterationBound,
}

impl Cap {
    /// The diagnostic text of the cap: a fixed text, built as an owned
    /// string, since code meant to be proved returns no string literal.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "no method of this release has a cap; the unit tests reach every case"
        )
    )]
    pub(crate) fn message(self) -> String {
        match self {
            Self::IterationBound => String::from("iteration bound reached"),
        }
    }
}

/// Why an internal computation stopped without a value: an error, or a stop
/// in a state, with the cap at which it stopped.
///
/// There is deliberately no conversion from `Halt` to `Error`, so every place
/// that ends an internal computation decides what a stop means there.
#[derive(Clone, Debug)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no method of this release stops in a state; the unit tests reach every case"
    )
)]
pub(crate) enum Halt {
    Error(Error),
    Stop(MathState, Cap),
}

impl From<Error> for Halt {
    fn from(error: Error) -> Self {
        Self::Error(error)
    }
}

/// An internal computation that can stop in a state. Sequencing with `?`
/// stops at the first halt, so a stop in an inner computation reaches the
/// boundary of the method unchanged.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no method of this release stops in a state; the unit tests reach every case"
    )
)]
pub(crate) type Run<T> = std::result::Result<T, Halt>;

/// Ends an internal computation at the boundary of a method that returns
/// [`Settled`]: a value becomes [`Settled::Value`], a stop becomes
/// [`Settled::State`] with its state, and every error stays the same error.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no method of this release stops in a state; the unit tests reach every case"
    )
)]
pub(crate) fn settle<T>(run: Run<T>) -> Result<Settled<T>> {
    match run {
        Ok(value) => Ok(Settled::Value(value)),
        Err(Halt::Stop(state, _)) => Ok(Settled::State(state)),
        Err(Halt::Error(error)) => Err(error),
    }
}

/// Ends an iterative method whose own stops are other values than the stop
/// of its evaluations: the stop that the method reached is kept, a stop of an
/// evaluation becomes the stop `capped` of the method, and every error stays
/// the same error.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "no method of this release stops in a state; the unit tests reach every case"
    )
)]
pub(crate) fn evaluation_stop<S>(run: Run<S>, capped: S) -> Result<S> {
    match run {
        Ok(stop) => Ok(stop),
        Err(Halt::Stop(_, _)) => Ok(capped),
        Err(Halt::Error(error)) => Err(error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::{CancelFlag, Context, Limits};

    const STATES: [MathState; 5] = [
        MathState::NotConverged,
        MathState::Unevaluated,
        MathState::NotApplicable,
        MathState::Undecided,
        MathState::IterationLimit,
    ];

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

    fn span(start: usize, end: usize) -> Option<Span> {
        Some(Span::new(start, end).unwrap())
    }

    fn work_exhausted() -> Error {
        let exceeded = LimitExceeded::new(
            LimitId::Field(LimitField::Work),
            None,
            10,
            LimitAmount::Required(11),
        );
        Error::resource_limit(exceeded, span(0, 3))
    }

    /// One error of each request kind, a domain error and an invalid input,
    /// each with a span.
    fn failures() -> Vec<Error> {
        vec![
            work_exhausted(),
            Error::cancelled(span(1, 2)),
            Error::deadline_exceeded(span(2, 2)),
            Error::new(FaultKind::DivisionByZero, span(0, 7), "division by zero"),
            Error::new(FaultKind::Syntax, span(0, 1), "unexpected character"),
        ]
    }

    /// Whether two errors agree in kind, span, cause frames and exceeded
    /// limit, the parts of an error that programs act on.
    fn same(left: &Error, right: &Error) -> bool {
        left.kind() == right.kind()
            && left.span() == right.span()
            && left.frames() == right.frames()
            && left.exceeded() == right.exceeded()
    }

    // Carried over: the partition of runs by `settle`.
    #[test]
    fn settle_partitions_runs_into_values_states_and_errors() {
        assert_eq!(settle(Ok(7)).unwrap(), Settled::Value(7));
        for state in STATES {
            assert_eq!(
                settle::<u8>(Err(Halt::Stop(state, Cap::IterationBound))).unwrap(),
                Settled::State(state)
            );
        }
        for error in failures() {
            let settled = settle::<u8>(Err(error.clone().into())).unwrap_err();
            assert!(same(&settled, &error), "{error:?}");
        }
    }

    // Carried over: `evaluation_stop` keeps stops and errors.
    #[test]
    fn evaluation_stop_keeps_stops_and_errors_and_names_caps() {
        assert_eq!(evaluation_stop(Ok("decided"), "capped").unwrap(), "decided");
        for state in STATES {
            assert_eq!(
                evaluation_stop(Err(Halt::Stop(state, Cap::IterationBound)), "capped").unwrap(),
                "capped"
            );
        }
        for error in failures() {
            let stopped = evaluation_stop(Err(error.clone().into()), "capped").unwrap_err();
            assert!(same(&stopped, &error), "{error:?}");
        }
    }

    // Carried over: the diagnostic text of a cap is fixed.
    #[test]
    fn caps_have_fixed_messages() {
        assert_eq!(Cap::IterationBound.message(), "iteration bound reached");
    }

    // Carried over: the accessors of the result-state carrier.
    #[test]
    fn settled_accessors_distinguish_values_and_states() {
        let value = Settled::Value(3);
        assert_eq!(value.value(), Some(&3));
        assert_eq!(value.state(), None);
        assert!(value.is_value() && !value.is_state());
        assert_eq!(value.into_value(), Some(3));
        for state in STATES {
            let stopped = Settled::<u8>::State(state);
            assert_eq!(stopped.value(), None);
            assert_eq!(stopped.state(), Some(state));
            assert!(!stopped.is_value() && stopped.is_state());
            assert_eq!(stopped.into_value(), None);
        }
    }

    // Request failures, positive: each is an error of its own kind, of the
    // context class, with the span of its caller.
    #[test]
    fn request_failures_are_errors_of_the_context_class() {
        let expected = [
            (ErrorKind::ResourceLimit, span(0, 3)),
            (ErrorKind::Cancelled, span(1, 2)),
            (ErrorKind::DeadlineExceeded, span(2, 2)),
        ];
        for (error, (kind, span)) in failures().iter().zip(expected) {
            assert_eq!(error.kind(), kind);
            assert_eq!(error.kind().class(), ErrorClass::Context);
            assert_eq!(error.span(), span);
            assert_eq!(error.exceeded().is_some(), kind == ErrorKind::ResourceLimit);
        }
        assert_eq!(Error::cancelled(None).span(), None);
    }

    // Request failures, negative: no fault is of the context class, and no
    // error, of a request kind or a fault such as an invalid input, ever
    // settles into a state.
    #[test]
    fn faults_are_never_of_the_context_class_and_errors_never_states() {
        for fault in FAULTS {
            let error = Error::new(fault, None, "fault");
            assert_ne!(error.kind().class(), ErrorClass::Context);
            assert!(error.exceeded().is_none());
            assert!(settle::<u8>(Err(Halt::Error(error.clone()))).is_err());
            assert!(evaluation_stop(Err(Halt::Error(error)), 0_u8).is_err());
        }
        assert_eq!(FaultKind::Internal.class(), ErrorClass::Internal);
        for error in failures() {
            assert!(settle::<u8>(Err(Halt::Error(error.clone()))).is_err());
            assert!(evaluation_stop(Err(Halt::Error(error)), 0_u8).is_err());
        }
    }

    // Mathematical states, positive: each of the five states is reached at a
    // boundary as a state of the result.
    #[test]
    fn each_math_state_settles_into_a_state() {
        for state in STATES {
            let settled = settle::<u8>(Err(Halt::Stop(state, Cap::IterationBound))).unwrap();
            assert_eq!(settled.state(), Some(state));
        }
    }

    // Mathematical states, negative: a stop is never an error, and a value is
    // never a state.
    #[test]
    fn a_math_state_is_never_an_error_and_a_value_never_a_state() {
        for state in STATES {
            assert!(settle::<u8>(Err(Halt::Stop(state, Cap::IterationBound))).is_ok());
            assert!(evaluation_stop(Err(Halt::Stop(state, Cap::IterationBound)), 0_u8).is_ok());
        }
        assert!(!settle(Ok(0_u8)).unwrap().is_state());
    }

    // Limit identifiers, positive: every field of `Limits` is reported by
    // its identifier, with the scope that the contract requires for it, the
    // allowed value and the amount.
    #[test]
    fn resource_limits_carry_structured_identifiers() {
        for &field in LimitField::ALL {
            let scope = match field {
                LimitField::Nodes | LimitField::StorageBytes => Some(LimitScope::Value),
                _ => None,
            };
            let exceeded =
                LimitExceeded::new(LimitId::Field(field), scope, 64, LimitAmount::Used(65));
            let error = Error::resource_limit(exceeded, None);
            let reported = error.exceeded().unwrap();
            assert_eq!(reported.id(), &LimitId::Field(field));
            assert_eq!(reported.id().name(), field.name());
            assert_eq!(reported.scope(), scope);
            assert_eq!(reported.allowed(), 64);
            assert_eq!(reported.amount(), LimitAmount::Used(65));
            assert_eq!(reported.amount().value(), 65);
        }
    }

    // Limit identifiers, positive and negative: the frame limit and the
    // temporary limit are told apart by their scope, and both differ from
    // the limit on the number of frames.
    #[test]
    fn frame_and_temporary_limits_differ_by_scope() {
        let nodes = |scope| {
            Error::resource_limit(
                LimitExceeded::new(
                    LimitId::Field(LimitField::Nodes),
                    Some(scope),
                    8192,
                    LimitAmount::Required(8193),
                ),
                None,
            )
        };
        let frame = nodes(LimitScope::Frame);
        let temporary = nodes(LimitScope::Temporary);
        let frames = Error::resource_limit(
            LimitExceeded::new(
                LimitId::Field(LimitField::Frames),
                None,
                32,
                LimitAmount::Required(33),
            ),
            None,
        );
        let frame = frame.exceeded().unwrap();
        let temporary = temporary.exceeded().unwrap();
        assert_eq!(frame.id(), temporary.id());
        assert_eq!(frame.scope(), Some(LimitScope::Frame));
        assert_eq!(temporary.scope(), Some(LimitScope::Temporary));
        assert_ne!(frame, temporary);
        let frames = frames.exceeded().unwrap();
        assert_eq!(frames.scope(), None);
        assert_ne!(frames.id(), frame.id());
    }

    // Limit identifiers, positive and negative: a request parameter is named
    // by its parameter, never by a field.
    #[test]
    fn a_request_parameter_limit_names_the_parameter() {
        let parameter = |name: &str| {
            Error::resource_limit(
                LimitExceeded::new(
                    LimitId::Parameter(String::from(name)),
                    None,
                    100,
                    LimitAmount::Bound(u64::MAX),
                ),
                None,
            )
        };
        let error = parameter("dimension");
        let exceeded = error.exceeded().unwrap();
        assert_eq!(
            exceeded.id(),
            &LimitId::Parameter(String::from("dimension"))
        );
        assert_eq!(exceeded.id().name(), "dimension");
        assert_eq!(exceeded.amount(), LimitAmount::Bound(u64::MAX));
        for &field in LimitField::ALL {
            assert_ne!(exceeded.id(), &LimitId::Field(field));
        }
        assert_ne!(parameter("rows").exceeded().unwrap().id(), exceeded.id());
    }

    // `exceeded()` is `Some` exactly for a `ResourceLimit` error.
    #[test]
    fn only_a_resource_limit_has_an_exceeded_limit() {
        for error in failures() {
            assert_eq!(
                error.exceeded().is_some(),
                error.kind() == ErrorKind::ResourceLimit,
                "{error:?}"
            );
        }
    }

    // A default span fills only a missing span: an error with a span keeps
    // it, and the kind and the exceeded limit stay the same.
    #[test]
    fn a_default_span_fills_only_a_missing_span() {
        for error in failures() {
            let kept = error.clone().with_default_span(span(5, 6));
            assert!(same(&kept, &error), "{error:?}");
        }
        let unplaced = [
            Error::new(FaultKind::Internal, None, "broken invariant"),
            Error::cancelled(None),
            Error::resource_limit(
                LimitExceeded::new(
                    LimitId::Field(LimitField::Nodes),
                    Some(LimitScope::Value),
                    2,
                    LimitAmount::Required(3),
                ),
                None,
            ),
        ];
        for error in unplaced {
            let placed = error.clone().with_default_span(span(5, 6));
            assert_eq!(placed.span(), span(5, 6));
            assert_eq!(placed.kind(), error.kind());
            assert_eq!(placed.exceeded(), error.exceeded());
            assert_eq!(error.clone().with_default_span(None).span(), None);
        }
    }

    // Cause frames are records only. Every constructor gives an error without
    // frames; adding a frame puts it before the frames that the error has and
    // keeps the kind, the span and the exceeded limit, charges nothing, opens
    // no frame of the request context and is not bounded by `max_frames`; the
    // span stays the span in the text of the innermost frame's operand; and
    // clones, default spans and the boundaries keep the frames. `CauseFrame`
    // has a constructor and accessors only.
    #[test]
    fn causal_frames_are_records_without_charges() {
        for error in failures() {
            assert!(error.frames().is_empty(), "{error:?}");
        }
        let frame = CauseFrame::new("ineq", 0);
        assert_eq!((frame.name(), frame.operand_index()), ("ineq", 0));
        assert_eq!(frame.clone(), frame);
        assert_ne!(frame, CauseFrame::new("ineq", 1));
        assert_ne!(frame, CauseFrame::new("membership", 0));

        // A request failure of a context whose work and frames are exhausted.
        let limits = Limits::new().with_max_work(1).with_max_frames(0);
        let mut context = Context::new(limits, CancelFlag::new());
        let failure = context.charge(2).unwrap_err();
        let counters = |context: &Context| {
            (
                context.work_used(),
                context.output_used(),
                context.open_frames(),
                context.retained(),
            )
        };
        let before = counters(&context);
        let framed = failure
            .clone()
            .with_outer_frame(CauseFrame::new("algebraic-evaluation", 2))
            .with_outer_frame(CauseFrame::new("alg-at", 1));
        assert_eq!(counters(&context), before);
        assert_eq!(
            framed.frames(),
            [
                CauseFrame::new("alg-at", 1),
                CauseFrame::new("algebraic-evaluation", 2)
            ]
        );
        assert_eq!(framed.kind(), failure.kind());
        assert_eq!(framed.span(), failure.span());
        assert_eq!(framed.exceeded(), failure.exceeded());
        assert!(context.enter_frame().is_err());

        // The span of an error that arose in the operand of the innermost
        // frame stays the span in that operand's text.
        let nested = Error::new(FaultKind::OutsideDomain, span(3, 5), "outside the domain")
            .with_outer_frame(CauseFrame::new("ineq", 0))
            .with_outer_frame(CauseFrame::new("rel-and", 0));
        assert_eq!(nested.span(), span(3, 5));
        assert_eq!(nested.frames().last(), Some(&CauseFrame::new("ineq", 0)));
        assert_eq!(nested.frames().len(), 2);

        let unplaced = Error::new(FaultKind::Unsupported, None, "unknown role")
            .with_outer_frame(CauseFrame::new("eval", 1));
        let placed = unplaced.clone().with_default_span(span(0, 1));
        assert_eq!(placed.span(), span(0, 1));
        assert_eq!(placed.frames(), unplaced.frames());
        for error in [framed, nested, unplaced] {
            assert!(same(&error.clone(), &error), "{error:?}");
            let settled = settle::<u8>(Err(error.clone().into())).unwrap_err();
            assert!(same(&settled, &error), "{error:?}");
            let stopped = evaluation_stop(Err(error.clone().into()), 0_u8).unwrap_err();
            assert!(same(&stopped, &error), "{error:?}");
        }
    }
}
