//! The command entry: one request in, one outcome out, and the line bytes of
//! the outcome.
//!
//! A [`Request`] names an operation, the variable of the operation, the input
//! text, its table of further [`Operand`]s and the versions that its outcome
//! echoes, with the [`Settings`] of the request. [`execute`] runs it under the
//! caller's [`Context`], which carries the limits, the deadline and the
//! cancellation probe of the request, and returns an [`Outcome`]: the
//! versions of the request and its structured result, an [`Answer`] or a
//! mathematical state, or the [`Error`] that ended it. The entry never
//! chooses a process exit code. [`serialize`] writes an outcome as one line
//! of bytes, charging every byte to the context before it is written; it is
//! the only output format of the library.
//!
//! The operations are found by name in one dispatch table:
//!
//! - `eval` evaluates the input to its exact number;
//! - `expand` expands the input as a polynomial in the variable of the
//!   request and returns it as a term;
//! - `diff` returns the derivative of that polynomial by the variable.
//!
//! The three operations read the input alone and no role of the operand
//! table. An unknown operation, settings other than the default and an entry
//! of the table with a role that the operation does not read fail with
//! `Unsupported`, and a missing operand, an input that is empty or holds
//! only whitespace, fails with `Syntax` at the end of the input.
//!
//! ```
//! use kalyx::command::serialize;
//! use kalyx::context::CancelFlag;
//! use kalyx::{Context, ErrorKind, FaultKind, Limits, Request, Span, execute};
//!
//! let request = Request::new("expand", "x", "(x + 1)^2").with_input_version(7);
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let outcome = execute(&request, &mut context);
//! assert_eq!(outcome.input_version(), 7);
//! let line = serialize(&outcome, &mut context)?;
//! assert_eq!(line, b"value\t7\t0\t0\t1 + 2*x + x^2\n");
//!
//! let request = Request::new("eval", "x", "  ");
//! let mut context = Context::new(Limits::new(), CancelFlag::new());
//! let outcome = execute(&request, &mut context);
//! let error = outcome.result().as_ref().unwrap_err();
//! assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
//! assert_eq!(error.span(), Span::new(2, 2));
//! # Ok::<(), kalyx::Error>(())
//! ```
//!
//! The rules of this module are stated in the component contract,
//! `docs/components/command/contract.md`, and the bytes of the lines in
//! `docs/semantics.md`.

mod dispatch;
mod line;
mod operands;
#[cfg(test)]
mod tests;

pub use line::serialize;

use crate::term::Term;
use crate::{Context, Error, FaultKind, Result, Settled};

/// The settings of a request: the choices that change the meaning of a
/// request, such as the number domain of an evaluation. The default is the
/// current semantics.
///
/// This release has no setting, so the default is the only value, and code
/// outside the library builds it with [`Settings::new`] or
/// [`Settings::default`]. A setting that a later release adds is a new field
/// with a default; a request whose settings are not the default fails with
/// `Unsupported` until the release that supports the value. The settings are
/// an input of the request and never part of the context.
///
/// ```
/// use kalyx::command::Settings;
///
/// assert_eq!(Settings::new(), Settings::default());
/// ```
///
/// No other value can be built:
///
/// ```compile_fail,E0639
/// let settings = kalyx::command::Settings {};
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Settings {}

impl Settings {
    /// The default settings, the current semantics.
    #[must_use]
    pub const fn new() -> Self {
        Self {}
    }
}

/// A request to the command entry.
///
/// Start from [`Request::new`], which sets the operation, the variable and
/// the input, and change the versions and the settings with the `with_`
/// methods. The versions are numbers that the caller chooses and that the
/// outcome echoes, so that the caller can tell which input, context and
/// settings a result belongs to. [`Request::with_operand`] appends an entry
/// to the operand table, for an operation whose signature reads roles of the
/// table; the operations of this release read none.
///
/// ```
/// use kalyx::Request;
/// use kalyx::command::Settings;
///
/// let request = Request::new("diff", "t", "t^3")
///     .with_input_version(4)
///     .with_context_version(2)
///     .with_settings(Settings::new())
///     .with_settings_version(1);
/// assert_eq!(request.operation, "diff");
/// assert_eq!((request.input_version, request.context_version), (4, 2));
/// assert!(request.operands.is_empty());
/// ```
///
/// Code outside the library builds a request only with [`Request::new`]:
///
/// ```compile_fail,E0639
/// let request = kalyx::Request {
///     operation: String::from("eval"),
///     variable: String::new(),
///     input: String::from("1"),
///     operands: Vec::new(),
///     input_version: 0,
///     context_version: 0,
///     settings: kalyx::command::Settings::new(),
///     settings_version: 0,
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Request {
    /// The name of the operation: `eval`, `expand` or `diff`.
    pub operation: String,
    /// The variable of `expand` and `diff`, a symbol name; `eval` does not
    /// read it.
    pub variable: String,
    /// The input text, in the input syntax of `docs/semantics.md`: the
    /// operand of index 0.
    pub input: String,
    /// The operand table: the operands after the input, in their order, so
    /// that the entry `operands[k-1]` is the operand of index `k`. Empty for
    /// a request of [`Request::new`].
    pub operands: Vec<Operand>,
    /// The version of the input, such as the revision of the text of a
    /// cell; echoed by the outcome.
    pub input_version: u64,
    /// The version of the computation context that the input refers to, such
    /// as a document or a session; echoed by the outcome. This release has
    /// no session and does not check it.
    pub context_version: u64,
    /// The settings of the request.
    pub settings: Settings,
    /// The version of the settings, such as the revision of the settings of
    /// a document; echoed by the outcome.
    pub settings_version: u64,
}

impl Request {
    /// The request for `operation` on `input`, in the variable `variable`,
    /// with an empty operand table, the versions 0 and the default settings.
    #[must_use]
    pub fn new(operation: &str, variable: &str, input: &str) -> Self {
        Self {
            operation: String::from(operation),
            variable: String::from(variable),
            input: String::from(input),
            operands: Vec::new(),
            input_version: 0,
            context_version: 0,
            settings: Settings::new(),
            settings_version: 0,
        }
    }

    /// This request with the entry of the role `role` and the text `text`
    /// appended to its operand table.
    ///
    /// ```
    /// use kalyx::Request;
    /// use kalyx::command::Operand;
    ///
    /// let request = Request::new("eval", "x", "1").with_operand("scope", "x: real");
    /// assert_eq!(request.operands, [Operand::new("scope", "x: real")]);
    /// ```
    #[must_use]
    pub fn with_operand(mut self, role: &str, text: &str) -> Self {
        self.operands.push(Operand::new(role, text));
        self
    }

    /// This request with the input version `version`.
    #[must_use]
    pub fn with_input_version(mut self, version: u64) -> Self {
        self.input_version = version;
        self
    }

    /// This request with the context version `version`.
    #[must_use]
    pub fn with_context_version(mut self, version: u64) -> Self {
        self.context_version = version;
        self
    }

    /// This request with the settings `settings`.
    #[must_use]
    pub fn with_settings(mut self, settings: Settings) -> Self {
        self.settings = settings;
        self
    }

    /// This request with the settings version `version`.
    #[must_use]
    pub fn with_settings_version(mut self, version: u64) -> Self {
        self.settings_version = version;
        self
    }
}

/// An entry of the operand table of a [`Request`]: the role of an operand
/// and its text.
///
/// The signature of an operation, which its component contract states,
/// names the roles that it reads, whether each is required, optional or
/// repeatable, and the start symbol of the input syntax that reads each.
/// The operations of this release read no role of the table, so every entry
/// of a request to them is an unknown role.
///
/// ```
/// use kalyx::command::Operand;
///
/// let operand = Operand::new("scope", "x: positive");
/// assert_eq!((operand.role.as_str(), operand.text.as_str()), ("scope", "x: positive"));
/// ```
///
/// Code outside the library builds an entry only with [`Operand::new`]:
///
/// ```compile_fail,E0639
/// let operand = kalyx::command::Operand {
///     role: String::from("scope"),
///     text: String::from("x: real"),
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Operand {
    /// The role of the operand, a name of the signature of the operation.
    pub role: String,
    /// The text of the operand, read with the start symbol of its role.
    pub text: String,
}

impl Operand {
    /// The entry of the role `role` with the text `text`.
    #[must_use]
    pub fn new(role: &str, text: &str) -> Self {
        Self {
            role: String::from(role),
            text: String::from(text),
        }
    }
}

/// The value of a result, one variant for each kind of value that an
/// operation returns.
///
/// Each variant is a value kind of the table of value kinds in
/// `docs/semantics.md`. A term, the only kind of this release, is written as
/// a value line; a later kind is written as an answer line. Code that reads
/// an answer matches its variants with a wildcard arm, since later releases
/// add variants.
///
/// ```
/// use kalyx::command::Answer;
/// use kalyx::context::CancelFlag;
/// use kalyx::{Context, Limits, Request, Settled, execute};
///
/// let mut context = Context::new(Limits::new(), CancelFlag::new());
/// let outcome = execute(&Request::new("diff", "x", "x^2"), &mut context);
/// let text = match outcome.result() {
///     Ok(Settled::Value(Answer::Term(term))) => term.display(&mut context)?,
///     // Later releases add kinds of values and states.
///     Ok(_) => String::from("another value or a state"),
///     Err(error) => String::from(error.message()),
/// };
/// assert_eq!(text, "2*x");
/// # Ok::<(), kalyx::Error>(())
/// ```
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Answer {
    /// A term of the term core.
    Term(Term),
}

/// The outcome of a request: the versions of the request and its result.
///
/// The result is a [`Settled`] answer, a value or a mathematical state, or
/// the [`Error`] that ended the request, as every method with states returns
/// it. No operation of this release ends in a state. Only [`execute`] builds
/// an outcome, and [`serialize`] writes it as a line.
#[derive(Clone, Debug)]
#[must_use = "an outcome holds the result or the error of its request"]
pub struct Outcome {
    input_version: u64,
    context_version: u64,
    settings_version: u64,
    result: Result<Settled<Answer>>,
}

impl Outcome {
    /// The input version of the request.
    #[must_use]
    pub const fn input_version(&self) -> u64 {
        self.input_version
    }

    /// The context version of the request.
    #[must_use]
    pub const fn context_version(&self) -> u64 {
        self.context_version
    }

    /// The settings version of the request.
    #[must_use]
    pub const fn settings_version(&self) -> u64 {
        self.settings_version
    }

    /// The result: an answer or a state, or the error that ended the
    /// request.
    #[must_use]
    pub const fn result(&self) -> &Result<Settled<Answer>> {
        &self.result
    }

    /// The result, consuming the outcome.
    pub fn into_result(self) -> Result<Settled<Answer>> {
        self.result
    }
}

/// Runs `request` under `context` and returns its outcome, which echoes the
/// versions of the request.
///
/// The entry checks the settings, then finds the operation in the dispatch
/// table; then it checks each entry of the operand table, which charges one
/// unit before it looks up the role in the signature of the operation, and
/// each required role of the signature, and only then runs the operation:
/// `eval` parses the input, `expand` and `diff` check the variable, then
/// parse the input and work on the polynomial of the term. The first failure
/// ends the request. Every step of the work is charged to `context`, which
/// the caller creates with the limits, the deadline and the cancellation
/// probe of the request; the entry never creates a context and never charges
/// output. An error of an operand carries the entry frame of the operation
/// and the index of the operand as its first [cause frame](Error::frames).
///
/// A host that runs the requests of a job one after another creates a
/// context for each, on one clock of the job and with the deadline of the
/// job, and checks the cancellation flag and the deadline of the job between
/// two of them, since a request that fails before its first charge point
/// reports its own error and not the cancellation. It publishes a line for
/// every request that ran: the line under the context of the request, or,
/// when that fails and the outcome is an error, of any kind, the line under a
/// fresh context, with a fresh flag and no deadline; a value or a state is
/// never written again. The job stops at a cancellation or a passed
/// deadline, goes on after a fault or a `ResourceLimit`, and ends in one
/// terminal state, as the contract of the command entry states for a job of
/// several requests:
///
/// ```
/// use kalyx::command::serialize;
/// use kalyx::context::{CancelFlag, Clock, MonotonicClock};
/// use kalyx::{Context, ErrorKind, Limits, Outcome, Request, execute};
///
/// /// The terminal states of a job.
/// #[derive(Debug, PartialEq, Eq)]
/// enum JobState {
///     Completed,
///     Failed,
///     Cancelled,
///     ResourceExhausted,
/// }
///
/// /// The line that the job publishes for `outcome`, if any, and the errors
/// /// of its request: the error of the outcome, and the error of `serialize`
/// /// when the line fails under `context`, the context of the request.
/// fn publish(outcome: &Outcome, context: &mut Context) -> (Option<Vec<u8>>, Vec<ErrorKind>) {
///     let mut errors = Vec::new();
///     if let Err(error) = outcome.result() {
///         errors.push(error.kind());
///     }
///     let line = match serialize(outcome, context) {
///         Ok(line) => Some(line),
///         Err(error) => {
///             errors.push(error.kind());
///             match outcome.result() {
///                 // The fallback step, for an error of any kind: a fresh
///                 // flag and no deadline.
///                 Err(_) => {
///                     let mut fresh = Context::new(Limits::new(), CancelFlag::new());
///                     serialize(outcome, &mut fresh).ok()
///                 }
///                 // A value or a state is never written again.
///                 Ok(_) => None,
///             }
///         }
///     };
///     (line, errors)
/// }
///
/// /// Runs `requests` one after another on `clock`, the clock of the job,
/// /// until `deadline`, a reading of that clock, or until `flag` is set, and
/// /// returns the lines that the job publishes and its terminal state.
/// fn run_job(
///     requests: &[Request],
///     mut clock: MonotonicClock,
///     deadline: u64,
///     flag: &CancelFlag,
/// ) -> (Vec<Vec<u8>>, JobState) {
///     let mut lines = Vec::new();
///     let mut failed = false;
///     for request in requests {
///         // Between two requests, the host checks cancellation, then the
///         // deadline of the job, itself.
///         if flag.is_cancelled() {
///             return (lines, JobState::Cancelled);
///         }
///         if clock.now() >= deadline {
///             return (lines, JobState::ResourceExhausted);
///         }
///         // One context per request: its budget, a copy of the clock of the
///         // job, which keeps its origin, the deadline of the job and the
///         // flag of the job.
///         let mut context =
///             Context::with_observers(Limits::new(), Box::new(clock), Box::new(flag.clone()))
///                 .with_deadline(deadline);
///         let outcome = execute(request, &mut context);
///         let (line, errors) = publish(&outcome, &mut context);
///         lines.extend(line);
///         let cancelled = errors.contains(&ErrorKind::Cancelled);
///         if cancelled || errors.contains(&ErrorKind::DeadlineExceeded) {
///             // The job stops; once its cancellation is requested, it ends
///             // cancelled, whatever stopped it.
///             let state = if cancelled || flag.is_cancelled() {
///                 JobState::Cancelled
///             } else {
///                 JobState::ResourceExhausted
///             };
///             return (lines, state);
///         }
///         // A fault or a `ResourceLimit` fails the job and does not stop it.
///         failed |= !errors.is_empty();
///     }
///     let state = if failed { JobState::Failed } else { JobState::Completed };
///     (lines, state)
/// }
///
/// let mut clock = MonotonicClock::new();
/// // The deadline of the job, a minute after its start, on the clock of the job.
/// let deadline = clock.now().saturating_add(60_000_000_000);
/// let requests = [
///     Request::new("eval", "x", "1/3 + 1/6"),
///     Request::new("eval", "x", "1/0").with_input_version(2),
///     Request::new("diff", "x", "x^2").with_input_version(3),
/// ];
/// let flag = CancelFlag::new();
/// // The division by zero fails the job, and the next request still runs.
/// let (lines, state) = run_job(&requests, clock, deadline, &flag);
/// assert_eq!(state, JobState::Failed);
/// assert_eq!(lines.len(), 3);
/// assert_eq!(lines[0], b"value\t0\t0\t0\t1/2\n");
/// assert!(lines[1].starts_with(b"error\t2\t0\t0\tDivisionByZero\t"));
/// assert_eq!(lines[2], b"value\t3\t0\t0\t2*x\n");
/// let (lines, state) = run_job(&requests[2..], clock, deadline, &flag);
/// assert_eq!((lines.len(), state), (1, JobState::Completed));
/// // A deadline of the job that has passed stops it before its next request.
/// let (lines, state) = run_job(&requests, clock, 0, &flag);
/// assert_eq!((lines.len(), state), (0, JobState::ResourceExhausted));
/// // So does a cancellation.
/// flag.cancel();
/// let (lines, state) = run_job(&requests, clock, deadline, &flag);
/// assert_eq!((lines.len(), state), (0, JobState::Cancelled));
/// ```
///
/// # Errors
///
/// The outcome holds the error that ended the request:
///
/// - `Fault(Unsupported)`, without a span and without a frame, for settings
///   other than the default and for an unknown operation;
/// - `Fault(Unsupported)`, without a span, for an entry of the operand table
///   whose role the operation does not read, which every role is for the
///   operations of this release, with the frame of the operation at the
///   index of the entry;
/// - `Fault(Syntax)` or `Fault(Unsupported)`, without a span and without a
///   frame, for a variable of `expand` or `diff` that is not a symbol name or
///   is reserved;
/// - `ResourceLimit` naming `max_input_bytes`, without a span and without a
///   frame, when the operand table is not empty and the bytes of the input
///   and of every entry exceed that limit;
/// - the errors of `parse`, each with a span into the input: among them
///   `Fault(Syntax)` with the empty span at the end of the input when the
///   operand is missing;
/// - `Fault(UnknownSymbol)` when the input of `eval` is not a number, and the
///   errors of the expansion, the derivative and the conversion back to a
///   term for `expand` and `diff`, all without a span;
/// - the request failures of the charges.
///
/// The errors of `parse` and of the operation itself have the frame of the
/// operation at the index 0, the input, and the request failures of a charge
/// have the frame of the step that charged, if that step has one.
pub fn execute(request: &Request, context: &mut Context) -> Outcome {
    Outcome {
        input_version: request.input_version,
        context_version: request.context_version,
        settings_version: request.settings_version,
        result: result_of(request, context),
    }
}

/// The result of `request`: steps 1 and 2 of its order, the settings and
/// the operation, then the steps of the operation.
fn result_of(request: &Request, context: &mut Context) -> Result<Settled<Answer>> {
    check_default(&request.settings)?;
    let (name, operation) = dispatch::lookup(&request.operation)?;
    dispatch::run(name, operation, request, context)
}

/// Checks that `settings` is the default, the only settings that this
/// release supports; charges nothing. The check compares the whole record
/// with its default, so a setting that a later release adds is checked
/// without a change here.
fn check_default<S: Default + PartialEq>(settings: &S) -> Result<()> {
    if *settings == S::default() {
        Ok(())
    } else {
        Err(Error::new(
            FaultKind::Unsupported,
            None,
            "settings other than the default are not supported in this release",
        ))
    }
}
